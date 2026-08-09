//! Counterexample extraction and refinement.
//!
//! This module holds the counterexample-specific logic that used to live inline
//! in `smt_verify.rs`, so that file stays close to its pre-counterexample shape.
//! Two things happen here, both driven off the Z3 model produced for a failing
//! query (see `smt_verify::smt_get_model`):
//!
//! 1. **Extraction** (`gather_counterexamples`): read concrete values out of the
//!    model via `(eval ...)`. Scalars evaluate directly; `Vec<T>` is
//!    reconstructed through its `Seq` view (length + per-element queries),
//!    because Z3 never materializes a `Vec`'s contents into a single constant.
//!    See `trivial_example/SMT_VALUE_EXTRACTION.md` for the full walkthrough.
//!
//! 2. **Refinement** (`refine_and_classify`): decide whether the extracted
//!    witness is a genuine failing input (REAL) or a solver artifact (SPURIOUS),
//!    entirely on the Z3 side (no compile/run). Both stages pin the *concrete
//!    counterexample values* back into the still-loaded failing query (which
//!    already asserts the negation of the property) as plain ground equalities,
//!    and re-run `check-sat`. Same polarity at both stages — `unsat` is the only
//!    definitive signal, and it only ever proves SPURIOUS:
//!
//!    - **Refutation**: pin the concrete **inputs** (`requires`-side) only.
//!      `unsat` => the witness cannot actually satisfy the constraints once the
//!      inputs are nailed down => SPURIOUS, and refinement stops here. Otherwise
//!      (`sat`/`unknown`) proceed to Confirmation.
//!    - **Confirmation**: additionally pin the concrete **output**
//!      (`ensures`-side) — it never re-asserts the postcondition formula itself.
//!      `unsat` => the exact (input, output) pair is inconsistent with the
//!      failing query => SPURIOUS. `sat`/`unknown` => the pair stays consistent
//!      with the property violation => REAL. In practice Verus's quantified
//!      prelude runs with `smt.mbqi false`, tuned to prove `unsat`, so a genuine
//!      witness surfaces as `unknown` rather than a clean `sat` — REAL is always
//!      reached via this `sat`/`unknown` fallback, never proven by `unsat`.
//!
//!    Everything runs inside `push`/`pop` scopes so the solver state the caller
//!    reuses for subsequent error localization is never corrupted.

use crate::ast::{Typ, TypX};
use crate::context::{CexClassification, Context, Counterexample, VarRole};
use crate::counterexample_ablation::AblationArm;
use crate::model::ModelDef;

/// Parse an SMT term string into an s-expression node for `(eval ...)` / `(assert ...)`.
pub(crate) fn parse_smt_term(s: &str) -> sise::Node {
    let mut parser = sise::Parser::new(s.as_bytes());
    sise::read_into_tree(&mut parser).expect("counterexample: failed to parse SMT term")
}

/// Normalize an SMT scalar value into Rust literal text.
/// Z3 prints negatives as `(- 5)`; turn that into `-5`. Other values pass through.
pub(crate) fn clean_smt_value(s: &str) -> String {
    let t = s.trim();
    if let Some(inner) = t.strip_prefix('(').and_then(|x| x.strip_suffix(')')) {
        let inner = inner.trim();
        if let Some(n) = inner.strip_prefix('-') {
            return format!("-{}", n.trim());
        }
        return inner.to_string();
    }
    t.to_string()
}

/// Render a cleaned scalar model value for *display*, using the Rust type pushed
/// down from VIR (`Context::counterexample_types`) to recover distinctions the SMT
/// sort drops. Only the printed value is affected — the value pinned back into the
/// solver always uses the raw SMT term (a `char` is pinned as its codepoint int).
///
/// - `char`: the model gives a unicode codepoint (an `Int`); render it as a Rust
///   char literal `'A'` (with escaping) instead of `65`.
/// - struct/tuple: the model gives a constructor application
///   `<sort>./<Ctor> <arg0> <arg1> ...`; render it as `Ctor(arg0, arg1)` (or
///   `(arg0, arg1)` for tuples) when every field is already concrete.
fn render_scalar(cleaned: &str, rust_ty: Option<&str>) -> String {
    if rust_ty == Some("char") {
        if let Ok(cp) = cleaned.parse::<u32>() {
            if let Some(c) = char::from_u32(cp) {
                return format!("'{}'", c.escape_default());
            }
        }
        return cleaned.to_string();
    }
    render_constructor(cleaned)
}

/// Prettify a datatype constructor application the model returns as
/// `<sort>./<Ctor> <arg0> <arg1> ...` into `Ctor(arg0, arg1)` (structs/enums) or
/// `(arg0, arg1)` (tuples). Left untouched (returned verbatim) unless every field
/// is a simple concrete token — if any field is itself parenthesized (a negative
/// `(- 5)` or a nested constructor) or an opaque `Poly!val!N` handle, we do not
/// risk mangling it. This is display-only.
fn render_constructor(cleaned: &str) -> String {
    // Nested structure (negatives, nested ctors) — leave raw rather than mangle.
    if cleaned.contains('(') {
        return cleaned.to_string();
    }
    let tokens: Vec<&str> = cleaned.split_whitespace().collect();
    if tokens.len() < 2 || !tokens[0].contains("./") {
        return cleaned.to_string();
    }
    // Opaque, un-materialized fields (e.g. tuple's `Poly!val!N`): don't pretend.
    if tokens[1..].iter().any(|t| t.contains("!val!")) {
        return cleaned.to_string();
    }
    let ctor = tokens[0].rsplit('/').next().unwrap_or(tokens[0]);
    let args = tokens[1..].join(", ");
    if ctor.starts_with("tuple%") {
        format!("({})", args)
    } else {
        format!("{}({})", ctor, args)
    }
}

/// Map an integer element-type name (as found in a Vec sort string) to its SMT
/// type term and Rust type name. Returns None for unsupported element types.
fn int_type_smt_and_rust(t: &str) -> Option<(String, &'static str)> {
    let r = match t {
        "u8" => ("(UINT 8)".to_string(), "u8"),
        "u16" => ("(UINT 16)".to_string(), "u16"),
        "u32" => ("(UINT 32)".to_string(), "u32"),
        "u64" => ("(UINT 64)".to_string(), "u64"),
        "u128" => ("(UINT 128)".to_string(), "u128"),
        "usize" => ("USIZE".to_string(), "usize"),
        "i8" => ("(SINT 8)".to_string(), "i8"),
        "i16" => ("(SINT 16)".to_string(), "i16"),
        "i32" => ("(SINT 32)".to_string(), "i32"),
        "i64" => ("(SINT 64)".to_string(), "i64"),
        "i128" => ("(SINT 128)".to_string(), "i128"),
        "isize" => ("ISIZE".to_string(), "isize"),
        _ => return None,
    };
    Some(r)
}

/// Superset of `int_type_smt_and_rust` that also covers the *element* types that
/// only ever appear inside composite/ghost collections — a `char` element (SMT
/// type `CHAR`) inside a `String`/`Vec<char>`, and the unbounded ghost integer
/// element types `int`/`nat` (SMT types `INT`/`NAT`) inside a ghost `Seq`. Kept
/// separate so the Vec-element boundary (`int_type_smt_and_rust`, which must stay
/// exec-representable) is not widened. Returns `(smt_type_term, rust_type_name)`.
fn elem_smt_and_rust(t: &str) -> Option<(String, &'static str)> {
    match t {
        "int" => Some(("INT".to_string(), "int")),
        "nat" => Some(("NAT".to_string(), "nat")),
        "char" => Some(("CHAR".to_string(), "char")),
        _ => int_type_smt_and_rust(t),
    }
}

/// Which flavor of indexable collection a witness constant is, controlling only
/// how the reconstructed element list is *rendered* (the SMT element-walk is the
/// same for all three — see `collection_view` / `query_collection_counterexample`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum CollectionKind {
    /// `Vec<T>` — rendered `vec![..]`.
    Vec,
    /// `String` — a `Seq<char>` view, rendered as a quoted string literal.
    StringChars,
    /// A bare ghost `Seq<T>` — rendered `[..]`.
    Seq,
}

/// For a witness constant `name` of SMT sort `sort`, if it is one of the three
/// supported indexable collections, return everything the element-walk needs:
/// the element SMT type term, the element Rust type name, the `Seq`-view `Poly`
/// term to index into, and the collection kind. Returns `None` for anything else
/// (scalars, tuples, structs — handled elsewhere).
///
/// The three shapes differ only in how the `Seq` view is obtained:
/// - **Vec** (`alloc!vec.Vec<T./..>.`): `View::view` of the boxed Vec, with the
///   Type argument `(TYPE%alloc!vec.Vec. $ elemT $ TYPE%alloc!alloc.Global.)`.
/// - **String** (`alloc!string.String.`): `View::view` of the boxed String, whose
///   `View::V` is `Seq<char>`; the element type is always `CHAR`.
/// - **ghost Seq** (`vstd!seq.Seq<T.>.`): already a view — just box it with
///   `Poly%<sort>`; no `View::view` wrapper.
fn collection_view(
    name: &str,
    sort: &str,
) -> Option<(String, &'static str, String, CollectionKind)> {
    if sort.starts_with("alloc!vec.Vec<") {
        let after = sort.split_once("Vec<")?.1;
        let elem_raw = after.split('.').next()?;
        let (smt_elem_ty, rust_elem_ty) = elem_smt_and_rust(elem_raw)?;
        // The allocator Type argument MUST be `TYPE%alloc!alloc.Global.` (see the
        // long note that used to live in `vec_view_and_elem_ty`): using the opaque
        // `ALLOCATOR_GLOBAL` const lands the ground `Seq.index` terms on a different
        // Seq than the quantifiers constrain.
        let view = format!(
            "(vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ {ety} $ TYPE%alloc!alloc.Global.) (Poly%{sort} {name}))",
            ety = smt_elem_ty,
            sort = sort,
            name = name,
        );
        Some((smt_elem_ty, rust_elem_ty, view, CollectionKind::Vec))
    } else if sort.starts_with("alloc!string.String") {
        // A String's `View::V` is `Seq<char>`; walk it exactly like a Vec<char>.
        let view = format!(
            "(vstd!view.View.view.? $ TYPE%alloc!string.String. (Poly%alloc!string.String. {name}))",
            name = name,
        );
        Some(("CHAR".to_string(), "char", view, CollectionKind::StringChars))
    } else if sort.starts_with("vstd!seq.Seq<") {
        // A bare ghost `Seq<T>` is already a view — no `View::view` wrapper, just
        // box the concrete-sort constant back to `Poly` for `Seq.len`/`Seq.index`.
        let after = sort.split_once("Seq<")?.1;
        let elem_raw = after.split('.').next()?;
        let (smt_elem_ty, rust_elem_ty) = elem_smt_and_rust(elem_raw)?;
        let view = format!("(Poly%{sort} {name})", sort = sort, name = name);
        Some((smt_elem_ty, rust_elem_ty, view, CollectionKind::Seq))
    } else {
        None
    }
}

/// SMT assert terms that **instantiate** (materialize) an *input* `Vec` so Z3
/// completes a precondition-valid model for it. Two parts, both required:
///  1. **pin the length** to its current-model value, and
///  2. `has_type(Seq.index(view, i), elemT)` for each in-bounds `i`.
///
/// This reproduces at the SMT level exactly what source `let e_i = v[i]` bindings
/// do: (2) creates the ground `Seq.index` term that fires the `sorted`/`upper_bound`
/// quantifier patterns (keyed on `Seq.index(v,i)`) and pins the element's int range,
/// while (1) is needed because those foralls are guarded by `i < len` — without a
/// fixed length Z3 picks a short sequence and leaves the tail unconstrained.
/// Returns `None` if the element type is unsupported or the length is unreadable.
fn vec_materialization_terms(
    context: &mut Context,
    name: &str,
    sort: &str,
) -> Option<Vec<String>> {
    let (smt_elem_ty, _rust, view, _kind) = collection_view(name, sort)?;
    let len_term = format!("(vstd!seq.Seq.len.? $ {ety} {view})", ety = smt_elem_ty, view = view);
    let len_raw = context.eval_expr(parse_smt_term(&len_term));
    let len: i64 = clean_smt_value(&len_raw).parse().ok()?;
    if len < 0 {
        return None;
    }
    let mut terms = Vec::with_capacity(len as usize + 1);
    terms.push(format!("(= {} {})", len_term, clean_smt_value(&len_raw)));
    for i in 0..len {
        terms.push(format!(
            "(has_type (vstd!seq.Seq.index.? $ {ety} {view} (I {i})) {ety})",
            ety = smt_elem_ty,
            view = view,
            i = i,
        ));
    }
    Some(terms)
}

/// Reconstruct just the *display value* of one witness constant from the current
/// model (no pins), dispatching the same way `gather_counterexamples` does:
/// collection → `query_collection`, tuple → `query_tuple`, else scalar. Used to
/// snapshot the initial ("first counterexample") witness before instantiation so
/// it can be compared against the post-instantiation witness.
fn display_value_of(context: &mut Context, name: &str, ret: &Typ, rust_ty: Option<&str>) -> String {
    match &**ret {
        TypX::Named(sort) if collection_view(name, sort).is_some() => {
            query_collection_counterexample(context, name, sort)
                .map(|(c, _)| c.var_value)
                .unwrap_or_default()
        }
        TypX::Named(sort) if sort.starts_with("tuple%") => {
            query_tuple_counterexample(context, name, rust_ty)
                .map(|(c, _)| c.var_value)
                .unwrap_or_default()
        }
        _ => {
            let raw = context.eval_expr(parse_smt_term(name));
            render_scalar(&clean_smt_value(&raw), rust_ty)
        }
    }
}

/// Extract counterexample values from the model, plus:
///  - `pins`: the SMT equality terms that pin every model constant back to its
///    value (the *full* witness — used by refutation);
///  - `scalar_param_names`: the names of the scalar `!` constants in model order
///    (used as the argument list for the confirmation's ens application).
///
/// Candidates are the zero-arity model entries whose name ends in `!` (function
/// parameters and the return binder) or contains `@` (locals / SSA values),
/// skipping the internal `%%`-prefixed labels. Only `!` constants are pinned;
/// `@` locals are extracted for display but not pinned (the body recomputes
/// them). The model is iterated in Z3's output order so the pin/name lists are
/// deterministic.
pub(crate) fn gather_counterexamples(
    context: &mut Context,
    model: &[ModelDef],
) -> GatheredCounterexamples {
    let candidates: Vec<(String, Typ)> = model
        .iter()
        .filter(|def| def.params.len() == 0)
        .filter(|def| def.name.ends_with('!') || def.name.contains('@'))
        .filter(|def| !def.name.starts_with("%%"))
        .map(|def| (def.name.to_string(), def.ret.clone()))
        .collect();
    let candidates_total = candidates.len();
    let arm = AblationArm::from_env();

    // Turn on model completion for the eval queries below.
    context.smt_log.log_set_option("model.completion", "true");
    let opt_data = context.smt_log.take_pipe_data();
    let _ = context.get_smt_process().send_commands(opt_data);

    // --- Counterexample instantiation (SMT-level materialization) -------------
    // Materialize every Vec param — inputs AND outputs — via
    // `vec_materialization_terms` (see its doc comment for the mechanism).
    // Materializing an output does NOT pin it for refutation (kept input-only
    // so classification isn't corrupted). The push scope stays open so the
    // eval loop below reads the refined model; popped before returning.
    // `arm.instantiate()` gates this off entirely for B0/B2.
    let mut materialize_terms: Vec<String> = Vec::new();
    if arm.instantiate() {
        for def in model.iter() {
            if def.params.len() != 0 || !def.name.ends_with('!') || def.name.starts_with("%%") {
                continue;
            }
            if let TypX::Named(sort) = &*def.ret {
                if sort.starts_with("alloc!vec.Vec<") {
                    if let Some(terms) = vec_materialization_terms(context, &def.name, sort) {
                        materialize_terms.extend(terms);
                    }
                }
            }
        }
    }
    let instantiation_pushed = !materialize_terms.is_empty();

    // Snapshot every `!` param + return binder from the *initial* model before
    // materializing, so the post-instantiation values below can be compared
    // against it (`changed_by_instantiation`) — see that field's doc.
    let mut pre_values: Vec<(String, String)> = Vec::new();
    // Raw-witness precondition check (Stage 0.5, see `refine_and_classify`'s doc):
    // the same input-role SMT-pinnable equality terms Stage 3/4 will build below,
    // but evaluated against the model as it stands *right now* — before
    // instantiation materializes anything. Must be captured here, before the
    // `log_push`/materialize block just below switches the solver into the
    // post-instantiation state that the rest of this function (and the main
    // per-candidate loop further down) reads from.
    let mut raw_input_pins: Vec<String> = Vec::new();
    if instantiation_pushed {
        for def in model.iter() {
            if def.params.len() != 0 || !def.name.ends_with('!') || def.name.starts_with("%%") {
                continue;
            }
            let rust_ty = context.counterexample_types.get(def.name.as_str()).cloned();
            let val = display_value_of(context, &def.name, &def.ret, rust_ty.as_deref());
            pre_values.push((def.name.to_string(), val));
        }
        raw_input_pins = extract_input_pins(context, &candidates);
        context.smt_log.log_push();
        for t in &materialize_terms {
            context.smt_log.log_node(&parse_smt_term(&format!("(assert {})", t)));
        }
        context.smt_log.log_word("check-sat");
        let data = context.smt_log.take_pipe_data();
        let _ = context.get_smt_process().send_commands(data);
    }

    let mut counterexamples: Vec<Counterexample> = Vec::new();
    // Pins split by role: refutation pins inputs only; confirmation pins
    // inputs+outputs (see `refine_and_classify`'s doc for why that split
    // matters).
    let mut input_pins: Vec<String> = Vec::new();
    let mut output_pins: Vec<String> = Vec::new();
    // Shape-recognized-but-extraction-failed candidates (name, reason) — see
    // `GatheredCounterexamples::unsupported`'s doc.
    let mut unsupported: Vec<(String, String)> = Vec::new();
    for (name, ret) in candidates {
        let is_param = name.ends_with('!');
        let role = context.counterexample_roles.get(name.as_str()).copied();
        // Where does this variable's value-pin go? Inputs (and unknown-role params)
        // → input_pins; the return/output → output_pins. `@` locals are never
        // pinned (the body recomputes them).
        let pin_bucket: Option<&mut Vec<String>> = if !is_param {
            None
        } else if role == Some(VarRole::Output) {
            Some(&mut output_pins)
        } else {
            Some(&mut input_pins)
        };
        match &*ret {
            // Vec / String / ghost Seq: reconstruct their elements by querying the
            // shared Seq view (length + per-element), see `query_collection_...`.
            TypX::Named(sort) if collection_view(&name, sort).is_some() => {
                if let Some((mut cex, coll_pins)) =
                    query_collection_counterexample(context, &name, sort)
                {
                    cex.role = role;
                    counterexamples.push(cex);
                    if let Some(bucket) = pin_bucket {
                        bucket.extend(coll_pins);
                    }
                } else {
                    unsupported.push((
                        name.clone(),
                        "Vec/String/Seq witness: could not determine a concrete length from \
                         the model (non-numeric or negative Seq.len)"
                            .to_string(),
                    ));
                }
            }
            // Tuple: fields come back `Poly`-boxed inside the constructor app, so
            // reconstruct each via its field accessor + unbox (see helper).
            TypX::Named(sort) if sort.starts_with("tuple%") => {
                let rust_ty = context.counterexample_types.get(name.as_str()).cloned();
                if let Some((mut cex, tup_pins)) =
                    query_tuple_counterexample(context, &name, rust_ty.as_deref())
                {
                    cex.role = role;
                    counterexamples.push(cex);
                    if let Some(bucket) = pin_bucket {
                        bucket.extend(tup_pins);
                    }
                } else {
                    unsupported.push((
                        name.clone(),
                        "tuple witness: model constructor pattern not recognized (unexpected \
                         arity/ctor shape)"
                            .to_string(),
                    ));
                }
            }
            _ => {
                // Simple scalar (Int/Bool/...): evaluate the variable directly.
                let raw = context.eval_expr(parse_smt_term(&name));
                if let Some(bucket) = pin_bucket {
                    // The raw eval output is already valid SMT (e.g. `8`, `(- 5)`,
                    // `true`), so it can be pinned verbatim. NOTE: pin the raw SMT
                    // value, never the display rendering below (a `char` is pinned
                    // as its codepoint int, not as `'A'`).
                    bucket.push(format!("(= {} {})", name, raw.trim()));
                }
                // Recover the Rust type (char/struct/tuple/...) the SMT sort dropped,
                // for display only.
                let rust_ty = context.counterexample_types.get(name.as_str()).cloned();
                let cleaned = clean_smt_value(&raw);
                counterexamples.push(Counterexample {
                    var_name: name.clone(),
                    var_value: render_scalar(&cleaned, rust_ty.as_deref()),
                    var_type: rust_ty,
                    classification: None,
                    role,
                    stage_report: None,
                });
            }
        }
    }

    if instantiation_pushed {
        context.smt_log.log_pop();
        let data = context.smt_log.take_pipe_data();
        let _ = context.get_smt_process().send_commands(data);
    }

    // Did instantiation change any collection value vs. the initial model?
    let mut changed_by_instantiation = false;
    for (name, pre) in &pre_values {
        if let Some(post) = counterexamples.iter().find(|c| &c.var_name == name) {
            if &post.var_value != pre {
                changed_by_instantiation = true;
            }
        }
    }

    // Stage 1 as full `Counterexample`s — see `GatheredCounterexamples::
    // raw_counterexamples`'s doc. Role/type looked up from the Stage-2 entry
    // by name (only the value can differ between stages).
    let mut raw_counterexamples: Vec<Counterexample> = Vec::new();
    if instantiation_pushed {
        for (name, val) in &pre_values {
            let (var_type, role) = counterexamples
                .iter()
                .find(|c| &c.var_name == name)
                .map(|c| (c.var_type.clone(), c.role))
                .unwrap_or((None, None));
            raw_counterexamples.push(Counterexample {
                var_name: name.clone(),
                var_value: val.clone(),
                var_type,
                classification: None,
                role,
                stage_report: None,
            });
        }
    }

    GatheredCounterexamples {
        counterexamples,
        input_pins,
        output_pins,
        raw_input_pins,
        instantiated: instantiation_pushed,
        changed_by_instantiation,
        pre_instantiation_values: pre_values,
        materialize_terms,
        candidates_total,
        unsupported,
        raw_counterexamples,
    }
}

/// Extract just the SMT-pinnable equality terms for **input**-role candidates
/// (output-role and `@` locals are skipped, matching `input_pins`'s own
/// population rule in the main per-candidate loop above), evaluated against
/// whatever solver state is currently active. The pin-only counterpart to
/// that loop: no display `Counterexample`s are built, no `unsupported`
/// diagnostics tracked — this exists solely so `gather_counterexamples` can
/// call it twice against two different solver states (before and after the
/// instantiation push) without duplicating the collection/tuple/scalar
/// dispatch logic. See `raw_input_pins`'s doc for why the "before" call
/// matters.
fn extract_input_pins(context: &mut Context, candidates: &[(String, Typ)]) -> Vec<String> {
    let mut input_pins: Vec<String> = Vec::new();
    for (name, ret) in candidates {
        if !name.ends_with('!') {
            continue; // not a param — `@` locals are never pinned
        }
        if context.counterexample_roles.get(name.as_str()).copied() == Some(VarRole::Output) {
            continue;
        }
        match &**ret {
            TypX::Named(sort) if collection_view(name, sort).is_some() => {
                if let Some((_, coll_pins)) = query_collection_counterexample(context, name, sort) {
                    input_pins.extend(coll_pins);
                }
            }
            TypX::Named(sort) if sort.starts_with("tuple%") => {
                let rust_ty = context.counterexample_types.get(name.as_str()).cloned();
                if let Some((_, tup_pins)) =
                    query_tuple_counterexample(context, name, rust_ty.as_deref())
                {
                    input_pins.extend(tup_pins);
                }
            }
            _ => {
                let raw = context.eval_expr(parse_smt_term(name));
                input_pins.push(format!("(= {} {})", name, raw.trim()));
            }
        }
    }
    input_pins
}

/// Result of `gather_counterexamples`: the display values plus the role-split pins
/// the refinement stages consume.
pub(crate) struct GatheredCounterexamples {
    pub(crate) counterexamples: Vec<Counterexample>,
    /// Equality pins for the **input** witness (refutation + confirmation).
    pub(crate) input_pins: Vec<String>,
    /// Equality pins for the **output** witness (confirmation only).
    pub(crate) output_pins: Vec<String>,
    /// Equality pins for the **input** witness, evaluated against the model
    /// *before* instantiation materialized anything (empty unless instantiation
    /// ran — see `instantiated`). Consumed by `refine_and_classify`'s Stage 0.5
    /// (raw-witness precondition check): pinning these into the failing query
    /// and re-checking `sat` tests whether the *raw* Stage-1 witness (what a
    /// naive Stage-1-only tool would report) is coherent on its own terms,
    /// independent of whether instantiation later produced a coherent one.
    pub(crate) raw_input_pins: Vec<String>,
    /// Whether the instantiation/materialization stage actually ran (for the trace).
    pub(crate) instantiated: bool,
    /// Whether instantiation actually *changed* a collection value vs. the initial
    /// model — i.e. the first counterexample was incoherent and this pipeline's
    /// materialization corrected it (for the trace + tooling).
    pub(crate) changed_by_instantiation: bool,
    /// The raw Stage-1 witness (every `!` param and the return binder), read from
    /// the model *before* instantiation ran. Empty when instantiation didn't run.
    /// Printed by `refine_and_classify` so the Stage-1 intermediary counterexample
    /// is actually visible, not just whether it later changed.
    pub(crate) pre_instantiation_values: Vec<(String, String)>,
    /// The SMT-level ground terms asserted during Stage 2 materialization (length
    /// pin + per-element `has_type`, for every `Vec`/`Seq` input and output) — the
    /// Z3-nomenclature detail behind "instantiation changed the counterexample".
    pub(crate) materialize_terms: Vec<String>,
    /// Total number of zero-arity `!`/`@` model constants that matched the
    /// extraction filter, before any per-candidate dispatch. If this is 0, the
    /// failing query had no witnessed variables at all (not an extraction bug).
    pub(crate) candidates_total: usize,
    /// Candidates whose SMT sort was recognized as a collection/tuple shape but
    /// whose value extraction still failed (name, reason) — these used to be
    /// silently dropped with zero trace. A permanent diagnostic, unrelated to
    /// `AblationArm` (which lives in its own module for the same isolation
    /// reason this exists: keep evaluation concerns out of the normal path).
    pub(crate) unsupported: Vec<(String, String)>,
    /// Stage 1's raw (pre-instantiation) witness, as full `Counterexample`s
    /// (same role/type as Stage-2, only the value can differ). Empty when
    /// instantiation didn't run. Lets the caller runtime-check both stages'
    /// witnesses against ground truth — see `smt_verify`'s use of
    /// `context::STAGE1_RAW_WITNESS_PREFIX` to carry these across the
    /// `ValidityResult` boundary.
    pub(crate) raw_counterexamples: Vec<Counterexample>,
}

/// Render one reconstructed element (an `Int` model value, already `clean_smt_
/// value`-normalized) as Rust literal text for its element type. Chars come back
/// as unicode codepoints and become `'A'`; everything else passes through.
fn render_element(cleaned: &str, rust_elem_ty: &str) -> String {
    if rust_elem_ty == "char" {
        if let Ok(cp) = cleaned.parse::<u32>() {
            if let Some(c) = char::from_u32(cp) {
                return format!("'{}'", c.escape_default());
            }
        }
    }
    cleaned.to_string()
}

/// Reconstruct a collection (`Vec` / `String` / ghost `Seq`) counterexample by
/// querying its `Seq` view, returning both the display `Counterexample` and the
/// SMT equality terms (length + each element) that pin it back to its model
/// value. This is the *one* element-walk shared by all three: the only per-kind
/// differences are the `Seq`-view term (from `collection_view`) and how the
/// element list is finally rendered (`vec![..]` / `"..."` / `[..]`).
fn query_collection_counterexample(
    context: &mut Context,
    name: &str,
    sort: &str,
) -> Option<(Counterexample, Vec<String>)> {
    let (smt_elem_ty, rust_elem_ty, view, kind) = collection_view(name, sort)?;

    let len_term = format!("(vstd!seq.Seq.len.? $ {ety} {view})", ety = smt_elem_ty, view = view);
    let len_raw = context.eval_expr(parse_smt_term(&len_term));
    let len: i64 = clean_smt_value(&len_raw).parse().ok()?;
    if len < 0 {
        return None;
    }

    let mut pins: Vec<String> = Vec::new();
    // Pin the length, then each element (mirrors the manual `let e0 = v[0]...`
    // trick used in the ex4 example to force Z3 to materialize the sequence).
    pins.push(format!("(= {} {})", len_term, clean_smt_value(&len_raw)));

    let mut elems: Vec<String> = Vec::new();
    for i in 0..len {
        let elem_term = format!(
            "(%I (vstd!seq.Seq.index.? $ {ety} {view} (I {i})))",
            ety = smt_elem_ty,
            view = view,
            i = i,
        );
        let raw = context.eval_expr(parse_smt_term(&elem_term));
        pins.push(format!("(= {} {})", elem_term, raw.trim()));
        elems.push(clean_smt_value(&raw));
    }

    // Render the element list per collection kind.
    let (var_value, var_type) = match kind {
        CollectionKind::Vec => {
            let items =
                elems.iter().map(|e| render_element(e, rust_elem_ty)).collect::<Vec<_>>();
            (format!("vec![{}]", items.join(", ")), format!("Vec<{}>", rust_elem_ty))
        }
        CollectionKind::Seq => {
            // Ghost Seq: elements are `int`/`nat` (or widths) — render as-is.
            (format!("[{}]", elems.join(", ")), format!("Seq<{}>", rust_elem_ty))
        }
        CollectionKind::StringChars => {
            // Rebuild the actual string from its char codepoints; `{:?}` yields a
            // correctly-escaped Rust string literal (e.g. `"hi"`, `"\u{0}"`).
            let s: String = elems
                .iter()
                .filter_map(|e| e.parse::<u32>().ok())
                .filter_map(char::from_u32)
                .collect();
            (format!("{:?}", s), "String".to_string())
        }
    };

    let cex = Counterexample {
        var_name: name.to_string(),
        var_value,
        var_type: Some(var_type),
        classification: None,
        role: None,
        stage_report: None,
    };
    Some((cex, pins))
}

/// Reconstruct a tuple counterexample. The model returns the tuple constant as a
/// constructor application `tuple%N./tuple%N Poly!val!0 .. Poly!val!{N-1}` whose
/// fields are opaque `Poly` boxes, so — mirroring the Vec `Seq.index` walk — each
/// field is pulled out via its field accessor `(tuple%N./tuple%N/K p!)` and
/// unboxed with `%I`. Field Rust types come from the pushed-down tuple type
/// string (e.g. `(u32, char)`) so a `char` field renders `'A'`; absent that, all
/// fields render as their raw integer value. Returns the display `Counterexample`
/// plus per-field equality pins for refutation.
fn query_tuple_counterexample(
    context: &mut Context,
    name: &str,
    rust_ty: Option<&str>,
) -> Option<(Counterexample, Vec<String>)> {
    // Evaluate the tuple constant to recover its constructor name + arity.
    let raw = context.eval_expr(parse_smt_term(name));
    let cleaned = raw.trim();
    let inner = cleaned.strip_prefix('(').and_then(|s| s.strip_suffix(')')).unwrap_or(cleaned);
    let tokens: Vec<&str> = inner.split_whitespace().collect();
    let ctor = *tokens.first()?;
    if !ctor.contains("./") {
        return None;
    }
    let arity = tokens.len() - 1;
    if arity == 0 {
        return None;
    }

    // Per-field Rust types parsed from e.g. `(u32, char)`; empty if unavailable.
    let field_tys: Vec<String> = rust_ty
        .and_then(|t| t.strip_prefix('(').and_then(|s| s.strip_suffix(')')))
        .map(|inner| split_top_level_commas(inner).into_iter().map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();

    let mut pins: Vec<String> = Vec::new();
    let mut rendered: Vec<String> = Vec::new();
    for k in 0..arity {
        let accessor = format!("({}/{} {})", ctor, k, name);
        let elem_term = format!("(%I {})", accessor);
        let fv = context.eval_expr(parse_smt_term(&elem_term));
        pins.push(format!("(= {} {})", elem_term, fv.trim()));
        let cleaned_fv = clean_smt_value(&fv);
        let fty = field_tys.get(k).map(|s| s.as_str()).unwrap_or("");
        rendered.push(render_element(&cleaned_fv, fty));
    }

    let cex = Counterexample {
        var_name: name.to_string(),
        var_value: format!("({})", rendered.join(", ")),
        var_type: rust_ty.map(|s| s.to_string()),
        classification: None,
        role: None,
        stage_report: None,
    };
    Some((cex, pins))
}

/// Split a string at top-level (bracket-depth 0) commas — for parsing a tuple
/// type like `(u32, (i8, i8))` into its field types without breaking on nested
/// commas.
fn split_top_level_commas(s: &str) -> Vec<&str> {
    let bytes = s.as_bytes();
    let (mut depth, mut last) = (0i32, 0usize);
    let mut out = Vec::new();
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' | b'[' | b'<' | b'{' => depth += 1,
            b')' | b']' | b'>' | b'}' => depth -= 1,
            b',' if depth == 0 => {
                out.push(&s[last..i]);
                last = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[last..]);
    out
}

#[derive(PartialEq, Eq)]
enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

/// Assert `terms` (each a boolean SMT term) inside a fresh `push`/`pop` scope and
/// run `check-sat`, returning the solver's verdict. The scope guarantees the
/// surrounding solver state is left exactly as it was.
fn check_sat_with(context: &mut Context, terms: &[String]) -> SatResult {
    context.smt_log.log_push();
    for t in terms {
        let node = parse_smt_term(&format!("(assert {})", t));
        context.smt_log.log_node(&node);
    }
    context.smt_log.log_word("check-sat");
    let data = context.smt_log.take_pipe_data();
    let out = context.get_smt_process().send_commands(data);

    context.smt_log.log_pop();
    let pop_data = context.smt_log.take_pipe_data();
    let _ = context.get_smt_process().send_commands(pop_data);

    for line in out.iter() {
        match line.trim() {
            "sat" => return SatResult::Sat,
            "unsat" => return SatResult::Unsat,
            "unknown" => return SatResult::Unknown,
            _ => {}
        }
    }
    SatResult::Unknown
}

impl std::fmt::Display for SatResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            SatResult::Sat => "sat",
            SatResult::Unsat => "unsat",
            SatResult::Unknown => "unknown (incomplete quantifiers)",
        };
        write!(f, "{}", s)
    }
}

impl SatResult {
    /// Uppercase, no-annotation form for the `Z3 OUTCOME: ...` trace line.
    fn outcome_word(&self) -> &'static str {
        match self {
            SatResult::Sat => "SAT",
            SatResult::Unsat => "UNSAT",
            SatResult::Unknown => "UNKNOWN",
        }
    }
}

/// The Z3-side refinement (Stages 3-4): pin the witness back into the failing
/// query and re-check `check-sat`. See the module doc comment (top of file)
/// for the full mechanism and polarity (`unsat` ⇒ SPURIOUS at either stage;
/// `sat`/`unknown` ⇒ REAL, never proven). One fact not covered there: bare
/// `assert` failures have no `ensures`/output to pin, so Confirm ≡ Refute,
/// and a real assert failure's pinned input yields `unknown` → REAL.
pub(crate) fn refine_and_classify(
    context: &mut Context,
    counterexamples: &[Counterexample],
    input_pins: &[String],
    output_pins: &[String],
    raw_input_pins: &[String],
    instantiated: bool,
    changed_by_instantiation: bool,
    pre_instantiation_values: &[(String, String)],
    materialize_terms: &[String],
    candidates_total: usize,
    unsupported: &[(String, String)],
    report: &mut Vec<String>,
) -> CexClassification {
    let arm = AblationArm::from_env();
    // Helper: dump the concrete witness terms that a stage pins (raw SMT-LIB, Z3
    // nomenclature), so the trace shows exactly what was asserted at that stage.
    fn dump_pins(report: &mut Vec<String>, pins: &[String]) {
        if pins.is_empty() {
            report.push("        (none)".to_string());
        }
        for p in pins {
            report.push(format!("        pin: {}", p));
        }
    }

    // Helper: dump a witness in clean Verus/Rust form — `name = value`, one per
    // line — from a list of (name, value) pairs (already-rendered display values).
    fn dump_witness_pairs(report: &mut Vec<String>, entries: &[(String, String)]) {
        if entries.is_empty() {
            report.push("        (none)".to_string());
        }
        for (name, val) in entries {
            report.push(format!("        {} = {}", name.trim_end_matches('!'), val));
        }
    }

    // Helper: same, but reading straight from `Counterexample`s, optionally
    // filtered by role (`None` filter = show everything, including `@` locals;
    // `Some(f)` = only params where `f(role)` holds, matching what that stage
    // actually pins).
    fn dump_witness(
        report: &mut Vec<String>,
        counterexamples: &[Counterexample],
        role_filter: Option<fn(Option<VarRole>) -> bool>,
    ) {
        let entries: Vec<(String, String)> = counterexamples
            .iter()
            .filter(|c| match role_filter {
                None => true,
                Some(f) => c.var_name.ends_with('!') && f(c.role),
            })
            .map(|c| (c.var_name.clone(), c.var_value.clone()))
            .collect();
        dump_witness_pairs(report, &entries);
    }

    // --- Stage 1 — Regular counterexample -----------------------------------
    report.push(
        "Stage 1 — Regular counterexample: read the initial model from the failing query."
            .to_string(),
    );
    if instantiated {
        // The model as first read, before any materialization — this is what
        // Stage 2 below either keeps or corrects.
        dump_witness_pairs(report, pre_instantiation_values);
    } else {
        // Nothing gets materialized, so Stage 1's witness is also the final one.
        dump_witness(report, counterexamples, None);
    }

    // --- Extraction diagnostics: candidates found vs. actually extracted, so a
    // benchmark run can grep "unsupported:" for stats on uncovered shapes. -----
    if candidates_total == 0 {
        report.push(
            "Extraction: 0 candidate model constant(s) — this failing query has no \
             witnessed `!`/`@` variables to report (nothing to extract, not an extractor bug)."
                .to_string(),
        );
    } else {
        report.push(format!(
            "Extraction: {} candidate model constant(s) found; {} produced a counterexample \
             value{}",
            candidates_total,
            counterexamples.len(),
            if unsupported.is_empty() {
                String::new()
            } else {
                format!(", {} unsupported (type/shape not handled by this extractor)", unsupported.len())
            }
        ));
    }
    for (name, reason) in unsupported {
        report.push(format!("      unsupported: {} — {}", name.trim_end_matches('!'), reason));
    }

    // --- Stage 2 — Instantiate inputs/outputs --------------------------------
    report.push(format!(
        "Stage 2 — Instantiate inputs/outputs: {}",
        if instantiated {
            "materialized Vec/Seq elements so the witness is concrete/coherent"
        } else {
            "skipped (no Vec/Seq parameters to materialize)"
        }
    ));
    if instantiated {
        report.push("      Counterexample after instantiation:".to_string());
        dump_witness(report, counterexamples, None);
        // Greppable "yes/no" marker so tooling can flag examples where
        // materialization was load-bearing (see `changed_by_instantiation`'s doc).
        report.push(format!(
            "      Instantiation changed counterexample: {}",
            if changed_by_instantiation {
                "yes (initial model was under-constrained; corrected by materialization)"
            } else {
                "no (initial model already coherent)"
            }
        ));
        report.push(
            "      Z3-level terms asserted to materialize (length pin + per-index \
             has_type):"
                .to_string(),
        );
        dump_pins(report, materialize_terms);
    } else {
        report.push("      Instantiation changed counterexample: n/a".to_string());
    }

    // --- Ablation arm gate (see `counterexample_ablation`) — unset/B3 falls
    // straight through unchanged; B0/B1 skip classification, always REAL. -----
    if arm != AblationArm::B3 {
        report.push(format!("Ablation arm: {}", arm.label()));
    }
    if !arm.classify() {
        report.push(
            "Stage 3 — Refute: skipped (ablation arm B0/B1: classification disabled by design)."
                .to_string(),
        );
        report.push(
            "Stage 4 — Confirm: skipped (ablation arm B0/B1: classification disabled by design)."
                .to_string(),
        );
        report.push(
            "=> Classification: REAL (ablation arm B0/B1 — always-REAL by design, not evidence)"
                .to_string(),
        );
        return CexClassification::Real;
    }

    if input_pins.is_empty() {
        report.push("Stage 3 — Refute: skipped (no input witness to pin).".to_string());
        report.push("Stage 4 — Confirm: skipped.".to_string());
        report.push(
            "=> Classification: INCONCLUSIVE (no concrete input to pin, cannot refute or \
             confirm the witness)"
                .to_string(),
        );
        return CexClassification::Inconclusive;
    }

    // --- Stage 0.5 — Raw-witness precondition check (diagnostic only; never
    // affects `CexClassification`) ----------------------------------------------
    // Pins the SAME kind of concrete input values Stage 3 pins below, but the
    // *raw* (pre-instantiation) ones — i.e. exactly what a naive Stage-1-only
    // tool would have reported, before this pipeline's Stage 2 materialized any
    // Vec/Seq elements. `unsat` here means the raw witness is already
    // internally inconsistent with its own precondition, on its own terms,
    // independent of whether Refute (Stage 3, on the *instantiated* witness)
    // later proves anything — i.e. static, `unsat`-backed proof that
    // instantiation was necessary to reach a witness coherent enough to
    // evaluate at all, not merely a presentation nicety. Only meaningful when
    // instantiation actually ran (raw and instantiated pins are identical
    // otherwise, which would just duplicate Stage 3's own check) — gated the
    // same way `pre_instantiation_values` is. See TASKS_IMPORTANT.md item 4.
    if instantiated && !raw_input_pins.is_empty() {
        report.push(format!(
            "Stage 0.5 — Raw-witness precondition check: re-run verification with the {} \
             concrete RAW (pre-instantiation) INPUT value(s) pinned:",
            raw_input_pins.len()
        ));
        report.push("      Raw witness (Stage 1, before materialization):".to_string());
        dump_witness_pairs(report, pre_instantiation_values);
        report.push("      Z3-level pins asserted (raw values):".to_string());
        dump_pins(report, raw_input_pins);
        let raw_refute = check_sat_with(context, raw_input_pins);
        report.push(format!("      check-sat = {}", raw_refute));
        if raw_refute == SatResult::Unsat {
            report.push(
                "      => UNSAT: the raw Stage-1 witness's own concrete values are already \
                 inconsistent with the precondition, BEFORE instantiation materialized \
                 anything — instantiation was necessary to reach an evaluable witness at all, \
                 not merely cosmetic."
                    .to_string(),
            );
        } else {
            report.push(
                "      => still satisfiable (sat/unknown): the raw witness was already \
                 internally coherent on its own terms; instantiation's contribution here is \
                 presentation/runtime-compilability, not fixing an incoherent witness."
                    .to_string(),
            );
        }
        report.push(format!("      RAW WITNESS COHERENCE: {}", raw_refute.outcome_word()));
        report.push(
            "      (diagnostic only — does not affect Classification; see Stage 3/4 below for \
             the actual REAL/SPURIOUS/INCONCLUSIVE call)"
                .to_string(),
        );
    }

    // --- Stage 3 — Refute: pin the concrete INPUTS back into the failing query
    // and re-run the verification. ---------------------------------------------
    report.push(format!(
        "Stage 3 — Refute: re-run verification with the {} concrete INPUT value(s) pinned:",
        input_pins.len()
    ));
    report.push("      Witness pinned at this stage (input only):".to_string());
    dump_witness(report, counterexamples, Some(|role| role != Some(VarRole::Output)));
    report.push("      Z3-level pins asserted:".to_string());
    dump_pins(report, input_pins);
    let refute = check_sat_with(context, input_pins);
    report.push(format!("      check-sat = {}", refute));
    if refute == SatResult::Unsat {
        // unsat here = the query (which asserts the property's negation) has NO model
        // once the inputs are fixed = the property HOLDS for these inputs = the
        // verification PASSES = this "counterexample" cannot actually occur.
        report.push(
            "      => UNSAT: with these concrete inputs pinned, the verification now PASSES"
                .to_string(),
        );
        report.push(
            "         (the failing query has no model), so these values can never trigger the"
                .to_string(),
        );
        report.push(
            "         failure. This witness is NOT a real counterexample — it is a solver artifact."
                .to_string(),
        );
        report.push(format!("      Z3 OUTCOME: {}", refute.outcome_word()));
        report.push("=> Classification: SPURIOUS".to_string());
        return CexClassification::Spurious;
    }
    report.push(
        "      => still satisfiable (sat/unknown): inputs do not by themselves refute the \
         witness; proceeding to Confirm."
            .to_string(),
    );
    report.push(format!("      Z3 OUTCOME: {}", refute.outcome_word()));

    // --- Stage 4 — Confirm: additionally pin the concrete OUTPUT and re-check the
    // specific witnessed (input, output) pair. ----------------------------------
    let mut all_pins = input_pins.to_vec();
    all_pins.extend_from_slice(output_pins);
    report.push(format!(
        "Stage 4 — Confirm: re-run with inputs + the {} concrete OUTPUT value(s) pinned:",
        output_pins.len()
    ));
    report.push("      Witness pinned at this stage (input + output):".to_string());
    dump_witness(report, counterexamples, Some(|_role| true));
    report.push("      Z3-level pins asserted:".to_string());
    dump_pins(report, &all_pins);
    let confirm = check_sat_with(context, &all_pins);
    report.push(format!("      check-sat = {}", confirm));

    let class = match confirm {
        // Fully-pinned witness is inconsistent -> it cannot actually occur.
        SatResult::Unsat => {
            report.push(
                "      => UNSAT: the exact (input, output) pair makes the query unsatisfiable, so"
                    .to_string(),
            );
            report.push(
                "         the verification PASSES for it — the pair cannot occur. SPURIOUS."
                    .to_string(),
            );
            CexClassification::Spurious
        }
        // Stays consistent (sat, or unknown due to the prelude quantifier wall) ->
        // the concrete witness is a genuine counterexample.
        SatResult::Sat | SatResult::Unknown => {
            report.push(
                "      => sat/unknown: the concrete (input, output) pair stays consistent with"
                    .to_string(),
            );
            report.push("         the property violation. REAL.".to_string());
            CexClassification::Real
        }
    };
    report.push(format!("      Z3 OUTCOME: {}", confirm.outcome_word()));
    report.push(format!("=> Classification: {}", match class {
        CexClassification::Real => "REAL",
        CexClassification::Spurious => "SPURIOUS",
        CexClassification::Inconclusive => "INCONCLUSIVE",
    }));
    class
}
