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
//!    entirely on the Z3 side (no compile/run). Two stages, in order:
//!
//!    - **Refutation**: pin the *full* witness (every model constant, inputs and
//!      the recomputed output) back into the failing query as strict equalities
//!      and re-run `check-sat`. `unsat` => the witness cannot actually satisfy
//!      the constraints (e.g. a non-linear-arithmetic guess whose output is
//!      inconsistent with the body once the numbers are concrete) => SPURIOUS.
//!      `sat` => the witness genuinely violates the property => REAL. Pinning the
//!      full witness is what makes the "use the latest/true output" property
//!      automatic: a bogus output contradicts the body and is refuted here,
//!      before confirmation ever runs.
//!    - **Confirmation** (only when refutation is `unknown`): assert that the
//!      user function's post-condition *holds* under the pinned witness and
//!      re-run `check-sat`. `unsat` => the post-condition provably cannot hold
//!      for this witness => REAL. This turns the "is it real?" question into an
//!      `unsat` proof, which the proof-oriented Z3 configuration answers cleanly
//!      even when it will not commit to `sat` (the `unknown` wall).
//!
//!    Everything runs inside `push`/`pop` scopes so the solver state the caller
//!    reuses for subsequent error localization is never corrupted.

use crate::ast::{Typ, TypX};
use crate::context::{CexClassification, Context, Counterexample, VarRole};
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

    // Turn on model completion for the eval queries below.
    context.smt_log.log_set_option("model.completion", "true");
    let opt_data = context.smt_log.take_pipe_data();
    let _ = context.get_smt_process().send_commands(opt_data);

    // --- Counterexample instantiation (SMT-level materialization) -------------
    // For each Vec param — inputs AND outputs (the return value) — assert the
    // two-part materialization (pin length + `has_type` per element). This forces
    // Z3 to complete a *coherent* model, the analogue of the source `let e_i = v[i]`
    // trick done entirely at the SMT level:
    //   - on inputs, it fires the `sorted`/`upper_bound` requires-quantifiers so the
    //     witness is precondition-valid;
    //   - on outputs, it fires the body's `push` ensures-quantifiers so the returned
    //     Vec's elements actually reflect `input ++ pushed values` instead of the
    //     under-constrained junk Z3 leaves when the ground `Seq.index` terms are
    //     absent.
    // NOTE: materializing an output does NOT pin it for refutation — that is a
    // separate decision below (`pin_value`), kept input-only so classification is
    // not corrupted. The push scope stays open so the eval loop reads the refined
    // model; it is popped before returning, restoring the caller's solver state.
    let mut materialize_terms: Vec<String> = Vec::new();
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
    let instantiation_pushed = !materialize_terms.is_empty();

    // Before materializing, snapshot the *whole* input/output witness (every `!`
    // param and the return binder — scalars, collections and tuples alike) as
    // reconstructed from the *initial* (un-instantiated) model — the "first
    // counterexample". After instantiation we compare against it: if ANY value
    // changed, the first model was an under-constrained/incoherent (likely
    // spurious) witness that the instantiation step corrected. Crucially this
    // includes the OUTPUT: materializing the input+output Vecs fires the body's
    // ensures-quantifiers, which can also change a scalar/derived output value —
    // not just the collections themselves. These are exactly the cases where this
    // pipeline's materialization was load-bearing rather than cosmetic.
    let mut pre_values: Vec<(String, String)> = Vec::new();
    if instantiation_pushed {
        for def in model.iter() {
            if def.params.len() != 0 || !def.name.ends_with('!') || def.name.starts_with("%%") {
                continue;
            }
            let rust_ty = context.counterexample_types.get(def.name.as_str()).cloned();
            let val = display_value_of(context, &def.name, &def.ret, rust_ty.as_deref());
            pre_values.push((def.name.to_string(), val));
        }
        context.smt_log.log_push();
        for t in &materialize_terms {
            context.smt_log.log_node(&parse_smt_term(&format!("(assert {})", t)));
        }
        context.smt_log.log_word("check-sat");
        let data = context.smt_log.take_pipe_data();
        let _ = context.get_smt_process().send_commands(data);
    }

    let mut counterexamples: Vec<Counterexample> = Vec::new();
    // Pins are split by role: refutation pins **inputs**; confirmation additionally
    // pins **outputs**. Pinning outputs *together with* inputs is what makes the
    // check a test of the *specific* witnessed (input, output) pair against the
    // failing query (see `refine_and_classify`), instead of relying on the body —
    // which is `TASKS`' "requires the concrete input / ensures the concrete output"
    // shape. A concrete pair that is a genuine counterexample stays consistent
    // (sat/unknown); a spurious one becomes `unsat` once fully pinned.
    let mut input_pins: Vec<String> = Vec::new();
    let mut output_pins: Vec<String> = Vec::new();
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

    GatheredCounterexamples {
        counterexamples,
        input_pins,
        output_pins,
        instantiated: instantiation_pushed,
        changed_by_instantiation,
    }
}

/// Result of `gather_counterexamples`: the display values plus the role-split pins
/// the refinement stages consume.
pub(crate) struct GatheredCounterexamples {
    pub(crate) counterexamples: Vec<Counterexample>,
    /// Equality pins for the **input** witness (refutation + confirmation).
    pub(crate) input_pins: Vec<String>,
    /// Equality pins for the **output** witness (confirmation only).
    pub(crate) output_pins: Vec<String>,
    /// Whether the instantiation/materialization stage actually ran (for the trace).
    pub(crate) instantiated: bool,
    /// Whether instantiation actually *changed* a collection value vs. the initial
    /// model — i.e. the first counterexample was incoherent and this pipeline's
    /// materialization corrected it (for the trace + tooling).
    pub(crate) changed_by_instantiation: bool,
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

/// The Z3-side refinement, run as the two witness-pinning stages of the pipeline.
///
/// Both stages pin the *concrete counterexample values* back into the still-loaded
/// failing query (which already asserts the negation of the property) and re-check:
///
/// - **Refute** — pin the concrete **inputs** (`requires`-side). This is the
///   "assume inputs" step: does the failing query stay satisfiable once the inputs
///   are nailed to the witness?
/// - **Confirm** — additionally pin the concrete **output** (`ensures`-side). This
///   is the "assume inputs + output" step: does the *specific* witnessed
///   (input, output) pair stay consistent with the failing query?
///
/// **Polarity (important, and empirically grounded):** Verus always runs Z3 with a
/// large quantified prelude and `smt.mbqi false`, tuned to prove `unsat`. So a
/// *genuine* counterexample's fully-pinned re-check does **not** return `sat` — it
/// returns `unknown ("incomplete quantifiers")` (verified: this holds even for a
/// hand-written `assume(input); …; assert(output)` source function, and even for
/// unbounded `int`; unlike Dafny, whose lean query returns a clean `sat`). The one
/// answer Z3 gives cleanly is `unsat`, which happens exactly when the pinned
/// concrete witness is **inconsistent** — i.e. it cannot actually occur, so the
/// counterexample is a solver artifact. Hence:
///
/// - `unsat`  → **Spurious** (the witness cannot occur), and
/// - `sat` / `unknown` → **Real** (the concrete witness stays consistent with a
///   genuine property violation).
///
/// This is what makes bare `assert` failures classify correctly too: they have no
/// `ensures`/output to pin, so Confirm ≡ Refute, and a real assert failure's pinned
/// input yields `unknown` → Real.
pub(crate) fn refine_and_classify(
    context: &mut Context,
    input_pins: &[String],
    output_pins: &[String],
    instantiated: bool,
    changed_by_instantiation: bool,
    report: &mut Vec<String>,
) -> CexClassification {
    // Helper: dump the concrete witness terms that a stage pins, so the debug
    // trace shows *exactly which counterexample* was fed to that stage's re-check.
    fn dump_pins(report: &mut Vec<String>, pins: &[String]) {
        if pins.is_empty() {
            report.push("      (none)".to_string());
        }
        for p in pins {
            report.push(format!("      pin: {}", p));
        }
    }

    report.push(
        "Stage 1 — Regular counterexample: read the initial model from the failing query."
            .to_string(),
    );
    report.push(format!(
        "Stage 2 — Instantiate inputs/outputs: {}",
        if instantiated {
            "materialized Vec elements so the witness is concrete/coherent"
        } else {
            "skipped (no Vec parameters to materialize)"
        }
    ));
    // Surface whether instantiation actually *changed* the witness vs. the initial
    // model. A machine-greppable marker ("Instantiation changed counterexample:
    // yes/no") lets tooling flag the examples where this pipeline's materialization
    // was load-bearing — the first (Stage 1) counterexample there was an
    // incoherent/likely-spurious model that instantiation corrected.
    if instantiated {
        report.push(format!(
            "      Instantiation changed counterexample: {}",
            if changed_by_instantiation {
                "yes (initial model was under-constrained; corrected by materialization)"
            } else {
                "no (initial model already coherent)"
            }
        ));
    } else {
        report.push("      Instantiation changed counterexample: n/a".to_string());
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

    // Stage 3 — Refute: pin the concrete INPUTS back into the failing query and
    // re-run the verification.
    report.push(format!(
        "Stage 3 — Refute: re-run verification with the {} concrete INPUT value(s) pinned:",
        input_pins.len()
    ));
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
        report.push("=> Classification: SPURIOUS".to_string());
        return CexClassification::Spurious;
    }
    report.push(
        "      => still satisfiable (sat/unknown): inputs do not by themselves refute the \
         witness; proceeding to Confirm."
            .to_string(),
    );

    // Stage 4 — Confirm: additionally pin the concrete OUTPUT and re-check the
    // specific witnessed (input, output) pair.
    let mut all_pins = input_pins.to_vec();
    all_pins.extend_from_slice(output_pins);
    report.push(format!(
        "Stage 4 — Confirm: re-run with inputs + the {} concrete OUTPUT value(s) pinned:",
        output_pins.len()
    ));
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
                "      => sat/unknown: the concrete (input, output) pair stays consistent with the"
                    .to_string(),
            );
            report.push(
                "         property violation (Verus never returns a clean 'sat' here — its prelude"
                    .to_string(),
            );
            report.push(
                "         runs with mbqi off, so a genuine witness surfaces as 'unknown'). REAL."
                    .to_string(),
            );
            CexClassification::Real
        }
    };
    report.push(format!("=> Classification: {}", match class {
        CexClassification::Real => "REAL",
        CexClassification::Spurious => "SPURIOUS",
        CexClassification::Inconclusive => "INCONCLUSIVE",
    }));
    class
}
