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

/// Build the shared Seq-view SMT term and element SMT/Rust types for a `Vec`
/// const, or `None` if the element type is not a supported integer type. The
/// element type is parsed from the SMT sort string
/// (e.g. `alloc!vec.Vec<u32./alloc!alloc.Global.>.`).
fn vec_view_and_elem_ty(name: &str, sort: &str) -> Option<(String, &'static str, String)> {
    let after = sort.split_once("Vec<")?.1;
    let elem_raw = after.split('.').next()?;
    let (smt_elem_ty, rust_elem_ty) = int_type_smt_and_rust(elem_raw)?;
    // The allocator Type argument MUST be `TYPE%alloc!alloc.Global.` — the same
    // term the function's requires/quantifiers use — NOT the prelude constant
    // `ALLOCATOR_GLOBAL` (an uninterpreted `(declare-const ALLOCATOR_GLOBAL Type)`
    // that is not equated to it in a pruned query). If they differ, the `Seq.index`
    // ground terms we materialize land on a *different* Seq than the one
    // `upper_bound`/`sorted` constrain, so the quantifiers never bite and the model
    // stays bogus. (Vec's default allocator is Global.)
    let view = format!(
        "(vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ {ety} $ TYPE%alloc!alloc.Global.) (Poly%{sort} {name}))",
        ety = smt_elem_ty,
        sort = sort,
        name = name,
    );
    Some((smt_elem_ty, rust_elem_ty, view))
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
    let (smt_elem_ty, _rust, view) = vec_view_and_elem_ty(name, sort)?;
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
    if instantiation_pushed {
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
            // Vec: reconstruct its elements by querying its Seq view (see helper).
            TypX::Named(sort) if sort.starts_with("alloc!vec.Vec<") => {
                if let Some((mut cex, vec_pins)) = query_vec_counterexample(context, &name, sort) {
                    cex.role = role;
                    counterexamples.push(cex);
                    if let Some(bucket) = pin_bucket {
                        bucket.extend(vec_pins);
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

    GatheredCounterexamples { counterexamples, input_pins, output_pins, instantiated: instantiation_pushed }
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
}

/// Reconstruct a `Vec` counterexample by querying the model, returning both the
/// display `Counterexample` and the SMT equality terms (length + each element)
/// that pin the vector back to its model value. The element type is parsed from
/// the SMT sort string (e.g. `alloc!vec.Vec<u32./alloc!alloc.Global.>.`).
fn query_vec_counterexample(
    context: &mut Context,
    name: &str,
    sort: &str,
) -> Option<(Counterexample, Vec<String>)> {
    // The Seq view of the Vec plus the element types, shared by the length and
    // index queries (and by the instantiation materialization).
    let (smt_elem_ty, rust_elem_ty, view) = vec_view_and_elem_ty(name, sort)?;

    let len_term = format!("(vstd!seq.Seq.len.? $ {ety} {view})", ety = smt_elem_ty, view = view);
    let len_raw = context.eval_expr(parse_smt_term(&len_term));
    let len: i64 = clean_smt_value(&len_raw).parse().ok()?;
    if len < 0 {
        return None;
    }

    let mut pins: Vec<String> = Vec::new();
    // Pin the length, then each element (mirrors the manual `let e0 = v[0]...`
    // trick used in the ex4 example to force Z3 to materialize the Vec).
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

    let cex = Counterexample {
        var_name: name.to_string(),
        var_value: format!("vec![{}]", elems.join(", ")),
        var_type: Some(format!("Vec<{}>", rust_elem_ty)),
        classification: None,
        role: None,
        stage_report: None,
    };
    Some((cex, pins))
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
