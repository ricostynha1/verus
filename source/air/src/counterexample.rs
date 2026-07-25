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

use crate::ast::{Ident, Typ, TypX};
use crate::context::{CexClassification, Context, Counterexample};
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
) -> (Vec<Counterexample>, Vec<String>, Vec<String>) {
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

    let mut counterexamples: Vec<Counterexample> = Vec::new();
    let mut pins: Vec<String> = Vec::new();
    let mut param_names: Vec<String> = Vec::new();
    for (name, ret) in candidates {
        let is_param = name.ends_with('!');
        match &*ret {
            // Vec: reconstruct its elements by querying its Seq view (see helper).
            TypX::Named(sort) if sort.starts_with("alloc!vec.Vec<") => {
                if let Some((cex, vec_pins)) = query_vec_counterexample(context, &name, sort) {
                    counterexamples.push(cex);
                    if is_param {
                        pins.extend(vec_pins);
                        // The raw Vec constant is itself the ens argument.
                        param_names.push(name.clone());
                    }
                }
            }
            _ => {
                // Simple scalar (Int/Bool/...): evaluate the variable directly.
                let raw = context.eval_expr(parse_smt_term(&name));
                if is_param {
                    // The raw eval output is already valid SMT (e.g. `8`, `(- 5)`,
                    // `true`), so it can be pinned verbatim.
                    pins.push(format!("(= {} {})", name, raw.trim()));
                    param_names.push(name.clone());
                }
                counterexamples.push(Counterexample {
                    var_name: name.clone(),
                    var_value: clean_smt_value(&raw),
                    var_type: None,
                    classification: None,
                });
            }
        }
    }
    (counterexamples, pins, param_names)
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
    // element type is the token between "Vec<" and the following "."
    let after = sort.split_once("Vec<")?.1;
    let elem_raw = after.split('.').next()?;
    let (smt_elem_ty, rust_elem_ty) = int_type_smt_and_rust(elem_raw)?;

    // The Seq view of the Vec, shared by the length and index queries.
    let view = format!(
        "(vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ {ety} $ ALLOCATOR_GLOBAL) (Poly%{sort} {name}))",
        ety = smt_elem_ty,
        sort = sort,
        name = name,
    );

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

/// Find the SMT `ens%...` function of the *user* function under verification
/// (i.e. not one injected by a library crate), returning its mangled name and
/// arity. Returns `None` if there is not exactly one such function (ambiguous or
/// absent), in which case confirmation is skipped.
fn find_user_ens(context: &Context) -> Option<(String, usize)> {
    const LIBS: [&str; 6] =
        ["vstd!", "alloc!", "core!", "std!", "builtin!", "verus_builtin!"];
    let mut found: Option<(String, usize)> = None;
    for (name, decl) in context.typing.decls.map().iter() {
        let n: &str = name.as_str();
        let Some(rest) = n.strip_prefix("ens%") else { continue };
        if LIBS.iter().any(|l| rest.starts_with(l)) {
            continue;
        }
        if let crate::typecheck::DeclaredX::Fun { params, .. } = &**decl {
            if found.is_some() {
                return None; // ambiguous: more than one user ens function
            }
            found = Some((n.to_string(), params.len()));
        }
    }
    found
}

/// Confirmation stage: assert the user function's post-condition *holds* under
/// the pinned witness. If that is `unsat`, the witness provably violates the
/// post-condition, so it is a genuine failing input.
///
/// The ens function's argument order (parameters..., return) is a VIR-level
/// convention not recoverable from the SMT declaration alone, so for the common
/// binary-signature case we try both orderings and accept an `unsat` from
/// either. Because only `unsat` upgrades the verdict to REAL, a wrong ordering
/// can at worst leave the result inconclusive — it can never fabricate a REAL.
fn confirm_real(context: &mut Context, pins: &[String], param_names: &[String]) -> bool {
    let Some((ens, arity)) = find_user_ens(context) else { return false };
    if param_names.is_empty() || param_names.len() != arity {
        // Can't build a well-typed application without an exact argument match.
        return false;
    }

    let mut orders: Vec<Vec<String>> = vec![param_names.to_vec()];
    if arity == 2 {
        orders.push(vec![param_names[1].clone(), param_names[0].clone()]);
    }

    for order in orders {
        let ens_holds = format!("({} {})", ens, order.join(" "));
        let mut terms: Vec<String> = pins.to_vec();
        terms.push(ens_holds);
        if check_sat_with(context, &terms) == SatResult::Unsat {
            return true;
        }
    }
    false
}

/// Two-stage Z3-side refinement. See the module docs. Returns the classification
/// for the whole model (the caller stamps it onto every extracted variable).
pub(crate) fn refine_and_classify(
    context: &mut Context,
    pins: &[String],
    param_names: &[String],
) -> CexClassification {
    if pins.is_empty() {
        return CexClassification::Inconclusive;
    }
    // Stage 1: refutation — pin the full witness and re-check the failing query.
    match check_sat_with(context, pins) {
        SatResult::Sat => CexClassification::Real,
        SatResult::Unsat => CexClassification::Spurious,
        SatResult::Unknown => {
            // Stage 2: confirmation — prove the post-condition can't hold here.
            if confirm_real(context, pins, param_names) {
                CexClassification::Real
            } else {
                CexClassification::Inconclusive
            }
        }
    }
}
