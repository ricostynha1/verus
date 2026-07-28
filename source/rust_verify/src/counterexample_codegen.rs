//! Counterexample codegen: given a VIR function + Z3 counterexample values,
//! generate a test .rs file that runs the counterexample at runtime to classify
//! it as REAL BUG or SPURIOUS.

use air::context::Counterexample;
use std::path::{Path, PathBuf};
use vir::ast::{Dt, IntRange, Typ, TypX, VarIdent};
use vir::sst::FunctionSst;

/// Extract file path from a VIR span's as_string field.
/// Format is like "path/to/file.rs:12:1: 16:2"
pub fn file_path_from_span(span_str: &str) -> Option<PathBuf> {
    // Find the first occurrence of ":<digit>" to split off the location
    let bytes = span_str.as_bytes();
    for i in 0..bytes.len().saturating_sub(1) {
        if bytes[i] == b':' && bytes[i + 1].is_ascii_digit() {
            return Some(PathBuf::from(&span_str[..i]));
        }
    }
    None
}

/// Information extracted from VIR about a function's parameters
struct ParamInfo {
    name: String,
    typ_str: String,
}

/// Extract a Rust type string from a VIR Typ.
///
/// Used by two consumers: (1) the counterexample role/type push-down records each
/// variable's Rust type for the Z3-side refinement's rendering (e.g. `char` vs
/// `Int`); (2) `generate_test_file` emits it as the type of the counterexample
/// input `let` bindings in the executable-contract witness (T3).
pub fn typ_to_rust_string(typ: &Typ) -> String {
    match &**typ {
        TypX::Bool => "bool".to_string(),
        TypX::Int(range) => match range {
            IntRange::Int => "int".to_string(),
            IntRange::Nat => "nat".to_string(),
            IntRange::U(n) => format!("u{}", n),
            IntRange::I(n) => format!("i{}", n),
            IntRange::USize => "usize".to_string(),
            IntRange::ISize => "isize".to_string(),
            IntRange::Char => "char".to_string(),
        },
        // Vec<T> is a datatype whose path ends in "Vec"; render its element type.
        TypX::Datatype(Dt::Path(path), targs, _) => {
            let is_vec = path.segments.last().map(|s| s.as_str()) == Some("Vec");
            let is_string = path.segments.last().map(|s| s.as_str()) == Some("String");
            match (is_vec, is_string, targs.first()) {
                (true, _, Some(elem)) => format!("Vec<{}>", typ_to_rust_string(elem)),
                (_, true, _) => "String".to_string(),
                _ => "/* unsupported type */".to_string(),
            }
        }
        // A tuple `(A, B, ..)` — render each field type so the counterexample
        // push-down carries per-field types (used to reconstruct/print fields).
        TypX::Datatype(Dt::Tuple(_), targs, _) => {
            let fields =
                targs.iter().map(|t| typ_to_rust_string(t)).collect::<Vec<_>>().join(", ");
            format!("({})", fields)
        }
        _ => "/* unsupported type */".to_string(),
    }
}

/// Extract param name string from VarIdent
fn var_ident_to_string(v: &VarIdent) -> String {
    (*v.0).clone()
}

/// Get ParamInfo list from VIR function params (exec-mode only)
fn get_params(function: &FunctionSst) -> Vec<ParamInfo> {
    function
        .x
        .pars
        .iter()
        .filter(|p| p.x.mode == vir::ast::Mode::Exec)
        .map(|p| ParamInfo {
            name: var_ident_to_string(&p.x.name),
            typ_str: typ_to_rust_string(&p.x.typ),
        })
        .collect()
}

/// Get return param info
fn get_ret(function: &FunctionSst) -> ParamInfo {
    ParamInfo {
        name: var_ident_to_string(&function.x.ret.x.name),
        typ_str: typ_to_rust_string(&function.x.ret.x.typ),
    }
}

/// Get the short function name (last segment of path)
fn get_fn_name(function: &FunctionSst) -> String {
    let segments = &function.x.name.path.segments;
    if let Some(last) = segments.last() {
        (**last).clone()
    } else {
        "unknown_fn".to_string()
    }
}

/// Parse the source file to extract:
/// - requires expression text
/// - ensures expression text  
/// - full function signature + body text
///
/// Uses the function name to locate the function in the source.
fn extract_source_parts(source: &str, fn_name: &str) -> Option<SourceParts> {
    let lines: Vec<&str> = source.lines().collect();

    // Find the line with `fn <fn_name>`
    let fn_line_idx = lines.iter().position(|l| {
        l.contains(&format!("fn {}", fn_name)) && !l.trim().starts_with("//")
    })?;

    // Find requires/ensures clauses between fn signature and opening brace
    let mut requires_text = String::new();
    let mut ensures_text = String::new();
    let mut body_start_idx = fn_line_idx;
    let mut in_requires = false;
    let mut in_ensures = false;

    for i in (fn_line_idx + 1)..lines.len() {
        // Strip line comments so `// ...` notes inside the requires/ensures
        // clauses don't get folded into (and comment out) the spec expression.
        let line = match lines[i].find("//") {
            Some(c) => &lines[i][..c],
            None => lines[i],
        };
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        if trimmed.starts_with("requires") {
            in_requires = true;
            in_ensures = false;
            let rest = trimmed.strip_prefix("requires").unwrap().trim();
            if !rest.is_empty() {
                requires_text.push_str(rest);
            }
            continue;
        }
        if trimmed.starts_with("ensures") {
            in_ensures = true;
            in_requires = false;
            let rest = trimmed.strip_prefix("ensures").unwrap().trim();
            if !rest.is_empty() {
                ensures_text.push_str(rest);
            }
            continue;
        }
        // `decreases`/`recommends`/`invariant` clauses are not part of the
        // requires/ensures spec and must not be folded into them (e.g. a
        // recursive fn's `decreases n` would otherwise leak into the ensures
        // body and break the generated spec fn). Stop accumulating at them.
        if trimmed.starts_with("decreases")
            || trimmed.starts_with("recommends")
            || trimmed.starts_with("invariant")
        {
            in_requires = false;
            in_ensures = false;
            continue;
        }
        if trimmed == "{" || trimmed.starts_with("{") {
            body_start_idx = i;
            break;
        }

        // Continue accumulating multi-line requires/ensures
        if in_requires {
            if !requires_text.is_empty() {
                requires_text.push_str(" ");
            }
            requires_text.push_str(trimmed);
        }
        if in_ensures {
            if !ensures_text.is_empty() {
                ensures_text.push_str(" ");
            }
            ensures_text.push_str(trimmed);
        }
    }

    // Find the matching closing brace for the function body
    let mut brace_depth = 0;
    let mut body_end_idx = body_start_idx;
    for i in body_start_idx..lines.len() {
        for ch in lines[i].chars() {
            if ch == '{' {
                brace_depth += 1;
            }
            if ch == '}' {
                brace_depth -= 1;
                if brace_depth == 0 {
                    body_end_idx = i;
                    break;
                }
            }
        }
        if brace_depth == 0 && i > body_start_idx {
            break;
        }
    }

    // Extract the body text (between { and })
    let body_lines: Vec<&str> = lines[body_start_idx + 1..body_end_idx].to_vec();
    let body_text = body_lines.join("\n");

    // If no requires found, default to true
    if requires_text.is_empty() {
        requires_text = "true".to_string();
    }
    // Strip trailing comma if present
    ensures_text = ensures_text.trim_end_matches(',').trim().to_string();
    requires_text = requires_text.trim_end_matches(',').trim().to_string();

    Some(SourceParts { requires_text, ensures_text, body_text })
}

struct SourceParts {
    requires_text: String,
    ensures_text: String,
    body_text: String,
}

/// Transform ensures text to handle Verus spec-mode integer promotion.
/// In Verus spec mode, arithmetic promotes to `int`, so `y == x + 1` type-checks
/// even when y: u64 and x: u32. In exec mode (exec_spec_unverified!), we need
/// explicit casts. This transforms `<ret> == <expr>` to `<ret> == (<expr>) as <ret_type>`
/// when the return type differs from parameter types.
fn fixup_ensures_for_exec(
    ensures_text: &str,
    ret: &ParamInfo,
    params: &[ParamInfo],
) -> String {
    // Only apply when return type differs from all param types
    let ret_type_differs = params.iter().all(|p| p.typ_str != ret.typ_str);
    if !ret_type_differs {
        return ensures_text.to_string();
    }

    // Match pattern: <ret_name> == <expr>
    let prefix = format!("{} == ", ret.name);
    if let Some(rhs) = ensures_text.strip_prefix(&prefix) {
        // Don't double-cast if already cast
        if rhs.ends_with(&format!("as {}", ret.typ_str)) {
            return ensures_text.to_string();
        }
        format!("{} == ({}) as {}", ret.name, rhs, ret.typ_str)
    } else {
        ensures_text.to_string()
    }
}

/// Transform chained inequalities like "0 < a < 1000" into "(0 < a) && (a < 1000)"
/// for compatibility with standard Rust parsing in exec_spec_unverified!
fn expand_chained_inequalities(expr: &str) -> String {
    let ops = ["<=", ">=", "==", "!=", "<", ">"];
    let mut result = expr.to_string();
    let mut changed = true;
    
    while changed {
        changed = false;
        
        for (i, _) in result.char_indices() {
            let slice = &result[i..];
            
            // 1. Find the first operator
            let mut found_op1 = None;
            for op in ops {
                if slice.starts_with(op) {
                    found_op1 = Some(op);
                    break;
                }
            }
            
            if let Some(op1) = found_op1 {
                let left = &result[..i];
                let rest1 = &result[i + op1.len()..];
                
                // Isolate the left expression from any previous logic (like && or ||)
                let mut left_start = 0;
                for (k, c) in left.char_indices().rev() {
                    if c == '&' || c == '|' || c == ',' || c == ';' || c == '=' || c == '(' || c == '[' || c == '{' {
                        left_start = k + c.len_utf8();
                        break;
                    }
                }
                let prefix = &left[..left_start];
                let left_expr = &left[left_start..];
                
                // 2. Find the middle identifier (safely skipping whitespace)
                let mid_start = rest1.find(|c: char| !c.is_whitespace()).unwrap_or(rest1.len());
                let rest1_trim = &rest1[mid_start..];
                
                let mut mid_len = 0;
                for (j, c) in rest1_trim.char_indices() {
                    if !c.is_alphanumeric() && c != '_' {
                        mid_len = j;
                        break;
                    }
                }
                
                // If we didn't find a valid identifier, continue scanning
                if mid_len == 0 { continue; } 
                
                let middle = &rest1_trim[..mid_len];
                let rest2 = &rest1_trim[mid_len..];
                
                // 3. Find the second operator (safely skipping whitespace)
                let op2_start = rest2.find(|c: char| !c.is_whitespace()).unwrap_or(rest2.len());
                let rest2_trim = &rest2[op2_start..];
                
                let mut found_op2 = None;
                for op in ops {
                    if rest2_trim.starts_with(op) {
                        found_op2 = Some(op);
                        break;
                    }
                }
                
                // If we found a valid A < B < C chain
                if let Some(op2) = found_op2 {
                    let rest3 = &rest2_trim[op2.len()..];
                    
                    // Isolate the right expression from any subsequent logic
                    let mut right_end = rest3.len();
                    for (k, c) in rest3.char_indices() {
                        if c == '&' || c == '|' || c == ',' || c == ';' || c == '=' || c == ')' || c == ']' || c == '}' {
                            right_end = k;
                            break;
                        }
                    }
                    let right_expr = &rest3[..right_end];
                    let suffix = &rest3[right_end..];
                    
                    // 4. Reassemble with explicit grouping: prefix + (L op1 M) && (M op2 R) + suffix
                    result = format!(
                        "{}({} {} {}) && ({} {} {}){}",
                        prefix,
                        left_expr.trim(),
                        op1,
                        middle,
                        middle,
                        op2,
                        right_expr.trim(),
                        suffix
                    );
                    changed = true;
                    break; // Break the character scan and restart the while loop with the newly expanded string
                }
            }
        }
    }
    
    result
}

/// Match counterexample values to function params by name.
/// The counterexample var_name is like "x!" — strip the "!" suffix to match param names.
fn match_counterexamples(
    params: &[ParamInfo],
    counterexamples: &[Counterexample],
) -> Vec<(String, String, String)> {
    // Returns: (param_name, param_type, value)
    params
        .iter()
        .filter_map(|p| {
            let cex = counterexamples.iter().find(|c| {
                let clean = c.var_name.trim_end_matches('!');
                clean == p.name
            });
            cex.map(|c| {
                // Prefer the type the querying step attached (e.g. "Vec<u32>"); fall
                // back to the type derived from VIR for simple scalars.
                let typ = c.var_type.clone().unwrap_or_else(|| p.typ_str.clone());
                (p.name.clone(), typ, c.var_value.clone())
            })
        })
        .collect()
}

/// If `typ_str` is `Vec<T>`, return `T`. Vec params are the only composite
/// type the codegen currently handles.
fn vec_elem(typ_str: &str) -> Option<&str> {
    typ_str.strip_prefix("Vec<").and_then(|s| s.strip_suffix('>')).map(|s| s.trim())
}

/// Types whose spec view is a `Seq` and therefore use the `@` view operator in
/// contracts (so a param named `v` appears as `v@` and must be handled like a
/// Vec): `Vec<T>` and `String`. Returns `true` for those.
fn is_viewed_type(typ_str: &str) -> bool {
    vec_elem(typ_str).is_some() || typ_str == "String"
}

/// Spec-mode type for a param. Spec code cannot mention `Vec`/`String`; the Verus
/// idiom is to write contracts over the `Seq` view (`v@`). So a `Vec<T>` exec
/// param becomes a `Seq<T>` spec param and a `String` becomes `Seq<char>`.
fn spec_param_type(typ_str: &str) -> String {
    match vec_elem(typ_str) {
        Some(elem) => format!("Seq<{}>", elem),
        None if typ_str == "String" => "Seq<char>".to_string(),
        None => typ_str.to_string(),
    }
}

/// Render a counterexample value as a Rust *expression* usable as a `let`
/// initializer for `typ`. Most values are already valid literals; a `String`
/// value comes back as a quoted `&str` literal and needs `.to_string()`.
fn value_as_expr(typ_str: &str, value: &str) -> String {
    if typ_str == "String" {
        format!("{}.to_string()", value)
    } else {
        value.to_string()
    }
}

/// Whether a Rust type is a primitive scalar (`exec_spec_unverified!` passes
/// these by value; every composite type — tuple/struct/Vec/String — is passed by
/// reference to the generated `exec_*` functions).
fn is_scalar_type(t: &str) -> bool {
    matches!(t, "bool" | "char" | "int" | "nat" | "usize" | "isize")
        || ((t.starts_with('u') || t.starts_with('i')) && t[1..].parse::<u32>().is_ok())
}

/// Remove the Verus view operator: `name@` -> `name`, for the given names.
/// Once a Vec param is retyped as its `Seq` view, `v@` in the source contract
/// (which was `Vec::view`) is just the parameter itself. Longer names first so
/// e.g. `new_v@` is handled before `v@` would match its suffix.
fn strip_view_ops(text: &str, names: &[String]) -> String {
    let mut ordered = names.to_vec();
    ordered.sort_by_key(|n| std::cmp::Reverse(n.len()));
    let mut out = text.to_string();
    for n in &ordered {
        out = out.replace(&format!("{}@", n), n);
    }
    out
}

/// Join top-level (paren/bracket-depth 0) comma-separated clauses with `&&`.
/// Verus writes multiple requires/ensures as comma-separated conjuncts, but a
/// spec fn body must be a single boolean expression. Commas inside call
/// arguments (e.g. `upper_bound(v, 10)`) are left untouched.
fn commas_to_and(text: &str) -> String {
    let mut out = String::new();
    let mut depth = 0i32;
    for ch in text.chars() {
        match ch {
            '(' | '[' | '{' => {
                depth += 1;
                out.push(ch);
            }
            ')' | ']' | '}' => {
                depth -= 1;
                out.push(ch);
            }
            ',' if depth == 0 => out.push_str(" && "),
            _ => out.push(ch),
        }
    }
    out
}

/// A spec fn definition extracted verbatim from the source.
struct SpecFnRaw {
    name: String,
    params: String,
    ret: String,
    body: String,
}

/// Extract `spec fn <name>(params) -> ret { body }` from the source, matching
/// parentheses and braces so nested calls/blocks are handled.
fn extract_spec_fn(source: &str, name: &str) -> Option<SpecFnRaw> {
    let needle = format!("spec fn {}", name);
    let start = source.find(&needle)?;
    let after = &source[start + needle.len()..];

    // Parameter list: from '(' to its matching ')'.
    let popen = after.find('(')?;
    let bytes = after.as_bytes();
    let (mut depth, mut i, mut pclose) = (0i32, popen, None);
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    pclose = Some(i);
                    break;
                }
            }
            _ => {}
        }
        i += 1;
    }
    let pclose = pclose?;
    let params = after[popen + 1..pclose].trim().to_string();

    // Return type: between ')' and the body's '{'.
    let rest = &after[pclose + 1..];
    let bopen = rest.find('{')?;
    let ret = rest[..bopen].trim().trim_start_matches("->").trim().to_string();

    // Body: from '{' to its matching '}'.
    let rbytes = rest.as_bytes();
    let (mut d, mut j, mut bclose) = (0i32, bopen, None);
    while j < rbytes.len() {
        match rbytes[j] {
            b'{' => d += 1,
            b'}' => {
                d -= 1;
                if d == 0 {
                    bclose = Some(j);
                    break;
                }
            }
            _ => {}
        }
        j += 1;
    }
    let bclose = bclose?;
    let body = rest[bopen + 1..bclose].trim().to_string();

    Some(SpecFnRaw { name: name.to_string(), params, ret, body })
}

/// Collect identifiers used in call position (`foo(`), excluding method calls
/// (`.foo(`) and quantifier keywords.
fn called_idents(expr: &str) -> Vec<String> {
    let bytes = expr.as_bytes();
    let mut res = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let s = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let mut k = i;
            while k < bytes.len() && bytes[k] == b' ' {
                k += 1;
            }
            if k < bytes.len() && bytes[k] == b'(' {
                let prev = if s > 0 { bytes[s - 1] } else { b' ' };
                if prev != b'.' {
                    let id = &expr[s..i];
                    if !matches!(id, "forall" | "exists" | "vec") {
                        res.push(id.to_string());
                    }
                }
            }
        } else {
            i += 1;
        }
    }
    res
}

/// Find the spec fns (transitively) referenced by the given expressions and
/// present in the source. Order within the returned list does not matter — the
/// generated exec fns may reference each other regardless of position.
fn referenced_spec_fns(source: &str, exprs: &[&str]) -> Vec<SpecFnRaw> {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut queue: Vec<String> = exprs.iter().flat_map(|e| called_idents(e)).collect();
    let mut found = Vec::new();
    while let Some(name) = queue.pop() {
        if seen.contains(&name) {
            continue;
        }
        seen.insert(name.clone());
        if let Some(def) = extract_spec_fn(source, &name) {
            queue.extend(called_idents(&def.body));
            found.push(def);
        }
    }
    found
}

/// Split a spec-code expression at the top-level occurrences of `sep`.
fn split_top_level<'a>(expr: &'a str, sep: &str) -> Vec<&'a str> {
    let bytes = expr.as_bytes();
    let sbytes = sep.as_bytes();
    let mut parts = Vec::new();
    let (mut depth, mut i, mut last) = (0i32, 0usize, 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            _ => {}
        }
        if depth == 0 && expr[i..].as_bytes().starts_with(sbytes) {
            parts.push(&expr[last..i]);
            i += sbytes.len();
            last = i;
            continue;
        }
        i += 1;
    }
    parts.push(&expr[last..]);
    parts
}

/// Rewrite a single range guard so every quantified variable is bounded on both
/// sides, as `exec_spec_unverified!` requires. A monotone chain like
/// `0 <= i <= j < v.len()` becomes `0 <= i < v.len() && i <= j < v.len()`.
/// Conjuncts that are not such chains are left unchanged.
fn normalize_range_guard(guard: &str, vars: &[String]) -> String {
    let ops = ["<=", ">=", "<", ">"];
    split_top_level(guard, "&&")
        .into_iter()
        .map(|conj| {
            let conj = conj.trim();
            // Tokenize into terms separated by top-level relational ops.
            let bytes = conj.as_bytes();
            let (mut depth, mut i, mut last) = (0i32, 0usize, 0usize);
            let mut terms: Vec<String> = Vec::new();
            let mut chain_ops: Vec<&str> = Vec::new();
            while i < bytes.len() {
                match bytes[i] {
                    b'(' | b'[' | b'{' => depth += 1,
                    b')' | b']' | b'}' => depth -= 1,
                    _ => {}
                }
                if depth == 0 {
                    if let Some(op) = ops.iter().find(|op| conj[i..].starts_with(**op)) {
                        terms.push(conj[last..i].trim().to_string());
                        chain_ops.push(op);
                        i += op.len();
                        last = i;
                        continue;
                    }
                }
                i += 1;
            }
            terms.push(conj[last..].trim().to_string());

            // Need >= 2 ops (>= 3 terms) and every interior term a quant var.
            let interior = &terms[1..terms.len().saturating_sub(1)];
            let is_chain = chain_ops.len() >= 2
                && !interior.is_empty()
                && interior.iter().all(|t| vars.iter().any(|v| v == t));
            if !is_chain {
                return conj.to_string();
            }
            let k = terms.len() - 1;
            let upper = &terms[k];
            let upper_op = chain_ops[k - 1];
            (1..k)
                .map(|t| {
                    format!("{} {} {} {} {}", terms[t - 1], chain_ops[t - 1], terms[t], upper_op, upper)
                })
                .collect::<Vec<_>>()
                .join(" && ")
        })
        .collect::<Vec<_>>()
        .join(" && ")
}

/// Normalize a spec-fn body containing a single leading `forall`/`exists`
/// quantifier into a form `exec_spec_unverified!` accepts: quantified vars get a
/// concrete `usize` type, range guards are split per-variable, and `Seq`
/// indexing by a quantified var gets the required `as int` cast (`v[i]` ->
/// `v[i as int]`). Bodies that are not a single quantifier are returned as-is.
fn normalize_quantifier_body(body: &str) -> String {
    let body = body.trim();
    let kind = if body.starts_with("forall") {
        "forall"
    } else if body.starts_with("exists") {
        "exists"
    } else {
        return body.to_string();
    };

    let rest = body[kind.len()..].trim_start();
    if !rest.starts_with('|') {
        return body.to_string();
    }
    let close = match rest[1..].find('|') {
        Some(c) => c + 1,
        None => return body.to_string(),
    };
    let decls = &rest[1..close];
    let tail = rest[close + 1..].trim_start();
    // Drop an optional trigger annotation `#![ ... ]`.
    let tail = if let Some(t) = tail.strip_prefix("#![") {
        match t.find(']') {
            Some(end) => t[end + 1..].trim_start(),
            None => tail,
        }
    } else {
        tail
    };

    // Quantified variable names, with their types forced to usize.
    let mut vars = Vec::new();
    let new_decls = decls
        .split(',')
        .map(|d| {
            let name = d.split(':').next().unwrap_or("").trim().to_string();
            if !name.is_empty() {
                vars.push(name.clone());
            }
            format!("{}: usize", name)
        })
        .collect::<Vec<_>>()
        .join(", ");

    // forall: `guard ==> consequent`; exists: `guard && body`.
    let sep = if kind == "forall" { "==>" } else { "&&" };
    let split = split_top_level(tail, sep);
    let (guard, consequent) = if split.len() >= 2 {
        (split[0].trim().to_string(), split[1..].join(sep).trim().to_string())
    } else {
        (String::new(), tail.trim().to_string())
    };

    let mut new_guard = normalize_range_guard(&guard, &vars);
    let mut new_consequent = consequent;
    // Seq indexing by a quantified var needs an `int` index.
    for v in &vars {
        let from = format!("[{}]", v);
        let to = format!("[{} as int]", v);
        new_guard = new_guard.replace(&from, &to);
        new_consequent = new_consequent.replace(&from, &to);
    }

    if guard.is_empty() {
        format!("{} |{}| {}", kind, new_decls, new_consequent)
    } else {
        format!("{} |{}| {} {} {}", kind, new_decls, new_guard, sep, new_consequent)
    }
}

/// Generate the counterexample test file content.
pub fn generate_test_file(
    function: &FunctionSst,
    counterexamples: &[Counterexample],
    source_path: &Path,
) -> Result<(PathBuf, String), String> {
    let source =
        std::fs::read_to_string(source_path).map_err(|e| format!("read source: {:?}", e))?;

    let fn_name = get_fn_name(function);
    let params = get_params(function);
    let ret = get_ret(function);

    // The executable-contract witness validates by evaluating `ensures` on the
    // real body's output. Functions with no return binder / unit return (their
    // failure is a bare `assert`, e.g. ex6/ex11 — the return name is an internal
    // `%`-mangled placeholder) have no output-vs-ensures contract to check, so
    // skip them. They stay covered by the Z3-side classifier only.
    if ret.name.contains('%') || ret.typ_str == "()" {
        return Err(format!(
            "{}: assert-failure / unit-return function has no ensures contract to \
             validate at runtime (Z3-side classifier only)",
            fn_name
        ));
    }

    let parts = extract_source_parts(&source, &fn_name)
        .ok_or_else(|| format!("could not find fn {} in source", fn_name))?;

    // No `ensures` clause (e.g. an assert-only proof) → nothing to validate.
    if parts.ensures_text.trim().is_empty() {
        return Err(format!(
            "{}: no ensures clause to validate at runtime (Z3-side classifier only)",
            fn_name
        ));
    }

    let matched = match_counterexamples(&params, counterexamples);
    if matched.is_empty() {
        return Err("no counterexample values matched function params".to_string());
    }

    // Bail cleanly on types the codegen cannot render as a valid Rust literal
    // yet (e.g. a user `struct`, whose value would need braced-field rendering
    // `Point { x: .., y: .. }` and an emitted struct definition). Emitting a
    // `/* unsupported type */` placeholder would produce a non-compiling file.
    if let Some((name, typ, _)) =
        matched.iter().find(|(_, typ, _)| typ.contains("unsupported"))
    {
        return Err(format!(
            "{}: param `{}` has unsupported type for witness codegen ({})",
            fn_name, name, typ
        ));
    }

    // Exec-mode signature (function under test): keeps the real types (Vec<T>).
    let params_sig: String = params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.typ_str))
        .collect::<Vec<_>>()
        .join(", ");

    // Spec-mode signatures: Vec params become their Seq view type.
    let spec_params_sig: String = params
        .iter()
        .map(|p| format!("{}: {}", p.name, spec_param_type(&p.typ_str)))
        .collect::<Vec<_>>()
        .join(", ");
    let spec_params_with_ret: String = {
        let mut v: Vec<String> =
            params.iter().map(|p| format!("{}: {}", p.name, spec_param_type(&p.typ_str))).collect();
        v.push(format!("{}: {}", ret.name, spec_param_type(&ret.typ_str)));
        v.join(", ")
    };

    // Names of viewed (Vec/String) params/ret — these need view (`@`)/reference
    // handling (their spec type is a `Seq`).
    let vec_names: Vec<String> = params
        .iter()
        .chain(std::iter::once(&ret))
        .filter(|p| is_viewed_type(&p.typ_str))
        .map(|p| p.name.clone())
        .collect();

    // Args passed to `_ensures` from the external_body fn: viewed args as `@`.
    let ensures_view_args: String = params
        .iter()
        .chain(std::iter::once(&ret))
        .map(|p| {
            if is_viewed_type(&p.typ_str) {
                format!("{}@", p.name)
            } else {
                p.name.clone()
            }
        })
        .collect::<Vec<_>>()
        .join(", ");

    // Generate output path
    let stem = source_path.file_stem().unwrap_or_default().to_string_lossy();
    let output_path = source_path.with_file_name(format!("{}_counterexample_test.rs", stem));

    // Build the test file
    let mut out = String::new();

    // Header
    out.push_str("use vstd::prelude::*;\n");
    out.push_str("use vstd::contrib::exec_spec::*;\n\n");
    out.push_str("verus! {\n\n");

    // Function with external_body (same body, ensures replaced by named fn)
    out.push_str(&format!(
        "#[verifier::external_body]\nfn {}({}) -> ({}: {})\n    ensures {}_ensures({})\n{{\n{}\n}}\n\n",
        fn_name,
        params_sig,
        ret.name,
        ret.typ_str,
        fn_name,
        ensures_view_args,
        parts.body_text,
    ));

    // Rewrite the contract text into spec-fn bodies:
    // strip view ops on Vec params (now Seq-typed), join comma clauses, and for
    // ensures apply the exec-mode integer-promotion cast.
    let requires_body = expand_chained_inequalities(&commas_to_and(&strip_view_ops(
        &parts.requires_text,
        &vec_names,
    )));
    let ensures_stripped = strip_view_ops(&parts.ensures_text, &vec_names);
    let ensures_body = expand_chained_inequalities(&commas_to_and(&fixup_ensures_for_exec(
        &ensures_stripped,
        &ret,
        &params,
    )));

    // Helper spec fns referenced by the contract must also be emitted (with
    // exec-compatible quantifiers) so the macro can generate their exec versions.
    let helpers = referenced_spec_fns(&source, &[requires_body.as_str(), ensures_body.as_str()]);

    // exec_spec_unverified! block
    out.push_str("exec_spec_unverified! {\n");
    for h in &helpers {
        out.push_str(&format!(
            "    spec fn {}({}) -> {} {{\n        {}\n    }}\n\n",
            h.name,
            h.params,
            h.ret,
            normalize_quantifier_body(&h.body)
        ));
    }
    out.push_str(&format!(
        "    spec fn {}_requires({}) -> bool {{\n        {}\n    }}\n\n",
        fn_name, spec_params_sig, requires_body
    ));
    out.push_str(&format!(
        "    spec fn {}_ensures({}) -> bool {{\n        {}\n    }}\n",
        fn_name, spec_params_with_ret, ensures_body
    ));
    out.push_str("}\n\n");

    out.push_str("} // verus\n\n");

    // Main function with counterexample test
    out.push_str("fn main() {\n");

    // Declare counterexample values (String literals get `.to_string()`).
    for (name, typ, value) in &matched {
        out.push_str(&format!("    let {}: {} = {};\n", name, typ, value_as_expr(typ, value)));
    }
    // A `String` param's spec view is `Seq<char>`, which `exec_spec_unverified!`
    // lowers to `&[char]`. `&String` does NOT coerce to `&[char]` (String derefs
    // to `&str`), so build an explicit `Vec<char>` view to borrow from.
    for p in params.iter().chain(std::iter::once(&ret)) {
        if p.typ_str == "String" {
            out.push_str(&format!(
                "    let {n}_chars: Vec<char> = {n}.chars().collect();\n",
                n = p.name
            ));
        }
    }
    out.push_str("\n");

    // Call-site argument lists.
    //  - Exec spec fns (`by_ref = true`): scalars go by value; every composite
    //    goes by reference. A `Vec<T>` passes as `&v` (coerces to `&[T]`); a
    //    `String` passes its char view `&v_chars`.
    //  - The function under test (`by_ref = false`): consumes owned args, so
    //    non-`Copy` collections (Vec/String) are `.clone()`d to stay available
    //    for the ensures check; scalars/tuples pass by value.
    let arg = |p: &ParamInfo, by_ref: bool| -> String {
        let scalar = is_scalar_type(&p.typ_str);
        match (scalar, by_ref) {
            (true, _) => p.name.clone(),
            (false, true) if p.typ_str == "String" => format!("&{}_chars", p.name),
            (false, true) => format!("&{}", p.name),
            (false, false) if is_viewed_type(&p.typ_str) => format!("{}.clone()", p.name),
            (false, false) => p.name.clone(),
        }
    };
    let requires_args: String =
        params.iter().map(|p| arg(p, true)).collect::<Vec<_>>().join(", ");
    let call_args: String =
        params.iter().map(|p| arg(p, false)).collect::<Vec<_>>().join(", ");
    let ensures_args: String = params
        .iter()
        .chain(std::iter::once(&ret))
        .map(|p| arg(p, true))
        .collect::<Vec<_>>()
        .join(", ");

    // Judge in two guarded phases so that a *panic* is classified correctly
    // instead of being blanket-labeled SPURIOUS (the T5B false-negative fix):
    //
    //  Phase 1 — evaluate `requires` alone. If it does not hold (or panics),
    //    the Z3 model picked an input outside the precondition, so the witness
    //    could never legitimately occur -> SPURIOUS.
    //
    //  Phase 2 — with preconditions established, run the *real body* under
    //    catch_unwind. Verus's proof obligations include no-overflow / no
    //    out-of-bounds / no-div-by-zero, so ANY panic on a valid input is a
    //    genuine violation of a checked obligation -> REAL BUG (this is exactly
    //    the arithmetic-underflow case that used to be downgraded to SPURIOUS).
    //    If the body runs to completion, judge by the ensures clause.
    out.push_str(&format!(
        "    let preconds_hold = std::panic::catch_unwind(|| exec_{}_requires({}))\n",
        fn_name, requires_args
    ));
    out.push_str("        .unwrap_or(false);\n");
    out.push_str("    if !preconds_hold {\n");
    out.push_str(
        "        eprintln!(\"SPURIOUS: Z3 values violate preconditions\");\n",
    );
    out.push_str("        std::process::exit(0);\n");
    out.push_str("    }\n\n");

    out.push_str("    let run_result = std::panic::catch_unwind(|| {\n");
    out.push_str(&format!(
        "        let {} = {}({});\n",
        ret.name, fn_name, call_args
    ));
    out.push_str(&format!(
        "        let ensures_holds = exec_{}_ensures({});\n",
        fn_name, ensures_args
    ));
    out.push_str(&format!(
        "        ({}, ensures_holds)\n",
        ret.name
    ));
    out.push_str("    });\n\n");

    // Match block (fixed template)
    out.push_str("    match run_result {\n");
    out.push_str("        Err(_) => {\n");
    out.push_str(
        "            eprintln!(\"REAL BUG: panicked on valid input (overflow/underflow/index -- a checked obligation Verus proves absent)\");\n",
    );
    out.push_str("            std::process::exit(1);\n");
    out.push_str("        }\n");
    out.push_str(&format!(
        "        Ok(({}, ensures_holds)) => {{\n",
        ret.name
    ));
    out.push_str("            if !ensures_holds {\n");
    out.push_str("                eprintln!(\"REAL BUG: ensures violated\");\n");
    out.push_str("                std::process::exit(1);\n");
    out.push_str("            } else {\n");
    out.push_str(
        "                eprintln!(\"SPURIOUS: ensures holds, counterexample is bogus\");\n",
    );
    out.push_str("                std::process::exit(0);\n");
    out.push_str("            }\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
    out.push_str("}\n");

    Ok((output_path, out))
}

/// Generate the **T3.5 debug reproduction test** (`<stem>_debug_test.rs`).
///
/// This is deliberately *not* a validator: it calls the function under test on
/// the concrete counterexample inputs and (for a scalar output) asserts it equals
/// the counterexample output, so a developer can step through the failing call in
/// a debugger. Because the counterexample `(X -> Y)` was derived from the real
/// body, running `f(X)` reproduces `Y` for BOTH real and spurious counterexamples
/// — the assertion says nothing about real-vs-spurious (that is T3's job).
///
/// It is compiled/run with `verus --compile` (the body may use `vstd`, e.g.
/// `Vec::push`); the emitted file keeps the real body but drops the `requires`/
/// `ensures` contract so nothing is verified — it is a plain runnable binary.
pub fn generate_debug_test_file(
    function: &FunctionSst,
    counterexamples: &[Counterexample],
    source_path: &Path,
) -> Result<(PathBuf, String), String> {
    let source =
        std::fs::read_to_string(source_path).map_err(|e| format!("read source: {:?}", e))?;

    let fn_name = get_fn_name(function);
    let params = get_params(function);
    let ret = get_ret(function);

    // Ghost-only signatures (proof fns) have no exec params / body to run.
    if params.is_empty() {
        return Err(format!("{}: no exec parameters (ghost-only), nothing to reproduce", fn_name));
    }

    let parts = extract_source_parts(&source, &fn_name)
        .ok_or_else(|| format!("could not find fn {} in source", fn_name))?;

    let matched = match_counterexamples(&params, counterexamples);
    if matched.is_empty() {
        return Err("no counterexample values matched function params".to_string());
    }
    if let Some((name, typ, _)) =
        matched.iter().find(|(_, typ, _)| typ.contains("unsupported"))
    {
        return Err(format!(
            "{}: param `{}` has unsupported type for debug codegen ({})",
            fn_name, name, typ
        ));
    }

    // The concrete counterexample output value (return binder, e.g. `r!`).
    let out_value = counterexamples
        .iter()
        .find(|c| c.var_name.trim_end_matches('!') == ret.name)
        .map(|c| c.var_value.clone());

    let params_sig: String = params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.typ_str))
        .collect::<Vec<_>>()
        .join(", ");

    let stem = source_path.file_stem().unwrap_or_default().to_string_lossy();
    let output_path = source_path.with_file_name(format!("{}_debug_test.rs", stem));

    let mut out = String::new();
    out.push_str(
        "// AUTO-GENERATED debug reproduction test (T3.5) — NOT a real/spurious verdict.\n\
         // Runs the function under test on the counterexample inputs so you can step\n\
         // through the failing call in a debugger. The counterexample output is\n\
         // reproduced by construction, so a passing assert here says NOTHING about\n\
         // whether the counterexample is real or spurious (that is the T3 witness's job).\n\
         // Build/run:  verus --compile <this file>  (then run the produced binary).\n\n",
    );
    out.push_str("use vstd::prelude::*;\n\n");
    out.push_str("verus! {\n\n");
    // Real body, contract dropped (external_body so the body is kept verbatim and
    // nothing is verified).
    out.push_str(&format!(
        "#[verifier::external_body]\nfn {}({}) -> (r_out: {})\n{{\n{}\n}}\n\n",
        fn_name, params_sig, ret.typ_str, parts.body_text,
    ));
    out.push_str("} // verus\n\n");

    out.push_str("fn main() {\n");
    for (name, typ, value) in &matched {
        out.push_str(&format!("    let {}: {} = {};\n", name, typ, value_as_expr(typ, value)));
    }
    let call_args: String = params.iter().map(|p| p.name.clone()).collect::<Vec<_>>().join(", ");
    out.push_str(&format!("    let result = {}({});\n", fn_name, call_args));
    out.push_str("    println!(\"result = {:?}\", result);\n");
    // Assert equality for scalar outputs only; composite outputs (Vec/Seq/tuple/
    // String) are printed but not asserted here (element-wise assert is left as a
    // TODO comment to keep this file dependency-light).
    match &out_value {
        Some(v) if !ret.typ_str.starts_with("Vec<") && ret.typ_str != "String" => {
            out.push_str(&format!(
                "    assert_eq!(result, {}); // counterexample output (debug reproduction only)\n",
                value_as_expr(&ret.typ_str, v),
            ));
        }
        Some(v) => {
            out.push_str(&format!(
                "    // counterexample output was: {} (assert element-wise if desired)\n",
                v,
            ));
        }
        None => {}
    }
    out.push_str("}\n");

    Ok((output_path, out))
}
