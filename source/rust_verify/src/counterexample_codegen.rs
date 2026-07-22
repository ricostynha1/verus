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

/// Extract a Rust type string from a VIR Typ
fn typ_to_rust_string(typ: &Typ) -> String {
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
            match (is_vec, targs.first()) {
                (true, Some(elem)) => format!("Vec<{}>", typ_to_rust_string(elem)),
                _ => "/* unsupported type */".to_string(),
            }
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
        let trimmed = lines[i].trim();

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

    let parts = extract_source_parts(&source, &fn_name)
        .ok_or_else(|| format!("could not find fn {} in source", fn_name))?;

    let matched = match_counterexamples(&params, counterexamples);
    if matched.is_empty() {
        return Err("no counterexample values matched function params".to_string());
    }

    // Build param list strings
    let params_sig: String = params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.typ_str))
        .collect::<Vec<_>>()
        .join(", ");

    let _params_names: String = params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(", ");

    let params_with_ret: String = {
        let mut v: Vec<String> = params.iter().map(|p| format!("{}: {}", p.name, p.typ_str)).collect();
        v.push(format!("{}: {}", ret.name, ret.typ_str));
        v.join(", ")
    };

    let params_names_with_ret: String = {
        let mut v: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
        v.push(ret.name.clone());
        v.join(", ")
    };

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
        params_names_with_ret,
        parts.body_text,
    ));

    // Fix up ensures text for exec-mode type correctness
    let ensures_exec = fixup_ensures_for_exec(&parts.ensures_text, &ret, &params);

    // Expand chained inequalities for compatibility with standard Rust parsing
    // (exec_spec_unverified! doesn't use Verus's custom parser)
    let requires_expanded = expand_chained_inequalities(&parts.requires_text);
    let ensures_expanded = expand_chained_inequalities(&ensures_exec);

    // exec_spec_unverified! block
    out.push_str("exec_spec_unverified! {\n");
    out.push_str(&format!(
        "    spec fn {}_requires({}) -> bool {{\n        {}\n    }}\n\n",
        fn_name, params_sig, requires_expanded
    ));
    out.push_str(&format!(
        "    spec fn {}_ensures({}) -> bool {{\n        {}\n    }}\n",
        fn_name, params_with_ret, ensures_expanded
    ));
    out.push_str("}\n\n");

    out.push_str("} // verus\n\n");

    // Main function with counterexample test
    out.push_str("fn main() {\n");

    // Declare counterexample values
    for (name, typ, value) in &matched {
        out.push_str(&format!("    let {}: {} = {};\n", name, typ, value));
    }
    out.push_str("\n");

    // catch_unwind block
    let params_clone: String = params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(", ");
    out.push_str("    let run_result = std::panic::catch_unwind(|| {\n");
    out.push_str(&format!(
        "        let preconds_hold = exec_{}_requires({});\n",
        fn_name, params_clone
    ));
    out.push_str(&format!(
        "        let {} = {}({});\n",
        ret.name, fn_name, params_clone
    ));
    out.push_str(&format!(
        "        let ensures_holds = exec_{}_ensures({});\n",
        fn_name, params_names_with_ret
    ));
    out.push_str(&format!(
        "        (preconds_hold, {}, ensures_holds)\n",
        ret.name
    ));
    out.push_str("    });\n\n");

    // Match block (fixed template)
    out.push_str("    match run_result {\n");
    out.push_str("        Err(_) => {\n");
    out.push_str("            eprintln!(\"SPURIOUS: panicked (overflow or invalid input)\");\n");
    out.push_str("            std::process::exit(0);\n");
    out.push_str("        }\n");
    out.push_str(&format!(
        "        Ok((preconds_hold, {}, ensures_holds)) => {{\n",
        ret.name
    ));
    out.push_str("            if !preconds_hold {\n");
    out.push_str(
        "                eprintln!(\"SPURIOUS: Z3 values violate preconditions\");\n",
    );
    out.push_str("                std::process::exit(0);\n");
    out.push_str("            } else if !ensures_holds {\n");
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
