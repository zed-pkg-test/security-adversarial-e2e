//! Checked monomorphic scalar-Any specialization for single-source browser guests.
//!
//! This is **not** general runtime Any: no dynamic boxes, runtime type tags,
//! imported dispatch, capture, cross-scope mutation, or polymorphic function
//! pointers. A source-local immutable Any literal makes its scalar type
//! statically provable. One direct function accepting one Any parameter may
//! specialize to that same scalar. The ordinary parser/checker/Wasm emitter
//! then enforces type-correct results and guard control flow.
//!
//! Type arms whose tag cannot match the proven scalar are removed; compatible
//! arms lower to guards / catch-alls preserving arm order and once-only match
//! subject evaluation. Unsupported Any shapes fail *before* emitting Wasm.
use std::collections::{BTreeMap, BTreeSet};

use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};

type R<T> = Result<T, Diagnostic>;
const MAX_TYPE_ARMS: usize = 64;

fn word(t: &[Token], i: usize, w: &str) -> bool {
    matches!(t.get(i).map(|x| &x.tok), Some(Tok::Ident(s)) if s == w)
}
fn fail(p: Pos, code: &'static str, description: impl Into<String>) -> Diagnostic {
    Diagnostic::new(p, code, description)
}
fn scalar_lit(t: &Tok) -> Option<&'static str> {
    match t {
        Tok::Int(Some(_)) => Some("int"),
        Tok::Str(_) => Some("string"),
        Tok::Float(_) => Some("float"),
        Tok::Ident(s) if matches!(s.as_str(), "true" | "false") => Some("bool"),
        _ => None,
    }
}
fn scalar_type(s: &str) -> Option<&'static str> {
    match s {
        "int" => Some("int"),
        "bool" | "boolean" => Some("bool"),
        "string" | "String" => Some("string"),
        "float" | "f64" => Some("float"),
        _ => None,
    }
}

fn replace_match_arms(t: &[Token], start: usize, concrete: &str) -> R<(Vec<Token>, usize)> {
    // Exactly 'match known_scalar over on ... -> { ... } ... end'.
    // Braced bodies are self-delimiting; nested scopes are not scanned for
    // misleading 'on' / 'end' identifiers.
    let pos = t[start].pos;
    if start + 2 >= t.len() || !word(t, start + 2, "over") {
        return Err(fail(pos, "E_UNSUPPORTED",
            "monomorphic Any matching requires 'match known_value over'"));
    }
    let mut j = start + 3;
    let mut arms = 0;
    let mut selected = false;
    // Type-arm reachability must be validated before dead arms are pruned
    // by monomorphic specialization. Guarded arms do not cover a tag.
    let mut unguarded_tags = BTreeSet::<(bool, &'static str)>::new();
    let mut wildcard_covered = false;
    let mut output = t[start..start + 3].to_vec();
    while !word(t, j, "end") {
        let Some(head) = t.get(j) else {
            return Err(fail(pos, "E_EOF", "unterminated statically checked Any match"));
        };
        if head.tok == Tok::Eof {
            return Err(fail(pos, "E_EOF", "unterminated statically checked Any match"));
        }
        if !word(t, j, "on") {
            return Err(fail(head.pos, "E_UNSUPPORTED",
                "monomorphic Any match admits only on-is-Type or on-_ arms"));
        }
        arms += 1;
        if arms > MAX_TYPE_ARMS {
            return Err(fail(head.pos, "E_SOURCE_LIMIT", "Any match has too many type arms"));
        }
        let typed = word(t, j + 1, "is");
        let wildcard = word(t, j + 1, "_");
        if !typed && !wildcard {
            return Err(fail(head.pos, "E_UNSUPPORTED",
                "Any match requires a type pattern ('on is int') or wildcard"));
        }
        // Typed arms may negate the type test, and may bind a proven scalar.
        // Bind only after the type test succeeds: failed arms cannot leak names.
        let negated = typed && matches!(t.get(j + 2).map(|x| &x.tok), Some(Tok::Bang));
        let type_at = j + 2 + usize::from(negated);
        let arm_ty = if typed {
            let ty = match t.get(type_at).map(|x| &x.tok) {
                Some(Tok::Ident(s)) => scalar_type(s),
                _ => None,
            };
            Some(ty.ok_or_else(|| fail(head.pos, "E_UNSUPPORTED_TYPE",
                "runtime object type patterns are not implemented; only provable scalar tags are supported"))?)
        } else { None };
        let after_type = if typed { type_at + 1 } else { j + 2 };
        let binding = if typed && word(t, after_type, "as") {
            if !word(t, after_type + 1, "val") {
                return Err(fail(t[after_type].pos, "E_SYNTAX",
                    "type pattern capture requires 'as val name'; mutable and implicit bindings are not implemented"));
            }
            match t.get(after_type + 2) {
                Some(token @ Token { tok: Tok::Ident(name), .. })
                    if name != "_" && name != "when" => Some(token.clone()),
                _ => return Err(fail(t[after_type].pos, "E_SYNTAX",
                    "expected a non-wildcard binding name after 'as val'")),
            }
        } else { None };
        let header_end = after_type + if binding.is_some() { 3 } else { 0 };
        let mut body_open = header_end;
        while body_open < t.len() && t[body_open].tok != Tok::LBrace {
            if t[body_open].tok == Tok::Eof || word(t, body_open, "on") ||
                word(t, body_open, "end") {
                return Err(fail(t[body_open].pos, "E_SYNTAX", "Any type match arm requires a braced body"));
            }
            body_open += 1;
        }
        if body_open == t.len() || body_open == header_end || t[body_open - 1].tok != Tok::Arrow {
            return Err(fail(head.pos, "E_SYNTAX", "Any type match requires '-> { ... }'"));
        }
        let mut depth = 1usize;
        let mut end = body_open + 1;
        while depth > 0 {
            let Some(x) = t.get(end) else {
                return Err(fail(head.pos, "E_EOF", "unclosed Any match arm body"));
            };
            match x.tok {
                Tok::LBrace => depth += 1,
                Tok::RBrace => depth -= 1,
                Tok::Eof => return Err(fail(head.pos, "E_EOF", "unclosed Any match arm body")),
                _ => {}
            }
            if depth > 128 { return Err(fail(head.pos, "E_NESTING", "type arm nesting exceeds 128")); }
            end += 1;
        }
        let compatible = arm_ty.is_none_or(|ty| (ty == concrete) != negated);
        let guarded = word(t, header_end, "when");
        if wildcard_covered {
            return Err(fail(head.pos, "E_MATCH",
                "unreachable Any type arm after an unconditional wildcard"));
        }
        if let Some(ty) = arm_ty {
            if unguarded_tags.contains(&(negated, ty)) {
                return Err(fail(head.pos, "E_MATCH",
                    "unreachable Any type arm: this tag is already unconditionally covered"));
            }
            if !guarded {
                unguarded_tags.insert((negated, ty));
            }
        } else if !guarded {
            wildcard_covered = true;
        }
        if compatible && !selected {
            output.push(t[j].clone()); // on
            if typed {
                output.push(binding.unwrap_or(Token { tok: Tok::Ident("_".into()), pos: t[j + 1].pos }));
                output.extend_from_slice(&t[header_end..end]);
            } else {
                output.extend_from_slice(&t[j + 1..end]);
            }
            if !guarded { selected = true; }
        }
        j = end;
    }
    if arms == 0 {
        return Err(fail(pos, "E_MATCH", "Any match requires at least one arm"));
    }
    if output.len() == 3 {
        return Err(fail(pos, "E_MATCH", "no type arm can match the statically known Any tag"));
    }
    if !selected {
        return Err(fail(pos, "E_MATCH",
            "statically checked Any type match must have an unguarded matching or wildcard arm"));
    }
    output.push(t[j].clone()); // end
    Ok((output, j + 1))
}

/// Reject dynamic, escaped and inconsistent Any values rather than silently
/// treating unrelated runtime types as one scalar. The regular checker
/// validates all rewritten direct calls, actual expressions and branch code.
pub fn lower(mut t: Vec<Token>) -> R<Vec<Token>> {
    if !t.iter().any(|x| word(std::slice::from_ref(x), 0, "Any")) {
        return Ok(t);
    }
    let mut any_locals = BTreeMap::<String, &'static str>::new();
    let mut any_params = Vec::<(usize, String, String)>::new();
    let mut replacement = Vec::<(usize, &'static str)>::new();
    let mut original_any_local_binder: Option<usize> = None;
    for i in 0..t.len() {
        if !word(&t, i, "Any") { continue; }
        // Exact, immutable, literal-evaluable binding: val x: Any = 42;
        if i >= 3 && word(&t, i - 3, "val") &&
            matches!(t[i - 2].tok, Tok::Ident(_)) &&
            t[i - 1].tok == Tok::Colon && t.get(i + 1).is_some_and(|x| x.tok == Tok::Assign)
        {
            let type_name = t.get(i + 2).and_then(|x| scalar_lit(&x.tok))
                .ok_or_else(|| fail(t[i].pos, "E_UNSUPPORTED_TYPE",
                    "Any literal specialization requires a direct immutable scalar initializer"))?;
            if t.get(i + 3).is_none_or(|x| x.tok != Tok::Semi) {
                return Err(fail(t[i].pos, "E_UNSUPPORTED_TYPE",
                    "Any literal specialization does not accept computed or escaped values"));
            }
            let Tok::Ident(name) = &t[i - 2].tok else { unreachable!() };
            if any_locals.insert(name.clone(), type_name).is_some() {
                return Err(fail(t[i].pos, "E_DUPLICATE",
                    "multiple Any bindings of the same name require lexical type analysis"));
            }
            original_any_local_binder = Some(i - 2);
            replacement.push((i, type_name));
            continue;
        }
        // A single monomorphic top-level fnc(Any param) supported by one
        // statically proven immutable Any literal binding at its call site.
        if i >= 3 && word(&t, i - 3, "fnc") &&
            matches!(t[i - 2].tok, Tok::Ident(_)) &&
            t[i - 1].tok == Tok::LParen &&
            matches!(t.get(i + 1).map(|x| &x.tok), Some(Tok::Ident(_))) &&
            t.get(i + 2).is_some_and(|x| x.tok == Tok::RParen)
        {
            let Tok::Ident(name) = &t[i - 2].tok else { unreachable!() };
            let Tok::Ident(param) = &t[i + 1].tok else { unreachable!() };
            any_params.push((i, name.clone(), param.clone()));
            continue;
        }
        return Err(fail(t[i].pos, "E_UNSUPPORTED_TYPE",
            "general Any values, dynamic type tags and polymorphic runtime dispatch require a checked Any ABI"));
    }
    if any_params.len() != 1 || any_locals.len() != 1 {
        return Err(fail(t[0].pos, "E_UNSUPPORTED",
            "bounded Any specialization needs exactly one immutable literal and one direct function accepting Any"));
    }
    let (index, fn_name, param_name) = &any_params[0];
    let (local_name, concrete) = any_locals.iter().next().unwrap();
    if param_name == local_name {
        // The two scopes are independent but both must be specialized to the
        // same concrete type. A second unrelated declaration of this name
        // would require full lexical shadow analysis, so reject it.
        let count = t.iter().enumerate().filter(|(i,x)|
            word(std::slice::from_ref(x), 0, local_name) &&
            (*i != index + 1) &&
            !(*i >= 1 && word(&t, i - 1, "val"))
        ).count();
        if count > 24 {
            return Err(fail(t[*index].pos, "E_SOURCE_LIMIT", "Any specialization use budget exceeded"));
        }
    }
    if t.iter().enumerate().any(|(i,_)| word(&t,i,"fnc") &&
        i+2 < t.len() && word(&t,i+1,fn_name) && i+2!=index-1) {
        return Err(fail(t[*index].pos, "E_DUPLICATE", "monomorphic Any function is overloaded"));
    }
    for i in 0..t.len() {
        if word(&t,i,fn_name) && t.get(i+1).is_some_and(|x| x.tok==Tok::LParen)
            && i != index-2
            && (!word(&t,i+2,local_name) || t.get(i+3).is_none_or(|x| x.tok!=Tok::RParen)) {
            return Err(fail(t[i].pos, "E_UNSUPPORTED",
                "Any monomorphization only supports direct calls using the proven immutable binding"));
        }
    }
    // Prevent a token-level scalar proof for one variable name from being
    // applied to a different lexical variable sharing that spelling.
    // General Any requires an AST/dataflow environment, so shadowing and
    // unrelated parameters are deliberately fail-closed in this subset.
    for (i, token) in t.iter().enumerate() {
        let Tok::Ident(name) = &token.tok else { continue; };
        if name != param_name && name != local_name { continue; }
        let prev = i.checked_sub(1);
        let bound_by_keyword = prev.is_some_and(|at|
            word(&t, at, "val") || word(&t, at, "let") ||
            word(&t, at, "const") || word(&t, at, "mut") ||
            word(&t, at, "for") || word(&t, at, "on") ||
            word(&t, at, "case"));
        let is_other_param = i >= 2 &&
            matches!(&t[i - 1].tok, Tok::Ident(ty) if scalar_type(ty).is_some()) &&
            matches!(t[i - 2].tok, Tok::LParen | Tok::Comma);
        let allowed_local = original_any_local_binder == Some(i) &&
            prev.is_some_and(|at| word(&t, at, "val"));
        let allowed_param = i == *index + 1;
        if (bound_by_keyword || is_other_param) && !allowed_local && !allowed_param {
            return Err(fail(token.pos, "E_UNSUPPORTED",
                "monomorphic Any type proof cannot cross a shadowing binding or unrelated parameter"));
        }
    }
    replacement.push((*index, concrete));
    for (i, typ) in replacement { t[i].tok = Tok::Ident(typ.to_owned()); }
    let mut tags = BTreeMap::new();
    tags.insert(param_name.clone(), *concrete);
    tags.insert(local_name.clone(), *concrete);
    let mut out = Vec::with_capacity(t.len());
    let mut i = 0;
    while i < t.len() {
        if word(&t, i, "match") &&
            t.get(i+1).is_some_and(|x| matches!(x.tok, Tok::Ident(_))) &&
            t.get(i+2).is_some_and(|x| word(std::slice::from_ref(x),0,"over")) &&
            matches!(t.get(i+1).map(|x| &x.tok), Some(Tok::Ident(name)) if tags.contains_key(name)) {
            let Tok::Ident(name) = &t[i+1].tok else { unreachable!() };
            let (expanded,next) = replace_match_arms(&t,i,tags[name])?;
            out.extend(expanded);
            i=next;
            continue;
        }
        // Conditional type capture is a branch-local binding, never a cast.
        // Lower only a stable, statically proven immutable scalar:
        //   if v is T as val n then body fi
        // becomes:
        //   if <known type predicate> then val n: Concrete = v; body fi
        // The ordinary parser/checker enforces lexical visibility and rejects
        // references in else or after fi. No dynamic Any ABI is fabricated.
        if word(&t, i, "if") &&
            t.get(i + 1).is_some_and(|x| matches!(&x.tok, Tok::Ident(name) if tags.contains_key(name))) &&
            word(&t, i + 2, "is")
        {
            let Tok::Ident(subject) = &t[i + 1].tok else { unreachable!() };
            let concrete = tags[subject];
            let negated = t.get(i + 3).is_some_and(|x| x.tok == Tok::Bang);
            let type_at = i + 3 + usize::from(negated);
            let Some(Tok::Ident(type_name)) = t.get(type_at).map(|x| &x.tok) else {
                return Err(fail(t[i + 2].pos, "E_UNSUPPORTED_TYPE",
                    "conditional type capture requires a reifiable scalar type"));
            };
            let expected = scalar_type(type_name).ok_or_else(|| fail(t[type_at].pos,
                "E_UNSUPPORTED_TYPE", "conditional type capture requires a supported scalar type"))?;
            let after_type = type_at + 1;
            if word(&t, after_type, "as") {
                if !word(&t, after_type + 1, "val") {
                    return Err(fail(t[after_type].pos, "E_SYNTAX",
                        "conditional type capture requires 'as val name'"));
                }
                let binder_at = after_type + 2;
                let Some(Tok::Ident(binder)) = t.get(binder_at).map(|x| &x.tok) else {
                    return Err(fail(t[after_type].pos, "E_SYNTAX",
                        "missing conditional capture binder"));
                };
                if binder == "_" || binder == "then" || tags.contains_key(binder) {
                    return Err(fail(t[binder_at].pos, "E_DUPLICATE",
                        "conditional type capture needs a fresh branch-local name"));
                }
                let then_at = binder_at + 1;
                if !word(&t, then_at, "then") {
                    return Err(fail(t[then_at.min(t.len() - 1)].pos, "E_SYNTAX",
                        "conditional type capture requires 'then'"));
                }
                let at = t[i + 1].pos;
                let make = |w: &str| Token { tok: Tok::Ident(w.to_owned()), pos: at };
                out.push(t[i].clone());
                out.push(make(if (concrete == expected) != negated { "true" } else { "false" }));
                out.push(t[then_at].clone());
                out.push(make("val"));
                out.push(t[binder_at].clone());
                out.push(Token { tok: Tok::Colon, pos: at });
                out.push(make(concrete));
                out.push(Token { tok: Tok::Assign, pos: at });
                out.push(t[i + 1].clone());
                out.push(Token { tok: Tok::Semi, pos: at });
                i = then_at + 1;
                continue;
            }
        }
        if word(&t,i,"is") && i > 0 && matches!(t[i-1].tok,Tok::Ident(_)) {
            let Tok::Ident(name) = &t[i-1].tok else { unreachable!() };
            if let Some(actual) = tags.get(name) {
                let negated = matches!(t.get(i + 1).map(|x| &x.tok), Some(Tok::Bang));
                let type_at = i + 1 + usize::from(negated);
                let test = match t.get(type_at).map(|x| &x.tok) {
                    Some(Tok::Ident(type_name)) => scalar_type(type_name),
                    _ => None
                }.ok_or_else(|| fail(t[i].pos,"E_UNSUPPORTED_TYPE",
                    "monomorphic Any 'is' requires a supported scalar type"))?;
                if out.last().is_none_or(|x: &Token| x.tok != t[i-1].tok) {
                    return Err(fail(t[i].pos,"E_SYNTAX","'is' requires the checked scalar operand"));
                }
                out.pop();
                out.push(Token {tok:Tok::Ident(if (*actual == test) != negated {"true"} else {"false"}.into()),pos:t[i-1].pos});
                i = type_at + 1;
                continue;
            }
            return Err(fail(t[i].pos,"E_UNSUPPORTED","'is' on a value without a proven Any type tag is not executable"));
        }
        out.push(t[i].clone());
        i+=1;
    }
    if out.len()>crate::lexer::MAX_TOKENS {
        return Err(fail(t[0].pos,"E_SOURCE_LIMIT","Any specialization exceeds lexer token budget"));
    }
    Ok(out)
}
