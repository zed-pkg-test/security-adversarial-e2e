//! Compile-time monomorphization of a bounded named Fnc<int,int> callback.
//!
//! The admitted profile has zero runtime callable handles: a function taking
//! a named, non-routine top-level callback gets a distinct direct-call Wasm
//! specialization. Attempts to escape a routine or callback value reject.
//! General higher-order/indirect dispatch still requires callable ABI work.
use std::collections::{BTreeMap, BTreeSet};
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};
type R<T> = Result<T, Diagnostic>;
const PREFIX: &str = "__atto_internal_direct_cb_";
const MAX_SPECIALIZATIONS: usize = 64;

#[derive(Clone)]
struct Func {
    name: String,
    start: usize,
    end: usize,
    args_start: usize,
    args_end: usize,
    body_start: usize,
    body_end: usize,
    routine: bool,
}
#[derive(Clone)]
struct Template {
    func: Func,
    callback: String,
    first_arg_end: usize,
}
fn is(t: &[Token], i: usize, value: &str) -> bool {
    matches!(t.get(i).map(|x| &x.tok), Some(Tok::Ident(s)) if s == value)
}
fn fail(pos: Pos, code: &'static str, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(pos, code, message)
}
fn balanced(t: &[Token], start: usize, open: Tok, close: Tok) -> R<usize> {
    let mut level = 0;
    for (i, token) in t.iter().enumerate().skip(start) {
        if token.tok == open { level += 1; }
        if token.tok == close {
            if level == 0 { return Err(fail(token.pos, "E_SYNTAX", "unexpected closing delimiter")); }
            level -= 1;
            if level == 0 { return Ok(i); }
        }
        if level > 128 { return Err(fail(token.pos, "E_NESTING", "callback nesting exceeds 128")); }
    }
    Err(fail(t[start].pos, "E_EOF", "unclosed callable signature or body"))
}
fn funcs(t: &[Token]) -> R<BTreeMap<String, Func>> {
    let mut out = BTreeMap::new();
    let mut i = 0;
    while i + 2 < t.len() {
        if !(is(t, i, "fnc") || is(t, i, "routine")) ||
           !matches!(t.get(i + 1).map(|x| &x.tok), Some(Tok::Ident(_))) ||
           t[i + 2].tok != Tok::LParen {
            i += 1;
            continue;
        }
        let routine = is(t, i, "routine");
        let Tok::Ident(name) = &t[i + 1].tok else { unreachable!() };
        let name = name.clone();
        let args_end = balanced(t, i + 2, Tok::LParen, Tok::RParen)?;
        let mut j = args_end + 1;
        while j < t.len() && t[j].tok != Tok::LBrace && t[j].tok != Tok::Semi &&
              !is(t, j, "end") {
            if t[j].tok == Tok::Eof { break; }
            j += 1;
        }
        // End-bodied routines are direct-call-only too. Record their own
        // lexical boundary; never scan into the following function's '{',
        // which would fabricate recursion from calls inside main().
        if j < t.len() && is(t, j, "end") {
            if t[i + 3..args_end].iter().any(|x|
                matches!(&x.tok, Tok::Ident(n) if n == "Fnc")) {
                return Err(fail(t[i].pos, "E_UNSUPPORTED",
                    "end-bodied higher-order callback lowering needs a checked body mode"));
            }
            // Nested match/select end-delimiters require a proper statement
            // grammar, not this intentionally bounded lexical profile.
            if t[args_end + 1..j].iter().any(|x|
                matches!(&x.tok, Tok::Ident(n) if n == "match" || n == "select")) {
                return Err(fail(t[i].pos, "E_UNSUPPORTED",
                    "end-bodied routine with nested match/select requires an explicit body CFG"));
            }
            let f = Func { name: name.clone(), start: i, end: j + 1,
                args_start: i + 2, args_end, body_start: args_end, body_end: j,
                routine };
            if out.insert(name.clone(), f).is_some() {
                return Err(fail(t[i].pos, "E_DUPLICATE",
                    format!("duplicate named callable '{name}'")));
            }
            i = j + 1;
            continue;
        }
        if j >= t.len() || t[j].tok != Tok::LBrace {
            i += 1;
            continue; // real frontend handles unrecognized callable declarations
        }
        let body_end = balanced(t, j, Tok::LBrace, Tok::RBrace)?;
        let f = Func { name: name.clone(), start: i, end: body_end + 1,
            args_start: i + 2, args_end, body_start: j, body_end, routine };
        if out.insert(name.clone(), f).is_some() {
            return Err(fail(t[i].pos, "E_DUPLICATE", format!("duplicate named callable '{name}'")));
        }
        i = body_end + 1;
    }
    Ok(out)
}
fn first_callback(t: &[Token], f: &Func) -> R<Option<Template>> {
    let i = f.args_start + 1;
    if !is(t, i, "Fnc") { return Ok(None); }
    let start = i;
    let code = [
        Tok::Ident("Fnc".into()), Tok::Lt, Tok::Ident("int".into()),
        Tok::Comma, Tok::Ident("int".into()), Tok::Gt
    ];
    if i + 6 >= t.len() || t[i..i + 6].iter().map(|x| x.tok.clone()).collect::<Vec<_>>().as_slice() != code.as_slice() {
        return Err(fail(t[start].pos, "E_UNSUPPORTED_TYPE",
            "direct Fnc callback profile admits only Fnc<int,int>"));
    }
    let Some(Token { tok: Tok::Ident(callback), .. }) = t.get(i + 6) else {
        return Err(fail(t[start].pos, "E_SYNTAX", "callback parameter requires a name"));
    };
    let j = i + 7;
    if t.get(j).map(|x| &x.tok) != Some(&Tok::Comma) {
        return Err(fail(t[start].pos, "E_UNSUPPORTED",
            "callback must be first and followed by at least one scalar parameter"));
    }
    Ok(Some(Template { func: f.clone(), callback: callback.clone(), first_arg_end: j + 1 }))
}
fn scalar_fnc(t: &[Token], f: &Func) -> bool {
    if f.routine || f.args_end != f.args_start + 3 { return false; }
    // Only fnc name(int value): int ... is first-class under this profile.
    is(t, f.args_start + 1, "int") &&
    matches!(t.get(f.args_start + 2).map(|x| &x.tok), Some(Tok::Ident(_))) &&
    f.args_start + 3 == f.args_end &&
    t.get(f.args_end + 1).is_some_and(|x| x.tok == Tok::Colon || x.tok == Tok::Arrow) &&
    is(t, f.args_end + 2, "int")
}
fn generated(template: &str, callback: &str) -> String {
    format!("{PREFIX}{}_{}_{}_{}", template.len(), template, callback.len(), callback)
}
pub fn lower(t: Vec<Token>) -> R<Vec<Token>> {
    if !t.iter().any(|x| matches!(&x.tok, Tok::Ident(s) if s == "routine" || s == "Fnc")) {
        return Ok(t);
    }
    for x in &t {
        if matches!(&x.tok, Tok::Ident(s) if s.starts_with(PREFIX)) {
            return Err(fail(x.pos, "E_RESERVED", "compiler-owned direct callback symbol is reserved"));
        }
    }
    let known = funcs(&t)?;
    let routines: BTreeSet<String> = known.values().filter(|f| f.routine).map(|f| f.name.clone()).collect();
    // Nonrecursive routine contracts must be checked across the entire
    // *known* call graph, not only by searching for direct self-calls.
    // Otherwise two routines (or a routine and a normal fnc) can recurse
    // indirectly while still being classified as nonrecursive.
    // Traverse iteratively: adversarial deep call chains must not grow the
    // Rust compiler stack, and each source-visible edge stays within the
    // bounded file-local named callable registry.
    let mut edges = BTreeMap::<String, BTreeSet<String>>::new();
    for f in known.values() {
        let mut calls = BTreeSet::new();
        for j in f.body_start + 1..f.body_end {
            let Tok::Ident(target) = &t[j].tok else { continue };
            if known.contains_key(target) &&
                t.get(j + 1).is_some_and(|x| x.tok == Tok::LParen) &&
                (j == 0 || t[j - 1].tok != Tok::Dot)
            {
                calls.insert(target.clone());
            }
        }
        edges.insert(f.name.clone(), calls);
    }
    for routine in &routines {
        let mut seen = BTreeSet::<String>::new();
        let mut pending = edges.get(routine).map(|s| s.iter().cloned().collect::<Vec<_>>())
            .unwrap_or_default();
        while let Some(next) = pending.pop() {
            if next == *routine {
                let pos = known.get(routine).map(|f| t[f.start].pos).unwrap_or(t[0].pos);
                return Err(fail(pos, "E_ROUTINE_RECURSION",
                    format!("routine '{routine}' participates in a recursive call cycle")));
            }
            if seen.insert(next.clone()) {
                if let Some(deps) = edges.get(&next) {
                    pending.extend(deps.iter().cloned());
                }
            }
        }
    }
    for j in 0..t.len() {
        let Tok::Ident(n) = &t[j].tok else { continue };
        if !routines.contains(n) { continue; }
        if known.get(n).is_some_and(|f| f.start + 1 == j) { continue; }
        if t.get(j + 1).map(|x| &x.tok) != Some(&Tok::LParen) {
            return Err(fail(t[j].pos, "E_ROUTINE", "routine is direct-call only and cannot escape as a value"));
        }
    }

    let templates = known.values()
        .map(|f| first_callback(&t, f))
        .collect::<R<Vec<_>>>()?
        .into_iter().flatten().collect::<Vec<_>>();
    if templates.is_empty() { return Ok(t); }
    if templates.len() != 1 {
        return Err(fail(t[0].pos, "E_UNSUPPORTED", "one statically specialized callback declaration per source file"));
    }
    let tpl = &templates[0];
    for j in tpl.func.body_start + 1..tpl.func.body_end {
        if is(&t, j, &tpl.callback) && t.get(j + 1).map(|x| &x.tok) != Some(&Tok::LParen) {
            return Err(fail(t[j].pos, "E_UNSUPPORTED", "callback parameter must be invoked directly, never aliased or escaped"));
        }
    }
    let mut callbacks = BTreeSet::<String>::new();
    let mut out = Vec::with_capacity(t.len());
    let mut i = 0;
    while i < t.len() {
        if i == tpl.func.start { i = tpl.func.end; continue; }
        if is(&t, i, &tpl.func.name) &&
           t.get(i + 1).map(|x| &x.tok) == Some(&Tok::LParen) {
            let Some(Token { tok: Tok::Ident(cb), .. }) = t.get(i + 2) else {
                return Err(fail(t[i].pos, "E_UNSUPPORTED", "direct Fnc call requires named static callback"));
            };
            if !known.get(cb).is_some_and(|f| scalar_fnc(&t, f)) {
                return Err(fail(t[i + 2].pos, "E_TYPE",
                    "callback must be a matching ordinary fnc(int)->int, not a routine or escaped value"));
            }
            if t.get(i + 3).map(|x| &x.tok) != Some(&Tok::Comma) {
                return Err(fail(t[i].pos, "E_ARITY", "specialized direct callback requires scalar argument"));
            }
            if callbacks.len() >= MAX_SPECIALIZATIONS {
                return Err(fail(t[i].pos, "E_SOURCE_LIMIT", "too many distinct direct callback specializations"));
            }
            callbacks.insert(cb.clone());
            out.push(Token { tok: Tok::Ident(generated(&tpl.func.name, cb)), pos: t[i].pos });
            out.push(t[i + 1].clone()); // (
            i += 4; // skip source callback value and separating comma
            continue;
        }
        if is(&t, i, &tpl.func.name) {
            return Err(fail(t[i].pos, "E_UNSUPPORTED", "higher-order template cannot escape as a value"));
        }
        out.push(t[i].clone());
        i += 1;
    }
    if callbacks.is_empty() {
        return Err(fail(t[tpl.func.start].pos, "E_UNSUPPORTED",
            "unused higher-order templates are not checked by direct specialization"));
    }
    let eof = out.pop().ok_or_else(|| fail(t[0].pos, "E_EOF", "empty source"))?;
    if eof.tok != Tok::Eof { return Err(fail(eof.pos, "E_SYNTAX", "missing source end token")); }
    for callback in callbacks {
        for j in tpl.func.start..tpl.func.end {
            if j > tpl.func.args_start && j < tpl.first_arg_end { continue; }
            let mut token = t[j].clone();
            if j == tpl.func.start + 1 {
                token.tok = Tok::Ident(generated(&tpl.func.name, &callback));
            }
            if j > tpl.func.body_start && j < tpl.func.body_end && is(&t, j, &tpl.callback) {
                token.tok = Tok::Ident(callback.clone());
            }
            out.push(token);
        }
    }
    out.push(eof);
    if out.len() > crate::lexer::MAX_TOKENS {
        return Err(fail(t[0].pos, "E_SOURCE_LIMIT", "monomorphized source exceeds lexer token budget"));
    }
    Ok(out)
}
