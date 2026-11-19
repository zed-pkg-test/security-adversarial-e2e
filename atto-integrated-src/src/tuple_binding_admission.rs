//! Bounded tuple destructuring grammar admission.
//!
//! This module recognizes the tuple binding header and per-element qualifiers.
//! Guest compilation exists only for the separate, checked Copy-scalar
//! source lowering (tuple_binding_lower). Object tuple ownership/loans,
//! general const evaluation and independent backend parity remain unsupported.
//! The syntax contract lives in atto-spec: language/tuple-destructuring-v1.md.
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};
use std::collections::BTreeSet;

type R<T> = Result<T, Diagnostic>;
const MAX_BINDERS: usize = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingMode { Let, Val, Const }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleMember {
    pub name: Option<String>, // None is the discard-only '_' wildcard
    pub mode: BindingMode,
    pub mutable_referent: bool,
    /// Explicit primitive type annotation, preserved for typed lowering.
    pub annotation: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootAlias {
    pub name: String,
    pub mode: BindingMode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleBinding {
    pub pos: Pos,
    pub members: Vec<TupleMember>,
    pub alias: Option<RootAlias>,
    /// Original token offset where the declaration begins.
    pub start_index: usize,
    /// Original token offset immediately after the '=' token.
    pub rhs_start_index: usize,
}

fn mode(tok: Option<&Tok>) -> Option<BindingMode> {
    match tok {
        Some(Tok::Ident(s)) if s == "let" => Some(BindingMode::Let),
        Some(Tok::Ident(s)) if s == "val" => Some(BindingMode::Val),
        Some(Tok::Ident(s)) if s == "const" => Some(BindingMode::Const),
        _ => None,
    }
}

fn word(tok: Option<&Tok>, spelling: &str) -> bool {
    matches!(tok, Some(Tok::Ident(s)) if s == spelling)
}

fn tok(toks: &[Token], i: usize) -> Option<&Tok> {
    toks.get(i).map(|t| &t.tok)
}

fn fail(toks: &[Token], i: usize, code: &'static str, msg: &str) -> Diagnostic {
    Diagnostic::new(toks.get(i).map_or(Pos::default(), |t| t.pos), code, msg)
}

fn parse_one(toks: &[Token], start: usize, outer: Option<BindingMode>) -> R<(TupleBinding, usize)> {
    let open = if outer.is_some() { start + 1 } else { start };
    if tok(toks, open) != Some(&Tok::LParen) {
        return Err(fail(toks, open, "E_SYNTAX", "tuple binding requires '('"));
    }
    let mut i = open + 1;
    let mut members = Vec::new();
    let mut names = BTreeSet::new();
    let mut saw_comma = false;

    while tok(toks, i) != Some(&Tok::RParen) {
        if matches!(tok(toks, i), None | Some(Tok::Eof)) {
            return Err(fail(toks, i, "E_SYNTAX", "unclosed tuple binding"));
        }
        if members.len() >= MAX_BINDERS {
            return Err(fail(toks, i, "E_SOURCE_LIMIT", "tuple binding exceeds 1024 elements"));
        }

        let explicit = mode(tok(toks, i));
        if explicit.is_some() { i += 1; }
        if outer.is_none() && explicit.is_none() && !word(tok(toks, i), "_") {
            return Err(fail(toks, i, "E_SYNTAX", "each element needs let, val or const without an outer binding kind"));
        }
        let inherited = explicit.or(outer).unwrap_or(BindingMode::Val);
        let mutable_referent = word(tok(toks, i), "mut");
        if mutable_referent { i += 1; }

        let name = match tok(toks, i) {
            Some(Tok::Ident(s)) if s == "_" => {
                if mutable_referent || explicit.is_some() {
                    return Err(fail(toks, i, "E_SYNTAX", "discard '_' cannot have binding qualifiers"));
                }
                None
            },
            Some(Tok::Ident(s)) if s != "let" && s != "val" && s != "const" && s != "mut" => Some(s.clone()),
            _ => return Err(fail(toks, i, "E_SYNTAX", "expected tuple binding name or '_'")),
        };
        if let Some(ref name) = name {
            if !names.insert(name.clone()) {
                return Err(fail(toks, i, "E_DUPLICATE", "duplicate tuple binding name"));
            }
        }
        i += 1;

        // Preserve annotations, never silently drop an explicit type.
        let mut annotation = None;
        if tok(toks, i) == Some(&Tok::Colon) {
            if name.is_none() {
                return Err(fail(toks, i, "E_SYNTAX",
                    "discard '_' cannot carry a type annotation"));
            }
            i += 1;
            let begin = i;
            let mut generics = 0usize;
            while let Some(t) = tok(toks, i) {
                if (t == &Tok::Comma || t == &Tok::RParen) && generics == 0 { break; }
                if t == &Tok::Eof { break; }
                if t == &Tok::Lt { generics += 1; }
                if t == &Tok::Gt {
                    if generics == 0 { break; }
                    generics -= 1;
                }
                i += 1;
            }
            if i == begin || generics != 0 {
                return Err(fail(toks, i, "E_SYNTAX", "invalid tuple binder type annotation"));
            }
            if i != begin + 1 {
                return Err(fail(toks, begin, "E_UNSUPPORTED_TYPE",
                    "only primitive typed binders are executable in scalar tuple destructuring"));
            }
            annotation = match tok(toks, begin) {
                Some(Tok::Ident(w)) if matches!(w.as_str(),
                    "int" | "bool" | "float" | "f64" | "string" | "String") => Some(w.clone()),
                _ => return Err(fail(toks, begin, "E_UNSUPPORTED_TYPE",
                    "tuple binder annotation requires a scalar primitive type")),
            };
        }

        members.push(TupleMember { name, mode: inherited, mutable_referent, annotation });
        if tok(toks, i) == Some(&Tok::Comma) {
            saw_comma = true;
            i += 1;
        } else if tok(toks, i) != Some(&Tok::RParen) {
            return Err(fail(toks, i, "E_SYNTAX", "expected ',' or ')' after tuple binder"));
        }
    }
    if members.len() == 1 && !saw_comma {
        return Err(fail(toks, i, "E_SYNTAX", "singleton tuple binding needs trailing comma"));
    }
    i += 1; // ')'

    let alias = if word(tok(toks, i), "as") {
        i += 1;
        let override_mode = mode(tok(toks, i));
        if override_mode.is_some() { i += 1; }
        let alias_mode = match override_mode.or(outer) {
            Some(mode) => mode,
            None => return Err(fail(toks, i, "E_SYNTAX", "explicit tuple binder list requires as let/val/const for root alias")),
        };
        let alias_name = match tok(toks, i) {
            Some(Tok::Ident(s)) if !["let", "val", "const", "mut", "_"].contains(&s.as_str()) => s.clone(),
            _ => return Err(fail(toks, i, "E_SYNTAX", "expected root alias name")),
        };
        if !names.insert(alias_name.clone()) {
            return Err(fail(toks, i, "E_DUPLICATE", "root alias conflicts with tuple element"));
        }
        i += 1;
        Some(RootAlias { name: alias_name, mode: alias_mode })
    } else { None };

    if tok(toks, i) != Some(&Tok::Assign) {
        return Err(fail(toks, i, "E_SYNTAX", "tuple destructuring requires '=' before initializer"));
    }
    Ok((TupleBinding { pos: toks[start].pos, members, alias, start_index: start, rhs_start_index: i + 1 }, i + 1))
}

/// Reject a parenthesized tuple LHS with no declaration qualifiers.
/// Ordinary tuple-valued expressions and comparisons are untouched: only
/// a comma-containing '(...)' immediately followed by '=' is diagnosed.
fn bare_tuple_assignment(toks: &[Token], start: usize) -> bool {
    if tok(toks, start) != Some(&Tok::LParen)
        || !matches!(tok(toks, start + 1), Some(Tok::Ident(_)))
        || mode(tok(toks, start + 1)).is_some()
    {
        return false;
    }
    let mut depth = 0usize;
    let mut saw_separator = false;
    // Bound lexical inspection by the existing binder source budget.
    for i in start..toks.len().min(start.saturating_add(MAX_BINDERS * 4)) {
        match tok(toks, i) {
            Some(Tok::LParen) => depth += 1,
            Some(Tok::RParen) => {
                if depth == 1 {
                    return saw_separator && tok(toks, i + 1) == Some(&Tok::Assign);
                }
                if depth == 0 { return false; }
                depth -= 1;
            }
            Some(Tok::Comma) if depth == 1 => saw_separator = true,
            Some(Tok::Eof) | None => return false,
            _ => {}
        }
    }
    false
}

/// Inspect tuple destructuring headers anywhere in the token stream, ignoring
/// strings/comments because lex() has already normalized them. No codegen.
pub fn inspect(toks: &[Token]) -> R<Vec<TupleBinding>> {
    let mut found = Vec::new();
    let mut i = 0usize;
    while i + 1 < toks.len() {
        let outer = mode(tok(toks, i));
        let explicit_tuple = tok(toks, i) == Some(&Tok::LParen)
            && mode(tok(toks, i + 1)).is_some();
        if (outer.is_some() && tok(toks, i + 1) == Some(&Tok::LParen)) || explicit_tuple {
            let (binding, next) = parse_one(toks, i, if explicit_tuple { None } else { outer })?;
            found.push(binding);
            i = next;
        } else if bare_tuple_assignment(toks, i) {
            return Err(fail(toks, i, "E_SYNTAX",
                "tuple binding requires an outer let/val/const or explicit element modes"));
        } else {
            i += 1;
        }
    }
    Ok(found)
}
