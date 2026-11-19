//! Named collection layout syntax preflight for the browser compiler.
//!
//! This module validates a narrow compile-time generic binding contract but
//! NEVER admits AoS/SoA/AoSoA guest execution. General Array/List/Vector
//! runtime storage, element proxies and ownership are not implemented here.
//! Do not use raw source spelling as a monomorphization/type-identity key.

use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};

/// Conservative browser-front-end syntax limit. This is not a claim that any
/// backend supports blocks of this size.
pub const MAX_AOSOA_LANES: u64 = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    Aos,
    Soa,
    Aosoa(u16),
}

/// A syntactic request only; the element spans must later undergo nominal type
/// resolution and cannot be used as a semantic type or runtime storage plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Candidate {
    pub collection: &'static str,
    pub element_span: (usize, usize),
    pub layout: Layout,
    pub pos: Pos,
}

fn error(pos: Pos, code: &'static str, message: &str) -> Diagnostic {
    Diagnostic::new(pos, code, message)
}

fn top_level_args(toks: &[Token], lt: usize) -> Result<(Vec<(usize, usize)>, usize), Diagnostic> {
    let mut parts = Vec::new();
    let mut begin = lt + 1;
    let mut angle = 1usize;
    let mut paren = 0usize;
    let mut bracket = 0usize;
    let mut i = begin;
    while i < toks.len() {
        match &toks[i].tok {
            Tok::Lt => {
                angle += 1;
                if angle > 128 {
                    return Err(error(toks[i].pos, "E_LAYOUT_SYNTAX", "generic nesting exceeds 128 levels"));
                }
            }
            Tok::Gt => {
                angle -= 1;
                if angle == 0 {
                    parts.push((begin, i));
                    return Ok((parts, i));
                }
            }
            Tok::LParen => paren += 1,
            Tok::RParen => paren = paren.saturating_sub(1),
            Tok::LBracket => bracket += 1,
            Tok::RBracket => bracket = bracket.saturating_sub(1),
            Tok::Comma if angle == 1 && paren == 0 && bracket == 0 => {
                parts.push((begin, i));
                begin = i + 1;
            }
            Tok::Eof => break,
            _ => {}
        }
        i += 1;
    }
    Err(error(toks[lt].pos, "E_LAYOUT_SYNTAX", "unterminated collection generic argument list"))
}

fn parse_layout(value: &[Token], pos: Pos) -> Result<Layout, Diagnostic> {
    if let [Token { tok: Tok::Ident(name), .. }] = value {
        return match name.as_str() {
            "aos" => Ok(Layout::Aos),
            "soa" => Ok(Layout::Soa),
            _ => Err(error(pos, "E_LAYOUT_VALUE", "expected aos, soa or aosoa(<constant positive lanes>)")),
        };
    }
    if let [
        Token { tok: Tok::Ident(name), .. },
        Token { tok: Tok::LParen, .. },
        Token { tok: Tok::Int(Some(n)), .. },
        Token { tok: Tok::RParen, .. },
    ] = value {
        if name == "aosoa" {
            return if *n >= 1 && *n <= MAX_AOSOA_LANES {
                Ok(Layout::Aosoa(*n as u16))
            } else {
                Err(error(pos, "E_LAYOUT_SIZE", "aosoa block size must be in 1..=1024"))
            };
        }
    }
    if matches!(value.first().map(|t| &t.tok), Some(Tok::Ident(name)) if name == "aosoa") {
        return Err(error(pos, "E_LAYOUT_SIZE", "aosoa requires a constant positive integer block size in 1..=1024"));
    }
    Err(error(pos, "E_LAYOUT_VALUE", "expected aos, soa or aosoa(<constant positive lanes>)"))
}

/// Find layout-bearing collection type requests. Pure syntax only: no nominal
/// binding, ABI offsets, memory allocation or physical-contiguity guarantees.
pub fn inspect(toks: &[Token]) -> Result<Vec<Candidate>, Diagnostic> {
    let mut results = Vec::new();
    for i in 0..toks.len().saturating_sub(1) {
        let collection = match &toks[i].tok {
            Tok::Ident(name) if name == "Array" => "Array",
            Tok::Ident(name) if name == "List" => "List",
            Tok::Ident(name) if name == "Vector" => "Vector",
            _ => continue,
        };
        if !matches!(toks[i + 1].tok, Tok::Lt) {
            continue;
        }

        let (parts, _) = match top_level_args(toks, i + 1) {
            Ok(parsed) => parsed,
            Err(err) => {
                // Preserve the existing parser's diagnostics for unrelated
                // generic syntax. A missing '>' that mentions the new layout
                // formal receives a deterministic targeted syntax error.
                let has_layout = toks[i + 2..].iter().take_while(|t| !matches!(t.tok, Tok::Semi | Tok::Eof))
                    .any(|t| matches!(&t.tok, Tok::Ident(s) if s == "layout"));
                if has_layout { return Err(err); }
                continue;
            }
        };
        let uses_layout = parts.iter().any(|&(a, b)| a < b &&
            matches!(&toks[a].tok, Tok::Ident(s) if s == "layout"));
        if !uses_layout {
            continue; // Other generic types retain their existing admission.
        }

        let mut element = None;
        let mut layout = None;
        let mut named = false;
        for (start, end) in parts {
            if start == end {
                return Err(error(toks[i].pos, "E_LAYOUT_SYNTAX", "empty collection generic argument"));
            }
            let value = &toks[start..end];
            let label = if value.len() >= 2 && matches!(value[1].tok, Tok::Assign) {
                match &value[0].tok { Tok::Ident(s) => Some(s.as_str()), _ => None }
            } else {
                None
            };
            match label {
                Some("layout") => {
                    named = true;
                    if layout.is_some() {
                        return Err(error(toks[start].pos, "E_GENERIC_DUP", "duplicate named generic layout binding"));
                    }
                    layout = Some(parse_layout(&value[2..], toks[start].pos)?);
                }
                Some("T") => {
                    named = true;
                    if element.is_some() {
                        return Err(error(toks[start].pos, "E_GENERIC_DUP", "duplicate element type generic binding"));
                    }
                    if value.len() == 2 {
                        return Err(error(toks[start].pos, "E_LAYOUT_SYNTAX", "missing T type argument"));
                    }
                    element = Some((start + 2, end));
                }
                Some(_) => return Err(error(toks[start].pos, "E_GENERIC_NAME", "unknown collection generic formal; expected T or layout")),
                None => {
                    if matches!(&value[0].tok, Tok::Ident(s) if s == "layout") {
                        return Err(error(toks[start].pos, "E_LAYOUT_SYNTAX", "layout requires a named value: layout=..."));
                    }
                    if named {
                        return Err(error(toks[start].pos, "E_GENERIC_ORDER", "positional generic argument after a named argument"));
                    }
                    if element.is_some() {
                        return Err(error(toks[start].pos, "E_GENERIC_ARITY", "too many positional collection generic arguments"));
                    }
                    element = Some((start, end));
                }
            }
        }
        let element_span = element.ok_or_else(|| error(toks[i].pos, "E_GENERIC_ARITY", "missing collection element type T"))?;
        let layout = layout.ok_or_else(|| error(toks[i].pos, "E_LAYOUT_SYNTAX", "missing layout=... binding"))?;
        results.push(Candidate { collection, element_span, layout, pos: toks[i].pos });
    }
    Ok(results)
}

/// Integration gate: syntax can be understood, but the browser compiler MUST
/// reject before generating guest Wasm until actual layout lowering is proven.
pub fn reject_unlowered(toks: &[Token]) -> Result<(), Diagnostic> {
    if let Some(first) = inspect(toks)?.first() {
        return Err(error(first.pos, "E_UNSUPPORTED",
            "named collection layout recognized but Array/List/Vector layout storage and guest execution are not implemented"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn candidates(src: &str) -> Result<Vec<Candidate>, Diagnostic> {
        inspect(&crate::lexer::lex(src).unwrap())
    }

    #[test]
    fn canonical_order_and_nested_generic_spans() {
        let a = candidates("Array<Particle, layout=soa>").unwrap();
        let b = candidates("Array<layout=soa, T=Particle>").unwrap();
        assert_eq!(a[0].layout, Layout::Soa);
        assert_eq!(a[0].layout, b[0].layout);
        assert_eq!(a[0].collection, "Array");
        assert_eq!(b[0].element_span.1 - b[0].element_span.0, 1);
        assert_eq!(candidates("Array<Particle>").unwrap().len(), 0);
        assert_eq!(candidates("Array<Map<int, int>, layout=aosoa(16)>").unwrap()[0].layout, Layout::Aosoa(16));
    }

    #[test]
    fn rejects_malformed_bindings() {
        for (src, code) in [
            ("Array<Particle, layout=soa, layout=aos>", "E_GENERIC_DUP"),
            ("Array<T=Particle, layout=soa, Particle>", "E_GENERIC_ORDER"),
            ("Array<Particle, layout=unknown>", "E_LAYOUT_VALUE"),
            ("Array<Particle, layout=aosoa(0)>", "E_LAYOUT_SIZE"),
            ("Array<Particle, layout=aosoa(1025)>", "E_LAYOUT_SIZE"),
            ("Array<Particle, layout=aosoa(n)>", "E_LAYOUT_SIZE"),
            ("Array<Particle, xyz=1, layout=soa>", "E_GENERIC_NAME"),
            ("Array<layout=soa>", "E_GENERIC_ARITY"),
            ("Array<Particle, layout>", "E_LAYOUT_SYNTAX"),
            ("Array<Particle, layout=soa,>", "E_LAYOUT_SYNTAX"),
        ] {
            assert_eq!(candidates(src).unwrap_err().code, code, "{src}");
        }
    }

    #[test]
    fn does_not_scan_comments_or_strings() {
        assert!(candidates(r#"// Array<Particle, layout=soa>
            val s = "Array<Particle, layout=soa>";"#).unwrap().is_empty());
    }

    #[test]
    fn no_false_guest_execution_promotion() {
        for (ty, expected) in [
            // The production nominal resolver now distinguishes unknown
            // element types from unsupported collection execution.
            ("Array<Particle, layout=soa>", "E_UNKNOWN_TYPE"),
            ("Vector<Particle, layout=aosoa(16)>", "E_UNSUPPORTED"),
            ("List<layout=aos, T=Particle>", "E_UNSUPPORTED"),
        ] {
            let input = format!("fnc example() -> {ty} {{ return []; }}");
            let err = crate::compile(&input).unwrap_err();
            assert_eq!(err.code, expected, "{ty}");
        }
    }
}
