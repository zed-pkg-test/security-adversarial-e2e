//! Shared canonical Array<T, layout=...> generic binder.
//! Called by the ordinary production parser and the bounded guest profile.
//! Type recognition does not grant guest storage or borrowing rights.

use crate::ast::ArrayType;
use crate::collection_layout_plan::Storage;
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};

fn diag(tokens: &[Token], index: usize, code: &'static str, message: &str) -> Diagnostic {
    let pos = tokens.get(index).map_or(Pos { line: 1, col: 1 }, |t| t.pos);
    Diagnostic::new(pos, code, message)
}

fn is(tokens: &[Token], i: usize, token: Tok) -> bool {
    tokens.get(i).is_some_and(|t| t.tok == token)
}

fn ident(tokens: &[Token], i: &mut usize, description: &str) -> Result<String, Diagnostic> {
    let index = *i;
    match tokens.get(index).map(|t| &t.tok) {
        Some(Tok::Ident(name)) if !name.is_empty() && name.len() <= 96 => {
            *i += 1;
            Ok(name.clone())
        }
        _ => Err(diag(tokens, index, "E_LAYOUT_SYNTAX", description)),
    }
}

fn expect(tokens: &[Token], i: &mut usize, token: Tok, msg: &str) -> Result<(), Diagnostic> {
    if !is(tokens, *i, token) {
        return Err(diag(tokens, *i, "E_LAYOUT_SYNTAX", msg));
    }
    *i += 1;
    Ok(())
}

fn layout(tokens: &[Token], i: &mut usize) -> Result<Storage, Diagnostic> {
    let start = *i;
    let word = match tokens.get(start).map(|t| &t.tok) {
        Some(Tok::Ident(word)) => word.as_str(),
        _ => return Err(diag(tokens, start, "E_LAYOUT_VALUE", "layout must be a compile-time Layout value")),
    };
    *i += 1;
    match word {
        "aos" => Ok(Storage::Aos),
        "soa" => Ok(Storage::Soa),
        "aosoa" => {
            expect(tokens, i, Tok::LParen, "expected '(' after aosoa")?;
            let lanes = match tokens.get(*i).map(|t| &t.tok) {
                Some(Tok::Int(Some(n))) if *n >= 1 && *n <= crate::collection_layout::MAX_AOSOA_LANES => *n,
                _ => return Err(diag(tokens, *i, "E_LAYOUT_SIZE", "aosoa requires a constant lane count in 1..=1024")),
            };
            *i += 1;
            expect(tokens, i, Tok::RParen, "expected ')' after aosoa lane count")?;
            Ok(Storage::Aosoa(lanes as u16))
        }
        _ => Err(diag(tokens, start, "E_LAYOUT_VALUE", "expected aos, soa or aosoa(N)")),
    }
}

/// Parse an Array type from the given index, returning the next index.
/// Identity is nominal element plus normalized physical layout, never order.
pub fn parse(tokens: &[Token], start: usize) -> Result<(ArrayType, usize), Diagnostic> {
    let pos = tokens.get(start).map_or(Pos { line: 1, col: 1 }, |t| t.pos);
    if !matches!(tokens.get(start).map(|t| &t.tok), Some(Tok::Ident(n)) if n == "Array") {
        return Err(diag(tokens, start, "E_LAYOUT_SYNTAX", "expected Array generic type"));
    }
    let mut i = start + 1;
    expect(tokens, &mut i, Tok::Lt, "expected '<' for Array generics")?;
    let mut element: Option<String> = None;
    let mut physical: Option<Storage> = None;
    let mut named_seen = false;
    loop {
        let here = i;
        let name = match (tokens.get(i).map(|t| &t.tok), tokens.get(i + 1).map(|t| &t.tok)) {
            (Some(Tok::Ident(name)), Some(Tok::Assign)) => Some(name.as_str()),
            _ => None,
        };
        match name {
            Some("T") => {
                i += 2;
                named_seen = true;
                if element.is_some() {
                    return Err(diag(tokens, here, "E_GENERIC_DUP", "T was bound twice"));
                }
                element = Some(ident(tokens, &mut i, "expected nominal Array element type")?);
            }
            Some("layout") => {
                i += 2;
                named_seen = true;
                if physical.is_some() {
                    return Err(diag(tokens, here, "E_GENERIC_DUP", "layout was bound twice"));
                }
                physical = Some(layout(tokens, &mut i)?);
            }
            Some(_) => return Err(diag(tokens, here, "E_GENERIC_NAME", "unknown Array generic; expected T or layout")),
            None => {
                if named_seen {
                    return Err(diag(tokens, here, "E_GENERIC_ORDER", "positional Array argument after named arguments"));
                }
                if element.is_some() {
                    return Err(diag(tokens, here, "E_GENERIC_ARITY", "too many Array positional arguments"));
                }
                element = Some(ident(tokens, &mut i, "Array requires a nominal element type")?);
            }
        }
        if !is(tokens, i, Tok::Comma) { break; }
        i += 1;
        if is(tokens, i, Tok::Gt) {
            return Err(diag(tokens, i, "E_LAYOUT_SYNTAX", "trailing generic comma"));
        }
    }
    expect(tokens, &mut i, Tok::Gt, "expected '>' after Array generics")?;
    let element = element.ok_or_else(|| diag(tokens, start, "E_GENERIC_ARITY", "Array requires element type T"))?;
    Ok((ArrayType { element, layout: physical.unwrap_or(Storage::Aos), pos }, i))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn parse_source(s: &str) -> Result<ArrayType, Diagnostic> {
        let tokens = crate::lexer::lex(s)?;
        let (ty, end) = parse(&tokens, 0)?;
        assert_eq!(tokens[end].tok, Tok::Eof);
        Ok(ty)
    }
    #[test]
    fn canonical_argument_order_and_default_aos() {
        let a = parse_source("Array<Particle, layout=soa>").unwrap();
        let b = parse_source("Array<layout=soa, T=Particle>").unwrap();
        let c = parse_source("Array<T=Particle, layout=soa>").unwrap();
        assert_eq!(a.element, b.element);
        assert_eq!(a.layout, b.layout);
        assert_eq!(a.layout, c.layout);
        assert_eq!(parse_source("Array<Particle>").unwrap().layout,
                   parse_source("Array<Particle, layout=aos>").unwrap().layout);
        assert_ne!(a.layout, parse_source("Array<Particle, layout=aosoa(16)>").unwrap().layout);
    }
    #[test]
    fn rejects_invalid_shape_without_source_guessing() {
        for (input, diagnostic) in [
            ("Array<layout=soa, Particle>", "E_GENERIC_ORDER"),
            ("Array<Particle, layout=soa, layout=aos>", "E_GENERIC_DUP"),
            ("Array<T=Particle, T=Particle>", "E_GENERIC_DUP"),
            ("Array<Particle, bogus=soa>", "E_GENERIC_NAME"),
            ("Array<Particle, layout=aosoa(n)>", "E_LAYOUT_SIZE"),
            ("Array<Particle, layout=aosoa(0)>", "E_LAYOUT_SIZE"),
            ("Array<Particle, layout=wat>", "E_LAYOUT_VALUE"),
            ("Array<>", "E_LAYOUT_SYNTAX"),
            ("Array<Particle,>", "E_LAYOUT_SYNTAX"),
        ] {
            assert_eq!(parse_source(input).unwrap_err().code, diagnostic, "{input}");
        }
    }
}
