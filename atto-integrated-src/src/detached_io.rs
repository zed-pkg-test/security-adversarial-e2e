//! Parse-only supervised detached I/O syntax for the restricted browser compiler.
//! This module does not schedule tasks, invoke callbacks or lower channel I/O.
//! A valid declaration must fail closed before guest emission.

use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind { Read, Write }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callback { None, SuccessOnly, Outcome(String) }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DetachedIo {
    pub kind: Kind,
    pub handle: String,
    pub callback: Callback,
    pub pos: Pos,
}

fn keyword(t: &Token) -> Option<&str> {
    if let Tok::Ident(w) = &t.tok { Some(w.as_str()) } else { None }
}

fn fail(pos: Pos, code: &'static str, message: &str) -> Diagnostic {
    Diagnostic::new(pos, code, message)
}

/// Lexically small receiver grammar. Computed receivers need the real parser.
fn handle(t: &[Token], mut i: usize) -> Option<(String, usize)> {
    let mut parts = vec![keyword(t.get(i)?)?.to_owned()];
    i += 1;
    while matches!(t.get(i).map(|x| &x.tok), Some(Tok::Dot)) {
        i += 1;
        let part = keyword(t.get(i)?)?;
        if crate::parser::is_reserved(part) { return None; }
        parts.push(part.to_owned());
        i += 1;
    }
    Some((parts.join("."), i))
}

fn callback(t: &[Token], mut i: usize, kind: Kind, pos: Pos)
    -> Result<(Callback, usize), Diagnostic>
{
    if !matches!(t.get(i).map(|x| &x.tok), Some(Tok::Pipe)) {
        return Err(fail(pos, "E_IO_CALLBACK",
            "detached completion callback must be a lambda with || or |outcome|"));
    }
    i += 1;
    let result = if matches!(t.get(i).map(|x| &x.tok), Some(Tok::Pipe)) {
        i += 1;
        if kind == Kind::Read {
            return Err(fail(pos, "E_IO_DISCARD",
                "detached read callback must accept one checked outcome; never discard read data"));
        }
        Callback::SuccessOnly
    } else {
        let binding = keyword(t.get(i).ok_or_else(|| fail(pos, "E_IO_CALLBACK",
            "detached callback missing outcome binding"))?)
            .ok_or_else(|| fail(pos, "E_IO_CALLBACK", "detached callback expects a binding"))?;
        if crate::parser::is_reserved(binding) {
            return Err(fail(pos, "E_IO_CALLBACK", "detached callback has reserved binding name"));
        }
        let result = Callback::Outcome(binding.to_owned());
        i += 1;
        if !matches!(t.get(i).map(|x| &x.tok), Some(Tok::Pipe)) {
            return Err(fail(pos, "E_IO_CALLBACK", "detached callback accepts exactly one outcome"));
        }
        i += 1;
        result
    };
    if !matches!(t.get(i).map(|x| &x.tok), Some(Tok::Arrow)) ||
        t.get(i + 1).and_then(keyword) != Some("void") ||
        !matches!(t.get(i + 2).map(|x| &x.tok), Some(Tok::LBrace))
    {
        return Err(fail(pos, "E_IO_CALLBACK",
            "detached callback must have return form -> void { ... }"));
    }
    i += 3;
    let mut depth = 1usize;
    while depth > 0 {
        match t.get(i).map(|x| &x.tok) {
            Some(Tok::LBrace) => depth += 1,
            Some(Tok::RBrace) => depth -= 1,
            Some(Tok::Eof) | None => {
                return Err(fail(pos, "E_IO_CALLBACK", "unclosed detached callback body"));
            }
            _ => {}
        }
        i += 1;
    }
    // A semicolon after the callback is optional at an enclosing block end.
    if matches!(t.get(i).map(|x| &x.tok), Some(Tok::Semi)) { i += 1; }
    Ok((result, i))
}

/// Validate explicit do readch/writech statements at the token level.
/// All successfully recognized forms are returned as syntax candidates only.
pub fn inspect(t: &[Token]) -> Result<Vec<DetachedIo>, Diagnostic> {
    let mut operations = Vec::new();
    for start in 0..t.len().saturating_sub(1) {
        if t.get(start).and_then(keyword) != Some("do") { continue; }
        let kind = match t.get(start + 1).and_then(keyword) {
            Some("readch") => Kind::Read,
            Some("writech") => Kind::Write,
            _ => continue, // do select, do match, etc. are unrelated.
        };
        let pos = t[start].pos;
        let (receiver, mut i) = handle(t, start + 2).ok_or_else(|| fail(pos,
            "E_IO_SYNTAX", "detached I/O requires a qualified channel or stream handle"))?;
        // A call or computed receiver is not a plain readable capability.
        // Do not misreport foo() as a valid handle with a missing callback.
        if matches!(t.get(i).map(|x| &x.tok), Some(Tok::LParen)) {
            return Err(fail(pos, "E_IO_SYNTAX",
                "computed detached I/O receiver requires the full typed parser"));
        }
        if !matches!(t.get(i).map(|x| &x.tok), Some(Tok::Comma)) {
            if kind == Kind::Read {
                return Err(fail(pos, "E_IO_DISCARD",
                    "do readch requires a completion callback receiving the checked outcome"));
            }
            return Err(fail(pos, "E_IO_SYNTAX",
                "do writech requires a comma followed by the payload"));
        }
        i += 1;
        let cb = if kind == Kind::Read {
            let (cb, next) = callback(t, i, kind, pos)?;
            i = next;
            cb
        } else {
            // The write expression must have a value. Keep balanced
            // parentheses/brackets so f(a,b) is one payload, not a callback.
            let value_begin = i;
            let (mut parens, mut brackets) = (0usize, 0usize);
            loop {
                match t.get(i).map(|x| &x.tok) {
                    Some(Tok::LParen) => parens += 1,
                    Some(Tok::RParen) if parens > 0 => parens -= 1,
                    Some(Tok::LBracket) => brackets += 1,
                    Some(Tok::RBracket) if brackets > 0 => brackets -= 1,
                    Some(Tok::Comma | Tok::Semi | Tok::Eof | Tok::RBrace) | None
                        if parens == 0 && brackets == 0 => break,
                    None | Some(Tok::Eof) => {
                        return Err(fail(pos, "E_IO_SYNTAX",
                            "unclosed detached-write payload expression"));
                    }
                    _ => {}
                }
                i += 1;
            }
            if i == value_begin {
                return Err(fail(pos, "E_IO_SYNTAX",
                    "detached write must have a nonempty payload"));
            }
            if matches!(t.get(i).map(|x| &x.tok), Some(Tok::Comma)) {
                let (cb, next) = callback(t, i + 1, kind, pos)?;
                i = next;
                cb
            } else {
                match t.get(i).map(|x| &x.tok) {
                    Some(Tok::Semi) => i += 1,
                    Some(Tok::Eof) => {},
                    _ => return Err(fail(pos, "E_IO_SYNTAX",
                        "detached write requires a semicolon or a completion callback")),
                }
                Callback::None
            }
        };
        if !matches!(t.get(i).map(|x| &x.tok), Some(Tok::RBrace | Tok::Eof)) &&
            (i > 0 && !matches!(t.get(i - 1).map(|x| &x.tok), Some(Tok::Semi)))
        {
            return Err(fail(pos, "E_IO_SYNTAX",
                "detached callback must terminate the statement"));
        }
        operations.push(DetachedIo { kind, handle: receiver, callback: cb, pos });
    }
    Ok(operations)
}
