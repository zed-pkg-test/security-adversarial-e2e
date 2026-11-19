//! Bounded single-file export declarations and unlinked foreign prototypes.
//! This is not a package linker or a foreign-function runtime.
//! Public exports add deterministic Wasm metadata; private/package entries
//! cannot be imported as host functions.
use std::collections::BTreeSet;
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};
type R<T> = Result<T, Diagnostic>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility { Public, Package }
#[derive(Clone, Debug)]
pub struct Export {
    pub name: String,
    pub kind: &'static str,
    pub visibility: Visibility,
    pub pos: Pos,
}
pub struct Lowered { pub tokens: Vec<Token>, pub exports: Vec<Export> }
fn word(t: &[Token], i: usize, value: &str) -> bool {
    matches!(t.get(i).map(|x| &x.tok), Some(Tok::Ident(s)) if s == value)
}
fn error(pos: Pos, code: &'static str, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(pos, code, message)
}
fn name(t: &[Token], i: usize) -> R<String> {
    match t.get(i) {
        Some(Token { tok: Tok::Ident(n), .. }) if n.len() <= 96
            && !matches!(n.as_str(), "pub" | "export" | "class" | "fnc" | "as" | "end") =>
            Ok(n.clone()),
        Some(x) => Err(error(x.pos, "E_SYNTAX", "expected bounded export identifier")),
        None => Err(error(Pos { line: 1, col: 1 }, "E_EOF", "missing export name")),
    }
}
/// Resolve exports against the checked parser's actual declaration table,
/// not arbitrary tokens: a class member named Foo is NOT a top-level fnc
/// Foo, and a foreign prototype never grants source-level export authority.
pub fn resolve_exports(exports: &mut [Export], parsed: &crate::ast::Program) -> R<()> {
    for export in exports {
        let class_count = parsed.classes.iter()
            .filter(|c| c.name == export.name && !c.state_container).count();
        let fnc_count = parsed.funcs.iter()
            .filter(|f| f.name == export.name).count();
        let matches = class_count + fnc_count;
        if matches == 0 {
            return Err(error(export.pos, "E_UNBOUND",
                format!("export '{}' has no top-level declaration", export.name)));
        }
        if matches != 1 {
            return Err(error(export.pos, "E_DUPLICATE",
                format!("export '{}' is ambiguous without an arity-qualified export", export.name)));
        }
        let kind = if class_count == 1 { "class" } else { "fnc" };
        if !export.kind.is_empty() && export.kind != kind {
            return Err(error(export.pos, "E_TYPE", "export declaration kind mismatch"));
        }
        export.kind = kind;
    }
    Ok(())
}
fn external_prototype(t: &[Token], start: usize) -> R<(usize, String)> {
    let p = t[start].pos;
    if !word(t, start + 1, "fnc") {
        return Err(error(p, "E_UNSUPPORTED", "only unlinked external fnc prototypes are recognized"));
    }
    let id = name(t, start + 2)?;
    let mut i = start + 3;
    if t.get(i).map(|x| &x.tok) != Some(&Tok::LParen) {
        return Err(error(p, "E_SYNTAX", "external fnc requires parameter list"));
    }
    let mut level = 0usize;
    loop {
        match t.get(i).map(|x| &x.tok) {
            Some(Tok::LParen) => level += 1,
            Some(Tok::RParen) => {
                if level == 0 { return Err(error(p, "E_SYNTAX", "invalid external parentheses")); }
                level -= 1;
                if level == 0 { i += 1; break; }
            },
            Some(Tok::Eof) | None => return Err(error(p, "E_EOF", "unclosed external prototype")),
            _ => {}
        }
        if level > 32 { return Err(error(p, "E_NESTING", "external signature nesting limit")); }
        i += 1;
    }
    if !matches!(t.get(i).map(|x| &x.tok), Some(Tok::Colon | Tok::Arrow)) {
        return Err(error(p, "E_SYNTAX", "external prototype needs result annotation"));
    }
    i += 1;
    if !matches!(t.get(i).map(|x| &x.tok), Some(Tok::Ident(_))) {
        return Err(error(p, "E_SYNTAX", "external prototype needs a result type"));
    }
    i += 1;
    if t.get(i).map(|x| &x.tok) != Some(&Tok::Semi) {
        return Err(error(p, "E_UNSUPPORTED", "external definitions and foreign ABI calls remain unsupported"));
    }
    Ok((i + 1, id))
}
pub fn lower(t: Vec<Token>) -> R<Lowered> {
    if !t.iter().any(|x| matches!(&x.tok, Tok::Ident(s)
        if matches!(s.as_str(), "export" | "external" | "internal" | "protected"))) {
        return Ok(Lowered { tokens: t, exports: vec![] });
    }
    let mut exports: Vec<Export> = Vec::new();
    let mut foreign = BTreeSet::new();
    let mut out = Vec::new();
    let mut i = 0;
    while i < t.len() {
        let pos = t[i].pos;
        if word(&t, i, "export") {
            if exports.len() >= 128 { return Err(error(pos, "E_SOURCE_LIMIT", "export budget exceeded")); }
            if !word(&t, i + 1, "pub") {
                return Err(error(pos, "E_SYNTAX", "export requires pub or pub[pkg]"));
            }
            let mut j = i + 2;
            let visibility = if t.get(j).map(|x| &x.tok) == Some(&Tok::LBracket) {
                if !word(&t, j + 1, "pkg") ||
                   t.get(j + 2).map(|x| &x.tok) != Some(&Tok::RBracket) {
                    return Err(error(pos, "E_SYNTAX", "only pub[pkg] package visibility is supported"));
                }
                j += 3;
                Visibility::Package
            } else { Visibility::Public };
            let mut kind = "";
            if word(&t, j, "class") || word(&t, j, "fnc") {
                kind = if word(&t, j, "class") { "class" } else { "fnc" };
                j += 1;
            }
            let id = name(&t, j)?;
            if t.get(j + 1).map(|x| &x.tok) != Some(&Tok::Semi) {
                return Err(error(pos, "E_SYNTAX", "export must end with semicolon"));
            }
            if exports.iter().any(|e| e.name == id) {
                return Err(error(pos, "E_DUPLICATE", format!("duplicate exported name '{id}'")));
            }
            exports.push(Export { name: id, kind, visibility, pos });
            i = j + 2;
            continue;
        }
        if word(&t, i, "external") {
            let (next, foreign_name) = external_prototype(&t, i)?;
            if !foreign.insert(foreign_name) {
                return Err(error(pos, "E_DUPLICATE", "duplicate external prototype"));
            }
            i = next;
            continue;
        }
        if word(&t, i, "internal") {
            if !word(&t, i + 1, "fnc") {
                return Err(error(pos, "E_UNSUPPORTED", "only source-file local internal fnc is admitted"));
            }
            i += 1;
            continue;
        }
        if word(&t, i, "protected") {
            if !word(&t, i + 1, "final") {
                return Err(error(pos, "E_UNSUPPORTED", "protected field requires final class-only profile"));
            }
            out.push(Token { tok: Tok::Ident("private".into()), pos });
            i += 1;
            continue;
        }
        if t[i].tok == Tok::Colon && out.len() >= 4 {
            let n = out.len();
            if word(&out, n - 4, "private") && word(&out, n - 3, "let") &&
                matches!(out[n - 2].tok, Tok::Ident(_)) &&
                matches!(out[n - 1].tok, Tok::Ident(_)) {
                out.push(Token { tok: Tok::Assign, pos });
                i += 1;
                continue;
            }
        }
        out.push(t[i].clone());
        i += 1;
    }
    for x in &out {
        if let Tok::Ident(n) = &x.tok {
            if foreign.contains(n) {
                return Err(error(x.pos, "E_UNSUPPORTED",
                    format!("foreign prototype '{n}' cannot be referenced without a validated ABI")));
            }
        }
    }
    // Export-name resolution is deferred to resolve_exports after parsing.
    // A token sweep cannot prove source-level class/function membership.
    let mut lowered = Vec::with_capacity(out.len() + exports.len());
    for j in 0..out.len() {
        if word(&out, j, "define") && word(&out, j + 1, "class") {
            if let Some(Tok::Ident(id)) = out.get(j + 2).map(|x| &x.tok) {
                if exports.iter().any(|e| e.name == *id && e.kind == "class" &&
                       e.visibility == Visibility::Public) &&
                    !(j > 0 && word(&out, j - 1, "pub")) {
                    lowered.push(Token { tok: Tok::Ident("pub".into()), pos: out[j].pos });
                }
            }
        }
        lowered.push(out[j].clone());
    }
    Ok(Lowered { tokens: lowered, exports })
}
fn leb(bytes: &mut Vec<u8>, mut v: usize) {
    while v >= 128 { bytes.push((v as u8 & 127) | 128); v >>= 7; }
    bytes.push(v as u8);
}
/// Versioned and deterministic checked metadata; never a host Wasm export.
pub fn metadata(bytes: &mut Vec<u8>, exports: &[Export]) {
    if exports.is_empty() { return; }
    let section_name = b"atto.visibility.profile.v1";
    let mut section = vec![];
    leb(&mut section, section_name.len());
    section.extend_from_slice(section_name);
    leb(&mut section, exports.len());
    for e in exports {
        leb(&mut section, e.name.len());
        section.extend_from_slice(e.name.as_bytes());
        section.push(match e.visibility { Visibility::Public => 1, Visibility::Package => 2 });
        section.push(if e.kind == "class" { 1 } else { 2 });
    }
    bytes.push(0);
    leb(bytes, section.len());
    bytes.extend_from_slice(&section);
}
