//! UTF-8 lexer for the browser AttoLang subset.
//!
//! Follows spec chapter 16 lexical rules: case-sensitive identifiers that start
//! with a letter or `_`, `//` line comments, nesting `/* */` block comments,
//! decimal integers with `_` separators, `"..."`/`'...'` strings.
//! Floats, imaginary literals, templates and Symbols are recognised so that
//! they can be rejected with a precise diagnostic instead of a generic error.

use crate::diag::{Diagnostic, Pos};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    Ident(String),
    /// Decimal integer literal. `None` means it exceeds 2^63 (only valid
    /// directly after unary minus as `-9223372036854775808`).
    Int(Option<u64>),
    /// Float literal, stored as `f64::to_bits` so `Tok` stays `Eq`.
    Float(u64),
    Str(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Semi,
    Comma,
    Colon,
    ColonColon,
    Arrow,
    FatArrow,
    Dot,
    /// Exact contiguous `...` token. Interpretation is restricted to pattern context.
    Ellipsis,
    Assign,
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    PlusPlus,
    PlusAssign,
    Minus,
    MinusMinus,
    Star,
    /// Contiguous `yield*` delegation token; whitespace makes it two tokens.
    YieldStar,
    Slash,
    Bang,
    Question,
    Pipe,
    PipeGt,
    Amp,
    At,
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub pos: Pos,
}

pub const MAX_TOKENS: usize = 32_768;
pub const MAX_STRING_BYTES: usize = 4_096;

pub fn lex(source: &str) -> Result<Vec<Token>, Diagnostic> {
    let chars: Vec<char> = source.chars().collect();
    let mut out = Vec::new();
    let (mut i, mut line, mut col) = (0usize, 1u32, 1u32);
    macro_rules! bump {
        () => {{
            if chars[i] == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
            i += 1;
        }};
    }
    while i < chars.len() {
        let c = chars[i];
        let pos = Pos { line, col };
        if c == '\0' {
            return Err(Diagnostic::new(pos, "E_NUL", "NUL characters are not allowed in source"));
        }
        if c == ' ' || c == '\t' || c == '\r' || c == '\n' {
            bump!();
            continue;
        }
        if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                bump!();
            }
            continue;
        }
        if c == '/' && chars.get(i + 1) == Some(&'*') {
            let mut depth = 0usize;
            loop {
                if i >= chars.len() {
                    return Err(Diagnostic::new(pos, "E_COMMENT", "unterminated block comment"));
                }
                if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
                    depth += 1;
                    bump!();
                    bump!();
                } else if chars[i] == '*' && chars.get(i + 1) == Some(&'/') {
                    depth -= 1;
                    bump!();
                    bump!();
                    if depth == 0 {
                        break;
                    }
                } else {
                    bump!();
                }
            }
            continue;
        }
        if out.len() >= MAX_TOKENS {
            return Err(Diagnostic::new(pos, "E_SOURCE_LIMIT", "too many tokens"));
        }
        if c.is_alphabetic() || c == '_' {
            let mut s = String::new();
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                s.push(chars[i]);
                bump!();
            }
            // Generator delegation is a single contiguous lexical spelling.
            // Do not consume a separated star: `yield *value` is not `yield*`.
            let tok = if s == "yield" && chars.get(i) == Some(&'*') {
                bump!();
                Tok::YieldStar
            } else {
                Tok::Ident(s)
            };
            out.push(Token { tok, pos });
            continue;
        }
        if c.is_ascii_digit() {
            let mut digits = String::new();
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                if chars[i] != '_' {
                    digits.push(chars[i]);
                }
                bump!();
            }
            if i < chars.len() && (chars[i] == 'x' || chars[i] == 'X' || chars[i] == 'b' || chars[i] == 'o') && digits == "0" {
                return Err(Diagnostic::new(
                    pos,
                    "E_INTEGER_LITERAL",
                    "only decimal integer literals are supported",
                ));
            }
            // Float literals follow the Java lexer exactly: digits '.' digits,
            // and/or an exponent e/E [+-] digits; '_' separators allowed.
            let mut floating = false;
            if i < chars.len() && chars[i] == '.' && chars.get(i + 1).is_some_and(|d| d.is_ascii_digit()) {
                floating = true;
                digits.push('.');
                bump!();
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    if chars[i] != '_' {
                        digits.push(chars[i]);
                    }
                    bump!();
                }
            }
            if i < chars.len() && (chars[i] == 'e' || chars[i] == 'E') {
                floating = true;
                digits.push('e');
                bump!();
                if i < chars.len() && (chars[i] == '+' || chars[i] == '-') {
                    digits.push(chars[i]);
                    bump!();
                }
                if !(i < chars.len() && chars[i].is_ascii_digit()) {
                    return Err(Diagnostic::new(pos, "E_FLOAT_LITERAL", "malformed exponent"));
                }
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    if chars[i] != '_' {
                        digits.push(chars[i]);
                    }
                    bump!();
                }
            }
            if i < chars.len() && chars[i] == 'i' && !chars.get(i + 1).is_some_and(|d| d.is_alphanumeric() || *d == '_') {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED_TYPE",
                    "imaginary literals are not supported by the browser compiler yet",
                ));
            }
            if i < chars.len() && (chars[i].is_alphabetic() || chars[i] == '_') {
                return Err(Diagnostic::new(pos, "E_INTEGER_LITERAL", "malformed integer literal"));
            }
            if floating {
                // Rust and Java both parse decimal text with correct rounding.
                let v: f64 = digits
                    .parse()
                    .map_err(|_| Diagnostic::new(pos, "E_FLOAT_LITERAL", "malformed float literal"))?;
                out.push(Token {
                    tok: Tok::Float(v.to_bits()),
                    pos,
                });
                continue;
            }
            let value = digits.parse::<u64>().ok().filter(|v| *v <= 1u64 << 63);
            if value.is_none() {
                return Err(Diagnostic::new(
                    pos,
                    "E_INTEGER_RANGE",
                    "integer literal does not fit in a signed 64-bit int",
                ));
            }
            let v = value.unwrap();
            out.push(Token {
                tok: Tok::Int(if v == 1u64 << 63 { None } else { Some(v) }),
                pos,
            });
            continue;
        }
        if c == '"' || c == '\'' {
            let quote = c;
            bump!();
            let mut s = String::new();
            loop {
                if i >= chars.len() || chars[i] == '\n' {
                    return Err(Diagnostic::new(pos, "E_STRING", "unterminated string literal"));
                }
                let ch = chars[i];
                if ch == quote {
                    bump!();
                    break;
                }
                if ch == '\\' {
                    bump!();
                    if i >= chars.len() {
                        return Err(Diagnostic::new(pos, "E_STRING", "unterminated string literal"));
                    }
                    let e = chars[i];
                    match e {
                        'n' => s.push('\n'),
                        'r' => s.push('\r'),
                        't' => s.push('\t'),
                        '"' => s.push('"'),
                        '\'' => s.push('\''),
                        '\\' => s.push('\\'),
                        'u' if chars.get(i + 1) == Some(&'{') => {
                            bump!();
                            bump!();
                            let mut hex = String::new();
                            while i < chars.len() && chars[i] != '}' && hex.len() <= 6 {
                                hex.push(chars[i]);
                                bump!();
                            }
                            if i >= chars.len() || chars[i] != '}' {
                                return Err(Diagnostic::new(pos, "E_STRING", "malformed \\u{...} escape"));
                            }
                            let cp = u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32);
                            match cp {
                                Some(cp) => s.push(cp),
                                None => return Err(Diagnostic::new(pos, "E_STRING", "invalid Unicode scalar in \\u{...} escape")),
                            }
                        }
                        other => s.push(other), // spec 16: unknown escape keeps the character
                    }
                    // Escaped characters, including Unicode scalar escapes,
                    // must obey the same decoded UTF-8 byte budget as plain
                    // characters. Without this check repeated \\u{...} could
                    // bypass MAX_STRING_BYTES and inflate tuple source data.
                    if s.len() > MAX_STRING_BYTES {
                        return Err(Diagnostic::new(pos, "E_SOURCE_LIMIT",
                            "string literal is too long"));
                    }
                    bump!();
                    continue;
                }
                s.push(ch);
                bump!();
                if s.len() > MAX_STRING_BYTES {
                    return Err(Diagnostic::new(pos, "E_SOURCE_LIMIT", "string literal is too long"));
                }
            }
            out.push(Token { tok: Tok::Str(s), pos });
            continue;
        }
        let next = chars.get(i + 1).copied();
        let (tok, len) = match (c, next) {
            ('(', _) => (Tok::LParen, 1),
            (')', _) => (Tok::RParen, 1),
            ('{', _) => (Tok::LBrace, 1),
            ('}', _) => (Tok::RBrace, 1),
            ('[', _) => (Tok::LBracket, 1),
            (']', _) => (Tok::RBracket, 1),
            (';', _) => (Tok::Semi, 1),
            (',', _) => (Tok::Comma, 1),
            (':', Some(':')) => (Tok::ColonColon, 2),
            (':', _) => (Tok::Colon, 1),
            ('-', Some('>')) => (Tok::Arrow, 2),
            ('-', Some('-')) => (Tok::MinusMinus, 2),
            ('-', _) => (Tok::Minus, 1),
            ('+', Some('+')) => (Tok::PlusPlus, 2),
            ('+', Some('=')) => (Tok::PlusAssign, 2),
            ('+', _) => (Tok::Plus, 1),
            ('.', Some('.')) if chars.get(i + 2) == Some(&'.') => (Tok::Ellipsis, 3),
            ('.', _) => (Tok::Dot, 1),
            ('=', Some('=')) => (Tok::EqEq, 2),
            ('=', Some('>')) => (Tok::FatArrow, 2),
            ('=', _) => (Tok::Assign, 1),
            ('!', Some('=')) => (Tok::NotEq, 2),
            ('!', _) => (Tok::Bang, 1),
            ('<', Some('=')) => (Tok::Le, 2),
            ('<', _) => (Tok::Lt, 1),
            ('>', Some('=')) => (Tok::Ge, 2),
            ('>', _) => (Tok::Gt, 1),
            ('*', _) => (Tok::Star, 1),
            ('/', _) => (Tok::Slash, 1),
            ('%', _) | ('^', _) => {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED",
                    "removed arithmetic operator is not part of AttoLang",
                ));
            }
            ('?', _) => (Tok::Question, 1),
            ('|', Some('>')) => (Tok::PipeGt, 2),
            ('|', _) => (Tok::Pipe, 1),
            ('&', _) => (Tok::Amp, 1),
            ('@', _) => (Tok::At, 1),
            ('`', _) => {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED",
                    "template strings are not supported by the browser compiler yet",
                ))
            }
            ('#', _) => {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED",
                    "Symbols are not supported by the browser compiler yet",
                ))
            }
            _ => return Err(Diagnostic::new(pos, "E_TOKEN", "unexpected character")),
        };
        for _ in 0..len {
            bump!();
        }
        out.push(Token { tok, pos });
    }
    out.push(Token {
        tok: Tok::Eof,
        pos: Pos { line, col },
    });
    Ok(out)
}
