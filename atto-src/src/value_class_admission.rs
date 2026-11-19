//! Fail-closed source admission for identity-free value classes.
//!
//! AttoLang value classes have no observable identity. Ordinary class/struct
//! browser lowering currently allocates objects and rejects class equality,
//! so accepting `define value class` by token rewriting would be unsound.
//! This bounded preflight recognizes the declaration header early, reports a
//! stable diagnostic, and never emits a guest Wasm artifact. It is NOT a
//! value-class implementation or proof of semantic conformance.
use crate::diag::Diagnostic;
use crate::lexer::{Tok, Token};

fn word(t: &[Token], i: usize, value: &str) -> bool {
    matches!(t.get(i).map(|x| &x.tok), Some(Tok::Ident(s)) if s == value)
}

/// Require the dedicated value-type backend before admitting the new syntax.
/// Future backends MUST replace this gate with real checked value construction,
/// immutable storage, recursive equality, copy and AOT layout.
pub fn preflight(t: &[Token]) -> Result<(), Diagnostic> {
    let mut braces = 0usize;
    for i in 0..t.len() {
        let at_top = braces == 0;
        if at_top {
            // Old and canonical publication spellings:
            //   define value class T ...
            //   define pub value class T ...
            //   pub define value class T ...
            let header = (word(t, i, "define") && word(t, i + 1, "value")
                && word(t, i + 2, "class"))
                || (word(t, i, "define") && word(t, i + 1, "pub")
                    && word(t, i + 2, "value") && word(t, i + 3, "class"))
                || (word(t, i, "pub") && word(t, i + 1, "define")
                    && word(t, i + 2, "value") && word(t, i + 3, "class"));
            if header {
                return Err(Diagnostic::new(t[i].pos, "E_VALUE_UNSUPPORTED",
                    "identity-free value class recognized, but this backend lacks immutable value storage, value equality and a proven AOT layout; no guest was emitted"));
            }
        }
        match &t[i].tok {
            Tok::LBrace => braces = braces.saturating_add(1),
            Tok::RBrace => braces = braces.saturating_sub(1),
            _ => {}
        }
    }
    Ok(())
}
