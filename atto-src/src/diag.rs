//! Source positions and compiler diagnostics.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Pos {
    pub line: u32,
    pub col: u32,
}

/// A single fail-closed compiler diagnostic. `code` is a stable machine
/// readable identifier (for example `E_IMMUTABLE`); `message` is prose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub pos: Pos,
    pub code: &'static str,
    pub message: String,
}

impl Diagnostic {
    pub fn new(pos: Pos, code: &'static str, message: impl Into<String>) -> Self {
        Diagnostic {
            pos,
            code,
            message: message.into(),
        }
    }

    /// `E_CODE: message`, the format the playground displays.
    pub fn render(&self) -> String {
        format!("{}: {}", self.code, self.message)
    }
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.pos.line, self.pos.col, self.render())
    }
}
