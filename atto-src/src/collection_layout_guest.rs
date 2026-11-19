//! First ACTUAL guest-Wasm collection storage profile. This intentionally
//! supports only one local fixed-size Array of scalar-i64 nominal struct rows
//! in a single main(), plus checked row/column cell operations. No actor
//! transfer, dynamic indexing, escaping views, arbitrary expressions, lists,
//! nested elements, or general-purpose array API is admitted.
//!
//! This is a narrowly parsed and TYPE-CHECKED source profile. It lowers into
//! the production typed IR and uses the existing Wasm heap allocator, i64
//! memory loads/stores and checked integer arithmetic helpers. Unsupported
//! sources fail closed before artifact emission. The broader compiler must
//! eventually integrate Array as a first-class nominal generic AST type.

use crate::ast::{BinOp, Type};
use crate::check::{TExpr, TFunc, TProgram, TStmt, TE};
use crate::collection_layout_plan::{Plan, ScalarField, Storage};
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};

const MAX_FIELDS: usize = 64;
const MAX_ROWS: usize = 1024;
// Reserve some heap for the nonzero Wasm allocator start and other metadata.
const MAX_GUEST_ARRAY_BYTES: u64 = (crate::wasm::HEAP_PAGES as u64) * 65_536 - 4_096;

fn error(pos: Pos, code: &'static str, msg: impl Into<String>) -> Diagnostic {
    Diagnostic::new(pos, code, msg)
}

fn unsupported(pos: Pos, what: &str) -> Diagnostic {
    error(pos, "E_UNSUPPORTED", format!("collection guest v1 does not support {what}"))
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ResolvedType {
    nominal_struct: String,
    layout: Storage,
}

struct Parser<'a> {
    tokens: &'a [Token],
    at: usize,
}
impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token]) -> Self { Self { tokens, at: 0 } }
    fn pos(&self) -> Pos { self.tokens.get(self.at).map_or(Pos::default(), |t| t.pos) }
    fn peek(&self) -> &Tok { &self.tokens[self.at].tok }
    fn take(&mut self) -> Tok {
        let tok = self.peek().clone();
        if tok != Tok::Eof { self.at += 1; }
        tok
    }
    fn eat(&mut self, tok: Tok) -> bool {
        if *self.peek() == tok { self.take(); true } else { false }
    }
    fn expect(&mut self, tok: Tok, expected: &str) -> Result<(), Diagnostic> {
        if self.eat(tok) { Ok(()) } else {
            Err(error(self.pos(), "E_LAYOUT_SYNTAX", format!("expected {expected}")))
        }
    }
    fn word(&mut self, want: &str) -> Result<(), Diagnostic> {
        match self.peek() {
            Tok::Ident(v) if v == want => { self.take(); Ok(()) },
            _ => Err(error(self.pos(), "E_LAYOUT_SYNTAX", format!("expected '{want}'"))),
        }
    }
    fn ident(&mut self) -> Result<String, Diagnostic> {
        match self.take() {
            Tok::Ident(s) => Ok(s),
            _ => Err(error(self.pos(), "E_LAYOUT_SYNTAX", "expected identifier")),
        }
    }
    fn number(&mut self) -> Result<i64, Diagnostic> {
        let pos = self.pos();
        let neg = self.eat(Tok::Minus);
        match self.take() {
            Tok::Int(Some(n)) if (!neg && n <= i64::MAX as u64)
                || (neg && n <= (i64::MAX as u64) + 1) => {
                if neg && n == (i64::MAX as u64) + 1 { Ok(i64::MIN) }
                else if neg { Ok(-(n as i64)) }
                else { Ok(n as i64) }
            }
            _ => Err(error(pos, "E_INTEGER_RANGE", "the scalar layout profile needs a signed i64 constant")),
        }
    }
    fn index(&mut self, len: usize) -> Result<u64, Diagnostic> {
        let pos = self.pos();
        self.expect(Tok::LBracket, "'['")?;
        let n = self.number()?;
        self.expect(Tok::RBracket, "']'")?;
        if n < 0 || n as u64 >= len as u64 {
            return Err(error(pos, "E_LAYOUT_BOUNDS", "array index outside the logical length"));
        }
        Ok(n as u64)
    }
}

/// Reuse the production parser's canonical generic argument resolution.
/// Guest admission remains restricted to a proved local nominal struct.
fn collection_type(p: &mut Parser<'_>, nominal: &str) -> Result<ResolvedType, Diagnostic> {
    let (specialization, next) = crate::collection_layout_type::parse(p.tokens, p.at)?;
    p.at = next;
    if specialization.element != nominal {
        return Err(error(specialization.pos, "E_UNKNOWN_TYPE",
            format!("this scope declares '{nominal}', not '{}'", specialization.element)));
    }
    Ok(ResolvedType { nominal_struct: specialization.element, layout: specialization.layout })
}

fn struct_row(p: &mut Parser<'_>, struct_name: &str, fields: &[String]) -> Result<Vec<i64>, Diagnostic> {
    let pos = p.pos();
    p.word(struct_name)?;
    let braces = if p.eat(Tok::LParen) { false } else {
        p.expect(Tok::LBrace, "'(' or '{' after struct constructor")?;
        true
    };
    let mut out = vec![None; fields.len()];
    let mut count = 0usize;
    loop {
        let field_pos = p.pos();
        let field = p.ident()?;
        if braces { p.expect(Tok::Colon, "':' in struct initializer")?; }
        else { p.expect(Tok::Assign, "'=' in struct initializer")?; }
        let value = p.number()?;
        let idx = fields.iter().position(|f| f == &field)
            .ok_or_else(|| error(field_pos, "E_STRUCT_FIELD", format!("unknown field '{field}'")))?;
        if out[idx].replace(value).is_some() {
            return Err(error(field_pos, "E_STRUCT_FIELD", format!("duplicate field '{field}'")));
        }
        count += 1;
        if count > fields.len() { return Err(error(pos, "E_STRUCT_FIELD", "too many initializers")); }
        if !p.eat(Tok::Comma) { break; }
    }
    p.expect(if braces { Tok::RBrace } else { Tok::RParen }, "end of struct constructor")?;
    if out.iter().any(Option::is_none) {
        return Err(error(pos, "E_STRUCT_FIELD", "missing required struct field"));
    }
    Ok(out.into_iter().map(|v| v.expect("validated all fields")).collect())
}

fn loc() -> TE {
    TE { e: TExpr::Local(0), ty: Type::Array(0) }
}
fn i64_const(n: i64) -> TE {
    TE { e: TExpr::I64(n), ty: Type::Int }
}
fn cell(offset: u32) -> TE {
    TE { e: TExpr::CollectionLoad { array: Box::new(loc()), offset }, ty: Type::Int }
}
fn write(offset: u32, value: TE) -> TStmt {
    TStmt::CollectionStore { array: loc(), offset, value }
}

fn build(p: &mut Parser<'_>) -> Result<TProgram, Diagnostic> {
    p.word("define")?;
    p.word("struct")?;
    let nominal = p.ident()?;
    p.expect(Tok::LBrace, "'{' in struct declaration")?;
    let mut fields: Vec<String> = Vec::new();
    while *p.peek() != Tok::RBrace {
        if fields.len() >= MAX_FIELDS {
            return Err(error(p.pos(), "E_SOURCE_LIMIT", "too many scalar struct fields"));
        }
        let pos = p.pos();
        let f = p.ident()?;
        if fields.contains(&f) { return Err(error(pos, "E_STRUCT_FIELD", "duplicate declared field")); }
        p.expect(Tok::Colon, "':' after struct field")?;
        if p.word("int").is_err() { return Err(unsupported(pos, "non-int struct fields")); }
        p.expect(Tok::Semi, "';' after struct field")?;
        fields.push(f);
    }
    p.expect(Tok::RBrace, "'}' after struct definition")?;
    if fields.is_empty() { return Err(error(p.pos(), "E_STRUCT_FIELD", "struct cannot be empty")); }
    p.eat(Tok::Semi);
    p.word("fnc")?;
    p.word("main")?;
    p.expect(Tok::LParen, "'(' after main")?;
    p.expect(Tok::RParen, "')' after main")?;
    p.expect(Tok::Arrow, "'->' after main")?;
    p.word("int")?;
    p.expect(Tok::LBrace, "'{' in main")?;
    p.word("let")?;
    let variable = p.ident()?;
    p.expect(Tok::Colon, "':' after binding")?;
    let ty = collection_type(p, &nominal)?;
    debug_assert_eq!(ty.nominal_struct, nominal);
    p.expect(Tok::Assign, "'=' after Array type")?;
    p.expect(Tok::LBracket, "'[' for array initializer")?;
    let mut rows: Vec<Vec<i64>> = Vec::new();
    if *p.peek() != Tok::RBracket {
        loop {
            if rows.len() >= MAX_ROWS { return Err(error(p.pos(), "E_SOURCE_LIMIT", "array literal exceeds 1024 rows")); }
            rows.push(struct_row(p, &nominal, &fields)?);
            if !p.eat(Tok::Comma) { break; }
            if *p.peek() == Tok::RBracket { return Err(error(p.pos(), "E_LAYOUT_SYNTAX", "trailing row comma")); }
        }
    }
    p.expect(Tok::RBracket, "']' after array literal")?;
    p.expect(Tok::Semi, "';' after binding")?;

    let plan = Plan::new(ty.layout, vec![ScalarField { size: 8, align: 8 }; fields.len()], rows.len() as u64)
        .map_err(|e| error(p.pos(), "E_LAYOUT_SIZE", format!("cannot represent collection physical layout: {e:?}")))?;
    if plan.total_bytes > MAX_GUEST_ARRAY_BYTES {
        return Err(error(p.pos(), "E_LAYOUT_SIZE", "array exceeds the guest heap budget"));
    }
    let bytes = u32::try_from(plan.total_bytes.max(8))
        .map_err(|_| error(p.pos(), "E_LAYOUT_SIZE", "array is too large for wasm32"))?;
    let mut body = vec![TStmt::Set(0, TE { e: TExpr::CollectionAlloc(bytes), ty: Type::Array(0) })];
    for (row, values) in rows.iter().enumerate() {
        for (field, value) in values.iter().enumerate() {
            let offset = plan.offset(row as u64, field).ok_or_else(||
                error(p.pos(), "E_LAYOUT_BOUNDS", "invalid field allocation offset"))?;
            body.push(write(offset as u32, i64_const(*value)));
        }
    }

    // Only checked fixed-index writes are admitted. Disallow address-taking,
    // column views that escape, or any borrowed row alias.
    while !matches!(p.peek(), Tok::Ident(x) if x == "return") {
        let pos = p.pos();
        let owner = p.ident()?;
        if owner != variable { return Err(unsupported(pos, "non-owner mutation")); }
        let row = p.index(rows.len())?;
        p.expect(Tok::Dot, "'.' before field")?;
        let field = p.ident()?;
        let idx = fields.iter().position(|f| f == &field)
            .ok_or_else(|| error(pos, "E_STRUCT_FIELD", "unknown struct field"))?;
        p.expect(Tok::PlusAssign, "'+=' on mutable scalar cell")?;
        let delta = p.number()?;
        p.expect(Tok::Semi, "';' after mutation")?;
        let offset = plan.offset(row, idx).ok_or_else(||
            error(pos, "E_LAYOUT_BOUNDS", "invalid mutation offset"))? as u32;
        body.push(write(offset, TE {
            e: TExpr::Bin(BinOp::Add, Box::new(cell(offset)), Box::new(i64_const(delta))),
            ty: Type::Int,
        }));
    }

    p.word("return")?;
    let pos = p.pos();
    let owner = p.ident()?;
    if owner != variable { return Err(error(pos, "E_UNBOUND", "return must read from the array owner")); }
    p.expect(Tok::Dot, "'.' in column read")?;
    p.word("columns")?;
    p.expect(Tok::Dot, "'.' before column name")?;
    let f = p.ident()?;
    let field = fields.iter().position(|x| x == &f)
        .ok_or_else(|| error(pos, "E_STRUCT_FIELD", "unknown column"))?;
    let row = p.index(rows.len())?;
    p.expect(Tok::Semi, "';' after return")?;
    p.expect(Tok::RBrace, "'}' after main")?;
    if *p.peek() != Tok::Eof {
        return Err(unsupported(p.pos(), "additional top-level source after main"));
    }
    let offset = plan.offset(row, field)
        .ok_or_else(|| error(pos, "E_LAYOUT_BOUNDS", "invalid column read"))? as u32;
    body.push(TStmt::Return(Some(cell(offset))));
    Ok(TProgram {
        funcs: vec![TFunc { name: "main".to_owned(), params: vec![], ret: Type::Int,
            locals: vec![Type::Array(0)], body }],
        generators: vec![], main: 0, imports: vec![], data: vec![],
        heap: true, globals: vec![], actors: vec![],
        strings: false, guest_eh: false, raise_tag: false, catch_depth: false,
    })
}

/// If the source requests the strictly supported fixed-scalar struct+Array
/// profile, build and return its checked, typed program. All other sources
/// remain on the existing production parser and reject unsupported syntax.
pub fn try_lower(toks: &[Token]) -> Result<Option<TProgram>, Diagnostic> {
    let has_struct = toks.windows(2).any(|pair|
        matches!((&pair[0].tok, &pair[1].tok),
            (Tok::Ident(a), Tok::Ident(b)) if a == "define" && b == "struct"));
    let has_array = toks.windows(2).any(|pair|
        matches!((&pair[0].tok, &pair[1].tok),
            (Tok::Ident(a), Tok::Lt) if a == "Array"));
    if !has_struct || !has_array { return Ok(None); }
    build(&mut Parser::new(toks)).map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;
    const PROGRAM: &str = r#"
define struct Particle {
    x: int;
    y: int;
    velocity: int;
}
fnc main() -> int {
    let particles: Array<Particle, layout=soa> = [
        Particle(x=10, y=20, velocity=1),
        Particle(x=30, y=40, velocity=2)
    ];
    particles[0].x += 5;
    return particles.columns.x[0];
}
"#;

    fn compiler(src: &str) -> Result<Vec<u8>, Diagnostic> { crate::compile(src) }

    #[test]
    fn lowers_real_scalar_columns_to_existing_guest_wasm_emitter() {
        let wasm = compiler(PROGRAM).unwrap();
        assert_eq!(&wasm[..4], b"\0asm");
        assert!(wasm.len() > 40);
        let typed = try_lower(&crate::lexer::lex(PROGRAM).unwrap()).unwrap().unwrap();
        let TStmt::CollectionStore { offset: ox0, .. } = &typed.funcs[0].body[1] else { panic!("missing first field store") };
        let TStmt::CollectionStore { offset: oy0, .. } = &typed.funcs[0].body[2] else { panic!("missing second field store") };
        let TStmt::CollectionStore { offset: ox1, .. } = &typed.funcs[0].body[4] else { panic!("missing second-row field store") };
        assert_eq!((*ox0, *ox1, *oy0), (0, 8, 16)); // true column-major physical addresses
    }

    #[test]
    fn canonical_named_order_compiles_to_byte_identical_wasm() {
        let a = compiler(PROGRAM).unwrap();
        let b = compiler(&PROGRAM.replace("Array<Particle, layout=soa>",
            "Array<layout=soa, T=Particle>")).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn rejection_is_fail_closed_and_emits_no_bytes() {
        for (replacement, code) in [
            ("Array<Particle, layout=wat>", "E_LAYOUT_VALUE"),
            ("Array<Particle, layout=aosoa(0)>", "E_LAYOUT_SIZE"),
            ("Array<Particle, layout=aosoa(n)>", "E_LAYOUT_SIZE"),
            ("Array<Particle, layout=soa, layout=aos>", "E_GENERIC_DUP"),
            ("Array<layout=soa, Particle>", "E_GENERIC_ORDER"),
            ("Array<Particle, layout=soa, nope=1>", "E_GENERIC_NAME"),
            ("Array<Wrong, layout=soa>", "E_UNKNOWN_TYPE"),
        ] {
            let bad = PROGRAM.replace("Array<Particle, layout=soa>", replacement);
            assert_eq!(compiler(&bad).unwrap_err().code, code, "{replacement}");
        }
        assert_eq!(compiler(&PROGRAM.replace("particles[0].x += 5", "particles[2].x += 5"))
            .unwrap_err().code, "E_LAYOUT_BOUNDS");
        assert_eq!(compiler(&PROGRAM.replace("return particles.columns.x[0]", "return particles.columns.x[2]"))
            .unwrap_err().code, "E_LAYOUT_BOUNDS");
        assert_eq!(compiler(&PROGRAM.replace("velocity: int;", "velocity: string;"))
            .unwrap_err().code, "E_UNSUPPORTED");
    }

    #[test]
    fn accepts_aosoa_tail_and_aos_using_same_typed_address_plan() {
        for layout in ["aos", "aosoa(16)"] {
            let wasm = compiler(&PROGRAM.replace("layout=soa", &format!("layout={layout}"))).unwrap();
            assert_eq!(&wasm[..4], b"\0asm");
        }
    }

    #[test]
    fn default_aos_has_same_specialization_as_explicit_aos() {
        let explicit = PROGRAM.replace("layout=soa", "layout=aos");
        let implicit = PROGRAM.replace("Array<Particle, layout=soa>", "Array<Particle>");
        assert_eq!(compiler(&explicit).unwrap(), compiler(&implicit).unwrap());
    }

    #[test]
    fn struct_brace_and_equals_initializers_have_equal_guest_meaning() {
        let braces = PROGRAM.replace("Particle(x=10, y=20, velocity=1)",
            "Particle{x: 10, y: 20, velocity: 1}")
            .replace("Particle(x=30, y=40, velocity=2)",
            "Particle{velocity: 2, x: 30, y: 40}");
        assert_eq!(compiler(PROGRAM).unwrap(), compiler(&braces).unwrap());
    }

    #[test]
    fn duplicate_or_unknown_struct_fields_are_compile_failures() {
        for change in [
            "Particle(x=10, x=20, velocity=1)",
            "Particle(x=10, unknown=20, velocity=1)",
            "Particle(x=10, y=20)",
        ] {
            assert_eq!(compiler(&PROGRAM.replace("Particle(x=10, y=20, velocity=1)", change))
                .unwrap_err().code, "E_STRUCT_FIELD");
        }
    }

    #[test]
    fn rejects_nested_expressions_or_unverified_borrow_paths() {
        let bad = PROGRAM.replace("Particle(x=10", "Particle(x=1+9");
        assert!(compiler(&bad).is_err());
        let bad = PROGRAM.replace("particles[0].x += 5;", "let unsafe_alias = particles.columns.x;");
        assert!(compiler(&bad).is_err());
    }
}
