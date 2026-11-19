//! Recursive-descent parser for the browser AttoLang subset.
//!
//! The grammar follows `docs/grammar.ebnf` (Oreslang v0.6) in the Java
//! reference compiler and spec chapter 16. Constructs outside the admitted
//! subset are recognised and rejected with `E_UNSUPPORTED` rather than being
//! mis-parsed or silently approximated.

use crate::ast::*;
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};

pub const MAX_DEPTH: u32 = 128;
pub const MAX_FUNCS: usize = 1024;
pub const MAX_PARAMS: usize = 32;
/// Members (fields, methods, constructor, receive) in one class or actor,
/// and variants in one enum.
pub const MAX_MEMBERS: usize = 256;
/// Bound on the height of any syntax tree the parser builds. Left-associative
/// operator chains (`a + b + ...`) and `elif` arms are parsed iteratively but
/// produce trees that the checker, emitter and `Drop` walk recursively, so
/// each chain link counts against this budget as well as each nested level.
pub const MAX_TREE_HEIGHT: u32 = 256;

/// Words reserved by the reference lexer (spec chapter 16 keyword table).
const RESERVED: &[&str] = &[
    "define",
    "def",
    "module",
    "namespace",
    "contract",
    "conforms",
    "class",
    "struct",
    "interface",
    "trait",
    "type",
    "types",
    "typeof",
    "abstract",
    "extends",
    "implements",
    "impl",
    "import",
    "from",
    "as",
    "using",
    "fnc",
    "routine",
    "pure",
    "async",
    "suspends",
    "generator",
    "yield",
    "nlex",
    "return",
    "self",
    "super",
    "static",
    "pub",
    "private",
    "const",
    "val",
    "let",
    "mut",
    "if",
    "guard",
    "then",
    "else",
    "elif",
    "elseif",
    "fi",
    "do",
    "done",
    "end",
    "while",
    "for",
    "of",
    "loop",
    "block",
    "break",
    "continue",
    "switch",
    "match",
    "matches",
    "over",
    "default",
    "try",
    "catch",
    "finally",
    "throw",
    "raise",
    "panic",
    "recover",
    "trap",
    "defer",
    "actor",
    "persistent",
    "durable",
    "isoactor",
    "shared",
    "untrusted",
    "spawn",
    "stop",
    "rt",
    "await",
    "nb",
    "cb",
    "select",
    "readch",
    "writech",
    "eq",
    "neq",
    "is",
    "new",
    "true",
    "false",
    "null",
    "void",
    "obj",
    "arr",
    "cpu",
    "gpu",
    "quantum",
];

/// Statement-leading keywords that name real AttoLang features this compiler
/// does not lower yet. They are rejected, never approximated.
const UNSUPPORTED_STMT: &[&str] = &[
    "using",
    "switch",
    "try",
    "select",
    "defer",
    "throw",
    "raise",
    "panic",
    "recover",
    "trap",
    "spawn",
    "await",
    "actor",
    "persistent",
    "durable",
    "isoactor",
    "define",
    "import",
    "async",
    "yield",
    "nb",
    "cb",
    "readch",
    "writech",
    "rt",
    "class",
    "struct",
    "module",
    "namespace",
    "interface",
    "trait",
    "type",
    "generator",
    "critical",
    "stop",
];

const UNSUPPORTED_TYPES: &[&str] = &[
    "f32",
    "decimal",
    "complex",
    "complex64",
    "complex128",
    "bigint",
    "i8",
    "i16",
    "i32",
    "i64",
    "u8",
    "u16",
    "u32",
    "u64",
    "uint",
    "Symbol",
    "Option",
    "Result",
    "Array",
    "List",
    "Vector",
    "Slice",
    "Tuple",
    "FixedArray",
    "FixedList",
    "Map",
    "Set",
    "char",
    "byte",
];

pub fn is_reserved(name: &str) -> bool {
    RESERVED.contains(&name)
}

#[derive(Clone)]
pub struct Parser {
    toks: Vec<Token>,
    i: usize,
    depth: u32,
    /// Height of the tree path being built; see [`MAX_TREE_HEIGHT`].
    height: u32,
    /// Nonzero while parsing an if/while condition head, where `,` and `|` are
    /// boolean AND / OR (spec chapter 16).
    cond: u32,
    /// Spellings of user type references, see `Type::Named`.
    type_names: Vec<(String, Pos)>,
    /// Canonically interned nominal Array<T, layout=...> type parameters.
    array_types: Vec<ArrayType>,
    /// Scope of an explicit generator function body.
    in_generator: bool,
    /// Only the outer Erlang-style callable sequence accepts commas as
    /// statement terminators. Nested C blocks keep their own grammar.
    erlang_body: bool,
    state_method: bool,
    state_binder: Option<String>,
}

struct TypeFirstField {
    field: Field,
    /// `T name: e` (class field spelling) rather than `T name = e`.
    init_was_colon: bool,
}

/// Members collected from a class or actor body.
#[derive(Default)]
struct Members {
    fields: Vec<Field>,
    ctor: Option<Constructor>,
    methods: Vec<Method>,
    receive: Option<Receive>,
    persistence_hooks: Vec<ActorPersistenceHook>,
}

type R<T> = Result<T, Diagnostic>;

fn unsupported(pos: Pos, what: &str) -> Diagnostic {
    Diagnostic::new(pos, "E_UNSUPPORTED", format!("{what} is not supported by the browser compiler yet"))
}

/// Conservative control-flow proof for guard's failure path. In particular,
/// a break/continue, an if without else, or a match without exhaustiveness
/// evidence cannot stand in for a guaranteed enclosing-function exit.
/// Later checker stages may admit richer terminal constructs only after
/// proving they cannot fall through.
fn guard_failure_exits(stmts: &[Stmt]) -> bool {
    match stmts.last() {
        Some(Stmt::Return(..) | Stmt::Throw(..)) => true,
        Some(Stmt::Block(inner)) => guard_failure_exits(inner),
        Some(Stmt::If { arms, otherwise: Some(other), .. }) =>
            !arms.is_empty()
                && arms.iter().all(|(_, branch)| guard_failure_exits(branch))
                && guard_failure_exits(other),
        _ => false,
    }
}

impl Parser {
    pub fn new(toks: Vec<Token>) -> Self {
        Parser {
            toks,
            i: 0,
            depth: 0,
            height: 0,
            cond: 0,
            type_names: Vec::new(),
            array_types: Vec::new(),
            in_generator: false,
            erlang_body: false,
            state_method: false,
            state_binder: None,
        }
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.i].tok
    }
    fn peek_at(&self, n: usize) -> &Tok {
        &self.toks[(self.i + n).min(self.toks.len() - 1)].tok
    }
    fn pos(&self) -> Pos {
        self.toks[self.i].pos
    }
    fn advance(&mut self) -> Token {
        let t = self.toks[self.i].clone();
        if self.i < self.toks.len() - 1 {
            self.i += 1;
        }
        t
    }
    fn is_word(&self, w: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if s == w)
    }
    fn word_at(&self, n: usize) -> Option<&str> {
        match self.peek_at(n) {
            Tok::Ident(s) => Some(s.as_str()),
            _ => None,
        }
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.advance();
            true
        } else {
            false
        }
    }
    fn eat_word(&mut self, w: &str) -> bool {
        if self.is_word(w) {
            self.advance();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: Tok, what: &str) -> R<()> {
        if self.eat(&t) {
            Ok(())
        } else {
            Err(self.expected(what))
        }
    }
    fn expect_word(&mut self, w: &str) -> R<()> {
        if self.eat_word(w) {
            Ok(())
        } else {
            Err(self.expected(&format!("'{w}'")))
        }
    }
    fn expected(&self, what: &str) -> Diagnostic {
        let found = describe(self.peek());
        let code = match (what, self.peek()) {
            (_, Tok::Eof) => "E_EOF",
            ("';'", _) => "E_SEMICOLON",
            _ => "E_SYNTAX",
        };
        Diagnostic::new(self.pos(), code, format!("expected {what}, found {found}"))
    }
    fn enter(&mut self) -> R<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(Diagnostic::new(
                self.pos(),
                "E_NESTING",
                format!("nesting deeper than {MAX_DEPTH} levels"),
            ));
        }
        self.grow(1)
    }
    fn leave(&mut self) {
        self.depth -= 1;
        self.height -= 1;
    }
    /// Account for `n` more levels of tree height (one chain link or arm).
    fn grow(&mut self, n: u32) -> R<()> {
        self.height += n;
        if self.height > MAX_TREE_HEIGHT {
            return Err(Diagnostic::new(
                self.pos(),
                "E_NESTING",
                format!("expression or elif chain deeper than {MAX_TREE_HEIGHT} levels"),
            ));
        }
        Ok(())
    }

    fn ident(&mut self, what: &str) -> R<(String, Pos)> {
        let pos = self.pos();
        match self.peek().clone() {
            Tok::Ident(s) => {
                if is_reserved(&s) {
                    return Err(Diagnostic::new(
                        pos,
                        "E_RESERVED",
                        format!("'{s}' is a reserved word and cannot be used as {what}"),
                    ));
                }
                self.advance();
                Ok((s, pos))
            }
            _ => Err(self.expected(what)),
        }
    }

    // ---------------------------------------------------------------- types

    fn is_type_word(&self, n: usize) -> bool {
        matches!(
            self.word_at(n),
            Some("int" | "bool" | "boolean" | "void" | "float" | "f64" | "string" | "String" | "fnc")
        ) || self.word_at(n).is_some_and(|w| UNSUPPORTED_TYPES.contains(&w))
    }

    fn parse_type(&mut self) -> R<Type> {
        let pos = self.pos();
        let name = match self.peek() {
            Tok::Ident(s) => s.clone(),
            _ => return Err(self.expected("a type")),
        };
        self.advance();
        let ty = match name.as_str() {
            "int" => Type::Int,
            "Array" => {
                // Reuse the exact same generic binder used by the already
                // executable, bounded scalar-collection guest profile.
                let (specialization, next) = crate::collection_layout_type::parse(&self.toks, self.i - 1)?;
                self.i = next;
                let idx = self.array_types.iter().position(|t|
                    t.element == specialization.element && t.layout == specialization.layout);
                let idx = match idx {
                    Some(existing) => existing as u32,
                    None => {
                        let idx = self.array_types.len() as u32;
                        self.array_types.push(specialization);
                        idx
                    }
                };
                Type::Array(idx)
            },
            "fnc" => {
                // Canonical source type form: fnc(int, bool) -> float.
                // The first profile admits scalar callback contracts only,
                // without silently treating callable types as runtime values.
                self.expect(Tok::LParen, "'(' after fnc callable type")?;
                let mut params = Vec::<Type>::new();
                if *self.peek() != Tok::RParen {
                    loop {
                        if params.len() >= MAX_PARAMS {
                            return Err(Diagnostic::new(self.pos(), "E_SOURCE_LIMIT",
                                "callable signature exceeds maximum parameter count"));
                        }
                        let arg_pos = self.pos();
                        let arg = self.parse_type()?;
                        if !matches!(arg, Type::Int | Type::Bool | Type::Float | Type::Str) {
                            return Err(Diagnostic::new(arg_pos, "E_UNSUPPORTED_TYPE",
                                "callable parameter must be a non-void scalar type"));
                        }
                        params.push(arg);
                        if !self.eat(&Tok::Comma) { break; }
                    }
                }
                self.expect(Tok::RParen, "')' after callable parameters")?;
                self.expect(Tok::Arrow, "'->' before callable result type")?;
                let result_pos = self.pos();
                let result = self.parse_type()?;
                if !matches!(result,
                    Type::Int | Type::Bool | Type::Float | Type::Str | Type::Void) {
                    return Err(Diagnostic::new(result_pos, "E_UNSUPPORTED_TYPE",
                        "callable return type must be scalar or void"));
                }
                let spelling = format!("fnc({})->{}",
                    params.iter().map(|t| t.name()).collect::<Vec<_>>().join(","),
                    result.name());
                // Identical contracts have identical Type identity across
                // declarations, regardless of whitespace and type aliases.
                let id = match self.type_names.iter().position(|(n, _)| *n == spelling) {
                    Some(existing) => existing as u32,
                    None => self.type_name(spelling, pos),
                };
                Type::Callable(id)
            }
            "Option" => {
                self.expect(Tok::Lt, "'<' after Option")?;
                let inner = self.parse_type()?;
                self.expect(Tok::Gt, "'>' after Option payload")?;
                match inner {
                    Type::Int => Type::OptionInt,
                    Type::ResultIntStr => Type::OptionResultIntStr,
                    _ => return Err(Diagnostic::new(pos, "E_UNSUPPORTED_TYPE",
                        "browser ADT admits only Option<int> and Option<Result<int,string>>")),
                }
            }
            "Generator" => {
                self.expect(Tok::Lt, "'<' after Generator")?;
                let inner = self.parse_type()?;
                self.expect(Tok::Gt, "'>' after Generator item type")?;
                if inner != Type::Int {
                    return Err(Diagnostic::new(pos, "E_UNSUPPORTED_TYPE",
                        "the browser generator frontend currently recognizes only Generator<int>"));
                }
                Type::GeneratorInt
            }
            "Result" => {
                self.expect(Tok::Lt, "'<' after Result")?;
                let good = self.parse_type()?;
                self.expect(Tok::Comma, "',' between Result type arguments")?;
                let bad = self.parse_type()?;
                self.expect(Tok::Gt, "'>' after Result types")?;
                if good != Type::Int || bad != Type::Str {
                    return Err(Diagnostic::new(pos, "E_UNSUPPORTED_TYPE",
                        "browser ADT v1 admits only Result<int,string>"));
                }
                Type::ResultIntStr
            },
            "bool" | "boolean" => Type::Bool,
            "void" => Type::Void,
            "float" | "f64" => Type::Float,
            "string" | "String" => Type::Str,
            n if UNSUPPORTED_TYPES.contains(&n) => {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED_TYPE",
                    format!("type '{n}' is not supported by the browser compiler yet"),
                ))
            }
            "ActorRef" => {
                self.expect(Tok::Lt, "'<' after ActorRef")?;
                let (actor, apos) = self.ident("an actor name")?;
                self.expect(Tok::Gt, "'>'")?;
                Type::NamedRef(self.type_name(actor, apos))
            }
            "ActorMail" => {
                return Err(Diagnostic::new(
                    pos,
                    "E_TYPE",
                    "ActorMail<T> is only the parameter type of an actor receive handler",
                ))
            }
            n if is_reserved(n) => return Err(Diagnostic::new(pos, "E_UNKNOWN_TYPE", format!("unknown type '{n}'"))),
            // A class or enum name; the checker resolves it.
            n => Type::Named(self.type_name(n.to_string(), pos)),
        };
        if matches!(self.peek(), Tok::Lt | Tok::LBracket | Tok::Question | Tok::Pipe) {
            return Err(unsupported(self.pos(), "generic, optional, union and sequence types"));
        }
        Ok(ty)
    }

    fn type_name(&mut self, name: String, pos: Pos) -> u32 {
        self.type_names.push((name, pos));
        (self.type_names.len() - 1) as u32
    }

    // Parse exactly one declaration at an existing token offset. This reuses
    // production nesting rules rather than scanning to the first stray 'end';
    // essential for Erlang-style methods inside a class or actor definition.
    pub(crate) fn parse_target_class_at(toks: &[Token], offset: usize) -> R<(ClassDecl, usize)> {
        let mut p = Self::new(toks.to_vec());
        p.i = offset;
        p.expect_word("define")?;
        p.expect_word("class")?;
        let decl = p.parse_class(false)?;
        Ok((decl, p.i))
    }

    pub(crate) fn parse_target_actor_at(toks: &[Token], offset: usize) -> R<(ActorDecl, usize)> {
        let mut p = Self::new(toks.to_vec());
        p.i = offset;
        p.expect_word("define")?;
        p.expect_word("actor")?;
        let decl = p.parse_actor(true, ActorPersistenceMode::Volatile)?;
        Ok((decl, p.i))
    }

    // ------------------------------------------------------------ top level

    pub fn parse_program(&mut self) -> R<Program> {
        let mut prog = Program::default();
        let mut decls = 0usize;
        while *self.peek() != Tok::Eof {
            if decls >= MAX_FUNCS {
                return Err(Diagnostic::new(
                    self.pos(),
                    "E_SOURCE_LIMIT",
                    format!("more than {MAX_FUNCS} top-level declarations"),
                ));
            }
            decls += 1;
            let public = self.is_word("pub");
            let at = usize::from(public);
            let start = self.pos();
            // Canonical 'define [pub] (persistent | durable) actor'.
            // Also retain legacy 'pub define ...' visibility placement.
            // Never downgrade a qualified actor to ordinary volatile state.
            if self.word_at(at) == Some("define") {
                let mut qualifier = at + 1;
                if self.word_at(qualifier) == Some("pub") {
                    qualifier += 1;
                }
                let mode = match self.word_at(qualifier) {
                    Some("persistent") => Some(ActorPersistenceMode::Persistent),
                    Some("durable") => Some(ActorPersistenceMode::Durable),
                    _ => None,
                };
                if let Some(mode) = mode {
                    if self.word_at(qualifier + 1) != Some("actor") {
                        return Err(Diagnostic::new(
                            start, "E_ACTOR_PERSISTENCE_MODIFIER",
                            "persistent/durable must occur once before 'actor'; not a class modifier",
                        ));
                    }
                    self.i += qualifier + 2;
                    prog.actors.push(self.parse_actor(true, mode)?);
                    continue;
                }
            }
            match (self.word_at(at), self.word_at(at + 1)) {
                (Some("define"), Some("class")) => {
                    self.i += at + 2;
                    prog.classes.push(self.parse_class(public)?);
                }
                (Some("define"), Some("state")) => {
                    self.i += at + 2;
                    prog.classes.push(self.parse_state_container(public)?);
                }
                (Some("define"), Some("actor")) => {
                    if public {
                        return Err(unsupported(start, "'pub' actors"));
                    }
                    self.i += 2;
                    let decl = self.parse_actor(true, ActorPersistenceMode::Volatile)?;
                    prog.actors.push(decl);
                }
                (Some("actor"), Some(w)) if w != "fnc" => {
                    if public {
                        return Err(unsupported(start, "'pub' actors"));
                    }
                    self.i += 1;
                    let decl = self.parse_actor(false, ActorPersistenceMode::Volatile)?;
                    prog.actors.push(decl);
                }
                (Some("define"), Some("enum")) => {
                    if public {
                        return Err(unsupported(start, "'pub' enums"));
                    }
                    self.i += 2;
                    prog.enums.push(self.parse_enum()?);
                }
                (Some("define"), Some(w)) => {
                    let what = match w {
                        "abstract" => "abstract classes".to_string(),
                        "pub" | "private" => {
                            "visibility after 'define' on classes, actors and enums (write 'pub define class')".to_string()
                        }
                        _ => format!("'define {w}' declarations"),
                    };
                    return Err(unsupported(self.pos(), &what));
                }
                _ => prog.funcs.push(self.parse_func()?),
            }
        }
        prog.type_names = std::mem::take(&mut self.type_names);
        prog.array_types = std::mem::take(&mut self.array_types);
        Ok(prog)
    }

    /// After `define class`: `Name as { class_member } end`.
    fn parse_class(&mut self, public: bool) -> R<ClassDecl> {
        let (name, pos) = self.ident("a class name")?;
        self.decl_head("class")?;
        self.expect_word("as")?;
        let m = self.parse_members(&name, false, "end")?;
        Ok(ClassDecl {
            name,
            pos,
            public,
            state_container: false,
            fields: m.fields,
            ctor: m.ctor,
            methods: m.methods,
        })
    }


    /// Browser-only single-worker state profile; class instances cannot cross
    /// guest Wasm memories. This does not provide a cross-worker RW lock.
    fn parse_state_container(&mut self, public: bool) -> R<ClassDecl> {
        self.eat_word("container"); // Java-canonical long spelling; short form is an Atto alias
        let (name, pos) = self.ident("a state container name")?;
        self.decl_head("state container")?;
        self.expect_word("as")?;
        let (mut fields, mut methods) = (Vec::new(), Vec::new());
        let mut seen = false;
        while !self.eat_word("end") {
            if *self.peek() == Tok::Eof {
                return Err(self.expected("'end' to close state container"));
            }
            if fields.len() >= 128 || methods.len() >= 64 {
                return Err(Diagnostic::new(self.pos(), "E_SOURCE_LIMIT", "protected state fields (128) or methods (64) exceed Java reference budget"));
            }
            if self.eat_word("state") {
                if seen { return Err(Diagnostic::new(self.pos(), "E_DUPLICATE", "duplicate state {} block")); }
                seen = true;
                self.expect(Tok::LBrace, "'{' after state")?;
                while !self.eat(&Tok::RBrace) {
                    if *self.peek() == Tok::Eof { return Err(self.expected("'}' after state fields")); }
                    if fields.len() >= 128 {
                        return Err(Diagnostic::new(self.pos(), "E_SOURCE_LIMIT", "protected state field budget exceeded (128)"));
                    }
                    if !self.eat_word("let") {
                        return Err(Diagnostic::new(self.pos(), "E_STATE",
                            "protected state fields must start with let, as in Java"));
                    }
                    let parsed = self.parse_type_first_field(FieldVisibility::Private, FieldMode::ActorState, FieldBinding::ActorState, false)?;
                    if !matches!(parsed.field.ty, Type::Int | Type::Bool) {
                        return Err(Diagnostic::new(parsed.field.pos, "E_UNSUPPORTED_TYPE",
                            "Worker-local state container admits only owned int/bool fields"));
                    }
                    if fields.iter().any(|f: &Field| f.name == parsed.field.name) {
                        return Err(Diagnostic::new(parsed.field.pos, "E_DUPLICATE", "duplicate state field"));
                    }
                    fields.push(parsed.field);
                }
                continue;
            }
            if !seen {
                return Err(Diagnostic::new(self.pos(), "E_STATE",
                    "protected state {} schema must precede instance methods"));
            }
            let method_public = self.eat_word("pub");
            self.eat_word("fnc");
            self.eat_word("method");
            if self.is_word("handle_state") {
                return Err(Diagnostic::new(self.pos(), "E_STATE",
                    "handle_state is compiler-owned and cannot be overridden"));
            }
            if *self.peek_at(1) != Tok::LParen {
                return Err(Diagnostic::new(self.pos(), "E_STATE",
                    "state container supports only a state {} block and instance methods"));
            }
            self.state_method = true;
            let result = self.parse_method(method_public, false);
            self.state_method = false;
            let method = result?;
            if method.params.iter().any(|p| p.name == "s") {
                return Err(Diagnostic::new(method.pos, "E_STATE_BORROW",
                    "parameter s would shadow the critical lease binder"));
            }
            if methods.iter().any(|m: &Method| m.name == method.name) {
                return Err(Diagnostic::new(method.pos, "E_DUPLICATE", "duplicate state method"));
            }
            methods.push(method);
        }
        if !seen { return Err(Diagnostic::new(pos, "E_STATE", "define state requires state {}")); }
        if fields.is_empty() {
            return Err(Diagnostic::new(pos, "E_STATE", "protected state requires at least one scalar field"));
        }
        Ok(ClassDecl { name, pos, public, state_container: true,
            fields, ctor: None, methods })
    }

    /// After `define actor` (`defined`) or a bare `actor`.
    fn parse_actor(&mut self, defined: bool, persistence: ActorPersistenceMode) -> R<ActorDecl> {
        let (name, pos) = self.ident("an actor name")?;
        self.decl_head("actor")?;
        let close = if defined {
            self.expect_word("as")?;
            "end"
        } else if self.eat(&Tok::LBrace) {
            "}"
        } else {
            "end"
        };
        let m = self.parse_members(&name, true, close)?;
        if persistence == ActorPersistenceMode::Volatile && !m.persistence_hooks.is_empty() {
            return Err(Diagnostic::new(pos, "E_PERSIST_SIGNATURE",
                "persistence hooks require a persistent actor"));
        }
        if persistence == ActorPersistenceMode::Durable && !m.persistence_hooks.is_empty() {
            return Err(Diagnostic::new(pos, "E_DURABLE_HOOK_OVERRIDE",
                "durable actor persistence is runtime-managed, not overridden by hooks"));
        }
        Ok(ActorDecl {
            name,
            pos,
            persistence,
            persistence_hooks: m.persistence_hooks,
            fields: m.fields,
            receive: m.receive,
            methods: m.methods,
        })
    }

    /// Generic parameters and inheritance clauses are outside the subset.
    fn decl_head(&mut self, kind: &str) -> R<()> {
        if *self.peek() == Tok::Lt {
            return Err(unsupported(self.pos(), &format!("generic {kind}es")));
        }
        if let Some(w @ ("extends" | "implements" | "impl" | "conforms")) = self.word_at(0) {
            return Err(unsupported(self.pos(), &format!("'{w}' on a {kind}")));
        }
        Ok(())
    }

    /// After `define enum`: `Name as Variant { Variant } end`.
    fn parse_enum(&mut self) -> R<EnumDecl> {
        let (name, pos) = self.ident("an enum name")?;
        self.decl_head("enum")?;
        self.expect_word("as")?;
        let mut variants: Vec<(String, Pos)> = Vec::new();
        while !self.eat_word("end") {
            if variants.len() >= MAX_MEMBERS {
                return Err(Diagnostic::new(
                    self.pos(),
                    "E_SOURCE_LIMIT",
                    format!("more than {MAX_MEMBERS} enum variants"),
                ));
            }
            let (v, vpos) = self.ident("an enum variant or 'end'")?;
            match self.peek() {
                Tok::LParen => return Err(unsupported(self.pos(), "enum variants with payloads")),
                Tok::Assign => return Err(unsupported(self.pos(), "enum variants with explicit values")),
                Tok::Comma => return Err(self.expected("an enum variant on its own line")),
                _ => {}
            }
            if variants.iter().any(|(w, _)| *w == v) {
                return Err(Diagnostic::new(
                    vpos,
                    "E_DUPLICATE",
                    format!("duplicate variant '{v}' in enum '{name}'"),
                ));
            }
            variants.push((v, vpos));
        }
        if variants.is_empty() {
            return Err(Diagnostic::new(
                pos,
                "E_SYNTAX",
                format!("enum '{name}' needs at least one variant"),
            ));
        }
        Ok(EnumDecl { name, pos, variants })
    }

    fn at_close(&self, close: &str) -> bool {
        if close == "}" {
            *self.peek() == Tok::RBrace
        } else {
            self.is_word(close)
        }
    }


    /// A deliberately non-executable syntax gate for persistent actor hooks.
    /// The full nested Result/Option/ActorStateSnapshot type shape is checked
    /// exactly here; this browser compiler lacks generic suspended codegen.
    /// The body is only brace-balanced and cannot reach the Wasm emitter.
    fn parse_persistence_hook(&mut self, owner: &str) -> R<ActorPersistenceHook> {
        let pos = self.pos();
        let parse = (|| -> R<ActorPersistenceHook> {
            if !self.eat_word("susp") && !self.eat_word("suspends") {
                return Err(self.expected("'susp' persistence hook"));
            }
            self.expect_word("fnc")?;
            let (name, _) = self.ident("persistence hook name")?;
            let is_load = match name.as_str() {
                "load_state" => true,
                "save_state" => false,
                _ => return Err(self.expected("load_state or save_state")),
            };
            self.expect(Tok::LParen, "'(' after hook name")?;
            self.expect_word("ctx")?;
            self.expect(Tok::Colon, "':' after ctx")?;
            self.expect_word("PersistenceContext")?;
            if !is_load {
                self.expect(Tok::Comma, "',' after PersistenceContext")?;
                self.expect_word("snapshot")?;
                self.expect(Tok::Colon, "':' after snapshot")?;
                self.expect_word("ActorStateSnapshot")?;
                self.expect(Tok::Lt, "'<' in ActorStateSnapshot")?;
                if !self.is_word(owner) && !self.is_word("State") {
                    return Err(self.expected("the actor state type or State"));
                }
                self.advance();
                self.expect(Tok::Gt, "'>' in ActorStateSnapshot")?;
            }
            self.expect(Tok::RParen, "')' after hook parameters")?;
            self.expect(Tok::Colon, "':' before hook result")?;
            self.expect_word("Result")?;
            self.expect(Tok::Lt, "'<' after Result")?;
            if is_load {
                self.expect_word("Option")?;
                self.expect(Tok::Lt, "'<' after Option")?;
                self.expect_word("ActorStateSnapshot")?;
                self.expect(Tok::Lt, "'<' after ActorStateSnapshot")?;
                if !self.is_word(owner) && !self.is_word("State") {
                    return Err(self.expected("the actor state type or State"));
                }
                self.advance();
                self.expect(Tok::Gt, "'>' after actor state")?;
                self.expect(Tok::Gt, "'>' after Option")?;
            } else {
                self.expect_word("CheckpointReceipt")?;
            }
            self.expect(Tok::Comma, "',' before PersistenceError")?;
            self.expect_word("PersistenceError")?;
            self.expect(Tok::Gt, "'>' after Result")?;
            let body_provided = if self.eat(&Tok::Semi) {
                false
            } else if self.eat(&Tok::LBrace) {
                let mut depth: usize = 1;
                let mut count: usize = 0;
                while depth > 0 {
                    if *self.peek() == Tok::Eof || count >= 32768 {
                        return Err(self.expected("complete persistence hook body"));
                    }
                    match self.advance().tok {
                        Tok::LBrace => depth += 1,
                        Tok::RBrace => depth -= 1,
                        _ => {},
                    }
                    count += 1;
                }
                true
            } else {
                return Err(self.expected("';' or a braced persistence hook body"));
            };
            Ok(ActorPersistenceHook { name, pos, body_provided })
        })();
        parse.map_err(|e| Diagnostic::new(e.pos, "E_PERSIST_SIGNATURE",
            format!("invalid persistent actor hook signature: {}", e.message)))
    }

    /// Class or actor members up to and including `close` (`end` or `}`).
    fn parse_members(&mut self, owner: &str, actor: bool, close: &str) -> R<Members> {
        let kind = if actor { "actor" } else { "class" };
        let mut m = Members::default();
        let mut count = 0usize;
        loop {
            if self.at_close(close) {
                self.advance();
                break;
            }
            if *self.peek() == Tok::Eof {
                return Err(self.expected(&format!("'{close}' to close {kind} '{owner}'")));
            }
            count += 1;
            if count > MAX_MEMBERS {
                return Err(Diagnostic::new(
                    self.pos(),
                    "E_SOURCE_LIMIT",
                    format!("more than {MAX_MEMBERS} members in {kind} '{owner}'"),
                ));
            }
            if *self.peek() == Tok::At {
                return Err(unsupported(self.pos(), "annotations"));
            }
            let mpos = self.pos();
            let visibility = if self.eat_word("pub") {
                if self.eat(&Tok::LBracket) {
                    if !self.eat_word("pkg") || !self.eat(&Tok::RBracket) {
                        return Err(Diagnostic::new(mpos, "E_SYNTAX",
                            "class field visibility accepts only pub[pkg]"));
                    }
                    if actor { return Err(unsupported(mpos, "pub[pkg] actor members")); }
                    FieldVisibility::Package
                } else { FieldVisibility::Public }
            } else if self.eat_word("private") {
                if *self.peek() == Tok::LBracket {
                    return Err(Diagnostic::new(mpos, "E_SYNTAX",
                        "private is unqualified; use private or pub[pkg]"));
                }
                FieldVisibility::Private
            } else { FieldVisibility::Private };
            let public = visibility == FieldVisibility::Public;
            let word = self.word_at(0).map(str::to_owned);
            if visibility == FieldVisibility::Package
                && (matches!(word.as_deref(), Some("static" | "constructor" | "fnc" | "method" | "receive"))
                    || *self.peek_at(1) == Tok::LParen)
            {
                return Err(unsupported(mpos, "pub[pkg] on non-field class members"));
            }
            match word.as_deref() {
                Some("static") => {
                    if actor {
                        return Err(unsupported(self.pos(), "static functions in actors"));
                    }
                    self.advance();
                    if let Some(w @ ("async" | "structural")) = self.word_at(0) {
                        return Err(unsupported(self.pos(), &format!("'{w}' static functions")));
                    }
                    self.expect_word("fnc")?;
                    let method = self.parse_method(public, true)?;
                    m.methods.push(method);
                }
                Some("constructor") => {
                    if actor {
                        return Err(Diagnostic::new(
                            self.pos(),
                            "E_ACTOR",
                            "actors do not declare constructors; initialize actor-local state with fields",
                        ));
                    }
                    if m.ctor.is_some() {
                        return Err(Diagnostic::new(
                            self.pos(),
                            "E_DUPLICATE",
                            format!("class '{owner}' may declare at most one constructor"),
                        ));
                    }
                    self.advance();
                    self.expect(Tok::LParen, "'('")?;
                    let params = self.parse_params()?;
                    let body = self.parse_block()?;
                    m.ctor = Some(Constructor { pos: mpos, params, body });
                }
                Some("state") if actor => {
                    self.advance();
                    // Explicit actor-owned sealed state with a typed initializer.
                    // The browser profile currently admits only int/bool.
                    let mut f = self.parse_named_field(visibility, true)?;
                    f.mode = FieldMode::ActorState;
                    m.fields.push(f);
                }
                Some("final") => {
                    self.advance();
                    if matches!(self.peek(), Tok::Ident(_)) && *self.peek_at(1) == Tok::Colon {
                        let f = self.parse_named_field(visibility, actor)?;
                        m.fields.push(f);
                    } else if actor {
                        return Err(self.expected("'name: type' after 'final' in an actor"));
                    } else {
                        let referent_mutable = self.eat_word("mut");
                        let f = self.parse_type_first_field(visibility, FieldMode::Final, FieldBinding::Final, referent_mutable)?;
                        m.fields.push(f.field);
                    }
                }
                Some("mut") if !actor => {
                    self.advance();
                    let f = self.parse_type_first_field(visibility, FieldMode::Constructor, FieldBinding::Let, true)?;
                    m.fields.push(f.field);
                }
                Some(w @ ("let" | "val" | "const")) => {
                    let mode = match (w, actor) {
                        ("let", true) => FieldMode::ActorState,
                        ("let", false) => FieldMode::Constructor,
                        _ => FieldMode::Final,
                    };
                    let binding = match (w, actor) {
                        ("let", true) => FieldBinding::ActorState,
                        ("let", false) => FieldBinding::Let,
                        ("val", _) => FieldBinding::Val,
                        ("const", _) => FieldBinding::Const,
                        _ => unreachable!("exhaustive field keyword"),
                    };
                    self.advance();
                    // In 'val mut T x', val still forbids name rebinding while
                    // mut requests separately checked writes through the object.
                    let referent_mutable = self.eat_word("mut");
                    if matches!(self.peek(), Tok::Ident(_)) && *self.peek_at(1) == Tok::Colon {
                        return Err(self.expected("a field type before the field name"));
                    }
                    let f = self.parse_type_first_field(visibility, mode, binding, referent_mutable)?;
                    if f.init_was_colon {
                        return Err(Diagnostic::new(
                            f.field.init.pos,
                            "E_SYNTAX",
                            "a 'let'/'val'/'const' field initializer uses '='",
                        ));
                    }
                    m.fields.push(f.field);
                }
                Some("fnc" | "method") => {
                    self.advance();
                    let method = self.parse_method(public, false)?;
                    m.methods.push(method);
                }
                Some("susp" | "suspends") if actor => {
                    if public {
                        return Err(Diagnostic::new(mpos, "E_PERSIST_SIGNATURE",
                            "persistence hooks are actor-private lifecycle methods"));
                    }
                    let hook = self.parse_persistence_hook(owner)?;
                    if m.persistence_hooks.iter().any(|existing: &ActorPersistenceHook| existing.name == hook.name)
                        || m.methods.iter().any(|other| other.name == hook.name) {
                        return Err(Diagnostic::new(hook.pos, "E_DUPLICATE",
                            "duplicate persistence hook or conflicting actor method"));
                    }
                    m.persistence_hooks.push(hook);
                }
                Some(w @ ("async" | "suspend" | "suspends" | "structural" | "abstract" | "nlex" | "shared")) => {
                    return Err(unsupported(self.pos(), &format!("'{w}' members")));
                }
                Some("receive") if actor && *self.peek_at(1) == Tok::LParen => {
                    if public {
                        return Err(Diagnostic::new(
                            mpos,
                            "E_ACTOR",
                            format!("receive handler '{owner}.receive' is actor-local and cannot be pub"),
                        ));
                    }
                    if m.receive.is_some() {
                        return Err(Diagnostic::new(
                            self.pos(),
                            "E_DUPLICATE",
                            format!("actor '{owner}' already declares receive"),
                        ));
                    }
                    let r = self.parse_receive(owner)?;
                    m.receive = Some(r);
                }
                Some(_) if *self.peek_at(1) == Tok::LParen => {
                    let method = self.parse_method(public, false)?;
                    m.methods.push(method);
                }
                Some(_) if *self.peek_at(1) == Tok::Colon && !actor => {
                    let f = self.parse_named_field(visibility, actor)?;
                    m.fields.push(f);
                }
                Some(_) if matches!(self.peek_at(1), Tok::Ident(_)) && !actor => {
                    // Bare type-first class fields default to 'let' for every
                    // type, per accepted atto-spec class-field-binding-defaults-v1.
                    // Field binding does not grant mutable receiver authority;
                    // explicit val/final/const remain non-rebindable and
                    // separate referent 'mut' never bypasses loan checks.
                    let f = self.parse_type_first_field(
                        visibility, FieldMode::Constructor, FieldBinding::Let, false
                    )?;
                    m.fields.push(f.field);
                }
                _ => {
                    return Err(self.expected(if actor {
                        "an actor member (field, method or receive)"
                    } else {
                        "a class member (field, constructor or method)"
                    }))
                }
            }
        }
        Ok(m)
    }

    /// `name: type [= expr]` (immutable field).
    fn parse_named_field(&mut self, visibility: FieldVisibility, _actor: bool) -> R<Field> {
        let (name, pos) = self.ident("a field name")?;
        self.expect(Tok::Colon, "':'")?;
        let ty = self.parse_type()?;
        if !self.eat(&Tok::Assign) {
            return Err(unsupported(self.pos(), "fields without an initializer"));
        }
        let init = self.parse_expr()?;
        self.terminator()?;
        Ok(Field {
            name,
            pos,
            ty,
            visibility,
            mode: FieldMode::Final,
            binding: FieldBinding::Final,
            referent_mutable: false,
            init,
        })
    }

    /// `type name (":" | "=") expr`.
    fn parse_type_first_field(
        &mut self, visibility: FieldVisibility, mode: FieldMode,
        binding: FieldBinding, referent_mutable: bool,
    ) -> R<TypeFirstField> {
        let ty = self.parse_type()?;
        let (name, pos) = self.ident("a field name")?;
        let init_was_colon = if self.eat(&Tok::Colon) {
            true
        } else if self.eat(&Tok::Assign) {
            false
        } else {
            return Err(unsupported(self.pos(), "fields without an initializer"));
        };
        let init = self.parse_expr()?;
        self.terminator()?;
        Ok(TypeFirstField {
            field: Field {
                name,
                pos,
                ty,
                visibility,
                mode,
                binding,
                referent_mutable,
                init,
            },
            init_was_colon,
        })
    }

    /// Method head after any `fnc`/`method`/`static fnc` keyword.
    fn parse_method(&mut self, public: bool, is_static: bool) -> R<Method> {
        let (name, pos) = self.ident("a method name")?;
        if *self.peek() == Tok::Lt {
            return Err(unsupported(self.pos(), "generic methods"));
        }
        self.expect(Tok::LParen, "'('")?;
        if self.is_word("self") {
            return Err(unsupported(self.pos(), "explicit 'self' receivers"));
        }
        let params = self.parse_params()?;
        if *self.peek() == Tok::LParen {
            return Err(unsupported(self.pos(), "curried method parameter lists"));
        }
        let arrow_type = *self.peek() == Tok::Arrow;
        let colon_type = *self.peek() == Tok::Colon;
        let ret = self.parse_return_spec(&params)?;
        let body = self.parse_callable_body(arrow_type, colon_type, ret)?;
        Ok(Method {
            name,
            pos,
            public,
            is_static,
            params,
            ret,
            body,
        })
    }

    /// `receive ( ActorMail < T > name ) [ : void ] block`.
    fn parse_receive(&mut self, owner: &str) -> R<Receive> {
        let pos = self.pos();
        self.advance();
        self.expect(Tok::LParen, "'('")?;
        if !self.is_word("ActorMail") {
            return Err(Diagnostic::new(
                self.pos(),
                "E_TYPE",
                format!("actor mailbox handler '{owner}.receive' parameter must be ActorMail<T>"),
            ));
        }
        self.advance();
        if *self.peek() != Tok::Lt {
            return Err(Diagnostic::new(
                self.pos(),
                "E_TYPE",
                "ActorMail requires an explicit payload type, for example ActorMail<int>",
            ));
        }
        self.advance();
        let payload = self.parse_type()?;
        self.expect(Tok::Gt, "'>'")?;
        let (mail, _) = self.ident("a mail parameter name")?;
        if *self.peek() == Tok::Comma {
            return Err(Diagnostic::new(
                self.pos(),
                "E_TYPE",
                format!("actor mailbox handler '{owner}.receive' takes exactly one ActorMail<T> parameter"),
            ));
        }
        self.expect(Tok::RParen, "')'")?;
        if self.parse_return_spec(&[])? != Type::Void {
            return Err(Diagnostic::new(
                pos,
                "E_TYPE",
                format!("actor mailbox handler '{owner}.receive' must return void"),
            ));
        }
        let body = self.parse_block()?;
        Ok(Receive { pos, mail, payload, body })
    }

    /// A static typeof query is resolved before producing the typed guest AST.
    /// This browser/AOT slice permits only declared parameter bindings.
    /// Other value queries and runtime-reflective expressions fail closed.
    fn parse_return_spec(&mut self, params: &[Param]) -> R<Type> {
        if !(self.eat(&Tok::Colon) || self.eat(&Tok::Arrow)) {
            return Ok(Type::Void);
        }
        if !self.eat_word("typeof") {
            return self.parse_type();
        }
        let pos = self.pos();
        if self.eat(&Tok::Bang) {
            return Err(Diagnostic::new(pos, "E_TYPE_QUERY_UNSUPPORTED",
                "typeof! is not a type operator; use typeof name"));
        }
        let parenthesized = self.eat(&Tok::LParen);
        let (name, _) = self.ident("a binding name after typeof")?;
        if parenthesized {
            self.expect(Tok::RParen, "')' after the typeof binding")?;
        }
        if name == "fnc" {
            return Err(Diagnostic::new(pos, "E_TYPE_QUERY_UNSUPPORTED",
                "typeof fnc(...) callable types are not yet implemented in this browser backend"));
        }
        match params.iter().find(|p| p.name == name) {
            Some(p) => Ok(p.ty),
            None => Err(Diagnostic::new(pos, "E_TYPE_QUERY_UNBOUND",
                format!("typeof {name} must reference a declared parameter in this AOT profile"))),
        }
    }

    /// Parameters after `(` up to and including `)`.
    fn parse_params(&mut self) -> R<Vec<Param>> {
        let mut params: Vec<Param> = Vec::new();
        if *self.peek() != Tok::RParen {
            loop {
                if params.len() >= MAX_PARAMS {
                    return Err(Diagnostic::new(
                        self.pos(),
                        "E_SOURCE_LIMIT",
                        format!("more than {MAX_PARAMS} parameters"),
                    ));
                }
                let p = self.parse_param()?;
                if params.iter().any(|q| q.name == p.name) {
                    return Err(Diagnostic::new(
                        p.pos,
                        "E_DUPLICATE",
                        format!("duplicate parameter name '{}'", p.name),
                    ));
                }
                params.push(p);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(Tok::RParen, "')'")?;
        Ok(params)
    }

    fn parse_func(&mut self) -> R<Func> {
        if *self.peek() == Tok::At {
            return Err(unsupported(self.pos(), "annotations"));
        }
        let start = self.pos();
        self.eat_word("pub");
        let is_pure = self.eat_word("pure");
        if self.is_word("private") {
            return Err(unsupported(self.pos(), "'private' visibility"));
        }
        for m in [
            "async",
            "suspend",
            "suspends",
            "nlex",
            "abstract",
            "structural",
            "static",
            "generator",
        ] {
            if self.is_word(m) {
                return Err(unsupported(self.pos(), &format!("'{m}' callables")));
            }
        }
        if !(self.eat_word("fnc") || self.eat_word("routine")) {
            if let Some(w) = self.word_at(0) {
                if UNSUPPORTED_STMT.contains(&w) || matches!(w, "val" | "let" | "const") {
                    return Err(unsupported(self.pos(), &format!("top-level '{w}'")));
                }
            }
            return Err(Diagnostic::new(
                self.pos(),
                "E_TOPLEVEL",
                format!("expected a 'fnc' declaration, found {}", describe(self.peek())),
            ));
        }
        let is_generator = if *self.peek() == Tok::Star {
            self.advance();
            self.expect_word("gen")?;
            true
        } else {
            false
        };
        let (name, pos) = self.ident("a function name")?;
        if *self.peek() == Tok::Lt {
            return Err(unsupported(self.pos(), "generic functions"));
        }
        self.expect(Tok::LParen, "'('")?;
        let params = self.parse_params()?;
        let arrow_type = *self.peek() == Tok::Arrow;
        let colon_type = *self.peek() == Tok::Colon;
        let ret = self.parse_return_spec(&params)?;
        let declared_effects = self.parse_effect_clauses()?;
        if is_pure && is_generator {
            return Err(Diagnostic::new(pos, "E_PURE",
                "pure generator effects require verified continuation semantics"));
        }
        if is_generator && ret != Type::GeneratorInt {
            return Err(Diagnostic::new(pos, "E_TYPE",
                "a 'fnc *gen' declaration must return Generator<int> in this frontend stage"));
        }
        self.in_generator = is_generator;
        let body = self.parse_callable_body(arrow_type, colon_type, ret)?;
        self.in_generator = false;
        let _ = start;
        Ok(Func {
            name,
            pos,
            is_generator,
            is_pure,
            declared_effects,
            params,
            ret,
            body,
        })
    }

    /// Explicit exceptional-effect clauses are a *checked upper bound*
    /// for ordinary throw and raise. A completely unannotated function
    /// keeps inferred legacy behavior. The panic channel is parsed and
    /// retained, but fatal-trap analysis is not yet certified.
    fn parse_effect_clauses(&mut self) -> R<Option<DeclaredEffects>> {
        let mut declared = DeclaredEffects::default();
        let mut any = false;
        loop {
            let kind = match self.word_at(0) {
                Some("throws") => "throws",
                Some("raises") => "raises",
                Some("panics") => "panics",
                _ => return Ok(any.then_some(declared)),
            };
            if *self.peek_at(1) != Tok::LParen {
                // Keep unsupported free-form Java-style headers in the
                // existing parser error path rather than consuming body text.
                return Ok(any.then_some(declared));
            }
            let pos = self.pos();
            let seen = match kind {
                "throws" => declared.throws,
                "raises" => declared.raises,
                "panics" => declared.panics,
                _ => unreachable!(),
            };
            if seen {
                return Err(Diagnostic::new(pos, "E_DUPLICATE",
                    format!("duplicate '{kind}' effect clause")));
            }
            match kind {
                "throws" => declared.throws = true,
                "raises" => declared.raises = true,
                "panics" => declared.panics = true,
                _ => unreachable!(),
            }
            any = true;
            self.advance();
            self.advance();
            let (ty, ty_pos) = self.ident("an Error type in the effect clause")?;
            if ty != "Error" {
                return Err(Diagnostic::new(ty_pos, "E_TYPE",
                    format!("'{kind}' admits only the built-in Error in this browser slice, found '{ty}'")));
            }
            if self.eat(&Tok::Comma) {
                return Err(Diagnostic::new(self.pos(), "E_DUPLICATE",
                    format!("duplicate Error type in '{kind}' effect clause")));
            }
            self.expect(Tok::RParen, "')' to close the effect clause")?;
            // `throws(Error), raises(Error)`: a comma may separate clauses.
            if *self.peek() == Tok::Comma
                && matches!(self.word_at(1), Some("throws" | "raises" | "panics"))
                && *self.peek_at(2) == Tok::LParen
            {
                self.advance();
            }
        }
    }

    /// `try { } [catch (Error e) { }] [finally { }]`, at least one handler.
    fn parse_try(&mut self, pos: Pos) -> R<Stmt> {
        self.advance();
        let body = self.parse_block()?;
        let catch = if self.eat_word("catch") {
            self.expect(Tok::LParen, "'(' after 'catch'")?;
            let (ty, ty_pos) = self.ident("the caught Error type")?;
            if ty != "Error" {
                return Err(Diagnostic::new(ty_pos, "E_TYPE",
                    "this browser slice catches only the built-in Error"));
            }
            let (binder, _) = self.ident("a catch binding name")?;
            self.expect(Tok::RParen, "')' after the catch binding")?;
            Some((binder, self.parse_block()?))
        } else {
            None
        };
        if self.is_word("catch") {
            return Err(unsupported(self.pos(), "multiple catch clauses"));
        }
        let finally = if self.eat_word("finally") { Some(self.parse_block()?) } else { None };
        if catch.is_none() && finally.is_none() {
            return Err(Diagnostic::new(pos, "E_SYNTAX", "'try' requires a 'catch' or 'finally' clause"));
        }
        Ok(Stmt::Try { body, catch, finally, pos })
    }

    /// Shared registration factory header: \`|T first, T second|\`.
    /// These are explicit values evaluated at registration, not lexical captures.
    fn parse_cleanup_factory_params(&mut self) -> R<Vec<(String, Type, Pos)>> {
        self.expect(Tok::Pipe, "'|' to open the factory parameters")?;
        let mut params: Vec<(String, Type, Pos)> = Vec::new();
        if !self.eat(&Tok::Pipe) {
            loop {
                if params.len() >= MAX_PARAMS {
                    return Err(Diagnostic::new(self.pos(), "E_SOURCE_LIMIT",
                        "too many cleanup factory parameters"));
                }
                let ty = self.parse_type()?;
                let (name, p) = self.ident("a cleanup factory parameter")?;
                if name == "_" || params.iter().any(|(n, ..)| *n == name) {
                    return Err(Diagnostic::new(p, "E_DUPLICATE",
                        format!("duplicate or reserved factory parameter '{name}'")));
                }
                params.push((name, ty, p));
                if self.eat(&Tok::Pipe) { break; }
                self.expect(Tok::Comma, "',' or '|' after a factory parameter")?;
            }
        }
        Ok(params)
    }

    /// A deferred cleanup can be a block, a zero-argument lambda, or a
    /// factory with explicit, single-evaluation captures.
    fn parse_defer(&mut self, pos: Pos) -> R<Stmt> {
        self.advance();
        let (params, body, args) = if *self.peek() == Tok::LBrace {
            (Vec::new(), self.parse_block()?, Vec::new())
        } else if self.eat_word("_") {
            self.expect(Tok::Arrow, "'->' after 'defer _'")?;
            (Vec::new(), self.parse_block()?, Vec::new())
        } else if self.eat(&Tok::Pipe) {
            self.expect(Tok::Pipe, "empty '||' lambda after 'defer'")?;
            self.expect(Tok::Arrow, "'->' after 'defer ||'")?;
            (Vec::new(), self.parse_block()?, Vec::new())
        } else if self.eat(&Tok::LParen) {
            let params = self.parse_cleanup_factory_params()?;
            self.expect(Tok::Arrow, "'->' after the defer factory parameters")?;
            if !self.eat_word("_") {
                return Err(self.expected("'_' for the zero-argument deferred cleanup"));
            }
            self.expect(Tok::Arrow, "'->' before the deferred cleanup body")?;
            let body = self.parse_block()?;
            self.expect(Tok::RParen, "')' after the defer factory")?;
            let args = self.parse_args()?;
            (params, body, args)
        } else {
            return Err(self.expected("'{' or '_ ->' or '|| ->' or a defer factory"));
        };
        self.terminator()?;
        Ok(Stmt::Defer { params, body, args, pos })
    }

    /// Recovery handlers receive a lexical, non-escaping ErrorView and a
    /// one-shot cursor; either binder may carry its explicit special type.
    fn parse_recovery_handler(&mut self, params: &[(String, Type, Pos)])
        -> R<(String, String, Vec<Stmt>)>
    {
        self.expect(Tok::Pipe, "'|' to open the recovery handler")?;
        if self.word_at(0) == Some("ErrorView") && matches!(self.peek_at(1), Tok::Ident(_)) {
            self.advance();
        }
        let (err, err_pos) = self.ident("the recovery error handle")?;
        self.expect(Tok::Comma, "',' after the recovery error handle")?;
        if self.word_at(0) == Some("RecoveryCursor") && matches!(self.peek_at(1), Tok::Ident(_)) {
            self.advance();
        }
        let (cursor, cursor_pos) = self.ident("the recovery cursor")?;
        if err == cursor || err == "_" || cursor == "_" ||
            params.iter().any(|(n, ..)| *n == err || *n == cursor)
        {
            return Err(Diagnostic::new(if err == "_" { err_pos } else { cursor_pos },
                "E_DUPLICATE", "recovery bindings must be distinct and cannot be '_'"));
        }
        self.expect(Tok::Pipe, "'|' after the recovery cursor")?;
        self.expect(Tok::Arrow, "'->' before the recovery handler body")?;
        let body = self.parse_block()?;
        Ok((err, cursor, body))
    }

    /// Canonical \`recover |err, cursor| -> { ... };\` and compatible
    /// \`recover (|T v| -> |err, cursor| -> { ... })(value);\`.
    fn parse_recover(&mut self, pos: Pos) -> R<Stmt> {
        self.advance();
        let (params, err, cursor, body, args) = if self.eat(&Tok::LParen) {
            let params = self.parse_cleanup_factory_params()?;
            self.expect(Tok::Arrow, "'->' after the recovery factory parameters")?;
            let (err, cursor, body) = self.parse_recovery_handler(&params)?;
            self.expect(Tok::RParen, "')' to close the recovery factory")?;
            let args = self.parse_args()?;
            (params, err, cursor, body, args)
        } else {
            let (err, cursor, body) = self.parse_recovery_handler(&[])?;
            (Vec::new(), err, cursor, body, Vec::new())
        };
        self.terminator()?;
        Ok(Stmt::Recover { params, err, cursor, body, args, pos })
    }

    fn parse_param(&mut self) -> R<Param> {
        let pos = self.pos();
        if self.is_word("structural") {
            return Err(unsupported(pos, "structural parameters"));
        }
        // compatibility form `name: type [mut]`
        if matches!(self.peek(), Tok::Ident(_)) && *self.peek_at(1) == Tok::Colon {
            let (name, pos) = self.ident("a parameter name")?;
            self.advance();
            let ty = self.parse_type()?;
            let mutable = self.eat_word("mut");
            return self.finish_param(name, ty, mutable, pos);
        }
        let ty = self.parse_type()?;
        let mutable = self.eat_word("mut");
        let (name, pos) = self.ident("a parameter name")?;
        self.finish_param(name, ty, mutable, pos)
    }

    fn finish_param(&self, name: String, ty: Type, mutable: bool, pos: Pos) -> R<Param> {
        if ty == Type::Void {
            return Err(Diagnostic::new(pos, "E_TYPE", "a parameter cannot have type void"));
        }
        if *self.peek() == Tok::Assign {
            return Err(unsupported(self.pos(), "default parameter values"));
        }
        Ok(Param { name, ty, mutable, pos })
    }

    // ----------------------------------------------------------- statements

    /// C-style braces remain the default. The extra -> after : Type is an
    /// explicit body marker; a -> Type header also admits comma/end bodies.
    fn parse_callable_body(&mut self, arrow_type: bool, colon_type: bool, ret: Type) -> R<Vec<Stmt>> {
        if arrow_type {
            if *self.peek() == Tok::LBrace {
                return self.parse_block();
            }
            // Keep existing implicit-return comma/end bodies compatible.
            // A semicolon/end body is an explicit-return sequence. Try it in
            // an isolated parser snapshot: failed trials must not leak token
            // positions, symbol interning or nesting-budget state.
            let explicit_comma = self.eat(&Tok::ColonColon);
            if explicit_comma && *self.peek() == Tok::LBrace {
                return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                    "'::' requires a comma/end body, not a brace block"));
            }
            // The pinned website also uses '::' as an optional header
            // separator before explicit semicolon/return statements. Until
            // the versioned header migration (#185), preserve both spellings
            // without relaxing the checked return contract.
            let mut trial = self.clone();
            if let Ok(body) = trial.parse_explicit_end_body() {
                // A lone final expression still means a comma/end *implicit*
                // tail return. Never reinterpret it as a statement/end body:
                // doing so changes the type of existing class mtd methods.
                // The current compatibility profile admits explicit-return
                // bodies only when a top-level terminal is present. Fully
                // branch-terminal explicit bodies await the versioned grammar.
                if body.iter().any(|stmt| matches!(stmt, Stmt::Return(..) | Stmt::Throw(..))) {
                    *self = trial;
                    return Ok(body);
                }
            }
            return self.parse_erlang_body(ret);
        }
        if colon_type && self.eat(&Tok::Arrow) && *self.peek() != Tok::LBrace {
            return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                "a ': Type ->' callable body must open with '{'"));
        }
        self.parse_block()
    }

    /// Explicit statement/end bodies use ordinary semicolon terminators
    /// and do NOT infer a return from the last expression. Nested if/fi and
    /// match/end consume their own delimiters before this outer 'end'.
    /// A callable's return and exhaustiveness obligations remain checked by
    /// the normal typed frontend, not guessed by the parser.
    fn parse_explicit_end_body(&mut self) -> R<Vec<Stmt>> {
        if self.in_generator {
            return Err(unsupported(self.pos(), "explicit/end generator bodies"));
        }
        self.enter()?;
        let previous = self.erlang_body;
        self.erlang_body = false;
        let parsed = (|| -> R<Vec<Stmt>> {
            let mut body = Vec::new();
            if self.is_word("end") {
                return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                    "explicit/end callable bodies require a statement"));
            }
            while !self.is_word("end") {
                if *self.peek() == Tok::Eof {
                    return Err(self.expected("'end'"));
                }
                if *self.peek() == Tok::Comma {
                    return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                        "explicit/end callable bodies cannot contain comma-separated items"));
                }
                let start = self.i;
                body.push(self.parse_stmt()?);
                if self.i == start {
                    return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                        "explicit/end body statement did not consume source"));
                }
            }
            self.expect_word("end")?;
            Ok(body)
        })();
        self.erlang_body = previous;
        self.leave();
        parsed
    }

    /// In an Erlang-style sequence the last expression is an implicit return
    /// for a value-typed callable. All earlier items require commas; the
    /// nested statement grammar is kept independent by parse_block/until.
    fn parse_erlang_body(&mut self, ret: Type) -> R<Vec<Stmt>> {
        if self.in_generator {
            return Err(unsupported(self.pos(), "Erlang-style generator bodies"));
        }
        self.enter()?;
        let previous = self.erlang_body;
        self.erlang_body = true;
        let parsed = (|| -> R<Vec<Stmt>> {
            let mut out: Vec<Stmt> = Vec::new();
            if self.is_word("end") {
                return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                    "Erlang-style callable bodies require at least one item"));
            }
            while !self.is_word("end") {
                if *self.peek() == Tok::Eof {
                    return Err(self.expected("'end'"));
                }
                if *self.peek() == Tok::Comma {
                    return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                        "empty item in Erlang-style callable body"));
                }
                let start = self.i;
                let stmt = self.parse_stmt()?;
                if self.i == start {
                    return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                        "callable body did not consume a statement"));
                }
                // Ordinary statements consume the comma in terminator().
                // Compound statements like if/fi leave the comma for us.
                let consumed_comma = self.i > 0 && self.toks[self.i - 1].tok == Tok::Comma;
                if !consumed_comma && !self.is_word("end") {
                    self.expect(Tok::Comma, "',' between Erlang-style body items")?;
                }
                if self.is_word("end") &&
                    (consumed_comma || (self.i > 0 && self.toks[self.i - 1].tok == Tok::Comma)) {
                    return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                        "trailing comma in Erlang-style callable body"));
                }
                out.push(stmt);
            }
            self.expect_word("end")?;
            if ret != Type::Void {
                if let Some(last) = out.last_mut() {
                    if let Stmt::Expr(expr) = last {
                        let pos = expr.pos;
                        *last = Stmt::Return(Some(expr.clone()), pos);
                    }
                }
            }
            Ok(out)
        })();
        self.erlang_body = previous;
        self.leave();
        parsed
    }

    fn parse_block(&mut self) -> R<Vec<Stmt>> {
        self.expect(Tok::LBrace, "'{'")?;
        self.enter()?;
        let previous = self.erlang_body;
        self.erlang_body = false;
        let parsed = (|| -> R<Vec<Stmt>> {
            let mut out = Vec::new();
            while *self.peek() != Tok::RBrace {
                if *self.peek() == Tok::Eof {
                    return Err(self.expected("'}'"));
                }
                out.push(self.parse_stmt()?);
            }
            self.advance();
            Ok(out)
        })();
        self.erlang_body = previous;
        self.leave();
        parsed
    }

    fn parse_stmts_until(&mut self, stops: &[&str]) -> R<Vec<Stmt>> {
        self.enter()?;
        let previous = self.erlang_body;
        self.erlang_body = false;
        let parsed = (|| -> R<Vec<Stmt>> {
            let mut out = Vec::new();
            loop {
                if let Some(w) = self.word_at(0) {
                    if stops.contains(&w) {
                        break;
                    }
                }
                if *self.peek() == Tok::Eof {
                    let want: Vec<String> = stops.iter().map(|s| format!("'{s}'")).collect();
                    return Err(self.expected(&want.join(" or ")));
                }
                if *self.peek() == Tok::RBrace {
                    return Err(self.expected(&format!("'{}'", stops.last().unwrap())));
                }
                out.push(self.parse_stmt()?);
            }
            Ok(out)
        })();
        self.erlang_body = previous;
        self.leave();
        parsed
    }

    fn parse_loop_body(&mut self) -> R<Vec<Stmt>> {
        if *self.peek() == Tok::LBrace {
            self.parse_block()
        } else if self.eat_word("do") {
            let body = self.parse_stmts_until(&["done"])?;
            self.expect_word("done")?;
            Ok(body)
        } else {
            Err(self.expected("'do' or '{'"))
        }
    }

    /// Java `Parser.consumeStatementTerminator`: a `;`, a safe statement
    /// boundary (`}` `fi` `end` `else` `elseif` `done` or end of input), or an
    /// implicit newline terminator (the next token starts on a later line).
    fn terminator(&mut self) -> R<()> {
        if self.erlang_body {
            if self.eat(&Tok::Comma) || self.is_word("end") {
                return Ok(());
            }
            // An unterminated comma/end callable must report the missing
            // block delimiter, not a misleading separator error at EOF.
            if *self.peek() == Tok::Eof {
                return Err(self.expected("'end'"));
            }
            return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                "Erlang-style callable body items require ',' or 'end', not ';' or newline"));
        }
        if self.eat(&Tok::Semi) {
            return Ok(());
        }
        let boundary = matches!(self.peek(), Tok::RBrace | Tok::Eof)
            || matches!(
                self.word_at(0),
                Some("fi" | "end" | "done" | "elif" | "elseif" | "else" | "catch" | "finally")
            );
        let newline = self.i > 0 && *self.peek() != Tok::Eof && self.toks[self.i - 1].pos.line < self.pos().line;
        if boundary || newline {
            Ok(())
        } else {
            Err(self.expected("';'"))
        }
    }

    fn parse_stmt(&mut self) -> R<Stmt> {
        let pos = self.pos();
        if *self.peek() == Tok::At {
            return Err(unsupported(pos, "annotations"));
        }
        if *self.peek() == Tok::LBrace || *self.peek() == Tok::LBracket {
            return Err(unsupported(pos, "destructuring"));
        }
        // Contiguous yield* is a dedicated token, not multiplication.
        if *self.peek() == Tok::YieldStar {
            if !self.in_generator {
                return Err(Diagnostic::new(pos, "E_YIELD",
                    "'yield*' is only valid inside a 'fnc *gen' generator"));
            }
            self.advance();
            let source = self.parse_expr()?;
            self.terminator()?;
            return Ok(Stmt::YieldFrom(source, pos));
        }
        let word = self.word_at(0).map(str::to_owned);
        match word.as_deref() {
            Some("handle_state") if self.state_method && *self.peek_at(1) == Tok::LParen =>
                self.parse_state_critical_stmt(),
            Some("val" | "const" | "let") => {
                let s = self.parse_binding()?;
                self.terminator()?;
                Ok(s)
            }
            // Java Parser.looksLikePrimitiveTypeFirstImmutableBinding: exactly
            // `int|bool|string|String name = expr` is an immutable binding.
            Some("int" | "bool" | "string" | "String")
                if matches!(self.peek_at(1), Tok::Ident(_)) && *self.peek_at(2) == Tok::Assign =>
            {
                let ty = self.parse_type()?;
                let (name, _) = self.ident("a variable name")?;
                self.advance();
                let init = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Bind {
                    kind: BindKind::Const,
                    name,
                    ty: Some(ty),
                    init,
                    pos,
                })
            }
            Some(_) if self.is_type_word(0) && matches!(self.peek_at(1), Tok::Ident(_)) => Err(Diagnostic::new(
                pos,
                "E_SYNTAX",
                "a local binding starts with 'val', 'const' or 'let' (for example 'val x: int = 1;'); only int, bool and string have the immutable 'T name = e' form",
            )),
            Some("yield") => {
                if !self.in_generator {
                    return Err(Diagnostic::new(pos, "E_YIELD",
                        "'yield' is only valid inside a 'fnc *gen' generator"));
                }
                self.advance();
                let value = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Yield(value, pos))
            }
            Some("return") => {
                self.advance();
                if self.is_word("match") {
                    // Return-position match is a value. Generators cannot
                    // return values, including an exhaustive match.
                    if self.in_generator {
                        return Err(Diagnostic::new(pos, "E_RETURN",
                            "generator cannot return a match value"));
                    }
                    return self.parse_return_match(pos);
                }
                let at_end = matches!(self.peek(), Tok::Semi | Tok::RBrace | Tok::Comma)
                    || matches!(self.word_at(0), Some("fi" | "end" | "done" | "elif" | "elseif" | "else"));
                let value = if at_end { None } else { Some(self.parse_expr()?) };
                if self.in_generator && value.is_some() {
                    return Err(Diagnostic::new(pos, "E_RETURN",
                        "generators may terminate with 'return;' but cannot return a value"));
                }
                self.terminator()?;
                Ok(Stmt::Return(value, pos))
            }
            Some("throw") => {
                self.advance();
                // Only the typed Error constructor is admitted by the
                // checker. A raw string is never silently throwable.
                let error = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Throw(error, pos))
            }
            Some("raise") => {
                self.advance();
                let error = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Raise(error, pos))
            }
            Some("try") if *self.peek_at(1) == Tok::LBrace => self.parse_try(pos),
            Some("defer") => self.parse_defer(pos),
            Some("recover") => self.parse_recover(pos),
            Some("if") => self.parse_if(),
            Some("guard") => self.parse_guard(),
            Some("while") => {
                self.advance();
                let cond = self.parse_cond_head()?;
                self.eat(&Tok::Semi);
                let body = self.parse_loop_body()?;
                Ok(Stmt::While { cond, body, pos })
            }
            Some("loop") => {
                self.advance();
                let body = self.parse_loop_body()?;
                Ok(Stmt::Loop { body, pos })
            }
            Some("for") => self.parse_for(),
            Some("block") => {
                self.advance();
                Ok(Stmt::Block(self.parse_block()?))
            }
            Some("break") => {
                self.advance();
                self.terminator()?;
                Ok(Stmt::Break(pos))
            }
            Some("continue") => {
                self.advance();
                self.terminator()?;
                Ok(Stmt::Continue(pos))
            }
            Some("match") => self.parse_match(false),
            Some("do") if self.word_at(1) == Some("match") => {
                self.advance();
                self.parse_match(true)
            }
            Some("do") if matches!(self.word_at(1), Some("switch" | "select" | "nb")) => {
                Err(unsupported(pos, &format!("'do {}'", self.word_at(1).unwrap())))
            }
            // Narrow, executable Writable<string/int/bool/float> builtin.
            // Use the existing typed stdio.print lowering, not a new host
            // import or unchecked operator overload. The << token pair
            // must be contiguous to avoid interpreting '< <' as I/O.
            Some("stdio")
                if *self.peek_at(1) == Tok::Dot
                    && self.word_at(2) == Some("out")
                    && *self.peek_at(3) == Tok::Lt
                    && *self.peek_at(4) == Tok::Lt
                    && {
                        let a = self.toks[self.i + 3].pos;
                        let b = self.toks[self.i + 4].pos;
                        a.line == b.line && a.col.checked_add(1) == Some(b.col)
                    } =>
            {
                for _ in 0..5 { self.advance(); }
                let value = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Expr(Expr {
                    kind: ExprKind::Call("stdio.print".to_owned(), vec![value]),
                    pos,
                }))
            }
            // Parentheses around a qualified handle do not change its
            // identity or I/O capability. This mirrors the preflight's
            // conservative (stdio.out) path recognition, without admitting
            // arbitrary computed receivers or dynamic dispatch.
            _ if *self.peek() == Tok::LParen
                && self.word_at(1) == Some("stdio")
                && *self.peek_at(2) == Tok::Dot
                && self.word_at(3) == Some("out")
                && *self.peek_at(4) == Tok::RParen
                && *self.peek_at(5) == Tok::Lt
                && *self.peek_at(6) == Tok::Lt
                && {
                    let a = self.toks[self.i + 5].pos;
                    let b = self.toks[self.i + 6].pos;
                    a.line == b.line && a.col.checked_add(1) == Some(b.col)
                } =>
            {
                for _ in 0..7 { self.advance(); }
                let value = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Expr(Expr {
                    kind: ExprKind::Call("stdio.print".to_owned(), vec![value]),
                    pos,
                }))
            }
            // Explicit spelling is retained alongside the shorthand.
            // Other writech/readch targets must not be mistaken for stdout.
            Some("writech") if self.word_at(1) == Some("stdio")
                && *self.peek_at(2) == Tok::Dot
                && self.word_at(3) == Some("out")
                && *self.peek_at(4) == Tok::Comma =>
            {
                for _ in 0..5 { self.advance(); }
                let value = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Expr(Expr {
                    kind: ExprKind::Call("stdio.print".to_owned(), vec![value]),
                    pos,
                }))
            }
            Some("trap") => {
                // Caller-side trap also works in expression-statement position.
                let e = self.parse_expr()?;
                self.terminator()?;
                Ok(Stmt::Expr(e))
            }
            Some(w) if UNSUPPORTED_STMT.contains(&w) => Err(unsupported(pos, &format!("'{w}'"))),
            Some("fnc" | "routine") => Err(unsupported(pos, "nested functions")),
            _ => {
                let e = self.parse_expr()?;
                // Compound addition uses the existing checked binary addition.
                // Restrict it to locals: field/index targets need once-only lvalue lowering.
                if *self.peek() == Tok::PlusAssign {
                    let at = self.pos();
                    self.advance();
                    let value = self.parse_expr()?;
                    self.terminator()?;
                    return match e.kind {
                        ExprKind::Var(name) => Ok(Stmt::Assign {
                            name: name.clone(),
                            value: Expr {
                                kind: ExprKind::Binary(BinOp::Add, Box::new(Expr {
                                    kind: ExprKind::Var(name), pos,
                                }), Box::new(value)),
                                pos: at,
                            },
                            pos,
                        }),
                        _ => Err(Diagnostic::new(at, "E_ASSIGN_TARGET",
                            "compound '+=' currently requires a mutable local variable")),
                    };
                }
                if *self.peek() == Tok::Assign {
                    let at = self.pos();
                    self.advance();
                    let value_of = |p: &mut Self| -> R<Expr> {
                        let value = p.parse_expr()?;
                        if *p.peek() == Tok::Assign {
                            return Err(unsupported(p.pos(), "chained assignment"));
                        }
                        p.terminator()?;
                        Ok(value)
                    };
                    return match e.kind {
                        ExprKind::Var(name) => {
                            let value = value_of(self)?;
                            Ok(Stmt::Assign { name, value, pos })
                        }
                        ExprKind::Member(target, field) => {
                            let value = value_of(self)?;
                            Ok(Stmt::FieldAssign {
                                target: *target,
                                field,
                                value,
                                pos,
                            })
                        }
                        _ => Err(Diagnostic::new(
                            at,
                            "E_ASSIGN_TARGET",
                            "only a local variable or a 'self' field can be assigned",
                        )),
                    };
                }
                if matches!(self.peek(), Tok::PlusPlus | Tok::MinusMinus) {
                    return Err(Diagnostic::new(
                        self.pos(),
                        "E_UNSUPPORTED",
                        "'++' and '--' exist only in a for update clause",
                    ));
                }
                self.terminator()?;
                Ok(Stmt::Expr(e))
            }
        }
    }


    /// The Java/LLVM compound-keyword contract requires exactly adjacent
    /// ASCII critical-read / critical-write, not spaced subtraction tokens.
    /// The lexer intentionally keeps '-' separate for arithmetic; this
    /// contextual check preserves the original byte columns and diagnostics.
    fn parse_state_critical_mode(&mut self, read_only: bool) -> R<bool> {
        let keyword_pos = self.pos();
        self.expect_word("critical")?;
        if self.peek() != &Tok::Minus {
            if read_only {
                return Err(Diagnostic::new(keyword_pos, "E_SYNTAX",
                    "critical-read must use one contiguous compound keyword"));
            }
            return Ok(true); // bare critical is the exclusive write alias
        }
        let minus_pos = self.pos();
        if minus_pos.line != keyword_pos.line ||
            minus_pos.col != keyword_pos.col + 8 {
            return Err(Diagnostic::new(minus_pos, "E_SYNTAX",
                "critical-read / critical-write must not contain whitespace around '-'"));
        }
        self.advance();
        let suffix_pos = self.pos();
        if suffix_pos.line != minus_pos.line ||
            suffix_pos.col != minus_pos.col + 1 {
            return Err(Diagnostic::new(suffix_pos, "E_SYNTAX",
                "critical-read / critical-write must not contain whitespace around '-'"));
        }
        if self.eat_word("read") {
            return Ok(false);
        }
        if self.eat_word("write") && !read_only {
            return Ok(true);
        }
        Err(Diagnostic::new(suffix_pos, "E_SYNTAX",
            "expected a contiguous critical-read or critical-write state mode"))
    }

    /// A lexical, non-suspending state loan. Syntactic admission is deliberately
    /// narrower than arbitrary closures: mutation only, pure scalar RHS, no
    /// early return, IO, allocations, calls, loops or nested state access.
    fn parse_state_critical_stmt(&mut self) -> R<Stmt> {
        let pos = self.pos();
        if self.state_binder.is_some() {
            return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                "nested critical scopes cannot mint a second state loan"));
        }
        self.expect_word("handle_state")?;
        self.expect(Tok::LParen, "'('")?;
        let write = self.parse_state_critical_mode(false)?;
        // A read-only block cannot become StateWrite: that AST always
        // requests an exclusive write ticket from the trusted Worker host.
        // Reads are accepted only as nonescaping by-value s.field projections.
        if !write {
            return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                "critical-read is by-value s.field only; block scopes cannot request a write lease"));
        }
        self.expect(Tok::Pipe, "'|' before lease binder")?;
        let (binder, _) = self.ident("state lease binder")?;
        if binder != "s" { return Err(Diagnostic::new(pos, "E_STATE_BORROW",
            "this browser profile uses the binder s")); }
        self.expect(Tok::Pipe, "'|' after lease binder")?;
        self.expect(Tok::Arrow, "'->' after lease binder")?;
        self.state_binder = Some(binder);
        let result = self.parse_block();
        self.state_binder = None;
        let body = result?;
        for stmt in &body {
            match stmt {
                Stmt::FieldAssign { target, value, .. }
                    if write && matches!(target.kind, ExprKind::SelfRef)
                        && Self::pure_state_value(value) => {}
                _ => return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                    "critical block permits only pure state assignments (no calls, return, await or escapes)")),
            }
        }
        self.expect(Tok::RParen, "')' after critical scope")?;
        self.terminator()?;
        Ok(Stmt::StateWrite { body, pos })
    }

    fn pure_state_value(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Bool(_) => true,
            ExprKind::Var(name) => name != "s",
            ExprKind::Member(base, _) => matches!(base.kind, ExprKind::SelfRef),
            ExprKind::Unary(_, v) => Self::pure_state_value(v),
            ExprKind::Binary(_, a, b) => Self::pure_state_value(a) && Self::pure_state_value(b),
            _ => false,
        }
    }

    /// A single by-value immutable state projection, not a reference loan.
    fn parse_state_critical_read(&mut self) -> R<ExprKind> {
        if self.state_binder.is_some() {
            return Err(Diagnostic::new(self.pos(), "E_STATE_BORROW",
                "critical-read cannot nest inside an active critical state write"));
        }
        self.expect_word("handle_state")?;
        self.expect(Tok::LParen, "'('")?;
        if self.parse_state_critical_mode(true)? {
            return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                "critical-read must be immutable"));
        }
        self.expect(Tok::Pipe, "'|' before lease binder")?;
        let (binder, _) = self.ident("state lease binder")?;
        if binder != "s" { return Err(Diagnostic::new(self.pos(), "E_STATE_BORROW",
            "this browser profile uses the binder s")); }
        self.expect(Tok::Pipe, "'|' after lease binder")?;
        self.expect(Tok::Arrow, "'->' after lease binder")?;
        let (projector, pos) = self.ident("s.field state projection")?;
        if projector != "s" { return Err(Diagnostic::new(pos, "E_STATE_BORROW",
            "critical-read requires s.field")); }
        self.expect(Tok::Dot, "'.' in s.field")?;
        let (field, _) = self.ident("state field")?;
        self.expect(Tok::RParen, "')' after critical-read")?;
        Ok(ExprKind::StateRead(field))
    }

    /// grammar.ebnf `binding_decl`: `("val"|"const"|"let") (IDENT ":" type_ref | [type_ref] IDENT) "=" expression`.
    fn parse_binding(&mut self) -> R<Stmt> {
        let pos = self.pos();
        let kind = if self.eat_word("val") {
            BindKind::Val
        } else if self.eat_word("const") {
            BindKind::Const
        } else if self.eat_word("let") {
            BindKind::Let
        } else {
            return Err(self.expected("'val', 'const' or 'let'"));
        };
        // Java Parser.parseReferentMutability: `const mut` / `let mut` request a
        // mutable referent (no effect on scalar values); `val` already means
        // `const mut`, so `val mut` is a duplicate qualifier.
        if self.is_word("mut") {
            if kind == BindKind::Val {
                return Err(Diagnostic::new(
                    self.pos(),
                    "E_SYNTAX",
                    "'val' already means 'const mut'; 'val mut' is a duplicate mutability qualifier",
                ));
            }
            self.advance();
        }
        let (name, ty) = if matches!(self.peek(), Tok::Ident(_)) && *self.peek_at(1) == Tok::Colon {
            let (name, _) = self.ident("a variable name")?;
            self.advance();
            (name, Some(self.parse_type()?))
        } else if matches!(self.peek(), Tok::Ident(_))
            && (matches!(self.peek_at(1), Tok::Ident(_))
                || (matches!(self.word_at(0), Some("Option" | "Result" | "ActorRef" | "Array"))
                    && *self.peek_at(1) == Tok::Lt))
        {
            // Recognize generic type-first bindings without treating
            // 'Option' as a variable name and '<' as a comparison.
            let ty = self.parse_type()?;
            let (name, _) = self.ident("a variable name")?;
            (name, Some(ty))
        } else {
            let (name, _) = self.ident("a variable name")?;
            (name, None)
        };
        if self.state_method && name == "s" {
            return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                "a local named s would shadow the critical lease binder"));
        }
        if ty == Some(Type::Void) {
            return Err(Diagnostic::new(pos, "E_TYPE", "a variable cannot have type void"));
        }
        if *self.peek() != Tok::Assign {
            return Err(Diagnostic::new(
                self.pos(),
                "E_UNINITIALIZED",
                format!("binding '{name}' needs an initializer"),
            ));
        }
        self.advance();
        let init = self.parse_expr()?;
        Ok(Stmt::Bind { kind, name, ty, init, pos })
    }

    /// A guard is an else-free early-exit check. Its failure branch runs only
    /// when the predicate is false, and every path through that branch must
    /// leave the enclosing function. Lower to an ordinary typed 'if !cond'
    /// so the existing Rust/Wasm checker and emitter enforce bool typing,
    /// checked effects, lexical scoping, and exactly-once predicate evaluation.
    fn parse_guard(&mut self) -> R<Stmt> {
        let pos = self.pos();
        self.expect_word("guard")?;
        let predicate = self.parse_cond_head()?;
        if *self.peek() != Tok::LBrace {
            return Err(Diagnostic::new(self.pos(), "E_GUARD",
                "guard requires a braced failure branch"));
        }
        let failure = self.parse_block()?;
        if !guard_failure_exits(&failure) {
            return Err(Diagnostic::new(pos, "E_GUARD",
                "guard failure branch must exit the enclosing function on every path"));
        }
        Ok(Stmt::If {
            arms: vec![(
                Expr {
                    kind: ExprKind::Unary(UnOp::Not, Box::new(predicate)),
                    pos,
                },
                failure,
            )],
            otherwise: None,
            pos,
        })
    }

    fn parse_if(&mut self) -> R<Stmt> {
        let pos = self.pos();
        self.expect_word("if")?;
        let cond = self.parse_cond_head()?;
        let mut arms = Vec::new();
        let mut otherwise = None;
        if *self.peek() == Tok::LBrace {
            arms.push((cond, self.parse_block()?));
            loop {
                if self.eat_word("elif")
                    || self.eat_word("elseif")
                    || (self.is_word("else") && self.word_at(1) == Some("if") && {
                        self.advance();
                        self.advance();
                        true
                    })
                {
                    self.grow(1)?;
                    let c = self.parse_cond_head()?;
                    arms.push((c, self.parse_block()?));
                } else if self.eat_word("else") {
                    otherwise = Some(self.parse_block()?);
                    break;
                } else {
                    break;
                }
            }
        } else {
            self.eat(&Tok::Semi);
            if !(self.eat_word("then") || self.eat_word("do")) {
                return Err(self.expected("'then'"));
            }
            let stops = ["elif", "elseif", "else", "fi"];
            arms.push((cond, self.parse_stmts_until(&stops)?));
            loop {
                let is_elif = self.eat_word("elif")
                    || self.eat_word("elseif")
                    || (self.is_word("else") && self.word_at(1) == Some("if") && {
                        self.advance();
                        self.advance();
                        true
                    });
                if is_elif {
                    self.grow(1)?;
                    let c = self.parse_cond_head()?;
                    self.eat(&Tok::Semi);
                    if !(self.eat_word("then") || self.eat_word("do")) {
                        return Err(self.expected("'then'"));
                    }
                    arms.push((c, self.parse_stmts_until(&stops)?));
                } else if self.eat_word("else") {
                    otherwise = Some(self.parse_stmts_until(&["fi"])?);
                    break;
                } else {
                    break;
                }
            }
        }
        if !self.eat_word("fi") {
            return Err(Diagnostic::new(
                self.pos(),
                if *self.peek() == Tok::Eof { "E_EOF" } else { "E_FI" },
                format!(
                    "expected 'fi' to close the if started at {}:{}, found {}",
                    pos.line,
                    pos.col,
                    describe(self.peek())
                ),
            ));
        }
        // each elif arm nests one level deeper in the lowered if/else chain
        self.height -= arms.len() as u32 - 1;
        Ok(Stmt::If { arms, otherwise, pos })
    }

    /// Java Parser.parseMatch. Canonical `match x over on P -> { } end`
    /// (or `over { on P { } }`); legacy `match [first] x [;] P -> { } end`
    /// with `else` as the catch-all. `do match` requires `over`.
    fn parse_match(&mut self, procedural: bool) -> R<Stmt> {
        let pos = self.pos();
        self.expect_word("match")?;
        if *self.peek() == Tok::Lt {
            return Err(unsupported(self.pos(), "value match ('match<T>')"));
        }
        self.eat_word("first");
        let subject = self.parse_expr()?;
        let over = self.eat_word("over");
        if !over {
            self.eat(&Tok::Semi);
        }
        let braced = over && self.eat(&Tok::LBrace);
        if procedural && !over {
            return Err(Diagnostic::new(
                self.pos(),
                "E_SYNTAX",
                "'do match' requires 'over' before its arms",
            ));
        }
        let mut arms = Vec::new();
        loop {
            let done = if braced { *self.peek() == Tok::RBrace } else { self.is_word("end") };
            if done || *self.peek() == Tok::Eof {
                break;
            }
            self.grow(1)?;
            let apos = self.pos();
            if over && !self.eat_word("on") {
                let msg = if self.is_word("else") || self.is_word("default") {
                    "match has no default/else keyword; use 'on _ -> { ... }'"
                } else {
                    "every 'match ... over' arm must start with contextual keyword 'on'"
                };
                return Err(Diagnostic::new(self.pos(), "E_SYNTAX", msg));
            }
            let pattern = if !over && self.eat_word("else") {
                Pattern::Wild
            } else {
                self.parse_pattern()?
            };
            let guard = if self.eat_word("when") { Some(self.parse_expr()?) } else { None };
            if *self.peek() == Tok::Assign && *self.peek_at(1) == Tok::Gt {
                return Err(Diagnostic::new(
                    self.pos(),
                    "E_SYNTAX",
                    "match implementations use the slim arrow '->'; '=>' is reserved for type definitions",
                ));
            }
            if !self.eat(&Tok::Arrow) && !braced {
                return Err(Diagnostic::new(self.pos(), "E_SYNTAX", "match arms in 'over ... end' use '->'"));
            }
            let body = self.parse_block()?;
            arms.push(MatchArm {
                pattern,
                guard,
                body,
                pos: apos,
            });
        }
        if braced {
            self.expect(Tok::RBrace, "'}' to close braced match")?;
        } else if !self.eat_word("end") {
            return Err(Diagnostic::new(
                self.pos(),
                if *self.peek() == Tok::Eof { "E_EOF" } else { "E_SYNTAX" },
                "expected 'end' to close match",
            ));
        }
        self.height -= arms.len() as u32;
        if arms.is_empty() {
            return Err(Diagnostic::new(pos, "E_SYNTAX", "match requires at least one arm"));
        }
        Ok(Stmt::Match { subject, arms, pos })
    }

    /// A return-position match expression:
    /// `return match value over on P -> expr, default -> expr, end`.
    ///
    /// Lowering to statement match deliberately reuses the existing
    /// once-only subject evaluation, exhaustive pattern checker, strict return
    /// typing, unreachable-arm detection and Wasm branches. It does not
    /// pretend that arbitrary expressions are value matches.
    fn parse_return_match(&mut self, pos: Pos) -> R<Stmt> {
        self.expect_word("match")?;
        let subject = self.parse_expr()?;
        self.expect_word("over")?;
        let mut arms = Vec::new();
        while !self.is_word("end") {
            if *self.peek() == Tok::Eof {
                return Err(Diagnostic::new(self.pos(), "E_EOF", "expected 'end' to close return match"));
            }
            self.grow(1)?;
            let apos = self.pos();
            let pattern = if self.eat_word("default") {
                Pattern::Wild
            } else {
                self.expect_word("on")?;
                self.parse_pattern()?
            };
            // The guard sees a pattern binding only after that pattern
            // matches. A guarded catch-all does not prove exhaustiveness.
            // The existing match type checker enforces these properties.
            let guard = if self.eat_word("when") {
                Some(self.parse_expr()?)
            } else {
                None
            };
            self.expect(Tok::Arrow, "'->' in a return match arm")?;
            let braced = *self.peek() == Tok::LBrace;
            let body = if braced {
                let body = self.parse_block()?;
                if !guard_failure_exits(&body) {
                    return Err(Diagnostic::new(apos, "E_RETURN",
                        "braced return match arm must return or throw on every path"));
                }
                body
            } else {
                let value = self.parse_expr()?;
                vec![Stmt::Return(Some(value), apos)]
            };
            arms.push(MatchArm {
                pattern,
                guard,
                body,
                pos: apos,
            });
            // Expression arms require comma separators. Braced arms are
            // self-delimiting, including before another 'on' or 'default'.
            // A trailing comma is permitted in either form.
            if braced {
                self.eat(&Tok::Comma);
            } else if !self.eat(&Tok::Comma) && !self.is_word("end") {
                return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                    "expected ',' between return match value arms"));
            }
        }
        self.expect_word("end")?;
        self.height -= arms.len() as u32;
        if arms.is_empty() {
            return Err(Diagnostic::new(pos, "E_SYNTAX", "return match requires at least one arm"));
        }
        self.terminator()?;
        Ok(Stmt::Match { subject, arms, pos })
    }

    /// Java Parser.parsePattern, restricted to the forms this compiler lowers.
    fn parse_pattern(&mut self) -> R<Pattern> {
        let pos = self.pos();
        match self.peek().clone() {
            Tok::Int(Some(v)) => {
                self.advance();
                Ok(Pattern::Int(v as i64))
            }
            Tok::Int(None) => Err(Diagnostic::new(
                pos,
                "E_INTEGER_RANGE",
                "integer literal does not fit in a signed 64-bit int",
            )),
            Tok::Float(_) => Err(unsupported(pos, "float literal patterns")),
            Tok::Str(_) => Err(unsupported(pos, "string literal patterns")),
            // V2 rests and counted groups have a dedicated token. Reject
            // them deliberately until checked sequence AST and runtime
            // lowering exist; never reinterpret as a binding or an enum.
            Tok::Ellipsis => Err(unsupported(pos, "sequence rest/count patterns")),
            Tok::LParen => Err(unsupported(pos, "tuple patterns")),
            Tok::LBracket => Err(Diagnostic::new(
                pos,
                "E_SYNTAX",
                "list patterns are not supported; use tuples for fixed structural matching",
            )),
            Tok::Ident(w) => match w.as_str() {
                "true" | "false" => {
                    self.advance();
                    Ok(Pattern::Bool(w == "true"))
                }
                "None" => {
                    self.advance();
                    if *self.peek() == Tok::LParen {
                        return Err(Diagnostic::new(self.pos(), "E_ARITY",
                            "None is a zero-payload variant; write 'on None'"));
                    }
                    Ok(Pattern::Adt(w, None))
                }
                "Some" | "Ok" | "Err" => {
                    self.advance();
                    self.expect(Tok::LParen, "'(' after payload variant")?;
                    let (name, _) = self.ident("a payload binding name")?;
                    self.expect(Tok::RParen, "')' after payload binding")?;
                    Ok(Pattern::Adt(w, Some(name)))
                },
                "_" => {
                    self.advance();
                    Ok(Pattern::Wild)
                }
                "is" | "structural" => Err(unsupported(pos, "type patterns")),
                _ => {
                    self.advance();
                    if *self.peek() == Tok::Dot {
                        self.advance();
                        // `of` is reserved, so this check must run BEFORE
                        // ident("an enum variant") performs reserved-word
                        // validation. The v2 collection forms are not enum
                        // variants and may not create a guest artifact yet.
                        if matches!(w.as_str(), "List" | "Array" | "Tuple")
                            && self.is_word("of") && *self.peek_at(1) == Tok::LParen
                        {
                            return Err(unsupported(pos, "structural sequence patterns"));
                        }
                        let (variant, _) = self.ident("an enum variant")?;
                        if self.is_word("as") || *self.peek() == Tok::Dot {
                            return Err(unsupported(self.pos(), "variant payload patterns"));
                        }
                        return Ok(Pattern::Variant(w, variant));
                    }
                    if *self.peek() == Tok::LParen {
                        return Err(unsupported(pos, "constructor patterns"));
                    }
                    if let Tok::Ident(next) = self.peek() {
                        if next != "when" && next != "_" {
                            return Err(unsupported(pos, "typed binding patterns ('Type name')"));
                        }
                    }
                    if w.chars().next().is_some_and(|c| c.is_uppercase()) {
                        return Err(unsupported(pos, "constructor patterns"));
                    }
                    if is_reserved(&w) {
                        return Err(Diagnostic::new(pos, "E_RESERVED", format!("'{w}' is a reserved word")));
                    }
                    Ok(Pattern::Bind(w))
                }
            },
            _ => Err(Diagnostic::new(pos, "E_SYNTAX", "expected match pattern")),
        }
    }

    fn parse_for(&mut self) -> R<Stmt> {
        let pos = self.pos();
        self.expect_word("for")?;
        if matches!(self.peek(), Tok::Ident(_)) && self.word_at(1) == Some("in") {
            let (name, _) = self.ident("an iteration variable")?;
            self.expect_word("in")?;
            let source = self.parse_expr()?;
            let body = self.parse_loop_body()?;
            return Ok(Stmt::ForIn { name, source, body, pos });
        }
        let paren = self.eat(&Tok::LParen);
        if matches!(self.word_at(0), Some("const" | "let")) && self.word_at(2) == Some("of") {
            return Err(unsupported(self.pos(), "'for ... of' loops"));
        }
        let init = if *self.peek() == Tok::Semi {
            None
        } else if matches!(self.word_at(0), Some("val" | "const" | "let")) {
            Some(Box::new(self.parse_binding()?))
        } else if self.is_type_word(0) && matches!(self.peek_at(1), Tok::Ident(_)) {
            // grammar.ebnf for_init: type_ref IDENT "=" expression (immutable loop variable is useless; treat as let)
            let pos = self.pos();
            let ty = self.parse_type()?;
            let (name, _) = self.ident("a loop variable")?;
            self.expect(Tok::Assign, "'='")?;
            let init = self.parse_expr()?;
            Some(Box::new(Stmt::Bind {
                kind: BindKind::Let,
                name,
                ty: Some(ty),
                init,
                pos,
            }))
        } else {
            Some(Box::new(self.parse_simple_assign()?))
        };
        self.expect(Tok::Semi, "';'")?;
        let cond = if *self.peek() == Tok::Semi {
            None
        } else {
            Some(self.parse_cond()?)
        };
        self.expect(Tok::Semi, "';'")?;
        let update_end = if paren { Tok::RParen } else { Tok::LBrace };
        let update = if *self.peek() == update_end || (!paren && self.is_word("do")) {
            None
        } else {
            let upos = self.pos();
            let (name, _) = self.ident("a loop variable")?;
            if self.eat(&Tok::PlusPlus) {
                Some(Box::new(incr(name, upos, BinOp::Add)))
            } else if self.eat(&Tok::MinusMinus) {
                Some(Box::new(incr(name, upos, BinOp::Sub)))
            } else {
                self.expect(Tok::Assign, "'++', '--' or '='")?;
                let value = self.parse_expr()?;
                Some(Box::new(Stmt::Assign { name, value, pos: upos }))
            }
        };
        if paren {
            self.expect(Tok::RParen, "')'")?;
        }
        let body = self.parse_loop_body()?;
        Ok(Stmt::For {
            init,
            cond,
            update,
            body,
            pos,
        })
    }

    fn parse_simple_assign(&mut self) -> R<Stmt> {
        let pos = self.pos();
        let (name, _) = self.ident("a variable name")?;
        self.expect(Tok::Assign, "'='")?;
        let value = self.parse_expr()?;
        Ok(Stmt::Assign { name, value, pos })
    }

    // ---------------------------------------------------------- expressions

    fn parse_cond_head(&mut self) -> R<Expr> {
        let c = self.parse_cond()?;
        if *self.peek() == Tok::Assign {
            return Err(Diagnostic::new(
                self.pos(),
                "E_ASSIGN_CONDITION",
                "assignment is not allowed in a condition; use 'eq' to compare",
            ));
        }
        if self.is_word("as") {
            return Err(unsupported(self.pos(), "conditional 'as let' bindings"));
        }
        Ok(c)
    }

    /// `condition = condition_and { "|" condition_and } ;
    ///  condition_and = equality { "," equality } ;`
    fn parse_cond(&mut self) -> R<Expr> {
        self.cond += 1;
        let r = (|| {
            let mut links = 0;
            let mut left = self.parse_cond_and()?;
            while *self.peek() == Tok::Pipe {
                let pos = self.pos();
                self.advance();
                self.grow(1)?;
                links += 1;
                let right = self.parse_cond_and()?;
                left = Expr {
                    kind: ExprKind::Binary(BinOp::Or, Box::new(left), Box::new(right)),
                    pos,
                };
            }
            self.height -= links;
            Ok(left)
        })();
        self.cond -= 1;
        r
    }

    fn parse_cond_and(&mut self) -> R<Expr> {
        let mut links = 0;
        let mut left = self.parse_logical_or()?;
        while *self.peek() == Tok::Comma {
            let pos = self.pos();
            self.advance();
            self.grow(1)?;
            links += 1;
            let right = self.parse_logical_or()?;
            left = Expr {
                kind: ExprKind::Binary(BinOp::And, Box::new(left), Box::new(right)),
                pos,
            };
        }
        self.height -= links;
        Ok(left)
    }

    pub fn parse_expr(&mut self) -> R<Expr> {
        self.enter()?;
        let saved = self.cond;
        self.cond = 0;
        let r = self.parse_ternary();
        self.cond = saved;
        self.leave();
        r
    }

    fn parse_ternary(&mut self) -> R<Expr> {
        let mut c = self.parse_logical_or()?;
        // Functional pipeline: value |> f |> g(extra) lowers to g(f(value), extra).
        // Only ordinary named functions are admitted: no computed callees,
        // receiver calls or actor piping. This preserves argument evaluation
        // order and leaves arity/type checking to the existing call checker.
        let mut links = 0;
        while *self.peek() == Tok::PipeGt {
            let pos = self.pos();
            self.advance();
            let stage = self.parse_postfix()?;
            let (name, mut args) = match stage.kind {
                ExprKind::Var(name) => (name, Vec::new()),
                ExprKind::Call(name, args) => (name, args),
                _ => return Err(unsupported(pos, "pipeline stages other than named function calls")),
            };
            if args.len() >= MAX_PARAMS {
                return Err(Diagnostic::new(pos, "E_SOURCE_LIMIT", "pipeline exceeds the call argument limit"));
            }
            self.grow(1)?;
            links += 1;
            args.insert(0, c);
            c = Expr { kind: ExprKind::Call(name, args), pos };
        }
        self.height -= links;
        match self.peek() {
            Tok::Pipe => {
                return Err(Diagnostic::new(
                    self.pos(),
                    "E_UNSUPPORTED",
                    "'|' is a boolean OR only inside an if/while condition; use Or(a, b) elsewhere",
                ))
            }
            Tok::Question => {
                let pos = self.pos();
                self.advance();
                let a = self.parse_expr()?;
                self.expect(Tok::Colon, "':'")?;
                self.enter()?;
                let b = self.parse_ternary();
                self.leave();
                return Ok(Expr {
                    kind: ExprKind::Ternary(Box::new(c), Box::new(a), Box::new(b?)),
                    pos,
                });
            }
            _ => {}
        }
        Ok(c)
    }

    /// Short-circuit logical operators are distinct from comma/pipe condition
    /// operators, which are eagerly evaluated. The lexer deliberately keeps
    /// paired pipes as two tokens: initial || still starts a zero-arg lambda.
    /// In infix position only, a pair is logical OR.
    fn parse_logical_or(&mut self) -> R<Expr> {
        let mut left = self.parse_logical_and()?;
        let mut links = 0;
        while *self.peek() == Tok::Pipe && *self.peek_at(1) == Tok::Pipe {
            let pos = self.pos();
            self.advance();
            self.advance();
            self.grow(1)?;
            links += 1;
            let right = self.parse_logical_and()?;
            left = Expr {
                kind: ExprKind::Ternary(
                    Box::new(left),
                    Box::new(Expr { kind: ExprKind::Bool(true), pos }),
                    Box::new(right),
                ),
                pos,
            };
        }
        self.height -= links;
        Ok(left)
    }

    /// a && b lowers to a ? b : false. The normal typed ternary emitter
    /// evaluates a exactly once and b only when a is true. No eager builtin
    /// and no changed meaning for unary & (reserved ownership/borrow form).
    fn parse_logical_and(&mut self) -> R<Expr> {
        let mut left = self.parse_equality()?;
        let mut links = 0;
        while *self.peek() == Tok::Amp && *self.peek_at(1) == Tok::Amp {
            let pos = self.pos();
            self.advance();
            self.advance();
            self.grow(1)?;
            links += 1;
            let right = self.parse_equality()?;
            left = Expr {
                kind: ExprKind::Ternary(
                    Box::new(left),
                    Box::new(right),
                    Box::new(Expr { kind: ExprKind::Bool(false), pos }),
                ),
                pos,
            };
        }
        self.height -= links;
        Ok(left)
    }

    fn parse_equality(&mut self) -> R<Expr> {
        let mut links = 0;
        let mut left = self.parse_comparison()?;
        loop {
            let pos = self.pos();
            let op = match self.peek() {
                Tok::EqEq => BinOp::Eq,
                Tok::NotEq => BinOp::Ne,
                Tok::Ident(s) if s == "eq" => BinOp::Eq,
                Tok::Ident(s) if s == "neq" => BinOp::Ne,
                Tok::Bang if self.word_at(1) == Some("eq") => {
                    self.advance();
                    BinOp::Ne
                }
                Tok::Ident(s) if s == "is" => return Err(unsupported(pos, "a type test using 'is' (requires a statically proven type tag in this backend)")),
                _ => break,
            };
            self.advance();
            self.grow(1)?;
            links += 1;
            let right = self.parse_comparison()?;
            left = Expr {
                kind: ExprKind::Binary(op, Box::new(left), Box::new(right)),
                pos,
            };
        }
        self.height -= links;
        Ok(left)
    }

    fn parse_comparison(&mut self) -> R<Expr> {
        let mut links = 0;
        let mut left = self.parse_additive()?;
        loop {
            let pos = self.pos();
            let op = match self.peek() {
                Tok::Lt => BinOp::Lt,
                Tok::Le => BinOp::Le,
                Tok::Gt => BinOp::Gt,
                Tok::Ge => BinOp::Ge,
                Tok::Ident(s) if s == "as" || s == "matches" => return Err(unsupported(pos, &format!("'{s}'"))),
                _ => break,
            };
            self.advance();
            self.grow(1)?;
            links += 1;
            let right = self.parse_additive()?;
            left = Expr {
                kind: ExprKind::Binary(op, Box::new(left), Box::new(right)),
                pos,
            };
        }
        self.height -= links;
        Ok(left)
    }

    fn parse_additive(&mut self) -> R<Expr> {
        let mut links = 0;
        let mut left = self.parse_multiplicative()?;
        loop {
            let pos = self.pos();
            let op = match self.peek() {
                Tok::Plus => BinOp::Add,
                Tok::Minus => BinOp::Sub,
                _ => break,
            };
            self.advance();
            self.grow(1)?;
            links += 1;
            let right = self.parse_multiplicative()?;
            left = Expr {
                kind: ExprKind::Binary(op, Box::new(left), Box::new(right)),
                pos,
            };
        }
        self.height -= links;
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> R<Expr> {
        let mut links = 0;
        let mut left = self.parse_unary()?;
        loop {
            let pos = self.pos();
            let op = match self.peek() {
                Tok::Star => BinOp::Mul,
                Tok::Slash => BinOp::Div,
                _ => break,
            };
            self.advance();
            self.grow(1)?;
            links += 1;
            let right = self.parse_unary()?;
            left = Expr {
                kind: ExprKind::Binary(op, Box::new(left), Box::new(right)),
                pos,
            };
        }
        self.height -= links;
        Ok(left)
    }

    fn parse_unary(&mut self) -> R<Expr> {
        self.enter()?;
        let r = self.parse_unary_inner();
        self.leave();
        r
    }

    fn parse_unary_inner(&mut self) -> R<Expr> {
        let pos = self.pos();
        let op = match self.peek() {
            Tok::Minus => UnOp::Neg,
            Tok::Plus => UnOp::Plus,
            Tok::Bang => UnOp::Not,
            Tok::Amp => return Err(unsupported(pos, "borrow expressions")),
            Tok::PlusPlus | Tok::MinusMinus => {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED",
                    "'++' and '--' exist only in a for update clause",
                ))
            }
            Tok::Ident(s) if s == "await" => return Err(unsupported(pos, "'await'")),
            // Ownership is a prefix unary expression, like trap. Its operand
            // may be a name, postfix chain, or a grouped expression; the
            // canonical spelling never requires parentheses around a name.
            Tok::Ident(s) if matches!(s.as_str(), "borrow" | "copy" | "take" | "share" | "freeze" | "weak" | "pin" | "drop")
                && *self.peek_at(1) == Tok::Bang =>
            {
                let action = match s.as_str() {
                    "borrow" => OwnershipOp::Borrow,
                    "copy" => OwnershipOp::Copy,
                    "take" => OwnershipOp::Take,
                    "share" => OwnershipOp::Share,
                    "freeze" => OwnershipOp::Freeze,
                    "weak" => OwnershipOp::Weak,
                    "pin" => OwnershipOp::Pin,
                    "drop" => OwnershipOp::Drop,
                    _ => unreachable!(),
                };
                self.advance(); // name
                let first_bang = self.advance(); // !
                // 'copy!!' is a single canonical operator only when the word
                // and both bangs are adjacent. 'copy! !x' stays a shallow copy
                // of the logical negation, never a deep copy.
                let copy_word_is_adjacent = first_bang.pos.line == pos.line
                    && first_bang.pos.col == pos.col + 4;
                let second_bang_is_adjacent = *self.peek() == Tok::Bang
                    && self.pos().line == first_bang.pos.line
                    && self.pos().col == first_bang.pos.col + 1;
                let action = if action == OwnershipOp::Copy && copy_word_is_adjacent
                    && second_bang_is_adjacent {
                    self.advance();
                    OwnershipOp::DeepCopy
                } else {
                    action
                };
                let mutable = action == OwnershipOp::Borrow && self.eat_word("mut");
                if action != OwnershipOp::Borrow && self.is_word("mut") {
                    return Err(Diagnostic::new(self.pos(), "E_SYNTAX", "only borrow! permits a mut qualifier"));
                }
                let inner = self.parse_unary()?;
                return Ok(Expr { kind: ExprKind::Ownership(action, mutable, Box::new(inner)), pos });
            },
            Tok::Ident(s) if matches!(s.as_str(), "lt" | "lifetime")
                && *self.peek_at(1) == Tok::Bang =>
            {
                // Lifetime binders are type-level. Do not emit guest values.
                return Err(Diagnostic::new(pos, "E_LIFETIME_CONTEXT",
                    "lt! a / lifetime! a binds a lifetime, not an expression; lifetime generic lowering is unavailable in this browser subset"));
            }
            Tok::Ident(s) if s == "trap" => {
                self.advance();
                let inner = self.parse_unary()?;
                return Ok(Expr { kind: ExprKind::Trap(Box::new(inner)), pos });
            }
            _ => return self.parse_postfix(),
        };
        self.advance();
        let inner = self.parse_unary()?;
        Ok(Expr {
            kind: ExprKind::Unary(op, Box::new(inner)),
            pos,
        })
    }

    /// Call arguments after `(` up to and including `)`.
    fn parse_args(&mut self) -> R<Vec<Expr>> {
        self.expect(Tok::LParen, "'('")?;
        let mut args = Vec::new();
        if *self.peek() != Tok::RParen {
            loop {
                if matches!(self.peek(), Tok::Ident(_)) && *self.peek_at(1) == Tok::Colon {
                    return Err(unsupported(self.pos(), "named arguments"));
                }
                if *self.peek() == Tok::Dot {
                    return Err(unsupported(self.pos(), "spread arguments"));
                }
                args.push(self.parse_expr()?);
                if args.len() > MAX_PARAMS {
                    return Err(Diagnostic::new(self.pos(), "E_SOURCE_LIMIT", "too many call arguments"));
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(Tok::RParen, "')' to close the call")?;
        Ok(args)
    }

    fn parse_postfix(&mut self) -> R<Expr> {
        let mut chain = 0u32;
        let r = self.parse_postfix_chain(&mut chain);
        // member links nest one tree level each, like operator chain links
        self.height -= chain;
        r
    }

    // A '?' is ternary only when a top-level ':' follows its true arm.
    // Otherwise it is postfix propagation. Stop at the current expression
    // boundary and do not accidentally search into the next statement.
    fn question_opens_ternary(&self) -> bool {
        let mut depth = 0usize;
        for t in self.toks.iter().skip(self.i + 1) {
            match &t.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace if depth == 0 => return false,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::Colon if depth == 0 => return true,
                Tok::Semi | Tok::Comma | Tok::Eof if depth == 0 => return false,
                Tok::Ident(w) if depth == 0 && matches!(
                    w.as_str(), "fi" | "end" | "done" | "elif" | "elseif" | "else"
                ) => return false,
                _ => {}
            }
        }
        false
    }

    fn parse_postfix_chain(&mut self, chain: &mut u32) -> R<Expr> {
        let pos = self.pos();
        let mut e = self.parse_primary()?;
        loop {
            match self.peek() {
                Tok::LParen => {
                    let name = match &e.kind {
                        ExprKind::Var(n) => n.clone(),
                        _ => return Err(unsupported(self.pos(), "calling a computed value")),
                    };
                    let args = self.parse_args()?;
                    e = Expr {
                        kind: ExprKind::Call(name, args),
                        pos,
                    };
                    if matches!(self.peek(), Tok::LParen) {
                        return Err(unsupported(self.pos(), "calling a computed value"));
                    }
                }
                Tok::Dot => {
                    let dot = self.pos();
                    if let ExprKind::Var(base) = &e.kind {
                        if base == "stdio" {
                            if let Some(m @ ("print" | "println")) = self.word_at(1) {
                                let qualified = format!("stdio.{m}");
                                self.advance();
                                self.advance();
                                if *self.peek() != Tok::LParen {
                                    return Err(self.expected("'('"));
                                }
                                e = Expr {
                                    kind: ExprKind::Var(qualified),
                                    pos,
                                };
                                continue;
                            }
                        }
                    }
                    if matches!(&e.kind, ExprKind::Var(b) if b == "stdio") {
                        return Err(unsupported(dot, "stdio members other than print and println"));
                    }
                    self.advance();
                    let member = match self.peek().clone() {
                        Tok::Ident(m) if !is_reserved(&m) => m,
                        _ => return Err(self.expected("a member name after '.'")),
                    };
                    self.advance();
                    self.grow(1)?;
                    *chain += 1;
                    if *self.peek() == Tok::LParen {
                        let args = self.parse_args()?;
                        e = Expr {
                            kind: ExprKind::MethodCall(Box::new(e), member, args),
                            pos: dot,
                        };
                    } else {
                        e = Expr {
                            kind: ExprKind::Member(Box::new(e), member),
                            pos: dot,
                        };
                    }
                }
                Tok::LBracket => return Err(unsupported(self.pos(), "indexing")),
                Tok::Question if !self.question_opens_ternary() => {
                    let question = self.pos();
                    self.advance();
                    self.grow(1)?;
                    *chain += 1;
                    e = Expr { kind: ExprKind::Propagate(Box::new(e)), pos: question };
                }
                Tok::Question => break, // true ternary: parsed by parse_ternary

                _ => break,
            }
        }
        if let ExprKind::Var(n) = &e.kind {
            if n.contains('.') {
                return Err(self.expected("'('"));
            }
        }
        Ok(e)
    }

    /// Lambda annotations use a full type spelling before the slim arrow:
    /// `|n| : Result<int, Error> -> ...`. Unlike executable browser types,
    /// this syntax-only annotation admits generic and qualified names.
    fn parse_lambda_type(&mut self) -> R<String> {
        self.enter()?;
        let result = (|| {
            let mut name = match self.peek().clone() {
                Tok::Ident(s) if !is_reserved(&s) || s == "void" => {
                    self.advance();
                    s
                }
                _ => return Err(self.expected("a lambda return type")),
            };
            while self.eat(&Tok::Dot) {
                // Namespace/module segments may be spelled like keywords
                // (e.g. my.types.Response). After '.', the token is never
                // parsed as a control-flow keyword.
                let part = match self.peek().clone() {
                    Tok::Ident(part) => { self.advance(); part }
                    _ => return Err(self.expected("a qualified type name")),
                };
                name.push('.');
                name.push_str(&part);
            }
            if self.eat(&Tok::Lt) {
                name.push('<');
                loop {
                    name.push_str(&self.parse_lambda_type()?);
                    if !self.eat(&Tok::Comma) { break; }
                    name.push(',');
                }
                self.expect(Tok::Gt, "'>' after lambda type arguments")?;
                name.push('>');
            }
            Ok(name)
        })();
        self.leave();
        result
    }

    fn parse_lambda(&mut self) -> R<ExprKind> {
        self.expect(Tok::Pipe, "'|' to start lambda parameters")?;
        let mut params = Vec::new();
        if !self.eat(&Tok::Pipe) {
            loop {
                if params.len() >= MAX_PARAMS {
                    return Err(Diagnostic::new(self.pos(), "E_SOURCE_LIMIT", "too many lambda parameters"));
                }
                let (name, pos) = self.ident("a lambda parameter")?;
                if params.contains(&name) {
                    return Err(Diagnostic::new(pos, "E_DUPLICATE", format!("duplicate lambda parameter '{name}'")));
                }
                params.push(name);
                if self.eat(&Tok::Pipe) { break; }
                self.expect(Tok::Comma, "',' or '|' after lambda parameter")?;
            }
        }
        let mut return_type = if self.eat(&Tok::Colon) {
            Some(self.parse_lambda_type()?)
        } else { None };
        if self.eat(&Tok::FatArrow) {
            if return_type.is_some() {
                return Err(Diagnostic::new(self.pos(), "E_SYNTAX",
                    "use ':' rather than combining a return annotation with '=>'"));
            }
            return_type = Some(self.parse_lambda_type()?);
            self.expect(Tok::Arrow, "'->' after legacy '=>' return type")?;
        } else {
            self.expect(Tok::Arrow, "'->' after lambda parameters and optional return type")?;
            if return_type.is_none() && matches!(self.peek(), Tok::Ident(_)) {
                // Legacy braced form: |n| -> int { return n; }.
                // Roll back for an ordinary expression body, e.g. |n| -> n * 2.
                let checkpoint = (self.i, self.depth, self.height);
                let candidate = self.parse_lambda_type();
                match candidate {
                    Ok(candidate) if *self.peek() == Tok::LBrace => {
                        return_type = Some(candidate);
                    }
                    result => {
                        // Speculative type recognition must never change the
                        // parser state when the tokens actually start an
                        // expression. In particular, an interrupted recursive
                        // type parse can leave the nesting counters elevated.
                        (self.i, self.depth, self.height) = checkpoint;
                        if let Err(err) = result {
                            // Resource/recursion limits are security gates;
                            // never downgrade them to a different expression.
                            if err.code == "E_NESTING" || err.code == "E_SOURCE_LIMIT" {
                                return Err(err);
                            }
                        }
                    }
                }
            }
        }
        let body = if *self.peek() == Tok::LBrace {
            LambdaBody::Block(self.parse_block()?)
        } else if self.is_word("return") {
            // Unlike ordinary statements, a braceless lambda's return must
            // have a literal semicolon. A newline before the closing ')' does
            // not terminate this lambda body.
            let pos = self.pos();
            self.advance();
            let value = if *self.peek() == Tok::Semi {
                None
            } else {
                Some(self.parse_expr()?)
            };
            if !self.eat(&Tok::Semi) {
                return Err(Diagnostic::new(self.pos(), "E_SEMICOLON",
                    "a braceless lambda return requires ';' before its closing delimiter"));
            }
            LambdaBody::Statement(Box::new(Stmt::Return(value, pos)))
        } else {
            LambdaBody::Expression(Box::new(self.parse_expr()?))
        };
        Ok(ExprKind::Lambda { params, return_type, body })
    }

    fn parse_array_literal(&mut self) -> R<ExprKind> {
        self.expect(Tok::LBracket, "'['")?;
        let mut items = Vec::new();
        if !self.eat(&Tok::RBracket) {
            loop {
                if items.len() >= 1024 {
                    return Err(Diagnostic::new(self.pos(), "E_SOURCE_LIMIT", "array literal exceeds 1024 elements"));
                }
                items.push(self.parse_expr()?);
                if !self.eat(&Tok::Comma) { break; }
                if *self.peek() == Tok::RBracket { break; }
            }
            self.expect(Tok::RBracket, "']' after array items")?;
        }
        Ok(ExprKind::Array(items))
    }

    fn parse_primary(&mut self) -> R<Expr> {
        let pos = self.pos();
        let t = self.peek().clone();
        let kind = match t {
            Tok::Int(v) => {
                self.advance();
                ExprKind::Int(v)
            }
            Tok::Str(s) => {
                self.advance();
                ExprKind::Str(s)
            }
            Tok::Float(bits) => {
                self.advance();
                ExprKind::Float(bits)
            }
            Tok::LParen => {
                self.advance();
                let inner = if self.cond > 0 { self.parse_cond()? } else { self.parse_expr()? };
                if *self.peek() == Tok::Comma {
                    return Err(unsupported(self.pos(), "tuples"));
                }
                self.expect(Tok::RParen, "')'")?;
                return Ok(Expr { kind: inner.kind, pos });
            }
            Tok::Ident(s) => match s.as_str() {
                "borrow_mut" if *self.peek_at(1) == Tok::Bang => {
                    return Err(Diagnostic::new(pos, "E_SYNTAX", "use 'borrow! mut owner', not 'borrow_mut! owner'"));
                }
                "true" => {
                    self.advance();
                    ExprKind::Bool(true)
                }
                "false" => {
                    self.advance();
                    ExprKind::Bool(false)
                }
                "null" => return Err(Diagnostic::new(pos, "E_NULL", "AttoLang has no null value; use Option<T>")),
                "self" => {
                    if self.state_method {
                        return Err(Diagnostic::new(pos, "E_STATE_ACCESS",
                            "state fields are sealed; use a critical state lease"));
                    }
                    self.advance();
                    ExprKind::SelfRef
                }
                "handle_state" if self.state_method => self.parse_state_critical_read()?,
                "new" => {
                    self.advance();
                    let (class, _) = self.ident("a class name after 'new'")?;
                    if *self.peek() == Tok::Lt {
                        return Err(unsupported(self.pos(), "generic class instantiation"));
                    }
                    if *self.peek() != Tok::LParen {
                        return Err(self.expected("'(' after the class name"));
                    }
                    let args = self.parse_args()?;
                    ExprKind::New(class, args)
                }
                "spawn" => {
                    self.advance();
                    let (actor, _) = self.ident("an actor name after 'spawn'")?;
                    self.expect(Tok::LParen, "'(' after the actor name")?;
                    if *self.peek() != Tok::RParen {
                        return Err(Diagnostic::new(
                            self.pos(),
                            "E_ACTOR",
                            format!(
                                "actor '{actor}' does not accept constructor/startup arguments; initialize actor-local state with fields"
                            ),
                        ));
                    }
                    self.advance();
                    ExprKind::Spawn(actor)
                }
                "await" | "nb" | "super" | "match" | "select" | "readch" | "writech" | "obj" | "arr" | "typeof" => {
                    return Err(unsupported(pos, &format!("'{s}' expressions")))
                }
                w if is_reserved(w) => {
                    return Err(Diagnostic::new(
                        pos,
                        "E_SYNTAX",
                        format!("expected an expression, found keyword '{w}'"),
                    ))
                }
                _ if self.state_binder.as_deref() == Some(s.as_str()) => {
                    if *self.peek_at(1) != Tok::Dot {
                        return Err(Diagnostic::new(pos, "E_ESCAPE",
                            "state borrow cannot escape or be passed by value"));
                    }
                    self.advance();
                    ExprKind::SelfRef
                }
                _ => {
                    self.advance();
                    if *self.peek() == Tok::Lt && self.looks_generic() {
                        return Err(unsupported(self.pos(), "generic calls"));
                    }
                    ExprKind::Var(s)
                }
            },
            Tok::Pipe => self.parse_lambda()?,
            Tok::LBracket => self.parse_array_literal()?,
            Tok::LBrace => return Err(unsupported(pos, "record literals")),
            _ => return Err(self.expected("an expression")),
        };
        Ok(Expr { kind, pos })
    }

    /// `f<int>(..)` heuristic: `<` Type `>` `(`.
    fn looks_generic(&self) -> bool {
        matches!(self.peek_at(1), Tok::Ident(_)) && *self.peek_at(2) == Tok::Gt && *self.peek_at(3) == Tok::LParen
    }
}

fn incr(name: String, pos: Pos, op: BinOp) -> Stmt {
    let var = Expr {
        kind: ExprKind::Var(name.clone()),
        pos,
    };
    let one = Expr {
        kind: ExprKind::Int(Some(1)),
        pos,
    };
    Stmt::Assign {
        name,
        value: Expr {
            kind: ExprKind::Binary(op, Box::new(var), Box::new(one)),
            pos,
        },
        pos,
    }
}

fn describe(t: &Tok) -> String {
    match t {
        Tok::Ident(s) => format!("'{s}'"),
        Tok::Int(_) => "an integer".into(),
        Tok::Str(_) => "a string".into(),
        Tok::Eof => "end of input".into(),
        other => {
            let s = match other {
                Tok::LParen => "(",
                Tok::RParen => ")",
                Tok::LBrace => "{",
                Tok::RBrace => "}",
                Tok::LBracket => "[",
                Tok::RBracket => "]",
                Tok::Semi => ";",
                Tok::Comma => ",",
                Tok::Colon => ":",
                Tok::ColonColon => "::",
                Tok::Arrow => "->",
                Tok::FatArrow => "=>",
                Tok::Dot => ".",
                Tok::Assign => "=",
                Tok::EqEq => "==",
                Tok::NotEq => "!=",
                Tok::Lt => "<",
                Tok::Le => "<=",
                Tok::Gt => ">",
                Tok::Ge => ">=",
                Tok::Plus => "+",
                Tok::PlusPlus => "++",
                Tok::PlusAssign => "+=",
                Tok::Minus => "-",
                Tok::MinusMinus => "--",
                Tok::Star => "*",
                Tok::YieldStar => "yield*",
                Tok::Slash => "/",
                Tok::Bang => "!",
                Tok::Question => "?",
                Tok::Pipe => "|",
                Tok::PipeGt => "|>",
                Tok::Amp => "&",
                Tok::At => "@",
                _ => "?",
            };
            format!("'{s}'")
        }
    }
}
