//! Bounded parse-only grammar for proposed actor declarations and mtd receivers.
//! This does not lower, link, typecheck method bodies, or emit actor Wasm.
use crate::ast::{ActorDecl, ClassDecl};
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};
use crate::parser::{is_reserved, Parser, MAX_FUNCS, MAX_PARAMS};
type R<T> = Result<T, Diagnostic>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverParam {
    pub name: String,
    pub type_name: String,
    pub pos: Pos,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverHeader {
    pub owner: String,
    pub name: String,
    pub arity: usize,
    pub params: Vec<ReceiverParam>,
    pub return_type: String,
    pub mutable: bool,
    pub public: bool,
    pub pos: Pos,
}
/// Source token offsets for an out-of-line receiver, retained so executable
/// class mtd declarations can be lowered by the production method parser.
#[derive(Clone, Debug)]
pub struct ReceiverSite {
    pub declaration_start: usize,
    pub method_start: usize,
    pub end: usize,
}

/// An out-of-line constructor's source tokens, deliberately preserving the
/// original argument/body spans for checked existing-class lowering.
#[derive(Clone, Debug)]
pub struct ConstructorSite {
    pub owner: String,
    pub pos: Pos,
    pub public: bool,
    pub declaration_start: usize,
    pub params_start: usize,
    pub body_start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, Default)]
pub struct TargetHeaders {
    pub namespace: Option<String>,
    /// Imported module aliases. Imports are not resolved or linked here.
    pub imports: Vec<String>,
    pub actors: Vec<String>,
    /// Non-instantiating class forward declarations.
    pub class_forwards: Vec<String>,
    /// Token ranges for class forward declarations, omitted after linkage.
    pub class_forward_sites: Vec<(usize, usize)>,
    /// Parsed but unsupported protected per-instance class state attachments.
    pub state_owners: Vec<String>,
    /// Parsed but deliberately unlinked struct forwards.
    pub struct_forwards: Vec<String>,
    /// New-style constructor sites; lowered only to checked local classes.
    pub constructors: Vec<ConstructorSite>,
    /// Class owners found in concrete class definitions.
    pub classes: Vec<String>,
    /// Parsed class definitions; mtd linking/typing remains unsupported.
    pub class_definitions: Vec<ClassDecl>,
    /// Token offset of each class's closing 'end', in class_definitions order.
    pub class_ends: Vec<usize>,
    /// Receiver declaration and body token offsets, in receivers order.
    pub receiver_sites: Vec<ReceiverSite>,
    /// Real concrete actor syntax trees parsed by the production parser.
    /// Bodies are parsed but NOT typechecked for the new out-of-line profile.
    pub definitions: Vec<ActorDecl>,
    pub receivers: Vec<ReceiverHeader>,
}
struct Cursor<'a> { toks: &'a [Token], i: usize }
impl Cursor<'_> {
    fn tok(&self) -> &Tok { &self.toks[self.i.min(self.toks.len()-1)].tok }
    fn pos(&self) -> Pos { self.toks[self.i.min(self.toks.len()-1)].pos }
    fn word(&self) -> Option<&str> {
        match self.tok() { Tok::Ident(s) => Some(s), _ => None }
    }
    fn next(&mut self) { if self.i + 1 < self.toks.len() { self.i += 1; } }
    fn take(&mut self, t: &Tok) -> bool {
        if self.tok() == t { self.next(); true } else { false }
    }
    fn take_word(&mut self, w: &str) -> bool {
        if self.word() == Some(w) { self.next(); true } else { false }
    }
    fn err(&self, code: &'static str, message: impl Into<String>) -> Diagnostic {
        Diagnostic::new(self.pos(), code, message)
    }
    fn expect(&mut self, t: &Tok, message: &str) -> R<()> {
        if self.take(t) { Ok(()) } else { Err(self.err("E_SYNTAX", message)) }
    }
    fn expect_word(&mut self, w: &str) -> R<()> {
        if self.take_word(w) { Ok(()) }
        else { Err(self.err("E_SYNTAX", format!("expected '{w}'"))) }
    }
    fn ident(&mut self) -> R<String> {
        match self.tok().clone() {
            Tok::Ident(s) if !is_reserved(&s)
                && !matches!(s.as_str(), "declare" | "mtd" | "use" | "pub") => {
                self.next(); Ok(s)
            }
            _ => Err(self.err("E_SYNTAX", "expected an identifier")),
        }
    }
    /// Bounded type-only lookahead for '<-' before a named callable.
    /// No expression operators are accepted in this declaration position.
    fn return_first_header(&self) -> bool {
        if !matches!(self.tok(), Tok::Ident(_)) { return false; }
        if self.toks.get(self.i + 1).is_some_and(|t| t.tok == Tok::LeftArrow) {
            return true;
        }
        if !self.toks.get(self.i + 1).is_some_and(|t| t.tok == Tok::Lt) {
            return false;
        }
        let mut depth = 0usize;
        // Even malicious generic nesting cannot scan an unbounded source.
        for off in 1..=128 {
            let Some(token) = self.toks.get(self.i + off) else { return false };
            match &token.tok {
                Tok::Lt => depth += 1,
                Tok::Gt => {
                    if depth == 0 { return false; }
                    depth -= 1;
                    if depth == 0 {
                        return self.toks.get(self.i + off + 1)
                            .is_some_and(|t| t.tok == Tok::LeftArrow);
                    }
                }
                Tok::Ident(_) | Tok::Comma | Tok::Dot => {}
                _ => return false,
            }
        }
        false
    }
    fn type_name(&mut self) -> R<String> {
        self.type_name_depth(0)
    }
    /// Parse a syntactic type name without accepting arbitrary run-time
    /// expressions as type args. The production compiler still validates
    /// supported ADT instantiations and enforces all ownership rules.
    fn type_name_depth(&mut self, depth: usize) -> R<String> {
        if depth >= 16 {
            return Err(self.err("E_SOURCE_LIMIT", "nested generic return type exceeds 16 levels"));
        }
        let name = match self.tok().clone() {
            Tok::Ident(s) => { self.next(); s }
            _ => return Err(self.err("E_SYNTAX", "expected a type name")),
        };
        if !self.take(&Tok::Lt) { return Ok(name); }
        let arity = match name.as_str() {
            "Option" | "Generator" | "ActorRef" => 1,
            "Result" => 2,
            _ => return Err(self.err("E_UNSUPPORTED_TYPE",
                "target generic type must be Option, Result, Generator or ActorRef")),
        };
        let mut args = Vec::with_capacity(arity);
        for i in 0..arity {
            if i > 0 { self.expect(&Tok::Comma, "expected ',' in generic type")?; }
            args.push(self.type_name_depth(depth + 1)?);
        }
        self.expect(&Tok::Gt, "expected '>' closing generic type")?;
        if name == "ActorRef" && args[0].contains('<') {
            return Err(self.err("E_UNSUPPORTED_TYPE",
                "ActorRef parameter must be one nominal actor name"));
        }
        Ok(format!("{}<{}>", name, args.join(",")))
    }
    fn params(&mut self) -> R<Vec<ReceiverParam>> {
        self.expect(&Tok::LParen, "expected '(' before parameters")?;
        let mut params = Vec::new();
        if self.take(&Tok::RParen) { return Ok(params); }
        loop {
            if params.len() >= MAX_PARAMS {
                return Err(self.err("E_SOURCE_LIMIT", "too many parameters"));
            }
            let pos = self.pos();
            let type_name = self.type_name()?;
            let name = self.ident()?;
            if params.iter().any(|p: &ReceiverParam| p.name == name) {
                return Err(Diagnostic::new(pos, "E_DUPLICATE",
                    format!("duplicate method parameter '{name}'")));
            }
            params.push(ReceiverParam { name, type_name, pos });
            if !self.take(&Tok::Comma) {
                self.expect(&Tok::RParen, "expected ')' after parameters")?;
                return Ok(params);
            }
        }
    }
    /// For explicit statement/end bodies, use a bounded delimiter scan.
    /// This frontend is syntax-only; production parsing verifies statements
    /// before any guest artifact is emitted.
    fn explicit_end_body(&mut self) -> R<()> {
        let (mut braces, mut conditional, mut nested_end) = (0u32, 0u32, 0u32);
        loop {
            match self.tok() {
                Tok::Eof => return Err(self.err("E_EOF", "unclosed statement/end body")),
                Tok::Ident(s) if s == "end" && braces == 0 && conditional == 0 => {
                    if nested_end == 0 {
                        self.next();
                        return Ok(());
                    }
                    nested_end -= 1;
                }
                Tok::Ident(s) if s == "begin" && braces == 0 => nested_end += 1,
                Tok::Ident(s) if s == "if" && braces == 0 => conditional += 1,
                Tok::Ident(s) if s == "fi" && braces == 0 => {
                    if conditional == 0 { return Err(self.err("E_SYNTAX", "unmatched fi")); }
                    conditional -= 1;
                }
                Tok::LBrace => {
                    braces += 1;
                    if braces > 128 { return Err(self.err("E_NESTING", "body nesting limit")); }
                }
                Tok::RBrace => {
                    if braces == 0 { return Err(self.err("E_SYNTAX", "unmatched '}'")); }
                    braces -= 1;
                }
                _ => {}
            }
            self.next();
        }
    }

    fn body(&mut self, arrow_type: bool, colon_type: bool, return_first: bool) -> R<()> {
        // Target-only receiver bodies are delimiter scans, not executable Wasm.
        if colon_type && self.take(&Tok::Arrow) && *self.tok() != Tok::LBrace {
            return Err(self.err("E_SYNTAX", "': Type ->' requires a braced body"));
        }
        if self.take_word("begin") { return self.explicit_end_body(); }
        if self.take(&Tok::LBrace) {
            let mut depth = 1u32;
            while depth != 0 {
                match self.tok() {
                    Tok::Eof => return Err(self.err("E_EOF", "unclosed method body")),
                    Tok::LBrace => {
                        depth += 1;
                        if depth > 128 { return Err(self.err("E_NESTING", "body nesting limit")); }
                    }
                    Tok::RBrace => depth -= 1,
                    _ => {}
                }
                self.next();
            }
            return Ok(());
        }
        if return_first { return self.explicit_end_body(); }
        if !arrow_type {
            return Err(self.err("E_SYNTAX", "expected '{' or begin/end for a method body"));
        }
        if self.take(&Tok::ColonColon) && *self.tok() == Tok::LBrace {
            return Err(self.err("E_SYNTAX", "'::' requires a comma/end body, not '{'"));
        }
        if *self.tok() == Tok::Arrow {
            return Err(self.err("E_SYNTAX", "a second '->' is not a body delimiter"));
        }
        let (mut braces, mut conditionals, mut items) = (0u32, 0u32, 0usize);
        loop {
            match self.tok() {
                Tok::Eof => return Err(self.err("E_EOF", "unclosed Erlang-style method body")),
                Tok::Ident(s) if s == "end" && braces == 0 => {
                    if conditionals != 0 { return Err(self.err("E_SYNTAX", "unclosed if/fi in Erlang-style body")); }
                    if items == 0 { return Err(self.err("E_SYNTAX", "empty Erlang-style method body")); }
                    self.next();
                    return Ok(());
                }
                Tok::Ident(s) if braces == 0 && matches!(s.as_str(), "match" | "select" | "switch") =>
                    return Err(self.err("E_UNSUPPORTED",
                        "nested end-delimited match/select/switch requires a recursive method parser")),
                Tok::Ident(s) if braces == 0 && s == "if" => conditionals += 1,
                Tok::Ident(s) if braces == 0 && s == "fi" => {
                    if conditionals == 0 { return Err(self.err("E_SYNTAX", "unmatched fi")); }
                    conditionals -= 1;
                }
                Tok::LBrace => {
                    braces += 1;
                    if braces > 128 { return Err(self.err("E_NESTING", "body nesting limit")); }
                }
                Tok::RBrace => {
                    if braces == 0 { return Err(self.err("E_SYNTAX", "unmatched '}'")); }
                    braces -= 1;
                }
                Tok::Semi if braces == 0 && conditionals == 0 =>
                    return Err(self.err("E_SYNTAX", "Erlang-style items require commas, not semicolons")),
                Tok::Comma if braces == 0 && conditionals == 0 => {
                    if matches!(self.toks.get(self.i + 1).map(|x| &x.tok), Some(Tok::Ident(s)) if s == "end") {
                        return Err(self.err("E_SYNTAX", "trailing comma in Erlang-style body"));
                    }
                }
                _ => {}
            }
            items += 1;
            self.next();
        }
    }
    fn receiver(&mut self, pos: Pos, public: bool) -> R<(ReceiverHeader, usize, usize, usize)> {
        self.expect(&Tok::LParen, "expected '(' before receiver")?;
        // Both the explicit typed spelling and the nominal receiver spelling
        // are accepted: (mut self: Foo), (self: Foo), (Foo self),
        // (Foo) and (Foo _). All variants have one nominal owner.
        let (owner, mutable) = if self.take_word("mut") {
            self.expect_word("self")?;
            self.expect(&Tok::Colon, "expected ':' after self")?;
            (self.ident()?, true)
        } else if self.take_word("self") {
            self.expect(&Tok::Colon, "expected ':' after self")?;
            (self.ident()?, false)
        } else {
            let owner = self.ident()?;
            // Explicit name or compiler-owned implicit receiver.
            if !self.take_word("self") {
                self.take_word("_");
            }
            (owner, false)
        };
        self.expect(&Tok::RParen, "expected ')' after receiver")?;
        let method_start = self.i;
        let return_first = self.return_first_header();
        let prefix_type = if return_first {
            let t = self.type_name()?;
            self.expect(&Tok::LeftArrow, "expected '<-' after return type")?;
            Some(t)
        } else { None };
        let name = self.ident()?;
        let params = self.params()?;
        let arity = params.len();
        let arrow_type = !return_first && *self.tok() == Tok::Arrow;
        let colon_type = !return_first && *self.tok() == Tok::Colon;
        let return_type = if let Some(t) = prefix_type {
            if matches!(self.tok(), Tok::Colon | Tok::Arrow) {
                return Err(self.err("E_RETURN_ANNOTATION", "return type declared twice"));
            }
            t
        } else {
            if !(self.take(&Tok::Colon) || self.take(&Tok::Arrow)) {
                return Err(self.err("E_RETURN_ANNOTATION",
                    "out-of-line method requires -> T, -> void, -> infer or T <- name"));
            }
            self.type_name()?
        };
        let start = self.i;
        self.body(arrow_type, colon_type, return_first)?;
        let end = self.i;
        Ok((ReceiverHeader { owner, name, arity, params, return_type, mutable, public, pos }, start, end, method_start))
    }

    /// Use production parsing for one declaration; unlike a token-only scan,
    /// it consumes inner Erlang-style method 'end' without closing the class.
    fn definition(&mut self, start: usize) -> R<ActorDecl> {
        let (decl, end) = Parser::parse_target_actor_at(self.toks, start)?;
        self.i = end;
        Ok(decl)
    }
    fn constructor_site(&mut self, pos: Pos, public: bool, declaration_start: usize) -> R<ConstructorSite> {
        self.expect(&Tok::LParen, "expected '(' before constructor owner")?;
        let owner = self.ident()?;
        self.expect(&Tok::RParen, "expected ')' after constructor owner")?;
        let params_start = self.i;
        self.params()?;
        self.expect(&Tok::Colon, "out-of-line constructor requires ': self'")?;
        self.expect_word("self")?;
        let body_start = self.i;
        self.body(false, true, false)?;
        Ok(ConstructorSite { owner, pos, public, declaration_start,
            params_start, body_start, end: self.i })
    }

    /// Guarded state syntax is recognized only, never lowered to unprotected fields.
    fn state_attachment(&mut self) -> R<String> {
        self.expect_word("on")?;
        self.expect_word("class")?;
        let owner = self.ident()?;
        self.expect_word("as")?;
        self.expect(&Tok::LBrace, "expected '{' for guarded class state")?;
        let mut depth = 1usize;
        while depth != 0 {
            match self.tok() {
                Tok::Eof => return Err(self.err("E_EOF", "unclosed protected class state")),
                Tok::LBrace => {
                    depth += 1;
                    if depth > 128 { return Err(self.err("E_NESTING", "state nesting limit")); }
                }
                Tok::RBrace => depth -= 1,
                _ => {}
            }
            self.next();
        }
        Ok(owner)
    }

    fn class_definition(&mut self, start: usize) -> R<ClassDecl> {
        let (decl, end) = Parser::parse_target_class_at(self.toks, start)?;
        self.i = end;
        Ok(decl)
    }
    fn function(&mut self) -> R<(usize, usize)> {
        let return_first = self.return_first_header();
        if return_first {
            self.type_name()?;
            self.expect(&Tok::LeftArrow, "expected '<-' after return type")?;
        }
        self.ident()?;
        self.params()?;
        let arrow_type = !return_first && *self.tok() == Tok::Arrow;
        let colon_type = !return_first && *self.tok() == Tok::Colon;
        if !return_first {
            if !(self.take(&Tok::Colon) || self.take(&Tok::Arrow)) {
                return Err(self.err("E_RETURN_ANNOTATION",
                    "named function requires -> T, -> void, -> infer or T <- name"));
            }
            self.type_name()?;
        } else if matches!(self.tok(), Tok::Colon | Tok::Arrow) {
            return Err(self.err("E_RETURN_ANNOTATION", "return type declared twice"));
        }
        let start = self.i;
        self.body(arrow_type, colon_type, return_first)?;
        Ok((start, self.i))
    }
}

/// Validate a target-only source unit: optional flat namespace header,
/// module imports, forward-declared actors, nominal or typed receivers and functions.
/// Body braces are balanced only: there is no semantic/state access proof.
pub fn parse_target_declarations(toks: &[Token]) -> R<TargetHeaders> {
    if toks.is_empty() {
        return Err(Diagnostic::new(Pos::default(), "E_EOF", "empty token stream"));
    }
    let mut c = Cursor { toks, i: 0 };
    let mut out = TargetHeaders::default();
    let mut spans: Vec<(usize, usize, usize)> = Vec::new();
    let mut function_spans: Vec<(usize, usize)> = Vec::new();
    let mut decls = 0;
    while *c.tok() != Tok::Eof {
        if decls >= MAX_FUNCS {
            return Err(c.err("E_SOURCE_LIMIT", "too many target declarations"));
        }
        let pos = c.pos();
        if c.take_word("use") {
            if decls != 0 { return Err(c.err("E_SYNTAX", "namespace header must come first")); }
            c.expect_word("namespace")?;
            out.namespace = Some(c.ident()?);
            c.expect(&Tok::Semi, "expected ';' after namespace")?;
        } else if c.take_word("import") {
            if !out.actors.is_empty() || !out.classes.is_empty() || !out.class_forwards.is_empty() ||
               !out.struct_forwards.is_empty() || !out.state_owners.is_empty() ||
               !out.constructors.is_empty() || !out.receivers.is_empty() {
                return Err(c.err("E_SYNTAX", "module imports must precede actor declarations"));
            }
            c.expect_word("module")?;
            let alias = c.ident()?;
            if out.imports.contains(&alias) {
                return Err(c.err("E_DUPLICATE", format!("duplicate module import '{alias}'")));
            }
            c.expect_word("from")?;
            match c.tok() {
                Tok::Str(_) => c.next(),
                _ => return Err(c.err("E_SYNTAX", "expected a quoted module import path")),
            }
            c.expect(&Tok::Semi, "expected ';' after module import")?;
            out.imports.push(alias);
        } else if c.take_word("define") {
            if c.take_word("state") {
                let owner = c.state_attachment()?;
                if out.state_owners.contains(&owner) {
                    return Err(Diagnostic::new(pos, "E_DUPLICATE",
                        format!("duplicate protected state attachment for class '{owner}'")));
                }
                out.state_owners.push(owner);
            } else if c.word() == Some("actor") {
                let actor = c.definition(c.i - 1)?;
                if out.definitions.iter().any(|other| other.name == actor.name) ||
                    out.classes.iter().any(|n| n == &actor.name) ||
                    out.class_forwards.contains(&actor.name) ||
                    out.struct_forwards.contains(&actor.name) {
                    return Err(Diagnostic::new(actor.pos, "E_DUPLICATE",
                        format!("duplicate concrete actor definition '{}'", actor.name)));
                }
                out.definitions.push(actor);
            } else if c.word() == Some("class") {
                let class = c.class_definition(c.i - 1)?;
                if out.classes.contains(&class.name) ||
                    out.actors.contains(&class.name) ||
                    out.definitions.iter().any(|a| a.name == class.name) ||
                    out.struct_forwards.contains(&class.name) {
                    return Err(Diagnostic::new(class.pos, "E_DUPLICATE",
                        format!("duplicate class or actor owner '{}'", class.name)));
                }
                out.classes.push(class.name.clone());
                out.class_ends.push(c.i - 1);
                out.class_definitions.push(class);
            } else {
                return Err(c.err("E_SYNTAX", "expected 'class' or 'actor' after define"));
            }
        } else if c.take_word("declare") {
            let start = c.i - 1;
            let kind = c.word().map(str::to_owned).unwrap_or_default();
            if !matches!(kind.as_str(), "actor" | "class" | "struct") {
                return Err(c.err("E_SYNTAX", "expected actor, class or struct after declare"));
            }
            c.next();
            let name = c.ident()?;
            if out.actors.contains(&name) || out.class_forwards.contains(&name) ||
                out.struct_forwards.contains(&name) ||
                (kind != "class" && out.classes.contains(&name)) ||
                out.definitions.iter().any(|a| a.name == name) {
                return Err(c.err("E_DUPLICATE", format!("duplicate nominal forward '{name}'")));
            }
            c.expect(&Tok::Semi, "expected ';' after forward declaration")?;
            match kind.as_str() {
                "actor" => out.actors.push(name),
                "class" => {
                    out.class_forwards.push(name);
                    out.class_forward_sites.push((start, c.i));
                }
                "struct" => out.struct_forwards.push(name),
                _ => unreachable!(),
            }
        } else {
            let declaration_start = c.i;
            let public = c.take_word("pub");
            if c.take_word("mtd") {
                let (method, start, end, method_start) = c.receiver(pos, public)?;
                if out.receivers.iter().any(|m: &ReceiverHeader| m.owner == method.owner
                    && m.name == method.name && m.arity == method.arity) {
                    return Err(Diagnostic::new(pos, "E_DUPLICATE",
                        "duplicate receiver signature (owner/name/arity)"));
                }
                spans.push((out.receivers.len(), start, end));
                out.receiver_sites.push(ReceiverSite {
                    declaration_start, method_start, end,
                });
                out.receivers.push(method);
            } else if c.take_word("constructor") {
                let site = c.constructor_site(pos, public, declaration_start)?;
                if out.constructors.iter().any(|prev| prev.owner == site.owner) {
                    return Err(Diagnostic::new(pos, "E_DUPLICATE",
                        "at most one authored constructor per nominal owner in v1"));
                }
                out.constructors.push(site);
            } else if c.take_word("fnc") || c.take_word("routine") {
                function_spans.push(c.function()?);
            } else if c.return_first_header() {
                // A keyword-free T <- name(...) callable is unambiguous in
                // declaration scope, and has the same owner/name/arity identity.
                function_spans.push(c.function()?);
            } else {
                return Err(c.err("E_SYNTAX",
                    "expected namespace header, module import, declared/concrete actor, receiver method, or fnc"));
            }
        }
        decls += 1;
    }
    for receiver in &out.receivers {
        if !out.actors.contains(&receiver.owner) && !out.classes.contains(&receiver.owner) &&
           !out.class_forwards.contains(&receiver.owner) &&
           !out.struct_forwards.contains(&receiver.owner) {
            return Err(Diagnostic::new(receiver.pos, "E_UNBOUND",
                format!("receiver owner '{}' is not declared in this source namespace",
                    receiver.owner)));
        }
        // For classes, mtd adds a *second implementation*: same owner/name/
        // arity alongside an inline method is a duplicate. For actors, mtd
        // remains a signature-only declaration paired with an inline actor
        // method. Its return/parameter mismatch is E_SIGNATURE from the
        // actor interface checker, NOT a duplicate-implementation error.
        let duplicate_inline = out.class_definitions.iter()
            .filter(|d| d.name == receiver.owner)
            .any(|d| d.methods.iter().any(|m| m.name == receiver.name &&
                 m.params.len() == receiver.arity));
        if duplicate_inline {
            return Err(Diagnostic::new(receiver.pos, "E_DUPLICATE",
                "out-of-line receiver duplicates an inline method (owner/name/arity)"));
        }
    }
    for owner in &out.state_owners {
        if !out.classes.contains(owner) && !out.class_forwards.contains(owner) {
            return Err(Diagnostic::new(toks[0].pos, "E_UNBOUND",
                format!("guarded state owner '{owner}' has no class declaration")));
        }
    }
    for site in &out.constructors {
        if out.actors.contains(&site.owner) {
            return Err(Diagnostic::new(site.pos, "E_ACTOR", "actors never have constructors"));
        }
        if out.struct_forwards.contains(&site.owner) {
            return Err(Diagnostic::new(site.pos, "E_UNSUPPORTED",
                "struct constructor value ABI is not implemented in this browser backend"));
        }
        if !out.classes.contains(&site.owner) && !out.class_forwards.contains(&site.owner) {
            return Err(Diagnostic::new(site.pos, "E_UNBOUND",
                format!("constructor owner '{}' is not declared", site.owner)));
        }
        if out.class_definitions.iter().any(|d| d.name == site.owner && d.ctor.is_some()) {
            return Err(Diagnostic::new(site.pos, "E_DUPLICATE",
                "out-of-line constructor conflicts with inline constructor"));
        }
    }
    for (i, start, end) in spans {
        validate_receiver_body(toks, &out, i, start, end)?;
    }
    for (start, end) in function_spans {
        validate_spawned_actor_calls(toks, &out, start, end)?;
    }
    Ok(out)
}



/// Transform a class-only out-of-line receiver unit into normal class member
/// tokens. This is a *syntax lowering*: the production parser, ownership
/// checker and Wasm emitter then do all semantic work on the resulting AST.
/// No actor receiver, namespace/import or mutable receiver is admitted here.
pub fn lower_class_receivers(toks: &[Token], headers: &TargetHeaders) -> R<Vec<Token>> {
    let pos = toks.first().map(|t| t.pos).unwrap_or_default();
    if !headers.state_owners.is_empty() {
        return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
            "guarded class state needs checked per-instance synchronization; no ordinary-field fallback"));
    }
    if headers.classes.is_empty() || headers.namespace.is_some() ||
       !headers.imports.is_empty() || !headers.actors.is_empty() ||
       !headers.definitions.is_empty() || !headers.struct_forwards.is_empty() {
        return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
            "only local class receivers can be compiled; actor, namespace and import linking is unavailable"));
    }
    if headers.class_ends.len() != headers.class_definitions.len() ||
        headers.receiver_sites.len() != headers.receivers.len() ||
        headers.class_forwards.len() != headers.class_forward_sites.len() {
        return Err(Diagnostic::new(pos, "E_SYNTAX", "inconsistent receiver token ranges"));
    }
    // One inserted token stream per class. The original class declaration is
    // kept in place, while out-of-line method headers/bodies are attached
    // immediately before its closing end. Source token positions are retained.
    let mut insertions: Vec<Vec<Token>> = vec![Vec::new(); headers.class_definitions.len()];
    // Bound source rewriting to O(tokens + copied method tokens), even when
    // a file declares hundreds of classes/receivers within SOURCE_CAP.
    // The previous nested per-token scans over class ends / omission ranges
    // were quadratic in declaration count.
    let mut omitted = vec![false; toks.len()];
    // Validate *all* source ranges before the first semantic self/effect
    // scan. A forged overlapping ledger must be E_SYNTAX, never be interpreted
    // as a receiver body that can accidentally read another declaration.
    for (start, end) in &headers.class_forward_sites {
        if *start >= *end || *end > toks.len() {
            return Err(Diagnostic::new(pos, "E_SYNTAX", "invalid class forward source span"));
        }
        for slot in &mut omitted[*start..*end] {
            if *slot { return Err(Diagnostic::new(pos, "E_SYNTAX", "overlapping class forward")); }
            *slot = true;
        }
    }
    for site in &headers.constructors {
        if site.declaration_start >= site.params_start ||
           site.params_start >= site.body_start ||
           site.body_start >= site.end || site.end > toks.len() {
            return Err(Diagnostic::new(site.pos, "E_SYNTAX",
                "invalid constructor source span"));
        }
        for slot in &mut omitted[site.declaration_start..site.end] {
            if *slot { return Err(Diagnostic::new(site.pos, "E_SYNTAX", "overlapping constructor")); }
            *slot = true;
        }
    }
    for site in &headers.receiver_sites {
        if site.declaration_start >= site.method_start ||
            site.method_start >= site.end || site.end > toks.len() {
            return Err(Diagnostic::new(pos, "E_SYNTAX",
                "invalid out-of-line receiver source span"));
        }
        for slot in &mut omitted[site.declaration_start..site.end] {
            if *slot {
                return Err(Diagnostic::new(pos, "E_SYNTAX",
                    "overlapping class receiver source spans"));
            }
            *slot = true;
        }
    }
    for (receiver, site) in headers.receivers.iter().zip(&headers.receiver_sites) {
        if receiver.mutable {
            return Err(Diagnostic::new(receiver.pos, "E_UNSUPPORTED",
                "mutable class mtd receivers require a verified mutable-self ownership ABI"));
        }
        let owner = headers.class_definitions.iter().position(|c| c.name == receiver.owner)
            .ok_or_else(|| Diagnostic::new(receiver.pos, "E_UNBOUND",
                "class receiver owner has no local definition"))?;
        if site.declaration_start >= site.method_start ||
            site.method_start >= site.end || site.end > toks.len() ||
            headers.class_ends[owner] >= toks.len() {
            return Err(Diagnostic::new(receiver.pos, "E_SYNTAX",
                "invalid out-of-line receiver source span"));
        }
        // Keep this v1 profile *conservative* until effect/borrow lowering is
        // available: an immutable receiver may observe scalar fields and call
        // another immutable class mtd, but may not escape or invoke arbitrary
        // inline methods with unproven effects. This check runs on original
        // lexer tokens, so comments and strings cannot forge receiver syntax.
        // The production parser/checker still validates the emitted AST.
        if headers.class_definitions[owner].fields.iter().any(|field|
            !matches!(field.ty, crate::ast::Type::Int | crate::ast::Type::Bool |
                crate::ast::Type::Float | crate::ast::Type::Str)) {
            return Err(Diagnostic::new(receiver.pos, "E_UNSUPPORTED_TYPE",
                "immutable mtd query mode requires scalar instance fields"));
        }
        for i in site.method_start..site.end {
            if !word_at(toks, i, "self") { continue; }
            if !at(toks, i + 1, &Tok::Dot) {
                return Err(diagnostic(toks, i, "E_OWNERSHIP",
                    "immutable class receiver cannot escape, alias or be reborrowed"));
            }
            let method = match toks.get(i + 2).map(|t| &t.tok) {
                Some(Tok::Ident(name)) => name.as_str(),
                _ => return Err(diagnostic(toks, i, "E_OWNERSHIP",
                    "invalid immutable class member access")),
            };
            match toks.get(i + 3).map(|t| &t.tok) {
                Some(Tok::Assign | Tok::PlusAssign | Tok::PlusPlus | Tok::MinusMinus) =>
                    return Err(diagnostic(toks, i, "E_OWNERSHIP",
                        "immutable class mtd cannot mutate instance fields")),
                Some(Tok::LParen) => {
                    if !headers.receivers.iter().any(|other|
                        other.owner == receiver.owner && other.name == method &&
                        !other.mutable) {
                        return Err(diagnostic(toks, i, "E_UNSUPPORTED",
                            "immutable mtd may call only checked immutable class mtd"));
                    }
                }
                _ => {}
            }
        }
        if receiver.public {
            // pub mtd (self: Type) method(...) becomes a public inline method.
            if !matches!(&toks[site.declaration_start].tok, Tok::Ident(s) if s == "pub") {
                return Err(Diagnostic::new(receiver.pos, "E_SYNTAX",
                    "missing public receiver visibility token"));
            }
            insertions[owner].push(toks[site.declaration_start].clone());
        }
        insertions[owner].extend_from_slice(&toks[site.method_start..site.end]);

    }
    // Constructor bodies are appended to the existing class declaration,
    // never turned into factory methods or used for actor/struct ownership.
    for site in &headers.constructors {
        let owner = headers.class_definitions.iter().position(|c| c.name == site.owner)
            .ok_or_else(|| Diagnostic::new(site.pos, "E_UNLINKED",
                "out-of-line constructor requires a concrete local class definition"))?;
        // All out-of-line constructors become the same parsed ClassDecl
        // as inline constructors. The AST-level constructor_self_stmts gate
        // in check::body_check applies to both forms before guest codegen.
        // No distinct lexer-only ownership policy remains here.
        // Reuse the *same* production constructor checker and guest codegen.
        // The result marker ': self' is compile-time only, not runtime ABI.
        if site.public {
            insertions[owner].push(Token { tok: Tok::Ident("pub".to_owned()), pos: site.pos });
        }
        insertions[owner].push(Token { tok: Tok::Ident("constructor".to_owned()), pos: site.pos });
        insertions[owner].extend_from_slice(&toks[site.params_start..site.body_start - 2]);
        insertions[owner].extend_from_slice(&toks[site.body_start..site.end]);
    }
    let mut insert_at = vec![None; toks.len()];
    for (owner, end) in headers.class_ends.iter().copied().enumerate() {
        if end >= toks.len() || insert_at[end].replace(owner).is_some() {
            return Err(Diagnostic::new(pos, "E_SYNTAX",
                "invalid or overlapping class closing token spans"));
        }
        if omitted[end] {
            return Err(Diagnostic::new(pos, "E_SYNTAX",
                "class receiver span overlaps a class end delimiter"));
        }
    }
    let mut result: Vec<Token> = Vec::with_capacity(toks.len());
    for (i, token) in toks.iter().enumerate() {
        if let Some(owner) = insert_at[i] {
            result.extend(insertions[owner].iter().cloned());
        }
        if !omitted[i] {
            result.push(token.clone());
        }
    }
    Ok(result)
}

/// Resolve a receiver header against nominal, file-scoped symbols. This does
/// not link a full actor definition or prove that a method is callable through
/// an ActorRef. The namespace is this file's identity, *not* an open import.
pub fn resolve_receiver_header<'a>(
    symbols: &'a TargetHeaders,
    namespace: Option<&str>,
    actor: &str,
    name: &str,
    arity: usize,
    external: bool,
    pos: Pos,
) -> R<&'a ReceiverHeader> {
    if symbols.namespace.as_deref() != namespace {
        return Err(Diagnostic::new(pos, "E_NAMESPACE",
            "receiver lookup is not in the source namespace"));
    }
    if !symbols.actors.iter().any(|a| a == actor) &&
        !symbols.classes.iter().any(|a| a == actor) {
        return Err(Diagnostic::new(pos, "E_UNBOUND",
            format!("unknown actor receiver type '{actor}'")));
    }
    let Some(method) = symbols.receivers.iter().find(|m|
        m.owner == actor && m.name == name && m.arity == arity) else {
        return Err(Diagnostic::new(pos, "E_UNBOUND",
            format!("actor '{actor}' has no receiver method '{name}' with arity {arity}")));
    };
    if external && !method.public {
        return Err(Diagnostic::new(pos, "E_VISIBILITY",
            format!("receiver '{actor}.{name}' is not public")));
    }
    Ok(method)
}

fn word_at(toks: &[Token], index: usize, word: &str) -> bool {
    matches!(toks.get(index).map(|t| &t.tok), Some(Tok::Ident(s)) if s == word)
}
fn at(toks: &[Token], index: usize, tok: &Tok) -> bool {
    toks.get(index).is_some_and(|t| &t.tok == tok)
}
fn diagnostic(toks: &[Token], index: usize, code: &'static str, why: &str) -> Diagnostic {
    Diagnostic::new(toks.get(index).map_or(Pos::default(), |t| t.pos), code, why)
}
fn close_paren(toks: &[Token], start: usize, limit: usize) -> R<usize> {
    let mut depth = 0usize;
    for i in start..limit {
        if at(toks, i, &Tok::LParen) { depth += 1; }
        if at(toks, i, &Tok::RParen) {
            if depth == 0 {
                return Err(diagnostic(toks, i, "E_SYNTAX", "unexpected ')'"));
            }
            depth -= 1;
            if depth == 0 { return Ok(i); }
        }
    }
    Err(diagnostic(toks, start, "E_EOF", "unterminated argument list"))
}
fn count_args(toks: &[Token], open: usize, close: usize) -> usize {
    if close == open + 1 { return 0; }
    let (mut n, mut round, mut square, mut braces) = (1, 0, 0, 0);
    for token in toks.iter().take(close).skip(open + 1) {
        match token.tok {
            Tok::LParen => round += 1,
            Tok::RParen => round -= 1,
            Tok::LBracket => square += 1,
            Tok::RBracket => square -= 1,
            Tok::LBrace => braces += 1,
            Tok::RBrace => braces -= 1,
            Tok::Comma if round == 0 && square == 0 && braces == 0 => n += 1,
            _ => {}
        }
    }
    n
}
fn validate_callback(
    toks: &[Token], symbols: &TargetHeaders, receiver: &ReceiverHeader,
    open: usize, limit: usize,
) -> R<usize> {
    let close = close_paren(toks, open, limit)?;
    let mut k = open + 1;
    if !word_at(toks, k, "critical") || !at(toks, k+1, &Tok::Minus) ||
        !(word_at(toks, k+2, "read") || word_at(toks, k+2, "write")) {
        return Err(diagnostic(toks, k, "E_SEALED",
            "handle_state requires 'critical-read' or 'critical-write'"));
    }
    let write = word_at(toks, k+2, "write");
    if write && !receiver.mutable {
        return Err(diagnostic(toks, k, "E_MUTABILITY",
            "critical-write requires a mutable actor receiver"));
    }
    k += 3;
    if !at(toks, k, &Tok::Pipe) {
        return Err(diagnostic(toks, k, "E_SEALED", "expected '|state|' callback"));
    }
    let binder_pos = k + 1;
    let binder = match toks.get(binder_pos).map(|t| &t.tok) {
        Some(Tok::Ident(name)) if !is_reserved(name) => name.as_str(),
        _ => return Err(diagnostic(toks, binder_pos, "E_SEALED", "invalid state callback binder")),
    };
    if binder == "self" || binder == "_" {
        return Err(diagnostic(toks, binder_pos, "E_SEALED",
            "state callback must bind a distinct state variable"));
    }
    k += 2;
    if !at(toks, k, &Tok::Pipe) || !at(toks, k+1, &Tok::Arrow) {
        return Err(diagnostic(toks, k, "E_SEALED",
            "state callback must be '|s| -> expression'"));
    }
    k += 2;
    if k == close {
        return Err(diagnostic(toks, k, "E_SEALED", "missing critical callback body"));
    }
    // The v1 gate is conservative. A full borrow checker must subsequently
    // prove reference lifetimes, effect purity, and field types before codegen.
    for i in k..close {
        if ["await", "select", "yield", "suspends", "spawn", "rt", "defer"].iter()
            .any(|w| word_at(toks, i, w)) {
            return Err(diagnostic(toks, i, "E_BORROW",
                "suspension, spawning and deferred effects are forbidden during critical access"));
        }
        if word_at(toks, i, "handle_state") ||
            (word_at(toks, i, "self") && at(toks, i+1, &Tok::Dot)) {
            return Err(diagnostic(toks, i, "E_BORROW",
                "nested actor state access or self capture is forbidden in critical callback"));
        }
        if word_at(toks, i, binder) {
            if !at(toks, i+1, &Tok::Dot) {
                return Err(diagnostic(toks, i, "E_ESCAPE",
                    "actor state binding cannot be copied, captured, or returned"));
            }
            if !matches!(toks.get(i+2).map(|t| &t.tok), Some(Tok::Ident(_))) {
                return Err(diagnostic(toks, i+2, "E_SEALED",
                    "state field member access requires a field name"));
            }
            if !write {
                if matches!(toks.get(i+3).map(|t| &t.tok),
                    Some(Tok::Assign | Tok::PlusAssign | Tok::PlusPlus | Tok::MinusMinus)) {
                    return Err(diagnostic(toks, i+3, "E_READONLY",
                        "critical-read cannot mutate actor state"));
                }
                if at(toks, i+3, &Tok::Dot) || at(toks, i+3, &Tok::LParen) {
                    return Err(diagnostic(toks, i+3, "E_UNSUPPORTED",
                        "state field method calls need a full effect and borrow checker"));
                }
            }
        }
    }
    // Prevent the callback from smuggling a second actor's receiver semantics.
    let _ = symbols;
    Ok(close)
}
fn validate_receiver_body(
    toks: &[Token], symbols: &TargetHeaders, which: usize,
    start: usize, end: usize,
) -> R<()> {
    let receiver = &symbols.receivers[which];
    // Class receivers are parsed but not actor-sealed. No class mtd emits
    // guest code until its linker, type checker and dispatch are implemented.
    if symbols.classes.iter().any(|c| c == &receiver.owner) {
        return Ok(());
    }
    // Bare -> Type bodies start with a statement rather than a delimiter;
    // do not skip the first token and bypass sealed-state validation.
    let mut i = if at(toks, start, &Tok::LBrace) || at(toks, start, &Tok::ColonColon) {
        start + 1
    } else { start };
    while i < end.saturating_sub(1) {
        if word_at(toks, i, "handle_state") &&
            !(i >= 2 && word_at(toks, i-2, "self") && at(toks, i-1, &Tok::Dot)) {
            return Err(diagnostic(toks, i, "E_SEALED",
                "actor state access must be 'self.handle_state(...)'"));
        }
        if word_at(toks, i, "self") && at(toks, i+1, &Tok::Dot) {
            let member = match toks.get(i+2).map(|t| &t.tok) {
                Some(Tok::Ident(s)) => s.as_str(),
                _ => return Err(diagnostic(toks, i+2, "E_SEALED", "invalid actor member access")),
            };
            if !at(toks, i+3, &Tok::LParen) {
                return Err(diagnostic(toks, i, "E_SEALED",
                    "direct actor fields are sealed; use self.handle_state"));
            }
            if member == "handle_state" {
                let closed = validate_callback(toks, symbols, receiver, i+3, end)?;
                i = closed + 1;
                continue;
            }
            let close = close_paren(toks, i+3, end)?;
            resolve_receiver_header(symbols, symbols.namespace.as_deref(), &receiver.owner,
                member, count_args(toks, i+3, close), false, toks[i].pos)?;
            i = close + 1;
            continue;
        }
        i += 1;
    }
    Ok(())
}
fn validate_spawned_actor_calls(
    toks: &[Token], symbols: &TargetHeaders, start: usize, end: usize,
) -> R<()> {
    // Narrow, lexical analysis of direct 'val ref = spawn Actor()' bindings.
    // A later typed checker must handle aliases, parameters and dataflow.
    let mut actor_refs: Vec<(&str, &str)> = Vec::new();
    let first = if at(toks, start, &Tok::LBrace) || at(toks, start, &Tok::ColonColon) {
        start + 1
    } else { start };
    for i in first..end.saturating_sub(1) {
        if (word_at(toks, i, "val") || word_at(toks, i, "let")) &&
            matches!(toks.get(i+1).map(|t| &t.tok), Some(Tok::Ident(_))) &&
            at(toks, i+2, &Tok::Assign) && word_at(toks, i+3, "spawn") {
            if let (Some(Tok::Ident(name)), Some(Tok::Ident(actor))) =
                (toks.get(i+1).map(|t| &t.tok), toks.get(i+4).map(|t| &t.tok)) {
                if symbols.actors.contains(actor) && at(toks, i+5, &Tok::LParen) &&
                    at(toks, i+6, &Tok::RParen) {
                    actor_refs.push((name, actor));
                }
            }
        }
    }
    for i in first..end.saturating_sub(1) {
        if let Some((name, _)) = actor_refs.iter().find(|(n,_)| word_at(toks, i, n)) {
            if at(toks, i+1, &Tok::Dot) &&
                matches!(toks.get(i+2).map(|t| &t.tok), Some(Tok::Ident(_)))
                && !(word_at(toks, i+2, "send") || word_at(toks, i+2, "get_done")) {
                return Err(diagnostic(toks, i, "E_ISOLATION",
                    "ActorRef cannot call receiver methods synchronously; send a mailbox message"));
            }
            let _ = name;
        }
    }
    Ok(())
}
