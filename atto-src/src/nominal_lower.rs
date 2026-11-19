//! Conservative nominal composition for source-local interface/trait/class declarations.
//!
//! Interface obligations and concrete trait/class methods are resolved before
//! the production parser, checker and Wasm emitter. This profile has NO runtime
//! base-class pointer, implicit dynamic dispatch, or unsafe actor state.
//! Direct initialized scalar parent slots have a bounded typed layout plan;
//! constructors, parent casts, owned fields and actor state fail closed.
use std::collections::{BTreeMap, BTreeSet};

use crate::diag::{Diagnostic, Pos};
use crate::lexer::{Tok, Token};

type R<T> = Result<T, Diagnostic>;
const MAX_DECLS: usize = 96;
const MAX_METHODS: usize = 256;
const MAX_BASES: usize = 8;

#[derive(Clone, Copy, Eq, PartialEq)]
enum Kind { Class, Trait, Interface }
#[derive(Clone)]
struct Method {
    name: String,
    sig: Vec<Tok>,
    tokens: Vec<Token>,
    origin: String,
    public: bool,
    overriding: bool,
    /// Exact source position of the override keyword; body identifiers
    /// named 'override' must never be rewritten or dropped.
    override_pos: Option<Pos>,
    pos: Pos,
}
#[derive(Clone)]
struct Decl {
    name: String,
    pos: Pos,
    kind: Kind,
    start: usize,
    end: usize,
    body: Vec<Token>,
    parents: Vec<String>,
    contracts: Vec<String>,
    methods: BTreeMap<String, Method>,
    has_fields_or_ctor: bool,
    export: bool,
    requires_lowering: bool,
}
fn is(t: &[Token], i: usize, value: &str) -> bool {
    matches!(t.get(i).map(|t| &t.tok), Some(Tok::Ident(s)) if s == value)
}
fn name(t: &[Token], i: usize) -> R<String> {
    match t.get(i) {
        Some(Token { tok: Tok::Ident(s), .. }) if s.len() <= 96 &&
            !matches!(s.as_str(), "as" | "end" | "define" | "pub" | "class" | "trait" | "interface" | "extends" | "implements") =>
            Ok(s.clone()),
        Some(t) => Err(Diagnostic::new(t.pos, "E_SYNTAX", "expected a bounded nominal identifier")),
        None => Err(Diagnostic::new(Pos { line: 1, col: 1 }, "E_EOF", "missing nominal identifier")),
    }
}
fn diag(pos: Pos, code: &'static str, what: impl Into<String>) -> Diagnostic {
    Diagnostic::new(pos, code, what)
}
fn closing(t: &[Token], open: usize, left: Tok, right: Tok) -> R<usize> {
    let mut depth = 0usize;
    for (i, token) in t.iter().enumerate().skip(open) {
        if token.tok == left { depth += 1; }
        if token.tok == right {
            if depth == 0 { return Err(diag(token.pos, "E_SYNTAX", "unbalanced delimiter")); }
            depth -= 1;
            if depth == 0 { return Ok(i); }
        }
        if depth > 128 { return Err(diag(token.pos, "E_NESTING", "nominal member nesting limit")); }
    }
    Err(diag(t[open].pos, "E_EOF", "unclosed nominal method body"))
}

/// Parse only brace-bodied methods and interface signatures. Refuse exotic
/// member syntax rather than accidentally treating a declaration as a field.
fn members(t: &[Token], kind: Kind, owner: &str, has_parent: bool) -> R<(BTreeMap<String, Method>, bool)> {
    let (mut i, mut out, mut fields) = (0usize, BTreeMap::new(), false);
    while i < t.len() {
        if out.len() >= MAX_METHODS { return Err(diag(t[i].pos, "E_SOURCE_LIMIT", "too many nominal members")); }
        let start = i;
        let public = if is(t, i, "pub") { i += 1; true } else {
            if is(t, i, "private") { i += 1; }
            kind != Kind::Class
        };
        let override_at = if is(t, i, "override") { let v = i; i += 1; Some(v) } else { None };
        if override_at.is_some() && kind != Kind::Class {
            return Err(diag(t[start].pos, "E_OVERRIDE",
                "trait/interface methods cannot declare a class override"));
        }
        // Parsed only in a class member declaration. Until inherited physical
        // slots have a verified layout ABI, recognize the exact target spelling
        // and fail closed rather than treating `use` as a field declaration.
        // A normal method named `use(...)` is NOT a field-alias declaration.
        if is(t, i, "use") && t.get(i + 1).map(|x| &x.tok) != Some(&Tok::LParen) {
            let at = t[i].pos;
            if kind != Kind::Class || override_at.is_some() || public {
                return Err(diag(at, "E_SYNTAX", "inherited field aliases require a plain class member 'use' declaration"));
            }
            let ancestor = name(t, i + 1)?;
            if t.get(i + 2).map(|x| &x.tok) != Some(&Tok::Dot) {
                return Err(diag(t.get(i + 2).map_or(at, |x| x.pos), "E_SYNTAX",
                    "inherited member qualification uses '.' (never '::')"));
            }
            let field = name(t, i + 3)?;
            if !is(t, i + 4, "as") {
                return Err(diag(t.get(i + 4).map_or(at, |x| x.pos), "E_SYNTAX",
                    "inherited field alias requires 'as alias_name'"));
            }
            let alias = name(t, i + 5)?;
            if t.get(i + 6).map(|x| &x.tok) != Some(&Tok::Semi) {
                return Err(diag(t.get(i + 6).map_or(at, |x| x.pos), "E_SYNTAX",
                    "inherited field alias must end with ';'"));
            }
            if !has_parent {
                return Err(diag(at, "E_ALIAS_TARGET", format!(
                    "cannot alias {ancestor}.{field} as {alias}: class has no ancestors")));
            }
            // Syntax is valid. Semantic alias admission and physical-slot
            // generation run after the complete nominal ancestry is known.
            i += 7;
            continue;
        }
        if is(t, i, "fnc") || is(t, i, "method") { i += 1; }
        let is_ctor = is(t, i, "constructor");
        let method = matches!(t.get(i + 1).map(|x| &x.tok), Some(Tok::LParen));
        if !method && !is_ctor {
            if kind != Kind::Class { return Err(diag(t[start].pos, "E_UNSUPPORTED", "interfaces/traits only admit callable members")); }
            if override_at.is_some() {
                return Err(diag(t[start].pos, "E_OVERRIDE", "override requires a callable method"));
            }
            fields = true;
            while i < t.len() && t[i].tok != Tok::Semi {
                if t[i].tok == Tok::LBrace || t[i].tok == Tok::Eof {
                    return Err(diag(t[i].pos, "E_UNSUPPORTED", "non-scalar inherited fields are unsupported"));
                }
                i += 1;
            }
            if i == t.len() { return Err(diag(t[start].pos, "E_SYNTAX", "unterminated class field")); }
            i += 1;
            continue;
        }
        let member_name = name(t, i)?;
        if is_ctor && kind != Kind::Class {
            return Err(diag(t[i].pos, "E_UNSUPPORTED", "trait/interface constructors are unsupported"));
        }
        let args_end = closing(t, i + 1, Tok::LParen, Tok::RParen)?;
        let mut end = args_end + 1;
        while end < t.len() && t[end].tok != Tok::LBrace && t[end].tok != Tok::Semi {
            if is(t, end, "end") { return Err(diag(t[end].pos, "E_UNSUPPORTED", "end-bodied inherited members require separate lowering")); }
            end += 1;
        }
        if end == t.len() { return Err(diag(t[start].pos, "E_EOF", "unterminated member signature")); }
        let signature = t[i + 1..end].iter().map(|t| t.tok.clone()).collect();
        let header_end = end;
        let has_body = t[end].tok == Tok::LBrace;
        if kind == Kind::Interface && has_body {
            return Err(diag(t[end].pos, "E_UNSUPPORTED", "interface members require signatures, not trait defaults"));
        }
        if kind != Kind::Interface && !has_body {
            return Err(diag(t[end].pos, "E_UNSUPPORTED", "concrete nominal members require braced implementation"));
        }
        if has_body { end = closing(t, end, Tok::LBrace, Tok::RBrace)?; }
        if is_ctor {
            fields = true;
            i = end + 1;
            continue;
        }
        let mut copied = t[start..=end].to_vec();
        if let Some(at) = override_at { copied.remove(at - start); }
        if kind == Kind::Trait && !is(t, start, "pub") {
            copied.insert(0, Token { pos: t[start].pos, tok: Tok::Ident("pub".into()) });
        }
        let m = Method {
            name: member_name.clone(), sig: signature,
            tokens: copied, origin: format!("{owner}::{member_name}"),
            public, overriding: override_at.is_some(),
            override_pos: override_at.map(|i| t[i].pos), pos: t[start].pos,
        };
        if out.insert(member_name.clone(), m).is_some() {
            return Err(diag(t[start].pos, "E_DUPLICATE", format!("duplicate method '{member_name}'")));
        }
        i = header_end;
        if has_body { i = end + 1; } else { i += 1; }
    }
    Ok((out, fields))
}
fn decls(t: &[Token]) -> R<BTreeMap<String, Decl>> {
    let (mut i, mut out, mut braces) = (0usize, BTreeMap::new(), 0usize);
    while i < t.len() {
        if t[i].tok == Tok::LBrace { braces += 1; }
        if t[i].tok == Tok::RBrace { braces = braces.saturating_sub(1); }
        if braces > 0 { i += 1; continue; }
        let start = i;
        let mut j = i;
        let mut export = false;
        if is(t, j, "pub") && is(t, j + 1, "define") { export = true; j += 1; }
        if !is(t, j, "define") { i += 1; continue; }
        j += 1;
        if is(t, j, "pub") { export = true; j += 1; }
        let kind = if is(t, j, "class") { Kind::Class }
            else if is(t, j, "trait") { Kind::Trait }
            else if is(t, j, "interface") { Kind::Interface }
            else { i += 1; continue; };
        j += 1;
        if out.len() >= MAX_DECLS { return Err(diag(t[start].pos, "E_SOURCE_LIMIT", "too many nominal definitions")); }
        let owner = name(t, j)?;
        j += 1;
        let mut parents = Vec::new();
        let mut contracts = Vec::new();
        if is(t, j, "extends") {
            j += 1;
            loop {
                if parents.len() >= MAX_BASES { return Err(diag(t[start].pos, "E_SOURCE_LIMIT", "too many class bases")); }
                let candidate = name(t, j)?;
                if parents.contains(&candidate) {
                    return Err(diag(t[j].pos, "E_DUPLICATE",
                        format!("duplicate class base '{candidate}'")));
                }
                parents.push(candidate); j += 1;
                if t.get(j).map(|x| &x.tok) != Some(&Tok::Comma) { break; }
                j += 1;
            }
        }
        if is(t, j, "implements") {
            j += 1;
            loop {
                if contracts.len() >= MAX_BASES { return Err(diag(t[start].pos, "E_SOURCE_LIMIT", "too many contracts")); }
                let candidate = name(t, j)?;
                if contracts.contains(&candidate) {
                    return Err(diag(t[j].pos, "E_DUPLICATE",
                        format!("duplicate implemented contract '{candidate}'")));
                }
                contracts.push(candidate); j += 1;
                if t.get(j).map(|x| &x.tok) != Some(&Tok::Comma) { break; }
                j += 1;
            }
        }
        if !is(t, j, "as") { return Err(diag(t[j.min(t.len()-1)].pos, "E_SYNTAX", "expected 'as' after nominal header")); }
        j += 1;
        let body_start = j;
        let mut depth = 0usize;
        while j < t.len() {
            if t[j].tok == Tok::LBrace { depth += 1; }
            if t[j].tok == Tok::RBrace {
                if depth == 0 { return Err(diag(t[j].pos, "E_SYNTAX", "orphan class member brace")); }
                depth -= 1;
            }
            if depth == 0 && is(t, j, "end") { break; }
            if t[j].tok == Tok::Eof { break; }
            j += 1;
        }
        if j == t.len() || t[j].tok == Tok::Eof {
            return Err(diag(t[start].pos, "E_EOF", "unterminated nominal declaration"));
        }
        let body = t[body_start..j].to_vec();
        let (methods, has_fields_or_ctor) = members(&body, kind, &owner, !parents.is_empty())?;
        let d = Decl {
            name: owner.clone(), pos: t[start].pos, kind, start, end: j + 1,
            body, parents: parents.clone(), contracts: contracts.clone(),
            methods, has_fields_or_ctor, export,
            requires_lowering: kind != Kind::Class || !parents.is_empty() || !contracts.is_empty(),
        };
        if out.insert(owner.clone(), d).is_some() {
            return Err(diag(t[start].pos, "E_DUPLICATE", format!("duplicate nominal declaration '{owner}'")));
        }
        i = j + 1;
    }
    Ok(out)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScalarKind { Int, Bool }

/// A literal class field is one 8-byte physical storage slot in the current
/// checked browser-Wasm class ABI. Not an implicit parent pointer or cast.
#[derive(Clone)]
struct ScalarBaseField {
    name: String,
    tokens: Vec<Token>,
    name_index: usize,
    public: bool,
    kind: ScalarKind,
}

/// Identity is the *declaring* parent plus its original member, not an alias.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct FieldOrigin { parent: String, member: String }

/// Typed, bounded direct-parent storage descriptor. This plan is consumed
/// before token lowering, retaining provenance while determining offsets.
#[derive(Clone)]
struct PlannedScalarSlot {
    origin: FieldOrigin,
    scalar_type: ScalarKind,
    absolute_offset: u32,
    field: ScalarBaseField,
}
#[derive(Clone)]
struct DirectParentSubobject {
    parent: String,
    byte_offset: u32,
    byte_size: u32,
    slots: Vec<PlannedScalarSlot>,
}

const MAX_DIRECT_SCALAR_SLOTS: usize = 256;
const SCALAR_SLOT_BYTES: u32 = crate::check::FIELD_BYTES;
#[derive(Clone)]
struct InheritedAlias {
    parent: String,
    field: String,
    alias: String,
    start: usize,
    end: usize,
    pos: Pos,
}

/// Admit only initialized, directly owned int/bool storage. Any constructor,
/// method body, computed initializer, nested object or opaque source syntax
/// fails closed rather than silently dropping a parent's storage.
fn scalar_base_fields(base: &Decl) -> R<Vec<ScalarBaseField>> {
    if !base.parents.is_empty() || !base.contracts.is_empty() || !base.methods.is_empty() {
        return Err(diag(base.pos, "E_UNSUPPORTED",
            "state-bearing inheritance requires direct bases without methods or ancestors"));
    }
    let t = &base.body;
    let mut i = 0;
    let mut fields = Vec::new();
    let mut names = BTreeSet::new();
    while i < t.len() {
        if fields.len() >= 64 {
            return Err(diag(t[i].pos, "E_SOURCE_LIMIT", "too many inherited scalar fields"));
        }
        let begin = i;
        let public = is(t, i, "pub");
        if public {
            i += 1;
            if t.get(i).map(|v| &v.tok) == Some(&Tok::LBracket) {
                if !is(t, i + 1, "pkg") || t.get(i + 2).map(|v| &v.tok) != Some(&Tok::RBracket) {
                    return Err(diag(t[begin].pos, "E_SYNTAX",
                        "only pub[pkg] is supported for scoped field visibility"));
                }
                i += 3;
            }
        } else if is(t, i, "private") { i += 1; }
        let kind = if is(t, i, "int") { ScalarKind::Int } else if is(t, i, "bool") { ScalarKind::Bool } else {
            return Err(diag(t[begin].pos, "E_UNSUPPORTED",
                "inherited state admits only initialized int/bool fields, without constructors"));
        };
        i += 1;
        let field_name = name(t, i)?;
        let at_name = i - begin;
        i += 1;
        if t.get(i).map(|v| &v.tok) != Some(&Tok::Colon) {
            return Err(diag(t[begin].pos, "E_UNSUPPORTED",
                "inherited scalar fields require a literal ':' initializer"));
        }
        i += 1;
        if kind == ScalarKind::Int && t.get(i).map(|v| &v.tok) == Some(&Tok::Minus) { i += 1; }
        let valid_literal = match t.get(i).map(|v| &v.tok) {
            Some(Tok::Int(_)) if kind == ScalarKind::Int => true,
            Some(Tok::Ident(v)) if kind == ScalarKind::Bool && (v == "true" || v == "false") => true,
            _ => false,
        };
        if !valid_literal {
            return Err(diag(t.get(i).map_or(t[begin].pos, |v| v.pos), "E_UNSUPPORTED",
                "inherited scalar initializers must be literal int/bool values"));
        }
        i += 1;
        if t.get(i).map(|v| &v.tok) != Some(&Tok::Semi) {
            return Err(diag(t.get(i).map_or(t[begin].pos, |v| v.pos), "E_UNSUPPORTED",
                "inherited scalar field must be terminated by ';'"));
        }
        i += 1;
        if !names.insert(field_name.clone()) {
            return Err(diag(t[begin].pos, "E_DUPLICATE", "duplicate inherited field name"));
        }
        fields.push(ScalarBaseField {
            name: field_name, tokens: t[begin..i].to_vec(),
            name_index: at_name, public, kind,
        });
    }
    if fields.is_empty() {
        return Err(diag(base.pos, "E_UNSUPPORTED", "base constructor/state layout is not supported"));
    }
    Ok(fields)
}

/// Alias declarations have no storage identity. Each exact direct-base field
/// is represented by ONE physical child-class slot; the alias only chooses the
/// source-level name of that slot. No extra field is emitted per alias.
fn alias_declarations(d: &Decl) -> R<Vec<InheritedAlias>> {
    let t = &d.body;
    let mut aliases = Vec::new();
    let mut i = 0;
    while i < t.len() {
        if t[i].tok == Tok::LBrace {
            i = closing(t, i, Tok::LBrace, Tok::RBrace)? + 1;
            continue;
        }
        if is(t, i, "use") && t.get(i + 1).map(|v| &v.tok) != Some(&Tok::LParen) {
            // The structural spelling was checked by members(). Never
            // reinterpret an ordinary method named use() as an alias.
            if i + 6 >= t.len() || t[i + 2].tok != Tok::Dot
                || !is(t, i + 4, "as") || t[i + 6].tok != Tok::Semi {
                return Err(diag(t[i].pos, "E_SYNTAX", "malformed inherited field alias"));
            }
            aliases.push(InheritedAlias {
                parent: name(t, i + 1)?,
                field: name(t, i + 3)?,
                alias: name(t, i + 5)?,
                start: i, end: i + 7, pos: t[i].pos,
            });
            i += 7;
        } else { i += 1; }
    }
    Ok(aliases)
}

/// Compute stable physical slots for direct parents. No class constructors,
/// inherited stateful methods, transitive parents, polymorphism or alias-created
/// fields are admitted by this bounded v1 ABI.
fn direct_parent_subobject_plan(
    d: &Decl, all: &BTreeMap<String, Decl>,
) -> R<Vec<DirectParentSubobject>> {
    let mut plan = Vec::new();
    let mut next_offset = 0u32;
    let mut total_fields = 0usize;
    for parent in &d.parents {
        let base = all.get(parent).ok_or_else(||
            diag(d.pos, "E_UNBOUND", format!("unknown parent class '{parent}'")))?;
        if base.kind != Kind::Class {
            return Err(diag(d.pos, "E_TYPE", "extends requires a concrete class"));
        }
        if !base.has_fields_or_ctor { continue; }
        let fields = scalar_base_fields(base)?;
        let start = next_offset;
        let mut slots = Vec::with_capacity(fields.len());
        for field in fields {
            total_fields = total_fields.checked_add(1).ok_or_else(||
                diag(d.pos, "E_SOURCE_LIMIT", "inherited scalar field count overflow"))?;
            if total_fields > MAX_DIRECT_SCALAR_SLOTS {
                return Err(diag(d.pos, "E_SOURCE_LIMIT", "too many inherited physical scalar slots"));
            }
            let offset = next_offset;
            next_offset = next_offset.checked_add(SCALAR_SLOT_BYTES).ok_or_else(||
                diag(d.pos, "E_SOURCE_LIMIT", "inherited scalar layout byte offset overflow"))?;
            slots.push(PlannedScalarSlot {
                origin: FieldOrigin { parent: parent.clone(), member: field.name.clone() },
                scalar_type: field.kind,
                absolute_offset: offset,
                field,
            });
        }
        let size = next_offset.checked_sub(start).ok_or_else(||
            diag(d.pos, "E_SOURCE_LIMIT", "invalid direct-parent subobject size"))?;
        plan.push(DirectParentSubobject {
            parent: parent.clone(), byte_offset: start, byte_size: size, slots,
        });
    }
    Ok(plan)
}

/// Only direct scalar fields may currently be emitted into the flattened class
/// representation. The typed plan retains original parent, member and offset;
/// no extra field is generated for a second alias or an inherited constructor.
/// It will become the bridge to the fully typed class IR in a later stage.
fn checked_scalar_aliases(
    d: &Decl, all: &BTreeMap<String, Decl>, aliases: &[InheritedAlias],
) -> R<Vec<Token>> {
    let plan = direct_parent_subobject_plan(d, all)?;
    let mut fields = BTreeMap::<FieldOrigin, &PlannedScalarSlot>::new();
    let mut exposed_names = BTreeSet::new();
    for subobject in &plan {
        for slot in &subobject.slots {
            exposed_names.insert(slot.origin.member.clone());
            if fields.insert(slot.origin.clone(), slot).is_some() {
                return Err(diag(d.pos, "E_ALIAS_DUPLICATE", "duplicate inherited physical field origin"));
            }
        }
    }
    for parent in &d.parents {
        let base = &all[parent];
        for key in base.methods.keys() { exposed_names.insert(key.clone()); }
    }
    if fields.is_empty() && !aliases.is_empty() {
        return Err(diag(aliases[0].pos, "E_ALIAS_TARGET",
            "field alias target must be an inherited instance field"));
    }
    if fields.is_empty() { return Ok(Vec::new()); }
    if d.has_fields_or_ctor || !d.contracts.is_empty() {
        return Err(diag(d.pos, "E_UNSUPPORTED",
            "state-bearing inheritance with local fields/constructors or traits is not implemented"));
    }
    let mut used_origins = BTreeSet::new();
    let mut alias_names = BTreeSet::new();
    let mut aliases_by_origin = BTreeMap::new();
    for alias in aliases {
        if !d.parents.contains(&alias.parent) {
            return Err(diag(alias.pos, "E_ALIAS_TARGET",
                "field alias must select a direct ancestor in the bounded scalar layout"));
        }
        let key = FieldOrigin { parent: alias.parent.clone(), member: alias.field.clone() };
        let original = fields.get(&key).ok_or_else(||
            diag(alias.pos, "E_ALIAS_TARGET", format!(
                "no inherited instance field '{}.{}'", alias.parent, alias.field)))?;
        if !original.field.public {
            return Err(diag(alias.pos, "E_ALIAS_VISIBILITY",
                "private parent fields cannot be re-exported through use"));
        }
        if !used_origins.insert(key.clone()) || !alias_names.insert(alias.alias.clone())
            || exposed_names.contains(&alias.alias) || d.methods.contains_key(&alias.alias) {
            return Err(diag(alias.pos, "E_ALIAS_DUPLICATE",
                "field alias duplicates an origin or collides with an inherited/local member"));
        }
        aliases_by_origin.insert(key, alias);
    }
    if used_origins.len() != fields.len() {
        return Err(diag(d.pos, "E_UNSUPPORTED",
            "every inherited physical scalar slot requires exactly one explicit use alias"));
    }
    let mut output = Vec::new();
    let mut cursor = 0u32;
    for subobject in &plan {
        if subobject.byte_offset != cursor {
            return Err(diag(d.pos, "E_UNSUPPORTED", "non-contiguous parent subobject layout"));
        }
        for slot in &subobject.slots {
            if slot.absolute_offset != cursor
                || slot.origin.parent != subobject.parent
                || slot.scalar_type != slot.field.kind {
                return Err(diag(d.pos, "E_UNSUPPORTED", "parent field origin/layout mismatch"));
            }
            let alias = aliases_by_origin.get(&slot.origin).ok_or_else(||
                diag(d.pos, "E_UNSUPPORTED", "unresolved inherited scalar alias"))?;
            let mut tokens = slot.field.tokens.clone();
            tokens[slot.field.name_index] = Token {
                tok: Tok::Ident(alias.alias.clone()), pos: alias.pos,
            };
            output.extend(tokens);
            cursor = cursor.checked_add(SCALAR_SLOT_BYTES).ok_or_else(||
                diag(d.pos, "E_SOURCE_LIMIT", "parent slot offset overflow"))?;
        }
        if cursor - subobject.byte_offset != subobject.byte_size {
            return Err(diag(d.pos, "E_UNSUPPORTED", "incorrect parent subobject size"));
        }
    }
    Ok(output)
}
fn resolve(
    owner: &str, all: &BTreeMap<String, Decl>,
    cached: &mut BTreeMap<String, BTreeMap<String, Method>>,
    visiting: &mut BTreeSet<String>,
) -> R<BTreeMap<String, Method>> {
    if let Some(found) = cached.get(owner) { return Ok(found.clone()); }
    let d = all.get(owner).ok_or_else(|| diag(Pos { line: 1, col: 1 }, "E_UNBOUND", format!("unknown class '{owner}'")))?;
    if d.kind != Kind::Class { return Err(diag(d.pos, "E_TYPE", "extends requires a concrete class")); }
    if !visiting.insert(owner.to_owned()) { return Err(diag(d.pos, "E_CYCLE", "class inheritance cycle")); }
    let answer = (|| -> R<BTreeMap<String, Method>> {
        let mut inherited = BTreeMap::<String, Vec<Method>>::new();
        for parent in &d.parents {
            let base = all.get(parent).ok_or_else(|| diag(d.pos, "E_UNBOUND", format!("unknown class '{parent}'")))?;
            if base.kind != Kind::Class { return Err(diag(d.pos, "E_TYPE", "extends requires a class, not a trait/interface")); }
            // Inherited state is admitted separately by checked_scalar_aliases,
            // which rejects constructors, transitive state and unknown layouts.
            for (key, method) in resolve(parent, all, cached, visiting)? {
                if method.public {
                    let same = inherited.entry(key).or_default();
                    if !same.iter().any(|m| m.origin == method.origin) { same.push(method); }
                }
            }
        }
        let mut requirements = BTreeMap::<String, Vec<Tok>>::new();
        for contract in &d.contracts {
            let trait_or_if = all.get(contract).ok_or_else(|| diag(d.pos, "E_UNBOUND", format!("unknown implemented contract '{contract}'")))?;
            match trait_or_if.kind {
                Kind::Interface => {
                    for m in trait_or_if.methods.values() {
                        if let Some(old) = requirements.insert(m.name.clone(), m.sig.clone()) {
                            if old != m.sig { return Err(diag(d.pos, "E_SIGNATURE", "conflicting interface method signatures")); }
                        }
                    }
                }
                Kind::Trait => for (key, method) in &trait_or_if.methods {
                    let same = inherited.entry(key.clone()).or_default();
                    if !same.iter().any(|m| m.origin == method.origin) { same.push(method.clone()); }
                },
                Kind::Class => return Err(diag(d.pos, "E_TYPE", "implements expects interface or trait, not class")),
            }
        }
        let mut result = BTreeMap::new();
        let mut inherited_concrete_names = BTreeSet::new();
        for (name, choices) in inherited {
            if let Some(local) = d.methods.get(&name) {
                if !local.overriding {
                    return Err(diag(local.pos, "E_OVERRIDE_REQUIRED",
                        format!("'{name}' must explicitly override the inherited implementation")));
                }
                // Every competing origin must have an identical signature.
                // Never allow a child to silently change parameter/return ABI
                // or narrow a public inherited method to private.
                for candidate in &choices {
                    if local.sig != candidate.sig {
                        return Err(diag(local.pos, "E_SIGNATURE",
                            format!("override '{name}' must match all inherited method signatures")));
                    }
                    if candidate.public && !local.public {
                        return Err(diag(local.pos, "E_PRIVATE",
                            format!("override '{name}' cannot reduce inherited visibility")));
                    }
                }
                inherited_concrete_names.insert(name);
            } else if choices.len() > 1 {
                return Err(diag(d.pos, "E_AMBIGUOUS_MEMBER",
                    format!("ambiguous concrete inherited method '{name}'; define an explicit override")));
            } else {
                result.insert(name, choices[0].clone());
            }
        }
        for (name, local) in &d.methods {
            // Inherited methods can originate from any ancestor depth, not
            // solely direct parent methods. An interface signature alone is
            // not a concrete method that may be overridden.
            if local.overriding && !inherited_concrete_names.contains(name) {
                return Err(diag(local.pos, "E_OVERRIDE",
                    format!("method '{name}' has no concrete inherited method to override")));
            }
            result.insert(name.clone(), local.clone());
        }
        for (name, sig) in requirements {
            let selected = result.get(&name).ok_or_else(|| diag(d.pos, "E_INTERFACE", format!("missing required interface method '{name}'")))?;
            if !selected.public { return Err(diag(selected.pos, "E_PRIVATE", format!("interface method '{name}' must be public"))); }
            if selected.sig != sig {
                return Err(diag(selected.pos, "E_SIGNATURE", format!("interface method '{name}' signature mismatch")));
            }
        }
        Ok(result)
    })();
    visiting.remove(owner);
    let answer = answer?;
    cached.insert(owner.to_owned(), answer.clone());
    Ok(answer)
}
/// Desugar supported nominal composition into ordinary class methods while
/// preserving each source token's original file position.
pub fn lower(t: Vec<Token>) -> R<Vec<Token>> {
    if !t.iter().any(|x| matches!(&x.tok, Tok::Ident(s) if s == "trait" || s == "interface" || s == "extends" || s == "implements" || s == "use")) {
        return Ok(t);
    }
    let all = decls(&t)?;
    if !all.values().any(|d| d.requires_lowering) { return Ok(t); }
    let mut cache = BTreeMap::new();
    let mut visiting = BTreeSet::new();
    let mut replace = BTreeMap::<usize, (usize, Vec<Token>)>::new();
    for d in all.values() {
        if d.kind != Kind::Class {
            replace.insert(d.start, (d.end, Vec::new()));
            continue;
        }
        if !d.requires_lowering { continue; }
        let aliases = alias_declarations(d)?;
        let physical_fields = checked_scalar_aliases(d, &all, &aliases)?;
        let resolved = resolve(&d.name, &all, &mut cache, &mut visiting)?;
        let mut additions = Vec::new();
        for (name, method) in resolved {
            if !d.methods.contains_key(&name) {
                // Prevent copied inherited methods from leaking private base
                // state via self. Inherited fields/constructors are also gated.
                if method.tokens.iter().any(|t| is(std::slice::from_ref(t), 0, "super")) {
                    return Err(diag(method.pos, "E_UNSUPPORTED", "super receiver lowering is not implemented"));
                }
                additions.extend(method.tokens);
            }
        }
        let mut output = Vec::new();
        if d.export { output.push(Token { pos: d.pos, tok: Tok::Ident("pub".into()) }); }
        output.extend([
            Token { pos: d.pos, tok: Tok::Ident("define".into()) },
            Token { pos: d.pos, tok: Tok::Ident("class".into()) },
            Token { pos: d.pos, tok: Tok::Ident(d.name.clone()) },
            Token { pos: d.pos, tok: Tok::Ident("as".into()) },
        ]);
        // Emit one parent-derived physical field for each verified alias,
        // before local state so parent initialization happens first.
        output.extend(physical_fields);
        // Never pass 'use Parent.field as alias' through to the ordinary
        // parser; its exact original slot is already represented above.
        let skipped: BTreeSet<usize> = aliases.iter()
            .flat_map(|a| a.start..a.end).collect();
        // Remove only exact declaration-header override tokens. A token
        // spelled 'override' inside a method body is never a header marker.
        // Source coordinates remain unchanged for every retained token.
        for (i, token) in d.body.iter().enumerate() {
            if skipped.contains(&i) { continue; }
            let header_override = is(std::slice::from_ref(token), 0, "override")
                && d.methods.values().any(|m|
                    m.override_pos.is_some_and(|p|
                        p.line == token.pos.line && p.col == token.pos.col));
            if !header_override { output.push(token.clone()); }
        }
        output.extend(additions);
        output.push(Token { pos: d.pos, tok: Tok::Ident("end".into()) });
        replace.insert(d.start, (d.end, output));
    }
    let mut out = Vec::with_capacity(t.len());
    let mut i = 0;
    while i < t.len() {
        if let Some((end, span)) = replace.get(&i) {
            out.extend_from_slice(span);
            i = *end;
        } else {
            out.push(t[i].clone());
            i += 1;
        }
    }
    if out.len() > crate::lexer::MAX_TOKENS {
        return Err(diag(t.first().map(|x| x.pos).unwrap_or_default(), "E_SOURCE_LIMIT",
            "expanded nominal methods exceed compiler token budget"));
    }
    Ok(out)
}

#[cfg(test)]
mod typed_parent_layout_tests {
    use super::*;
    use crate::lexer::lex;

    #[test]
    fn direct_parents_keep_independent_origins_types_and_offsets() {
        let source = r#"
            define class Dog as
                pub int age: 5;
                pub bool hungry: true;
            end
            define class Cat as pub int age: 10; end
            define class Hybrid extends Dog, Cat as
                use Cat.age as cat_age;
                use Dog.hungry as dog_hungry;
                use Dog.age as dog_age;
            end
            pub fnc main(): int { return 0; }
        "#;
        let toks = lex(source).unwrap();
        let all = decls(&toks).unwrap();
        let hybrid = &all["Hybrid"];
        let plan = direct_parent_subobject_plan(hybrid, &all).unwrap();
        assert_eq!(plan.len(), 2);
        assert_eq!(plan[0].parent, "Dog");
        assert_eq!(plan[0].byte_offset, 0);
        assert_eq!(plan[0].byte_size, 16);
        assert_eq!(plan[1].parent, "Cat");
        assert_eq!(plan[1].byte_offset, 16);
        assert_eq!(plan[1].byte_size, 8);
        let dog = &plan[0].slots;
        let cat = &plan[1].slots;
        assert_eq!(dog[0].origin, FieldOrigin { parent: "Dog".into(), member: "age".into() });
        assert_eq!(dog[0].scalar_type, ScalarKind::Int);
        assert_eq!(dog[0].absolute_offset, 0);
        assert_eq!(dog[1].origin, FieldOrigin { parent: "Dog".into(), member: "hungry".into() });
        assert_eq!(dog[1].scalar_type, ScalarKind::Bool);
        assert_eq!(dog[1].absolute_offset, 8);
        assert_eq!(cat[0].origin, FieldOrigin { parent: "Cat".into(), member: "age".into() });
        assert_eq!(cat[0].absolute_offset, 16);
        let aliases = alias_declarations(hybrid).unwrap();
        assert_eq!(aliases.len(), 3);
        let tokens = checked_scalar_aliases(hybrid, &all, &aliases).unwrap();
        let names: Vec<_> = tokens.iter().filter_map(|t| match &t.tok {
            Tok::Ident(s) if s.starts_with("dog_") || s.starts_with("cat_") => Some(s.as_str()),
            _ => None,
        }).collect();
        assert_eq!(names, vec!["dog_age", "dog_hungry", "cat_age"]);
    }

    #[test]
    fn parent_constructor_never_gets_flattened_into_scalar_subobject() {
        let all = decls(&lex(r#"
            define class Dog as pub int age: 5; constructor() {} end
            define class Hybrid extends Dog as use Dog.age as dog_age; end
            pub fnc main(): int { return 0; }
        "#).unwrap()).unwrap();
        let d = direct_parent_subobject_plan(&all["Hybrid"], &all).err().unwrap();
        assert_eq!(d.code, "E_UNSUPPORTED");
    }

    #[test]
    fn bounded_parent_subobject_planning_rejects_slot_budget_exhaustion() {
        let mut src = String::new();
        let mut parents = Vec::new();
        for p in 0..5 {
            let name = format!("Parent{p}");
            parents.push(name.clone());
            src.push_str(&format!("define class {name} as "));
            for f in 0..60 {
                src.push_str(&format!("pub int f{f}: 1; "));
            }
            src.push_str("end\n");
        }
        src.push_str(&format!("define class Hybrid extends {} as end\n",
            parents.join(", ")));
        let all = decls(&lex(&src).unwrap()).unwrap();
        let d = direct_parent_subobject_plan(&all["Hybrid"], &all).err().unwrap();
        assert_eq!(d.code, "E_SOURCE_LIMIT");
    }
}
