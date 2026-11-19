//! Conservative executable scalar tuple lowering for the Rust/browser compiler.
//!
//! Converts closed `Tuple<int|bool|float|string,...>` into private generated
//! class storage and converts destructuring into exactly-once root evaluation
//! plus independent Copy scalar projections. Object/loan tuples, unproven
//! constexpr sources, dynamic tuple shapes and nested patterns fail closed.
//!
//! This is a bounded ABI subset; it is not general Tuple or actor semantics.
use std::collections::BTreeMap;
use crate::diag::{Diagnostic, Pos};
use crate::lexer::{lex, Tok, Token};
use crate::tuple_binding_admission::{self, BindingMode};

type R<T> = Result<T, Diagnostic>;
const PREFIX: &str = "__atto_tuple_private_";
const LIMIT: usize = 16;
const MAX_SHAPES: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Shape(Vec<String>);

fn word(t: &Token, s: &str) -> bool {
    matches!(&t.tok, Tok::Ident(w) if w == s)
}
fn id(t: &Token) -> Option<&str> {
    if let Tok::Ident(s) = &t.tok { Some(s) } else { None }
}
fn error(pos: Pos, code: &'static str, message: &str) -> Diagnostic {
    Diagnostic::new(pos, code, message)
}
fn eofless(mut v: Vec<Token>) -> Vec<Token> {
    if matches!(v.last().map(|t| &t.tok), Some(Tok::Eof)) { v.pop(); }
    v
}
fn synthetic(code: &str, pos: Pos) -> R<Vec<Token>> {
    let mut v = eofless(lex(code)?);
    for t in &mut v { t.pos = pos; }
    Ok(v)
}
fn matching(t: &[Token], i: usize, left: Tok, right: Tok) -> Option<usize> {
    if t.get(i)?.tok != left { return None; }
    let mut depth = 0usize;
    for (j, tok) in t.iter().enumerate().skip(i) {
        if tok.tok == left { depth += 1; }
        if tok.tok == right {
            depth -= 1;
            if depth == 0 { return Some(j); }
        }
    }
    None
}
fn primitive(s: &str) -> Option<&'static str> {
    match s {
        "int" => Some("int"),
        "bool" => Some("bool"),
        "float" | "f64" => Some("float"),
        "string" | "String" => Some("string"),
        _ => None,
    }
}
fn ctor_name(i: usize) -> String { format!("{PREFIX}{i}") }
fn shape_for(parts: Vec<String>, shapes: &mut Vec<Shape>, pos: Pos) -> R<String> {
    if parts.len() > LIMIT {
        return Err(error(pos, "E_SOURCE_LIMIT", "scalar tuples support at most 16 elements"));
    }
    let target = Shape(parts);
    if let Some(idx) = shapes.iter().position(|x| *x == target) {
        Ok(ctor_name(idx))
    } else {
        if shapes.len() >= MAX_SHAPES {
            return Err(error(pos, "E_SOURCE_LIMIT", "too many distinct scalar tuple shapes (64 maximum)"));
        }
        let idx = shapes.len();
        shapes.push(target);
        Ok(ctor_name(idx))
    }
}
fn default_value(ty: &str) -> &'static str {
    match ty {
        "int" => "0", "bool" => "false", "float" => "0.0",
        "string" => "\"\"", _ => unreachable!(),
    }
}
fn create_class(name: &str, shape: &Shape) -> String {
    let mut out = format!("define class {name} as\n");
    for (i, ty) in shape.0.iter().enumerate() {
        // Class fields now default to val/final. Tuple storage is populated
        // exactly once by this generated constructor, so its write authority
        // must be explicit, as in shape_lower::synthesized. Users still cannot
        // mutate tuple-root fields outside constructor or via mutable loans.
        out.push_str(&format!("pub let {ty} e{i} = {};\n", default_value(ty)));
    }
    out.push_str("constructor(");
    for (i, ty) in shape.0.iter().enumerate() {
        if i > 0 { out.push_str(", "); }
        out.push_str(&format!("{ty} p{i}"));
    }
    out.push_str(") {\n");
    for i in 0..shape.0.len() {
        out.push_str(&format!("self.e{i} = p{i};\n"));
    }
    out.push_str("}\nend\n");
    out
}

/// Resolve only explicitly scalar Tuple<T,...> types. No fake object
/// mutability or actor-sendable tuple representation is inferred.
fn rewrite_types(tokens: &mut Vec<Token>, shapes: &mut Vec<Shape>) -> R<()> {
    let mut i = 0usize;
    while i + 1 < tokens.len() {
        if !word(&tokens[i], "Tuple") || tokens[i + 1].tok != Tok::Lt {
            i += 1;
            continue;
        }
        // 'Tuple < expression' must remain an ordinary comparison when
        // Tuple is a local identifier. Rewrite generic types only in a
        // type-introducing context; never classify expressions by spelling.
        let type_context = if i == 0 { false } else {
            match &tokens[i - 1].tok {
                Tok::Colon | Tok::Arrow => true,
                Tok::Ident(w) if matches!(w.as_str(),
                    "let" | "val" | "const" | "pub" | "private" |
                    "final" | "mut" | "static") => true,
                Tok::LParen | Tok::Comma => {
                    // Callable argument lists also use these punctuation
                    // tokens. Require an actual generic close followed by
                    // an identifier binder, as in '(Tuple<int> value)'.
                    let mut j = i + 2;
                    while j < tokens.len()
                        && tokens[j].tok != Tok::Gt
                        && tokens[j].tok != Tok::RParen
                        && tokens[j].tok != Tok::Semi
                    { j += 1; }
                    tokens.get(j).is_some_and(|t| t.tok == Tok::Gt)
                        && tokens.get(j + 1).is_some_and(|t|
                            matches!(&t.tok, Tok::Ident(w) if w != "then"))
                }
                _ => false,
            }
        };
        if !type_context {
            i += 1;
            continue;
        }
        let start = i;
        i += 2;
        let mut ts = Vec::new();
        if tokens.get(i).is_some_and(|x| x.tok != Tok::Gt) {
            loop {
                let t = tokens.get(i).and_then(id)
                    .and_then(primitive).ok_or_else(|| error(tokens[start].pos,
                        "E_UNSUPPORTED_TYPE", "only flat Tuple<int|bool|float|string,...> is executable"))?;
                ts.push(t.to_string());
                i += 1;
                if tokens.get(i).is_some_and(|x| x.tok == Tok::Comma) {
                    i += 1;
                    continue;
                }
                break;
            }
        }
        if !tokens.get(i).is_some_and(|x| x.tok == Tok::Gt) {
            return Err(error(tokens[start].pos, "E_SYNTAX", "expected '>' after tuple element types"));
        }
        let name = shape_for(ts, shapes, tokens[start].pos)?;
        let pos = tokens[start].pos;
        tokens.splice(start..i+1, [Token { tok: Tok::Ident(name), pos }]);
        i = start + 1;
    }
    Ok(())
}

/// Split an already balanced parenthesized tuple, respecting nested calls.
/// Items remain token slices so guest expression evaluation is not duplicated.
fn tuple_items<'a>(t: &'a [Token]) -> Option<Vec<&'a [Token]>> {
    if t.first()?.tok != Tok::LParen || t.last()?.tok != Tok::RParen { return None; }
    let mut start = 1usize;
    let mut items = Vec::new();
    let mut depth = 0usize;
    let mut saw_comma = false;
    for i in 1..t.len()-1 {
        match t[i].tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                if depth == 0 { return None; }
                depth -= 1;
            }
            Tok::Comma if depth == 0 => {
                saw_comma = true;
                if i == start { return None; }
                items.push(&t[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if depth != 0 { return None; }
    if start < t.len()-1 { items.push(&t[start..t.len()-1]); }
    if !saw_comma && !items.is_empty() { return None; }
    if items.len() > LIMIT { return None; }
    Some(items)
}
fn scalar_literal(item: &[Token]) -> Option<&'static str> {
    match item {
        [Token { tok: Tok::Int(_), .. }] => Some("int"),
        [Token { tok: Tok::Float(_), .. }] => Some("float"),
        [Token { tok: Tok::Str(_), .. }] => Some("string"),
        [Token { tok: Tok::Ident(s), .. }] if s == "true" || s == "false" => Some("bool"),
        [Token { tok: Tok::Minus, .. }, Token { tok: Tok::Int(_), .. }] => Some("int"),
        [Token { tok: Tok::Minus, .. }, Token { tok: Tok::Float(_), .. }] => Some("float"),
        _ => None,
    }
}
fn constant_tuple(rhs: &[Token]) -> bool {
    tuple_items(rhs).is_some_and(|items| items.iter().all(|x| scalar_literal(x).is_some()))
}
/// Quote tokenized string values with exactly the escapes Atto's lexer
/// implements. Rust Debug uses \0 for U+0000, but Atto deliberately treats
/// unknown \0 as literal '0'; using Debug would silently corrupt data.
fn quote_string(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn as_code(tokens: &[Token]) -> R<String> {
    let mut out = String::new();
    for t in tokens {
        let s = match &t.tok {
            Tok::Ident(s) => s.clone(),
            Tok::Int(Some(v)) => v.to_string(),
            Tok::Int(None) => "9223372036854775808".to_string(),
            Tok::Float(bits) => {
                let value = f64::from_bits(*bits);
                if !value.is_finite() {
                    return Err(error(t.pos, "E_FLOAT_LITERAL",
                        "non-finite scalar tuple literal cannot be round-tripped safely"));
                }
                let mut n = value.to_string();
                if !n.contains('.') && !n.contains('e') && !n.contains('E') { n.push_str(".0"); }
                n
            },
            Tok::Str(s) => quote_string(s),
            Tok::LParen => "(".to_string(), Tok::RParen => ")".to_string(),
            Tok::LBrace => "{".to_string(), Tok::RBrace => "}".to_string(),
            Tok::LBracket => "[".to_string(), Tok::RBracket => "]".to_string(),
            Tok::Comma => ",".to_string(), Tok::Colon => ":".to_string(),
            Tok::Semi => ";".to_string(), Tok::Assign => "=".to_string(),
            Tok::Dot => ".".to_string(), Tok::Plus => "+".to_string(),
            Tok::Minus => "-".to_string(), Tok::Star => "*".to_string(),
            Tok::Slash => "/".to_string(), Tok::Lt => "<".to_string(), Tok::Gt => ">".to_string(),
            Tok::EqEq => "==".to_string(), Tok::NotEq => "!=".to_string(),
            Tok::Le => "<=".to_string(), Tok::Ge => ">=".to_string(),
            Tok::PlusPlus => "++".to_string(), Tok::MinusMinus => "--".to_string(),
            Tok::PlusAssign => "+=".to_string(), Tok::ColonColon => "::".to_string(),
            Tok::Arrow => "->".to_string(), Tok::FatArrow => "=>".to_string(),
            Tok::Pipe => "|".to_string(), Tok::PipeGt => "|>".to_string(),
            Tok::Amp => "&".to_string(), Tok::Bang => "!".to_string(),
            Tok::Question => "?".to_string(), Tok::At => "@".to_string(),
            Tok::Ellipsis => "...".to_string(), Tok::YieldStar => "yield*".to_string(),
            Tok::Eof => return Err(error(t.pos, "E_SYNTAX", "unexpected EOF in tuple expression")),
        };
        out.push_str(&s);
        out.push(' ');
    }
    Ok(out)
}

/// Gather explicit top-level scalar tuple-return signatures, so a tuple
/// binder consuming `fixtures()` cannot accidentally project an arbitrary
/// class merely because it has similarly named fields.
/// Count only source-level call/parameter commas; nested generic/function
/// delimiters do not accidentally change overload resolution.
fn argument_count(tokens: &[Token], type_parameters: bool) -> usize {
    if tokens.is_empty() { return 0; }
    let mut depth = 0usize;
    let mut count = 1usize;
    for t in tokens {
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace if depth > 0 => depth -= 1,
            // In formal parameter TYPE annotations, angles delimit
            // generic arguments. In actual CALL expressions, < and >
            // are comparisons, not grouping. Counting '<' as nesting
            // would silently misidentify a tuple-returning overload.
            Tok::Lt if type_parameters => depth += 1,
            Tok::Gt if type_parameters && depth > 0 => depth -= 1,
            Tok::Comma if depth == 0 => count += 1,
            _ => {}
        }
    }
    count
}

fn tuple_functions(tokens: &[Token], shapes: &[Shape]) -> BTreeMap<(String, usize), usize> {
    let mut result = BTreeMap::new();
    for i in 0..tokens.len().saturating_sub(3) {
        if !word(&tokens[i], "fnc") { continue; }
        let Some(name) = id(&tokens[i+1]) else { continue; };
        if tokens[i+2].tok != Tok::LParen { continue; }
        let Some(end) = matching(tokens, i+2, Tok::LParen, Tok::RParen) else { continue; };
        if tokens.get(end+1).is_none_or(|t| t.tok != Tok::Colon && t.tok != Tok::Arrow) {
            continue;
        }
        let Some(ret) = tokens.get(end+2).and_then(id) else { continue; };
        if let Some(n) = shapes.iter().enumerate().find_map(|(j,_)|
            (ctor_name(j) == ret).then_some(j))
        {
            result.insert((name.to_string(), argument_count(&tokens[i+3..end], true)), n);
        }
    }
    result
}

fn tuple_call(rhs: &[Token], funcs: &BTreeMap<(String, usize), usize>) -> Option<usize> {
    if rhs.len() < 3 || rhs[1].tok != Tok::LParen { return None; }
    let name = id(&rhs[0])?;
    if matching(rhs, 1, Tok::LParen, Tok::RParen) != Some(rhs.len()-1) { return None; }
    funcs.get(&(name.to_string(), argument_count(&rhs[2..rhs.len()-1], false))).copied()
}

/// A tuple initializer must either be an explicit tuple constructor or a
/// typed function return. This disallows arbitrary non-Tuple objects.
fn checked_rhs(rhs: &[Token], functions: &BTreeMap<(String, usize), usize>, pos: Pos) -> R<()> {
    if tuple_items(rhs).is_some() || tuple_call(rhs, functions).is_some() {
        return Ok(());
    }
    Err(error(pos, "E_UNSUPPORTED",
        "tuple destructuring requires a scalar tuple literal or a function returning Tuple<...>"))
}

fn lower_bindings(tokens: &mut Vec<Token>, functions: &BTreeMap<(String, usize), usize>, shapes: &[Shape]) -> R<()> {
    let bindings = tuple_binding_admission::inspect(tokens)?;
    for (i, b) in bindings.iter().enumerate().rev() {
        let mut end = b.rhs_start_index;
        let mut depth = 0usize;
        while end < tokens.len() {
            match tokens[end].tok {
                Tok::LParen | Tok::LBrace | Tok::LBracket => depth += 1,
                Tok::RParen | Tok::RBrace | Tok::RBracket if depth > 0 => depth -= 1,
                Tok::Semi if depth == 0 => break,
                _ => {}
            }
            end += 1;
        }
        if tokens.get(end).is_none_or(|t| t.tok != Tok::Semi) {
            return Err(error(b.pos, "E_UNSUPPORTED",
                "scalar tuple lowering requires an explicit ';' terminator"));
        }
        let rhs = &tokens[b.rhs_start_index..end];
        checked_rhs(rhs, functions, b.pos)?;
        let actual_arity = if let Some(items) = tuple_items(rhs) {
            items.len()
        } else {
            let index = tuple_call(rhs, functions).ok_or_else(|| error(b.pos,
                "E_UNSUPPORTED", "tuple-returning callable overload is not statically known"))?;
            shapes[index].0.len()
        };
        if actual_arity != b.members.len() {
            return Err(error(b.pos, "E_ARITY",
                "tuple destructuring binder count must equal initializer tuple arity"));
        }
        if b.members.iter().any(|m| m.name.is_some()
            && m.mode == BindingMode::Const && m.mutable_referent)
        {
            return Err(error(b.pos, "E_CONST_MUT_TARGET",
                "const mut on a Copy-scalar tuple element is not meaningful"));
        }
        let want_const = b.alias.as_ref().is_some_and(|a| a.mode == BindingMode::Const)
            || b.members.iter().any(|m| m.name.is_some() && m.mode == BindingMode::Const);
        if want_const && !constant_tuple(rhs) {
            return Err(error(b.pos, "E_CONST",
                "local tuple const requires a compile-time scalar tuple literal; a runtime fixtures() call is not const"));
        }
        let constant_elements = if constant_tuple(rhs) { tuple_items(rhs) } else { None };
        let owned = format!("{PREFIX}owner_{i}");
        let alias = b.alias.as_ref().map_or(owned.as_str(), |a| a.name.as_str());
        let root_mutable = b.alias.as_ref().is_some_and(|a| a.mode == BindingMode::Let);
        let mut generated = format!("{} {alias} = {} ;\n",
            if root_mutable { "let" } else { "val" }, as_code(rhs)?);
        for (k, member) in b.members.iter().enumerate() {
            if let Some(name) = &member.name {
                let ty = member.annotation.as_ref()
                    .map_or(String::new(), |t| format!(": {t}"));
                let (kind, init) = match member.mode {
                    BindingMode::Let => ("let", format!("{alias}.e{k}")),
                    BindingMode::Val => ("val", format!("{alias}.e{k}")),
                    // A const element is a true constexpr local: preserve
                    // the checked source literal, not a field read from
                    // the runtime materialized tuple root.
                    BindingMode::Const => {
                        let part = constant_elements.as_ref()
                            .and_then(|items| items.get(k))
                            .ok_or_else(|| error(b.pos, "E_CONST",
                                "tuple const element requires a constexpr literal"))?;
                        ("const", as_code(part)?)
                    }
                };
                generated.push_str(&format!("{kind} {name}{ty} = {init};\n"));
            }
        }
        tokens.splice(b.start_index..=end, synthetic(&generated, b.pos)?);
    }
    Ok(())
}

fn rewrite_literal_tuples(tokens: &mut Vec<Token>, shapes: &mut Vec<Shape>) -> R<()> {
    let mut i = 0usize;
    while i < tokens.len() {
        if tokens[i].tok != Tok::LParen
            || !(i > 0 && (word(&tokens[i-1], "return") || tokens[i-1].tok == Tok::Assign))
        {
            i += 1;
            continue;
        }
        let Some(close) = matching(tokens, i, Tok::LParen, Tok::RParen) else {
            return Err(error(tokens[i].pos, "E_SYNTAX", "unclosed tuple expression"));
        };
        let Some(items) = tuple_items(&tokens[i..=close]) else {
            i += 1;
            continue;
        };
        let detected: Option<Vec<String>> = items.iter().map(|x| scalar_literal(x).map(str::to_owned)).collect();
        let shape_name = if let Some(parts) = detected {
            shape_for(parts, shapes, tokens[i].pos)?
        } else {
            let candidates: Vec<usize> = shapes.iter().enumerate().filter_map(|(idx, s)|
                (s.0.len() == items.len()).then_some(idx)).collect();
            if candidates.len() != 1 {
                return Err(error(tokens[i].pos, "E_UNSUPPORTED_TYPE",
                    "nonliteral scalar tuple expression requires exactly one known Tuple shape of this arity"));
            }
            ctor_name(candidates[0])
        };
        // A source tuple permits '(x,)' and '(x,y,)', but the
        // production class constructor parser requires exactly N arguments.
        // Reconstruct from the checked item slices, omitting trailing
        // tuple-only separators while retaining nested call delimiters.
        let inner = items.iter()
            .map(|item| as_code(item))
            .collect::<R<Vec<_>>>()?
            .join(", ");
        let expression = format!("new {shape_name}({inner})");
        let replacement = synthetic(&expression, tokens[i].pos)?;
        let next = i + replacement.len();
        tokens.splice(i..=close, replacement);
        i = next;
    }
    Ok(())
}

/// Return a fully ordinary compiler token stream for provably Copy-scalar
/// tuple shapes, or fail closed. Evaluation of a function-produced tuple
/// happens exactly once in the root local; scalar projections copy values.
pub fn lower(mut tokens: Vec<Token>) -> R<Vec<Token>> {
    if tokens.iter().any(|t| id(t).is_some_and(|s| s.starts_with(PREFIX))) {
        return Err(error(tokens.first().map_or(Pos::default(), |t| t.pos),
            "E_RESERVED", "internal tuple storage names are reserved"));
    }
    let mut shapes = Vec::new();
    rewrite_types(&mut tokens, &mut shapes)?;
    let functions = tuple_functions(&tokens, &shapes);
    lower_bindings(&mut tokens, &functions, &shapes)?;
    rewrite_literal_tuples(&mut tokens, &mut shapes)?;
    if shapes.is_empty() { return Ok(tokens); }
    let pos = tokens.first().map_or(Pos::default(), |t| t.pos);
    let mut source = String::new();
    for (i, shape) in shapes.iter().enumerate() {
        source.push_str(&create_class(&ctor_name(i), shape));
    }
    let mut prefix = synthetic(&source, pos)?;
    prefix.extend(tokens);
    if prefix.len() > crate::lexer::MAX_TOKENS {
        return Err(error(pos, "E_SOURCE_LIMIT", "tuple lowering exceeds token budget"));
    }
    Ok(prefix)
}
