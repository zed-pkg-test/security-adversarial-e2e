//! Conservative direct-call lowering of bounded, immutable scalar-capturing lambdas.
//!
//! One immutable local lambda per source function is supported. Direct calls
//! become named private Wasm function calls with frozen scalar capture parameters.
//! Callable values, escaping closures, mutable captures and indirect tables
//! remain unsupported.
use crate::ast::*;
use crate::diag::{Diagnostic, Pos};
use super::callable_ir::{CallableSignature, CallableTarget, TypedCallable};
use std::collections::{BTreeMap, BTreeSet};
type R<T> = Result<T, Diagnostic>;

#[derive(Clone)]
struct Capture { source: String, snapshot: String, ty: Type }

struct Direct {
    source: String,
    hidden: String,
    lambda: Expr,
    params: Vec<String>,
    inferred: Option<Vec<Type>>,
    captures: Vec<Capture>,
    calls: usize,
    expression_depth: usize,
    statement_depth: usize,
}
const MAX_REWRITE_DEPTH: usize = 128;
fn error(p: Pos, code: &'static str, m: impl Into<String>) -> Diagnostic {
    Diagnostic::new(p, code, m)
}
fn literal_type(e: &Expr) -> Option<Type> {
    match &e.kind {
        ExprKind::Int(_) => Some(Type::Int),
        ExprKind::Bool(_) => Some(Type::Bool),
        ExprKind::Float(_) => Some(Type::Float),
        ExprKind::Str(_) => Some(Type::Str),
        ExprKind::Unary(UnOp::Plus | UnOp::Neg, inner) if
            matches!(inner.kind, ExprKind::Int(_) | ExprKind::Float(_)) => literal_type(inner),
        _ => None,
    }
}
pub fn lower(input: &Program) -> R<Program> {
    let mut program = input.clone();
    let mut generated = Vec::new();
    for (idx, f) in program.funcs.iter_mut().enumerate() {
        if f.is_generator { continue; }
        let mut direct: Option<Direct> = None;
        // Keep the top-level lexical binding ledger before desugaring removes
        // the lambda declaration. The ordinary checker would otherwise miss
        // an earlier same-scope declaration with the identical name.
        let mut bindings_before_lambda = BTreeSet::<String>::new();
        // Immutable scalar parameters are stable capture sources. A val
        // initialized from one of these parameters is also an immutable
        // snapshot (unlike a let alias, mutable parameter or owned object).
        // Keep this deliberately narrower than general closure capture:
        // no reference/heap handle or mutable value may escape the frame.
        let mut scalar_immutables = f.params.iter()
            .filter(|p| !p.mutable && matches!(p.ty, Type::Int | Type::Bool | Type::Float))
            .map(|p| (p.name.clone(), p.ty))
            .collect::<BTreeMap<String, Type>>();
        let mut body = Vec::new();
        for mut stmt in std::mem::take(&mut f.body) {
            if let Stmt::Bind { kind, name, ty, init, pos } = &stmt {
                if let ExprKind::Lambda { params, .. } = &init.kind {
                    if direct.is_some() {
                        return Err(error(*pos, "E_UNSUPPORTED",
                            "at most one direct lambda per function is supported"));
                    }
                    if let Some(t @ Type::Callable(_)) = ty {
                        // Even though callable storage is not executable,
                        // a typed lambda binding provides a complete
                        // contextual signature: check its body and captures
                        // before the explicit runtime capability gate.
                        let want = CallableSignature::from_source_type(
                            *t, &input.type_names, *pos)?;
                        let _typed = CallableSignature::from_noncapturing(
                            init, Some(&want.params), Some(want.result))?;
                        return Err(error(*pos, "E_UNSUPPORTED",
                            "typed callable values require verified Wasm indirect dispatch"));
                    }
                    if *kind != BindKind::Val || ty.is_some() {
                        return Err(error(*pos, "E_UNSUPPORTED",
                            "direct lambdas need an unannotated immutable val binding"));
                    }
                    if bindings_before_lambda.contains(name) {
                        return Err(error(*pos, "E_DUPLICATE",
                            "direct lambda duplicates an existing local binding"));
                    }
                    if f.params.iter().any(|p| p.name == *name) {
                        return Err(error(*pos, "E_DUPLICATE",
                            "lambda name duplicates a function parameter"));
                    }
                    if generated.len() >= 64 {
                        return Err(error(*pos, "E_SOURCE_LIMIT", "too many direct lambdas"));
                    }
                    // The private name is reserved by source grammar but a
                    // checker caller may construct a Program directly. Reject
                    // collisions instead of letting a forged declaration
                    // impersonate the compiled callback.
                    let hidden = format!("$lambda_{}", idx);
                    if input.funcs.iter().any(|f| f.name == hidden)
                        || input.classes.iter().any(|c| c.name == hidden)
                        || input.enums.iter().any(|e| e.name == hidden)
                        || input.actors.iter().any(|a| a.name == hidden) {
                        return Err(error(*pos, "E_DUPLICATE",
                            "compiler-generated lambda name collides with a declaration"));
                    }
                    let mut free = BTreeSet::new();
                    if let ExprKind::Lambda { body: LambdaBody::Expression(expression), .. } = &init.kind {
                        free_names(expression, &mut free, 0)?;
                    }
                    for p in params { free.remove(p); }
                    let mut captures = Vec::new();
                    for candidate in free {
                        if let Some(&ty) = scalar_immutables.get(&candidate) {
                            if captures.len() == 8 || params.len() + captures.len() >= crate::parser::MAX_PARAMS {
                                return Err(error(*pos, "E_SOURCE_LIMIT",
                                    "direct scalar lambda capture budget exceeded"));
                            }
                            captures.push(Capture {
                                source: candidate,
                                snapshot: format!("$capture_{}_{}", idx, captures.len()),
                                ty,
                            });
                        }
                    }
                    // Snapshot at the lexical definition point, not at a call
                    // inside a shadowing block. Values are immutable scalars.
                    for c in &captures {
                        body.push(Stmt::Bind {
                            kind: BindKind::Val, name: c.snapshot.clone(),
                            ty: Some(c.ty),
                            init: Expr { kind: ExprKind::Var(c.source.clone()), pos: *pos },
                            pos: *pos,
                        });
                    }
                    direct = Some(Direct {
                        source: name.clone(),
                        hidden,
                        lambda: init.clone(),
                        params: params.clone(), inferred: None, captures, calls: 0,
                        expression_depth: 0, statement_depth: 0,
                    });
                    continue;
                }
            }
            if let Some(d) = &mut direct { rewrite_stmt(&mut stmt, d)?; }
            if let Stmt::Bind { kind, name, init, .. } = &stmt {
                bindings_before_lambda.insert(name.clone());
                if *kind == BindKind::Val {
                    // A copied immutable scalar remains immutable even when
                    // its initializer is a parameter rather than a literal.
                    // Record only verified source types, never guessed types
                    // for calls, heap objects, mutable locals or ownership ops.
                    let scalar_ty = literal_type(init).or_else(|| match &init.kind {
                        ExprKind::Var(source) => scalar_immutables.get(source).copied(),
                        _ => None,
                    });
                    if let Some(ty @ (Type::Int | Type::Bool | Type::Float)) = scalar_ty {
                        scalar_immutables.insert(name.clone(), ty);
                    }
                }
            }
            body.push(stmt);
        }
        if let Some(d) = direct {
            if d.calls == 0 {
                return Err(error(d.lambda.pos, "E_UNSUPPORTED",
                    "unused lambdas are not executable; first-class callables remain unsupported"));
            }
            let types = d.inferred.ok_or_else(|| error(d.lambda.pos, "E_INFER",
                "lambda parameter types need a direct invocation"))?;
            let mut lifted = d.lambda.clone();
            let mut all_types = types.clone();
            if let ExprKind::Lambda { params, .. } = &mut lifted.kind {
                for c in &d.captures {
                    params.push(c.source.clone());
                    all_types.push(c.ty);
                }
            }
            let signature = CallableSignature::from_noncapturing(&lifted, Some(&all_types), None)?;
            let callable = TypedCallable::checked(
                signature,
                CallableTarget::Direct {
                    function_index: (input.funcs.len() + generated.len()) as u32,
                },
                d.lambda.pos,
            )?;
            callable.check_arguments(&all_types, d.lambda.pos)?;
            let inner = match d.lambda.kind {
                ExprKind::Lambda { body, .. } => body,
                _ => unreachable!(),
            };
            let lambda_body = match inner {
                LambdaBody::Expression(e) => {
                    let p = e.pos;
                    vec![Stmt::Return(Some(*e), p)]
                }
                LambdaBody::Statement(s) => vec![*s],
                LambdaBody::Block(b) => b,
            };
            generated.push(Func {
                name: d.hidden,
                pos: d.lambda.pos,
                is_generator: false,
                is_pure: true,
                declared_effects: None,
                params: d.params.into_iter().chain(
                    d.captures.into_iter().map(|c| c.source)
                ).zip(all_types).map(|(name, ty)| Param {
                    name, ty, mutable: false, pos: d.lambda.pos,
                }).collect(),
                ret: callable.signature().result,
                body: lambda_body,
            });
        }
        f.body = body;
    }
    if program.funcs.len().saturating_add(generated.len()) > crate::parser::MAX_FUNCS {
        return Err(error(Pos { line: 1, col: 1 }, "E_SOURCE_LIMIT",
            "compiled lambdas exceed the module function budget"));
    }
    program.funcs.extend(generated);
    Ok(program)
}
fn rewrite_statements(body: &mut [Stmt], d: &mut Direct) -> R<()> {
    for stmt in body { rewrite_stmt(stmt, d)?; }
    Ok(())
}
fn rewrite_stmt(s: &mut Stmt, d: &mut Direct) -> R<()> {
    if d.statement_depth >= MAX_REWRITE_DEPTH {
        return Err(error(stmt_pos(s), "E_NESTING",
            "direct lambda statement rewrite nesting limit exceeded"));
    }
    d.statement_depth += 1;
    let result = rewrite_stmt_inner(s, d);
    d.statement_depth -= 1;
    result
}
fn rewrite_stmt_inner(s: &mut Stmt, d: &mut Direct) -> R<()> {
    match s {
        Stmt::Bind { name, init, pos, .. } => {
            if *name == d.source {
                return Err(error(*pos, "E_UNSUPPORTED",
                    "shadowing direct lambda is unsupported"));
            }
            rewrite_expr(init, d)
        }
        Stmt::Assign { name, value, pos } => {
            if *name == d.source {
                return Err(error(*pos, "E_IMMUTABLE",
                    "direct lambda cannot be reassigned"));
            }
            rewrite_expr(value, d)
        }
        Stmt::FieldAssign { target, value, .. } => {
            rewrite_expr(target, d)?;
            rewrite_expr(value, d)
        }
        Stmt::StateWrite { pos, .. } => Err(error(*pos, "E_UNSUPPORTED",
            "direct lambda rewriting cannot cross a protected state loan")),
        Stmt::Expr(e) | Stmt::Throw(e, _) | Stmt::Raise(e, _) | Stmt::Yield(e, _) | Stmt::YieldFrom(e, _) =>
            rewrite_expr(e, d),
        Stmt::Try { body, catch, finally, .. } => {
            rewrite_statements(body, d)?;
            if let Some((_, handler)) = catch { rewrite_statements(handler, d)?; }
            if let Some(cleanup) = finally { rewrite_statements(cleanup, d)?; }
            Ok(())
        }
        // Cleanup/recovery bodies are checked in an isolated scope, but
        // their factory argument expressions execute at registration and must
        // undergo the same checked direct-call rewriting as ordinary calls.
        Stmt::Defer { args, .. } => {
            for arg in args { rewrite_expr(arg, d)?; }
            Ok(())
        },
        Stmt::Recover { args, .. } => {
            for arg in args { rewrite_expr(arg, d)?; }
            Ok(())
        }
        Stmt::Return(Some(e), _) => rewrite_expr(e, d),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => Ok(()),
        Stmt::Block(b) | Stmt::Loop { body: b, .. } => rewrite_statements(b, d),
        Stmt::While { cond, body, .. } => {
            rewrite_expr(cond, d)?;
            rewrite_statements(body, d)
        }
        Stmt::If { arms, otherwise, .. } => {
            for (cond, body) in arms {
                rewrite_expr(cond, d)?;
                rewrite_statements(body, d)?;
            }
            if let Some(other) = otherwise { rewrite_statements(other, d)?; }
            Ok(())
        }
        Stmt::For { init, cond, update, body, .. } => {
            if let Some(x) = init { rewrite_stmt(x, d)?; }
            if let Some(x) = cond { rewrite_expr(x, d)?; }
            if let Some(x) = update { rewrite_stmt(x, d)?; }
            rewrite_statements(body, d)
        }
        Stmt::ForIn { name, source, body, pos } => {
            if *name == d.source {
                return Err(error(*pos, "E_UNSUPPORTED",
                    "for-in may not shadow direct lambda"));
            }
            rewrite_expr(source, d)?;
            rewrite_statements(body, d)
        }
        Stmt::Match { subject, arms, .. } => {
            rewrite_expr(subject, d)?;
            for arm in arms {
                let bound = match &arm.pattern {
                    Pattern::Bind(n) | Pattern::Adt(_, Some(n)) => Some(n),
                    _ => None,
                };
                if bound.is_some_and(|n| *n == d.source) {
                    return Err(error(arm.pos, "E_UNSUPPORTED",
                        "match arm cannot shadow direct lambda"));
                }
                if let Some(guard) = &mut arm.guard { rewrite_expr(guard, d)?; }
                rewrite_statements(&mut arm.body, d)?;
            }
            Ok(())
        }
    }
}
fn rewrite_expr(e: &mut Expr, d: &mut Direct) -> R<()> {
    if d.expression_depth >= MAX_REWRITE_DEPTH {
        return Err(error(e.pos, "E_NESTING",
            "direct lambda expression rewrite nesting limit exceeded"));
    }
    d.expression_depth += 1;
    let result = rewrite_expr_inner(e, d);
    d.expression_depth -= 1;
    result
}
fn rewrite_expr_inner(e: &mut Expr, d: &mut Direct) -> R<()> {
    match &mut e.kind {
        ExprKind::Var(n) if *n == d.source =>
            Err(error(e.pos, "E_UNSUPPORTED",
                "direct lambda cannot escape as a first-class value")),
        ExprKind::Call(name, args) => {
            for a in args.iter_mut() { rewrite_expr(a, d)?; }
            if *name == d.source {
                if args.len() != d.params.len() {
                    return Err(error(e.pos, "E_ARITY", format!(
                        "lambda expects {} arguments, got {}",
                        d.params.len(), args.len())));
                }
                if d.inferred.is_none() {
                    let types = args.iter().map(literal_type).collect::<Option<Vec<_>>>()
                        .ok_or_else(|| error(e.pos, "E_INFER",
                            "first direct call must have scalar literal arguments"))?;
                    d.inferred = Some(types);
                }
                *name = d.hidden.clone();
                // Every call uses the definition-site snapshot, even if
                // the source name is shadowed in the caller's nested block.
                args.extend(d.captures.iter().map(|c| Expr {
                    kind: ExprKind::Var(c.snapshot.clone()), pos: e.pos,
                }));
                d.calls += 1;
            }
            Ok(())
        }
        // Ownership wrappers may contain a direct lambda call or a value
        // escape. Traverse their operand before the ordinary ownership checker
        // validates move/borrow/copy semantics.
        ExprKind::Ownership(_, _, x) | ExprKind::Unary(_, x) |
        ExprKind::Trap(x) | ExprKind::Propagate(x) => rewrite_expr(x, d),
        ExprKind::Binary(_, x, y) => {
            rewrite_expr(x, d)?;
            rewrite_expr(y, d)
        }
        ExprKind::Ternary(c, x, y) => {
            rewrite_expr(c, d)?;
            rewrite_expr(x, d)?;
            rewrite_expr(y, d)
        }
        ExprKind::Member(x, _) => rewrite_expr(x, d),
        ExprKind::MethodCall(x, _, args) => {
            rewrite_expr(x, d)?;
            for a in args { rewrite_expr(a, d)?; }
            Ok(())
        }
        ExprKind::Array(args) | ExprKind::New(_, args) => {
            // Constructor arguments are genuine call arguments. Omitting
            // them lets a direct lambda call bypass lexical snapshot rewriting
            // (or silently resolve to a same-named top-level function).
            for a in args { rewrite_expr(a, d)?; }
            Ok(())
        }
        ExprKind::Lambda { .. } => Err(error(e.pos, "E_UNSUPPORTED",
            "nested or escaping lambda needs closure lowering")),
        ExprKind::StateRead(_) => Err(error(e.pos, "E_UNSUPPORTED",
            "protected state projections require a lexical state lease, not direct closure lowering")),
        // Exhaustive AST traversal: introducing a new expression kind must
        // require a compiler review of its lexical binding behaviour.
        ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Bool(_) |
        ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::SelfRef |
        ExprKind::Spawn(_) => Ok(()),
    }
}

// Collect only simple expression-body free variables. Other lambda bodies
// remain under the existing no-capture/effect checker until scoped capture
// analysis and lifetime lowering are implemented.
fn free_names(e: &Expr, names: &mut BTreeSet<String>, depth: usize) -> R<()> {
    if depth >= MAX_REWRITE_DEPTH {
        return Err(error(e.pos, "E_NESTING", "lambda capture walk limit exceeded"));
    }
    match &e.kind {
        ExprKind::Var(name) => { names.insert(name.clone()); }
        ExprKind::Unary(_, a) => free_names(a, names, depth + 1)?,
        ExprKind::Binary(_, a, b) => {
            free_names(a, names, depth + 1)?;
            free_names(b, names, depth + 1)?;
        }
        ExprKind::Ternary(c, a, b) => {
            free_names(c, names, depth + 1)?;
            free_names(a, names, depth + 1)?;
            free_names(b, names, depth + 1)?;
        }
        // Keep this match exhaustive. Newly introduced AST expression forms
        // must be reviewed here before direct closure conversion is enabled;
        // otherwise a missed free-variable use could escape capture analysis.
        ExprKind::Int(_) | ExprKind::Float(_) |
        ExprKind::Bool(_) | ExprKind::Str(_) => {},
        ExprKind::Trap(a) | ExprKind::Propagate(a) | ExprKind::Member(a, _) =>
            free_names(a, names, depth + 1)?,
        ExprKind::Call(_, args) | ExprKind::New(_, args) |
        ExprKind::Array(args) => {
            for arg in args { free_names(arg, names, depth + 1)?; }
        }
        ExprKind::MethodCall(recv, _, args) => {
            free_names(recv, names, depth + 1)?;
            for arg in args { free_names(arg, names, depth + 1)?; }
        }
        // A receiver and a nested lambda are outside the direct-call scalar
        // capture profile. The noncapturing typechecker retains the precise
        // E_CAPTURE/E_UNSUPPORTED failure classification for these forms.
        // Capturing or moving ownership through a generated lambda requires
        // a verified lifetime/effect model. Refuse rather than accidentally
        // skipping an owned free variable during closure conversion.
        ExprKind::Ownership(_, _, _) => return Err(error(e.pos, "E_UNSUPPORTED",
            "explicit ownership inside a direct lambda requires verified capture lifetimes")),
        ExprKind::StateRead(_) => return Err(error(e.pos, "E_UNSUPPORTED",
            "protected state projection inside a direct lambda is not lifetime-verified")),
        ExprKind::SelfRef | ExprKind::Spawn(_) | ExprKind::Lambda { .. } => {},
    }
    Ok(())
}

fn stmt_pos(s: &Stmt) -> Pos {
    match s {
        Stmt::Bind { pos, .. } | Stmt::Assign { pos, .. } |
        Stmt::FieldAssign { pos, .. } | Stmt::StateWrite { pos, .. } | Stmt::If { pos, .. } |
        Stmt::While { pos, .. } | Stmt::Loop { pos, .. } |
        Stmt::For { pos, .. } | Stmt::ForIn { pos, .. } |
        Stmt::Match { pos, .. } | Stmt::Throw(_, pos) |
        Stmt::Raise(_, pos) | Stmt::Try { pos, .. } | Stmt::Defer { pos, .. } | Stmt::Recover { pos, .. } |
        Stmt::Yield(_, pos) | Stmt::YieldFrom(_, pos) |
        Stmt::Return(_, pos) | Stmt::Break(pos) |
        Stmt::Continue(pos) => *pos,
        Stmt::Block(body) => body.first().map_or(Pos { line: 1, col: 1 }, stmt_pos),
        Stmt::Expr(e) => e.pos,
    }
}
