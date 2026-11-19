//! Contextual type checker for noncapturing scalar lambdas.
//! Signature checking only: no closure lowering or callback execution.

use crate::ast::{BinOp, BindKind, Expr, ExprKind, LambdaBody, Stmt, Type, UnOp};
use crate::diag::{Diagnostic, Pos};

type R<T> = Result<T, Diagnostic>;
const LOCAL_LIMIT: usize = 128;
const DEPTH_LIMIT: usize = 128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedLambda {
    pub params: Vec<(String, Type)>,
    pub result: Type,
    pub annotated: bool,
}

/// Infer a lambda signature from contextual argument types, optional expected
/// result, and the lambda AST. Refuses captures, effects and non-scalar types.
/// This is not a Wasm lowering API; compile() must still fail closed.
pub fn check_noncapturing(
    lambda: &Expr, expected_params: Option<&[Type]>, expected_result: Option<Type>
) -> R<CheckedLambda> {
    let (names, annotated, body) = match &lambda.kind {
        ExprKind::Lambda { params, return_type, body } => (params, return_type, body),
        _ => return Err(err(lambda.pos, "E_TYPE", "expected a lambda")),
    };
    let types: &[Type] = match expected_params {
        Some(types) if types.len() == names.len() => types,
        Some(types) => return Err(err(lambda.pos, "E_ARITY", format!(
            "callback expects {} parameters, found {}", types.len(), names.len()))),
        None if names.is_empty() => &[],
        None => return Err(err(lambda.pos, "E_INFER",
            "lambda parameters need contextual callable types")),
    };
    if types.iter().any(|t| !scalar(*t) || *t == Type::Void) {
        return Err(err(lambda.pos, "E_UNSUPPORTED_TYPE", "lambda parameter type is not a scalar value"));
    }
    if expected_result.is_some_and(|t| !scalar(t)) {
        return Err(err(lambda.pos, "E_UNSUPPORTED_TYPE", "lambda result type is not scalar"));
    }
    let ann = annotated.as_deref().map(|s| annotation(s, lambda.pos)).transpose()?;
    if let (Some(a), Some(b)) = (ann, expected_result) {
        if a != b {
            return Err(err(lambda.pos, "E_TYPE", format!(
                "annotated result {} differs from expected {}", a.name(), b.name())));
        }
    }
    let mut ctx = Context {
        frames: vec![vec![]], returns: vec![], count: 0,
        depth: 0, statement_depth: 0,
    };
    for (name, ty) in names.iter().zip(types) {
        ctx.bind(name, *ty, false, lambda.pos)?;
    }
    let complete = match body {
        LambdaBody::Expression(e) => {
            let t = ctx.expression(e)?;
            ctx.returns.push((t, e.pos));
            true
        }
        LambdaBody::Statement(s) => ctx.statement(s)?,
        LambdaBody::Block(stmts) => ctx.statements(stmts)?,
    };
    let inferred = ctx.returns.first().map_or(Type::Void, |x| x.0);
    for &(ty, pos) in &ctx.returns {
        if ty != inferred {
            return Err(err(pos, "E_TYPE", format!(
                "inconsistent lambda returns: {} and {}", inferred.name(), ty.name())));
        }
    }
    let result = ann.or(expected_result).unwrap_or(inferred);
    if result != inferred {
        let code = if ctx.returns.is_empty() { "E_RETURN" } else { "E_TYPE" };
        return Err(err(lambda.pos, code, format!(
            "lambda returns {} but expected {}", inferred.name(), result.name())));
    }
    if result != Type::Void && !complete {
        return Err(err(lambda.pos, "E_RETURN", "not all lambda paths return a value"));
    }
    Ok(CheckedLambda {
        params: names.iter().cloned().zip(types.iter().copied()).collect(),
        result, annotated: ann.is_some(),
    })
}

fn scalar(t: Type) -> bool {
    matches!(t, Type::Int | Type::Bool | Type::Float | Type::Str | Type::Void)
}
fn annotation(s: &str, p: Pos) -> R<Type> {
    match s {
        "int" => Ok(Type::Int), "bool" | "boolean" => Ok(Type::Bool),
        "float" | "f64" => Ok(Type::Float), "string" | "String" => Ok(Type::Str),
        "void" => Ok(Type::Void),
        _ => Err(err(p, "E_UNSUPPORTED_TYPE",
            format!("cannot yet type-check lambda result annotation '{s}'"))),
    }
}
fn err(p: Pos, code: &'static str, why: impl Into<String>) -> Diagnostic {
    Diagnostic::new(p, code, why)
}
#[derive(Clone)]
struct Local { name: String, ty: Type, mutable: bool }
struct Context {
    frames: Vec<Vec<Local>>,
    returns: Vec<(Type, Pos)>,
    count: usize,
    depth: usize,
    statement_depth: usize,
}
impl Context {
    fn bind(&mut self, name: &str, ty: Type, mutable: bool, p: Pos) -> R<()> {
        // Even callers that construct ASTs directly must not bypass the
        // parser's receiver-name restriction.
        if name == "self" {
            return Err(err(p, "E_RESERVED", "'self' cannot be rebound in a lambda"));
        }
        let frame = self.frames.last_mut().unwrap();
        if frame.iter().any(|l| l.name == name) {
            return Err(err(p, "E_DUPLICATE", format!("duplicate lambda name '{name}'")));
        }
        if self.count >= LOCAL_LIMIT {
            return Err(err(p, "E_SOURCE_LIMIT", "too many lambda locals"));
        }
        self.count += 1;
        frame.push(Local { name: name.into(), ty, mutable });
        Ok(())
    }
    fn lookup(&self, name: &str) -> Option<&Local> {
        self.frames.iter().rev().flat_map(|f| f.iter().rev()).find(|l| l.name == name)
    }
    fn scope(&mut self, body: &[Stmt]) -> R<bool> {
        self.frames.push(Vec::new());
        let r = self.statements(body);
        self.frames.pop();
        r
    }
    fn statements(&mut self, body: &[Stmt]) -> R<bool> {
        let mut complete = false;
        for s in body {
            // Do not silently skip invalid return types, captures, or
            // unsupported effects hidden in unreachable tail statements.
            if complete {
                return Err(err(position(s), "E_UNREACHABLE",
                    "lambda has a statement after an unconditional return"));
            }
            complete = self.statement(s)?;
        }
        Ok(complete)
    }
    fn statement(&mut self, s: &Stmt) -> R<bool> {
        if self.statement_depth >= DEPTH_LIMIT {
            return Err(err(position(s), "E_NESTING",
                "lambda statement nesting limit exceeded"));
        }
        self.statement_depth += 1;
        let checked = self.statement_inner(s);
        self.statement_depth -= 1;
        checked
    }
    fn statement_inner(&mut self, s: &Stmt) -> R<bool> {
        match s {
            Stmt::Return(v, p) => {
                let ty = v.as_ref().map_or(Ok(Type::Void), |e| self.expression(e))?;
                self.returns.push((ty, *p));
                Ok(true)
            }
            Stmt::Bind { kind, name, ty, init, pos } => {
                if *kind == BindKind::Const && !matches!(init.kind,
                    ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Float(_) | ExprKind::Str(_)) {
                    return Err(err(*pos, "E_CONST", "const lambda local needs literal initializer"));
                }
                let got = self.expression(init)?;
                if let Some(want) = ty {
                    if !scalar(*want) || *want == Type::Void {
                        return Err(err(*pos, "E_UNSUPPORTED_TYPE", "unsupported lambda local type"));
                    }
                    if *want != got {
                        return Err(err(init.pos, "E_TYPE", "lambda local initializer type mismatch"));
                    }
                }
                if got == Type::Void {
                    return Err(err(init.pos, "E_TYPE", "void cannot initialize a lambda local"));
                }
                self.bind(name, got, *kind == BindKind::Let, *pos)?;
                Ok(false)
            }
            Stmt::Assign { name, value, pos } => {
                let l = self.lookup(name).ok_or_else(||
                    err(*pos, "E_CAPTURE", format!("noncapturing lambda cannot write '{name}'")))?;
                let (ty, mutable) = (l.ty, l.mutable);
                if !mutable { return Err(err(*pos, "E_IMMUTABLE", "lambda local is immutable")); }
                if self.expression(value)? != ty {
                    return Err(err(value.pos, "E_TYPE", "lambda local assignment type mismatch"));
                }
                Ok(false)
            }
            Stmt::Expr(e) => { self.expression(e)?; Ok(false) }
            Stmt::Block(b) => self.scope(b),
            Stmt::If { arms, otherwise, pos } => {
                if arms.is_empty() { return Err(err(*pos, "E_SYNTAX", "empty lambda if")); }
                let mut complete = true;
                for (cond, body) in arms {
                    if self.expression(cond)? != Type::Bool {
                        return Err(err(cond.pos, "E_TYPE", "lambda condition must be bool"));
                    }
                    complete &= self.scope(body)?;
                }
                complete &= match otherwise {
                    Some(body) => self.scope(body)?, None => false,
                };
                Ok(complete)
            }
            _ => Err(err(position(s), "E_UNSUPPORTED",
                "lambda statement requires unsupported effect or control flow")),
        }
    }
    fn expression(&mut self, e: &Expr) -> R<Type> {
        if self.depth >= DEPTH_LIMIT {
            return Err(err(e.pos, "E_NESTING", "lambda type-check nesting limit"));
        }
        self.depth += 1;
        let r = self.expression_inner(e);
        self.depth -= 1;
        r
    }
    fn expression_inner(&mut self, e: &Expr) -> R<Type> {
        match &e.kind {
            ExprKind::Int(Some(v)) if *v <= i64::MAX as u64 => Ok(Type::Int),
            ExprKind::Int(_) => Err(err(e.pos, "E_INTEGER_RANGE", "int exceeds signed 64-bit range")),
            ExprKind::Bool(_) => Ok(Type::Bool), ExprKind::Float(_) => Ok(Type::Float),
            ExprKind::Str(_) => Ok(Type::Str),
            ExprKind::Var(name) => self.lookup(name).map(|l| l.ty).ok_or_else(||
                err(e.pos, "E_CAPTURE", format!(
                    "noncapturing lambda cannot read outer or unbound name '{name}'"))),
            ExprKind::Unary(op, inner) => {
                if *op == UnOp::Neg && matches!(inner.kind, ExprKind::Int(None)) {
                    return Ok(Type::Int);
                }
                let ty = self.expression(inner)?;
                match op {
                    UnOp::Neg | UnOp::Plus if matches!(ty, Type::Int | Type::Float) => Ok(ty),
                    UnOp::Not if ty == Type::Bool => Ok(Type::Bool),
                    _ => Err(err(e.pos, "E_TYPE", "invalid lambda unary operand")),
                }
            }
            ExprKind::Binary(op, a, b) => {
                let left = self.expression(a)?;
                let right = self.expression(b)?;
                let num = |t| matches!(t, Type::Int | Type::Float);
                match op {
                    BinOp::Add if left == Type::Str && right == Type::Str => Ok(Type::Str),
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div
                        if num(left) && num(right) => {
                        if *op == BinOp::Div && left == Type::Int && right == Type::Int {
                            Err(err(e.pos, "E_UNSUPPORTED", "int / int semantics unresolved"))
                        } else if left == Type::Float || right == Type::Float {
                            Ok(Type::Float)
                        } else {
                            Ok(Type::Int)
                        }
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                        if (num(left) && num(right))
                            || (left == Type::Str && right == Type::Str) => Ok(Type::Bool),
                    BinOp::Eq | BinOp::Ne if left == right => Ok(Type::Bool),
                    BinOp::And | BinOp::Or
                        if left == Type::Bool && right == Type::Bool => Ok(Type::Bool),
                    _ => Err(err(e.pos, "E_TYPE", format!(
                        "operator '{}' cannot combine {} and {}",
                        op.symbol(), left.name(), right.name()))),
                }
            }
            ExprKind::Ternary(cond, yes, no) => {
                if self.expression(cond)? != Type::Bool {
                    return Err(err(cond.pos, "E_TYPE", "lambda ternary condition must be bool"));
                }
                let a = self.expression(yes)?;
                let b = self.expression(no)?;
                if a != b {
                    return Err(err(e.pos, "E_TYPE", "lambda ternary branches differ in type"));
                }
                Ok(a)
            }
            ExprKind::SelfRef => Err(err(e.pos, "E_CAPTURE", "noncapturing lambda cannot access self")),
            _ => Err(err(e.pos, "E_UNSUPPORTED",
                "lambda expression needs unsupported effect, capture or callable lowering")),
        }
    }
}
fn position(stmt: &Stmt) -> Pos {
    match stmt {
        Stmt::Bind { pos, .. } | Stmt::Assign { pos, .. } |
        Stmt::FieldAssign { pos, .. } | Stmt::StateWrite { pos, .. } | Stmt::If { pos, .. } |
        Stmt::While { pos, .. } | Stmt::Loop { pos, .. } |
        Stmt::For { pos, .. } | Stmt::ForIn { pos, .. } |
        Stmt::Match { pos, .. } | Stmt::Throw(_, pos) |
        Stmt::Raise(_, pos) | Stmt::Try { pos, .. } | Stmt::Defer { pos, .. } | Stmt::Recover { pos, .. } |
        Stmt::Yield(_, pos) | Stmt::YieldFrom(_, pos) |
        Stmt::Return(_, pos) | Stmt::Break(pos) | Stmt::Continue(pos) => *pos,
        Stmt::Expr(e) => e.pos,
        Stmt::Block(body) => body.first().map_or(Pos::default(), position),
    }
}
