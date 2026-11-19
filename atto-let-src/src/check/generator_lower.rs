//! First genuinely CFG-driven generator continuation lowering.
//!
//! Unlike the original CountTo special case this uses the parsed, bounded
//! generator control-flow graph and a finite typed symbol table. Every mutable
//! integer that survives a yield owns a persistent slot in the guest arena.
//! There are no implicit heap references, arbitrary calls, or effectful
//! expressions in this profile, so suspension cannot retain a borrow.
//!
//! Declarations must precede control flow, cannot be shadowed, and nested
//! branches/loops may only mutate existing locals. This is intentionally
//! fail-closed until scope-sensitive definite-assignment and borrow checking
//! for richer values have been implemented.

use super::*;
use crate::generator_cfg::{self, Instruction};

mod liveness;

// Live slot bound comes from the shared checker/guest frame ABI.
pub(super) const GENERATOR_TYPED_CFG_LIMIT: usize = 128;

/// Indices in the native guest Wasm next() function, not source-level locals.
/// 0=generator handle, 1..5=runtime scratch, 6=immutable int param.
const PARAM_WASM_SLOT: u32 = 6;
const FIRST_LOCAL_WASM_SLOT: u32 = 7;

#[derive(Clone, Copy)]
struct Binding {
    local: u32,
    mutable: bool,
}

fn blocked(pos: Pos, why: &str) -> Diagnostic {
    Diagnostic::new(pos, "E_UNSUPPORTED", why)
}

fn type_error(pos: Pos, why: &str) -> Diagnostic {
    Diagnostic::new(pos, "E_TYPE", why)
}

fn body_is_pure(body: &[Stmt], allow_binding: bool) -> bool {
    body.iter().all(|stmt| match stmt {
        Stmt::Bind { .. } => allow_binding,
        Stmt::Assign { .. } | Stmt::Yield(..) | Stmt::Return(None, _) |
        Stmt::Break(_) | Stmt::Continue(_) => true,
        Stmt::While { body, .. } | Stmt::Loop { body, .. } |
        Stmt::Block(body) => body_is_pure(body, false),
        Stmt::If { arms, otherwise, .. } =>
            arms.iter().all(|(_, b)| body_is_pure(b, false))
                && otherwise.as_ref().is_none_or(|b| body_is_pure(b, false)),
        _ => false,
    })
}

fn value(expr: &Expr, bindings: &BTreeMap<String, Binding>) -> R<TE> {
    let typed = match &expr.kind {
        ExprKind::Int(Some(v)) if *v <= i64::MAX as u64 =>
            TE { e: TExpr::I64(*v as i64), ty: Type::Int },
        ExprKind::Bool(v) =>
            TE { e: TExpr::Bool(*v), ty: Type::Bool },
        ExprKind::Var(name) => {
            let binding = bindings.get(name).ok_or_else(||
                Diagnostic::new(expr.pos, "E_UNBOUND",
                    format!("uninitialized or unknown generator local '{name}'")))?;
            TE { e: TExpr::Local(binding.local), ty: Type::Int }
        }
        ExprKind::Unary(UnOp::Neg, inner) => {
            if matches!(&inner.kind, ExprKind::Int(None)) {
                TE { e: TExpr::I64(i64::MIN), ty: Type::Int }
            } else {
                let inner = value(inner, bindings)?;
                if inner.ty != Type::Int {
                    return Err(type_error(expr.pos, "unary minus needs int"));
                }
                TE { e: TExpr::Neg(Box::new(inner)), ty: Type::Int }
            }
        }
        ExprKind::Unary(UnOp::Plus, inner) => {
            let v = value(inner, bindings)?;
            if v.ty != Type::Int {
                return Err(type_error(expr.pos, "unary plus needs int"));
            }
            v
        }
        ExprKind::Unary(UnOp::Not, inner) => {
            let inner = value(inner, bindings)?;
            if inner.ty != Type::Bool {
                return Err(type_error(expr.pos, "logical not needs bool"));
            }
            TE { e: TExpr::Not(Box::new(inner)), ty: Type::Bool }
        }
        ExprKind::Binary(op, a, b) => {
            let left = value(a, bindings)?;
            let right = value(b, bindings)?;
            let (operand, result) = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul =>
                    (Type::Int, Type::Int),
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le |
                BinOp::Gt | BinOp::Ge => (Type::Int, Type::Bool),
                BinOp::And | BinOp::Or => (Type::Bool, Type::Bool),
                BinOp::Div => {
                    return Err(blocked(expr.pos,
                        "division in generator continuation is not yet supported"));
                }
            };
            if left.ty != operand || right.ty != operand {
                return Err(type_error(expr.pos,
                    "generator arithmetic/condition operand types do not match"));
            }
            TE {
                e: TExpr::Bin(*op, Box::new(left), Box::new(right)),
                ty: result,
            }
        }
        _ => {
            return Err(blocked(expr.pos,
                "generator expression has effects or captures that cannot cross yield"));
        }
    };
    Ok(typed)
}

/// A complete, typed, bounded continuation plan. None means a non-CFG
/// generator may still be accepted by the original restricted CountTo or
/// lazy-delegation profile. No partially typed plan is returned.
pub(super) fn lower(f: &Func) -> R<Option<TGenerator>> {
    if f.params.len() > 1 || f.params.iter().any(|p| p.ty != Type::Int) {
        return Ok(None);
    }
    if !body_is_pure(&f.body, true) {
        return Ok(None);
    }
    // Declarations must run on every path before conditional control flow,
    // avoiding use-before-init or scope leakage without a full dominator pass.
    let mut finished_bindings = false;
    for stmt in &f.body {
        match stmt {
            Stmt::Bind { .. } if finished_bindings => return Ok(None),
            Stmt::Bind { .. } => {},
            _ => finished_bindings = true,
        }
    }

    let plan = generator_cfg::lower(&f.body)?;
    if plan.instructions.len() > GENERATOR_TYPED_CFG_LIMIT ||
        plan.delegate_slots > 0 {
        return Ok(None);
    }

    let mut bindings = BTreeMap::new();
    if let Some(param) = f.params.first() {
        bindings.insert(param.name.clone(), Binding {
            local: PARAM_WASM_SLOT,
            mutable: false,
        });
    }

    let mut locals = 0_u32;
    let mut steps = Vec::with_capacity(plan.instructions.len());
    for instruction in plan.instructions {
        let step = match instruction {
            Instruction::Evaluate(Stmt::Bind { kind, name, ty, init, pos }) => {
                if ty.is_some_and(|t| t != Type::Int) {
                    return Err(type_error(pos, "generator live locals must have type int"));
                }
                if bindings.contains_key(&name) {
                    return Err(Diagnostic::new(pos, "E_DUPLICATE",
                        format!("generator local '{name}' is already bound")));
                }
                if locals as usize >= GENERATOR_MAX_LIVE_I64_LOCALS {
                    return Err(blocked(pos, "generator exceeds 16 live integer locals"));
                }
                let assigned = value(&init, &bindings)?;
                if assigned.ty != Type::Int {
                    return Err(type_error(pos, "generator local initializer must be int"));
                }
                let local = locals;
                locals += 1;
                bindings.insert(name, Binding {
                    local: FIRST_LOCAL_WASM_SLOT + local,
                    mutable: kind == BindKind::Let,
                });
                TGenStep::Set { local, value: assigned }
            }
            Instruction::Evaluate(Stmt::Assign { name, value: rhs, pos }) => {
                let binding = bindings.get(&name).ok_or_else(||
                    Diagnostic::new(pos, "E_UNBOUND",
                        format!("assignment to unknown generator local '{name}'")))?;
                if !binding.mutable {
                    return Err(Diagnostic::new(pos, "E_IMMUTABLE",
                        format!("generator local '{name}' cannot be reassigned")));
                }
                let rhs = value(&rhs, &bindings)?;
                if rhs.ty != Type::Int {
                    return Err(type_error(pos, "generator assignment requires int"));
                }
                TGenStep::Set {
                    local: binding.local - FIRST_LOCAL_WASM_SLOT,
                    value: rhs,
                }
            }
            Instruction::Guard { condition, on_false } => {
                let cond = value(&condition, &bindings)?;
                if cond.ty != Type::Bool {
                    return Err(type_error(condition.pos,
                        "generator branch/loop condition must be bool"));
                }
                TGenStep::Guard { condition: cond, on_false }
            }
            Instruction::Jump { to } => TGenStep::Jump { to },
            Instruction::Yield { value: yielded } => {
                let value = value(&yielded, &bindings)?;
                if value.ty != Type::Int {
                    return Err(type_error(yielded.pos,
                        "Generator<int> can only yield int values"));
                }
                TGenStep::Yield(value)
            }
            Instruction::Done => TGenStep::Done,
            _ => {
                return Ok(None);
            }
        };
        steps.push(step);
    }

    let live_after = liveness::analyze(f, &steps, locals)?;
    Ok(Some(TGenerator { function: 0, steps, locals, live_after }))
}
