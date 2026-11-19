//! Bounded generator control-flow lowering.
//!
//! Converts a parsed synchronous generator body into explicit resumable steps.
//! This CFG feeds the typed integer-local continuation lowering and native
//! guest-Wasm resume functions for a strictly admitted subset. Unsupported
//! expressions, bindings, and effects remain fail-closed.
//!
//! Each instruction index is a stable resume PC:
//! - Yield stores the next PC (pc + 1) and returns one item.
//! - Delegate retains its current PC and a unique delegate slot while the
//!   child iterator is active; only child DONE advances the outer PC.
//! - All normal exit paths reach Done, where the eventual runtime must close
//!   any live delegated iterators exactly once.
//!
//! The CFG is deliberately explicit so compiled runtime cannot equate
//! 'yield*' with eagerly collecting or executing a child generator.

use crate::ast::{Expr, Stmt};
use crate::diag::{Diagnostic, Pos};

/// Upper bound on static resume instructions for a single generator function.
/// Runtime iteration counts remain independently bounded by cooperative
/// scheduler budgets; this cap prevents oversized compile-time switch tables.
pub const MAX_GENERATOR_INSTRUCTIONS: usize = 4096;
pub const MAX_GENERATOR_NESTING: u32 = 128;

#[derive(Clone, Debug)]
pub enum Instruction {
    /// A non-suspending source statement. Typed lowering must turn this into
    /// checked assignments and expressions before it is executable.
    Evaluate(Stmt),
    /// If the condition is false, jump to the indexed instruction;
    /// otherwise continue at the next instruction.
    Guard { condition: Expr, on_false: u32 },
    Jump { to: u32 },
    /// Emit exactly one element, then resume at the next instruction.
    Yield { value: Expr },
    /// Resume this same PC until the delegated generator is exhausted.
    /// A dedicated frame slot retains the child handle across outer pulls.
    Delegate { source: Expr, slot: u32 },
    /// Terminal state (also the target for a bare return).
    Done,
}

#[derive(Clone, Debug)]
pub struct GeneratorPlan {
    pub instructions: Vec<Instruction>,
    /// Number of distinct child-handle slots required by yield* expressions.
    pub delegate_slots: u32,
    pub yields: u32,
}

#[derive(Default)]
struct LoopEdges {
    breaks: Vec<usize>,
    continues: Vec<usize>,
}

#[derive(Default)]
struct Builder {
    instructions: Vec<Instruction>,
    loops: Vec<LoopEdges>,
    delegate_slots: u32,
    yields: u32,
    depth: u32,
}

impl Builder {
    fn pc(&self) -> u32 {
        self.instructions.len() as u32
    }

    fn push(&mut self, ins: Instruction, pos: Pos) -> Result<usize, Diagnostic> {
        if self.instructions.len() >= MAX_GENERATOR_INSTRUCTIONS {
            return Err(Diagnostic::new(pos, "E_SOURCE_LIMIT",
                "generator resume CFG exceeds 4096 instructions"));
        }
        let n = self.instructions.len();
        self.instructions.push(ins);
        Ok(n)
    }

    fn jump(&mut self, pos: Pos) -> Result<usize, Diagnostic> {
        self.push(Instruction::Jump { to: 0 }, pos)
    }

    fn patch_jump(&mut self, index: usize, to: u32) {
        match &mut self.instructions[index] {
            Instruction::Jump { to: destination } => *destination = to,
            _ => unreachable!("only a jump may be patched as a jump"),
        }
    }

    fn patch_guard(&mut self, index: usize, to: u32) {
        match &mut self.instructions[index] {
            Instruction::Guard { on_false, .. } => *on_false = to,
            _ => unreachable!("only a guard may be patched as a guard"),
        }
    }

    fn nested(&mut self, body: &[Stmt], pos: Pos) -> Result<(), Diagnostic> {
        if self.depth >= MAX_GENERATOR_NESTING {
            return Err(Diagnostic::new(pos, "E_NESTING",
                "generator control-flow nesting exceeds 128 levels"));
        }
        self.depth += 1;
        let result = self.stmts(body);
        self.depth -= 1;
        result
    }

    fn loop_body(&mut self, cond: Option<&Expr>, body: &[Stmt],
                 update: Option<&Stmt>, pos: Pos) -> Result<(), Diagnostic> {
        let head = self.pc();
        let guard = if let Some(c) = cond {
            Some(self.push(Instruction::Guard {
                condition: c.clone(), on_false: 0,
            }, c.pos)?)
        } else {
            None
        };

        self.loops.push(LoopEdges::default());
        self.nested(body, pos)?;
        let continue_target = self.pc();
        if let Some(update) = update {
            self.stmt(update)?;
        }
        self.push(Instruction::Jump { to: head }, pos)?;
        let exit = self.pc();

        if let Some(guard) = guard {
            self.patch_guard(guard, exit);
        }
        let edges = self.loops.pop().expect("matching loop");
        for site in edges.breaks {
            self.patch_jump(site, exit);
        }
        for site in edges.continues {
            self.patch_jump(site, continue_target);
        }
        Ok(())
    }

    fn stmt(&mut self, stmt: &Stmt) -> Result<(), Diagnostic> {
        match stmt {
            Stmt::Bind { pos, .. } | Stmt::Assign { pos, .. } => {
                self.push(Instruction::Evaluate(stmt.clone()), *pos)?;
            }
            Stmt::Raise(_, pos) | Stmt::Try { pos, .. } | Stmt::Defer { pos, .. } | Stmt::Recover { pos, .. } => {
                return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                    "try/defer/recover/raise inside generators need continuation-owned unwind frames"));
            }
            Stmt::FieldAssign { pos, .. } | Stmt::StateWrite { pos, .. } => {
                return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                    "generator mutation and state loans require an owned frame and borrow analysis"));
            }
            Stmt::Expr(expr) => {
                self.push(Instruction::Evaluate(stmt.clone()), expr.pos)?;
            }
            Stmt::Yield(value, pos) => {
                self.push(Instruction::Yield { value: value.clone() }, *pos)?;
                self.yields += 1;
            }
            Stmt::YieldFrom(source, pos) => {
                let slot = self.delegate_slots;
                self.delegate_slots = self.delegate_slots.checked_add(1).ok_or_else(||
                    Diagnostic::new(*pos, "E_SOURCE_LIMIT", "too many generator delegates"))?;
                self.push(Instruction::Delegate { source: source.clone(), slot }, *pos)?;
            }
            Stmt::Return(None, pos) => {
                self.push(Instruction::Done, *pos)?;
            }
            Stmt::Return(Some(_), pos) => {
                return Err(Diagnostic::new(*pos, "E_RETURN",
                    "generators may only use a bare return"));
            }
            Stmt::If { arms, otherwise, pos } => {
                let mut ends = Vec::new();
                for (cond, arm) in arms {
                    let test = self.push(Instruction::Guard {
                        condition: cond.clone(), on_false: 0,
                    }, cond.pos)?;
                    self.nested(arm, *pos)?;
                    ends.push(self.jump(*pos)?);
                    let next_arm = self.pc();
                    self.patch_guard(test, next_arm);
                }
                if let Some(other) = otherwise {
                    self.nested(other, *pos)?;
                }
                let end = self.pc();
                for jump in ends {
                    self.patch_jump(jump, end);
                }
            }
            Stmt::While { cond, body, pos } => {
                self.loop_body(Some(cond), body, None, *pos)?;
            }
            Stmt::Loop { body, pos } => {
                self.loop_body(None, body, None, *pos)?;
            }
            Stmt::For { init, cond, update, body, pos } => {
                if let Some(init) = init {
                    self.stmt(init)?;
                }
                self.loop_body(cond.as_ref(), body, update.as_deref(), *pos)?;
            }
            Stmt::Break(pos) => {
                if self.loops.is_empty() {
                    return Err(Diagnostic::new(*pos, "E_LOOP",
                        "break outside generator loop"));
                }
                let site = self.jump(*pos)?;
                self.loops.last_mut().unwrap().breaks.push(site);
            }
            Stmt::Continue(pos) => {
                if self.loops.is_empty() {
                    return Err(Diagnostic::new(*pos, "E_LOOP",
                        "continue outside generator loop"));
                }
                let site = self.jump(*pos)?;
                self.loops.last_mut().unwrap().continues.push(site);
            }
            Stmt::Block(body) => {
                self.nested(body, Pos::default())?;
            }
            Stmt::ForIn { pos, .. } => {
                return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                    "for-in inside generator requires iterator lifetime/close lowering"));
            }
            Stmt::Match { pos, .. } => {
                return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                    "match inside generator requires typed arm CFG lowering"));
            }
            Stmt::Throw(_, pos) => {
                return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                    "throw inside generator requires continuation exception unwinding"));
            }
        }
        Ok(())
    }

    fn stmts(&mut self, body: &[Stmt]) -> Result<(), Diagnostic> {
        for s in body {
            self.stmt(s)?;
        }
        Ok(())
    }
}

/// Lower into a finite, stable resume-state graph. All jumps are checked
/// against the resulting graph length before returning. Only explicitly
/// supported source control-flow constructs are admitted; advanced features
/// remain E_UNSUPPORTED until runtime/lifetime semantics are implemented.
pub fn lower(body: &[Stmt]) -> Result<GeneratorPlan, Diagnostic> {
    let mut builder = Builder::default();
    builder.stmts(body)?;
    builder.push(Instruction::Done, Pos::default())?;
    let n = builder.pc();
    for op in &builder.instructions {
        let to = match op {
            Instruction::Guard { on_false, .. } => Some(*on_false),
            Instruction::Jump { to } => Some(*to),
            _ => None,
        };
        if let Some(to) = to {
            if to >= n {
                return Err(Diagnostic::new(Pos::default(), "E_COMPILER",
                    "invalid generator resume control-flow target"));
            }
        }
    }
    Ok(GeneratorPlan {
        instructions: builder.instructions,
        delegate_slots: builder.delegate_slots,
        yields: builder.yields,
    })
}
