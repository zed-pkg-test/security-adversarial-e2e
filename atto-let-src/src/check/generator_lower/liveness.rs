//! Per-suspension dataflow for the bounded scalar continuation profile.
//!
//! in_def[pc] is the intersection of initialized locals along every
//! reachable predecessor edge; live_out[pc] is the union of values required
//! by any successor. Both iterate to a fixed point, including loop backedges.
//! This is separate from source-order type checking: path-dependent reads
//! must never become accidentally valid in a future CFG expansion.
//!
//! No pointer, alias or borrowed-object value is admitted by scalar lowering.
//! Those require extended ownership/lifetime analysis.

use super::*;

fn error(f: &Func, reason: impl Into<String>) -> Diagnostic {
    Diagnostic::new(f.pos, "E_GENERATOR_LIVENESS", reason)
}

/// Map physical Wasm local to frame slot bit. Immutable parameter in
/// local 6 is initialized by the generator creator.
fn reads(f: &Func, value: &TE, slots: u32) -> R<u16> {
    match &value.e {
        TExpr::I64(_) | TExpr::Bool(_) => Ok(0),
        TExpr::Local(6) => Ok(0),
        TExpr::Local(slot) if *slot >= 7 && *slot - 7 < slots =>
            Ok(1u16 << (*slot - 7)),
        TExpr::Neg(a) | TExpr::Not(a) => reads(f, a, slots),
        TExpr::Bin(_, a, b) => Ok(reads(f, a, slots)? | reads(f, b, slots)?),
        _ => Err(error(f, "unsupported expression in generator liveness graph")),
    }
}

#[derive(Clone)]
struct Flow {
    uses: u16,
    defines: u16,
    successors: Vec<usize>,
}

/// For each PC returns local slots live after that instruction. Set bits
/// must be retained after a yield. Unreachable PCs have no live state.
pub(super) fn analyze(f: &Func, steps: &[TGenStep], locals: u32) -> R<Vec<u16>> {
    if steps.is_empty() || locals > GENERATOR_MAX_LIVE_I64_LOCALS as u32 {
        return Err(error(f, "invalid generator continuation size"));
    }
    let n = steps.len();
    let all = if locals == 16 {
        u16::MAX
    } else {
        ((1u32 << locals) - 1) as u16
    };

    let mut flow = Vec::with_capacity(n);
    for (pc, step) in steps.iter().enumerate() {
        let (uses, defines) = match step {
            TGenStep::Set { local, value } if *local < locals =>
                (reads(f, value, locals)?, 1u16 << local),
            TGenStep::Guard { condition, .. } =>
                (reads(f, condition, locals)?, 0),
            TGenStep::Yield(value) => (reads(f, value, locals)?, 0),
            TGenStep::Jump { .. } | TGenStep::Done => (0, 0),
            _ => return Err(error(f, "unsupported step in typed generator liveness")),
        };
        let successors = match step {
            TGenStep::Jump { to } => vec![*to as usize],
            TGenStep::Guard { on_false, .. } =>
                vec![pc + 1, *on_false as usize],
            TGenStep::Done => Vec::new(),
            _ => vec![pc + 1],
        };
        if successors.iter().any(|s| *s >= n) {
            return Err(error(f, "generator control-flow edge leaves the continuation"));
        }
        flow.push(Flow { uses, defines, successors });
    }

    let mut reachable = vec![false; n];
    let mut todo = vec![0usize];
    while let Some(pc) = todo.pop() {
        if reachable[pc] { continue; }
        reachable[pc] = true;
        todo.extend(flow[pc].successors.iter().copied());
    }

    // Forward must-definite-initialization: intersection, with entry=empty.
    let mut in_def = vec![all; n];
    in_def[0] = 0;
    loop {
        let mut changed = false;
        for pc in 0..n {
            if !reachable[pc] { continue; }
            let output = in_def[pc] | flow[pc].defines;
            for &next in &flow[pc].successors {
                let candidate = in_def[next] & output;
                if candidate != in_def[next] {
                    in_def[next] = candidate;
                    changed = true;
                }
            }
        }
        if !changed { break; }
    }
    for pc in 0..n {
        if reachable[pc] && flow[pc].uses & !in_def[pc] != 0 {
            return Err(error(f, format!(
                "local at resume PC {pc} may be read before initialization"
            )));
        }
    }

    // Backwards may-liveness: merge all possible successors.
    let mut live_in = vec![0u16; n];
    let mut live_out = vec![0u16; n];
    loop {
        let mut changed = false;
        for pc in (0..n).rev() {
            if !reachable[pc] { continue; }
            let output = flow[pc].successors.iter().fold(0, |acc, &next| acc | live_in[next]);
            let input = flow[pc].uses | (output & !flow[pc].defines);
            if output != live_out[pc] || input != live_in[pc] {
                live_out[pc] = output;
                live_in[pc] = input;
                changed = true;
            }
        }
        if !changed { break; }
    }
    Ok(live_out)
}


#[cfg(test)]
mod tests {
    use super::*;

    fn fake() -> Func {
        Func {
            name: "test_generator".into(),
            pos: Pos { line: 1, col: 1 },
            is_generator: true,
            is_pure: false,
            declared_effects: None,
            params: vec![],
            ret: Type::GeneratorInt,
            body: vec![],
        }
    }

    fn int(value: i64) -> TE {
        TE { e: TExpr::I64(value), ty: Type::Int }
    }

    fn local(index: u32) -> TE {
        TE { e: TExpr::Local(7 + index), ty: Type::Int }
    }

    #[test]
    fn branch_that_skips_initializer_cannot_read_uninitialized_slot() {
        let steps = vec![
            TGenStep::Guard {
                condition: TE { e: TExpr::Bool(true), ty: Type::Bool },
                on_false: 2,
            },
            TGenStep::Set { local: 0, value: int(8) },
            TGenStep::Yield(local(0)),
            TGenStep::Done,
        ];
        let e = analyze(&fake(), &steps, 1).unwrap_err();
        assert_eq!(e.code, "E_GENERATOR_LIVENESS");
        assert!(e.message.contains("before initialization"));
    }

    #[test]
    fn fixed_point_keeps_loop_carried_value_live() {
        let steps = vec![
            TGenStep::Set { local: 0, value: int(0) },
            TGenStep::Guard {
                condition: TE { e: TExpr::Bool(true), ty: Type::Bool },
                on_false: 5,
            },
            TGenStep::Set {
                local: 0,
                value: TE {
                    e: TExpr::Bin(
                        BinOp::Add, Box::new(local(0)), Box::new(int(1))
                    ),
                    ty: Type::Int,
                },
            },
            TGenStep::Yield(local(0)),
            TGenStep::Jump { to: 1 },
            TGenStep::Done,
        ];
        let live = analyze(&fake(), &steps, 1).unwrap();
        assert_eq!(live[3], 1, "counter survives the backedge");
    }

    #[test]
    fn dead_at_yield_slot_can_be_scrubbed_without_losing_output() {
        let steps = vec![
            TGenStep::Set { local: 0, value: int(7) },
            TGenStep::Set { local: 1, value: int(11) },
            TGenStep::Yield(local(0)),
            TGenStep::Yield(local(1)),
            TGenStep::Done,
        ];
        let live = analyze(&fake(), &steps, 2).unwrap();
        assert_eq!(live[2], 0b10);
        assert_eq!(live[3], 0);
    }

    #[test]
    fn malformed_edges_and_physical_slots_reject_without_issuing_wasm() {
        let bad_jump = vec![TGenStep::Jump { to: 4 }, TGenStep::Done];
        assert_eq!(analyze(&fake(), &bad_jump, 1).unwrap_err().code,
                   "E_GENERATOR_LIVENESS");
        let bad_slot = vec![TGenStep::Yield(TE {
            e: TExpr::Local(99), ty: Type::Int,
        }), TGenStep::Done];
        assert_eq!(analyze(&fake(), &bad_slot, 1).unwrap_err().code,
                   "E_GENERATOR_LIVENESS");
    }
}
