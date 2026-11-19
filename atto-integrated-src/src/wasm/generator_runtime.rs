//! Real guest-Wasm generator runtime code emission for the explicitly admitted
//! zero-capture, finite Generator<int> profile. Functions are ordinary Wasm
//! code with no host imports or JS generator shims.
use super::*;

const FRAME_LIVE_SLOTS: usize = crate::check::GENERATOR_MAX_LIVE_I64_LOCALS;
const GENERATOR_FRAME_BYTES: i32 = 56 + (FRAME_LIVE_SLOTS as i32) * 8;
const FUEL_LOCAL: u32 = 7 + FRAME_LIVE_SLOTS as u32;
const MAX_STEPS_PER_PULL: i32 = 65536;

/// Four guest functions after source callables: new, checked_ptr, next, close.
/// Every generator frame has the same bounded size so a recycled frame
/// cannot be too small for its next owner, even when local counts differ.
/// All loads from a handle go through the generation/bounds validator.
pub(super) fn bodies(p: &TProgram, l: &Layout) -> Vec<(Sig, Vec<u8>)> {
    assert!(p.heap && !p.generators.is_empty());
    let free = l.gen_free_global.expect("generator free-list global");
    let first = l.func(l.gen_first_func);
    let mut out = Vec::with_capacity(4);

    let make = |locals: &[Type]| Emit {
        l,
        code: locals_decl(locals),
        frames: Vec::new(),
        void_main: false,
        active_iterators: Vec::new(),
        // Generator functions never receive protected-state authority.
        state_ticket_slot: None,
        state_write_depth: 0,
        uw: None,
        in_recover: false,
        calls: Vec::new(),
        landings: Vec::new(),
    };

    // new(type_id: i32, arg: i64) -> i64 generation-fenced handle.
    // Local 2=frame pointer, local 3=generation.
    let mut e = make(&[Type::Bool, Type::Bool]);
    e.global_get(free);
    e.op(0x45); // free list empty
    e.open(0x04, 0x40, Frame::Other);
    // Align the shared bump allocator to 8 bytes. Other allocation
    // paths (e.g. string concatenation) need not have done so.
    e.global_get(1);
    e.i32c(7);
    e.op(0x6A);
    e.i32c(-8);
    e.op(0x71);
    e.global_set(1);
    e.i32c(GENERATOR_FRAME_BYTES);
    e.call(l.helper(H_ALLOC));
    e.set(2);
    e.i32c(1);
    e.set(3);
    e.op(0x05); // reuse a CLOSED equal-sized generator frame
    e.global_get(free);
    e.set(2);
    // Only a CLOSED frame may be recycled. An invalid free-list node
    // must trap rather than acquiring a forged or still-live frame.
    e.get(2); e.load_i32(8); e.i32c(5); e.op(0x47);
    e.open(0x04, 0x40, Frame::Other);
    e.invalid_gen();
    e.close();
    e.get(2);
    e.load_i32(24);
    e.global_set(free);
    e.get(2);
    e.load_i32(12);
    e.set(3);
    e.get(3);
    e.i32c(-1);
    e.op(0x46);
    e.open(0x04, 0x40, Frame::Other);
    e.invalid_gen(); // generation wrap/ABA prohibited
    e.close();
    e.get(3);
    e.i32c(1);
    e.op(0x6A);
    e.set(3);
    e.close();
    e.get(2); e.get(0); e.store_i32(0); // generator type
    e.get(2); e.i32c(0); e.store_i32(4); // PC = 0
    e.get(2); e.i32c(0); e.store_i32(8); // CREATED
    e.get(2); e.get(3); e.store_i32(12); // generation
    e.get(2); e.i64c(0); e.store_i64(16); // last value
    e.get(2); e.i32c(0); e.store_i32(24); // free link
    e.get(2); e.get(1); e.store_i64(32); // immutable generator parameter
    e.get(2); e.i64c(0); e.store_i64(40); // persistent counter local
    e.get(2); e.i64c(0); e.store_i64(48); // delegated child handle
    // Clear all persistent slots on create and reuse (no stale data flow).
    for n in 0..FRAME_LIVE_SLOTS {
        e.get(2); e.i64c(0); e.store_i64(56 + 8 * n as u32);
    }
    for (gen_type, gen) in p.generators.iter().enumerate() {
        if let Some(TGenStep::CountTo { start }) = gen.steps.iter()
            .find(|step| matches!(step, TGenStep::CountTo { .. })) {
            e.get(0); e.i32c(gen_type as i32); e.op(0x46);
            e.open(0x04, 0x40, Frame::Other);
            e.get(2); e.i64c(*start); e.store_i64(40);
            e.close();
        }
    }
    e.get(3); e.op(0xAD); // i64.extend_i32_u generation
    e.i64c(32); e.op(0x86); // shift left 32
    e.get(2); e.op(0xAD); e.op(0x84); // combine arena offset
    e.op(0x0B);
    out.push((Sig(vec![I32, I64], vec![I64]), e.code));

    // checked_ptr(handle: i64) -> i32.
    let mut e = make(&[Type::Bool, Type::Bool]);
    e.get(0); e.op(0xA7); e.set(1); // i32.wrap_i64
    e.get(1); e.i32c(8); e.op(0x49); // ptr < 8
    e.open(0x04, 0x40, Frame::Other); e.invalid_gen(); e.close();
    e.get(1); e.i32c(HEAP_PAGES as i32 * 65536 - GENERATOR_FRAME_BYTES);
    e.op(0x4B); // ptr > last complete frame start
    e.open(0x04, 0x40, Frame::Other); e.invalid_gen(); e.close();
    e.get(1); e.i32c(7); e.op(0x71); // alignment
    e.open(0x04, 0x40, Frame::Other); e.invalid_gen(); e.close();
    // Address must refer to a *completed* allocation, not simply an
    // in-bounds location within the fixed guest memory.
    e.get(1); e.i32c(GENERATOR_FRAME_BYTES); e.op(0x6A);
    e.global_get(1); e.op(0x4B); // frame end > bump pointer?
    e.open(0x04, 0x40, Frame::Other); e.invalid_gen(); e.close();
    e.get(0); e.i64c(32); e.op(0x88); e.op(0xA7); // generation
    e.set(2);
    e.get(2); e.op(0x45); // zero epoch invalid
    e.open(0x04, 0x40, Frame::Other); e.invalid_gen(); e.close();
    e.get(1); e.load_i32(12); e.get(2); e.op(0x47);
    e.open(0x04, 0x40, Frame::Other); e.invalid_gen(); e.close();
    e.get(1);
    e.op(0x0B);
    out.push((Sig(vec![I64], vec![I32]), e.code));

    // next(handle: i64) -> i32: 1=YIELDED, 0=DONE.
    // Pull-only progress: one item per invocation, no eager collection.
    // Locals: 1=frame ptr, 2=PC, 3=type, 4=child i64, 5=child status,
    // 6=immutable parameter, 7..=22=persistent ints, 23=dispatch budget.
    let mut next_locals = vec![
        Type::Bool, Type::Bool, Type::Bool,
        Type::GeneratorInt, Type::Bool, Type::Int,
    ];
    next_locals.extend(std::iter::repeat(Type::Int).take(FRAME_LIVE_SLOTS));
    next_locals.push(Type::Bool); // dispatch fuel i32
    let mut e = make(&next_locals);
    e.get(0); e.call(first + 1); e.set(1);
    e.get(1); e.load_i32(8); e.i32c(3); e.op(0x46);
    e.open(0x04, 0x40, Frame::Other);
    e.i32c(0); e.op(0x0F); // DONE stays DONE
    e.close();
    e.get(1); e.load_i32(8); e.i32c(0); e.op(0x46);
    e.get(1); e.load_i32(8); e.i32c(2); e.op(0x46);
    e.op(0x72); e.op(0x45); // only CREATED/SUSPENDED can run
    e.open(0x04, 0x40, Frame::Other); e.invalid_gen(); e.close();
    e.get(1); e.i32c(1); e.store_i32(8); // RUNNING
    e.get(1); e.load_i32(0); e.set(3);
    // Reload scalar locals each pull; each SET writes through immediately.
    e.get(1); e.load_i64(32); e.set(6);
    for n in 0..FRAME_LIVE_SLOTS {
        e.get(1); e.load_i64(56 + 8 * n as u32);
        e.set(7 + n as u32);
    }
    e.i32c(MAX_STEPS_PER_PULL); e.set(FUEL_LOCAL);
    // A completed delegate may be followed by more outer yields. Loop
    // internally until either one item is produced or the outer PC is DONE.
    e.open(0x03, 0x40, Frame::Top);
    // Every non-yielding CFG edge consumes fuel, including loops.
    e.get(FUEL_LOCAL); e.op(0x45);
    e.open(0x04, 0x40, Frame::Other);
    panic(&mut e.code, PANIC_GENERATOR_BUDGET);
    e.close();
    e.get(FUEL_LOCAL); e.i32c(1); e.op(0x6B); e.set(FUEL_LOCAL);
    e.get(1); e.load_i32(4); e.set(2);
    for (gen_id, gen) in p.generators.iter().enumerate() {
        e.get(3); e.i32c(gen_id as i32); e.op(0x46);
        e.open(0x04, 0x40, Frame::Other);
        for (pc, step) in gen.steps.iter().enumerate() {
            e.get(2); e.i32c(pc as i32); e.op(0x46);
            e.open(0x04, 0x40, Frame::Other);
            match step {
                TGenStep::Yield(item) => {
                    e.get(1); e.expr(item); e.store_i64(16);
                    // Once the yielded value is copied out, clear scalar
                    // locals that no successor can read before redefinition.
                    // This reduces stale frame data while preserving all
                    // loop-carried variables across suspension.
                    if let Some(&live) = gen.live_after.get(pc) {
                        for local in 0..gen.locals {
                            if live & (1u16 << local) == 0 {
                                e.get(1); e.i64c(0);
                                e.store_i64(56 + local * 8);
                            }
                        }
                    }
                    e.get(1); e.i32c(pc as i32 + 1); e.store_i32(4);
                    e.get(1); e.i32c(2); e.store_i32(8); // SUSPENDED
                    e.i32c(1); e.op(0x0F);
                }
                TGenStep::Delegate { function, arg } => {
                    let child_type = p.generators.iter().position(|g|
                        g.function == *function).expect("typed child generator type");
                    // Create child only when first pulled through delegation.
                    e.get(1); e.load_i64(48); e.op(0x50); // i64.eqz
                    e.open(0x04, 0x40, Frame::Other);
                    e.get(1);
                    e.i32c(child_type as i32);
                    match arg {
                        TGenArg::None => e.i64c(0),
                        TGenArg::Literal(n) => e.i64c(*n),
                        TGenArg::Parameter => {
                            e.get(1); e.load_i64(32);
                        }
                    }
                    e.call(first); // lazy child frame creation
                    e.store_i64(48);
                    e.close();
                    e.get(1); e.load_i64(48); e.set(4);
                    e.get(4); e.call(first + 2); e.set(5); // child next()
                    e.get(5);
                    e.open(0x04, 0x40, Frame::Other);
                    // One yielded child item propagates to the parent. Its
                    // PC stays on the delegate until the child is exhausted.
                    e.get(1);
                    e.get(4); e.op(0xA7); e.load_i64(16);
                    e.store_i64(16);
                    e.get(1); e.i32c(2); e.store_i32(8);
                    e.i32c(1); e.op(0x0F);
                    e.close();
                    // Child DONE: close exactly once, clear its handle, then
                    // advance the parent PC without consuming an outer pull.
                    e.get(4); e.call(first + 3);
                    e.get(1); e.i64c(0); e.store_i64(48);
                    e.get(1); e.i32c(pc as i32 + 1); e.store_i32(4);
                    e.br_to(Frame::Top);
                }
                TGenStep::Set { local, value } => {
                    assert!((*local as usize) < FRAME_LIVE_SLOTS);
                    let local_idx = 7 + *local;
                    e.expr(value);
                    e.set(local_idx);
                    e.get(1); e.get(local_idx);
                    e.store_i64(56 + *local * 8);
                    e.get(1); e.i32c(pc as i32 + 1); e.store_i32(4);
                    e.br_to(Frame::Top);
                }
                TGenStep::Guard { condition, on_false } => {
                    e.expr(condition);
                    e.open(0x04, 0x40, Frame::Other);
                    e.get(1); e.i32c(pc as i32 + 1); e.store_i32(4);
                    e.op(0x05);
                    e.get(1); e.i32c(*on_false as i32); e.store_i32(4);
                    e.close();
                    e.br_to(Frame::Top);
                }
                TGenStep::Jump { to } => {
                    e.get(1); e.i32c(*to as i32); e.store_i32(4);
                    e.br_to(Frame::Top);
                }
                TGenStep::Done => {
                    e.get(1); e.i32c(3); e.store_i32(8); // DONE
                    e.i32c(0); e.op(0x0F);
                }
                TGenStep::CountTo { .. } => {
                    // Persistent counter in frame local[0], immutable limit in
                    // parameter[0]. Preserve value between next() calls.
                    e.get(1); e.load_i64(40);
                    e.get(1); e.load_i64(32);
                    e.op(0x57); // i64.le_s
                    e.open(0x04, 0x40, Frame::Other);
                    e.get(1); e.get(1); e.load_i64(40);
                    e.store_i64(16);
                    // Avoid incrementing past i64::MAX at the final element.
                    e.get(1); e.load_i64(40);
                    e.get(1); e.load_i64(32);
                    e.op(0x51); // i64.eq
                    e.open(0x04, 0x40, Frame::Other);
                    e.get(1); e.i32c(pc as i32 + 1); e.store_i32(4);
                    e.op(0x05);
                    e.get(1);
                    e.get(1); e.load_i64(40);
                    e.i64c(1); e.op(0x7C); // safe: counter < limit
                    e.store_i64(40);
                    e.close();
                    e.get(1); e.i32c(2); e.store_i32(8);
                    e.i32c(1); e.op(0x0F);
                    e.close();
                    // Zero-element range (start > limit).
                    e.get(1); e.i32c(pc as i32 + 1); e.store_i32(4);
                    e.br_to(Frame::Top);
                }
            }
            e.close();
        }
        e.get(2); e.i32c(gen.steps.len() as i32); e.op(0x47);
        e.open(0x04, 0x40, Frame::Other);
        e.invalid_gen(); // corrupt PC is never silently DONE
        e.close();
        e.get(1); e.i32c(3); e.store_i32(8); // DONE
        e.i32c(0); e.op(0x0F);
        e.close();
    }
    e.invalid_gen(); // invalid generator type
    e.close(); // pull loop
    // A Wasm loop has a syntactically possible fallthrough regardless of the
    // unreachable at the end of its body. The function returns i32, so its
    // post-loop path must also be explicitly unreachable.
    e.invalid_gen();
    e.op(0x0B);
    out.push((Sig(vec![I64], vec![I32]), e.code));

    // close(handle: i64) -> (): duplicate close is idempotent until frame
    // reuse; stale handles fail generation checks. A temporary child handle
    // local lets close detach the child before its recursive cleanup.
    let mut e = make(&[Type::Bool, Type::GeneratorInt]);
    e.get(0); e.call(first + 1); e.set(1);
    e.get(1); e.load_i32(8); e.i32c(5); e.op(0x46);
    e.open(0x04, 0x40, Frame::Other);
    e.op(0x0F);
    e.close();
    // Allowed transitions are CREATED/SUSPENDED/DONE -> CLOSING -> CLOSED.
    // RUNNING, CLOSING and corrupted state values must never be recycled.
    e.get(1); e.load_i32(8); e.i32c(0); e.op(0x46);
    e.get(1); e.load_i32(8); e.i32c(2); e.op(0x46);
    e.op(0x72);
    e.get(1); e.load_i32(8); e.i32c(3); e.op(0x46);
    e.op(0x72); e.op(0x45);
    e.open(0x04, 0x40, Frame::Other);
    e.invalid_gen();
    e.close();
    e.get(1); e.i32c(4); e.store_i32(8); // CLOSING
    // Detach child *before* invoking recursive close, preventing reuse or
    // a reentrant cleanup from observing the child as still owned here.
    e.get(1); e.load_i64(48); e.set(2);
    e.get(1); e.i64c(0); e.store_i64(48);
    e.get(2); e.op(0x50); // child handle == 0?
    e.open(0x04, 0x40, Frame::Other);
    e.op(0x05);
    e.get(2); e.call(first + 3);
    e.close();
    // No previously yielded data, captured argument or local value remains
    // accessible in a CLOSED frame, even before that frame is reused.
    e.get(1); e.i64c(0); e.store_i64(16);
    e.get(1); e.i64c(0); e.store_i64(32);
    e.get(1); e.i64c(0); e.store_i64(40);
    for local in 0..FRAME_LIVE_SLOTS {
        e.get(1); e.i64c(0);
        e.store_i64(56 + local as u32 * 8);
    }
    e.get(1); e.i32c(0); e.store_i32(4); // clear resume PC
    e.get(1); e.i32c(5); e.store_i32(8); // CLOSED, preserve epoch
    e.get(1); e.global_get(free); e.store_i32(24);
    e.get(1); e.global_set(free);
    e.op(0x0B);
    out.push((Sig(vec![I64], vec![]), e.code));
    out
}
