//! Typed IR -> WebAssembly binary (core spec 1.0 plus mutable-global export).
//!
//! Guest contract `atto.browser.guest.v2` (v1 plus classes and actors):
//! * export `main: () -> i64` (a void `main` returns 0)
//! * export `panic_code: mut i32`, set before a language-level panic traps:
//!   1 = integer overflow; 2 is reserved (division/remainder unsupported);
//!   3 = object heap exhausted; 4 = invalid generator handle/state;
//!   5 = generator per-pull dispatch budget exhausted;
//!   6 = logical stack exhausted: a recursive call exceeded [`MAX_CALL_DEPTH`]
//! * export `memory` when strings, classes, or actors exist;
//!   actor-only modules receive one private 64 KiB page per instance;
//!   with classes it is a fixed, non-growable [`HEAP_PAGES`]-page memory
//! * imports, only those used, from module `atto`:
//!   `print_i64(i64)`, `print_bool(i32)`, `print_str(i32 offset, i32 len)`,
//!   `print_newline()`, `actor_spawn(i32 type) -> i32 ref`,
//!   `actor_send(i32 ref, i64 value)`
//! * with actors, also export `actor_init(i32 type)` and
//!   `actor_receive(i32 type, i64 value, i64 sequence)`, plus a custom section
//!   `atto.actors` listing actor type names by type index. The host runs each
//!   spawned actor in its own Wasm instance, calls `actor_init` once,
//!   then `actor_receive` per message in
//!   FIFO order. Actor state lives in that instance's globals.
//!
//! Output is a pure function of the source: no hash-map iteration, clocks or
//! randomness, so identical input yields byte-identical modules on every host.

use crate::ast::{BinOp, Type};
use crate::check::{Builtin, Import, PrintPiece, StrOp, TExpr, TGenArg, TGenStep, TProgram, TStmt, TE};

mod generator_runtime;

pub const MAX_OUTPUT: usize = 1 << 20;
pub const PANIC_OVERFLOW: i32 = 1;
/// Reserved ABI value; current admitted expressions cannot generate this panic.
pub const PANIC_DIV_ZERO: i32 = 2;
pub const PANIC_HEAP: i32 = 3;
pub const PANIC_GENERATOR: i32 = 4;
/// Non-yielding generator exceeded its bounded per-pull dispatch budget.
pub const PANIC_GENERATOR_BUDGET: i32 = 5;
/// Logical stack exhausted (spec chapter 25): a call inside a recursive call
/// cycle would exceed [`MAX_CALL_DEPTH`] live guest frames.
pub const PANIC_STACK: i32 = 6;
/// Live recursive guest frames per receive invocation (or `main`). Same
/// default quota as the Java backend, so a program overflows at the same
/// source depth in every browser instead of at each engine's native limit.
pub const MAX_CALL_DEPTH: i32 = 1024;
/// Fixed memory size, in 64 KiB pages, of a module that allocates objects.
pub const HEAP_PAGES: u32 = 16;

const I32: u8 = 0x7F;
const I64: u8 = 0x7E;
const F64: u8 = 0x7C;

fn uleb(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7F) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            break;
        }
        out.push(b | 0x80);
    }
}

fn sleb(out: &mut Vec<u8>, mut v: i64) {
    loop {
        let b = (v & 0x7F) as u8;
        v >>= 7;
        let done = (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0);
        out.push(if done { b } else { b | 0x80 });
        if done {
            break;
        }
    }
}

fn name(out: &mut Vec<u8>, s: &str) {
    uleb(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

fn section(out: &mut Vec<u8>, id: u8, body: Vec<u8>) {
    out.push(id);
    uleb(out, body.len() as u64);
    out.extend(body);
}

fn vt(t: Type) -> Option<u8> {
    match t {
        Type::Int => Some(I64),
        Type::Bool => Some(I32),
        Type::Void => None,
        Type::Float => Some(F64),
        Type::Str => Some(I64),
        Type::Class(_) | Type::Array(_) | Type::Enum(_) | Type::ActorRef(_) | Type::OptionInt | Type::ResultIntStr | Type::OptionResultIntStr => Some(I32),
        Type::GeneratorInt => Some(I64),
        Type::Named(_) | Type::NamedRef(_) | Type::Callable(_) => unreachable!("types are resolved or rejected by the checker"),
    }
}

#[derive(Clone, PartialEq, Eq)]
struct Sig(Vec<u8>, Vec<u8>);

struct Types(Vec<Sig>);
impl Types {
    fn idx(&mut self, s: Sig) -> u32 {
        if let Some(i) = self.0.iter().position(|x| *x == s) {
            return i as u32;
        }
        self.0.push(s);
        (self.0.len() - 1) as u32
    }
}

// helper function order, placed right after imports
const H_ADD: u32 = 0;
const H_SUB: u32 = 1;
const H_MUL: u32 = 2;
const H_NEG: u32 = 3;
/// present only when the program has classes
const H_ALLOC: u32 = 4;
// string helpers, present only when the program has string values; they
// follow H_ALLOC (or H_NEG) at `Layout::str_base + offset`
const S_BYTES_EQ: u32 = 0;
const S_EQ: u32 = 1;
const S_STARTS: u32 = 2;
const S_ENDS: u32 = 3;
const S_CONTAINS: u32 = 4;
const S_TRIM: u32 = 5;
const S_CONCAT: u32 = 6;
const S_CMP: u32 = 7;
const STRING_HELPERS: u32 = 8;

struct Layout {
    imports: Vec<Import>,
    helpers: u32,
    /// helper index of `S_BYTES_EQ`
    str_base: u32,
    /// global index of actor-state global 0
    state_base: u32,
    /// Per-instance free-list for 32-byte generator continuation frames.
    gen_free_global: Option<u32>,
    /// Function index within source funcs+runtime helpers: first appended
    /// generator operation is new(); then checked_ptr, next, close.
    gen_first_func: u32,
    /// Guest-global active-catch counter for two-phase recover dispatch.
    catch_depth: Option<u32>,
    /// Module-private escalated-failure tag (index 1) exists.
    raise_tag: bool,
}
impl Layout {
    fn import(&self, i: Import) -> u32 {
        self.imports.iter().position(|x| *x == i).expect("import registered by checker") as u32
    }
    fn helper(&self, h: u32) -> u32 {
        debug_assert!(h < self.helpers);
        self.imports.len() as u32 + h
    }
    fn func(&self, f: u32) -> u32 {
        self.imports.len() as u32 + self.helpers + f
    }
    fn str_helper(&self, s: u32) -> u32 {
        self.helper(self.str_base + s)
    }
}

/// Load (`store = false`) or store a field slot of type `t` at `offset`.
fn field_op(code: &mut Vec<u8>, t: Type, offset: u32, store: bool) {
    let (op, align) = match (t, store) {
        (Type::Int | Type::Str, false) => (0x29, 3),
        (Type::Int | Type::Str, true) => (0x37, 3),
        (Type::Float, false) => (0x2B, 3),
        (Type::Float, true) => (0x39, 3),
        (_, false) => (0x28, 2),
        (_, true) => (0x36, 2),
    };
    code.push(op);
    code.push(align);
    uleb(code, offset as u64);
}

#[derive(Clone, Copy, PartialEq)]
enum Frame {
    Break,
    Top,
    Continue,
    Other,
    /// Normal function exit that still runs registered defers.
    Ret,
    /// Function exit after defers already ran (recovered result).
    Done,
    /// Landing block before a `finally` body on a pending return.
    FinallyExit,
    /// Terminal `c.next()` target: the next older recovery callback.
    RecoverNext,
}

struct Emit<'a> {
    l: &'a Layout,
    code: Vec<u8>,
    frames: Vec<Frame>,
    /// `Some(..)` when compiling a void `main` export: plain `return` must
    /// still produce the exported i64 status 0.
    void_main: bool,
    /// Owned generator handles active in nested for-in loops. Function-level
    /// returns close these in reverse order before exiting.
    active_iterators: Vec<u32>,
    /// Scratch i64 local for an opaque host-issued admission ticket.
    state_ticket_slot: Option<u32>,
    state_write_depth: u32,
    /// Unwind slots of a try/defer/recover function: (ret, saved, msg, kind, pending).
    uw: Option<(Option<u32>, u32, u32, u32, u32)>,
    /// Emitting a recovery callback body: `return` exits after defers ran.
    in_recover: bool,
    /// Byte ranges `[start, end)` of user calls and their callee, for the
    /// post-pass that bounds recursive calls with the call-depth quota.
    calls: Vec<(usize, usize, u32)>,
    /// Byte offsets right after each catch / catch_all opcode (landing pads).
    landings: Vec<usize>,
}

impl Emit<'_> {
    fn op(&mut self, b: u8) {
        self.code.push(b);
    }
    fn i64c(&mut self, v: i64) {
        self.op(0x42);
        sleb(&mut self.code, v);
    }
    fn i32c(&mut self, v: i32) {
        self.op(0x41);
        sleb(&mut self.code, v as i64);
    }
    /// Mark an exception landing pad (just after `catch tag` / `catch_all`).
    fn landing(&mut self) {
        self.landings.push(self.code.len());
    }
    fn call(&mut self, idx: u32) {
        self.op(0x10);
        uleb(&mut self.code, idx as u64);
    }
    fn br_to(&mut self, f: Frame) {
        let at = self.frames.iter().rposition(|x| *x == f).expect("loop frame");
        self.op(0x0C);
        uleb(&mut self.code, (self.frames.len() - 1 - at) as u64);
    }
    fn open(&mut self, opcode: u8, blocktype: u8, f: Frame) {
        self.op(opcode);
        self.op(blocktype);
        self.frames.push(f);
    }
    fn close(&mut self) {
        self.op(0x0B);
        self.frames.pop();
    }

    fn get(&mut self, slot: u32) {
        self.op(0x20);
        uleb(&mut self.code, slot as u64);
    }
    fn set(&mut self, slot: u32) {
        self.op(0x21);
        uleb(&mut self.code, slot as u64);
    }
    fn global_get(&mut self, slot: u32) {
        self.op(0x23);
        uleb(&mut self.code, slot as u64);
    }
    fn global_set(&mut self, slot: u32) {
        self.op(0x24);
        uleb(&mut self.code, slot as u64);
    }
    fn load_i32(&mut self, offset: u32) {
        self.op(0x28);
        uleb(&mut self.code, 2);
        uleb(&mut self.code, offset as u64);
    }
    fn store_i32(&mut self, offset: u32) {
        self.op(0x36);
        uleb(&mut self.code, 2);
        uleb(&mut self.code, offset as u64);
    }
    fn load_i64(&mut self, offset: u32) {
        self.op(0x29);
        uleb(&mut self.code, 3);
        uleb(&mut self.code, offset as u64);
    }
    fn store_i64(&mut self, offset: u32) {
        self.op(0x37);
        uleb(&mut self.code, 3);
        uleb(&mut self.code, offset as u64);
    }
    fn invalid_gen(&mut self) {
        panic(&mut self.code, PANIC_GENERATOR);
    }

    fn depth_save(&mut self, slot: u32) {
        if let Some(g) = self.l.catch_depth {
            self.global_get(g);
            self.set(slot);
        }
    }
    fn depth_restore(&mut self, slot: u32) {
        if let Some(g) = self.l.catch_depth {
            self.get(slot);
            self.global_set(g);
        }
    }
    fn depth_add(&mut self, delta: i32) {
        if let Some(g) = self.l.catch_depth {
            self.global_get(g);
            self.i32c(delta);
            self.op(0x6A); // i32.add
            self.global_set(g);
        }
    }

    /// Leave the function after the return value was stored: a recovered
    /// result skips defers (they already ran); otherwise run the innermost
    /// pending `finally`, or the function's defers.
    fn return_path(&mut self) {
        if self.in_recover {
            self.br_to(Frame::Done);
        } else if self.frames.contains(&Frame::FinallyExit) {
            self.i32c(1);
            self.set(self.uw.expect("unwind slots").4);
            self.br_to(Frame::FinallyExit);
        } else {
            self.br_to(Frame::Ret);
        }
    }

    /// try / catch (Error) / finally on legacy Wasm EH.
    ///
    /// The catch matches only private tag 0 (ordinary throw). `finally`
    /// runs once on fallthrough, on a pending return (via FinallyExit),
    /// and on any escaping exception (catch_all + rethrow, preserving the
    /// original tag and payload). Engine traps are never Wasm exceptions.
    fn try_stmt(&mut self, saved: u32, body: &[TStmt], catch: Option<&[TStmt]>, finally: Option<&[TStmt]>) {
        self.depth_save(saved);
        if finally.is_some() {
            self.open(0x02, 0x40, Frame::FinallyExit);
            self.open(0x06, 0x40, Frame::Other);
        }
        if let Some(handler) = catch {
            self.depth_add(1); // an active catch outranks every callee recover
            self.open(0x06, 0x40, Frame::Other);
            self.stmts(body);
            self.op(0x07); // catch private ordinary-throw tag 0
            uleb(&mut self.code, 0);
            self.landing();
            self.op(0x1A); // drop the i64 Error message
            self.depth_restore(saved);
            self.stmts(handler);
            self.close();
            self.depth_restore(saved);
        } else {
            self.stmts(body);
        }
        if let Some(cleanup) = finally {
            self.op(0x19); // catch_all: raise, uncaught throw or rethrown failure
            self.landing();
            self.depth_restore(saved);
            self.stmts(cleanup);
            self.op(0x09); // rethrow the caught exception unchanged
            uleb(&mut self.code, 0);
            self.close(); // end try
            self.close(); // end FinallyExit
            self.depth_restore(saved);
            self.stmts(cleanup);
            let pending = self.uw.expect("unwind slots").4;
            self.get(pending);
            self.open(0x04, 0x40, Frame::Other);
            self.return_path();
            self.close();
        }
    }

    fn run_defers(&mut self, defers: &[(u32, &[TStmt])]) {
        for (flag, body) in defers.iter().rev() {
            self.get(*flag);
            self.open(0x04, 0x40, Frame::Other);
            self.stmts(body);
            self.close();
        }
    }

    /// Function body with compiler-owned unwind metadata
    /// (atto-spec language/defer-recover-unwind-v1.md):
    ///
    /// ```text
    /// block $done
    ///   block $ret
    ///     try                       ;; only with defers or recovers
    ///       body                    ;; return => ret := v; br $ret (or finally)
    ///     catch 0 | catch 1         ;; msg/kind := pending failure
    ///     end
    ///     restore depth; defers LIFO
    ///     throw && active outer catch => rethrow (caller catch has priority)
    ///     recovers LIFO             ;; return => br $done, c.next() => next
    ///     rethrow original failure
    ///   end
    ///   restore depth; defers LIFO
    /// end
    /// ```
    fn unwind_body(&mut self, body: &[TStmt], is_void_main: bool, ret: Type) {
        let (ret_slot, saved, msg, kind, _) = self.uw.expect("unwind slots");
        let defers: Vec<(u32, &[TStmt])> = body.iter().filter_map(|s| match s {
            TStmt::Defer { flag, body, .. } => Some((*flag, body.as_slice())),
            _ => None,
        }).collect();
        let recovers: Vec<(u32, &[TStmt])> = body.iter().filter_map(|s| match s {
            TStmt::Recover { flag, body, .. } => Some((*flag, body.as_slice())),
            _ => None,
        }).collect();
        let boundary = !defers.is_empty() || !recovers.is_empty();
        self.depth_save(saved);
        self.open(0x02, 0x40, Frame::Done);
        self.open(0x02, 0x40, Frame::Ret);
        if boundary {
            self.open(0x06, 0x40, Frame::Other);
        }
        self.stmts(body);
        if ret == Type::Void {
            self.br_to(Frame::Ret);
        } else {
            self.op(0x00); // definite-return analysis proved every path returns
        }
        if boundary {
            self.op(0x07);
            uleb(&mut self.code, 0);
            self.landing();
            self.set(msg);
            self.i32c(0);
            self.set(kind);
            if self.l.raise_tag {
                self.op(0x07);
                uleb(&mut self.code, 1);
                self.landing();
                self.set(msg);
                self.i32c(1);
                self.set(kind);
            }
            self.close();
            self.depth_restore(saved);
            self.run_defers(&defers);
            if !recovers.is_empty() {
                let g = self.l.catch_depth.expect("recover implies a catch-depth global");
                // Phase one: an ordinary throw with any active outer catch
                // or trap is NOT ours; the caller's handler wins.
                self.get(kind);
                self.op(0x45); // i32.eqz: ordinary throw
                self.global_get(g);
                self.i32c(0);
                self.op(0x4A); // i32.gt_s
                self.op(0x71); // i32.and
                self.open(0x04, 0x40, Frame::Other);
                self.get(msg);
                self.op(0x08);
                uleb(&mut self.code, 0);
                self.close();
                // Phase two: newest registered callback first.
                for (flag, handler) in recovers.iter().rev() {
                    self.get(*flag);
                    self.open(0x04, 0x40, Frame::Other);
                    self.open(0x02, 0x40, Frame::RecoverNext);
                    self.in_recover = true;
                    self.stmts(handler);
                    self.in_recover = false;
                    self.close();
                    self.close();
                }
            }
            if self.l.raise_tag {
                self.get(kind);
                self.open(0x04, 0x40, Frame::Other);
                self.get(msg);
                self.op(0x08);
                uleb(&mut self.code, 1);
                self.close();
            }
            self.get(msg);
            self.op(0x08);
            uleb(&mut self.code, 0);
        }
        self.close(); // end $ret
        self.depth_restore(saved);
        self.run_defers(&defers);
        self.close(); // end $done
        if is_void_main {
            self.i64c(0);
        } else if let Some(slot) = ret_slot {
            self.get(slot);
        }
    }

    fn stmts(&mut self, s: &[TStmt]) {
        for st in s {
            self.stmt(st);
        }
    }

    fn stmt(&mut self, s: &TStmt) {
        match s {
            TStmt::Set(slot, v) => {
                self.expr(v);
                self.op(0x21);
                uleb(&mut self.code, *slot as u64);
            }
            TStmt::CollectionStore { array, offset, value } => {
                // The checked collection planner supplies an in-bounds byte
                // offset, and the value is always a scalar i64 in this slice.
                self.expr(array);
                self.expr(value);
                field_op(&mut self.code, Type::Int, *offset, true);
            }
            TStmt::FieldSet { obj, offset, ty, value } => {
                self.expr(obj);
                self.expr(value);
                field_op(&mut self.code, *ty, *offset, true);
            }
            TStmt::StateFieldWrite { obj, offset, ty, value } => {
                assert!(self.state_write_depth > 0,
                    "state field write missing typed exclusive scope");
                self.expr(obj);
                self.expr(value);
                field_op(&mut self.code, *ty, *offset, true);
            }
            TStmt::StateCriticalWrite(body) => {
                // Synchronous, never-park: the host authenticates this
                // container/continuation and either grants immediately or
                // fails closed. Yield/throw/defer in this lexical scope are
                // rejected by the frontend's restricted state profile.
                let slot = self.state_ticket_slot.expect("protected state uses a ticket local");
                debug_assert_eq!(self.state_write_depth, 0);
                self.get(0); // typed receiver: protected state self
                self.i32c(1); // write mode
                self.call(self.l.import(Import::StateEnter));
                self.set(slot);
                self.state_write_depth += 1;
                self.stmts(body);
                self.state_write_depth -= 1;
                self.get(slot);
                self.call(self.l.import(Import::StateLeave));
            }
            TStmt::StateRegister(obj) => {
                self.expr(obj);
                self.call(self.l.import(Import::StateRegister));
            },
            TStmt::GlobalSet(g, v) => {
                self.expr(v);
                self.op(0x24);
                uleb(&mut self.code, (self.l.state_base + g) as u64);
            }
            TStmt::Expr(v) => {
                self.expr(v);
                if v.ty != Type::Void {
                    self.op(0x1A);
                }
            }
            TStmt::Throw(message) => {
                // This is NOT unreachable/panic. The module-private tagged
                // exception carries the guest Error message as an i64 string
                // view and automatically unwinds across ordinary Wasm calls.
                self.expr(message);
                self.op(0x08); // throw tag 0
                uleb(&mut self.code, 0);
            }
            TStmt::Return(v) if self.uw.is_some() => {
                // Snapshot the value before any finally/defer runs, then
                // leave through the compiler-owned cleanup path.
                if let Some(v) = v {
                    self.expr(v);
                    self.set(self.uw.unwrap().0.expect("non-void unwind function has a ret slot"));
                }
                for handle in self.active_iterators.clone().into_iter().rev() {
                    self.get(handle);
                    self.call(self.l.func(self.l.gen_first_func + 3));
                }
                self.return_path();
            }
            TStmt::Raise(message) => {
                self.expr(message);
                self.op(0x08); // throw escalated tag 1: never matched by catch/trap
                uleb(&mut self.code, 1);
            }
            TStmt::UnwindFrame { .. } => {}
            TStmt::Defer { flag, args, .. } => {
                // All factory captures are computed before registering the
                // cleanup; a failed argument cannot register half a defer.
                for (slot, value) in args {
                    self.expr(value);
                    self.set(*slot);
                }
                self.i32c(1);
                self.set(*flag);
            }
            TStmt::Recover { flag, args, .. } => {
                for (slot, value) in args {
                    self.expr(value);
                    self.set(*slot);
                }
                self.i32c(1);
                self.set(*flag);
            }
            TStmt::RecoverNext => self.br_to(Frame::RecoverNext),
            TStmt::Try { saved, body, catch, finally, .. } => self.try_stmt(*saved, body, catch.as_deref(), finally.as_deref()),
            TStmt::Return(v) => {
                if let Some(v) = v {
                    self.expr(v);
                } else if self.void_main {
                    self.i64c(0);
                }
                // Function-level returns cannot bypass iterator closure.
                for handle in self.active_iterators.clone().into_iter().rev() {
                    self.get(handle);
                    self.call(self.l.func(self.l.gen_first_func + 3));
                }
                self.op(0x0F);
            }
            TStmt::ForIn { source, handle_slot, value_slot, body } => {
                self.expr(source);
                self.set(*handle_slot);
                self.open(0x02, 0x40, Frame::Break);
                self.open(0x03, 0x40, Frame::Top);
                self.get(*handle_slot);
                self.call(self.l.func(self.l.gen_first_func + 2)); // next
                self.op(0x45); // i32.eqz => DONE
                self.op(0x0D); // br_if break
                uleb(&mut self.code, 1);
                self.get(*handle_slot);
                self.op(0xA7); // i32.wrap_i64: validated by next
                self.load_i64(16);
                self.set(*value_slot);
                self.open(0x02, 0x40, Frame::Continue);
                self.active_iterators.push(*handle_slot);
                self.stmts(body);
                self.active_iterators.pop();
                self.close();
                self.br_to(Frame::Top);
                self.close();
                self.close();
                self.get(*handle_slot);
                self.call(self.l.func(self.l.gen_first_func + 3)); // close
            }
            TStmt::If(arms, other) => self.if_chain(arms, other.as_deref()),
            TStmt::Loop { cond, body, update } => {
                self.open(0x02, 0x40, Frame::Break);
                self.open(0x03, 0x40, Frame::Top);
                if let Some(c) = cond {
                    self.expr(c);
                    self.op(0x45); // i32.eqz
                    self.op(0x0D); // br_if
                    uleb(&mut self.code, 1);
                }
                self.open(0x02, 0x40, Frame::Continue);
                self.stmts(body);
                self.close();
                self.stmts(update);
                self.br_to(Frame::Top);
                self.close();
                self.close();
            }
            TStmt::Break => self.br_to(Frame::Break),
            TStmt::Continue => self.br_to(Frame::Continue),
            TStmt::Block(b) => self.stmts(b),
            TStmt::Unreachable => self.op(0x00),
        }
    }

    fn if_chain(&mut self, arms: &[(TE, Vec<TStmt>)], other: Option<&[TStmt]>) {
        let (c, body) = &arms[0];
        self.expr(c);
        self.open(0x04, 0x40, Frame::Other);
        self.stmts(body);
        if arms.len() > 1 {
            self.op(0x05);
            self.if_chain(&arms[1..], other);
        } else if let Some(o) = other {
            self.op(0x05);
            self.stmts(o);
        }
        self.close();
    }

    fn expr(&mut self, v: &TE) {
        match &v.e {
            TExpr::I64(n) => self.i64c(*n),
            TExpr::F64(x) => {
                self.op(0x44);
                self.code.extend_from_slice(&x.to_le_bytes());
            }
            TExpr::StrConst(offset, len) => self.i64c(((*offset as i64) << 32) | *len as i64),
            TExpr::IntToFloat(a) => {
                self.expr(a);
                self.op(0xB9); // f64.convert_i64_s
            }
            TExpr::FNeg(a) => {
                self.expr(a);
                self.op(0x9A);
            }
            TExpr::Str(op, a, arg) => {
                self.expr(a);
                if let Some(b) = arg {
                    self.expr(b);
                }
                self.call(self.l.str_helper(match op {
                    StrOp::Eq => S_EQ,
                    StrOp::StartsWith => S_STARTS,
                    StrOp::EndsWith => S_ENDS,
                    StrOp::Contains => S_CONTAINS,
                    StrOp::Trim => S_TRIM,
                    StrOp::Concat => S_CONCAT,
                    StrOp::Cmp => S_CMP,
                }));
            }
            TExpr::PrintStrVal { value, tmp, newline } => {
                self.expr(value);
                self.op(0x21);
                uleb(&mut self.code, *tmp as u64);
                str_parts(&mut self.code, *tmp);
                self.call(self.l.import(Import::PrintStr));
                if *newline {
                    self.call(self.l.import(Import::PrintNewline));
                }
            }
            TExpr::Bool(b) => self.i32c(*b as i32),
            TExpr::Local(slot) => {
                self.op(0x20);
                uleb(&mut self.code, *slot as u64);
            }
            TExpr::Neg(a) => {
                self.expr(a);
                self.call(self.l.helper(H_NEG));
            }
            TExpr::Not(a) => {
                self.expr(a);
                self.op(0x45);
            }
            TExpr::Bin(op, a, b) => {
                // Canonical AttoLang conditions are eager: both operands
                // execute in source order even when the left decides truth.
                self.expr(a);
                self.expr(b);
                let int = a.ty == Type::Int;
                if a.ty == Type::Float {
                    self.op(match op {
                        BinOp::Add => 0xA0,
                        BinOp::Sub => 0xA1,
                        BinOp::Mul => 0xA2,
                        BinOp::Div => 0xA3,
                        BinOp::Eq => 0x61,
                        BinOp::Ne => 0x62,
                        BinOp::Lt => 0x63,
                        BinOp::Gt => 0x64,
                        BinOp::Le => 0x65,
                        BinOp::Ge => 0x66,
                        BinOp::And | BinOp::Or => unreachable!("conditions are bool"),
                    });
                    return;
                }
                match op {
                    BinOp::Add => self.call(self.l.helper(H_ADD)),
                    BinOp::Sub => self.call(self.l.helper(H_SUB)),
                    BinOp::Mul => self.call(self.l.helper(H_MUL)),
                    BinOp::And => self.op(0x71), // i32.and
                    BinOp::Or => self.op(0x72),  // i32.or
                    BinOp::Lt => self.op(0x53),
                    BinOp::Le => self.op(0x57),
                    BinOp::Gt => self.op(0x55),
                    BinOp::Ge => self.op(0x59),
                    BinOp::Eq => self.op(if int { 0x51 } else { 0x46 }),
                    BinOp::Ne => self.op(if int { 0x52 } else { 0x47 }),
                    BinOp::Div => unreachable!("division not admitted by checker"),
                }
            }
            TExpr::Ternary(c, a, b) => {
                self.expr(c);
                self.open(0x04, vt(v.ty).expect("ternary value type"), Frame::Other);
                self.expr(a);
                self.op(0x05);
                self.expr(b);
                self.close();
            }
            TExpr::Call(f, args) => {
                for a in args {
                    self.expr(a);
                }
                let at = self.code.len();
                self.call(self.l.func(*f));
                self.calls.push((at, self.code.len(), *f));
            }
            TExpr::Builtin(b, x, y) => {
                self.expr(x);
                self.expr(y);
                self.op(match b {
                    Builtin::And => 0x71,
                    Builtin::Or => 0x72,
                    Builtin::Xor => 0x73,
                });
            }
            TExpr::Print { value, newline } => {
                self.expr(value);
                let imp = match value.ty {
                    Type::Int => Import::PrintI64,
                    Type::Float => Import::PrintF64,
                    _ => Import::PrintBool,
                };
                self.call(self.l.import(imp));
                if *newline {
                    self.call(self.l.import(Import::PrintNewline));
                }
            }
            TExpr::PrintStr { offset, len, newline } => {
                self.i32c(*offset as i32);
                self.i32c(*len as i32);
                self.call(self.l.import(Import::PrintStr));
                if *newline {
                    self.call(self.l.import(Import::PrintNewline));
                }
            }
            TExpr::EnumVal(i) => self.i32c(*i as i32),
            TExpr::Trap { value, value_tmp, some_tmp, none_tmp } => {
                // The only caught signal is our private ordinary-throw tag.
                // WebAssembly engine traps, arithmetic panic, cancellation,
                // host exceptions, and any other tag bypass this catch.
                // A trap is an active ordinary-throw handler: a callee recover
                // must defer to it (two-phase dispatch). No-op without recover.
                self.depth_add(1);
                self.open(0x06, I32, Frame::Other); // try (result i32)
                self.expr(value); // evaluate once, before any Some allocation
                self.op(0x21); // local.set value_tmp
                uleb(&mut self.code, *value_tmp as u64);
                self.depth_add(-1);
                self.i32c(16);
                self.call(self.l.helper(H_ALLOC));
                self.op(0x21);
                uleb(&mut self.code, *some_tmp as u64);
                self.op(0x20); uleb(&mut self.code, *some_tmp as u64);
                self.i32c(1); // Some
                field_op(&mut self.code, Type::Bool, 0, true);
                self.op(0x20); uleb(&mut self.code, *some_tmp as u64);
                self.op(0x20); uleb(&mut self.code, *value_tmp as u64);
                field_op(&mut self.code, value.ty, 8, true);
                self.op(0x20); uleb(&mut self.code, *some_tmp as u64);

                self.op(0x07); // catch private tag 0
                uleb(&mut self.code, 0);
                self.landing();
                self.op(0x1A); // drop i64 Error message (not a panic)
                self.depth_add(-1);
                self.i32c(16);
                self.call(self.l.helper(H_ALLOC));
                self.op(0x21); uleb(&mut self.code, *none_tmp as u64);
                self.op(0x20); uleb(&mut self.code, *none_tmp as u64);
                self.i32c(0); // None
                field_op(&mut self.code, Type::Bool, 0, true);
                self.op(0x20); uleb(&mut self.code, *none_tmp as u64);
                self.close(); // end try: one i32 Option record on stack
            }
            TExpr::AdtNew { tag, payload, tmp } => {
                self.i32c(16); // 8-aligned, fixed immutable tagged record
                self.call(self.l.helper(H_ALLOC));
                self.op(0x21); // local.set temp: each constructor allocates once
                uleb(&mut self.code, *tmp as u64);
                self.op(0x20);
                uleb(&mut self.code, *tmp as u64);
                self.i32c(*tag as i32);
                field_op(&mut self.code, Type::Bool, 0, true);
                if let Some(payload) = payload {
                    self.op(0x20);
                    uleb(&mut self.code, *tmp as u64);
                    self.expr(payload);
                    field_op(&mut self.code, payload.ty, 8, true);
                }
                self.op(0x20);
                uleb(&mut self.code, *tmp as u64);
            }
            TExpr::AdtIs { obj, tag } => {
                self.expr(obj);
                field_op(&mut self.code, Type::Bool, 0, false);
                self.i32c(*tag as i32);
                self.op(0x46); // i32.eq
            }
            TExpr::AdtPayload(obj) => {
                self.expr(obj);
                field_op(&mut self.code, v.ty, 8, false);
            },
            TExpr::AdtPropagate { source, tmp, success_tag } => {
                // Source (and all of its effects) is evaluated exactly once.
                self.expr(source);
                self.op(0x21); // local.set tagged pointer
                uleb(&mut self.code, *tmp as u64);
                self.op(0x20); // local.get
                uleb(&mut self.code, *tmp as u64);
                field_op(&mut self.code, Type::Bool, 0, false); // i32 tag
                self.i32c(*success_tag as i32);
                self.op(0x47); // i32.ne: failure
                self.open(0x04, 0x40, Frame::Other); // if (void)
                self.op(0x20);
                uleb(&mut self.code, *tmp as u64);
                self.op(0x0F); // return original Err/None tagged pointer
                self.close();
                self.op(0x20);
                uleb(&mut self.code, *tmp as u64);
                field_op(&mut self.code, Type::Int, 8, false); // i64 Ok/Some payload
            },
            TExpr::CollectionLoad { array, offset } => {
                self.expr(array);
                field_op(&mut self.code, Type::Int, *offset, false);
            }
            TExpr::FieldGet { obj, offset } => {
                self.expr(obj);
                field_op(&mut self.code, v.ty, *offset, false);
            }
            TExpr::StateFieldRead { obj, offset } => {
                if self.state_write_depth == 0 {
                    // Read an immutable scalar by value. The host owns the
                    // ticket, never the source code or the Wasm guest.
                    let slot = self.state_ticket_slot.expect("protected read ticket local");
                    self.get(0);
                    self.i32c(0); // read mode
                    self.call(self.l.import(Import::StateEnter));
                    self.set(slot);
                    self.expr(obj);
                    field_op(&mut self.code, v.ty, *offset, false);
                    // Result remains on Wasm stack while leave consumes the
                    // ticket, guaranteeing leave before the value escapes.
                    self.get(slot);
                    self.call(self.l.import(Import::StateLeave));
                } else {
                    self.expr(obj);
                    field_op(&mut self.code, v.ty, *offset, false);
                }
            }
            TExpr::GlobalGet(g) => {
                self.op(0x23);
                uleb(&mut self.code, (self.l.state_base + g) as u64);
            }
            TExpr::CollectionAlloc(n) | TExpr::Alloc(n) => {
                self.i32c(*n as i32);
                self.call(self.l.helper(H_ALLOC));
            }
            TExpr::Spawn(a) => {
                self.i32c(*a as i32);
                self.call(self.l.import(Import::ActorSpawn));
            }
            TExpr::Send { target, value } => {
                self.expr(target);
                self.expr(value);
                if value.ty == Type::Bool {
                    self.op(0xAD); // i64.extend_i32_u
                }
                self.call(self.l.import(Import::ActorSend));
            }
            TExpr::PrintObj { obj, tmp, pieces, newline } => {
                self.expr(obj);
                self.op(0x21);
                uleb(&mut self.code, *tmp as u64);
                for piece in pieces {
                    match piece {
                        PrintPiece::Str(offset, len) => {
                            self.i32c(*offset as i32);
                            self.i32c(*len as i32);
                            self.call(self.l.import(Import::PrintStr));
                        }
                        PrintPiece::Field(offset, Type::Str) => {
                            // (ptr, len) from two loads of the packed field
                            for half in [true, false] {
                                self.op(0x20);
                                uleb(&mut self.code, *tmp as u64);
                                field_op(&mut self.code, Type::Str, *offset, false);
                                if half {
                                    self.code.extend_from_slice(&[0x42, 32, 0x88]);
                                }
                                self.op(0xA7);
                            }
                            self.call(self.l.import(Import::PrintStr));
                        }
                        PrintPiece::Field(offset, ty) => {
                            self.op(0x20);
                            uleb(&mut self.code, *tmp as u64);
                            field_op(&mut self.code, *ty, *offset, false);
                            let imp = match ty {
                                Type::Int => Import::PrintI64,
                                Type::Float => Import::PrintF64,
                                _ => Import::PrintBool,
                            };
                            self.call(self.l.import(imp));
                        }
                    }
                }
                if *newline {
                    self.call(self.l.import(Import::PrintNewline));
                }
            }
        }
    }
}

/// Emitted source function, kept for the recursive-call post-pass.
struct FnMeta {
    /// Index into `bodies`.
    body: usize,
    /// Byte length of the locals declaration prefix of that body.
    decl_len: usize,
    /// Declared locals after the parameters (including runtime scratch).
    locals: Vec<Type>,
    params: u32,
    /// `[start, end)` byte ranges of user `call`s and their callee.
    calls: Vec<(usize, usize, u32)>,
    /// Exception landing pads (just after `catch` / `catch_all`).
    landings: Vec<usize>,
}

/// Bound every call that lies on a recursive cycle of the source call graph
/// with a guest call-depth counter (`global depth`), raising [`PANIC_STACK`]
/// before [`MAX_CALL_DEPTH`] live recursive frames. Non-recursive calls are
/// statically bounded and left untouched. Exception unwinding skips the
/// decrement after a call, so a function with landing pads saves the depth at
/// entry and restores it at each pad (the pad's live frames are exactly that
/// function and its callers). Wasm control flow uses relative label depths,
/// so splicing instructions into a body is position-independent. Returns
/// whether the depth global is needed.
fn bound_recursive_calls(bodies: &mut [Vec<u8>], meta: &[FnMeta], depth: u32) -> bool {
    let n = meta.len();
    let adj: Vec<Vec<usize>> = meta.iter().map(|m| {
        let mut v: Vec<usize> = m.calls.iter().map(|c| c.2 as usize).filter(|&c| c < n).collect();
        v.sort_unstable();
        v.dedup();
        v
    }).collect();
    // reach[s][t]: t is reachable from s by at least one call edge.
    let reach: Vec<Vec<bool>> = (0..n).map(|s| {
        let mut seen = vec![false; n];
        let mut work = adj[s].clone();
        while let Some(v) = work.pop() {
            if !seen[v] {
                seen[v] = true;
                work.extend(adj[v].iter().copied());
            }
        }
        seen
    }).collect();
    // Call u -> v recurses iff v can reach u again.
    let recursive: Vec<Vec<bool>> = meta.iter().enumerate().map(|(u, m)| {
        m.calls.iter().map(|c| (c.2 as usize) < n && reach[c.2 as usize][u]).collect()
    }).collect();
    if !recursive.iter().flatten().any(|&r| r) {
        return false;
    }

    let get = |c: &mut Vec<u8>| { c.push(0x23); uleb(c, depth as u64); };
    let set = |c: &mut Vec<u8>| { c.push(0x24); uleb(c, depth as u64); };
    let mut prelude = Vec::new();
    get(&mut prelude);
    prelude.push(0x41);
    sleb(&mut prelude, MAX_CALL_DEPTH as i64);
    prelude.push(0x4F); // i32.ge_u
    prelude.extend_from_slice(&[0x04, 0x40]);
    panic(&mut prelude, PANIC_STACK);
    prelude.push(0x0B);
    get(&mut prelude);
    prelude.extend_from_slice(&[0x41, 1, 0x6A]); // + 1
    set(&mut prelude);
    let mut postlude = Vec::new();
    get(&mut postlude);
    postlude.extend_from_slice(&[0x41, 1, 0x6B]); // - 1
    set(&mut postlude);

    for (m, rec) in meta.iter().zip(&recursive) {
        let save_slot = m.params + m.locals.len() as u32;
        let save = !m.landings.is_empty();
        // Insertion order for equal offsets is the order below.
        let mut ins: Vec<(usize, Vec<u8>)> = Vec::new();
        if save {
            let mut prologue = Vec::new();
            get(&mut prologue);
            prologue.push(0x21); // local.set
            uleb(&mut prologue, save_slot as u64);
            ins.push((m.decl_len, prologue));
        }
        for (&(start, end, _), &r) in m.calls.iter().zip(rec) {
            if r {
                ins.push((start, prelude.clone()));
                ins.push((end, postlude.clone()));
            }
        }
        if save {
            for &pad in &m.landings {
                let mut restore = vec![0x20]; // local.get
                uleb(&mut restore, save_slot as u64);
                set(&mut restore);
                ins.push((pad, restore));
            }
        }
        if ins.is_empty() {
            continue;
        }
        ins.sort_by_key(|(at, _)| *at); // stable: keeps equal-offset order
        let body = &mut bodies[m.body];
        for (at, bytes) in ins.into_iter().rev() {
            body.splice(at..at, bytes);
        }
        if save {
            let mut locals = m.locals.clone();
            locals.push(Type::Bool); // i32 saved call depth, after every existing local
            body.splice(0..m.decl_len, locals_decl(&locals));
        }
    }
    true
}

/// panic: `i32.const code; global.set $panic_code; unreachable`
fn panic(c: &mut Vec<u8>, code: i32) {
    c.push(0x41);
    sleb(c, code as i64);
    c.extend_from_slice(&[0x24, 0x00, 0x00]);
}

fn helper_bodies() -> Vec<(Sig, Vec<u8>, Vec<u8>)> {
    // (signature, extra locals as (count,type) pairs encoded, code)
    let bin = Sig(vec![I64, I64], vec![I64]);
    let r_local = vec![1u8, 1, I64]; // 1 group: 1 x i64 (local 2)
    let no_locals = vec![0u8];
    let mut v = Vec::new();

    // add: r = a + b; overflow iff ((a ^ r) & (b ^ r)) < 0
    let mut c = vec![
        0x20, 0, 0x20, 1, 0x7C, 0x21, 2, 0x20, 0, 0x20, 2, 0x85, 0x20, 1, 0x20, 2, 0x85, 0x83, 0x42, 0, 0x53, 0x04, 0x40,
    ];
    panic(&mut c, PANIC_OVERFLOW);
    c.extend_from_slice(&[0x0B, 0x20, 2, 0x0B]);
    v.push((bin.clone(), r_local.clone(), c));

    // sub: r = a - b; overflow iff ((a ^ b) & (a ^ r)) < 0
    let mut c = vec![
        0x20, 0, 0x20, 1, 0x7D, 0x21, 2, 0x20, 0, 0x20, 1, 0x85, 0x20, 0, 0x20, 2, 0x85, 0x83, 0x42, 0, 0x53, 0x04, 0x40,
    ];
    panic(&mut c, PANIC_OVERFLOW);
    c.extend_from_slice(&[0x0B, 0x20, 2, 0x0B]);
    v.push((bin.clone(), r_local.clone(), c));

    // mul
    let mut c = vec![0x20, 0, 0x42, 0x7F, 0x51, 0x04, 0x40]; // if a == -1
    c.extend_from_slice(&[0x20, 1]);
    c.push(0x42);
    sleb(&mut c, i64::MIN);
    c.extend_from_slice(&[0x51, 0x04, 0x40]); // if b == MIN
    panic(&mut c, PANIC_OVERFLOW);
    c.extend_from_slice(&[0x0B, 0x42, 0, 0x20, 1, 0x7D, 0x0F, 0x0B]); // return 0 - b
    c.extend_from_slice(&[0x20, 0, 0x50, 0x04, 0x40, 0x42, 0, 0x0F, 0x0B]); // if a == 0 return 0
    c.extend_from_slice(&[0x20, 0, 0x20, 1, 0x7E, 0x21, 2]); // r = a * b
    c.extend_from_slice(&[0x20, 2, 0x20, 0, 0x7F, 0x20, 1, 0x52, 0x04, 0x40]); // if r / a != b
    panic(&mut c, PANIC_OVERFLOW);
    c.extend_from_slice(&[0x0B, 0x20, 2, 0x0B]);
    v.push((bin.clone(), r_local, c));

    // neg
    let mut c = vec![0x20, 0, 0x42];
    sleb(&mut c, i64::MIN);
    c.extend_from_slice(&[0x51, 0x04, 0x40]);
    panic(&mut c, PANIC_OVERFLOW);
    c.extend_from_slice(&[0x0B, 0x42, 0, 0x20, 0, 0x7D, 0x0B]);
    v.push((Sig(vec![I64], vec![I64]), no_locals.clone(), c));

    v
}

/// `alloc(size: i32) -> i32`: bump-allocate from `heap_ptr`; panic 3 when the
/// fixed memory is exhausted. Objects are never freed (no GC in this subset).
fn alloc_body(heap_global: u32) -> (Sig, Vec<u8>, Vec<u8>) {
    let limit = (HEAP_PAGES * 65536) as i64;
    let mut c = vec![0x23];
    uleb(&mut c, heap_global as u64);
    c.extend_from_slice(&[0x21, 1, 0x20, 1, 0x20, 0, 0x6A, 0x41]); // p = heap; p + size
    sleb(&mut c, limit);
    c.extend_from_slice(&[0x4B, 0x04, 0x40]); // if (p + size) >u limit
    panic(&mut c, PANIC_HEAP);
    c.extend_from_slice(&[0x0B, 0x20, 1, 0x20, 0, 0x6A, 0x24]); // heap = p + size
    uleb(&mut c, heap_global as u64);
    c.extend_from_slice(&[0x20, 1, 0x0B]); // return p
    (Sig(vec![I32], vec![I32]), vec![1u8, 1, I32], c)
}

/// Push `(ptr: i32, len: i32)` of the packed string in local `l`.
fn str_parts(c: &mut Vec<u8>, l: u32) {
    c.push(0x20);
    uleb(c, l as u64);
    c.extend_from_slice(&[0x42, 32, 0x88, 0xA7]); // (v >> 32) as i32
    c.push(0x20);
    uleb(c, l as u64);
    c.push(0xA7); // v as i32
}

fn ptr_of(c: &mut Vec<u8>, l: u8) {
    c.extend_from_slice(&[0x20, l, 0x42, 32, 0x88, 0xA7]);
}
fn len_of(c: &mut Vec<u8>, l: u8) {
    c.extend_from_slice(&[0x20, l, 0xA7]);
}
/// `if (len t > len s) return 0`
fn guard_longer(c: &mut Vec<u8>, s: u8, t: u8) {
    len_of(c, t);
    len_of(c, s);
    c.extend_from_slice(&[0x4B, 0x04, 0x40, 0x41, 0, 0x0F, 0x0B]);
}

/// Byte-exact string helpers over `offset << 32 | len` values. `base` is
/// the function index of `S_BYTES_EQ`, which the others call.
fn string_helpers(base: u32, alloc: Option<u32>) -> Vec<(Sig, Vec<u8>, Vec<u8>)> {
    let call_eq = |c: &mut Vec<u8>| {
        c.push(0x10);
        uleb(c, base as u64);
    };
    let pred = Sig(vec![I64, I64], vec![I32]);
    let mut v = Vec::new();

    // bytes_eq(p: i32, q: i32, n: i32) -> i32; local 3 = i
    let c = vec![
        0x02, 0x40, 0x03, 0x40, // block loop
        0x20, 3, 0x20, 2, 0x4F, 0x0D, 1, // i >= n -> exit
        0x20, 0, 0x20, 3, 0x6A, 0x2D, 0, 0, // p[i]
        0x20, 1, 0x20, 3, 0x6A, 0x2D, 0, 0, // q[i]
        0x47, 0x04, 0x40, 0x41, 0, 0x0F, 0x0B, // differ -> return 0
        0x20, 3, 0x41, 1, 0x6A, 0x21, 3, 0x0C, 0, // i++; continue
        0x0B, 0x0B, 0x41, 1, 0x0B,
    ];
    v.push((Sig(vec![I32, I32, I32], vec![I32]), vec![1, 1, I32], c));

    // str_eq(a, b)
    let mut c = Vec::new();
    len_of(&mut c, 0);
    len_of(&mut c, 1);
    c.extend_from_slice(&[0x47, 0x04, 0x40, 0x41, 0, 0x0F, 0x0B]);
    ptr_of(&mut c, 0);
    ptr_of(&mut c, 1);
    len_of(&mut c, 0);
    call_eq(&mut c);
    c.push(0x0B);
    v.push((pred.clone(), vec![0], c));

    // starts_with(s, t)
    let mut c = Vec::new();
    guard_longer(&mut c, 0, 1);
    ptr_of(&mut c, 0);
    ptr_of(&mut c, 1);
    len_of(&mut c, 1);
    call_eq(&mut c);
    c.push(0x0B);
    v.push((pred.clone(), vec![0], c));

    // ends_with(s, t): compare at ptr s + len s - len t
    let mut c = Vec::new();
    guard_longer(&mut c, 0, 1);
    ptr_of(&mut c, 0);
    len_of(&mut c, 0);
    c.push(0x6A);
    len_of(&mut c, 1);
    c.push(0x6B);
    ptr_of(&mut c, 1);
    len_of(&mut c, 1);
    call_eq(&mut c);
    c.push(0x0B);
    v.push((pred.clone(), vec![0], c));

    // contains_literal(s, t); local 2 = i, tries i = 0 ..= len s - len t
    let mut c = Vec::new();
    guard_longer(&mut c, 0, 1);
    c.extend_from_slice(&[0x02, 0x40, 0x03, 0x40, 0x20, 2]);
    len_of(&mut c, 0);
    len_of(&mut c, 1);
    c.extend_from_slice(&[0x6B, 0x4B, 0x0D, 1]); // i > len s - len t -> exit
    ptr_of(&mut c, 0);
    c.extend_from_slice(&[0x20, 2, 0x6A]);
    ptr_of(&mut c, 1);
    len_of(&mut c, 1);
    call_eq(&mut c);
    c.extend_from_slice(&[0x04, 0x40, 0x41, 1, 0x0F, 0x0B]);
    c.extend_from_slice(&[0x20, 2, 0x41, 1, 0x6A, 0x21, 2, 0x0C, 0, 0x0B, 0x0B, 0x41, 0, 0x0B]);
    v.push((pred, vec![1, 1, I32], c));

    // trim(s) -> string: Java String.trim drops chars <= U+0020 at both
    // ends; in UTF-8 those are exactly the bytes <= 0x20. locals 1 = start, 2 = end
    let mut c = Vec::new();
    ptr_of(&mut c, 0);
    c.extend_from_slice(&[0x22, 1]);
    len_of(&mut c, 0);
    c.extend_from_slice(&[0x6A, 0x21, 2]);
    c.extend_from_slice(&[
        0x02, 0x40, 0x03, 0x40, 0x20, 1, 0x20, 2, 0x4F, 0x0D, 1, // start >= end
        0x20, 1, 0x2D, 0, 0, 0x41, 0x20, 0x4B, 0x0D, 1, // byte > ' ' -> stop
        0x20, 1, 0x41, 1, 0x6A, 0x21, 1, 0x0C, 0, 0x0B, 0x0B,
    ]);
    c.extend_from_slice(&[
        0x02, 0x40, 0x03, 0x40, 0x20, 2, 0x20, 1, 0x4D, 0x0D, 1, // end <= start
        0x20, 2, 0x41, 1, 0x6B, 0x2D, 0, 0, 0x41, 0x20, 0x4B, 0x0D, 1, // byte before end > ' '
        0x20, 2, 0x41, 1, 0x6B, 0x21, 2, 0x0C, 0, 0x0B, 0x0B,
    ]);
    c.extend_from_slice(&[
        0x20, 1, 0xAD, 0x42, 32, 0x86, // (start as i64) << 32
        0x20, 2, 0x20, 1, 0x6B, 0xAD, 0x84, // | (end - start)
        0x0B,
    ]);
    v.push((Sig(vec![I64], vec![I64]), vec![1, 2, I32], c));

    // concat(a, b) -> string; locals 2 = p, 3 = i, 4 = len a, 5 = len b.
    // Without a heap (no concatenation in the program) the body only traps.
    let mut c = Vec::new();
    if let Some(alloc) = alloc {
        len_of(&mut c, 0);
        c.extend_from_slice(&[0x21, 4]);
        len_of(&mut c, 1);
        c.extend_from_slice(&[0x21, 5]);
        // p = alloc((la + lb + 7) & -8): keep the bump pointer 8-aligned for objects
        c.extend_from_slice(&[0x20, 4, 0x20, 5, 0x6A, 0x41, 7, 0x6A, 0x41, 0x78, 0x71, 0x10]);
        uleb(&mut c, alloc as u64);
        c.extend_from_slice(&[0x21, 2]);
        for (src, dst_extra) in [(0u8, false), (1u8, true)] {
            let lim = if src == 0 { 4 } else { 5 };
            c.extend_from_slice(&[0x41, 0, 0x21, 3, 0x02, 0x40, 0x03, 0x40, 0x20, 3, 0x20, lim, 0x4F, 0x0D, 1]);
            c.extend_from_slice(&[0x20, 2]);
            if dst_extra {
                c.extend_from_slice(&[0x20, 4, 0x6A]);
            }
            c.extend_from_slice(&[0x20, 3, 0x6A]);
            ptr_of(&mut c, src);
            c.extend_from_slice(&[0x20, 3, 0x6A, 0x2D, 0, 0, 0x3A, 0, 0]); // dst[i] = src[i]
            c.extend_from_slice(&[0x20, 3, 0x41, 1, 0x6A, 0x21, 3, 0x0C, 0, 0x0B, 0x0B]);
        }
        c.extend_from_slice(&[0x20, 2, 0xAD, 0x42, 32, 0x86, 0x20, 4, 0x20, 5, 0x6A, 0xAD, 0x84, 0x0B]);
    } else {
        c.extend_from_slice(&[0x00, 0x0B]);
    }
    v.push((Sig(vec![I64, I64], vec![I64]), vec![1, 4, I32], c));

    // cmp(a, b) -> int: sign of Java String.compareTo. UTF-8 byte order is
    // code point order; UTF-16 order differs only between a supplementary
    // character (UTF-8 lead >= 0xF0) and U+E000..U+FFFF (lead 0xEE/0xEF),
    // so that case flips. locals 2 = n, 3 = i, 4 = lead a, 5 = lead b, 6 = k
    let byte_at = |c: &mut Vec<u8>, s: u8, l: u8| {
        ptr_of(c, s);
        c.extend_from_slice(&[0x20, l, 0x6A, 0x2D, 0, 0]);
    };
    let k32 = |c: &mut Vec<u8>, v: i64| {
        c.push(0x41);
        sleb(c, v);
    };
    let mut c = Vec::new();
    len_of(&mut c, 0);
    len_of(&mut c, 1);
    len_of(&mut c, 0);
    len_of(&mut c, 1);
    c.extend_from_slice(&[0x49, 0x1B, 0x21, 2]); // n = min(la, lb)
    c.extend_from_slice(&[0x02, 0x40, 0x03, 0x40, 0x20, 3, 0x20, 2, 0x4F, 0x0D, 1]);
    byte_at(&mut c, 0, 3);
    byte_at(&mut c, 1, 3);
    c.extend_from_slice(&[0x47, 0x0D, 1, 0x20, 3, 0x41, 1, 0x6A, 0x21, 3, 0x0C, 0, 0x0B, 0x0B]);
    // equal prefix of length n: the shorter string is smaller
    c.extend_from_slice(&[0x20, 3, 0x20, 2, 0x46, 0x04, 0x40]);
    len_of(&mut c, 0);
    len_of(&mut c, 1);
    c.extend_from_slice(&[0x49, 0x04, 0x40, 0x42, 0x7F, 0x0F, 0x0B]);
    len_of(&mut c, 0);
    len_of(&mut c, 1);
    c.extend_from_slice(&[0x4B, 0x04, 0x40, 0x42, 1, 0x0F, 0x0B, 0x42, 0, 0x0F, 0x0B]);
    // k = start of the character holding byte i (shared prefix, so the same in both)
    c.extend_from_slice(&[0x20, 3, 0x21, 6, 0x02, 0x40, 0x03, 0x40, 0x20, 6, 0x45, 0x0D, 1]);
    byte_at(&mut c, 0, 6);
    k32(&mut c, 0xC0);
    c.push(0x71);
    k32(&mut c, 0x80);
    c.extend_from_slice(&[0x47, 0x0D, 1, 0x20, 6, 0x41, 1, 0x6B, 0x21, 6, 0x0C, 0, 0x0B, 0x0B]);
    byte_at(&mut c, 0, 6);
    c.extend_from_slice(&[0x21, 4]);
    byte_at(&mut c, 1, 6);
    c.extend_from_slice(&[0x21, 5]);
    for (x, y) in [(4u8, 5u8), (5, 4)] {
        c.extend_from_slice(&[0x20, x]);
        k32(&mut c, 0xF0);
        c.extend_from_slice(&[0x4F, 0x20, y]);
        k32(&mut c, 0xEE);
        c.extend_from_slice(&[0x4F, 0x71, 0x20, y]);
        k32(&mut c, 0xF0);
        c.extend_from_slice(&[0x49, 0x71]);
    }
    c.push(0x72); // flip?
    c.extend_from_slice(&[0x04, I64, 0x42, 1, 0x42, 0x7F]);
    byte_at(&mut c, 0, 3);
    byte_at(&mut c, 1, 3);
    c.extend_from_slice(&[0x49, 0x1B, 0x05, 0x42, 0x7F, 0x42, 1]);
    byte_at(&mut c, 0, 3);
    byte_at(&mut c, 1, 3);
    c.extend_from_slice(&[0x49, 0x1B, 0x0B, 0x0B]);
    v.push((Sig(vec![I64, I64], vec![I64]), vec![1, 5, I32], c));
    debug_assert_eq!(v.len() as u32, STRING_HELPERS);
    v
}

fn locals_decl(types: &[Type]) -> Vec<u8> {
    let mut groups: Vec<(u32, u8)> = Vec::new();
    for t in types {
        let b = vt(*t).expect("value local");
        match groups.last_mut() {
            Some((n, ty)) if *ty == b => *n += 1,
            _ => groups.push((1, b)),
        }
    }
    let mut out = Vec::new();
    uleb(&mut out, groups.len() as u64);
    for (n, t) in groups {
        uleb(&mut out, n as u64);
        out.push(t);
    }
    out
}

pub fn emit(p: &TProgram) -> Vec<u8> {
    let heap_global = 1;
    let str_base = if p.heap { H_ALLOC + 1 } else { H_ALLOC };
    let layout = Layout {
        imports: p.imports.clone(),
        helpers: str_base + if p.strings { STRING_HELPERS } else { 0 },
        str_base,
        state_base: 1 + u32::from(p.heap),
        gen_free_global: (!p.generators.is_empty()).then_some(
            1 + u32::from(p.heap) + p.globals.len() as u32
        ),
        gen_first_func: p.funcs.len() as u32,
        catch_depth: p.catch_depth.then_some(
            1 + u32::from(p.heap) + p.globals.len() as u32 + u32::from(!p.generators.is_empty())
        ),
        raise_tag: p.raise_tag,
    };
    let mut types = Types(Vec::new());

    let mut import_sec = Vec::new();
    uleb(&mut import_sec, p.imports.len() as u64);
    for imp in &p.imports {
        let sig = match imp {
            Import::PrintI64 => Sig(vec![I64], vec![]),
            Import::PrintBool => Sig(vec![I32], vec![]),
            Import::PrintStr => Sig(vec![I32, I32], vec![]),
            Import::PrintNewline => Sig(vec![], vec![]),
            Import::PrintF64 => Sig(vec![F64], vec![]),
            Import::ActorSpawn => Sig(vec![I32], vec![I32]),
            Import::ActorSend => Sig(vec![I32, I64], vec![]),
            Import::StateRegister => Sig(vec![I32], vec![]),
            Import::StateEnter => Sig(vec![I32, I32], vec![I64]),
            Import::StateLeave => Sig(vec![I64], vec![]),
        };
        name(&mut import_sec, "atto");
        name(&mut import_sec, imp.name());
        import_sec.push(0x00);
        uleb(&mut import_sec, types.idx(sig) as u64);
    }

    let mut func_types = Vec::new();
    let mut bodies = Vec::new();
    let mut helpers = helper_bodies();
    if p.heap {
        helpers.push(alloc_body(heap_global));
    }
    if p.strings {
        let alloc = p.heap.then(|| layout.helper(H_ALLOC));
        helpers.extend(string_helpers(layout.str_helper(S_BYTES_EQ), alloc));
    }
    for (sig, locals, code) in helpers {
        func_types.push(types.idx(sig));
        let mut b = locals;
        b.extend(code);
        bodies.push(b);
    }
    let main_void = p.funcs[p.main as usize].ret == Type::Void;
    let mut fn_meta: Vec<FnMeta> = Vec::with_capacity(p.funcs.len());
    for (i, f) in p.funcs.iter().enumerate() {
        let params: Vec<u8> = f.params.iter().map(|t| vt(*t).unwrap()).collect();
        let is_void_main = i as u32 == p.main && main_void;
        let results: Vec<u8> = if is_void_main { vec![I64] } else { vt(f.ret).into_iter().collect() };
        func_types.push(types.idx(Sig(params, results)));
        // Reserve one host-ticket local only in state-enabled modules.
        // The ticket never reaches user source or escapes into other methods.
        let state_hooks = p.imports.contains(&Import::StateEnter);
        let mut locals = f.locals.clone();
        if state_hooks { locals.push(Type::Int); }
        let mut e = Emit {
            l: &layout,
            code: locals_decl(&locals),
            frames: Vec::new(),
            void_main: is_void_main,
            active_iterators: Vec::new(),
            state_ticket_slot: state_hooks.then_some((f.params.len()+f.locals.len()) as u32),
            state_write_depth: 0,
            uw: None,
            in_recover: false,
            calls: Vec::new(),
            landings: Vec::new(),
        };
        if let Some(gen_id) = p.generators.iter().position(|g| g.function == i as u32) {
            // Creator is lazy: allocate a 56-byte checked continuation frame
            // and return its generation-fenced handle. No body runs here.
            e.i32c(gen_id as i32);
            if f.params.len() == 1 { e.get(0); }
            else { e.i64c(0); }
            e.call(layout.func(layout.gen_first_func));
            e.op(0x0F); // return the generation-fenced handle; never hit unreachable
        } else if let Some(TStmt::UnwindFrame { ret, saved, msg, kind, pending }) = f.body.first() {
            e.uw = Some((*ret, *saved, *msg, *kind, *pending));
            e.unwind_body(&f.body, is_void_main, f.ret);
        } else {
            e.stmts(&f.body);
        }
        if e.uw.is_some() {
            // unwind_body left the snapshotted result on the stack
        } else if is_void_main {
            e.i64c(0);
        } else if f.ret != Type::Void {
            e.op(0x00); // unreachable: definite-return analysis proved every path returns
        }
        e.op(0x0B);
        fn_meta.push(FnMeta {
            body: bodies.len(),
            decl_len: locals_decl(&locals).len(),
            locals: locals.clone(),
            params: f.params.len() as u32,
            calls: std::mem::take(&mut e.calls),
            landings: std::mem::take(&mut e.landings),
        });
        bodies.push(e.code);
    }

    // Logical stack quota (spec chapter 25): only calls on a recursive cycle
    // can grow the stack without a static bound, so only those are counted.
    // Programs without recursion keep byte-identical output.
    let depth_global = 1 + u32::from(p.heap) + p.globals.len() as u32
        + u32::from(!p.generators.is_empty()) + u32::from(p.catch_depth);
    let depth_used = bound_recursive_calls(&mut bodies, &fn_meta, depth_global);

    // Runtime ops after source functions preserve every existing index.
    if !p.generators.is_empty() {
        for (sig, code) in generator_runtime::bodies(p, &layout) {
            func_types.push(types.idx(sig));
            bodies.push(code);
        }
    }

    // actor_init(type) / actor_receive(type, value, sequence) dispatchers
    let has_actors = !p.actors.is_empty();
    let actor_init_idx = layout.func(p.funcs.len() as u32
        + if p.generators.is_empty() { 0 } else { 4 });
    if has_actors {
        func_types.push(types.idx(Sig(vec![I32], vec![])));
        let mut e = Emit {
            l: &layout,
            code: vec![0],
            frames: Vec::new(),
            void_main: false,
            active_iterators: Vec::new(),
            state_ticket_slot: None,
            state_write_depth: 0,
            uw: None,
            in_recover: false,
            calls: Vec::new(),
            landings: Vec::new(),
        };
        for (ai, a) in p.actors.iter().enumerate() {
            e.code.extend_from_slice(&[0x20, 0]);
            e.i32c(ai as i32);
            e.op(0x46);
            e.open(0x04, 0x40, Frame::Other);
            for (g, init) in &a.inits {
                e.stmt(&TStmt::GlobalSet(*g, init.clone()));
            }
            e.op(0x0F);
            e.close();
        }
        e.op(0x00); // unknown actor type
        e.op(0x0B);
        bodies.push(e.code);

        func_types.push(types.idx(Sig(vec![I32, I64, I64], vec![])));
        let mut c = vec![0];
        if depth_used {
            // Each receive invocation starts its own logical stack at depth 0.
            c.extend_from_slice(&[0x41, 0, 0x24]);
            uleb(&mut c, depth_global as u64);
        }
        for (ai, a) in p.actors.iter().enumerate() {
            if let Some(r) = a.receive {
                c.extend_from_slice(&[0x20, 0, 0x41]);
                sleb(&mut c, ai as i64);
                c.extend_from_slice(&[0x46, 0x04, 0x40, 0x20, 1, 0x20, 2, 0x10]);
                uleb(&mut c, layout.func(r) as u64);
                c.extend_from_slice(&[0x0F, 0x0B]);
            }
        }
        c.extend_from_slice(&[0x00, 0x0B]); // no receive handler for this type
        bodies.push(c);
    }

    // The tag has no JS import/export. Each instance gets its own identity,
    // so no host exception or foreign guest tag can be forged as an ordinary
    // Atto throw. Unaffected modules retain their original section layout.
    let guest_error_tag_type = p.guest_eh.then(|| types.idx(Sig(vec![I64], vec![])));
    let mut out = vec![0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00];

    let mut type_sec = Vec::new();
    uleb(&mut type_sec, types.0.len() as u64);
    for Sig(ps, rs) in &types.0 {
        type_sec.push(0x60);
        uleb(&mut type_sec, ps.len() as u64);
        type_sec.extend(ps);
        uleb(&mut type_sec, rs.len() as u64);
        type_sec.extend(rs);
    }
    section(&mut out, 1, type_sec);
    if !p.imports.is_empty() {
        section(&mut out, 2, import_sec);
    }

    let mut fsec = Vec::new();
    uleb(&mut fsec, func_types.len() as u64);
    for t in &func_types {
        uleb(&mut fsec, *t as u64);
    }
    section(&mut out, 3, fsec);

    let has_memory = !p.data.is_empty() || p.heap || p.strings || has_actors;
    if has_memory {
        // Fixed and non-growable: strings, the object heap, or a private
        // 64 KiB actor memory even for scalar-only actors.
        let pages = if p.heap { HEAP_PAGES } else { 1 };
        let mut m = vec![1, 0x01];
        uleb(&mut m, pages as u64);
        uleb(&mut m, pages as u64);
        section(&mut out, 5, m);
    }

    if let Some(tag_ty) = guest_error_tag_type {
        // Legacy WebAssembly EH: section 13 is ordered between memory (5)
        // and globals (6). One private tag: (i64 error_message) -> ().
        // Tag 1 (same signature) is the escalated `raise` failure.
        let count = 1 + u8::from(p.raise_tag);
        let mut tags = vec![count];
        for _ in 0..count {
            tags.push(0); // attribute=exception
            uleb(&mut tags, tag_ty as u64);
        }
        section(&mut out, 13, tags);
    }

    // global 0: mut i32 panic_code = 0; then heap_ptr; then actor state
    let mut gsec = Vec::new();
    uleb(&mut gsec, 1 + u64::from(p.heap) + p.globals.len() as u64
        + u64::from(!p.generators.is_empty())
        + u64::from(p.catch_depth)
        + u64::from(depth_used));
    gsec.extend_from_slice(&[I32, 0x01, 0x41, 0, 0x0B]);
    if p.heap {
        let heap_start = ((p.data.len() as i64 + 7) & !7)
            .max(if p.generators.is_empty() { 0 } else { 8 });
        gsec.extend_from_slice(&[I32, 0x01, 0x41]);
        sleb(&mut gsec, heap_start);
        gsec.push(0x0B);
    }
    for t in &p.globals {
        let ty = vt(*t).expect("value global");
        gsec.extend_from_slice(&[ty, 0x01, if ty == I64 { 0x42 } else { 0x41 }, 0, 0x0B]);
    }
    if !p.generators.is_empty() {
        gsec.extend_from_slice(&[I32, 0x01, 0x41, 0, 0x0B]); // frame freelist head
    }
    if p.catch_depth {
        gsec.extend_from_slice(&[I32, 0x01, 0x41, 0, 0x0B]); // active catch/trap depth
    }
    if depth_used {
        gsec.extend_from_slice(&[I32, 0x01, 0x41, 0, 0x0B]); // live recursive call depth
    }
    section(&mut out, 6, gsec);

    let mut exp = Vec::new();
    uleb(&mut exp, 2 + u64::from(has_memory) + if has_actors { 2 } else { 0 });
    name(&mut exp, "main");
    exp.push(0x00);
    uleb(&mut exp, layout.func(p.main) as u64);
    name(&mut exp, "panic_code");
    exp.push(0x03);
    uleb(&mut exp, 0);
    if has_memory {
        name(&mut exp, "memory");
        exp.push(0x02);
        uleb(&mut exp, 0);
    }
    if has_actors {
        name(&mut exp, "actor_init");
        exp.push(0x00);
        uleb(&mut exp, actor_init_idx as u64);
        name(&mut exp, "actor_receive");
        exp.push(0x00);
        uleb(&mut exp, actor_init_idx as u64 + 1);
    }
    section(&mut out, 7, exp);

    let mut code_sec = Vec::new();
    uleb(&mut code_sec, bodies.len() as u64);
    for b in bodies {
        uleb(&mut code_sec, b.len() as u64);
        code_sec.extend(b);
    }
    section(&mut out, 10, code_sec);

    if !p.data.is_empty() {
        let mut d = vec![1, 0x00, 0x41, 0x00, 0x0B];
        uleb(&mut d, p.data.len() as u64);
        d.extend_from_slice(&p.data);
        section(&mut out, 11, d);
    }

    // custom "name" section: function names for readable traps and stack traces
    let mut names = Vec::new();
    let mut helper_names = vec!["atto.checked_add", "atto.checked_sub", "atto.checked_mul", "atto.checked_neg"];
    if p.heap {
        helper_names.push("atto.alloc");
    }
    if p.strings {
        helper_names.extend([
            "atto.bytes_eq",
            "atto.str_eq",
            "atto.str_starts_with",
            "atto.str_ends_with",
            "atto.str_contains",
            "atto.str_trim",
            "atto.str_concat",
            "atto.str_cmp",
        ]);
    }
    let mut all: Vec<String> = p
        .imports
        .iter()
        .map(|i| format!("atto.{}", i.name()))
        .chain(helper_names.into_iter().map(String::from))
        .chain(p.funcs.iter().map(|f| f.name.clone()))
        .collect();
    if !p.generators.is_empty() {
        all.extend([
            "atto.generator_new", "atto.generator_check_ptr",
            "atto.generator_next", "atto.generator_close",
        ].into_iter().map(String::from));
    }
    if has_actors {
        all.push("atto.actor_init".into());
        all.push("atto.actor_receive".into());
    }
    let mut sub = Vec::new();
    uleb(&mut sub, all.len() as u64);
    for (i, n) in all.iter().enumerate() {
        uleb(&mut sub, i as u64);
        name(&mut sub, n);
    }
    name(&mut names, "name");
    names.push(1);
    uleb(&mut names, sub.len() as u64);
    names.extend(sub);
    section(&mut out, 0, names);

    if has_actors {
        // custom "atto.actors": vec(name) indexed by actor type
        let mut a = Vec::new();
        name(&mut a, "atto.actors");
        uleb(&mut a, p.actors.len() as u64);
        for actor in &p.actors {
            name(&mut a, &actor.name);
        }
        section(&mut out, 0, a);
    }
    out
}
