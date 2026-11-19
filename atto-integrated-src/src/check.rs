//! Name resolution and type checking: AST -> typed IR.
//!
//! Rules follow the reference compilers and the spec:
//! * `int` is a signed 64-bit integer (spec 17, LLVM `i64`), arithmetic is
//!   checked and overflow panics (spec 17 TARGET (decided); LLVM traps).
//! * conditions must be `bool`; there is no truthiness (spec 17).
//! * `val`/`const` bindings and parameters are immutable; `let` and
//!   `type mut name` parameters are reassignable (grammar.ebnf, Java).
//! * top-level overload identity is name + arity (Java reference).
//! * a non-void function must return on every path (Java reference).
//! * `int / int` is rejected: its result type is undecided (spec S-25; Java
//!   yields `float`, LLVM rejects).

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::*;
use crate::diag::{Diagnostic, Pos};

mod generator_lower;
pub mod lambda_types;
mod direct_lambda;
pub mod callable_ir;

pub const MAX_LOCALS: usize = 1024;
/// Fixed-size i64 continuation slots; all guest generator frames use one size.
pub const GENERATOR_MAX_LIVE_I64_LOCALS: usize = 16;
pub const MAX_STRING_DATA: usize = 32 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Builtin {
    And,
    Or,
    Xor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Import {
    PrintI64,
    PrintBool,
    PrintStr,
    PrintNewline,
    /// `print_f64(f64)`: the host renders it like Java `Double.toString`
    PrintF64,
    /// `actor_spawn(type: i32) -> i32`: start one actor, return its reference
    ActorSpawn,
    /// `actor_send(ref: i32, value: i64)`: enqueue one message
    ActorSend,
    /// Private Worker-owned state-container creation/lexical admission hooks.
    StateRegister,
    StateEnter,
    StateLeave,
}

impl Import {
    pub const ALL: [Import; 10] = [
        Import::PrintI64,
        Import::PrintBool,
        Import::PrintStr,
        Import::PrintNewline,
        Import::PrintF64,
        Import::ActorSpawn,
        Import::ActorSend,
        Import::StateRegister,
        Import::StateEnter,
        Import::StateLeave,
    ];
    pub fn name(self) -> &'static str {
        match self {
            Import::PrintI64 => "print_i64",
            Import::PrintBool => "print_bool",
            Import::PrintStr => "print_str",
            Import::PrintNewline => "print_newline",
            Import::PrintF64 => "print_f64",
            Import::ActorSpawn => "actor_spawn",
            Import::ActorSend => "actor_send",
            Import::StateRegister => "state_register",
            Import::StateEnter => "state_enter",
            Import::StateLeave => "state_leave",
        }
    }
}

/// One step of printing an object as `Name{a=1, b=true}` (Java format).
#[derive(Clone, Debug)]
pub enum PrintPiece {
    /// string data at `(offset, len)`
    Str(u32, u32),
    /// field at byte offset, printed as int or bool
    Field(u32, Type),
}

/// String operations lowered to module helpers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StrOp {
    Eq,
    StartsWith,
    EndsWith,
    Contains,
    Trim,
    /// `a + b`: allocates the result on the bump heap
    Concat,
    /// Java `String.compareTo` sign (-1, 0, 1) as an int
    Cmp,
}

#[derive(Clone, Debug)]
pub enum TExpr {
    I64(i64),
    F64(f64),
    Bool(bool),
    /// string value `offset << 32 | len` into the module's string data
    StrConst(u32, u32),
    /// `int` widened to `float` (Java numeric promotion)
    IntToFloat(Box<TE>),
    FNeg(Box<TE>),
    /// string helper call; `Eq` and the predicates take `arg`, `Trim` does not
    Str(StrOp, Box<TE>, Option<Box<TE>>),
    /// print a string value; `tmp` is an i64 scratch local holding it
    PrintStrVal {
        value: Box<TE>,
        tmp: u32,
        newline: bool,
    },
    Local(u32),
    Neg(Box<TE>),
    Not(Box<TE>),
    /// operand type is the type of `l`
    Bin(BinOp, Box<TE>, Box<TE>),
    Ternary(Box<TE>, Box<TE>, Box<TE>),
    Call(u32, Vec<TE>),
    Builtin(Builtin, Box<TE>, Box<TE>),
    /// `stdio.print` / `stdio.println` of an int or bool value
    Print {
        value: Box<TE>,
        newline: bool,
    },
    /// `stdio.print` / `stdio.println` of a string literal at data offset
    PrintStr {
        offset: u32,
        len: u32,
        newline: bool,
    },
    /// enum variant ordinal (i32)
    EnumVal(u32),
    /// Immutable tagged ADT value: 16-byte allocation, i32 tag at 0,
    /// i64 payload at 8; no payload for None. tmp is a fresh i32 local.
    AdtNew { tag: u32, payload: Option<Box<TE>>, tmp: u32 },
    /// Typed prefix trap: the operand is evaluated exactly once before
    /// allocating Some; only the private guest ordinary-throw tag yields None.
    /// All temporaries are function-local to avoid shared error state.
    Trap {
        value: Box<TE>,
        value_tmp: u32,
        some_tmp: u32,
        none_tmp: u32,
    },
    /// Compare the discriminant with a known variant tag.
    AdtIs { obj: Box<TE>, tag: u32 },
    /// Payload read, admissible only inside the tag-matched arm.
    AdtPayload(Box<TE>),
    /// Evaluate a tagged ADT once. On failure return its original handle from
    /// the enclosing function; on success leave the i64 payload on the stack.
    AdtPropagate { source: Box<TE>, tmp: u32, success_tag: u32 },
    /// Checked physical-array cell load at a compiler-planned in-bounds
    /// byte offset. Never represented as a class field or untrusted pointer.
    CollectionLoad { array: Box<TE>, offset: u32 },
    /// Bounded source-compiled Array allocation in guest linear memory.
    CollectionAlloc(u32),
    /// ordinary class field read
    FieldGet {
        obj: Box<TE>,
        offset: u32,
    },
    /// A compiler-authorized state field read; never fold into FieldGet
    /// without checking the protected receiver and lexical lease authority.
    StateFieldRead {
        obj: Box<TE>,
        offset: u32,
    },
    /// read an actor-state global
    GlobalGet(u32),
    /// bump-allocate a zeroed object of `n` bytes; panics when the heap is full
    Alloc(u32),
    /// start an actor of the given type
    Spawn(u32),
    /// enqueue `value` (int, or bool widened to i64) on an actor's mailbox
    Send {
        target: Box<TE>,
        value: Box<TE>,
    },
    /// print an object; `tmp` is an i32 scratch local holding it
    PrintObj {
        obj: Box<TE>,
        tmp: u32,
        pieces: Vec<PrintPiece>,
        newline: bool,
    },
}

#[derive(Clone, Debug)]
pub struct TE {
    pub e: TExpr,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub enum TStmt {
    Set(u32, TE),
    /// Compiler-planned scalar i64 cell store inside an owned Array allocation.
    /// Its offset is checked against the resolved nominal layout/length.
    CollectionStore { array: TE, offset: u32, value: TE },
    /// ordinary class field initialization / assignment
    FieldSet {
        obj: TE,
        offset: u32,
        ty: Type,
        value: TE,
    },
    /// Protected state write: verified lexical exclusive access to `obj`.
    StateFieldWrite {
        obj: TE,
        offset: u32,
        ty: Type,
        value: TE,
    },
    /// Retain lexical protected authority through typed IR.
    /// Single-Worker Wasm emits the body inline pending scheduler integration.
    StateCriticalWrite(Vec<TStmt>),
    /// Register a freshly allocated protected state object with the trusted
    /// Worker host BEFORE returning it. Constructors cannot forge a lease.
    StateRegister(TE),
    /// assign an actor-state global
    GlobalSet(u32, TE),
    Expr(TE),
    /// A guest Error(message) carried by a private Wasm exception tag.
    Throw(TE),
    /// Escalated failure on the separate module-private raise tag. It is
    /// never matched by `catch`/`trap`; only `recover` or the root sees it.
    Raise(TE),
    /// First statement of a top-level body that uses try/defer/recover:
    /// compiler-owned unwind slots (defer-recover-unwind-v1). `ret` holds
    /// the snapshotted return value, `msg`/`kind` the pending failure.
    UnwindFrame { ret: Option<u32>, saved: u32, msg: u32, kind: u32, pending: u32 },
    /// `try`/`catch (Error)`/`finally`; `saved` snapshots the catch depth.
    Try {
        saved: u32,
        body: Vec<TStmt>,
        catch: Option<Vec<TStmt>>,
        finally: Option<Vec<TStmt>>,
        pos: Pos,
    },
    /// Registration point of a top-level `defer`: sets `flag`. The body
    /// runs LIFO at every function exit after registration.
    Defer { flag: u32, args: Vec<(u32, TE)>, body: Vec<TStmt>, pos: Pos },
    /// Registration of a recovery callback: evaluates factory arguments into
    /// `args` slots once, sets `flag`. The body runs only while unwinding.
    Recover { flag: u32, args: Vec<(u32, TE)>, body: Vec<TStmt>, pos: Pos },
    /// Terminal `c.next()`: delegate the unchanged failure to the next
    /// older recovery callback or the outer boundary.
    RecoverNext,
    Return(Option<TE>),
    /// Pull-driven iterator loop; handle is owned by this loop, and closed
    /// at DONE, early break, or before a function-level return.
    ForIn {
        source: TE,
        handle_slot: u32,
        value_slot: u32,
        body: Vec<TStmt>,
    },
    If(Vec<(TE, Vec<TStmt>)>, Option<Vec<TStmt>>),
    /// `while`, `loop` and C-style `for`: `cond` absent means unconditional;
    /// `update` runs after the body and after `continue`.
    Loop {
        cond: Option<TE>,
        body: Vec<TStmt>,
        update: Vec<TStmt>,
    },
    Break,
    Continue,
    Block(Vec<TStmt>),
    /// a path the checker proved impossible (after an exhaustive match)
    Unreachable,
}

#[derive(Clone, Debug)]
pub struct TFunc {
    pub name: String,
    pub params: Vec<Type>,
    pub ret: Type,
    /// declared locals after the parameters
    pub locals: Vec<Type>,
    pub body: Vec<TStmt>,
}

/// Typed, bounded suspension instructions for the admitted guest-Wasm profile.
/// Each instruction is addressed by a stable generator resume PC.
#[derive(Clone, Debug)]
pub enum TGenStep {
    Yield(TE),
    Delegate { function: u32, arg: TGenArg },
    CountTo { start: i64 },
    Set { local: u32, value: TE },
    Guard { condition: TE, on_false: u32 },
    Jump { to: u32 },
    Done,
}

#[derive(Clone, Copy, Debug)]
pub enum TGenArg {
    None,
    Literal(i64),
    Parameter,
}

#[derive(Clone, Debug)]
pub struct TGenerator {
    pub function: u32,
    pub steps: Vec<TGenStep>,
    /// Number of arena-resident i64 locals retained across next() calls.
    pub locals: u32,
    /// Bitset of locals live after each resume PC for typed CFG plans.
    /// An empty vector is the legacy CountTo/yield* specialization.
    pub live_after: Vec<u16>,
}

/// One actor type: its state initializers and receive handler.
#[derive(Clone, Debug)]
pub struct TActor {
    pub name: String,
    /// `(state global, initializer)` in declaration order.
    pub inits: Vec<(u32, TE)>,
    /// Function index of `receive(value: i64, sequence: i64)`.
    pub receive: Option<u32>,
}

#[derive(Clone, Debug)]
pub struct TProgram {
    pub funcs: Vec<TFunc>,
    pub generators: Vec<TGenerator>,
    pub main: u32,
    pub imports: Vec<Import>,
    pub data: Vec<u8>,
    /// Classes exist: the module owns a bounded bump heap.
    pub heap: bool,
    /// Types of the actor-state globals, indexed by `TExpr::GlobalGet`.
    pub globals: Vec<Type>,
    pub actors: Vec<TActor>,
    /// String values exist: the module carries memory and the string helpers.
    pub strings: bool,
    /// Emit one module-private Wasm EH tag only when ordinary throw/trap exists.
    pub guest_eh: bool,
    /// A second private tag for `raise` (escalated failure).
    pub raise_tag: bool,
    /// A guest-global active-catch counter exists because some `recover`
    /// must defer to an outer caller's catch or trap (two-phase dispatch).
    pub catch_depth: bool,
}

/// Size in bytes of every field slot in a class instance.
pub const FIELD_BYTES: u32 = 8;

struct FieldInfo {
    name: String,
    ty: Type,
    visibility: FieldVisibility,
    mode: FieldMode,
    /// Do not conflate Val, Final and Const with the browser storage mode.
    binding: FieldBinding,
    /// Future referent-write authorization is independent of rebinding.
    #[allow(dead_code)]
    referent_mutable: bool,
    /// byte offset (classes) or state global (actors)
    slot: u32,
}

#[derive(Clone)]
struct MethodInfo {
    name: String,
    public: bool,
    is_static: bool,
    idx: u32,
    params: Vec<Type>,
    ret: Type,
}

struct ClassInfo {
    name: String,
    /// Distinct protected-state nominal declaration (single Worker-local profile).
    state_container: bool,
    fields: Vec<FieldInfo>,
    methods: Vec<MethodInfo>,
    new_idx: u32,
    /// AOT-generated, private per-concrete-class copier, present only after
    /// proving every stored field is a by-value/immutable scalar.
    deep_copy_idx: Option<u32>,
    ctor_idx: Option<u32>,
    ctor_params: Vec<Type>,
}

struct ActorInfo {
    name: String,
    fields: Vec<FieldInfo>,
    methods: Vec<MethodInfo>,
    receive_idx: Option<u32>,
    payload: Type,
}

/// Program-wide declaration tables shared by every body check.
struct Globals<'a> {
    sigs: BTreeMap<(String, usize), (u32, Vec<Type>, Type)>,
    names: BTreeMap<String, Vec<usize>>,
    classes: Vec<ClassInfo>,
    enums: &'a [EnumDecl],
    actors: Vec<ActorInfo>,
    type_names: &'a [(String, Pos)],
}

/// Where the code being checked lives.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    TopLevel,
    /// class `c`: `ctor` for the constructor body; static methods have no self
    Class {
        c: u32,
        ctor: bool,
        is_static: bool,
    },
    /// actor `a`; state is reached through `self`
    Actor {
        a: u32,
    },
    /// a field initializer: constant expressions only
    FieldInit {
        actor: bool,
    },
}

struct Local {
    name: String,
    slot: u32,
    ty: Type,
    mutable: bool,
    /// `Some(payload)` for the `ActorMail<T>` parameter of receive
    mail: Option<Type>,
}

#[derive(Clone, Copy)]
struct ScopedLoan { owner: u32, mutable: bool }

struct FnCx<'a> {
    g: &'a Globals<'a>,
    owner: Owner,
    ret: Type,
    scopes: Vec<Vec<Local>>,
    locals: Vec<Type>,
    nparams: u32,
    loops: u32,
    /// First slot declared inside each enclosing loop body.
    loop_floors: Vec<u32>,
    /// Class-typed locals whose value has been moved out.
    moved: BTreeSet<u32>,
    /// Borrowed class locals keyed by their own slot.
    loans: BTreeMap<u32, ScopedLoan>,
    /// Compiler-issued lexical protected state permissions.
    state_write_scope: bool,
    state_read_scope: bool,
    imports: &'a mut Vec<Import>,
    data: &'a mut Vec<u8>,
    /// Unwind slots, allocated on the first try/defer/recover.
    unwind: Option<(Option<u32>, u32, u32, u32, u32)>,
    /// > 0 while checking an isolated defer/recover body.
    cleanup_depth: u32,
    /// Cursor binder of the recovery callback being checked.
    recover_cursor: Option<String>,
    /// Non-escaping error-view binder; only explicitly admitted read-only
    /// properties may be lowered from the compiler-owned unwind slots.
    recover_error: Option<String>,
}

type R<T> = Result<T, Diagnostic>;
/// Compiler-owned slots and isolated bindings for one cleanup factory.
type CleanupCaptured = (Vec<(u32, TE)>, Vec<Local>);

fn string_member_err(name: &str, pos: Pos) -> Diagnostic {
    match name {
        "replace_literal" | "split_literal" | "is_identifier" | "is_route_segment" => Diagnostic::new(
            pos,
            "E_UNSUPPORTED",
            format!("string.{name} is not supported by the browser compiler yet"),
        ),
        _ => Diagnostic::new(pos, "E_UNBOUND", format!("unknown string member '{name}'")),
    }
}

fn type_err(pos: Pos, msg: impl Into<String>) -> Diagnostic {
    Diagnostic::new(pos, "E_TYPE", msg)
}

impl Globals<'_> {
    fn tn(&self, t: Type) -> String {
        match t {
            Type::Class(i) => self.classes[i as usize].name.clone(),
            Type::Enum(i) => self.enums[i as usize].name.clone(),
            Type::ActorRef(i) => format!("ActorRef<{}>", self.actors[i as usize].name),
            Type::Named(i) | Type::NamedRef(i) | Type::Callable(i) => self.type_names[i as usize].0.clone(),
            t => t.name().to_string(),
        }
    }

    fn class(&self, name: &str) -> Option<u32> {
        self.classes.iter().position(|c| c.name == name).map(|i| i as u32)
    }
    fn enum_(&self, name: &str) -> Option<u32> {
        self.enums.iter().position(|c| c.name == name).map(|i| i as u32)
    }
    fn actor(&self, name: &str) -> Option<u32> {
        self.actors.iter().position(|c| c.name == name).map(|i| i as u32)
    }
}

/// Resolve parser type names against the declaration tables.
fn resolve(t: Type, type_names: &[(String, Pos)], classes: &[String], enums: &[EnumDecl], actors: &[String]) -> R<Type> {
    Ok(match t {
        Type::Named(i) => {
            let (n, pos) = &type_names[i as usize];
            if let Some(c) = classes.iter().position(|c| c == n) {
                Type::Class(c as u32)
            } else if let Some(e) = enums.iter().position(|e| e.name == *n) {
                Type::Enum(e as u32)
            } else if actors.iter().any(|a| a == n) {
                return Err(type_err(*pos, format!("'{n}' is an actor; its references have type ActorRef<{n}>")));
            } else {
                return Err(Diagnostic::new(*pos, "E_UNKNOWN_TYPE", format!("unknown type '{n}'")));
            }
        }
        Type::Callable(_) => {
            // Type recognition and structural signature validation are
            // available now, but the browser backend has no callable value
            // storage or verified indirect-call ABI. Stop before emitting.
            let signature = callable_ir::CallableSignature::from_source_type(
                t, type_names, Pos { line: 1, col: 1 })?;
            return Err(Diagnostic::new(
                type_names[match t { Type::Callable(i) => i as usize, _ => unreachable!() }].1,
                "E_UNSUPPORTED",
                format!("callable value type {} is parsed and checked but requires validated Wasm indirect dispatch",
                    signature.source_spelling()),
            ));
        }
        Type::NamedRef(i) => {
            let (n, pos) = &type_names[i as usize];
            match actors.iter().position(|a| a == n) {
                Some(a) => Type::ActorRef(a as u32),
                None => return Err(type_err(*pos, format!("ActorRef<{n}> needs an actor type, and '{n}' is not one"))),
            }
        }
        t => t,
    })
}

fn isolation(pos: Pos, actor: &str, what: &str, name: &str) -> Diagnostic {
    Diagnostic::new(
        pos,
        "E_ISOLATION",
        format!(
            "actor '{actor}' cannot implicitly access {what} '{name}'; move the dependency to another source unit and import it explicitly"
        ),
    )
}

/// Field initializers run while the object is under construction: the Java
/// reference forbids calls there, and this compiler admits only constants.
fn const_init(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Float(_) | ExprKind::Str(_) => true,
        ExprKind::Unary(_, a) => const_init(a),
        ExprKind::Binary(_, a, b) => const_init(a) && const_init(b),
        ExprKind::Ternary(c, a, b) => const_init(c) && const_init(a) && const_init(b),
        ExprKind::Member(base, _) => matches!(base.kind, ExprKind::Var(_)),
        _ => false,
    }
}

/// Validate locally decidable generator item/delegation types before the
/// deliberate guest-Wasm continuation gate. This is not full expression
/// inference: unresolved/compound expressions remain fail-closed until the
/// generator IR and ownership-aware checker are implemented.
fn precheck_generator_body(body: &[Stmt], funcs: &[Func]) -> R<()> {
    for stmt in body {
        match stmt {
            Stmt::Yield(expr, _) => {
                if matches!(&expr.kind, ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::Float(_)) {
                    return Err(Diagnostic::new(expr.pos, "E_TYPE",
                        "Generator<int> can only yield int items"));
                }
            }
            Stmt::YieldFrom(expr, _) => {
                match &expr.kind {
                    ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::Float(_) => {
                        return Err(Diagnostic::new(expr.pos, "E_TYPE",
                            "yield* requires a generator/iterator, not a scalar"));
                    }
                    ExprKind::Call(name, args) => {
                        if let Some(target) = funcs.iter().find(|f|
                            f.name == *name && f.params.len() == args.len())
                        {
                            if !target.is_generator || target.ret != Type::GeneratorInt {
                                return Err(Diagnostic::new(expr.pos, "E_TYPE",
                                    format!("yield* target '{name}' is not a Generator<int>")));
                            }
                        }
                    }
                    _ => {}
                }
            }
            Stmt::If { arms, otherwise, .. } => {
                for (_, branch) in arms {
                    precheck_generator_body(branch, funcs)?;
                }
                if let Some(branch) = otherwise {
                    precheck_generator_body(branch, funcs)?;
                }
            }
            Stmt::While { body, .. } | Stmt::Loop { body, .. }
            | Stmt::ForIn { body, .. } | Stmt::Block(body) => {
                precheck_generator_body(body, funcs)?;
            }
            Stmt::For { body, .. } => precheck_generator_body(body, funcs)?,
            Stmt::Match { arms, .. } => {
                for arm in arms {
                    precheck_generator_body(&arm.body, funcs)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// The first executable for-in profile has no exception unwinder for
/// arbitrary user calls inside the loop. Restrict the body to effect-free
/// scalar expressions, local mutations, conditional control-flow, and early
/// return/break/continue. Checked arithmetic traps terminate the Wasm
/// instance, and no guest iterator is allowed to escape that instance.
fn generator_forin_scalar_expr(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Bool(_) |
        ExprKind::Str(_) | ExprKind::Var(_) => true,
        ExprKind::Unary(_, a) => generator_forin_scalar_expr(a),
        ExprKind::Binary(_, a, b) => generator_forin_scalar_expr(a)
            && generator_forin_scalar_expr(b),
        ExprKind::Ternary(a, b, c) => generator_forin_scalar_expr(a)
            && generator_forin_scalar_expr(b) && generator_forin_scalar_expr(c),
        _ => false,
    }
}

fn generator_forin_safe_body(body: &[Stmt]) -> bool {
    body.iter().all(|s| match s {
        Stmt::Bind { init, .. } | Stmt::Assign { value: init, .. } =>
            generator_forin_scalar_expr(init),
        Stmt::If { arms, otherwise, .. } =>
            arms.iter().all(|(cond, branch)|
                generator_forin_scalar_expr(cond) && generator_forin_safe_body(branch))
                && otherwise.as_ref().is_none_or(|b| generator_forin_safe_body(b)),
        Stmt::Block(b) => generator_forin_safe_body(b),
        Stmt::Return(Some(e), _) => generator_forin_scalar_expr(e),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => true,
        _ => false,
    })
}

/// Reject delegation cycles before code generation so an actor cannot
/// recursively allocate child frames without ever yielding an item.
/// The admitted graph is statically resolved and each frame has at most
/// one live delegated child; depth is bounded independently of wasm stacks.
fn validate_generator_graph(gens: &[TGenerator], p: &Program) -> R<()> {
    fn visit(node: usize, depth: u32, colors: &mut [u8],
             gens: &[TGenerator], p: &Program) -> R<()> {
        if colors[node] == 1 {
            return Err(Diagnostic::new(p.funcs[node].pos, "E_GENERATOR_CYCLE",
                "generator yield* delegation must be acyclic"));
        }
        if colors[node] == 2 { return Ok(()); }
        if depth > 64 {
            return Err(Diagnostic::new(p.funcs[node].pos, "E_NESTING",
                "generator delegation chain exceeds 64 frames"));
        }
        colors[node] = 1;
        if let Some(gen) = gens.iter().find(|g| g.function as usize == node) {
            for step in &gen.steps {
                if let TGenStep::Delegate { function, .. } = step {
                    visit(*function as usize, depth + 1, colors, gens, p)?;
                }
            }
        }
        colors[node] = 2;
        Ok(())
    }
    let mut colors = vec![0; p.funcs.len()];
    for g in gens {
        visit(g.function as usize, 1, &mut colors, gens, p)?;
    }
    Ok(())
}

/// Only one immutable int parameter and one mutable counter are admitted.
/// A C-style for must use i <= limit, i++, and yield i without side effects.
fn generator_count_loop(f: &Func, stmt: &Stmt) -> Option<i64> {
    if f.params.len() != 1 || f.params[0].ty != Type::Int { return None; }
    let Stmt::For { init: Some(init), cond: Some(cond),
                    update: Some(update), body, .. } = stmt else { return None; };
    let Stmt::Bind { kind: BindKind::Let, name, ty, init: initial, .. } =
        init.as_ref() else { return None; };
    if ty.is_some_and(|t| t != Type::Int) { return None; }
    let ExprKind::Int(Some(start)) = &initial.kind else { return None; };
    if *start > i64::MAX as u64 { return None; }
    let ExprKind::Binary(BinOp::Le, left, right) = &cond.kind else { return None; };
    if !matches!(&left.kind, ExprKind::Var(s) if s == name)
        || !matches!(&right.kind, ExprKind::Var(s) if s == &f.params[0].name) { return None; }
    let Stmt::Assign { name: update_name, value, .. } = update.as_ref() else { return None; };
    if update_name != name { return None; }
    let ExprKind::Binary(BinOp::Add, left, right) = &value.kind else { return None; };
    if !matches!(&left.kind, ExprKind::Var(s) if s == name)
        || !matches!(&right.kind, ExprKind::Int(Some(1))) { return None; }
    if body.len() != 1 || !matches!(&body[0],
        Stmt::Yield(Expr { kind: ExprKind::Var(s), .. }, _) if s == name) { return None; }
    Some(*start as i64)
}

/// Delegate arguments cannot evaluate arbitrary expressions or alias locals.
fn generator_arg(f: &Func, target: &Func, args: &[Expr]) -> Option<TGenArg> {
    match (target.params.as_slice(), args) {
        ([], []) => Some(TGenArg::None),
        ([p], [arg]) if p.ty == Type::Int => match &arg.kind {
            ExprKind::Int(Some(n)) if *n <= i64::MAX as u64 =>
                Some(TGenArg::Literal(*n as i64)),
            ExprKind::Var(name) if f.params.len() == 1
                && f.params[0].ty == Type::Int && *name == f.params[0].name =>
                Some(TGenArg::Parameter),
            _ => None,
        },
        _ => None,
    }
}

/// Gate every generated class copy against the **canonical** closed-world
/// AOT descriptor checker, vendored byte-identically from the independently
/// tested atto-borrow-checker.rs copy_graph_v1 module. No user annotations or
/// method names can mint a witness, and this does not admit actor sends.
fn authenticate_flat_copy_aot(classes: &[ClassInfo], ci: u32, pos: Pos) -> R<()> {
    use crate::copy_graph_v1::{
        admit_copy, CopyMode, CopyRequest, Field as CopyField,
        FieldKind as CopyFieldKind, TypeDescriptor,
    };

    let mut layouts = Vec::with_capacity(classes.len());
    for (id, class) in classes.iter().enumerate() {
        let fields = class.fields.iter().enumerate().map(|(i, f)| CopyField {
            id: (i as u32) + 1,
            kind: match f.ty {
                Type::Int | Type::Bool | Type::Float | Type::Str | Type::Enum(_) =>
                    CopyFieldKind::Scalar,
                Type::Class(child) => CopyFieldKind::OwnedMutable(child + 1),
                _ => CopyFieldKind::Unresolved,
            },
        }).collect();
        layouts.push(TypeDescriptor {
            id: id as u32 + 1,
            parent: None, // the browser compiler does not admit inheritance
            fields,
            deep_copy_witness: class.deep_copy_idx.is_some() && !class.state_container,
            shallow_copy_witness: false, // a deep witness does not grant copy!
            sendable: false, // actor Sendable is a separate, unimplemented proof
        });
    }
    let requested = ci.checked_add(1).ok_or_else(|| Diagnostic::new(
        pos, "E_COPY_AOT_WITNESS", "invalid concrete class identifier"))?;
    let plan = admit_copy(&layouts, CopyRequest {
        concrete_type: requested,
        static_type: requested,
        mode: CopyMode::Deep,
        actor_send: false,
    }).map_err(|err| Diagnostic::new(pos, err.0,
        "class lacks a complete, concrete, closed-world compiler-generated deep copy witness"))?;
    // The current AOT backend generates flat-object copies only. Do not
    // broaden witness admission to transitive graphs until the generated
    // copier has an identity memo and a rollback-safe graph allocation plan.
    if plan.copied_type_ids != vec![requested] {
        return Err(Diagnostic::new(pos, "E_COPY_DEEP_UNSUPPORTED",
            "nested mutable class graph requires a memoized AOT copy runtime"));
    }
    Ok(())
}

pub fn check(p: &Program) -> R<TProgram> {
    let lowered = direct_lambda::lower(p)?;
    check_lowered(&lowered)
}

fn check_lowered(p: &Program) -> R<TProgram> {
    // Validate the bounded CFG and integer-only suspension/lifetime profile
    // before registering signatures. Reject unsupported generator effects
    // before emission; never substitute eager iterator materialization.
    for spec in &p.array_types {
        // Nominal resolution is performed by the same production type checker
        // that validates functions/classes, not by token-level generic guesses.
        if !p.classes.iter().any(|c| c.name == spec.element) {
            return Err(Diagnostic::new(spec.pos, "E_UNKNOWN_TYPE",
                format!("Array element '{}' requires a declared nominal class type", spec.element)));
        }
    }
    if let Some(spec) = p.array_types.first() {
        return Err(Diagnostic::new(spec.pos, "E_UNSUPPORTED",
            format!("Array<{}, layout={:?}> is a checked nominal generic specialization, but general-purpose Array storage and borrow lowering are not yet enabled outside the bounded compiled guest profile",
                spec.element, spec.layout)));
    }
    for f in &p.funcs {
        if f.is_generator {
            precheck_generator_body(&f.body, &p.funcs)?;
            // Build the exact bounded resume graph before the ABI-v2 gate.
            // It is a compiler IR only; no generator guest artifact is emitted.
            let plan = crate::generator_cfg::lower(&f.body)?;
            // Preflight the AST-visible slots. The final codegen must repeat
            // this check using all typed locals and hidden scratch slots.
            let declared_locals = plan.instructions.iter().filter(|op|
                matches!(op, crate::generator_cfg::Instruction::Evaluate(Stmt::Bind { .. }))
            ).count() as u32;
            let _frame = crate::generator_frame::GeneratorFrameLayout::new(
                f.params.len() as u32, declared_locals, plan.delegate_slots, f.pos
            )?;
            // Bounded single-int-parameter and live counter profile.
            let count_loops = f.body.iter().filter(|s| matches!(s, Stmt::For { .. })).count();
            let admitted = f.params.len() <= 1
                && f.params.iter().all(|p| p.ty == Type::Int)
                && count_loops <= 1 && plan.delegate_slots <= 1
                && f.body.iter().enumerate().all(|(i, stmt)| {
                    match stmt {
                        Stmt::Yield(Expr { kind: ExprKind::Int(Some(n)), .. }, _) =>
                            *n <= i64::MAX as u64,
                        Stmt::YieldFrom(Expr { kind: ExprKind::Call(name, args), .. }, _) =>
                            p.funcs.iter().any(|target| target.is_generator
                                && target.name == *name
                                && generator_arg(f, target, args).is_some()),
                        Stmt::For { .. } => generator_count_loop(f, stmt).is_some(),
                        Stmt::Return(None, _) => i + 1 == f.body.len(),
                        _ => false,
                    }
                });
            if !admitted && generator_lower::lower(f)?.is_none() {
                return Err(Diagnostic::new(f.pos, "E_UNSUPPORTED",
                    "generator source requires typed, owned continuation lowering not yet implemented"));
            }
        }
        if (!f.is_generator && f.ret == Type::GeneratorInt)
            || f.params.iter().any(|p| p.ty == Type::GeneratorInt) {
            return Err(Diagnostic::new(f.pos, "E_UNSUPPORTED_TYPE",
                "Generator<int> requires a compiled generator continuation"));
        }
    }
    for c in &p.classes {
        if c.methods.iter().any(|m| m.ret == Type::GeneratorInt
            || m.params.iter().any(|p| p.ty == Type::GeneratorInt))
            || c.ctor.as_ref().is_some_and(|ctor|
                ctor.params.iter().any(|p| p.ty == Type::GeneratorInt)) {
            return Err(Diagnostic::new(c.pos, "E_UNSUPPORTED_TYPE",
                "generator methods and parameters require a compiled iterator continuation"));
        }
    }
    for a in &p.actors {
        if a.persistence != ActorPersistenceMode::Volatile {
            // Validate an AOT-friendly scalar snapshot schema first. No guest
            // emission may silently treat durable/persistent as volatile.
            let _schema = crate::actor_persistence::ActorStateSchema::for_actor(a)?;
            let legacy_load = a.methods.iter().find(|m| m.name == "load_state");
            let legacy_save = a.methods.iter().find(|m| m.name == "save_state");
            let has_load = a.persistence_hooks.iter().any(|h| h.name == "load_state");
            let has_save = a.persistence_hooks.iter().any(|h| h.name == "save_state");
            match a.persistence {
                ActorPersistenceMode::Persistent => {
                    if legacy_load.is_some() || legacy_save.is_some() {
                        return Err(Diagnostic::new(a.pos, "E_PERSIST_SIGNATURE",
                            "persistent actor hooks must use susp fnc and exact Result types"));
                    }
                    if !has_load || !has_save ||
                        a.persistence_hooks.iter().any(|h| !h.body_provided) {
                        return Err(Diagnostic::new(a.pos, "E_PERSIST_HOOKS",
                            "persistent actors require implemented load_state and save_state hooks"));
                    }
                    return Err(Diagnostic::new(a.pos, "E_PERSIST_RUNTIME_UNAVAILABLE",
                        "hook signatures validated, but suspended storage bodies and recovery are not yet executable"));
                }
                ActorPersistenceMode::Durable => {
                    if has_load || has_save || legacy_load.is_some() || legacy_save.is_some() {
                        return Err(Diagnostic::new(a.pos, "E_DURABLE_HOOK_OVERRIDE",
                            "durable actor storage is runtime-owned; user load/save hooks cannot override it"));
                    }
                    return Err(Diagnostic::new(a.pos, "E_DURABLE_RUNTIME_UNAVAILABLE",
                        "automatic durable disk commits and revival are not implemented by this browser backend"));
                }
                ActorPersistenceMode::Volatile => unreachable!(),
            }
        }
        if a.methods.iter().any(|m| m.ret == Type::GeneratorInt
            || m.params.iter().any(|p| p.ty == Type::GeneratorInt)) {
            return Err(Diagnostic::new(a.pos, "E_UNSUPPORTED_TYPE",
                "actor generator methods require a compiled iterator continuation"));
        }
    }
    let tn = &p.type_names;
    // ---- one namespace for functions, classes, enums and actors
    let mut seen: BTreeMap<&str, Pos> = BTreeMap::new();
    let decl_names = p
        .classes
        .iter()
        .map(|c| (c.name.as_str(), c.pos, "class"))
        .chain(p.enums.iter().map(|e| (e.name.as_str(), e.pos, "enum")))
        .chain(p.actors.iter().map(|a| (a.name.as_str(), a.pos, "actor")));
    for (name, pos, kind) in decl_names {
        if matches!(
            name,
            "And" | "Or" | "Xor" | "stdio" | "ActorRef" | "ActorMail" | "int" | "bool" | "boolean"
        ) {
            return Err(Diagnostic::new(
                pos,
                "E_DUPLICATE",
                format!("'{name}' is a builtin and cannot be redefined"),
            ));
        }
        if seen.insert(name, pos).is_some() {
            return Err(Diagnostic::new(
                pos,
                "E_DUPLICATE",
                format!("duplicate type name '{name}' ({kind})"),
            ));
        }
    }
    for f in &p.funcs {
        if seen.contains_key(f.name.as_str()) {
            return Err(Diagnostic::new(
                f.pos,
                "E_DUPLICATE",
                format!("'{}' is already declared as a type", f.name),
            ));
        }
    }
    let class_names: Vec<String> = p.classes.iter().map(|c| c.name.clone()).collect();
    let actor_names: Vec<String> = p.actors.iter().map(|a| a.name.clone()).collect();
    let res = |t: Type| resolve(t, tn, &class_names, &p.enums, &actor_names);

    // ---- top-level signatures keep indices 0..funcs.len()
    let mut sigs = BTreeMap::new();
    let mut names: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (i, f) in p.funcs.iter().enumerate() {
        if matches!(f.name.as_str(), "And" | "Or" | "Xor" | "stdio" | "Ok" | "Err" | "Some" | "None") {
            return Err(Diagnostic::new(
                f.pos,
                "E_DUPLICATE",
                format!("'{}' is a builtin and cannot be redefined", f.name),
            ));
        }
        let key = (f.name.clone(), f.params.len());
        if sigs.contains_key(&key) {
            return Err(Diagnostic::new(
                f.pos,
                "E_DUPLICATE",
                format!(
                    "function '{}' already has arity {}; overload identity is name + arity",
                    f.name,
                    f.params.len()
                ),
            ));
        }
        let params = f.params.iter().map(|q| res(q.ty)).collect::<R<Vec<_>>>()?;
        sigs.insert(key, (i as u32, params, res(f.ret)?));
        names.entry(f.name.clone()).or_default().push(f.params.len());
    }

    // ---- member function indices follow the top-level functions
    let mut next = p.funcs.len() as u32;
    let mut take = || {
        next += 1;
        next - 1
    };
    let methods_of = |owner: &str, ms: &[Method], fields: &[Field]| -> R<Vec<MethodInfo>> {
        let mut out: Vec<MethodInfo> = Vec::new();
        for m in ms {
            if out.iter().any(|o| o.name == m.name) || fields.iter().any(|f| f.name == m.name) {
                return Err(Diagnostic::new(
                    m.pos,
                    "E_DUPLICATE",
                    format!("'{owner}' already declares a member named '{}'", m.name),
                ));
            }
            out.push(MethodInfo {
                name: m.name.clone(),
                public: m.public,
                is_static: m.is_static,
                idx: 0,
                params: m.params.iter().map(|q| res(q.ty)).collect::<R<Vec<_>>>()?,
                ret: res(m.ret)?,
            });
        }
        Ok(out)
    };
    let fields_of = |owner: &str, fs: &[Field], actor: bool, global_base: u32| -> R<Vec<FieldInfo>> {
        let mut out: Vec<FieldInfo> = Vec::new();
        for (i, f) in fs.iter().enumerate() {
            if out.iter().any(|o| o.name == f.name) {
                return Err(Diagnostic::new(
                    f.pos,
                    "E_DUPLICATE",
                    format!("'{owner}' already declares a field named '{}'", f.name),
                ));
            }
            // A class 'const' is constexpr; it must not silently turn into
            // runtime initialization merely because Val/Final share a storage mode.
            // Non-const initializer effects are still intentionally unsupported
            // by the current restricted browser field-initialization backend.
            if !actor && f.binding == FieldBinding::Const && !const_init(&f.init) {
                return Err(Diagnostic::new(f.init.pos, "E_CONST",
                    format!("class constant '{}.{}' requires a compile-time initializer", owner, f.name)));
            }
            let ty = res(f.ty)?;
            let ok = match ty {
                Type::Int | Type::Bool => true,
                Type::Float | Type::Str | Type::Enum(_) => !actor,
                _ => false,
            };
            if !ok {
                return Err(Diagnostic::new(
                    f.pos,
                    "E_UNSUPPORTED_TYPE",
                    format!(
                        "field '{owner}.{}' has type {}; {} fields may be int or bool{} in the browser compiler",
                        f.name,
                        tn_plain(ty, tn, &class_names, &p.enums, &actor_names),
                        if actor { "actor" } else { "class" },
                        if actor { "" } else { ", float, string or an enum" }
                    ),
                ));
            }
            out.push(FieldInfo {
                name: f.name.clone(),
                ty,
                visibility: f.visibility,
                mode: f.mode,
                binding: f.binding,
                referent_mutable: f.referent_mutable,
                slot: if actor { global_base + i as u32 } else { i as u32 * FIELD_BYTES },
            });
        }
        Ok(out)
    };

    let mut classes = Vec::new();
    for c in &p.classes {
        let fields = fields_of(&c.name, &c.fields, false, 0)?;
        let mut methods = methods_of(&c.name, &c.methods, &c.fields)?;
        let new_idx = take();
        let ctor_idx = c.ctor.as_ref().map(|_| take());
        for m in &mut methods {
            m.idx = take();
        }
        // This first AOT profile may copy only a flat class of verified
        // identity-free slots. Class/actor/ADT handles require a graph memo,
        // and protected actor-state objects cannot bypass their sealed leases.
        // Custom copy_deep overrides need separate proof/hook chaining.
        let can_generate_deep_copy = !c.state_container
            && !c.methods.iter().any(|m| m.name == "copy_deep")
            && fields.iter().all(|f| matches!(f.ty,
                Type::Int | Type::Bool | Type::Float | Type::Str | Type::Enum(_)));
        let deep_copy_idx = if can_generate_deep_copy { Some(take()) } else { None };
        let ctor_params = match &c.ctor {
            Some(k) => k.params.iter().map(|q| res(q.ty)).collect::<R<Vec<_>>>()?,
            None => Vec::new(),
        };
        classes.push(ClassInfo {
            name: c.name.clone(),
            state_container: c.state_container,
            fields,
            methods,
            new_idx,
            deep_copy_idx,
            ctor_idx,
            ctor_params,
        });
    }
    let mut actors = Vec::new();
    let mut globals = Vec::new();
    for a in &p.actors {
        let fields = fields_of(&a.name, &a.fields, true, globals.len() as u32)?;
        globals.extend(fields.iter().map(|f| f.ty));
        let mut methods = methods_of(&a.name, &a.methods, &a.fields)?;
        if let Some(m) = a.methods.iter().find(|m| m.name == "receive") {
            return Err(Diagnostic::new(
                m.pos,
                "E_TYPE",
                format!("actor mailbox handler '{}.receive' parameter must be ActorMail<T>", a.name),
            ));
        }
        let receive_idx = a.receive.as_ref().map(|_| take());
        for m in &mut methods {
            m.idx = take();
        }
        let payload = match &a.receive {
            Some(r) => {
                let t = res(r.payload)?;
                if !matches!(t, Type::Int | Type::Bool) {
                    return Err(Diagnostic::new(
                        r.pos,
                        "E_UNSUPPORTED_TYPE",
                        format!(
                            "ActorMail<{}> is not supported by the browser compiler yet; mail payloads may be int or bool",
                            tn_plain(t, tn, &class_names, &p.enums, &actor_names)
                        ),
                    ));
                }
                t
            }
            None => Type::Void,
        };
        actors.push(ActorInfo {
            name: a.name.clone(),
            fields,
            methods,
            receive_idx,
            payload,
        });
    }
    let total = next as usize;

    let g = Globals {
        sigs,
        names,
        classes,
        enums: &p.enums,
        actors,
        type_names: tn,
    };

    let main = match g.sigs.get(&("main".to_string(), 0)) {
        Some((i, _, ret)) => {
            if !matches!(ret, Type::Int | Type::Void) {
                return Err(Diagnostic::new(
                    p.funcs[*i as usize].pos,
                    "E_ENTRY",
                    "main() must return int or void",
                ));
            }
            *i
        }
        None => {
            let pos = p
                .funcs
                .iter()
                .find(|f| f.name == "main")
                .map(|f| f.pos)
                .unwrap_or(Pos { line: 1, col: 1 });
            return Err(Diagnostic::new(
                pos,
                "E_ENTRY",
                "executable source requires a zero-argument main() entrypoint",
            ));
        }
    };

    let mut imports = Vec::new();
    let mut data = Vec::new();
    let mut funcs: Vec<Option<TFunc>> = (0..total).map(|_| None).collect();

    // ---- top-level functions
    let mut generators = Vec::new();
    for (i, f) in p.funcs.iter().enumerate() {
        let (_, params, ret) = g.sigs[&(f.name.clone(), f.params.len())].clone();
        if f.is_generator {
            if let Some(mut plan) = generator_lower::lower(f)? {
                plan.function = i as u32;
                generators.push(plan);
                funcs[i] = Some(TFunc {
                    name: f.name.clone(), params, ret,
                    locals: Vec::new(), body: Vec::new(),
                });
                continue;
            }
            // Original bounded CountTo/direct yield* fallback.
            let steps = f.body.iter().filter_map(|stmt| match stmt {
                Stmt::Yield(Expr { kind: ExprKind::Int(Some(n)), .. }, _) =>
                    Some(TGenStep::Yield(TE {
                        e: TExpr::I64(*n as i64), ty: Type::Int
                    })),
                Stmt::YieldFrom(Expr { kind: ExprKind::Call(name, args), .. }, _) => {
                    let target = p.funcs.iter().find(|target| target.is_generator
                        && target.name == *name && target.params.len() == args.len())
                        .expect("source validated before declaration lowering");
                    let arg = generator_arg(f, target, args)
                        .expect("argument validated before declaration lowering");
                    let idx = g.sigs.get(&(name.clone(), args.len()))
                        .expect("declared generator target").0;
                    Some(TGenStep::Delegate { function: idx, arg })
                }
                Stmt::For { .. } => Some(TGenStep::CountTo {
                    start: generator_count_loop(f, stmt).expect("verified counter loop")
                }),
                _ => None,
            }).collect();
            generators.push(TGenerator { function: i as u32, steps, locals: 0, live_after: Vec::new() });
            funcs[i] = Some(TFunc {
                name: f.name.clone(), params, ret,
                locals: Vec::new(), body: Vec::new(),
            });
            continue;
        }
        let named: Vec<(&str, Type, bool)> = f
            .params
            .iter()
            .zip(&params)
            .map(|(q, t)| (q.name.as_str(), *t, q.mutable))
            .collect();
        let body = body_check(
            &g,
            Owner::TopLevel,
            &named,
            None,
            ret,
            &f.body,
            &f.name,
            f.pos,
            &mut imports,
            &mut data,
        )?;
        funcs[i] = Some(TFunc {
            name: f.name.clone(),
            params,
            ret,
            locals: body.1,
            body: body.0,
        });
    }

    // ---- classes: P.new, P.constructor, methods
    for (ci, c) in p.classes.iter().enumerate() {
        let info = &g.classes[ci];
        let me = Type::Class(ci as u32);
        let mut field_inits = Vec::new();
        for (f, fi) in c.fields.iter().zip(&info.fields) {
            let v = field_init(&g, f, fi.ty, &c.name, false, &mut imports, &mut data)?;
            field_inits.push((fi.slot, fi.ty, v));
        }
        if let (Some(k), Some(kidx)) = (&c.ctor, info.ctor_idx) {
            let mut named = vec![("self", me, false)];
            named.extend(
                k.params
                    .iter()
                    .zip(&info.ctor_params)
                    .map(|(q, t)| (q.name.as_str(), *t, q.mutable)),
            );
            let owner = Owner::Class {
                c: ci as u32,
                ctor: true,
                is_static: false,
            };
            let body = body_check(
                &g,
                owner,
                &named,
                None,
                Type::Void,
                &k.body,
                "constructor",
                k.pos,
                &mut imports,
                &mut data,
            )?;
            let mut params = vec![me];
            params.extend(info.ctor_params.iter().copied());
            funcs[kidx as usize] = Some(TFunc {
                name: format!("{}.constructor", c.name),
                params,
                ret: Type::Void,
                locals: body.1,
                body: body.0,
            });
        }
        // P.new(args): allocate, run field initializers, run the constructor
        let n = info.ctor_params.len() as u32;
        let obj = TE {
            e: TExpr::Local(n),
            ty: me,
        };
        let mut body = vec![TStmt::Set(
            n,
            TE {
                e: TExpr::Alloc((info.fields.len() as u32 * FIELD_BYTES).max(FIELD_BYTES)),
                ty: me,
            },
        )];
        for (offset, ty, v) in field_inits {
            body.push(TStmt::FieldSet {
                obj: obj.clone(),
                offset,
                ty,
                value: v,
            });
        }
        if let Some(kidx) = info.ctor_idx {
            let mut args = vec![obj.clone()];
            args.extend(info.ctor_params.iter().enumerate().map(|(i, t)| TE {
                e: TExpr::Local(i as u32),
                ty: *t,
            }));
            body.push(TStmt::Expr(TE {
                e: TExpr::Call(kidx, args),
                ty: Type::Void,
            }));
        }
        if c.state_container {
            body.push(TStmt::StateRegister(obj.clone()));
        }
        body.push(TStmt::Return(Some(obj)));
        funcs[info.new_idx as usize] = Some(TFunc {
            name: format!("{}.new", c.name),
            params: info.ctor_params.clone(),
            ret: me,
            locals: vec![me],
            body,
        });
        // Generated source-independent whole-concrete-type copy plan. The
        // checker has proved that each slot can be copied by value; emitting
        // an allocation plus typed field loads/stores creates a fresh object
        // without invoking any initializer or user constructor a second time.
        // The copy function is private and has no reflective field access.
        if let Some(copy_idx) = info.deep_copy_idx {
            authenticate_flat_copy_aot(&g.classes, ci as u32, c.pos)?;
            let source = TE { e: TExpr::Local(0), ty: me };
            let cloned = TE { e: TExpr::Local(1), ty: me };
            let mut body = vec![TStmt::Set(1, TE {
                e: TExpr::Alloc((info.fields.len() as u32 * FIELD_BYTES).max(FIELD_BYTES)),
                ty: me,
            })];
            for field in &info.fields {
                body.push(TStmt::FieldSet {
                    obj: cloned.clone(),
                    offset: field.slot,
                    ty: field.ty,
                    value: TE { e: TExpr::FieldGet {
                        obj: Box::new(source.clone()), offset: field.slot,
                    }, ty: field.ty },
                });
            }
            body.push(TStmt::Return(Some(cloned)));
            funcs[copy_idx as usize] = Some(TFunc {
                name: format!("{}.copy_deep$generated", c.name),
                params: vec![me], ret: me, locals: vec![me], body,
            });
        }
        for (m, mi) in c.methods.iter().zip(&info.methods) {
            let owner = Owner::Class {
                c: ci as u32,
                ctor: false,
                is_static: m.is_static,
            };
            let mut named = Vec::new();
            if !m.is_static {
                named.push(("self", me, false));
            }
            named.extend(m.params.iter().zip(&mi.params).map(|(q, t)| (q.name.as_str(), *t, q.mutable)));
            let label = format!("{}.{}", c.name, m.name);
            let body = body_check(&g, owner, &named, None, mi.ret, &m.body, &label, m.pos, &mut imports, &mut data)?;
            funcs[mi.idx as usize] = Some(TFunc {
                name: label,
                params: named.iter().map(|x| x.1).collect(),
                ret: mi.ret,
                locals: body.1,
                body: body.0,
            });
        }
    }

    // ---- actors: state initializers, receive, methods
    let mut tactors = Vec::new();
    for (ai, a) in p.actors.iter().enumerate() {
        let info = &g.actors[ai];
        let owner = Owner::Actor { a: ai as u32 };
        let mut inits = Vec::new();
        for (f, fi) in a.fields.iter().zip(&info.fields) {
            inits.push((fi.slot, field_init(&g, f, fi.ty, &a.name, true, &mut imports, &mut data)?));
        }
        if let (Some(r), Some(ridx)) = (&a.receive, info.receive_idx) {
            let label = format!("{}.receive", a.name);
            let named = [("$value", Type::Int, false), ("$sequence", Type::Int, false)];
            let body = body_check(
                &g,
                owner,
                &named,
                Some((r.mail.as_str(), info.payload)),
                Type::Void,
                &r.body,
                &label,
                r.pos,
                &mut imports,
                &mut data,
            )?;
            funcs[ridx as usize] = Some(TFunc {
                name: label,
                params: vec![Type::Int, Type::Int],
                ret: Type::Void,
                locals: body.1,
                body: body.0,
            });
        }
        for (m, mi) in a.methods.iter().zip(&info.methods) {
            for (q, t) in m.params.iter().zip(&mi.params).map(|(q, t)| (q, *t)).chain(std::iter::once((
                &Param {
                    name: String::new(),
                    ty: mi.ret,
                    mutable: false,
                    pos: m.pos,
                },
                mi.ret,
            ))) {
                actor_type_ok(&g, &a.name, t, q.pos)?;
            }
            let named: Vec<(&str, Type, bool)> = m
                .params
                .iter()
                .zip(&mi.params)
                .map(|(q, t)| (q.name.as_str(), *t, q.mutable))
                .collect();
            let label = format!("{}.{}", a.name, m.name);
            let body = body_check(&g, owner, &named, None, mi.ret, &m.body, &label, m.pos, &mut imports, &mut data)?;
            funcs[mi.idx as usize] = Some(TFunc {
                name: label,
                params: mi.params.clone(),
                ret: mi.ret,
                locals: body.1,
                body: body.0,
            });
        }
        tactors.push(TActor {
            name: a.name.clone(),
            inits,
            receive: info.receive_idx,
        });
    }

    validate_generator_graph(&generators, p)?;
    if p.classes.iter().any(|c| c.state_container) {
        imports.extend([Import::StateRegister, Import::StateEnter, Import::StateLeave]);
    }
    imports.sort();
    imports.dedup();
    let funcs: Vec<TFunc> = funcs.into_iter().map(|f| f.expect("every function index is defined")).collect();
    // A pure declaration is a checked transitive effect contract, not a hint.
    // Inspect fully resolved typed calls, including branches that are never
    // executed at runtime. Other functions are impure unless declared pure.
    let pure_indices: BTreeSet<u32> = p.funcs.iter().enumerate()
        .filter_map(|(idx, f)| f.is_pure.then_some(idx as u32)).collect();
    for (idx, f) in p.funcs.iter().enumerate() {
        if !f.is_pure { continue; }
        if f.is_generator || !pure_stmts(&funcs[idx].body, &pure_indices) {
            return Err(Diagnostic::new(f.pos, "E_PURE",
                format!("pure fnc '{}' cannot perform I/O, use shared state, or call an impure function", f.name)));
        }
    }
    let strings = funcs
        .iter()
        .any(|f| f.params.contains(&Type::Str) || f.ret == Type::Str || f.locals.contains(&Type::Str) || any_in_stmts(&f.body, &uses_str))
        || tactors.iter().any(|a| a.inits.iter().any(|(_, e)| any_in(e, &uses_str)));
    audit_cleanup_call_effects(&funcs, &p.funcs)?;
    let concat = funcs.iter().any(|f| any_in_stmts(&f.body, &uses_concat));
    let adt_alloc = funcs.iter().any(|f| any_in_stmts(&f.body,
        &|e| matches!(e.e, TExpr::AdtNew { .. } | TExpr::Trap { .. })));
    let guest_eh = funcs.iter().any(|f| guest_eh_in_stmts(&f.body)
        || any_in_stmts(&f.body, &|e| matches!(e.e, TExpr::Trap { .. })));
    let raise_tag = funcs.iter().any(|f| stmt_exists(&f.body, &|s| matches!(s, TStmt::Raise(_))));
    let catch_depth = funcs.iter().any(|f| stmt_exists(&f.body, &|s| matches!(s, TStmt::Recover { .. })));
    Ok(TProgram {
        funcs,
        main,
        imports,
        data,
        heap: !p.classes.is_empty() || concat || adt_alloc || !generators.is_empty(),
        generators,
        globals,
        actors: tactors,
        strings,
        guest_eh,
        raise_tag,
        catch_depth,
    })
}

/// The source guest exception channels. Panic/trap is deliberately absent:
/// it is a fatal runtime outcome, not a catchable or locally recoverable
/// \`Error\`. These two bits are propagated through the typed call graph.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct EscapeEffects { throws: bool, raises: bool }

impl EscapeEffects {
    fn union(self, other: Self) -> Self {
        Self { throws: self.throws || other.throws, raises: self.raises || other.raises }
    }
    fn without_throw(self) -> Self {
        Self { throws: false, raises: self.raises }
    }
    fn any(self) -> bool { self.throws || self.raises }
}

/// Infer *escaping* effects of a typed expression. A trap discharges only
/// ordinary throw; it cannot intercept raise or a fatal runtime panic.
/// Evaluation of arguments occurs outside the called function's handler,
/// so argument effects must also be included in the result.
fn expr_escape_effects(value: &TE, effects: &[EscapeEffects]) -> EscapeEffects {
    fn combine<'a>(values: impl IntoIterator<Item=&'a TE>, effects: &[EscapeEffects]) -> EscapeEffects {
        values.into_iter().fold(EscapeEffects::default(),
            |acc, v| acc.union(expr_escape_effects(v, effects)))
    }
    match &value.e {
        TExpr::I64(_) | TExpr::F64(_) | TExpr::Bool(_)
        | TExpr::StrConst(_, _) | TExpr::Local(_) | TExpr::PrintStr { .. }
        | TExpr::EnumVal(_) | TExpr::GlobalGet(_) | TExpr::Alloc(_)
        | TExpr::CollectionAlloc(_)
        | TExpr::Spawn(_) => EscapeEffects::default(),
        TExpr::IntToFloat(v) | TExpr::FNeg(v) | TExpr::Neg(v)
        | TExpr::Not(v) | TExpr::Print { value: v, .. }
        | TExpr::PrintStrVal { value: v, .. } | TExpr::AdtIs { obj: v, .. }
        | TExpr::AdtPayload(v) | TExpr::AdtPropagate { source: v, .. }
        | TExpr::FieldGet { obj: v, .. }
        | TExpr::CollectionLoad { array: v, .. }
        | TExpr::StateFieldRead { obj: v, .. }
        | TExpr::PrintObj { obj: v, .. } =>
            expr_escape_effects(v, effects),
        TExpr::Trap { value: v, .. } =>
            expr_escape_effects(v, effects).without_throw(),
        TExpr::Bin(_, a, b) | TExpr::Builtin(_, a, b)
        | TExpr::Send { target: a, value: b } =>
            combine([a.as_ref(), b.as_ref()], effects),
        TExpr::Ternary(cond, yes, no) =>
            combine([cond.as_ref(), yes.as_ref(), no.as_ref()], effects),
        TExpr::Str(_, receiver, arg) =>
            expr_escape_effects(receiver, effects)
                .union(arg.as_ref().map_or(EscapeEffects::default(),
                    |v| expr_escape_effects(v, effects))),
        TExpr::AdtNew { payload, .. } =>
            payload.as_ref().map_or(EscapeEffects::default(),
                |v| expr_escape_effects(v, effects)),
        TExpr::Call(target, args) => {
            let callee = effects.get(*target as usize).copied().unwrap_or(
                // Unknown typed call targets must fail closed, not be assumed pure.
                EscapeEffects { throws: true, raises: true });
            combine(args.iter(), effects).union(callee)
        }
    }
}

/// Compute escaping effects through typed blocks. An ordinary catch handles
/// the entire ordinary-throw effect of its protected body, including calls,
/// nested handlers and error-producing arguments; a raise always bypasses it.
/// The catch body is analyzed independently because it may itself escape.
fn stmts_escape_effects(body: &[TStmt], effects: &[EscapeEffects]) -> EscapeEffects {
    let mut all = EscapeEffects::default();
    for stmt in body {
        let next = match stmt {
            TStmt::Set(_, value) | TStmt::GlobalSet(_, value)
            | TStmt::Expr(value) | TStmt::StateRegister(value)
            | TStmt::Return(Some(value)) =>
                expr_escape_effects(value, effects),
            TStmt::Return(None) | TStmt::UnwindFrame { .. }
            | TStmt::RecoverNext | TStmt::Break | TStmt::Continue
            | TStmt::Unreachable => EscapeEffects::default(),
            TStmt::Throw(value) => expr_escape_effects(value, effects)
                .union(EscapeEffects { throws: true, raises: false }),
            TStmt::Raise(value) => expr_escape_effects(value, effects)
                .union(EscapeEffects { throws: false, raises: true }),
            TStmt::CollectionStore { array: obj, value, .. } |
            TStmt::FieldSet { obj, value, .. } |
            TStmt::StateFieldWrite { obj, value, .. } =>
                expr_escape_effects(obj, effects)
                    .union(expr_escape_effects(value, effects)),
            TStmt::StateCriticalWrite(inner) | TStmt::Block(inner) =>
                stmts_escape_effects(inner, effects),
            TStmt::If(arms, other) => {
                let mut result = other.as_ref().map_or(EscapeEffects::default(),
                    |b| stmts_escape_effects(b, effects));
                for (cond, arm) in arms {
                    result = result.union(expr_escape_effects(cond, effects))
                        .union(stmts_escape_effects(arm, effects));
                }
                result
            }
            TStmt::Loop { cond, body, update } =>
                cond.as_ref().map_or(EscapeEffects::default(),
                    |v| expr_escape_effects(v, effects))
                    .union(stmts_escape_effects(body, effects))
                    .union(stmts_escape_effects(update, effects)),
            TStmt::ForIn { source, body, .. } =>
                expr_escape_effects(source, effects)
                    .union(stmts_escape_effects(body, effects)),
            TStmt::Try { body, catch, finally, .. } => {
                let protected = stmts_escape_effects(body, effects);
                let handled = if catch.is_some() {
                    protected.without_throw()
                } else { protected };
                // An ordinary Error handler cannot execute when the
                // protected region cannot emit an ordinary Error. Ignore
                // unreachable handler effects, without discharging raises.
                let caught = if protected.throws {
                    catch.as_ref().map_or(EscapeEffects::default(),
                        |b| stmts_escape_effects(b, effects))
                } else { EscapeEffects::default() };
                let cleanup = finally.as_ref().map_or(EscapeEffects::default(),
                    |b| stmts_escape_effects(b, effects));
                handled.union(caught).union(cleanup)
            }
            // Registration expressions run immediately; callbacks run
            // only on exit/failure. Including them remains conservative.
            // In particular, we NEVER assume recover handles the current
            // function's own errors: caller catches outrank callee recover.
            TStmt::Defer { args, body, .. } |
            TStmt::Recover { args, body, .. } => {
                let captures = args.iter().fold(EscapeEffects::default(),
                    |acc, (_, arg)| acc.union(expr_escape_effects(arg, effects)));
                captures.union(stmts_escape_effects(body, effects))
            }
        };
        all = all.union(next);
        // The same structural definite-exit analysis used for guest
        // emission also establishes that later statements cannot execute.
        // Never infer an outgoing effect from dead code after return/raise.
        if returns(std::slice::from_ref(stmt)) { break; }
    }
    all
}

/// Infer escaping effects by monotone fixed point, so recursion and
/// mutually recursive call groups converge without unsound assumptions.
/// Validate each cleanup body with those exact effects. A callee that
/// catches its own throw, or a call wrapped in \`trap\`, can now be used
/// safely within cleanup; an escaping raise can never be suppressed by
/// an ordinary catch/trap. Unreachable-code precision remains deliberately
/// conservative until the CFG effect solver is complete.
fn audit_cleanup_call_effects(funcs: &[TFunc], declared: &[Func]) -> R<()> {
    let mut effects = vec![EscapeEffects::default(); funcs.len()];
    loop {
        let mut changed = false;
        for (index, f) in funcs.iter().enumerate() {
            let next = stmts_escape_effects(&f.body, &effects);
            if next != effects[index] {
                effects[index] = effects[index].union(next);
                changed = true;
            }
        }
        if !changed { break; }
    }
    // A clause list asserts an upper bound on the ordinary exceptional
    // channels, not merely an annotation for documentation. Omission of a
    // clause inside an explicit list means that effect cannot escape.
    // Fully unannotated legacy functions remain inference-only.
    for (index, f) in declared.iter().enumerate() {
        let Some(contract) = f.declared_effects else { continue; };
        let actual = effects[index];
        if (actual.throws && !contract.throws) || (actual.raises && !contract.raises) {
            let missing = match (actual.throws && !contract.throws, actual.raises && !contract.raises) {
                (true, true) => "throws(Error), raises(Error)",
                (true, false) => "throws(Error)",
                (false, true) => "raises(Error)",
                (false, false) => unreachable!(),
            };
            return Err(Diagnostic::new(f.pos, "E_EFFECT",
                format!("function '{}' declares an incomplete exceptional-effect upper bound: escaping {missing}", f.name)));
        }
    }

    // Only registration is limited to the top-level browser profile:
    // try/finally and branch nesting can already be arbitrary.
    fn verify_scopes(body: &[TStmt], effects: &[EscapeEffects]) -> R<()> {
        for stmt in body {
            match stmt {
                TStmt::Defer { body: cleanup, pos, .. } |
                TStmt::Recover { body: cleanup, pos, .. } => {
                    if stmts_escape_effects(cleanup, effects).any() {
                        return Err(Diagnostic::new(*pos, "E_UNWIND_EFFECT",
                            "cleanup/recovery callback has a provably escaping throw or raise"));
                    }
                }
                TStmt::Try { body: inner, catch, finally, pos, .. } => {
                    if finally.as_ref().is_some_and(|b|
                        stmts_escape_effects(b, effects).any())
                    {
                        return Err(Diagnostic::new(*pos, "E_UNWIND_EFFECT",
                            "finally has an escaping throw or raise"));
                    }
                    verify_scopes(inner, effects)?;
                    if let Some(handler) = catch {
                        verify_scopes(handler, effects)?;
                    }
                    if let Some(cleanup) = finally {
                        verify_scopes(cleanup, effects)?;
                    }
                }
                TStmt::If(arms, other) => {
                    for (_, inner) in arms { verify_scopes(inner, effects)?; }
                    if let Some(inner) = other { verify_scopes(inner, effects)?; }
                }
                TStmt::Loop { body: inner, update, .. } => {
                    verify_scopes(inner, effects)?;
                    verify_scopes(update, effects)?;
                }
                TStmt::ForIn { body: inner, .. } |
                TStmt::Block(inner) | TStmt::StateCriticalWrite(inner) =>
                    verify_scopes(inner, effects)?,
                _ => {}
            }
        }
        Ok(())
    }
    for f in funcs { verify_scopes(&f.body, &effects)?; }
    Ok(())
}

fn tn_plain(t: Type, tn: &[(String, Pos)], classes: &[String], enums: &[EnumDecl], actors: &[String]) -> String {
    match t {
        Type::Class(i) => classes[i as usize].clone(),
        Type::Enum(i) => enums[i as usize].name.clone(),
        Type::ActorRef(i) => format!("ActorRef<{}>", actors[i as usize]),
        Type::Named(i) | Type::NamedRef(i) | Type::Callable(i) => tn[i as usize].0.clone(),
        t => t.name().to_string(),
    }
}

/// Actors are isolated from sibling classes, enums and other actors.
fn actor_type_ok(g: &Globals, actor: &str, t: Type, pos: Pos) -> R<()> {
    match t {
        Type::Class(i) => Err(isolation(pos, actor, "sibling class", &g.classes[i as usize].name)),
        Type::Enum(i) => Err(isolation(pos, actor, "sibling enum", &g.enums[i as usize].name)),
        Type::ActorRef(i) => Err(isolation(pos, actor, "actor", &g.actors[i as usize].name)),
        _ => Ok(()),
    }
}

fn field_init(g: &Globals, f: &Field, ty: Type, owner: &str, actor: bool, imports: &mut Vec<Import>, data: &mut Vec<u8>) -> R<TE> {
    if !const_init(&f.init) {
        return Err(Diagnostic::new(
            f.init.pos,
            "E_UNSUPPORTED",
            format!(
                "field initializer '{owner}.{}' must be a constant expression; initialize computed values in the constructor",
                f.name
            ),
        ));
    }
    let mut cx = FnCx::new(g, Owner::FieldInit { actor }, Type::Void, imports, data);
    let v = cx.value(&f.init)?;
    if v.ty != ty {
        return Err(type_err(
            f.init.pos,
            format!(
                "field '{owner}.{}' has type {} but its initializer has type {}",
                f.name,
                g.tn(ty),
                g.tn(v.ty)
            ),
        ));
    }
    Ok(v)
}

/// Check one callable body. `named` are the wasm parameters in order.
#[allow(clippy::too_many_arguments)]
/// A constructor receiver is a temporary initialization capability, not a
/// publishable reference. This admission pass operates on the *parsed AST*,
/// so both inline and out-of-line constructors have exactly the same rule.
/// Only direct field projection/assignment is allowed before publication.
/// Nested callbacks/closures cannot capture even a direct field projection.
fn constructor_self_expr(e: &Expr, captured: bool) -> R<()> {
    let denied = || Diagnostic::new(e.pos, "E_OWNERSHIP",
        "under-construction self cannot escape, be captured or dispatch methods");
    match &e.kind {
        ExprKind::SelfRef => Err(denied()),
        ExprKind::Member(base, _) if matches!(base.kind, ExprKind::SelfRef) => {
            if captured { Err(denied()) } else { Ok(()) }
        }
        ExprKind::Member(base, _) => constructor_self_expr(base, captured),
        ExprKind::MethodCall(base, _, args) => {
            // An arbitrary method can publish its receiver, even if it
            // returns an innocent scalar. Never dispatch on construction self.
            constructor_self_expr(base, true)?;
            for arg in args { constructor_self_expr(arg, captured)?; }
            Ok(())
        }
        ExprKind::Unary(_, inner) | ExprKind::Trap(inner)
        | ExprKind::Ownership(_, _, inner) | ExprKind::Propagate(inner) =>
            constructor_self_expr(inner, captured),
        ExprKind::Binary(_, left, right) => {
            constructor_self_expr(left, captured)?;
            constructor_self_expr(right, captured)
        }
        ExprKind::Ternary(cond, yes, no) => {
            constructor_self_expr(cond, captured)?;
            constructor_self_expr(yes, captured)?;
            constructor_self_expr(no, captured)
        }
        ExprKind::Call(_, args) | ExprKind::New(_, args) | ExprKind::Array(args) => {
            for arg in args { constructor_self_expr(arg, captured)?; }
            Ok(())
        }
        ExprKind::Lambda { body, .. } => match body {
            LambdaBody::Expression(expr) => constructor_self_expr(expr, true),
            LambdaBody::Statement(stmt) =>
                constructor_self_stmts(std::slice::from_ref(stmt.as_ref()), true),
            LambdaBody::Block(stmts) => constructor_self_stmts(stmts, true),
        },
        ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Bool(_)
        | ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::StateRead(_)
        | ExprKind::Spawn(_) => Ok(()),
    }
}

fn constructor_self_stmts(body: &[Stmt], captured: bool) -> R<()> {
    for stmt in body {
        match stmt {
            Stmt::Bind { init, .. } => constructor_self_expr(init, captured)?,
            Stmt::Assign { value, .. } => constructor_self_expr(value, captured)?,
            Stmt::FieldAssign { target, value, .. } => {
                if !matches!(target.kind, ExprKind::SelfRef) || captured {
                    constructor_self_expr(target, captured)?;
                }
                constructor_self_expr(value, captured)?;
            }
            Stmt::Expr(expr) | Stmt::Throw(expr, _) | Stmt::Raise(expr, _)
            | Stmt::Yield(expr, _) | Stmt::YieldFrom(expr, _) =>
                constructor_self_expr(expr, captured)?,
            Stmt::Return(Some(expr), _) => constructor_self_expr(expr, captured)?,
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
            Stmt::StateWrite { body, .. } | Stmt::Loop { body, .. }
            | Stmt::Block(body) => constructor_self_stmts(body, captured)?,
            Stmt::Try { body, catch, finally, .. } => {
                constructor_self_stmts(body, captured)?;
                if let Some((_, handler)) = catch {
                    constructor_self_stmts(handler, captured)?;
                }
                if let Some(cleanup) = finally {
                    constructor_self_stmts(cleanup, captured)?;
                }
            }
            Stmt::Defer { args, body, .. } | Stmt::Recover { args, body, .. } => {
                for arg in args { constructor_self_expr(arg, captured)?; }
                constructor_self_stmts(body, true)?;
            }
            Stmt::If { arms, otherwise, .. } => {
                for (cond, body) in arms {
                    constructor_self_expr(cond, captured)?;
                    constructor_self_stmts(body, captured)?;
                }
                if let Some(other) = otherwise {
                    constructor_self_stmts(other, captured)?;
                }
            }
            Stmt::While { cond, body, .. } => {
                constructor_self_expr(cond, captured)?;
                constructor_self_stmts(body, captured)?;
            }
            Stmt::For { init, cond, update, body, .. } => {
                if let Some(initializer) = init {
                    constructor_self_stmts(std::slice::from_ref(initializer.as_ref()), captured)?;
                }
                if let Some(cond) = cond { constructor_self_expr(cond, captured)?; }
                if let Some(update) = update {
                    constructor_self_stmts(std::slice::from_ref(update.as_ref()), captured)?;
                }
                constructor_self_stmts(body, captured)?;
            }
            Stmt::ForIn { source, body, .. } => {
                constructor_self_expr(source, captured)?;
                constructor_self_stmts(body, captured)?;
            }
            Stmt::Match { subject, arms, .. } => {
                constructor_self_expr(subject, captured)?;
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        constructor_self_expr(guard, captured)?;
                    }
                    constructor_self_stmts(&arm.body, captured)?;
                }
            }
        }
    }
    Ok(())
}

fn body_check(
    g: &Globals,
    owner: Owner,
    named: &[(&str, Type, bool)],
    mail: Option<(&str, Type)>,
    ret: Type,
    body: &[Stmt],
    label: &str,
    pos: Pos,
    imports: &mut Vec<Import>,
    data: &mut Vec<u8>,
) -> R<(Vec<TStmt>, Vec<Type>)> {
    // This is shared by inline class constructors and out-of-line headers
    // after they are lowered to the same production ClassDecl AST.
    if matches!(owner, Owner::Class { ctor: true, .. }) {
        constructor_self_stmts(body, false)?;
    }
    let mut cx = FnCx::new(g, owner, ret, imports, data);
    cx.nparams = named.len() as u32;
    if let Some((mail_name, payload)) = mail {
        cx.scopes[0].push(Local {
            name: mail_name.to_string(),
            slot: 0,
            ty: Type::Int,
            mutable: false,
            mail: Some(payload),
        });
    } else {
        for (i, (n, t, m)) in named.iter().enumerate() {
            cx.scopes[0].push(Local {
                name: n.to_string(),
                slot: i as u32,
                ty: *t,
                mutable: *m,
                mail: None,
            });
        }
    }
    cx.scopes.push(Vec::new());
    let mut tbody = cx.stmts(body)?;
    if let Some((ret, saved, msg, kind, pending)) = cx.unwind {
        tbody.insert(0, TStmt::UnwindFrame { ret, saved, msg, kind, pending });
    }
    if ret != Type::Void && !returns(&tbody) {
        let what = if matches!(owner, Owner::TopLevel) { "fnc" } else { "method" };
        return Err(Diagnostic::new(
            pos,
            "E_RETURN",
            format!("non-void {what} '{label}' must explicitly return on every path"),
        ));
    }
    Ok((tbody, cx.locals))
}

/// Definite-return analysis matching the Java reference: an `if` returns
/// only with an `else` whose every arm returns; an unconditional `loop`
/// without a `break` never falls through; `while true` is not special.
fn returns(body: &[TStmt]) -> bool {
    body.iter().any(|s| match s {
        TStmt::Return(_) | TStmt::Throw(_) | TStmt::Unreachable => true,
        TStmt::Raise(_) | TStmt::RecoverNext => true,
        TStmt::Try { body, catch, finally, .. } =>
            finally.as_ref().is_some_and(|f| returns(f))
                || (returns(body) && catch.as_ref().is_none_or(|c| returns(c))),
        TStmt::If(arms, Some(other)) => arms.iter().all(|(_, b)| returns(b)) && returns(other),
        TStmt::Loop { cond: None, body, .. } => !breaks(body),
        TStmt::Block(b) | TStmt::StateCriticalWrite(b) => returns(b),
        _ => false,
    })
}

/// Exhaustive, allowlisted purity verification over the fully typed tree.
///
/// Unlike a denylist, these matches intentionally have NO wildcard arm:
/// extending either TExpr or TStmt requires explicitly reviewing the new
/// operation's effects before the Rust compiler can build. A benign-looking
/// wrapper must not hide an impure child expression or branch.
fn pure_expr(value: &TE, pure_indices: &BTreeSet<u32>) -> bool {
    match &value.e {
        TExpr::I64(_) | TExpr::F64(_) | TExpr::Bool(_) |
        TExpr::StrConst(_, _) | TExpr::Local(_) | TExpr::EnumVal(_) => true,
        TExpr::IntToFloat(a) | TExpr::FNeg(a) |
        TExpr::Neg(a) | TExpr::Not(a) |
        TExpr::AdtIs { obj: a, .. } | TExpr::AdtPayload(a) =>
            pure_expr(a, pure_indices),
        TExpr::Bin(op, a, b) => {
            // Arithmetic, comparisons and eager boolean logic have no
            // observable external effects; newly added operators must be
            // reviewed explicitly, even if they reuse TExpr::Bin.
            let read_only = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div |
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le |
                BinOp::Gt | BinOp::Ge | BinOp::And | BinOp::Or => true,
            };
            read_only && pure_expr(a, pure_indices) && pure_expr(b, pure_indices)
        }
        TExpr::Builtin(op, a, b) => {
            // Fail closed when the builtin catalog adds a new operation.
            let read_only = match op {
                Builtin::And | Builtin::Or | Builtin::Xor => true,
            };
            read_only && pure_expr(a, pure_indices) && pure_expr(b, pure_indices)
        }
        TExpr::Ternary(c, a, b) =>
            pure_expr(c, pure_indices) &&
            pure_expr(a, pure_indices) && pure_expr(b, pure_indices),
        TExpr::Call(target, args) =>
            pure_indices.contains(target) &&
            args.iter().all(|arg| pure_expr(arg, pure_indices)),
        TExpr::Str(op, a, b) => {
            // Exhaustive over string helpers too: a new helper may allocate
            // or mutate memory, so it cannot silently inherit purity.
            let read_only = match op {
                StrOp::Eq | StrOp::StartsWith | StrOp::EndsWith |
                StrOp::Contains | StrOp::Trim | StrOp::Cmp => true,
                StrOp::Concat => false,
            };
            read_only && pure_expr(a, pure_indices) &&
                b.as_ref().is_none_or(|b| pure_expr(b, pure_indices))
        },
        // Disallowed effects include heap mutation/allocations, object/actor
        // state reads, I/O, actor operations, guest exception handling and
        // propagation. Keep these explicit when evolving the language.
        TExpr::Print { .. } | TExpr::PrintStr { .. } |
        TExpr::PrintStrVal { .. } | TExpr::PrintObj { .. } |
        TExpr::FieldGet { .. } | TExpr::StateFieldRead { .. } | TExpr::GlobalGet(_) |
        TExpr::CollectionLoad { .. } | TExpr::CollectionAlloc(_) |
        TExpr::Alloc(_) | TExpr::Spawn(_) | TExpr::Send { .. } |
        TExpr::AdtNew { .. } | TExpr::Trap { .. } |
        TExpr::AdtPropagate { .. } => false,
    }
}

fn pure_stmts(body: &[TStmt], pure_indices: &BTreeSet<u32>) -> bool {
    body.iter().all(|stmt| match stmt {
        TStmt::Set(_, value) | TStmt::Expr(value) =>
            pure_expr(value, pure_indices),
        TStmt::Return(value) =>
            value.as_ref().is_none_or(|value| pure_expr(value, pure_indices)),
        TStmt::If(arms, otherwise) =>
            arms.iter().all(|(cond, block)|
                pure_expr(cond, pure_indices) && pure_stmts(block, pure_indices)) &&
            otherwise.as_ref().is_none_or(|block| pure_stmts(block, pure_indices)),
        TStmt::Loop { cond, body, update } =>
            cond.as_ref().is_none_or(|cond| pure_expr(cond, pure_indices)) &&
            pure_stmts(body, pure_indices) && pure_stmts(update, pure_indices),
        TStmt::Block(body) => pure_stmts(body, pure_indices),
        TStmt::Break | TStmt::Continue | TStmt::Unreachable => true,
        TStmt::CollectionStore { .. } | TStmt::FieldSet { .. } | TStmt::StateFieldWrite { .. } |
        TStmt::StateCriticalWrite(_) | TStmt::StateRegister(_) |
        TStmt::GlobalSet(_, _) |
        TStmt::Throw(_) | TStmt::ForIn { .. } => false,
        TStmt::Raise(_) | TStmt::UnwindFrame { .. } | TStmt::Try { .. } |
        TStmt::Defer { .. } | TStmt::Recover { .. } | TStmt::RecoverNext => false,
    })
}

/// Whether any expression node in `body` satisfies `f`.
fn any_in_stmts(body: &[TStmt], f: &dyn Fn(&TE) -> bool) -> bool {
    body.iter().any(|s| match s {
        TStmt::Set(_, e) | TStmt::GlobalSet(_, e) | TStmt::Expr(e) |
        TStmt::StateRegister(e) | TStmt::Throw(e) | TStmt::Return(Some(e)) => any_in(e, f),
        TStmt::FieldSet { obj, value, .. } | TStmt::StateFieldWrite { obj, value, .. } =>
            any_in(obj, f) || any_in(value, f),
        TStmt::CollectionStore { array, value, .. } =>
            any_in(array, f) || any_in(value, f),
        TStmt::If(arms, other) => {
            arms.iter().any(|(c, b)| any_in(c, f) || any_in_stmts(b, f)) || other.as_ref().is_some_and(|b| any_in_stmts(b, f))
        }
        TStmt::Loop { cond, body, update } => {
            cond.as_ref().is_some_and(|c| any_in(c, f)) || any_in_stmts(body, f) || any_in_stmts(update, f)
        }
        TStmt::ForIn { source, body, .. } => any_in(source, f) || any_in_stmts(body, f),
        TStmt::Raise(e) => any_in(e, f),
        TStmt::Try { body, catch, finally, .. } => any_in_stmts(body, f)
            || catch.as_ref().is_some_and(|b| any_in_stmts(b, f))
            || finally.as_ref().is_some_and(|b| any_in_stmts(b, f)),
        TStmt::Defer { args, body, .. } => args.iter().any(|(_, e)| any_in(e, f)) || any_in_stmts(body, f),
        TStmt::Recover { args, body, .. } => args.iter().any(|(_, e)| any_in(e, f)) || any_in_stmts(body, f),
        TStmt::UnwindFrame { .. } | TStmt::RecoverNext => false,
        TStmt::Block(b) | TStmt::StateCriticalWrite(b) => any_in_stmts(b, f),
        TStmt::Return(None) | TStmt::Break | TStmt::Continue | TStmt::Unreachable => false,
    })
}

fn any_in(e: &TE, f: &dyn Fn(&TE) -> bool) -> bool {
    if f(e) {
        return true;
    }
    match &e.e {
        TExpr::Trap { value, .. } => any_in(value, f),
        TExpr::Neg(a) | TExpr::Not(a) | TExpr::FNeg(a) | TExpr::IntToFloat(a) => any_in(a, f),
        TExpr::Bin(_, a, b) | TExpr::Builtin(_, a, b) => any_in(a, f) || any_in(b, f),
        TExpr::Ternary(c, a, b) => any_in(c, f) || any_in(a, f) || any_in(b, f),
        TExpr::Str(_, a, b) => any_in(a, f) || b.as_ref().is_some_and(|b| any_in(b, f)),
        TExpr::Call(_, args) => args.iter().any(|a| any_in(a, f)),
        TExpr::AdtNew { payload, .. } => payload.as_ref().is_some_and(|p| any_in(p, f)),
        TExpr::AdtIs { obj, .. } | TExpr::AdtPayload(obj) => any_in(obj, f),
        TExpr::AdtPropagate { source, .. } => any_in(source, f),
        TExpr::Print { value, .. } | TExpr::PrintStrVal { value, .. } => any_in(value, f),
        TExpr::FieldGet { obj, .. } | TExpr::StateFieldRead { obj, .. } |
        TExpr::PrintObj { obj, .. } => any_in(obj, f),
        TExpr::CollectionLoad { array, .. } => any_in(array, f),
        TExpr::Send { target, value } => any_in(target, f) || any_in(value, f),
        _ => false,
    }
}

/// An actual ordinary throw, including one nested in a conditional or loop.
fn guest_eh_in_stmts(body: &[TStmt]) -> bool {
    body.iter().any(|s| match s {
        TStmt::Throw(_) => true,
        TStmt::Raise(_) | TStmt::Try { .. } | TStmt::UnwindFrame { .. } => true,
        TStmt::If(arms, other) => arms.iter().any(|(_, b)| guest_eh_in_stmts(b))
            || other.as_ref().is_some_and(|b| guest_eh_in_stmts(b)),
        TStmt::Loop { body, update, .. } =>
            guest_eh_in_stmts(body) || guest_eh_in_stmts(update),
        TStmt::ForIn { body, .. } => guest_eh_in_stmts(body),
        TStmt::Block(b) | TStmt::StateCriticalWrite(b) => guest_eh_in_stmts(b),
        _ => false,
    })
}

fn uses_str(e: &TE) -> bool {
    e.ty == Type::Str
        || matches!(e.e, TExpr::Str(..) | TExpr::StrConst(..) | TExpr::PrintStrVal { .. })
        || matches!(&e.e, TExpr::PrintObj { pieces, .. } if pieces.iter().any(|p| matches!(p, PrintPiece::Field(_, Type::Str))))
}

fn uses_concat(e: &TE) -> bool {
    matches!(e.e, TExpr::Str(StrOp::Concat, ..))
}

/// Whether a loop body contains a `break` that targets this loop.
fn breaks(body: &[TStmt]) -> bool {
    body.iter().any(|s| match s {
        TStmt::Break => true,
        TStmt::If(arms, other) => arms.iter().any(|(_, b)| breaks(b)) || other.as_ref().is_some_and(|b| breaks(b)),
        TStmt::Block(b) | TStmt::StateCriticalWrite(b) => breaks(b),
        _ => false,
    })
}

impl<'a> FnCx<'a> {
    fn new(g: &'a Globals<'a>, owner: Owner, ret: Type, imports: &'a mut Vec<Import>, data: &'a mut Vec<u8>) -> Self {
        FnCx {
            g,
            owner,
            ret,
            scopes: vec![Vec::new()],
            locals: Vec::new(),
            nparams: 0,
            loops: 0,
            loop_floors: Vec::new(),
            moved: BTreeSet::new(),
            loans: BTreeMap::new(),
            state_write_scope: false,
            state_read_scope: false,
            imports,
            data,
            unwind: None,
            cleanup_depth: 0,
            recover_cursor: None,
            recover_error: None,
        }
    }

    /// Allocate the function's unwind slots once (top-level `fnc` only).
    fn unwind_frame(&mut self, pos: Pos, what: &str) -> R<()> {
        if self.owner != Owner::TopLevel {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                format!("'{what}' in class and actor methods needs supervisor/cleanup integration")));
        }
        if self.cleanup_depth > 0 {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                format!("'{what}' inside a defer/recover body is not admitted: cleanup must not unwind")));
        }
        if self.unwind.is_none() {
            let ret = if self.ret == Type::Void { None } else { Some(self.temp(self.ret, pos)?) };
            let saved = self.temp(Type::Bool, pos)?;
            let msg = self.temp(Type::Int, pos)?;
            let kind = self.temp(Type::Bool, pos)?;
            let pending = self.temp(Type::Bool, pos)?;
            self.unwind = Some((ret, saved, msg, kind, pending));
        }
        Ok(())
    }

    /// defer/recover register only at the function's top-level scope, so
    /// the static LIFO order equals the dynamic registration order.
    fn top_registration(&self, pos: Pos, what: &str) -> R<()> {
        if self.scopes.len() != 2 || self.loops != 0 {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                format!("'{what}' is admitted only at the top level of a fnc body, not in a nested block or loop")));
        }
        Ok(())
    }

    /// Evaluate explicitly captured scalar/string arguments exactly once at
    /// registration. The resulting compiler-owned slots outlive the failed
    /// scope and are read by the deferred/recovery body on its owning task.
    fn cleanup_factory_args(&mut self, params: &[(String, Type, Pos)],
                            args: &[Expr], pos: Pos, kind: &str)
        -> R<CleanupCaptured>
    {
        if params.len() != args.len() {
            return Err(Diagnostic::new(pos, "E_ARITY", format!(
                "{kind} factory expects {} argument(s), found {}", params.len(), args.len())));
        }
        let mut sets = Vec::new();
        let mut bound = Vec::new();
        for ((name, ty, ppos), arg) in params.iter().zip(args) {
            let ty = self.resolve(*ty, *ppos)?;
            if !matches!(ty, Type::Int | Type::Bool | Type::Str | Type::Float) {
                return Err(Diagnostic::new(*ppos, "E_UNSUPPORTED_TYPE",
                    "cleanup factory parameters are restricted to scalar and string values"));
            }
            let v = self.consume_expected(arg, ty)?;
            if v.ty != ty {
                return Err(type_err(arg.pos, format!(
                    "{kind} factory argument has type {} but expected {}", self.tn(v.ty), self.tn(ty))));
            }
            let slot = self.temp(ty, *ppos)?;
            sets.push((slot, v));
            bound.push(Local { name: name.clone(), slot, ty, mutable: false, mail: None });
        }
        Ok((sets, bound))
    }

    /// Check a cleanup/recovery body in an isolated scope: it cannot see the
    /// enclosing locals (no by-reference capture lifetime is verified), only
    /// the explicit factory parameters in `bound`.
    fn isolated(&mut self, bound: Vec<Local>, cursor: Option<String>,
                error: Option<String>, body: &[Stmt]) -> R<Vec<TStmt>> {
        let scopes = std::mem::replace(&mut self.scopes, vec![bound, Vec::new()]);
        let loops = std::mem::replace(&mut self.loops, 0);
        let moved = std::mem::take(&mut self.moved);
        let loans = std::mem::take(&mut self.loans);
        let prev_cursor = std::mem::replace(&mut self.recover_cursor, cursor);
        let prev_error = std::mem::replace(&mut self.recover_error, error);
        self.cleanup_depth += 1;
        let r = self.stmts(body);
        self.cleanup_depth -= 1;
        self.recover_cursor = prev_cursor;
        self.recover_error = prev_error;
        self.loans = loans;
        self.moved = moved;
        self.loops = loops;
        self.scopes = scopes;
        r
    }

    /// The message of an admitted `throw`/`raise` operand:
    /// `Error(message)` or `new Error(message)`.
    fn guest_error_message(&mut self, error: &Expr, what: &str, pos: Pos) -> R<TE> {
        if self.owner != Owner::TopLevel {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                format!("ordinary {what} in class and actor methods needs supervisor/cleanup integration")));
        }
        if self.cleanup_depth > 0 {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                format!("'{what}' inside a defer/recover body would replace the pending failure")));
        }
        let args = match &error.kind {
            ExprKind::Call(name, args) | ExprKind::New(name, args) if name == "Error" => args,
            _ => return Err(type_err(error.pos,
                format!("{what} requires an Error subclass; this browser slice admits only {what} Error(message)"))),
        };
        if args.len() != 1 {
            return Err(Diagnostic::new(error.pos, "E_ARITY",
                "Error(message) requires exactly one string argument"));
        }
        if self.g.names.contains_key("Error") || self.g.class("Error").is_some() {
            return Err(Diagnostic::new(error.pos, "E_RESERVED",
                "the guest Error constructor cannot be shadowed"));
        }
        let msg = self.value(&args[0])?;
        if msg.ty != Type::Str {
            return Err(type_err(args[0].pos, "Error(message) requires a string message"));
        }
        Ok(msg)
    }

    fn tn(&self, t: Type) -> String {
        self.g.tn(t)
    }

    fn actor_name(&self) -> Option<&str> {
        match self.owner {
            Owner::Actor { a } => Some(&self.g.actors[a as usize].name),
            _ => None,
        }
    }

    fn lookup(&self, name: &str) -> Option<&Local> {
        self.scopes.iter().rev().flat_map(|s| s.iter().rev()).find(|l| l.name == name)
    }

    fn resolve(&self, t: Type, pos: Pos) -> R<Type> {
        let classes: Vec<String> = self.g.classes.iter().map(|c| c.name.clone()).collect();
        let actors: Vec<String> = self.g.actors.iter().map(|a| a.name.clone()).collect();
        let t = resolve(t, self.g.type_names, &classes, self.g.enums, &actors)?;
        if let Some(a) = self.actor_name() {
            actor_type_ok(self.g, a, t, pos)?;
        }
        Ok(t)
    }

    fn declare(&mut self, name: &str, ty: Type, mutable: bool, pos: Pos) -> R<u32> {
        if self.scopes.last().unwrap().iter().any(|l| l.name == name) {
            return Err(Diagnostic::new(pos, "E_DUPLICATE", format!("duplicate binding '{name}'")));
        }
        if name == "self" {
            return Err(Diagnostic::new(pos, "E_RESERVED", "'self' cannot be rebound"));
        }
        // An ErrorView and RecoveryCursor are compiler-issued capabilities, not
        // ordinary locals. Shadowing either binder would make an ordinary
        // expression such as err.message or cursor.next() resolve to the
        // wrong object and could counterfeit terminal recovery control flow.
        if self.cleanup_depth > 0 &&
            (self.recover_error.as_deref() == Some(name)
                || self.recover_cursor.as_deref() == Some(name))
        {
            return Err(Diagnostic::new(pos, "E_RESERVED",
                format!("recovery capability '{name}' cannot be shadowed")));
        }
        let slot = self.temp(ty, pos)?;
        self.scopes.last_mut().unwrap().push(Local {
            name: name.to_string(),
            slot,
            ty,
            mutable,
            mail: None,
        });
        Ok(slot)
    }

    /// A fresh unnamed local.
    fn temp(&mut self, ty: Type, pos: Pos) -> R<u32> {
        if self.locals.len() >= MAX_LOCALS {
            return Err(Diagnostic::new(
                pos,
                "E_SOURCE_LIMIT",
                format!("more than {MAX_LOCALS} locals in one function"),
            ));
        }
        let slot = self.nparams + self.locals.len() as u32;
        self.locals.push(ty);
        Ok(slot)
    }

    fn pop_scope(&mut self) {
        if let Some(ended) = self.scopes.pop() {
            for l in ended {
                self.loans.remove(&l.slot);
                self.moved.remove(&l.slot);
            }
        }
    }

    fn scoped(&mut self, body: &[Stmt]) -> R<Vec<TStmt>> {
        self.scopes.push(Vec::new());
        let r = self.stmts(body);
        self.pop_scope();
        r
    }

    fn looped(&mut self, body: &[Stmt]) -> R<Vec<TStmt>> {
        self.loops += 1;
        self.loop_floors.push(self.nparams + self.locals.len() as u32);
        let r = self.scoped(body);
        self.loop_floors.pop();
        self.loops -= 1;
        r
    }

    /// A loop condition is evaluated before EACH iteration, not once.
    /// Reject ownership moves from already-live locals even if a conditional
    /// branch, break, or early return would make the second evaluation rare.
    /// Evaluating it without a loop floor would silently permit repeated
    /// take! owner and repeated implicit class transfers.
    fn repeated_cond(&mut self, e: &Expr, what: &str) -> R<TE> {
        self.loop_floors.push(self.nparams + self.locals.len() as u32);
        let checked = self.cond(e, what);
        self.loop_floors.pop();
        checked
    }

    fn stmts(&mut self, body: &[Stmt]) -> R<Vec<TStmt>> {
        body.iter().map(|s| self.stmt(s)).collect()
    }

    fn cond(&mut self, e: &Expr, what: &str) -> R<TE> {
        let c = self.expr(e)?;
        if c.ty != Type::Bool {
            return Err(type_err(
                e.pos,
                format!("{what} condition must have type bool, found {}", self.tn(c.ty)),
            ));
        }
        Ok(c)
    }

    fn stmt(&mut self, s: &Stmt) -> R<TStmt> {
        Ok(match s {
            Stmt::Bind { kind, name, ty, init, pos } => {
                if let ExprKind::Ownership(OwnershipOp::Borrow, mutable, inner) = &init.kind {
                    return self.borrow_binding(*kind, name, *ty, inner, *mutable, *pos);
                }
                let want = match ty {
                    Some(t) => Some(self.resolve(*t, *pos)?),
                    None => None,
                };
                let v = match want {
                    Some(t) => self.consume_expected(init, t)?,
                    None => self.consume(init)?,
                };
                if let Some(t) = want {
                    if t != v.ty {
                        return Err(type_err(
                            init.pos,
                            format!(
                                "binding '{name}' has type {} but its initializer has type {}",
                                self.tn(t),
                                self.tn(v.ty)
                            ),
                        ));
                    }
                }
                // Unowned generator-valued locals could escape a close path.
                if v.ty == Type::GeneratorInt {
                    return Err(Diagnostic::new(*pos, "E_GENERATOR_OWNERSHIP",
                        "generator handles must be consumed by for-in until owned bindings support close"));
                }
                let slot = self.declare(name, v.ty, *kind == BindKind::Let, *pos)?;
                TStmt::Set(slot, v)
            }
            Stmt::Assign { name, value, pos } => {
                let (slot, ty, mutable, mail) = match self.lookup(name) {
                    Some(l) => (l.slot, l.ty, l.mutable, l.mail.is_some()),
                    None => return Err(Diagnostic::new(*pos, "E_UNBOUND", format!("unknown name '{name}'"))),
                };
                if !mutable || mail {
                    return Err(Diagnostic::new(
                        *pos,
                        "E_IMMUTABLE",
                        format!("cannot reassign val binding '{name}'"),
                    ));
                }
                if self.loans.contains_key(&slot) || self.loans.values().any(|loan| loan.owner == slot) {
                    return Err(Diagnostic::new(*pos, "E_BORROW", "cannot reassign a borrowed local or owner while the loan is live"));
                }
                let v = self.consume_expected(value, ty)?;
                if v.ty != ty {
                    return Err(type_err(
                        value.pos,
                        format!("cannot assign {} to '{name}' of type {}", self.tn(v.ty), self.tn(ty)),
                    ));
                }
                // a reassigned object binding owns a value again
                self.moved.remove(&slot);
                TStmt::Set(slot, v)
            }
            Stmt::StateWrite { body, pos } => {
                let allowed = matches!(self.owner,
                    Owner::Class { c, ctor: false, is_static: false }
                    if self.g.classes[c as usize].state_container);
                if !allowed || self.state_write_scope {
                    return Err(Diagnostic::new(*pos, "E_STATE_BORROW",
                        "critical-write requires a non-nested protected state container method"));
                }
                self.state_write_scope = true;
                let checked = self.scoped(body);
                self.state_write_scope = false;
                TStmt::StateCriticalWrite(checked?)
            }
            Stmt::FieldAssign { target, field, value, pos } => self.field_assign(target, field, value, *pos)?,
            Stmt::Expr(Expr { kind: ExprKind::MethodCall(base, method, args), pos })
                if method == "next" && args.is_empty()
                    && matches!(&base.kind, ExprKind::Var(n) if self.recover_cursor.as_deref() == Some(n.as_str())) =>
            {
                let _ = pos;
                TStmt::RecoverNext
            }
            Stmt::Raise(error, pos) => {
                let msg = self.guest_error_message(error, "raise", *pos)?;
                TStmt::Raise(msg)
            }
            Stmt::Try { body, catch, finally, pos } => {
                self.unwind_frame(*pos, "try")?;
                let saved = self.temp(Type::Bool, *pos)?;
                // break/continue may not bypass a handler or finally block.
                let loops = std::mem::replace(&mut self.loops, 0);
                let checked = (|| -> R<TStmt> {
                    let body = self.scoped(body)?;
                    // Conservative ownership: the handler and finally see
                    // every move the body might have made before failing.
                    let catch = match catch {
                        Some((_binder, handler)) => Some(self.scoped(handler)?),
                        None => None,
                    };
                    let finally = match finally {
                        Some(cleanup) => {
                            let cleanup = self.scoped(cleanup)?;
                            if exits_anywhere(&cleanup) {
                                return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                                    "a finally block must not return, throw or raise: it would replace the pending outcome"));
                            }
                            Some(cleanup)
                        }
                        None => None,
                    };
                    Ok(TStmt::Try { saved, body, catch, finally, pos: *pos })
                })();
                self.loops = loops;
                checked?
            }
            Stmt::Defer { params, body, args, pos } => {
                self.top_registration(*pos, "defer")?;
                self.unwind_frame(*pos, "defer")?;
                let (sets, bound) = self.cleanup_factory_args(params, args, *pos, "defer")?;
                let flag = self.temp(Type::Bool, *pos)?;
                let body = self.isolated(bound, None, None, body)?;
                TStmt::Defer { flag, args: sets, body, pos: *pos }
            }
            Stmt::Recover { params, err, cursor, body, args, pos } => {
                self.top_registration(*pos, "recover")?;
                self.unwind_frame(*pos, "recover")?;
                let (sets, bound) = self.cleanup_factory_args(params, args, *pos, "recover")?;
                let flag = self.temp(Type::Bool, *pos)?;
                let body = self.isolated(bound, Some(cursor.clone()), Some(err.clone()), body)?;
                if !returns(&body) {
                    return Err(Diagnostic::new(*pos, "E_RETURN",
                        "a recovery handler must return a value or call the cursor's next() on every path"));
                }
                TStmt::Recover { flag, args: sets, body, pos: *pos }
            }
            Stmt::Expr(e) => {
                if let ExprKind::Ownership(OwnershipOp::Drop, _, inner) = &e.kind {
                    // drop! is a consuming, standalone statement. No stored
                    // owner/borrow may remain usable afterward. The browser
                    // backend does not yet implement deterministic heap object
                    // destructors, so only resource-free primitives are legal.
                    let ExprKind::Var(name) = &inner.kind else {
                        return Err(Diagnostic::new(e.pos, "E_DROP_CONTEXT",
                            "drop! requires a named owned local, not a computed value"));
                    };
                    let (slot, ty) = match self.lookup(name) {
                        Some(l) => (l.slot, l.ty),
                        None => return Err(Diagnostic::new(inner.pos, "E_UNBOUND",
                            format!("unknown name '{name}'"))),
                    };
                    if self.moved.contains(&slot) {
                        return Err(Diagnostic::new(e.pos, "E_MOVED",
                            "cannot drop an already moved or dropped owner"));
                    }
                    if self.loans.contains_key(&slot)
                        || self.loans.values().any(|loan| loan.owner == slot) {
                        return Err(Diagnostic::new(e.pos, "E_BORROW",
                            "cannot drop an owner while an active loan exists"));
                    }
                    if self.loop_floors.last().is_some_and(|floor| slot < *floor) {
                        return Err(Diagnostic::new(e.pos, "E_MOVED",
                            "cannot drop a local declared outside a repeated loop"));
                    }
                    if !matches!(ty, Type::Int | Type::Bool | Type::Float | Type::Str) {
                        return Err(Diagnostic::new(e.pos, "E_DROP_UNSUPPORTED",
                            "dropping resource-owning values requires verified destructor and reclamation lowering"));
                    }
                    let last_value = self.value(inner)?;
                    self.moved.insert(slot);
                    // Evaluate the final primitive read once (no destructor).
                    return Ok(TStmt::Expr(last_value));
                }
                let v = self.expr(e)?;
                if v.ty == Type::GeneratorInt {
                    return Err(Diagnostic::new(e.pos, "E_GENERATOR_OWNERSHIP",
                        "discarding an unclosed generator handle is prohibited"));
                }
                TStmt::Expr(v)
            }
            Stmt::Throw(error, pos) => self.guest_throw(error, *pos)?,
            Stmt::Yield(_, pos) | Stmt::YieldFrom(_, pos) => {
                return Err(Diagnostic::new(*pos, "E_YIELD",
                    "yield and yield* require a compiled generator continuation"));
            }
            Stmt::ForIn { name, source, body, pos } => {
                let gen = self.consume(source)?;
                if gen.ty != Type::GeneratorInt {
                    return Err(type_err(source.pos,
                        format!("for-in expects Generator<int>, found {}", self.tn(gen.ty))));
                }
                if !generator_forin_safe_body(body) {
                    return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                        "generator for-in body has effects requiring exception/cancellation-safe unwinding"));
                }
                // This first slice owns a fresh handle produced by a direct
                // generator call. No aliasing or escaping local handles.
                if !matches!(gen.e, TExpr::Call(_, _)) {
                    return Err(Diagnostic::new(source.pos, "E_GENERATOR_OWNERSHIP",
                        "for-in currently requires a fresh generator call"));
                }
                let handle_slot = self.temp(Type::GeneratorInt, *pos)?;
                self.scopes.push(Vec::new());
                let checked = (|| {
                    let value_slot = self.declare(name, Type::Int, false, *pos)?;
                    let body = self.looped(body)?;
                    Ok(TStmt::ForIn { source: gen, handle_slot, value_slot, body })
                })();
                self.pop_scope();
                checked?
            }
            Stmt::Return(_, pos) if self.cleanup_depth > 0 && self.recover_cursor.is_none() => {
                return Err(Diagnostic::new(*pos, "E_UNSUPPORTED",
                    "a defer body cannot return: cleanup must not replace the pending outcome"));
            }
            Stmt::Return(v, pos) => match (v, self.ret) {
                (None, Type::Void) => TStmt::Return(None),
                (None, t) => {
                    return Err(Diagnostic::new(
                        *pos,
                        "E_RETURN",
                        format!("return needs a value of type {}", self.tn(t)),
                    ))
                }
                (Some(e), Type::Void) => return Err(type_err(e.pos, "a void fnc cannot return a value")),
                (Some(e), t) => {
                    let v = self.consume_expected(e, t)?;
                    if v.ty != t {
                        return Err(type_err(
                            e.pos,
                            format!("return value has type {} but expected {}", self.tn(v.ty), self.tn(t)),
                        ));
                    }
                    TStmt::Return(Some(v))
                }
            },
            Stmt::If { arms, otherwise, .. } => {
                // Ownership after the if is the union over arms that can
                // fall through; arms that always return do not contribute.
                let mut out = Vec::new();
                let mut after: BTreeSet<u32> = BTreeSet::new();
                for (c, b) in arms {
                    let c = self.cond(c, "if")?;
                    let at_cond = self.moved.clone();
                    let body = self.scoped(b)?;
                    if !returns(&body) {
                        after.extend(self.moved.iter().copied());
                    }
                    self.moved = at_cond;
                    out.push((c, body));
                }
                let other = match otherwise {
                    Some(b) => {
                        let body = self.scoped(b)?;
                        if !returns(&body) {
                            after.extend(self.moved.iter().copied());
                        }
                        Some(body)
                    }
                    None => {
                        after.extend(self.moved.iter().copied());
                        None
                    }
                };
                self.moved = after;
                TStmt::If(out, other)
            }
            Stmt::While { cond, body, .. } => {
                let c = self.repeated_cond(cond, "while")?;
                let body = self.looped(body)?;
                TStmt::Loop {
                    cond: Some(c),
                    body,
                    update: Vec::new(),
                }
            }
            Stmt::Loop { body, .. } => {
                let body = self.looped(body)?;
                TStmt::Loop {
                    cond: None,
                    body,
                    update: Vec::new(),
                }
            }
            Stmt::For {
                init, cond, update, body, ..
            } => {
                self.scopes.push(Vec::new());
                let r = (|| {
                    let mut out = Vec::new();
                    if let Some(i) = init {
                        out.push(self.stmt(i)?);
                    }
                    // The initializer executes once. By contrast the
                    // condition and update are re-evaluated every iteration,
                    // including after continue; they must not transfer
                    // locals allocated before the loop's repeated region.
                    let repeated_floor = self.nparams + self.locals.len() as u32;
                    let c = match cond {
                        Some(c) => Some(self.repeated_cond(c, "for")?),
                        None => None,
                    };
                    let b = self.looped(body)?;
                    self.loop_floors.push(repeated_floor);
                    let update_result = match update {
                        Some(u) => self.stmt(u).map(|u| vec![u]),
                        None => Ok(Vec::new()),
                    };
                    self.loop_floors.pop();
                    let u = update_result?;
                    out.push(TStmt::Loop {
                        cond: c,
                        body: b,
                        update: u,
                    });
                    Ok(TStmt::Block(out))
                })();
                self.pop_scope();
                r?
            }
            Stmt::Break(pos) | Stmt::Continue(pos) => {
                if self.loops == 0 {
                    let w = if matches!(s, Stmt::Break(_)) { "break" } else { "continue" };
                    return Err(Diagnostic::new(
                        *pos,
                        "E_LOOP",
                        format!("'{w}' may only appear inside loop, while or for"),
                    ));
                }
                if matches!(s, Stmt::Break(_)) {
                    TStmt::Break
                } else {
                    TStmt::Continue
                }
            }
            Stmt::Block(b) => TStmt::Block(self.scoped(b)?),
            Stmt::Match { subject, arms, pos } => self.match_stmt(subject, arms, *pos)?,
        })
    }

    /// `match`: the subject is evaluated once into a temp; arms are tried in
    /// source order; a guard runs only after its pattern matched. The checker
    /// rejects unreachable arms and requires exhaustiveness (Java reference:
    /// "unreachable match arm", "non-exhaustive match").
    fn match_stmt(&mut self, subject: &Expr, arms: &[MatchArm], pos: Pos) -> R<TStmt> {
        let subj = self.value(subject)?;
        let sty = subj.ty;
        if matches!(sty, Type::OptionInt | Type::ResultIntStr | Type::OptionResultIntStr) {
            return self.match_adt(subj, arms, pos);
        }
        if !matches!(sty, Type::Int | Type::Bool | Type::Enum(_) | Type::Float | Type::Str) {
            return Err(Diagnostic::new(
                subject.pos,
                "E_UNSUPPORTED",
                format!("matching a {} value is not supported by the browser compiler yet", self.tn(sty)),
            ));
        }
        let tmp = self.temp(sty, pos)?;
        let get = || TE {
            e: TExpr::Local(tmp),
            ty: sty,
        };
        let variants = match sty {
            Type::Enum(e) => self.g.enums[e as usize].variants.len(),
            Type::Bool => 2,
            _ => usize::MAX,
        };
        let mut seen: BTreeSet<i64> = BTreeSet::new();
        let mut covered = false;
        let mut out = Vec::new();
        // Pattern bindings used by guards must be initialized before the
        // guard condition executes. Pure scalar handles are copied from the
        // once-evaluated subject, and remain lexically scoped to their arms.
        // These initializations must precede TStmt::If, whose conditions
        // run before any branch body. Do not use this for ADT payloads:
        // their reads require a proven matching variant tag.
        let mut match_setup = vec![TStmt::Set(tmp, subj)];
        let mut after: BTreeSet<u32> = BTreeSet::new();
        for (i, arm) in arms.iter().enumerate() {
            if covered {
                return Err(Diagnostic::new(
                    arm.pos,
                    "E_MATCH",
                    format!("unreachable match arm {}: earlier arms already match every value", i + 1),
                ));
            }
            // (pattern test, literal key for reachability, binding name)
            let (test, key, bind): (Option<TE>, Option<i64>, Option<&str>) = match &arm.pattern {
                Pattern::Wild => (None, None, None),
                Pattern::Bind(n) => (None, None, Some(n.as_str())),
                Pattern::Int(v) => {
                    if sty != Type::Int {
                        return Err(type_err(arm.pos, format!("int pattern cannot match a {} value", self.tn(sty))));
                    }
                    let lit = TE {
                        e: TExpr::I64(*v),
                        ty: Type::Int,
                    };
                    (
                        Some(TE {
                            e: TExpr::Bin(BinOp::Eq, Box::new(get()), Box::new(lit)),
                            ty: Type::Bool,
                        }),
                        Some(*v),
                        None,
                    )
                }
                Pattern::Bool(b) => {
                    if sty != Type::Bool {
                        return Err(type_err(arm.pos, format!("bool pattern cannot match a {} value", self.tn(sty))));
                    }
                    let lit = TE {
                        e: TExpr::Bool(*b),
                        ty: Type::Bool,
                    };
                    (
                        Some(TE {
                            e: TExpr::Bin(BinOp::Eq, Box::new(get()), Box::new(lit)),
                            ty: Type::Bool,
                        }),
                        Some(*b as i64),
                        None,
                    )
                }
                Pattern::Adt(name, _) => return Err(type_err(arm.pos,
                    format!("ADT pattern '{name}' cannot match a {}", self.tn(sty)))),
                Pattern::Variant(en, var) => {
                    let ev = self.enum_value(en, var, arm.pos, arm.pos)?;
                    if ev.ty != sty {
                        return Err(type_err(
                            arm.pos,
                            format!(
                                "pattern {en}.{var} has type {} but the subject has type {}",
                                self.tn(ev.ty),
                                self.tn(sty)
                            ),
                        ));
                    }
                    let ord = match ev.e {
                        TExpr::EnumVal(o) => o as i64,
                        _ => unreachable!("enum_value yields an ordinal"),
                    };
                    (
                        Some(TE {
                            e: TExpr::Bin(BinOp::Eq, Box::new(get()), Box::new(ev)),
                            ty: Type::Bool,
                        }),
                        Some(ord),
                        None,
                    )
                }
            };
            if let Some(k) = key {
                if seen.contains(&k) {
                    return Err(Diagnostic::new(
                        arm.pos,
                        "E_MATCH",
                        format!(
                            "unreachable match arm {}: an earlier arm already matches every value accepted by it",
                            i + 1
                        ),
                    ));
                }
            }
            self.scopes.push(Vec::new());
            let r = (|| -> R<(TE, Vec<TStmt>)> {
                let mut body = Vec::new();
                if let Some(n) = bind {
                    let slot = self.declare(n, sty, false, arm.pos)?;
                    let assignment = TStmt::Set(slot, get());
                    if arm.guard.is_some() {
                        // A guard reads its arm-local binding in the If
                        // condition, before any arm body is reached.
                        match_setup.push(assignment);
                    } else {
                        body.push(assignment);
                    }
                }
                let guard = match &arm.guard {
                    Some(g) => Some(self.cond(g, "match guard")?),
                    None => None,
                };
                let at_arm = self.moved.clone();
                body.extend(self.stmts(&arm.body)?);
                if !returns(&body) {
                    after.extend(self.moved.iter().copied());
                }
                self.moved = at_arm;
                let truth = TE {
                    e: TExpr::Bool(true),
                    ty: Type::Bool,
                };
                let cond = match (test, guard) {
                    (None, None) => truth,
                    (Some(t), None) => t,
                    (None, Some(g)) => g,
                    // the guard must not run when the pattern fails
                    (Some(t), Some(g)) => TE {
                        e: TExpr::Ternary(
                            Box::new(t),
                            Box::new(g),
                            Box::new(TE {
                                e: TExpr::Bool(false),
                                ty: Type::Bool,
                            }),
                        ),
                        ty: Type::Bool,
                    },
                };
                Ok((cond, body))
            })();
            self.pop_scope();
            let (cond, body) = r?;
            if arm.guard.is_none() {
                match key {
                    Some(k) => {
                        seen.insert(k);
                        if seen.len() == variants {
                            covered = true;
                        }
                    }
                    None => covered = true,
                }
            }
            out.push((cond, body));
        }
        if !covered {
            return Err(Diagnostic::new(
                pos,
                "E_MATCH",
                format!(
                    "non-exhaustive match for {}; add an unguarded 'on _ -> {{ ... }}' arm or cover every provable case",
                    self.tn(sty)
                ),
            ));
        }
        self.moved = after;
        match_setup.push(TStmt::If(out, Some(vec![TStmt::Unreachable])));
        Ok(TStmt::Block(match_setup))
    }


    /// Check a concrete tagged ADT match. Only v1 profiles are admitted:
    /// Option<int> and Result<int,string>. Each variant has a unique tag;
    /// the payload read occurs only inside its matching guarded arm.
    fn match_adt(&mut self, subj: TE, arms: &[MatchArm], pos: Pos) -> R<TStmt> {
        let sty = subj.ty;
        let tmp = self.temp(sty, pos)?;
        let get = || TE { e: TExpr::Local(tmp), ty: sty };
        let mut seen: BTreeSet<i64> = BTreeSet::new();
        let mut covered = false;
        let mut out = Vec::new();
        // Guards run in the If condition, before their arm body. Stage each
        // guarded binding beforehand, but read tagged payloads ONLY after
        // confirming the corresponding variant discriminant.
        let mut match_setup = vec![TStmt::Set(tmp, subj)];
        let mut after: BTreeSet<u32> = BTreeSet::new();
        for (i, arm) in arms.iter().enumerate() {
            if covered {
                return Err(Diagnostic::new(arm.pos, "E_MATCH",
                    format!("unreachable match arm {}: prior arms cover every variant", i + 1)));
            }
            let (key, payload_name, payload_ty) = match &arm.pattern {
                Pattern::Wild => (None, None, None),
                Pattern::Bind(n) => (None, Some(n.as_str()), Some(sty)),
                Pattern::Adt(name, bind) => {
                    let (tag, needed) = match (sty, name.as_str()) {
                        (Type::ResultIntStr, "Ok") => (0, Some(Type::Int)),
                        (Type::ResultIntStr, "Err") => (1, Some(Type::Str)),
                        (Type::OptionInt, "None") => (0, None),
                        (Type::OptionInt, "Some") => (1, Some(Type::Int)),
                        (Type::OptionResultIntStr, "None") => (0, None),
                        (Type::OptionResultIntStr, "Some") => (1, Some(Type::ResultIntStr)),
                        _ => return Err(type_err(arm.pos,
                            format!("variant '{name}' is not part of {}", self.tn(sty)))),
                    };
                    if bind.is_some() != needed.is_some() {
                        return Err(Diagnostic::new(arm.pos, "E_ARITY",
                            format!("pattern '{name}' has incorrect payload arity")));
                    }
                    (Some(tag), bind.as_deref(), needed)
                }
                _ => return Err(type_err(arm.pos,
                    format!("pattern is not a variant of {}", self.tn(sty)))),
            };
            if key.is_some_and(|tag| seen.contains(&tag)) {
                return Err(Diagnostic::new(arm.pos, "E_MATCH",
                    format!("unreachable match arm {}: variant already covered", i + 1)));
            }
            let test = key.map(|tag| TE {
                e: TExpr::AdtIs { obj: Box::new(get()), tag: tag as u32 },
                ty: Type::Bool,
            });
            self.scopes.push(Vec::new());
            let r = (|| -> R<(TE, Vec<TStmt>)> {
                let mut body = Vec::new();
                if let Some(name) = payload_name {
                    let ty = payload_ty.expect("the pattern binds a value");
                    let slot = self.declare(name, ty, false, arm.pos)?;
                    let value = if key.is_none() {
                        get()
                    } else {
                        TE { e: TExpr::AdtPayload(Box::new(get())), ty }
                    };
                    let assignment = TStmt::Set(slot, value);
                    if arm.guard.is_some() {
                        if let Some(tag_test) = test.as_ref() {
                            // Reading Some/Ok/Err payload before checking its
                            // tag would be unsound (and can read uninitialized
                            // storage for the opposite variant).
                            match_setup.push(TStmt::If(
                                vec![(tag_test.clone(), vec![assignment])], None,
                            ));
                        } else {
                            // A whole-value binding is always safe to copy.
                            match_setup.push(assignment);
                        }
                    } else {
                        body.push(assignment);
                    }
                }
                let guard = match &arm.guard {
                    Some(g) => Some(self.cond(g, "match guard")?),
                    None => None,
                };
                let at_arm = self.moved.clone();
                body.extend(self.stmts(&arm.body)?);
                if !returns(&body) {
                    after.extend(self.moved.iter().copied());
                }
                self.moved = at_arm;
                let truth = TE { e: TExpr::Bool(true), ty: Type::Bool };
                let cond = match (test, guard) {
                    (None, None) => truth,
                    (Some(t), None) => t,
                    (None, Some(g)) => g,
                    (Some(t), Some(g)) => TE {
                        e: TExpr::Ternary(
                            Box::new(t), Box::new(g),
                            Box::new(TE { e: TExpr::Bool(false), ty: Type::Bool }),
                        ),
                        ty: Type::Bool,
                    },
                };
                Ok((cond, body))
            })();
            self.pop_scope();
            let (cond, body) = r?;
            if arm.guard.is_none() {
                match key {
                    Some(k) => {
                        seen.insert(k);
                        if seen.len() == 2 { covered = true; }
                    }
                    None => covered = true,
                }
            }
            out.push((cond, body));
        }
        if !covered {
            return Err(Diagnostic::new(pos, "E_MATCH",
                format!("non-exhaustive match for {}; cover both variants or use on _", self.tn(sty))));
        }
        self.moved = after;
        match_setup.push(TStmt::If(out, Some(vec![TStmt::Unreachable])));
        Ok(TStmt::Block(match_setup))
    }

    fn field_assign(&mut self, target: &Expr, field: &str, value: &Expr, pos: Pos) -> R<TStmt> {
        if let ExprKind::Var(name) = &target.kind {
            if let Some(local) = self.lookup(name) {
                if let Some(loan) = self.loans.get(&local.slot).copied() {
                    if !loan.mutable {
                        return Err(Diagnostic::new(pos, "E_BORROW", "shared borrow cannot mutate a field"));
                    }
                    let Type::Class(c) = local.ty else { unreachable!("tracked loans must be class typed") };
                    let class = &self.g.classes[c as usize];
                    if class.name.starts_with("__atto_tuple_private_") {
                        return Err(Diagnostic::new(pos, "E_IMMUTABLE",
                            "tuple root elements cannot be mutated through a class loan"));
                    }
                    let f = class.fields.iter().find(|f| f.name == field).ok_or_else(||
                        Diagnostic::new(pos, "E_UNBOUND", format!("class '{}' has no field '{field}'", class.name)))?;
                    if f.visibility == FieldVisibility::Private && self.inside_class() != Some(c) {
                        return Err(Diagnostic::new(pos, "E_PRIVATE", "cannot mutate private field outside its class"));
                    }
                    // A borrowed ordinary class handle is not a checked
                    // state-container lease: never lower protected state as
                    // an unrestricted FieldSet from this alternate path.
                    if f.mode == FieldMode::ActorState {
                        return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                            "protected state requires the checked critical-write lease"));
                    }
                    if !f.binding.rebindable() {
                        return Err(Diagnostic::new(pos, "E_IMMUTABLE",
                            "cannot reassign val/final/const field through borrow! mut"));
                    }
                    let (slot, offset, fty) = (local.slot, f.slot, f.ty);
                    // A class-valued field write would install an untracked owned
                    // handle through an alias. Lower only copyable field storage.
                    if !matches!(fty, Type::Int | Type::Bool | Type::Float | Type::Str | Type::Enum(_)) {
                        return Err(Diagnostic::new(pos, "E_BORROW",
                            "borrow! mut does not yet admit fields requiring owned-handle transfer"));
                    }
                    let checked = self.consume_expected(value, fty)?;
                    if checked.ty != fty { return Err(type_err(value.pos, "borrowed field assignment type mismatch")); }
                    return Ok(TStmt::FieldSet { obj: TE { e: TExpr::Local(slot), ty: Type::Class(c) },
                        offset, ty: fty, value: checked });
                }
            }
        }
        if !matches!(target.kind, ExprKind::SelfRef) {
            return Err(Diagnostic::new(
                pos,
                "E_OWNERSHIP",
                "fields are assigned only through 'self' in a constructor or an actor method",
            ));
        }
        match self.owner {
            Owner::Class { c, ctor, is_static } => {
                if is_static {
                    return Err(Diagnostic::new(target.pos, "E_UNBOUND", "unknown name 'self'"));
                }
                let class = &self.g.classes[c as usize];
                let f = match class.fields.iter().find(|f| f.name == field) {
                    Some(f) => f,
                    None => {
                        return Err(Diagnostic::new(
                            pos,
                            "E_UNBOUND",
                            format!("class '{}' has no field '{field}'", class.name),
                        ))
                    }
                };
                let (offset, fty, mode) = (f.slot, f.ty, f.mode);
                if !f.binding.rebindable() {
                    return Err(Diagnostic::new(
                        pos,
                        "E_IMMUTABLE",
                        format!(
                            "field '{}.{field}' is immutable/final; cannot reassign fixed class field",
                            class.name
                        ),
                    ));
                }
                // Never grant mutable state authority from a field mode alone.
                // The declaration must be a protected state container AND the
                // typed checker must be inside the lexical critical-write AST.
                if mode == FieldMode::ActorState {
                    if !class.state_container || !self.state_write_scope {
                        return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                            "mutable state requires a checked critical-write scope"));
                    }
                } else if !ctor {
                    return Err(Diagnostic::new(pos, "E_OWNERSHIP",
                        format!("cannot mutate field '{field}' through read-only binding 'self'")));
                }
                let v = self.value(value)?;
                if v.ty != fty {
                    return Err(type_err(
                        value.pos,
                        format!("cannot assign {} to field '{field}' of type {}", self.tn(v.ty), self.tn(fty)),
                    ));
                }
                let obj = TE {
                    e: TExpr::Local(0),
                    ty: Type::Class(c),
                };
                if mode == FieldMode::ActorState && class.state_container {
                    Ok(TStmt::StateFieldWrite { obj, offset, ty: fty, value: v })
                } else {
                    Ok(TStmt::FieldSet { obj, offset, ty: fty, value: v })
                }
            }
            Owner::Actor { a } => {
                let actor = &self.g.actors[a as usize];
                let f = match actor.fields.iter().find(|f| f.name == field) {
                    Some(f) => f,
                    None => {
                        return Err(Diagnostic::new(
                            pos,
                            "E_UNBOUND",
                            format!("actor '{}' has no field '{field}'", actor.name),
                        ))
                    }
                };
                let (global, fty, mode) = (f.slot, f.ty, f.mode);
                if mode != FieldMode::ActorState {
                    return Err(Diagnostic::new(
                        pos,
                        "E_IMMUTABLE",
                        format!(
                            "field '{}.{field}' is immutable/final; cannot reassign fixed class field",
                            actor.name
                        ),
                    ));
                }
                let v = self.value(value)?;
                if v.ty != fty {
                    return Err(type_err(
                        value.pos,
                        format!("cannot assign {} to field '{field}' of type {}", self.tn(v.ty), self.tn(fty)),
                    ));
                }
                Ok(TStmt::GlobalSet(global, v))
            }
            _ => Err(Diagnostic::new(target.pos, "E_UNBOUND", "unknown name 'self'")),
        }
    }

    /// Construct an ADT only where the full expected type is unambiguous.
    /// Neither Null nor a bare payload implicitly converts to an ADT.
    fn consume_expected(&mut self, e: &Expr, want: Type) -> R<TE> {
        let (variant, argument): (&str, Option<&Expr>) = match &e.kind {
            ExprKind::Call(name, args) if matches!(name.as_str(), "Ok" | "Err" | "Some") => {
                if args.len() != 1 {
                    return Err(Diagnostic::new(e.pos, "E_ARITY",
                        format!("{name} requires one payload argument, got {}", args.len())));
                }
                (name.as_str(), Some(&args[0]))
            }
            ExprKind::Var(name) if name == "None" => ("None", None),
            _ => return self.consume(e),
        };
        let (tag, payload_type) = match (want, variant) {
            (Type::ResultIntStr, "Ok") => (0, Some(Type::Int)),
            (Type::ResultIntStr, "Err") => (1, Some(Type::Str)),
            (Type::OptionInt, "None") => (0, None),
            (Type::OptionInt, "Some") => (1, Some(Type::Int)),
            (Type::OptionResultIntStr, "None") => (0, None),
            (Type::OptionResultIntStr, "Some") => (1, Some(Type::ResultIntStr)),
            _ => return Err(type_err(e.pos,
                format!("variant '{variant}' is not valid for {}", self.tn(want)))),
        };
        let payload = match (argument, payload_type) {
            (Some(arg), Some(ty)) => {
                // A nested Some(Ok(...)) or Some(Err(...)) carries the
                // expected inner Result type; constructors are contextual.
                let value = self.consume_expected(arg, ty)?;
                if value.ty != ty {
                    return Err(type_err(arg.pos,
                        format!("'{variant}' payload must be {}, found {}", self.tn(ty), self.tn(value.ty))));
                }
                Some(Box::new(value))
            }
            (None, None) => None,
            _ => unreachable!("variant arity checked above"),
        };
        let tmp = self.temp(want, e.pos)?;
        Ok(TE { e: TExpr::AdtNew { tag, payload, tmp }, ty: want })
    }

    /// An expression used as a value (not void).
    fn value(&mut self, e: &Expr) -> R<TE> {
        let v = self.expr(e)?;
        if v.ty == Type::Void {
            return Err(type_err(e.pos, "a void call has no value"));
        }
        Ok(v)
    }

    /// Class loans are bound to lexical locals; no owner transfer or escape.
    fn borrow_binding(&mut self, kind: BindKind, name: &str, annotation: Option<Type>,
                      inner: &Expr, mutable: bool, pos: Pos) -> R<TStmt> {
        let ExprKind::Var(owner_name) = &inner.kind else {
            return Err(Diagnostic::new(inner.pos, "E_BORROW", "borrow! requires a named owner"));
        };
        let (owner, owner_ty) = match self.lookup(owner_name) {
            Some(l) => (l.slot, l.ty),
            None => return Err(Diagnostic::new(inner.pos, "E_UNBOUND", format!("unknown name '{owner_name}'"))),
        };
        if self.loans.contains_key(&owner) {
            return Err(Diagnostic::new(pos, "E_BORROW", "reborrowing a borrowed handle requires a verified lifetime contract"));
        }
        if let Some(loan) = self.loans.values().find(|loan| loan.owner == owner) {
            if mutable || loan.mutable {
                return Err(Diagnostic::new(pos, "E_BORROW", "conflicting loans: mutable borrowing must be exclusive"));
            }
        }
        let value = self.value(inner)?;
        if let Some(annotation) = annotation {
            let expected = self.resolve(annotation, pos)?;
            if expected != value.ty {
                return Err(type_err(pos, format!("borrowed binding '{name}' expects {}, found {}", self.tn(expected), self.tn(value.ty))));
            }
        }
        // Tuple roots are value-aggregate anchors. Their non-Copy storage
        // is a private implementation detail, not a writable user class.
        // Mutable loans could bypass as-val/as-const guarantees and mutate
        // projected fields behind independently copied element binders.
        if mutable {
            if let Type::Class(c) = owner_ty {
                if self.g.classes[c as usize].name.starts_with("__atto_tuple_private_") {
                    return Err(Diagnostic::new(pos, "E_BORROW",
                        "mutable borrowing of a tuple root is not supported; use explicit element binding modes"));
                }
            }
        }
        if !matches!(owner_ty, Type::Class(_)) {
            if mutable {
                return Err(Diagnostic::new(pos, "E_BORROW", "mutable scalar loans require reference storage lowering; not yet supported"));
            }
            if !matches!(owner_ty, Type::Int | Type::Bool | Type::Float | Type::Str | Type::Enum(_)) {
                return Err(Diagnostic::new(pos, "E_BORROW", "borrowing this type is not supported by the guest Wasm backend"));
            }
            let slot = self.declare(name, value.ty, kind == BindKind::Let, pos)?;
            return Ok(TStmt::Set(slot, value));
        }
        let slot = self.declare(name, value.ty, false, pos)?;
        self.loans.insert(slot, ScopedLoan { owner, mutable });
        Ok(TStmt::Set(slot, value))
    }

    fn explicit_ownership(&mut self, action: OwnershipOp, mutable: bool, inner: &Expr, pos: Pos) -> R<TE> {
        if mutable && action != OwnershipOp::Borrow {
            return Err(Diagnostic::new(pos, "E_SYNTAX", "mut is only valid after borrow!"));
        }
        match action {
            OwnershipOp::Borrow => {
                if mutable {
                    return Err(Diagnostic::new(pos, "E_BORROW", "borrow! mut must initialize a scoped class loan"));
                }
                let value = self.value(inner)?;
                if !matches!(value.ty, Type::Int | Type::Bool | Type::Float | Type::Str | Type::Enum(_)) {
                    return Err(Diagnostic::new(pos, "E_BORROW", "borrow! on objects must initialize a lexical binding"));
                }
                Ok(value)
            }
            OwnershipOp::Copy | OwnershipOp::DeepCopy | OwnershipOp::Share => {
                // Identity-free admitted scalars have no mutable descendants:
                // shallow and deep copies are the same guest value operation.
                // Copy!! can also use a *compiler-emitted* AOT copier for an
                // ordinary flat class whose full stored field layout was
                // independently checked before this expression was lowered.
                let value = self.value(inner)?;
                if action == OwnershipOp::DeepCopy {
                    if let Type::Class(ci) = value.ty {
                        if let ExprKind::Var(name) = &inner.kind {
                            if let Some(owner_slot) = self.lookup(name).map(|l| l.slot) {
                                if self.loans.contains_key(&owner_slot)
                                    || self.loans.values().any(|l| l.owner == owner_slot && l.mutable)
                                {
                                    return Err(Diagnostic::new(pos, "E_BORROW",
                                        "copy!! cannot read a mutable/exclusive borrowed class owner"));
                                }
                            }
                        }
                        let class = &self.g.classes[ci as usize];
                        if class.methods.iter().any(|m| m.name == "copy_deep") {
                            return Err(Diagnostic::new(pos, "E_COPY_OVERRIDE",
                                "custom copy_deep overrides need verified complete-plan/hook support"));
                        }
                        let Some(copy_idx) = class.deep_copy_idx else {
                            return Err(Diagnostic::new(pos, "E_COPY_DEEP_UNSUPPORTED",
                                "copy!! class graph contains unproved mutable/reference slots or protected actor state"));
                        };
                        authenticate_flat_copy_aot(&self.g.classes, ci, pos)?;
                        return Ok(TE { e: TExpr::Call(copy_idx, vec![value]), ty: Type::Class(ci) });
                    }
                }
                if !matches!(value.ty, Type::Int | Type::Bool | Type::Float | Type::Str | Type::Enum(_)) {
                    if action == OwnershipOp::DeepCopy {
                        return Err(Diagnostic::new(pos, "E_COPY_DEEP_UNSUPPORTED",
                            "copy!! requires a verified concrete graph copier; class, actor, collection and resource handles are not yet admitted by the Rust/Wasm backend"));
                    }
                    let name = if action == OwnershipOp::Copy { "copy!" } else { "share!" };
                    return Err(Diagnostic::new(pos, if action == OwnershipOp::Copy { "E_COPY" } else { "E_SHARE" },
                        format!("{name} requires a verified immutable copyable scalar; class, actor and generator handles are not shareable")));
                }
                Ok(value)
            }
            OwnershipOp::Drop => Err(Diagnostic::new(pos, "E_DROP_CONTEXT",
                "drop! must be a standalone statement with a named owned local")),
            OwnershipOp::Freeze => {
                // Immutable primitive values have no mutable reachable object graph:
                // freeze! is observationally the identity for this *proven*
                // subset. Never extend this rule to class/actor/generator handles
                // without a transitive freeze witness and alias invalidation.
                let value = self.value(inner)?;
                if !matches!(value.ty, Type::Int | Type::Bool | Type::Float | Type::Str) {
                    return Err(Diagnostic::new(pos, "E_FREEZE_PROOF",
                        "freeze! requires verified deep immutability; this Wasm subset only admits immutable scalars"));
                }
                Ok(value)
            }
            OwnershipOp::Weak => {
                // A weak handle requires generation-fenced allocation identity,
                // a nullable upgrade result, and ownership-neutral cleanup.
                // Returning the source value would silently create a strong alias.
                Err(Diagnostic::new(pos, "E_WEAK_UNSUPPORTED",
                    "weak! requires a generation-checked weak handle and Option<Shared<T>> upgrade; not lowered by this Wasm backend"))
            }
            OwnershipOp::Pin => {
                // Pinning is stable *pointee storage*, not an OS-thread affinity
                // hint. Ordinary guest locals/handles cannot promise it yet.
                Err(Diagnostic::new(pos, "E_PIN_UNSUPPORTED",
                    "pin! requires stable-address storage and verified cleanup; not lowered by this Wasm backend"))
            }
            OwnershipOp::Take => {
                let ExprKind::Var(name) = &inner.kind else {
                    return Err(Diagnostic::new(pos, "E_OWNERSHIP", "take! requires a named owned local"));
                };
                let value = self.value(inner)?;
                let TExpr::Local(slot_ref) = &value.e else {
                    return Err(Diagnostic::new(pos, "E_OWNERSHIP", "take! requires a local, not a computed value"));
                };
                let slot = *slot_ref;
                if self.loans.contains_key(&slot) || self.loans.values().any(|loan| loan.owner == slot) {
                    return Err(Diagnostic::new(pos, "E_BORROW", "take! is forbidden while an owner is borrowed"));
                }
                if self.loop_floors.last().is_some_and(|floor| slot < *floor) {
                    return Err(Diagnostic::new(pos, "E_MOVED", format!("cannot take '{name}' from outside a loop")));
                }
                self.moved.insert(slot);
                Ok(value)
            }
        }
    }

    /// A value in an ownership-transferring position (binding initializer,
    /// assignment, argument, return): naming an object local moves it.
    fn consume(&mut self, e: &Expr) -> R<TE> {
        let v = self.value(e)?;
        if let (ExprKind::Var(name), TExpr::Local(slot), Type::Class(_)) = (&e.kind, &v.e, v.ty) {
            let slot = *slot;
            if self.loans.contains_key(&slot) || self.loans.values().any(|loan| loan.owner == slot) {
                return Err(Diagnostic::new(e.pos, "E_BORROW", "cannot transfer a borrowed class or owner while a loan is live"));
            }
            if self.loop_floors.last().is_some_and(|floor| slot < *floor) {
                return Err(Diagnostic::new(
                    e.pos,
                    "E_MOVED",
                    format!("cannot move '{name}' inside a loop: it is declared outside the loop"),
                ));
            }
            self.moved.insert(slot);
        }
        Ok(v)
    }

    // These non-inlined helpers keep the per-level stack frame of the
    // recursively invoked expression checker bounded on the browser runner.
    #[inline(never)]
    fn trap_value(&mut self, inner: &Expr, pos: Pos) -> R<TE> {
        if self.owner != Owner::TopLevel {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                "caller-side trap inside class/actor requires lifecycle integration"));
        }
        let value = self.consume(inner)?;
        let option_ty = match value.ty {
            Type::Int => Type::OptionInt,
            Type::ResultIntStr => Type::OptionResultIntStr,
            _ => return Err(Diagnostic::new(pos, "E_UNSUPPORTED_TYPE",
                format!("browser trap supports only int and Result<int,string> operands, found {}", self.tn(value.ty)))),
        };
        let value_tmp = self.temp(value.ty, pos)?;
        let some_tmp = self.temp(option_ty, pos)?;
        let none_tmp = self.temp(option_ty, pos)?;
        Ok(TE {
            e: TExpr::Trap { value: Box::new(value), value_tmp, some_tmp, none_tmp },
            ty: option_ty,
        })
    }

    #[inline(never)]
    fn guest_throw(&mut self, error: &Expr, pos: Pos) -> R<TStmt> {
        Ok(TStmt::Throw(self.guest_error_message(error, "throw", pos)?))
    }

    fn expr(&mut self, e: &Expr) -> R<TE> {
        match &e.kind {
            ExprKind::Unary(UnOp::Neg, inner) if matches!(inner.kind, ExprKind::Int(None)) => Ok(TE {
                e: TExpr::I64(i64::MIN),
                ty: Type::Int,
            }),
            ExprKind::Unary(op, inner) => self.unary(*op, inner, e.pos),
            ExprKind::Trap(inner) => self.trap_value(inner, e.pos),
            ExprKind::Ownership(action, mutable, inner) => self.explicit_ownership(*action, *mutable, inner, e.pos),
            ExprKind::Binary(op, l, r) => self.binary(*op, l, r, e.pos),
            ExprKind::Ternary(c, a, b) => self.ternary(c, a, b, e.pos),
            ExprKind::Propagate(inner) => {
                let value = self.consume(inner)?;
                let success_tag = match value.ty {
                    Type::ResultIntStr => 0,
                    Type::OptionInt => 1,
                    _ => return Err(type_err(e.pos,
                        format!("postfix '?' requires Option<int> or Result<int,string>, found {}", self.tn(value.ty)))),
                };
                if self.ret != value.ty {
                    return Err(type_err(e.pos,
                        format!("postfix '?' can propagate {} only from a function returning the same type; found {}", self.tn(value.ty), self.tn(self.ret))));
                }
                let tmp = self.temp(value.ty, e.pos)?;
                Ok(TE { e: TExpr::AdtPropagate {
                    source: Box::new(value), tmp, success_tag
                }, ty: Type::Int })
            }
            // receivers that are not names recurse; keep that path thin
            ExprKind::Member(base, name) if !matches!(base.kind, ExprKind::Var(_) | ExprKind::SelfRef) => {
                let obj = self.value(base)?;
                self.member_on(obj, name, e.pos)
            }
            ExprKind::MethodCall(base, name, args) if !matches!(base.kind, ExprKind::Var(_) | ExprKind::SelfRef) => {
                let recv = self.value(base)?;
                self.method_on(recv, name, args, e.pos)
            }
            _ => self.expr_cold(e),
        }
    }

    #[inline(never)]
    fn unary(&mut self, op: UnOp, inner: &Expr, pos: Pos) -> R<TE> {
        let op = &op;
        Ok({
            let v = self.value(inner)?;
            match op {
                UnOp::Neg | UnOp::Plus if v.ty == Type::Float => {
                    if *op == UnOp::Plus {
                        v
                    } else {
                        TE {
                            e: TExpr::FNeg(Box::new(v)),
                            ty: Type::Float,
                        }
                    }
                }
                UnOp::Neg | UnOp::Plus => {
                    if v.ty != Type::Int {
                        return Err(type_err(
                            pos,
                            format!(
                                "unary '{}' needs an int or float operand, found {}",
                                if *op == UnOp::Neg { "-" } else { "+" },
                                self.tn(v.ty)
                            ),
                        ));
                    }
                    if *op == UnOp::Plus {
                        v
                    } else {
                        TE {
                            e: TExpr::Neg(Box::new(v)),
                            ty: Type::Int,
                        }
                    }
                }
                UnOp::Not => {
                    if v.ty != Type::Bool {
                        return Err(type_err(pos, format!("'!' needs a bool operand, found {}", self.tn(v.ty))));
                    }
                    TE {
                        e: TExpr::Not(Box::new(v)),
                        ty: Type::Bool,
                    }
                }
            }
        })
    }

    #[inline(never)]
    fn binary(&mut self, op: BinOp, l: &Expr, r: &Expr, pos: Pos) -> R<TE> {
        let op = &op;
        Ok({
            let a = self.value(l)?;
            let b = self.value(r)?;
            if (a.ty == Type::Str || b.ty == Type::Str) && !matches!(op, BinOp::Eq | BinOp::Ne) {
                let both = a.ty == Type::Str && b.ty == Type::Str;
                return match op {
                    // Java: '+' joins two strings; it never converts other operands
                    BinOp::Add if both => Ok(TE {
                        e: TExpr::Str(StrOp::Concat, Box::new(a), Some(Box::new(b))),
                        ty: Type::Str,
                    }),
                    // Java String.compareTo order
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge if both => Ok(TE {
                        e: TExpr::Bin(
                            *op,
                            Box::new(TE {
                                e: TExpr::Str(StrOp::Cmp, Box::new(a), Some(Box::new(b))),
                                ty: Type::Int,
                            }),
                            Box::new(TE {
                                e: TExpr::I64(0),
                                ty: Type::Int,
                            }),
                        ),
                        ty: Type::Bool,
                    }),
                    _ => Err(type_err(
                        pos,
                        format!(
                            "operator '{}' needs numeric operands (or two strings for '+' and comparisons), found {} and {}",
                            op.symbol(),
                            self.tn(a.ty),
                            self.tn(b.ty)
                        ),
                    )),
                };
            }
            let numeric = |t: Type| matches!(t, Type::Int | Type::Float);
            if matches!(
                op,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
            ) {
                if !numeric(a.ty) || !numeric(b.ty) {
                    return Err(type_err(
                        pos,
                        format!(
                            "operator '{}' needs int or float operands, found {} and {}",
                            op.symbol(),
                            self.tn(a.ty),
                            self.tn(b.ty)
                        ),
                    ));
                }
                if a.ty == Type::Int && b.ty == Type::Int {
                    if *op == BinOp::Div {
                        return Err(Diagnostic::new(
                            pos,
                            "E_UNSUPPORTED",
                            "'/' on two ints is not admitted: whether int / int yields float or int is undecided (spec S-25); write a float operand, e.g. 7.0 / 2",
                        ));
                    }
                } else {
                    // Java binary numeric promotion: an int operand widens to float.
                    let widen = |v: TE| -> TE {
                        if v.ty == Type::Int {
                            TE {
                                e: TExpr::IntToFloat(Box::new(v)),
                                ty: Type::Float,
                            }
                        } else {
                            v
                        }
                    };
                    let ty = if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div) {
                        Type::Float
                    } else {
                        Type::Bool
                    };
                    return Ok(TE {
                        e: TExpr::Bin(*op, Box::new(widen(a)), Box::new(widen(b))),
                        ty,
                    });
                }
            }
            let ty = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => Type::Int,
                BinOp::Div => unreachable!("int / int rejected above"),
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Type::Bool,
                BinOp::Eq | BinOp::Ne => {
                    if a.ty != b.ty {
                        return Err(type_err(
                            pos,
                            format!(
                                "'{}' operands must have the same type, found {} and {}",
                                op.symbol(),
                                self.tn(a.ty),
                                self.tn(b.ty)
                            ),
                        ));
                    }
                    if matches!(a.ty, Type::Class(_) | Type::ActorRef(_) | Type::OptionInt | Type::ResultIntStr | Type::OptionResultIntStr) {
                        return Err(Diagnostic::new(
                            pos,
                            "E_UNSUPPORTED",
                            "comparing object, actor or tagged ADT references is unsupported; pointer equality is not structural equality",
                        ));
                    }
                    if a.ty == Type::Str {
                        // strings compare by content (spec 17), never by reference
                        let eq = TE {
                            e: TExpr::Str(StrOp::Eq, Box::new(a), Some(Box::new(b))),
                            ty: Type::Bool,
                        };
                        return Ok(if *op == BinOp::Ne {
                            TE {
                                e: TExpr::Not(Box::new(eq)),
                                ty: Type::Bool,
                            }
                        } else {
                            eq
                        });
                    }
                    Type::Bool
                }
                BinOp::And | BinOp::Or => {
                    if a.ty != Type::Bool || b.ty != Type::Bool {
                        return Err(type_err(pos, format!("condition operator '{}' needs bool operands", op.symbol())));
                    }
                    Type::Bool
                }
            };
            TE {
                e: TExpr::Bin(*op, Box::new(a), Box::new(b)),
                ty,
            }
        })
    }

    #[inline(never)]
    fn ternary(&mut self, c: &Expr, a: &Expr, b: &Expr, pos: Pos) -> R<TE> {
        Ok({
            let c = self.cond(c, "ternary")?;
            let a = self.value(a)?;
            let b = self.value(b)?;
            if a.ty != b.ty {
                return Err(type_err(
                    pos,
                    format!(
                        "ternary branches must have the same type, found {} and {}",
                        self.tn(a.ty),
                        self.tn(b.ty)
                    ),
                ));
            }
            if matches!(a.ty, Type::Class(_)) {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED",
                    "a ternary choosing between objects is not supported by the browser compiler yet",
                ));
            }
            let ty = a.ty;
            TE {
                e: TExpr::Ternary(Box::new(c), Box::new(a), Box::new(b)),
                ty,
            }
        })
    }

    /// Non-recursive and rarely deep expression forms, kept out of line so
    /// the recursive path through `expr` has a small stack frame (see
    /// parser::MAX_TREE_HEIGHT and examples/stackprobe.rs).
    #[inline(never)]
    fn expr_cold(&mut self, e: &Expr) -> R<TE> {
        let pos = e.pos;
        if let Owner::FieldInit { actor } = self.owner {
            if let ExprKind::Member(base, variant) = &e.kind {
                if let ExprKind::Var(n) = &base.kind {
                    if actor {
                        return Err(Diagnostic::new(
                            pos,
                            "E_UNSUPPORTED",
                            "actor field initializers must be int or bool constants",
                        ));
                    }
                    return self.enum_value(n, variant, base.pos, pos);
                }
            }
        }
        Ok(match &e.kind {
            ExprKind::Int(Some(v)) => TE {
                e: TExpr::I64(*v as i64),
                ty: Type::Int,
            },
            ExprKind::Int(None) => {
                return Err(Diagnostic::new(
                    pos,
                    "E_INTEGER_RANGE",
                    "integer literal does not fit in a signed 64-bit int",
                ))
            }
            ExprKind::Bool(b) => TE {
                e: TExpr::Bool(*b),
                ty: Type::Bool,
            },
            ExprKind::Float(bits) => TE {
                e: TExpr::F64(f64::from_bits(*bits)),
                ty: Type::Float,
            },
            ExprKind::Str(text) => {
                let (offset, len) = self.string(text, pos)?;
                TE {
                    e: TExpr::StrConst(offset, len),
                    ty: Type::Str,
                }
            }
            ExprKind::Var(name) if name == "None" => {
                return Err(type_err(pos, "None requires a contextual Option<int> type"))
            }
            ExprKind::Var(name) => match self.lookup(name) {
                Some(l) if l.mail.is_some() => {
                    return Err(Diagnostic::new(
                        pos,
                        "E_UNSUPPORTED",
                        format!("the ActorMail envelope '{name}' as a value; read {name}.value or {name}.sequence"),
                    ))
                }
                Some(l) => {
                    if self.moved.contains(&l.slot) {
                        return Err(Diagnostic::new(pos, "E_MOVED", format!("use of moved value '{name}'")));
                    }
                    if self.loans.values().any(|loan| loan.owner == l.slot && loan.mutable) {
                        return Err(Diagnostic::new(pos, "E_BORROW", format!("owner '{name}' is exclusively mutably borrowed")));
                    }
                    TE {
                        e: TExpr::Local(l.slot),
                        ty: l.ty,
                    }
                }
                None if self.g.names.contains_key(name) => {
                    return Err(Diagnostic::new(
                        pos,
                        "E_UNSUPPORTED",
                        "functions as values are not supported by the browser compiler yet",
                    ))
                }
                None if self.g.class(name).is_some() || self.g.enum_(name).is_some() || self.g.actor(name).is_some() => {
                    return Err(Diagnostic::new(
                        pos,
                        "E_UNSUPPORTED",
                        format!("the type name '{name}' is not a value"),
                    ))
                }
                None => return Err(Diagnostic::new(pos, "E_UNBOUND", format!("unknown name '{name}'"))),
            },
            ExprKind::Unary(..) | ExprKind::Trap(..) | ExprKind::Ownership(..) | ExprKind::Binary(..) | ExprKind::Ternary(..)
            | ExprKind::Propagate(..) => unreachable!("handled by expr"),
            ExprKind::Call(name, _) if matches!(name.as_str(), "Ok" | "Err" | "Some" | "None") =>
                return Err(type_err(pos, format!("'{name}' requires a contextual Result/Option type"))),
            ExprKind::Call(name, args) => self.call(name, args, pos)?,
            ExprKind::StateRead(field) => {
                let c = match self.owner {
                    Owner::Class { c, ctor: false, is_static: false }
                        if self.g.classes[c as usize].state_container => c,
                    _ => return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                        "critical-read requires a protected instance state container")),
                };
                if self.state_read_scope || self.state_write_scope {
                    return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                        "protected state read cannot nest with another active lease"));
                }
                self.state_read_scope = true;
                let checked = self.field_get(TE {
                    e: TExpr::Local(0),
                    ty: Type::Class(c),
                }, field, pos);
                self.state_read_scope = false;
                checked?
            }
            ExprKind::SelfRef => {
                return Err(match self.owner {
                    Owner::Class { is_static: false, .. } | Owner::Actor { .. } => Diagnostic::new(
                        pos,
                        "E_UNSUPPORTED",
                        "'self' as a value is not supported by the browser compiler yet; use self.field or self.method()",
                    ),
                    _ => Diagnostic::new(pos, "E_UNBOUND", "unknown name 'self'"),
                })
            }
            ExprKind::New(class, args) => self.new_object(class, args, pos)?,
            ExprKind::Spawn(actor) => {
                if let Some(me) = self.actor_name() {
                    return Err(Diagnostic::new(
                        pos,
                        "E_UNSUPPORTED",
                        format!("spawning from inside actor '{me}' is not supported by the browser compiler yet"),
                    ));
                }
                if matches!(self.owner, Owner::FieldInit { .. }) {
                    return Err(Diagnostic::new(pos, "E_UNSUPPORTED", "spawn in a field initializer"));
                }
                let a = match self.g.actor(actor) {
                    Some(a) => a,
                    None if self.g.class(actor).is_some() => {
                        return Err(type_err(
                            pos,
                            format!("'{actor}' is a class; create instances with new {actor}(...)"),
                        ))
                    }
                    None => return Err(Diagnostic::new(pos, "E_UNBOUND", format!("unknown actor '{actor}'"))),
                };
                self.imports.push(Import::ActorSpawn);
                TE {
                    e: TExpr::Spawn(a),
                    ty: Type::ActorRef(a),
                }
            }
            ExprKind::Member(base, name) => self.member(base, name, pos)?,
            ExprKind::MethodCall(base, name, args) => self.method_call(base, name, args, pos)?,
            ExprKind::Array(_) => return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                "array literals are parsed but not yet lowered to browser Wasm")),
            ExprKind::Lambda { .. } => return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                "lambdas are parsed but closure typing, captures, and browser Wasm lowering are not implemented")),
        })
    }

    fn enum_value(&mut self, enum_name: &str, variant: &str, base_pos: Pos, pos: Pos) -> R<TE> {
        let ei = match self.g.enum_(enum_name) {
            Some(e) => e,
            None => {
                return Err(Diagnostic::new(
                    base_pos,
                    "E_UNSUPPORTED",
                    format!("field initializers may only read enum variants; '{enum_name}' is not an enum"),
                ))
            }
        };
        let decl = &self.g.enums[ei as usize];
        match decl.variants.iter().position(|(v, _)| v == variant) {
            Some(i) => Ok(TE {
                e: TExpr::EnumVal(i as u32),
                ty: Type::Enum(ei),
            }),
            None => Err(Diagnostic::new(
                pos,
                "E_UNBOUND",
                format!("enum '{}' has no variant '{variant}'", decl.name),
            )),
        }
    }

    fn new_object(&mut self, class: &str, args: &[Expr], pos: Pos) -> R<TE> {
        if let Some(me) = self.actor_name() {
            return Err(isolation(pos, me, "sibling class", class));
        }
        if matches!(self.owner, Owner::FieldInit { .. }) {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED", "'new' in a field initializer"));
        }
        let ci = match self.g.class(class) {
            Some(c) => c,
            None if self.g.actor(class).is_some() => {
                return Err(type_err(pos, format!("'{class}' is an actor; start it with spawn {class}()")))
            }
            None => return Err(Diagnostic::new(pos, "E_UNBOUND", format!("unknown class '{class}'"))),
        };
        let info = &self.g.classes[ci as usize];
        if args.len() != info.ctor_params.len() {
            return Err(Diagnostic::new(
                pos,
                "E_ARITY",
                format!(
                    "constructor for {class} expects {} argument(s), got {}",
                    info.ctor_params.len(),
                    args.len()
                ),
            ));
        }
        let (idx, params) = (info.new_idx, info.ctor_params.clone());
        let targs = self.args(&format!("{class} constructor"), args, &params)?;
        Ok(TE {
            e: TExpr::Call(idx, targs),
            ty: Type::Class(ci),
        })
    }

    /// Check arguments against parameter types; object arguments move.
    fn args(&mut self, callee: &str, args: &[Expr], params: &[Type]) -> R<Vec<TE>> {
        let mut out = Vec::new();
        for (i, (a, want)) in args.iter().zip(params).enumerate() {
            let v = self.consume_expected(a, *want)?;
            if v.ty != *want {
                return Err(type_err(
                    a.pos,
                    format!(
                        "argument {} of '{callee}' has type {} but expected {}",
                        i + 1,
                        self.tn(v.ty),
                        self.tn(*want)
                    ),
                ));
            }
            out.push(v);
        }
        Ok(out)
    }

    fn arity(&self, callee: &str, want: usize, got: usize, pos: Pos) -> R<()> {
        if want != got {
            return Err(Diagnostic::new(
                pos,
                "E_ARITY",
                format!("call arity mismatch: '{callee}' takes {want} argument(s), found {got}"),
            ));
        }
        Ok(())
    }

    /// The class whose private members the current code may use.
    fn inside_class(&self) -> Option<u32> {
        match self.owner {
            Owner::Class { c, .. } => Some(c),
            _ => None,
        }
    }

    fn member(&mut self, base: &Expr, name: &str, pos: Pos) -> R<TE> {
        if let ExprKind::Var(n) = &base.kind {
            if self.recover_error.as_deref() == Some(n) {
                let (_, _, msg, kind, _) = self.unwind.expect("recovery needs unwind slots");
                // ErrorView is an ephemeral compiler-issued view, never a
                // first-class object or a transferable/returnable handle.
                return match name {
                    "message" => Ok(TE { e: TExpr::Local(msg), ty: Type::Str }),
                    "is_raise" => Ok(TE { e: TExpr::Local(kind), ty: Type::Bool }),
                    _ => Err(Diagnostic::new(pos, "E_UNBOUND",
                        format!("unknown ErrorView property '{name}'"))),
                };
            }
            if let Some(l) = self.lookup(n) {
                if let Some(payload) = l.mail {
                    return match name {
                        "value" if payload == Type::Bool => Ok(TE {
                            e: TExpr::Bin(
                                BinOp::Ne,
                                Box::new(TE {
                                    e: TExpr::Local(0),
                                    ty: Type::Int,
                                }),
                                Box::new(TE {
                                    e: TExpr::I64(0),
                                    ty: Type::Int,
                                }),
                            ),
                            ty: Type::Bool,
                        }),
                        "value" => Ok(TE {
                            e: TExpr::Local(0),
                            ty: Type::Int,
                        }),
                        "sequence" => Ok(TE {
                            e: TExpr::Local(1),
                            ty: Type::Int,
                        }),
                        "recipient" | "sender" => Err(Diagnostic::new(
                            pos,
                            "E_UNSUPPORTED_TYPE",
                            format!("ActorMail.{name} (ActorId values) is not supported by the browser compiler yet"),
                        )),
                        _ => Err(Diagnostic::new(pos, "E_UNBOUND", format!("ActorMail has no member '{name}'"))),
                    };
                }
            } else if self.g.enum_(n).is_some() {
                if let Some(me) = self.actor_name() {
                    return Err(isolation(base.pos, me, "sibling enum", n));
                }
                return self.enum_value(n, name, base.pos, pos);
            } else if self.g.class(n).is_some() {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED",
                    "static fields are not supported by the browser compiler yet",
                ));
            }
        }
        if let ExprKind::SelfRef = base.kind {
            match self.owner {
                Owner::Class { c, is_static: false, .. } => {
                    return self.field_get(
                        TE {
                            e: TExpr::Local(0),
                            ty: Type::Class(c),
                        },
                        name,
                        pos,
                    )
                }
                Owner::Actor { a } => {
                    let actor = &self.g.actors[a as usize];
                    return match actor.fields.iter().find(|f| f.name == name) {
                        Some(f) => Ok(TE {
                            e: TExpr::GlobalGet(f.slot),
                            ty: f.ty,
                        }),
                        None => Err(Diagnostic::new(
                            pos,
                            "E_UNBOUND",
                            format!("actor '{}' has no field '{name}'", actor.name),
                        )),
                    };
                }
                _ => return Err(Diagnostic::new(base.pos, "E_UNBOUND", "unknown name 'self'")),
            }
        }
        let obj = self.value(base)?;
        self.member_on(obj, name, pos)
    }

    #[inline(never)]
    fn member_on(&mut self, obj: TE, name: &str, pos: Pos) -> R<TE> {
        if obj.ty == Type::Str {
            return Err(string_member_err(name, pos));
        }
        match obj.ty {
            Type::Class(_) => self.field_get(obj, name, pos),
            Type::ActorRef(_) => Err(Diagnostic::new(
                pos,
                "E_PRIVATE",
                "actor fields are private mailbox-owned state; communicate with send(...)",
            )),
            t => Err(type_err(pos, format!("{} has no member '{name}'", self.tn(t)))),
        }
    }

    fn field_get(&mut self, obj: TE, name: &str, pos: Pos) -> R<TE> {
        let Type::Class(c) = obj.ty else {
            unreachable!("field_get on a class")
        };
        let class = &self.g.classes[c as usize];
        let f = match class.fields.iter().find(|f| f.name == name) {
            Some(f) => f,
            None => {
                let what = if class.methods.iter().any(|m| m.name == name) {
                    format!("'{}.{name}' is a method; call it with ()", class.name)
                } else {
                    format!("class '{}' has no field '{name}'", class.name)
                };
                return Err(Diagnostic::new(pos, "E_UNBOUND", what));
            }
        };
        if f.visibility == FieldVisibility::Private && self.inside_class() != Some(c) {
            return Err(Diagnostic::new(
                pos,
                "E_PRIVATE",
                format!(
                    "private field '{}.{name}' is accessible only from code declared in class {}",
                    class.name, class.name
                ),
            ));
        }
        // An exclusive loan of an owner prohibits reading even a scalar
        // field through the original owner's name until that loan ends.
        // This is particularly important for compiler-generated tuple roots:
        // their scalar projections must not bypass an existing mutable loan.
        if matches!(&obj.e, TExpr::Local(slot) if
            self.loans.values().any(|loan| loan.owner == *slot && loan.mutable))
        {
            return Err(Diagnostic::new(pos, "E_BORROW",
                "cannot read owner fields while an exclusive mutable loan is live"));
        }
        // A borrowed aggregate cannot yield an independently owned handle.
        // Without a nested-loan provenance IR, such a field could escape
        // the original owner's lifetime by ordinary binding or return.
        if matches!(&obj.e, TExpr::Local(slot) if self.loans.contains_key(slot))
            && matches!(f.ty, Type::Class(_) | Type::ActorRef(_) | Type::GeneratorInt)
        {
            return Err(Diagnostic::new(pos, "E_BORROW",
                "borrowed object field cannot yield an owned handle without nested-loan provenance"));
        }
        // Class privacy does not grant sealed state access: require a
        // compiler-recognized lease on the exact receiver instance.
        let protected = f.mode == FieldMode::ActorState && class.state_container;
        if protected {
            let same_receiver = matches!(&obj.e, TExpr::Local(0))
                && matches!(self.owner,
                    Owner::Class { c: owner, ctor: false, is_static: false } if owner == c);
            if !same_receiver || !(self.state_read_scope || self.state_write_scope) {
                return Err(Diagnostic::new(pos, "E_STATE_BORROW",
                    "protected state read requires critical-read or critical-write on this receiver"));
            }
        }
        Ok(TE {
            e: if protected {
                TExpr::StateFieldRead { obj: Box::new(obj), offset: f.slot }
            } else {
                TExpr::FieldGet { obj: Box::new(obj), offset: f.slot }
            },
            ty: f.ty,
        })
    }

    fn method_call(&mut self, base: &Expr, name: &str, args: &[Expr], pos: Pos) -> R<TE> {
        // Class.static(args)
        if let ExprKind::Var(n) = &base.kind {
            if self.lookup(n).is_none() {
                if let Some(c) = self.g.class(n) {
                    if let Some(me) = self.actor_name() {
                        return Err(isolation(base.pos, me, "sibling class", n));
                    }
                    let class = &self.g.classes[c as usize];
                    let m = match class.methods.iter().find(|m| m.name == name) {
                        Some(m) => m.clone(),
                        None => {
                            return Err(Diagnostic::new(
                                pos,
                                "E_UNBOUND",
                                format!("class '{n}' has no static function '{name}'"),
                            ))
                        }
                    };
                    if !m.is_static {
                        return Err(type_err(pos, format!("'{n}.{name}' is an instance method; call it on an instance")));
                    }
                    if !m.public && self.inside_class() != Some(c) {
                        return Err(Diagnostic::new(
                            pos,
                            "E_PRIVATE",
                            format!("private static function '{n}.{name}' is accessible only from code declared in class {n}"),
                        ));
                    }
                    let label = format!("{n}.{name}");
                    self.arity(&label, m.params.len(), args.len(), pos)?;
                    let targs = self.args(&label, args, &m.params)?;
                    return Ok(TE {
                        e: TExpr::Call(m.idx, targs),
                        ty: m.ret,
                    });
                }
                if self.g.enum_(n).is_some() || self.g.actor(n).is_some() {
                    return Err(Diagnostic::new(pos, "E_UNSUPPORTED", format!("'{n}' has no callable members")));
                }
            }
        }
        // self.method(args)
        if let ExprKind::SelfRef = base.kind {
            match self.owner {
                Owner::Class { c, is_static: false, .. } => {
                    let recv = TE {
                        e: TExpr::Local(0),
                        ty: Type::Class(c),
                    };
                    return self.instance_call(recv, c, name, args, pos);
                }
                Owner::Actor { a } => {
                    let actor = &self.g.actors[a as usize];
                    if name == "receive" {
                        return Err(Diagnostic::new(
                            pos,
                            "E_ACTOR",
                            "receive runs only for delivered mail; it cannot be called directly",
                        ));
                    }
                    let m = match actor.methods.iter().find(|m| m.name == name) {
                        Some(m) => m.clone(),
                        None => {
                            return Err(Diagnostic::new(
                                pos,
                                "E_UNBOUND",
                                format!("actor '{}' has no method '{name}'", actor.name),
                            ))
                        }
                    };
                    let label = format!("{}.{name}", actor.name);
                    self.arity(&label, m.params.len(), args.len(), pos)?;
                    let targs = self.args(&label, args, &m.params)?;
                    return Ok(TE {
                        e: TExpr::Call(m.idx, targs),
                        ty: m.ret,
                    });
                }
                _ => return Err(Diagnostic::new(base.pos, "E_UNBOUND", "unknown name 'self'")),
            }
        }
        let recv = self.value(base)?;
        self.method_on(recv, name, args, pos)
    }

    #[inline(never)]
    fn method_on(&mut self, recv: TE, name: &str, args: &[Expr], pos: Pos) -> R<TE> {
        if recv.ty == Type::Str {
            return self.string_method(recv, name, args, pos);
        }
        match recv.ty {
            Type::Class(c) => {
                // Calls on a loan may only return copyable, lifetime-independent
                // values. Owned object returns need result-lifetime provenance.
                if matches!(&recv.e, TExpr::Local(slot) if self.loans.contains_key(slot)) {
                    if let Some(m) = self.g.classes[c as usize].methods.iter().find(|m| m.name == name) {
                        if matches!(m.ret, Type::Class(_) | Type::ActorRef(_) | Type::GeneratorInt) {
                            return Err(Diagnostic::new(pos, "E_BORROW",
                                "borrowed receiver cannot return an owned handle without result provenance"));
                        }
                    }
                }
                self.instance_call(recv, c, name, args, pos)
            }
            Type::ActorRef(a) => {
                let actor = &self.g.actors[a as usize];
                if name != "send" {
                    return Err(Diagnostic::new(
                        pos,
                        "E_UNSUPPORTED",
                        format!(
                            "calling actor methods directly ('{}.{name}') is not supported; send a message with send(...)",
                            actor.name
                        ),
                    ));
                }
                if actor.receive_idx.is_none() {
                    return Err(type_err(
                        pos,
                        format!(
                            "actor '{}' has no receive(ActorMail<T>) handler, so it cannot accept send",
                            actor.name
                        ),
                    ));
                }
                let (payload, actor_name) = (actor.payload, actor.name.clone());
                self.arity("ActorRef.send", 1, args.len(), pos)?;
                let v = self.value(&args[0])?;
                if v.ty != payload {
                    return Err(type_err(
                        args[0].pos,
                        format!(
                            "ActorRef.send mailbox value has type {} but '{actor_name}' receives ActorMail<{}>",
                            self.tn(v.ty),
                            self.tn(payload)
                        ),
                    ));
                }
                self.imports.push(Import::ActorSend);
                Ok(TE {
                    e: TExpr::Send {
                        target: Box::new(recv),
                        value: Box::new(v),
                    },
                    ty: Type::Void,
                })
            }
            t => Err(type_err(pos, format!("{} has no method '{name}'", self.tn(t)))),
        }
    }

    fn instance_call(&mut self, recv: TE, c: u32, name: &str, args: &[Expr], pos: Pos) -> R<TE> {
        let class = &self.g.classes[c as usize];
        let m = match class.methods.iter().find(|m| m.name == name) {
            Some(m) => m.clone(),
            None => {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNBOUND",
                    format!("class '{}' has no method '{name}'", class.name),
                ))
            }
        };
        let cname = class.name.clone();
        if m.is_static {
            return Err(type_err(
                pos,
                format!("'{cname}.{name}' is a static function; call it as {cname}.{name}(...)"),
            ));
        }
        if !m.public && self.inside_class() != Some(c) {
            return Err(Diagnostic::new(
                pos,
                "E_PRIVATE",
                format!("private method '{cname}.{name}' is accessible only from code declared in class {cname}"),
            ));
        }
        let label = format!("{cname}.{name}");
        self.arity(&label, m.params.len(), args.len(), pos)?;
        let mut targs = vec![recv];
        targs.extend(self.args(&label, args, &m.params)?);
        Ok(TE {
            e: TExpr::Call(m.idx, targs),
            ty: m.ret,
        })
    }

    fn call(&mut self, name: &str, args: &[Expr], pos: Pos) -> R<TE> {
        if matches!(self.owner, Owner::FieldInit { .. }) {
            return Err(Diagnostic::new(pos, "E_UNSUPPORTED", "calls in a field initializer"));
        }
        if let Some(b) = match name {
            "And" => Some(Builtin::And),
            "Or" => Some(Builtin::Or),
            "Xor" => Some(Builtin::Xor),
            _ => None,
        } {
            if self.lookup(name).is_none() {
                // An array literal in this exact builtin position is an
                // unescaped, read-only scalar argument pack. No general
                // heap Array<bool> value, indexing, or mutable alias exists.
                let values: &[Expr] = if args.len() == 1 {
                    match &args[0].kind {
                        ExprKind::Array(items) => {
                            if items.iter().any(|e| !matches!(&e.kind,
                                ExprKind::Bool(_) | ExprKind::Var(_))) {
                                return Err(Diagnostic::new(pos, "E_UNSUPPORTED",
                                    "boolean array gate pack admits only immutable bool literals or bindings"));
                            }
                            items
                        }
                        _ => return Err(Diagnostic::new(pos, "E_ARITY",
                            format!("{name} expects at least 2 bool arguments or a scalar array literal"))),
                    }
                } else { args };
                if values.len() < 2 {
                    return Err(Diagnostic::new(pos, "E_ARITY",
                        format!("{name} expects at least 2 bool arguments")));
                }
                if values.len() > crate::parser::MAX_PARAMS {
                    return Err(Diagnostic::new(pos, "E_SOURCE_LIMIT",
                        format!("{name} has too many boolean operands")));
                }
                // Normal functions eagerly evaluate all arguments; nested
                // typed binary builtins retain exact left-to-right behavior.
                let mut iter = values.iter();
                let first = iter.next().expect("checked operand minimum");
                let mut accumulated = self.value(first)?;
                if accumulated.ty != Type::Bool {
                    return Err(type_err(first.pos, format!("{name} needs bool arguments")));
                }
                for arg in iter {
                    let next = self.value(arg)?;
                    if next.ty != Type::Bool {
                        return Err(type_err(arg.pos, format!("{name} needs bool arguments")));
                    }
                    accumulated = TE {
                        e: TExpr::Builtin(b, Box::new(accumulated), Box::new(next)),
                        ty: Type::Bool,
                    };
                }
                return Ok(accumulated);
            }
        }
        if name == "stdio.print" || name == "stdio.println" {
            // The parser desugars `stdio.out << value` and the explicit
            // `writech stdio.out, value` through this checked builtin.
            // Never let a lexical binding named `stdio` be silently bypassed
            // by that syntactic rewrite: it denotes a different receiver.
            // Full stream capability dispatch can resolve shadowed names
            // when it is implemented.
            if self.lookup("stdio").is_some() {
                return Err(Diagnostic::new(pos, "E_IO_SHADOW",
                    "the builtin stdio capability is shadowed by a local binding; use an unshadowed handle"));
            }
            let newline = name == "stdio.println";
            if args.len() != 1 {
                return Err(Diagnostic::new(
                    pos,
                    "E_ARITY",
                    format!("{name} takes 1 argument, found {}", args.len()),
                ));
            }
            if newline {
                self.imports.push(Import::PrintNewline);
            }
            if let ExprKind::Str(s) = &args[0].kind {
                let (offset, len) = self.string(s, pos)?;
                self.imports.push(Import::PrintStr);
                return Ok(TE {
                    e: TExpr::PrintStr { offset, len, newline },
                    ty: Type::Void,
                });
            }
            let v = self.value(&args[0])?;
            return match v.ty {
                Type::Float => {
                    self.imports.push(Import::PrintF64);
                    Ok(TE {
                        e: TExpr::Print {
                            value: Box::new(v),
                            newline,
                        },
                        ty: Type::Void,
                    })
                }
                Type::Str => {
                    self.imports.push(Import::PrintStr);
                    let tmp = self.temp(Type::Str, pos)?;
                    Ok(TE {
                        e: TExpr::PrintStrVal {
                            value: Box::new(v),
                            tmp,
                            newline,
                        },
                        ty: Type::Void,
                    })
                }
                Type::Int | Type::Bool => {
                    self.imports
                        .push(if v.ty == Type::Int { Import::PrintI64 } else { Import::PrintBool });
                    Ok(TE {
                        e: TExpr::Print {
                            value: Box::new(v),
                            newline,
                        },
                        ty: Type::Void,
                    })
                }
                Type::Class(c) => self.print_object(v, c, newline, pos),
                t => Err(Diagnostic::new(
                    args[0].pos,
                    "E_UNSUPPORTED",
                    format!("printing a {} value is not supported by the browser compiler yet", self.tn(t)),
                )),
            };
        }
        if self.lookup(name).is_some() {
            return Err(Diagnostic::new(
                pos,
                "E_UNSUPPORTED",
                format!("'{name}' is a local value, not a function"),
            ));
        }
        if let Some(me) = self.actor_name() {
            if self.g.names.contains_key(name) {
                return Err(isolation(pos, me, "file/module callable", name));
            }
        }
        let (idx, params, ret) = match self.g.sigs.get(&(name.to_string(), args.len())) {
            Some(s) => s.clone(),
            None => {
                return Err(match self.g.names.get(name) {
                    Some(arities) => Diagnostic::new(
                        pos,
                        "E_ARITY",
                        format!(
                            "call arity mismatch: '{name}' takes {} argument(s), found {}",
                            arities.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(" or "),
                            args.len()
                        ),
                    ),
                    None if self.g.class(name).is_some() => Diagnostic::new(
                        pos,
                        "E_NEW_REQUIRED",
                        format!("'{name}' is a class; create instances with new {name}(...)"),
                    ),
                    None => Diagnostic::new(pos, "E_UNBOUND", format!("unknown name '{name}'")),
                })
            }
        };
        let targs = self.args(name, args, &params)?;
        Ok(TE {
            e: TExpr::Call(idx, targs),
            ty: ret,
        })
    }

    /// The Java reference's string members (TypeChecker string member
    /// table) that lower without allocation.
    fn string_method(&mut self, recv: TE, name: &str, args: &[Expr], pos: Pos) -> R<TE> {
        let (op, arity) = match name {
            "trim" => (StrOp::Trim, 0),
            "starts_with" => (StrOp::StartsWith, 1),
            "ends_with" => (StrOp::EndsWith, 1),
            "contains_literal" => (StrOp::Contains, 1),
            _ => return Err(string_member_err(name, pos)),
        };
        let label = format!("string.{name}");
        self.arity(&label, arity, args.len(), pos)?;
        let arg = match args.first() {
            Some(a) => {
                let v = self.value(a)?;
                if v.ty != Type::Str {
                    return Err(type_err(a.pos, format!("{label} needs a string argument, found {}", self.tn(v.ty))));
                }
                Some(Box::new(v))
            }
            None => None,
        };
        Ok(TE {
            ty: if op == StrOp::Trim { Type::Str } else { Type::Bool },
            e: TExpr::Str(op, Box::new(recv), arg),
        })
    }

    fn string(&mut self, s: &str, pos: Pos) -> R<(u32, u32)> {
        if self.data.len() + s.len() > MAX_STRING_DATA {
            return Err(Diagnostic::new(pos, "E_SOURCE_LIMIT", "too much string literal data"));
        }
        let offset = self.data.len() as u32;
        self.data.extend_from_slice(s.as_bytes());
        Ok((offset, s.len() as u32))
    }

    /// `Name{a=1, b=true}`: the Java reference's object rendering.
    fn print_object(&mut self, v: TE, c: u32, newline: bool, pos: Pos) -> R<TE> {
        let class = &self.g.classes[c as usize];
        // Internal scalar products retain real guest-heap field storage but
        // display their documented positional notation, not the compiler's
        // private synthesized class name. User code cannot spell the reserved
        // product name prefix; shape_lower rejects attempted forgery.
        let product_style = if class.name.starts_with(crate::shape_lower::PREFIX) {
            if class.name.starts_with("__atto_shape_tuple_") { 1u8 }
            else if class.name.starts_with("__atto_shape_pair_") { 2u8 }
            else if class.name.starts_with("__atto_shape_entry_") { 3u8 }
            else { 0u8 }
        } else { 0u8 };
        let mut text = match product_style {
            1 => "(".to_owned(),
            2 => "Pair(".to_owned(),
            3 => "Entry(".to_owned(),
            _ => format!("{}{{", class.name),
        };
        let mut plan: Vec<(String, Option<(u32, Type)>)> = Vec::new();
        for (i, f) in class.fields.iter().enumerate() {
            if let Type::Enum(_) = f.ty {
                return Err(Diagnostic::new(
                    pos,
                    "E_UNSUPPORTED",
                    format!("printing class '{}' with enum field '{}' is not supported yet", class.name, f.name),
                ));
            }
            if i > 0 {
                text.push_str(", ");
            }
            if product_style == 0 {
                text.push_str(&f.name);
                text.push('=');
            }
            plan.push((std::mem::take(&mut text), Some((f.slot, f.ty))));
        }
        text.push(if product_style == 0 { '}' } else { ')' });
        plan.push((text, None));
        let mut pieces = Vec::new();
        for (s, field) in plan {
            let (off, len) = self.string(&s, pos)?;
            pieces.push(PrintPiece::Str(off, len));
            if let Some((offset, ty)) = field {
                self.imports.push(match ty {
                    Type::Int => Import::PrintI64,
                    Type::Float => Import::PrintF64,
                    Type::Str => Import::PrintStr,
                    _ => Import::PrintBool,
                });
                pieces.push(PrintPiece::Field(offset, ty));
            }
        }
        self.imports.push(Import::PrintStr);
        let tmp = self.temp(Type::Class(c), pos)?;
        Ok(TE {
            e: TExpr::PrintObj {
                obj: Box::new(v),
                tmp,
                pieces,
                newline,
            },
            ty: Type::Void,
        })
    }
}


/// Check proposed nominal actor interfaces *inside the production AST*.
/// This does not typecheck the concrete method bodies or enable codegen.
/// It prevents duplicate or incompatible in-actor/out-of-line declarations.
pub fn check_target_actor_interface(program: &Program) -> R<()> {
    let Some(interface) = &program.actor_interface else { return Ok(()); };
    for (i, name) in interface.forwards.iter().enumerate() {
        if interface.forwards[..i].contains(name) {
            return Err(Diagnostic::new(Pos::default(), "E_DUPLICATE",
                format!("duplicate forward actor '{name}'")));
        }
    }
    for (i, actor) in program.actors.iter().enumerate() {
        if !interface.forwards.contains(&actor.name) {
            return Err(Diagnostic::new(actor.pos, "E_UNBOUND",
                format!("actor definition '{}' has no matching declaration", actor.name)));
        }
        if program.actors[..i].iter().any(|a| a.name == actor.name) {
            return Err(Diagnostic::new(actor.pos, "E_DUPLICATE",
                format!("duplicate concrete actor '{}'", actor.name)));
        }
        let owner = interface.forwards.iter().position(|n| n == &actor.name)
            .expect("validated actor declaration");
        for method in interface.methods.iter().filter(|m| m.owner as usize == owner) {
            if method.name == "receive" {
                return Err(Diagnostic::new(method.pos, "E_SIGNATURE",
                    "receive is a sealed actor lifecycle handler"));
            }
            if actor.fields.iter().any(|f| f.name == method.name) {
                return Err(Diagnostic::new(method.pos, "E_DUPLICATE",
                    format!("receiver '{}.{}' collides with actor state", actor.name, method.name)));
            }
            for inside in &actor.methods {
                if inside.name == method.name && inside.params.len() == method.params.len() {
                    let equal = inside.ret == method.ret &&
                        inside.public == method.public &&
                        inside.params.iter().zip(&method.params).all(|(a,b)| a.ty == b.ty);
                    return Err(Diagnostic::new(method.pos,
                        if equal { "E_DUPLICATE" } else { "E_SIGNATURE" },
                        format!("receiver '{}.{}' collides with in-actor method",
                            actor.name, method.name)));
                }
            }
        }
    }
    Ok(())
}

/// Any return/throw/raise/cursor delegation anywhere in `body`, including
/// nested blocks: a finally block must never replace the pending outcome.
fn exits_anywhere(body: &[TStmt]) -> bool {
    stmt_exists(body, &|s| matches!(s,
        TStmt::Return(_) | TStmt::Throw(_) | TStmt::Raise(_) | TStmt::RecoverNext))
}

/// Whether any statement in `body` (recursively) satisfies `f`.
fn stmt_exists(body: &[TStmt], f: &dyn Fn(&TStmt) -> bool) -> bool {
    body.iter().any(|s| f(s) || match s {
        TStmt::If(arms, other) => arms.iter().any(|(_, b)| stmt_exists(b, f))
            || other.as_ref().is_some_and(|b| stmt_exists(b, f)),
        TStmt::Loop { body, update, .. } => stmt_exists(body, f) || stmt_exists(update, f),
        TStmt::ForIn { body, .. } => stmt_exists(body, f),
        TStmt::Block(b) | TStmt::StateCriticalWrite(b) => stmt_exists(b, f),
        TStmt::Try { body, catch, finally, .. } => stmt_exists(body, f)
            || catch.as_ref().is_some_and(|b| stmt_exists(b, f))
            || finally.as_ref().is_some_and(|b| stmt_exists(b, f)),
        TStmt::Defer { body, .. } | TStmt::Recover { body, .. } => stmt_exists(body, f),
        _ => false,
    })
}
