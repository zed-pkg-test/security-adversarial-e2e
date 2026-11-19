//! AttoLang browser compiler: `.atto` source -> WebAssembly, itself built for
//! `wasm32-unknown-unknown` so the playground compiles entirely client-side.
//!
//! Syntax follows `docs/grammar.ebnf` of the Java reference compiler; `int`
//! follows the LLVM backend and spec chapter 17 (signed 64-bit, checked).
//! This is a subset compiler: every construct outside the admitted subset is
//! rejected with a diagnostic and never produces an artifact. See README.md.

pub mod ast;
/// Versioned actor-owned scalar snapshot codec groundwork, not durable runtime.
pub mod actor_persistence;
/// Recognize and reject unlowered named collection layouts before Wasm emission.
pub mod collection_layout;
/// Target-ABI-agnostic checked scalar layout planning; no guest allocation.
pub mod collection_layout_plan;
/// Executable Rust storage kernel only; source-compiled guest admission remains gated.
pub mod collection_layout_storage;
/// Narrow genuine source-compiled scalar collection guest profile; all else fails closed.
pub mod collection_layout_guest;
/// Shared canonical generic binding for production and guest collection parsers.
pub mod collection_layout_type;
/// Pinned canonical typed AOT copy-plan admission (borrow-checker.rs PR #32).
/// Source Git blob 3008a139cfba41131839de3567a263163152cf00.
// The canonical verifier is imported byte-identically from the independent
// checker. Do not edit its SHA-pinned body for Clippy-only style changes.
#[allow(clippy::needless_return)]
pub mod copy_graph_v1;
pub mod check;
pub mod diag;
pub mod generator_cfg;
pub mod generator_frame;
pub mod lexer;
pub mod io_shorthand;
pub mod detached_io;
pub mod parser;
/// Checked single-source module functions; external imports remain unlinked.
pub mod module_lower;
/// Fail-closed monomorphic scalar Any specialization; no dynamic Any ABI.
pub mod any_type_lower;
/// Source-local scalar products use the checked class/constructor guest ABI.
pub mod shape_lower;
/// Identity-free value classes cannot be compiled as identity-bearing browser classes.
pub mod value_class_admission;
/// Checked source-local trait and class composition.
pub mod nominal_lower;
/// Explicitly unlinked foreign prototypes and source-only exports.
pub mod visibility_lower;
/// Direct routine-only and statically specialized named callbacks.
pub mod routine_lower;
/// Bounded reference scheduler gate; not yet wired to guest Wasm execution.
pub mod state_admission;
pub mod target_syntax;
pub mod tuple_binding_admission;
pub mod tuple_binding_lower;
pub mod target_typed;
pub mod wasm;

pub use diag::{Diagnostic, Pos};

pub const SOURCE_CAP: usize = 64 * 1024;
pub const ABI_VERSION: u32 = 2;
pub const COMPILER_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Compile one `.atto` source file to a guest WebAssembly module.
pub fn compile(source: &str) -> Result<Vec<u8>, Diagnostic> {
    if source.len() > SOURCE_CAP {
        return Err(Diagnostic::new(
            Pos { line: 1, col: 1 },
            "E_SOURCE_LIMIT",
            format!("source exceeds {SOURCE_CAP} UTF-8 bytes"),
        ));
    }
    let source_tokens = lexer::lex(source)?;
    // Bounded, source-compiled scalar layout specialization: complete grammar
    // and checked nominal field offsets are required before any Wasm bytes.
    if let Some(program) = collection_layout_guest::try_lower(&source_tokens)? {
        let bytes = wasm::emit(&program);
        if bytes.len() > wasm::MAX_OUTPUT {
            return Err(Diagnostic::new(Pos { line: 1, col: 1 },
                "E_OUTPUT_LIMIT", "generated module exceeds 1 MiB"));
        }
        return Ok(bytes);
    }
    // Nested generic Array graphs require a distinct owned allocation, indexing
    // and deep-copy ABI. Never misclassify their missing runtime as malformed
    // named layout syntax, or silently reinterpret copy!! graph requirements.
    for tokens in source_tokens.windows(4) {
        if matches!(
            (&tokens[0].tok, &tokens[1].tok, &tokens[2].tok, &tokens[3].tok),
            (lexer::Tok::Ident(outer), lexer::Tok::Lt,
             lexer::Tok::Ident(inner), lexer::Tok::Lt)
                if outer == "Array" && inner == "Array"
        ) {
            return Err(Diagnostic::new(tokens[0].pos, "E_UNSUPPORTED_TYPE",
                "nested Array<T> requires verified owned allocation, indexing and copy!! graph lowering"));
        }
    }
    // Nominal Array generic syntax goes through the production AST/checker.
    // General-purpose allocation remains fail-closed until fully checked.
    if source_tokens.windows(2).any(|pair| matches!(
        (&pair[0].tok, &pair[1].tok),
        (lexer::Tok::Ident(name), lexer::Tok::Lt) if name == "Array"
    )) {
        let mut parser = parser::Parser::new(source_tokens.clone());
        let parsed = parser.parse_program()?;
        if parsed.array_types.is_empty() {
            return Err(Diagnostic::new(Pos { line: 1, col: 1 },
                "E_UNSUPPORTED", "Array generic source has no validated collection type"));
        }
        let _ = check::check(&parsed)?;
        return Err(Diagnostic::new(Pos { line: 1, col: 1 },
            "E_UNSUPPORTED", "general-purpose collection execution is not enabled"));
    }
    // A nominal struct is a value; never accidentally dispatch a new
    // out-of-line struct receiver through shape_lower's identity-bearing
    // scalar-class preview ABI. Gate it until a true value ABI is verified.
    let mut structs = Vec::new();
    for w in source_tokens.windows(3) {
        if let [lexer::Token { tok: lexer::Tok::Ident(verb), .. },
                lexer::Token { tok: lexer::Tok::Ident(kind), .. },
                lexer::Token { tok: lexer::Tok::Ident(name), .. }] = w {
            if (verb == "define" || verb == "declare") && kind == "struct" {
                structs.push(name.as_str());
            }
        }
    }
    for (i, tok) in source_tokens.iter().enumerate() {
        if !matches!(&tok.tok, lexer::Tok::Ident(word) if word == "mtd" || word == "constructor") {
            continue;
        }
        let at = |j: usize| source_tokens.get(j).map(|t| &t.tok);
        let owner = match (at(i+1), at(i+2), at(i+3), at(i+4), at(i+5)) {
            (Some(lexer::Tok::LParen), Some(lexer::Tok::Ident(s)), Some(lexer::Tok::Colon),
                Some(lexer::Tok::Ident(n)), _) if s == "self" => Some(n.as_str()),
            (Some(lexer::Tok::LParen), Some(lexer::Tok::Ident(m)),
                Some(lexer::Tok::Ident(s)), Some(lexer::Tok::Colon),
                Some(lexer::Tok::Ident(n))) if m == "mut" && s == "self" => Some(n.as_str()),
            (Some(lexer::Tok::LParen), Some(lexer::Tok::Ident(n)),
                Some(lexer::Tok::RParen), _, _) => Some(n.as_str()),
            (Some(lexer::Tok::LParen), Some(lexer::Tok::Ident(n)),
                Some(lexer::Tok::Ident(s)), _, _) if s == "self" || s == "_" => Some(n.as_str()),
            _ => None,
        };
        if owner.is_some_and(|name| structs.contains(&name)) {
            return Err(Diagnostic::new(tok.pos, "E_UNSUPPORTED",
                "struct receiver/constructor needs a real value ABI; identity-bearing class fallback is forbidden"));
        }
    }
    // The expanded syntax is recognized before normal lowering so that
    // 'declare class' and out-of-line constructors can attach to a concrete
    // local class. Protected state may be parsed but MUST NOT be translated
    // into unlocked ordinary fields on this backend.
    let has_proposal = source_tokens.windows(2).any(|w|
        matches!((&w[0].tok, &w[1].tok),
            (lexer::Tok::Ident(a), lexer::Tok::Ident(b))
                if a == "declare" && (b == "class" || b == "struct")))
        || source_tokens.windows(4).any(|w|
            matches!((&w[0].tok, &w[1].tok, &w[2].tok, &w[3].tok),
                (lexer::Tok::Ident(a), lexer::Tok::Ident(b),
                 lexer::Tok::Ident(c), lexer::Tok::Ident(d))
                    if a == "define" && b == "state" && c == "on" && d == "class"))
        || source_tokens.windows(5).any(|w|
            matches!((&w[0].tok, &w[1].tok, &w[2].tok, &w[3].tok, &w[4].tok),
                (lexer::Tok::Ident(c), lexer::Tok::LParen, lexer::Tok::Ident(_),
                    lexer::Tok::RParen, lexer::Tok::LParen) if c == "constructor"));
    let source_tokens = if has_proposal {
        let headers = target_syntax::parse_target_declarations(&source_tokens)?;
        target_syntax::lower_class_receivers(&source_tokens, &headers)?
    } else {
        source_tokens
    };
    // Do not silently erase the 'value' modifier and emit identity-bearing objects.
    value_class_admission::preflight(&source_tokens)?;
    let mut visibility = visibility_lower::lower(source_tokens)?;
    collection_layout::reject_unlowered(&visibility.tokens)?;
    let toks = any_type_lower::lower(routine_lower::lower(shape_lower::lower(nominal_lower::lower(module_lower::lower(visibility.tokens)?)?)?)?)?;
    // Only the checked, bounded Copy-scalar Tuple profile can reach guest
    // lowering. Non-scalar tuple graphs/borrows fail closed before parser.
    let toks = tuple_binding_lower::lower(toks)?;
    // Detached tasks require ownership, completion callbacks and supervisor
    // error routing. Parse-check early; NEVER execute them as synchronous I/O.
    if let Some(detached) = detached_io::inspect(&toks)?.first() {
        return Err(Diagnostic::new(detached.pos, "E_UNSUPPORTED",
            "supervised do readch/writech syntax recognized, but detached I/O scheduling and completion callbacks are not implemented"));
    }
    // The browser guest already has a typed stdio.print output import.
    // Permit the exact stdio.out << value statement form to lower through
    // that existing checked path. All other channels, streams, read
    // directions and select registrations fail closed until implemented.
    for io in io_shorthand::inspect(&toks)? {
        if io.source_or_sink == "stdio.out"
            && io.direction == io_shorthand::Direction::Write
            && io.context == io_shorthand::Context::Standalone
            && io.mode == io_shorthand::Mode::Direct
            && !io.read_binder_on_left
        {
            continue;
        }
        return Err(Diagnostic::new(io.pos, "E_UNSUPPORTED",
            "I/O direction shorthand recognized, but this capability is not supported by the browser compiler; only standalone stdio.out writes are executable"));
    }
    // Detect target declarations at any file-scope position, not only at
    // source byte zero. Ignore comments/strings (the lexer already tokenizes
    // them) and ignore nested brace bodies so a string or local expression
    // cannot accidentally switch the compiler into the target grammar.
    let mut braces = 0usize;
    let mut target = false;
    for i in 0..toks.len() {
        match &toks[i].tok {
            lexer::Tok::LBrace => braces = braces.saturating_add(1),
            lexer::Tok::RBrace => braces = braces.saturating_sub(1),
            lexer::Tok::Ident(word) if braces == 0 => {
                let next = toks.get(i + 1).map(|token| &token.tok);
                if word == "declare" || word == "mtd" ||
                    (word == "use" && matches!(next,
                        Some(lexer::Tok::Ident(name)) if name == "namespace")) {
                    target = true;
                    break;
                }
            }
            _ => {}
        }
    }
    let program = if target {
        let headers = target_syntax::parse_target_declarations(&toks)?;
        if !headers.classes.is_empty() {
            // Out-of-line *immutable class* mtd is executable: translate the
            // receiver headers into equivalent in-class method tokens, then
            // reuse the full production parser, checker and guest Wasm emitter.
            // Namespace, imports, actor receivers and mutable-self are gated
            // inside the lowering helper, never silently compiled as classes.
            let lowered = target_syntax::lower_class_receivers(&toks, &headers)?;
            parser::Parser::new(lowered).parse_program()?
        } else {
            // Actor mtd stays strictly syntax/type preflight only. An ActorRef
            // must never acquire unverified synchronous method dispatch.
            let typed = target_typed::lower_target_signatures(&headers)?;
            let actor_ast = target_typed::build_actor_program(&headers, &typed);
            check::check_target_actor_interface(&actor_ast)?;
            return Err(Diagnostic::new(toks[0].pos, "E_UNSUPPORTED",
                "namespace-scoped actor declarations and mtd methods are syntax-only, not browser-lowered"));
        }
    } else {
        parser::Parser::new(toks).parse_program()?
    };
    // Validate exports against the parsed top-level symbol table, never a
    // lexical occurrence inside a class, nested method or foreign prototype.
    visibility_lower::resolve_exports(&mut visibility.exports, &program)?;
    let typed = check::check(&program)?;
    let mut bytes = wasm::emit(&typed);
    visibility_lower::metadata(&mut bytes, &visibility.exports);
    if bytes.len() > wasm::MAX_OUTPUT {
        return Err(Diagnostic::new(
            Pos { line: 1, col: 1 },
            "E_OUTPUT_LIMIT",
            "generated module exceeds 1 MiB",
        ));
    }
    Ok(bytes)
}

/// Browser host ABI (`atto-playground` compiler contract v2). One instance is
/// owned by one worker; callers copy results out before compiling again.
#[cfg(target_arch = "wasm32")]
mod abi {
    use super::*;
    use std::cell::RefCell;

    const ERROR_CAP: usize = 512;

    struct State {
        bytes: Vec<u8>,
        error: [u8; ERROR_CAP],
        line: u32,
        col: u32,
    }

    thread_local! {
        static STATE: RefCell<State> = const { RefCell::new(State { bytes: Vec::new(), error: [0; ERROR_CAP], line: 0, col: 0 }) };
    }
    static mut INPUT: [u8; SOURCE_CAP] = [0; SOURCE_CAP];

    #[no_mangle]
    pub extern "C" fn abi_version() -> u32 {
        ABI_VERSION
    }
    #[no_mangle]
    pub extern "C" fn input_ptr() -> u32 {
        std::ptr::addr_of_mut!(INPUT) as *mut u8 as usize as u32
    }
    #[no_mangle]
    pub extern "C" fn input_capacity() -> u32 {
        SOURCE_CAP as u32
    }
    #[no_mangle]
    pub extern "C" fn result_ptr() -> u32 {
        STATE.with(|s| s.borrow().bytes.as_ptr() as usize as u32)
    }
    #[no_mangle]
    pub extern "C" fn result_length() -> u32 {
        STATE.with(|s| s.borrow().bytes.len() as u32)
    }
    #[no_mangle]
    pub extern "C" fn error_ptr() -> u32 {
        STATE.with(|s| s.borrow().error.as_ptr() as usize as u32)
    }
    #[no_mangle]
    pub extern "C" fn error_line_number() -> u32 {
        STATE.with(|s| s.borrow().line)
    }
    #[no_mangle]
    pub extern "C" fn error_column_number() -> u32 {
        STATE.with(|s| s.borrow().col)
    }

    /// Returns 0 on success, 1 on a diagnostic. On error `result_length` is 0.
    #[no_mangle]
    pub extern "C" fn compile(length: i32) -> i32 {
        STATE.with(|s| {
            let mut st = s.borrow_mut();
            st.bytes = Vec::new();
            st.error = [0; ERROR_CAP];
            st.line = 0;
            st.col = 0;
            let fail = |st: &mut State, d: Diagnostic| {
                let msg = d.render();
                let mut n = msg.len().min(ERROR_CAP - 1);
                while !msg.is_char_boundary(n) {
                    n -= 1;
                }
                st.error[..n].copy_from_slice(&msg.as_bytes()[..n]);
                st.line = d.pos.line;
                st.col = d.pos.col;
                1
            };
            if length < 0 || length as usize > SOURCE_CAP {
                return fail(
                    &mut st,
                    Diagnostic::new(
                        Pos { line: 1, col: 1 },
                        "E_SOURCE_LIMIT",
                        format!("source exceeds {SOURCE_CAP} UTF-8 bytes"),
                    ),
                );
            }
            // SAFETY: single-threaded wasm; the host wrote `length` bytes before calling.
            let input: &[u8] = unsafe {
                std::slice::from_raw_parts(std::ptr::addr_of!(INPUT).cast::<u8>(), length as usize)
            };
            let source = match std::str::from_utf8(input) {
                Ok(s) => s,
                Err(_) => {
                    return fail(
                        &mut st,
                        Diagnostic::new(Pos { line: 1, col: 1 }, "E_UTF8", "source is not valid UTF-8"),
                    )
                }
            };
            match super::compile(source) {
                Ok(bytes) => {
                    st.bytes = bytes;
                    0
                }
                Err(d) => fail(&mut st, d),
            }
        })
    }
}
