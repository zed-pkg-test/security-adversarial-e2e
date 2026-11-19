//! Named callables must explicitly declare their result, including void.
//! This suite only proves Rust parser/checker output when actually executed.
use atto_compiler::{compile, lexer::lex, parser::Parser};
use atto_compiler::ast::Type;
use atto_compiler::target_syntax::parse_target_declarations;

#[test]
fn concrete_void_and_int_results_are_declared() {
    let src = r#"
      define class C as
        get() -> int { return 1; }
        reset(): void { }
        static fnc zero() -> int { return 0; }
      end
      fnc noop(): void { }
      fnc number() -> int { return 42; }
      pub fnc main() -> int { return number(); }
    "#;
    let p = Parser::new(lex(src).unwrap()).parse_program().unwrap();
    assert_eq!(p.funcs[0].ret, Type::Void);
    assert_eq!(p.funcs[1].ret, Type::Int);
    assert_eq!(p.classes[0].methods[0].ret, Type::Int);
    assert_eq!(p.classes[0].methods[1].ret, Type::Void);
    assert_eq!(p.classes[0].methods[2].ret, Type::Int);
}

#[test]
fn absent_annotation_never_means_implicit_void() {
    for src in [
        "fnc missing() { }",
        "fnc missing() { return 3; }",
        "define class C as missing() { } end",
        "define class C as static fnc missing() { } end",
        "define actor A as ping() { } end",
    ] {
        let tokens = lex(src).unwrap();
        let d = Parser::new(tokens).parse_program().unwrap_err();
        assert_eq!(d.code, "E_RETURN_ANNOTATION", "{src}: {d}");
    }
}

#[test]
fn infer_is_explicit_and_yields_concrete_types_for_proven_simple_results() {
    let src = r#"
      fnc inferred() -> infer { return 42; }
      fnc inferred_bool(): infer { return true; }
      fnc inferred_void(): infer { return; }
      fnc inferred_arg(int x): infer { return x; }
      define class C as
        get(): infer { return 2 + 3; }
      end
      pub fnc main() -> int { return inferred(); }
    "#;
    let p = Parser::new(lex(src).unwrap()).parse_program().unwrap();
    assert_eq!(p.funcs[0].ret, Type::Int);
    assert_eq!(p.funcs[1].ret, Type::Bool);
    assert_eq!(p.funcs[2].ret, Type::Void);
    assert_eq!(p.funcs[3].ret, Type::Int);
    assert_eq!(p.classes[0].methods[0].ret, Type::Int);
    let bytes = compile(src).unwrap();
    assert_eq!(&bytes[..8], &[0, 97, 115, 109, 1, 0, 0, 0]);
}

#[test]
fn inconsistent_infer_fails_closed_without_compiled_guest() {
    let src = r#"
      fnc contradictory() -> infer {
        return 3;
        return false;
      }
      pub fnc main() -> int { return 0; }
    "#;
    let d = compile(src).unwrap_err();
    assert_eq!(d.code, "E_RETURN_INFER", "{d}");
}

#[test]
fn unprovable_infer_requires_explicit_type() {
    let src = r#"
      fnc opaque() -> infer { return call_that_cannot_be_inferred(); }
      pub fnc main() -> int { return 0; }
    "#;
    let d = compile(src).unwrap_err();
    assert_eq!(d.code, "E_RETURN_INFER", "{d}");
}

#[test]
fn out_of_line_receivers_require_return_annotations() {
    let invalid = "define class C as end mtd (self: C) get() { return 3; }";
    let d = parse_target_declarations(&lex(invalid).unwrap()).unwrap_err();
    assert_eq!(d.code, "E_RETURN_ANNOTATION", "{d}");
    let valid = "define class C as end mtd (self: C) get() -> int { return 3; }";
    let p = parse_target_declarations(&lex(valid).unwrap()).unwrap();
    assert_eq!(p.receivers[0].return_type, "int");
}

#[test]
fn infer_supports_erlang_style_typed_tail_without_implicit_void() {
    let src = r#"
      fnc tail() -> infer :: 40 + 2 end
      pub fnc main() -> int { return tail(); }
    "#;
    let p = Parser::new(lex(src).unwrap()).parse_program().unwrap();
    assert_eq!(p.funcs[0].ret, Type::Int);
    let guest = compile(src).unwrap();
    assert_eq!(&guest[..8], &[0, 97, 115, 109, 1, 0, 0, 0]);
}

#[test]
fn actor_receive_requires_declared_void_not_infer() {
    for header in [
        "receive(ActorMail<int> mail) -> infer { }",
        "receive(ActorMail<int> mail) -> int { }",
    ] {
        let src = format!(
            "define actor Worker as {header} end pub fnc main() -> int {{ return 0; }}"
        );
        let d = Parser::new(lex(&src).unwrap()).parse_program().unwrap_err();
        assert_eq!(d.code, "E_TYPE", "{src}: {d}");
    }
}

#[test]
fn target_scanner_accepts_bounded_generic_return_first_headers() {
    // Token-only scanning cannot bypass the later checked guest frontend.
    let source = r#"
        declare class C;
        pub mtd (C self) Option<Result<int,string>> <- get() begin return None; end
        fnc Result<int,string> <- make() { return Ok(42); }
        Option<int> <- spare() begin return Some(9); end
    "#;
    let p = parse_target_declarations(&lex(source).unwrap()).unwrap();
    assert_eq!(p.receivers.len(), 1);
    assert_eq!(p.receivers[0].return_type, "Option<Result<int,string>>");
}

#[test]
fn target_scanner_rejects_bad_or_unbounded_generic_headers() {
    for source in [
        "Option<> <- f() begin end",
        "Result<int> <- f() begin end",
        "Option<int <- f() begin end",
        "Unsupported<int> <- f() begin end",
    ] {
        assert!(parse_target_declarations(&lex(source).unwrap()).is_err(), "{source}");
    }
    let nested = format!("{}int{} <- f() begin end",
        "Option<".repeat(18), ">".repeat(18));
    let diagnostic = parse_target_declarations(&lex(&nested).unwrap()).unwrap_err();
    assert_eq!(diagnostic.code, "E_SOURCE_LIMIT", "{diagnostic}");
}
