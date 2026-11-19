//! Return-first <- and begin/end syntax. These forms are alternative
//! declarations; duplicate names in one unit remain an error. Runtime
//! conformance requires actually executing the compiled guest.
use atto_compiler::{compile, lexer::{lex, Tok}, parser::Parser};
use atto_compiler::ast::Type;
use atto_compiler::target_syntax::parse_target_declarations;

const INT_FORMS: &[&str] = &[
    "fnc calculate(int x) -> int { return x * 2; }",
    "fnc calculate(int x): int { return x * 2; }",
    "fnc calculate(int x): int -> { return x * 2; }",
    "fnc int <- calculate(int x) { return x * 2; }",
    "int <- calculate(int x) { return x * 2; }",
    "int <- calculate(int x) return x * 2; end",
    "int <- calculate(int x) begin return x * 2; end",
    "fnc int <- calculate(int x) begin return x * 2; end",
    "fnc calculate(int x) -> int begin return x * 2; end",
];

#[test]
fn all_requested_int_forms_share_signature_and_compile_to_wasm() {
    for header in INT_FORMS {
        let source = format!("{header}\npub fnc main() -> int {{ return calculate(21); }}");
        let p = Parser::new(lex(&source).unwrap()).parse_program().unwrap();
        assert_eq!(p.funcs[0].name, "calculate", "{header}");
        assert_eq!(p.funcs[0].params.len(), 1, "{header}");
        assert_eq!(p.funcs[0].ret, Type::Int, "{header}");
        let guest = compile(&source).unwrap();
        assert_eq!(&guest[..8], &[0, 97, 115, 109, 1, 0, 0, 0], "{header}");
    }
}

#[test]
fn void_forms_support_empty_brace_begin_and_bare_end_bodies() {
    for header in [
        "fnc reset() -> void { }",
        "fnc reset(): void { }",
        "fnc reset(): void -> { }",
        "fnc void <- reset() { }",
        "void <- reset() { }",
        "void <- reset() end",
        "void <- reset() begin end",
        "fnc void <- reset() begin end",
    ] {
        let src = format!("{header}\npub fnc main() -> int {{ reset(); return 0; }}");
        let p = Parser::new(lex(&src).unwrap()).parse_program().unwrap();
        assert_eq!(p.funcs[0].ret, Type::Void, "{header}");
        assert!(!compile(&src).unwrap().is_empty(), "{header}");
    }
}

#[test]
fn infer_forms_resolve_int_and_do_not_fallback_to_void() {
    for header in [
        "fnc calculate_other() -> infer { return 42; }",
        "fnc calculate_other(): infer { return 42; }",
        "fnc calculate_other(): infer -> { return 42; }",
        "fnc infer <- calculate_other() { return 42; }",
        "infer <- calculate_other() { return 42; }",
        "infer <- calculate_other() return 42; end",
        "infer <- calculate_other() begin return 42; end",
        "fnc infer <- calculate_other() begin return 42; end",
    ] {
        let src = format!("{header}\npub fnc main() -> int {{ return calculate_other(); }}");
        let p = Parser::new(lex(&src).unwrap()).parse_program().unwrap();
        assert_eq!(p.funcs[0].ret, Type::Int, "{header}");
        assert!(!compile(&src).unwrap().is_empty(), "{header}");
    }
}

#[test]
fn return_first_inline_methods_obey_normal_class_method_semantics() {
    let src = r#"
        define class Counter as
          int <- calculate(int x) { return x * 2; }
          fnc void <- reset() begin end
          infer <- double(int x) begin return x * 2; end
        end
        pub fnc main() -> int { return 0; }
    "#;
    let p = Parser::new(lex(src).unwrap()).parse_program().unwrap();
    assert_eq!(p.classes[0].methods.len(), 3);
    assert_eq!(p.classes[0].methods[0].ret, Type::Int);
    assert_eq!(p.classes[0].methods[1].ret, Type::Void);
    assert_eq!(p.classes[0].methods[2].ret, Type::Int);
}

#[test]
fn return_first_target_header_scanner_preserves_signature() {
    let src = "fnc int <- calculate(int x) begin return x * 2; end";
    let headers = parse_target_declarations(&lex(src).unwrap()).unwrap();
    assert!(headers.receivers.is_empty());
    let src2 = "int <- calculate(int x) return x * 2; end";
    parse_target_declarations(&lex(src2).unwrap()).unwrap();
}

#[test]
fn invalid_return_first_forms_reject_before_guest_emission() {
    for (decl, code) in [
        ("int < - calculate(int x) { return x; }", "E_TOPLEVEL"),
        ("int <- calculate(int x) -> int { return x; }", "E_RETURN_ANNOTATION"),
    ] {
        let src = format!("{decl}\npub fnc main() -> int {{ return 0; }}");
        let d = compile(&src).unwrap_err();
        assert_eq!(d.code, code, "{decl}: {d}");
    }
}

#[test]
fn return_first_unclosed_begin_requires_matching_end() {
    let d = compile("int <- calculate(int x) begin return x;").unwrap_err();
    assert_eq!(d.code, "E_EOF", "{d}");
}

#[test]
fn return_first_nonvoid_requires_a_return_on_every_path() {
    for decl in [
        "int <- calculate(int x) begin end",
        "int <- calculate(int x) end",
    ] {
        let src = format!("{decl}\npub fnc main() -> int {{ return 0; }}");
        let d = compile(&src).unwrap_err();
        assert_eq!(d.code, "E_RETURN", "{decl}: {d}");
    }
}

#[test]
fn duplicate_spelling_variants_do_not_create_overloads() {
    let src = r#"
        fnc calculate(int x) -> int { return x; }
        int <- calculate(int x) begin return x; end
        pub fnc main() -> int { return 0; }
    "#;
    let d = compile(src).unwrap_err();
    assert_eq!(d.code, "E_DUPLICATE", "{d}");
}

#[test]
fn left_arrow_is_one_contiguous_header_token() {
    let packed = lex("int<-calculate(int x) { return x; }").unwrap();
    assert!(packed.iter().any(|t| t.tok == Tok::LeftArrow));
    let spaced = lex("int < - calculate(int x) { return x; }").unwrap();
    assert!(!spaced.iter().any(|t| t.tok == Tok::LeftArrow));
    assert!(spaced.iter().any(|t| t.tok == Tok::Lt));
    let relational = lex("int <= x").unwrap();
    assert!(relational.iter().any(|t| t.tok == Tok::Le));
}

#[test]
fn explicit_begin_end_preserves_void_and_inferred_void() {
    for declaration in [
        "fnc empty(): void begin end",
        "fnc inferred() -> infer begin end",
        "void <- empty() begin end",
        "infer <- inferred() begin end",
    ] {
        let src = format!("{declaration}\npub fnc main() -> int {{ return 0; }}");
        let p = Parser::new(lex(&src).unwrap()).parse_program().unwrap();
        assert_eq!(p.funcs[0].ret, Type::Void, "{declaration}");
    }
}

#[test]
fn nested_generic_return_first_headers_preserve_complete_declared_type() {
    // The parser must scan over balanced '<...>' before locating '<-';
    // return-first is not restricted to a single-token scalar type.
    let src = r#"
        fnc Option<int> <- optional() { return Some(7); }
        Result<int,string> <- result() begin return Ok(8); end
        Option<Result<int,string>> <- nested() return None; end
        define class C as
          Option<int> <- value() { return Some(9); }
        end
        pub fnc main() -> int { return 0; }
    "#;
    let p = Parser::new(lex(src).unwrap()).parse_program().unwrap();
    assert_eq!(p.funcs[0].ret, Type::OptionInt);
    assert_eq!(p.funcs[1].ret, Type::ResultIntStr);
    assert_eq!(p.funcs[2].ret, Type::OptionResultIntStr);
    assert_eq!(p.classes[0].methods[0].ret, Type::OptionInt);
}

#[test]
fn return_first_out_of_line_class_method_compiles_through_checked_guest_lowering() {
    // Out-of-line mtd must use the same typed class method checker, not a
    // syntax-only shortcut or an unchecked receiver dispatch path.
    for body in [
        "{ return self.value; }",
        "begin return self.value; end",
        "return self.value; end",
    ] {
        let src = format!(r#"
            declare class Counter;
            define class Counter as
              pub let int value = 0;
            end
            pub constructor (Counter)(int initial): self {{
              self.value = initial;
            }}
            pub mtd (Counter self) int <- get_value() {body}
            pub fnc main() -> int {{
              val counter = new Counter(42);
              return counter.get_value();
            }}
        "#);
        let guest = compile(&src).unwrap_or_else(|e|
            panic!("return-first out-of-line class method {body}: {e}"));
        assert_eq!(&guest[..8], &[0, 97, 115, 109, 1, 0, 0, 0]);
    }
}
