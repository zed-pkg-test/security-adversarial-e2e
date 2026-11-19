//! Class-field implicit let regression: this is parser/compiler-subset
//! evidence, NOT proof of mutable receiver, val mut, const evaluation or AOT parity.
use atto_compiler::{compile, lexer::lex, parser::Parser};
use atto_compiler::ast::{FieldBinding, FieldMode};

#[test]
fn bare_class_fields_are_let_for_scalar_string_and_class_types() {
    let source = r#"
        define class Leaf as
          pub int amount = 5;
        end
        define class Holder as
          pub int count = 1;
          pub let int explicit_count = 2;
          pub string name = "example";
          pub Leaf child = new Leaf();
          pub val int stable = 3;
          pub final int fixed = 4;
          pub const int limit = 5;
        end
        pub fnc main(): int { return 0; }
    "#;
    let parsed = Parser::new(lex(source).unwrap()).parse_program().unwrap();
    let holder = parsed.classes.iter().find(|c| c.name == "Holder").unwrap();
    for field_name in ["count", "name", "child"] {
        let field = holder.fields.iter().find(|f| f.name == field_name).unwrap();
        assert_eq!(field.mode, FieldMode::Constructor,
            "implicit class-field mode must be independent of primitive or object type: {field_name}");
        assert_eq!(field.binding, FieldBinding::Let, "{field_name} must be let");
        assert!(!field.referent_mutable, "{field_name} must not imply mut");
    }
    let explicit_let = holder.fields.iter().find(|f| f.name == "explicit_count").unwrap();
    assert_eq!(explicit_let.mode, FieldMode::Constructor);
    assert_eq!(explicit_let.binding, FieldBinding::Let);
    for field_name in ["stable", "fixed", "limit"] {
        let field = holder.fields.iter().find(|f| f.name == field_name).unwrap();
        assert_eq!(field.mode, FieldMode::Final,
            "existing storage mode treats val/final/const as immutable: {field_name}");
        let expected = match field_name {
            "stable" => FieldBinding::Val,
            "fixed" => FieldBinding::Final,
            "limit" => FieldBinding::Const,
            _ => unreachable!(),
        };
        assert_eq!(field.binding, expected, "source modifier must survive parsing");
    }
}

#[test]
fn implicit_and_explicit_let_both_compile_into_guest_wasm() {
    let source = r#"
        define class Counter as
          pub int count = 9;
        end
        pub fnc main(): int {
          val Counter value = new Counter();
          return value.count;
        }
    "#;
    for src in [source.to_owned(), source.replace("pub int count = 9;", "pub let int count = 9;")] {
        let parsed = Parser::new(lex(&src).unwrap()).parse_program().unwrap();
        assert_eq!(parsed.classes[0].fields[0].mode, FieldMode::Constructor);
        let guest = compile(&src).unwrap();
        assert_eq!(&guest[..8], &[0, 97, 115, 109, 1, 0, 0, 0]);
    }
}

#[test]
fn class_val_and_final_fields_cannot_be_reassigned_from_constructor() {
    for modifier in ["val", "final"] {
        let source = format!(r#"
            define class Stable as
              pub {modifier} int id = 1;
              constructor() {{ self.id = 3; }}
            end
            pub fnc main(): int {{ return 0; }}
        "#);
        let diagnostic = compile(&source).unwrap_err();
        assert_eq!(diagnostic.code, "E_IMMUTABLE", "{source}: {diagnostic}");
    }
}

#[test]
fn let_default_does_not_grant_mutable_readonly_receiver() {
    let source = r#"
        define class Counter as
          pub int count = 1;
          change(): int { self.count = 2; return self.count; }
        end
        pub fnc main(): int { return 0; }
    "#;
    let diagnostic = compile(source).unwrap_err();
    assert_eq!(diagnostic.code, "E_OWNERSHIP", "{diagnostic}");
}

#[test]
fn val_mut_and_let_mut_retain_separate_binding_and_referent_flags() {
    let src = r#"
        define class Cell as
          pub val mut int anchored = 7;
          pub let mut int replaceable = 8;
          pub mut int short_let = 9;
          pub int default_let = 10;
          pub const int fixed = 11;
        end
        pub fnc main(): int { return 0; }
    "#;
    let p = Parser::new(lex(src).unwrap()).parse_program().unwrap();
    let f = &p.classes[0].fields;
    assert_eq!(f.len(), 5);
    assert_eq!((f[0].binding, f[0].referent_mutable), (FieldBinding::Val, true));
    assert_eq!((f[1].binding, f[1].referent_mutable), (FieldBinding::Let, true));
    assert_eq!((f[2].binding, f[2].referent_mutable), (FieldBinding::Let, true));
    assert_eq!((f[3].binding, f[3].referent_mutable), (FieldBinding::Let, false));
    assert_eq!((f[4].binding, f[4].referent_mutable), (FieldBinding::Const, false));
}

#[test]
fn class_const_rejects_runtime_initializer_with_distinct_diagnostic() {
    let src = r#"
        fnc runtime_number(): int { return 5; }
        define class Invalid as
          pub const int limit = runtime_number();
        end
        pub fnc main(): int { return 0; }
    "#;
    let d = compile(src).unwrap_err();
    assert_eq!(d.code, "E_CONST", "{d}");
}

#[test]
fn val_mut_binding_cannot_be_reassigned_in_constructor() {
    let src = r#"
        define class Cell as
          pub val mut int anchored = 7;
          constructor() { self.anchored = 8; }
        end
        pub fnc main(): int { return 0; }
    "#;
    let d = compile(src).unwrap_err();
    assert_eq!(d.code, "E_IMMUTABLE", "{d}");
}

#[test]
fn bare_let_and_explicit_let_both_admit_constructor_assignment() {
    let source = r#"
        define class Counter as
            pub int count = 1;
            constructor() { self.count = 3; }
        end
        pub fnc main(): int { return 0; }
    "#;
    // These are exactly equivalent class bindings, not an accidental
    // mutable-receiver exemption. Constructor authority remains checked.
    for src in [source.to_owned(),
        source.replace("pub int count = 1;", "pub let int count = 1;")] {
        let guest = compile(&src).expect("constructor may assign let field");
        assert_eq!(&guest[..8], b"\0asm\x01\0\0\0");
    }
    // Explicit val retains immutable binding semantics.
    let fixed = source.replace("pub int count = 1;", "pub val int count = 1;");
    let d = compile(&fixed).unwrap_err();
    assert_eq!(d.code, "E_IMMUTABLE", "{d}");
}
