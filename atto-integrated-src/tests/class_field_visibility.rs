//! Class-field visibility: no accidental widening of scoped/package fields.
//! This backend accepts a single source package, not cross-package linking.
use atto_compiler::{ast::{FieldBinding, FieldMode, FieldVisibility}, compile, lexer::lex, parser::Parser};

fn compiled(source: &str) {
    let wasm = compile(source).unwrap_or_else(|e| panic!("expected valid guest: {e}"));
    assert_eq!(&wasm[..8], b"\0asm\x01\0\0\0");
    assert_eq!(wasm, compile(source).unwrap(), "Wasm must be deterministic");
}
fn rejected(source: &str, code: &str) {
    let e = compile(source).expect_err("invalid visibility must not emit guest Wasm");
    assert_eq!(e.code, code, "{e}");
    assert!(e.pos.line > 0 && e.pos.col > 0);
}
#[test]
fn parsed_fields_keep_private_package_and_public_distinct() {
    let src = r#"
        define class Vault as
            private int secret: 40;
            pub[pkg] val int package_id = 1;
            pub int exported: 2;
            int implicit_private: 3;
            pub read_secret(): int { return self.secret; }
        end
        pub fnc main(): int { return 0; }
    "#;
    let mut parser = Parser::new(lex(src).unwrap());
    let program = parser.parse_program().unwrap();
    let fields = &program.classes[0].fields;
    assert_eq!(fields.len(), 4);
    assert_eq!(fields[0].visibility, FieldVisibility::Private);
    assert_eq!(fields[1].visibility, FieldVisibility::Package);
    assert_eq!(fields[2].visibility, FieldVisibility::Public);
    assert_eq!(fields[3].visibility, FieldVisibility::Private);
    compiled(src);
}
#[test]
fn package_field_is_accessible_within_single_source_package() {
    compiled(r#"
        define class Vault as
            private int secret: 40;
            pub[pkg] val int package_id = 1;
            pub int exported: 2;
            pub read_secret(): int { return self.secret; }
        end
        pub fnc main(): int {
            val v = new Vault();
            return v.package_id + v.exported + v.read_secret();
        }
    "#);
}
#[test]
fn explicit_and_implicit_private_fields_reject_external_access() {
    for declaration in ["private int secret: 41;", "int secret: 41;"] {
        let src = format!(r#"
            define class Vault as {declaration} end
            pub fnc main(): int {{ return new Vault().secret; }}
        "#);
        rejected(&src, "E_PRIVATE");
    }
}
#[test]
fn field_visibility_works_with_existing_binding_qualifiers() {
    compiled(r#"
        define class Vault as
            pub[pkg] let int counter = 1;
            private val int hidden = 4;
            pub[pkg] final int epoch = 5;
            pub[pkg] const int scale = 2;
            pub total(): int { return self.counter + self.hidden + self.epoch + self.scale; }
        end
        pub fnc main(): int { return new Vault().total(); }
    "#);
}
#[test]
fn inheritance_alias_keeps_package_visibility_without_public_widening() {
    let src = r#"
        define class Base as pub[pkg] int age: 5; end
        define class Child extends Base as use Base.age as child_age; end
        pub fnc main(): int { return new Child().child_age; }
    "#;
    compiled(src);
    let tokens = atto_compiler::nominal_lower::lower(lex(src).unwrap()).unwrap();
    assert!(tokens.windows(4).any(|t|
        matches!(&t[0].tok, atto_compiler::lexer::Tok::Ident(v) if v == "pub")
        && matches!(&t[1].tok, atto_compiler::lexer::Tok::LBracket)
        && matches!(&t[2].tok, atto_compiler::lexer::Tok::Ident(v) if v == "pkg")
        && matches!(&t[3].tok, atto_compiler::lexer::Tok::RBracket)));
}
#[test]
fn malformed_scopes_and_unsupported_member_kinds_fail_closed() {
    for src in [
        "define class C as pub[other] int x: 1; end",
        "define class C as pub[pkg int x: 1; end",
        "define class C as private[pkg] int x: 1; end",
    ] {
        rejected(src, "E_SYNTAX");
    }
    rejected("define class C as pub[pkg] read(): int { return 1; } end", "E_UNSUPPORTED");
    rejected("define actor A as pub[pkg] let int x = 1; end", "E_UNSUPPORTED");
}

#[test]
fn implicit_type_first_fields_are_let_and_explicit_val_remains_immutable() {
    let src = r#"
        define class Box as
            int implicit_equals = 1;
            int implicit_colon: 2;
            val int explicit_val = 3;
            let int mutable_slot = 4;
            final int final_slot = 5;
        end
        pub fnc main(): int { return 0; }
    "#;
    let mut parser = Parser::new(lex(src).unwrap());
    let program = parser.parse_program().unwrap();
    let fields = &program.classes[0].fields;
    assert_eq!(fields.len(), 5);
    for field in &fields[..2] {
        assert_eq!(field.mode, FieldMode::Constructor);
        assert_eq!(field.binding, FieldBinding::Let);
        assert!(!field.referent_mutable);
    }
    assert_eq!(fields[2].mode, FieldMode::Final);
    assert_eq!(fields[2].binding, FieldBinding::Val);
    assert_eq!(fields[3].mode, FieldMode::Constructor);
    assert_eq!(fields[4].mode, FieldMode::Final);
    compiled(src);
}
#[test]
fn implicit_let_and_explicit_let_admit_constructor_assignment_but_val_rejects() {
    let source = r#"
        define class Box as
            pub int count = 1;
            constructor() { self.count = 2; }
        end
        pub fnc main(): int { return new Box().count; }
    "#;
    compiled(source);
    compiled(&source.replace("pub int count = 1;", "pub let int count = 1;"));
    rejected(&source.replace("pub int count = 1;", "pub val int count = 1;"),
        "E_IMMUTABLE");
}
#[test]
fn unsupported_scopes_never_become_public_fields() {
    for scope in ["pub(pkg)", "pub[other]", "pub[PKG]"] {
        let src = format!("define class C as {scope} int x = 1; end pub fnc main(): int {{ return 0; }}");
        assert!(compile(&src).is_err(), "{scope} must fail closed");
    }
}
