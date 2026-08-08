#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path


def replace_once(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected one replacement target, found {count}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def apply(root: Path) -> None:
    source = root / "src/external_subcommands.rs"
    replace_once(
        source,
        '''            if !arguments
                .iter()
                .any(|argument| argument == OsStr::new("--help") || argument == OsStr::new("-h"))
            {
                arguments.push(OsString::from("--help"));
            }
''',
        '''            ensure_help_argument(&mut arguments);
''',
    )
    replace_once(
        source,
        '''fn extract_root_options(args: &[OsString]) -> Option<ParsedExternalArguments> {
''',
        '''fn ensure_help_argument(arguments: &mut Vec<OsString>) {
    if arguments
        .iter()
        .any(|argument| argument == OsStr::new("--help") || argument == OsStr::new("-h"))
    {
        return;
    }
    let insertion = arguments
        .iter()
        .position(|argument| argument == OsStr::new("--"))
        .unwrap_or(arguments.len());
    arguments.insert(insertion, OsString::from("--help"));
}

fn extract_root_options(args: &[OsString]) -> Option<ParsedExternalArguments> {
''',
    )
    replace_once(
        source,
        '''    #[test]
    fn builtins_and_unsafe_names_are_never_external() {
''',
        '''    #[test]
    fn external_help_is_inserted_before_literal_double_dash() {
        let route = external_route(&os_args(&[
            "zed",
            "help",
            "gitops",
            "validate",
            "--",
            "--root",
            "child-owned",
        ]))
        .expect("external help route");
        assert_eq!(
            route.arguments,
            os_args(&["validate", "--help", "--", "--root", "child-owned"])
        );
    }

    #[test]
    fn builtins_and_unsafe_names_are_never_external() {
''',
    )

    integration = root / "tests/external_gitops_dispatch.rs"
    replace_once(
        integration,
        '''#[test]
fn root_help_alias_reaches_the_external_binary() {
''',
        '''#[test]
fn root_help_alias_keeps_help_before_literal_double_dash() {
    let output = Command::new(env!("CARGO_BIN_EXE_zed"))
        .args([
            "help",
            "gitops",
            "validate",
            "--",
            "--root",
            "child-owned",
        ])
        .output()
        .expect("run zed help gitops with literal delimiter");
    assert!(output.status.success(), "{}", text(&output));
    let text = text(&output);
    assert!(text.contains(&gitops_usage(" validate")), "{text}");
    assert!(text.contains("--offline"), "{text}");
}

#[test]
fn root_help_alias_reaches_the_external_binary() {
''',
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve(strict=True)
    apply(root)
    print(f"applied DEN-2725 help-delimiter fix under {root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
