#!/usr/bin/env bash
set -euo pipefail

SCANNER_DIR="${SCANNER_DIR:?SCANNER_DIR is required}"
WORK_ROOT="${WORK_ROOT:?WORK_ROOT is required}"

scan_row() {
  local repo_dir="$1"
  bash "$SCANNER_DIR/scripts/fleet-audit.sh" "$repo_dir" | tail -n 1
}

field() {
  local row="$1" index="$2"
  printf '%s\n' "$row" | awk -F '\t' -v n="$index" '{print $n}'
}

assert_no_plaintext_conflict() {
  local label="$1" repo_dir="$2"
  local row status plaintext
  row="$(scan_row "$repo_dir")"
  status="$(field "$row" 2)"
  plaintext="$(field "$row" 3)"

  printf '%s\t%s\n' "$label" "$row"

  if [[ "$plaintext" != "0" ]]; then
    printf '%s unexpectedly tracks %s plaintext dotenv path(s)\n' "$label" "$plaintext" >&2
    return 1
  fi
  if [[ "$status" == "conflicting" ]]; then
    printf '%s is still conflicting after the fixture migration\n' "$label" >&2
    return 1
  fi
}

assert_expected_conflict() {
  local label="$1" repo_dir="$2" minimum_plaintext="$3"
  local row status plaintext
  row="$(scan_row "$repo_dir")"
  status="$(field "$row" 2)"
  plaintext="$(field "$row" 3)"

  printf '%s\t%s\n' "$label" "$row"

  if [[ "$status" != "conflicting" ]]; then
    printf '%s should remain conflicting until its tracked dotenv fixtures are reconciled\n' "$label" >&2
    return 1
  fi
  if (( plaintext < minimum_plaintext )); then
    printf '%s expected at least %s tracked plaintext dotenv paths; got %s\n' \
      "$label" "$minimum_plaintext" "$plaintext" >&2
    return 1
  fi
}

printf 'lane\trepository\tstatus\ttracked_plaintext\tunexpected_env_enc\ttracked_symlinks\tsops_rules\tignore_contract\tciphertext_attributes\n'
assert_no_plaintext_conflict \
  'flags-2-env-fixed' \
  "$WORK_ROOT/flags-2-env-fixed"
assert_no_plaintext_conflict \
  'devops-slack-main' \
  "$WORK_ROOT/devops-slack-main"
assert_expected_conflict \
  'flags-2-env-pr27-pre-reconcile' \
  "$WORK_ROOT/flags-2-env-pr27" \
  3
