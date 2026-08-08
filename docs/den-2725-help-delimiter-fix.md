# DEN-2725 external-help delimiter correction

This security test-org lane verifies one semantic edge found during review of `zed-pkg/zed-cli#233` at the exact commit:

```text
1c94813c6b59c7621c1256d7c55246e7f06f44b7
```

## Finding

The external `help <command>` route synthesized `--help` by appending it to child arguments. When a literal `--` was already present, the synthesized flag landed after the delimiter and became child-owned data rather than a help flag.

The intended contract is:

```text
zed help gitops validate -- --root child-owned
```

routes as:

```text
zed-gitops validate --help -- --root child-owned
```

The ordinary direct-dispatch contract remains unchanged: a literal `--` still terminates extraction of Zed root options and preserves every following child argument.

## Read-only patch verification

The workflow checks out the exact public product commit with persisted credentials disabled, applies only two product-file changes in a disposable checkout, and requires the changed-file set to be exactly:

```text
src/external_subcommands.rs
tests/external_gitops_dispatch.rs
```

It then runs rustfmt, focused unit tests, the compiled external-dispatch integration suite, and strict Clippy. On success it uploads the two corrected files, a binary-safe Git patch, and SHA-256 sums. The product branch is not mutated by the workflow.

## Isolation

The workflow has read-only repository permission. It uses commit-pinned Actions and no PAT, GitHub App private key, registry credential, Kubernetes credential, Cloudflare token, DNS permission, or R2 key. It performs no network write and no deployment mutation.

## Coordination

- Product PR: `zed-pkg/zed-cli#233`
- Three-platform full dispatch canary: `zed-pkg-test/zed-pkg-e2e#118`
- Real merged cluster-contract canary: `zed-pkg-test/zed-pkg-e2e#121`
- Linear: `DEN-2725`

Once the artifact is green, the exact verified files can be committed to #233 and all exact-SHA test-org lanes can be repinned to the corrected product head.