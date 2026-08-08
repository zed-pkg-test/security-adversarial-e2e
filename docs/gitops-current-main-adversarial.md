# Current-main GitOps adversarial certification

This test-org lane verifies that the merged DEN-2724/DEN-2725 contract remains intact after later product and cluster changes. It is intentionally different from the original exact-parent feature canary: it certifies the current merged heads and mutates disposable worktrees to prove fail-closed behavior.

## Immutable inputs

Default pins:

```text
zed-pkg/zed-cli@5d1d13119be5784f545a7d812cdfaae3ca120693
ORESoftware/k8s-cluster@18f1fa1dc8360c4817e1adbc1351b93f7d8604de
```

The workflow runs on Ubuntu 24.04, macOS 15, and Windows Server 2025.

## Positive regression boundary

Each platform:

1. verifies both immutable checkout identities;
2. runs rustfmt, focused dispatcher and validator tests, strict Clippy, package-graph validation, and the native `k8s-cluster` validator suite;
3. builds exact release `zed` and `zed-gitops` siblings;
4. validates the real current `k8s-cluster` catalog through standalone `zed-gitops`, root-dispatched `zed gitops`, and the native Python validator;
5. requires root/direct Zed report identity and native/Zed record-count agreement;
6. renders the native deterministic preview and requires one rendered item per validated record; and
7. requires the ApplicationSet pilot to retain its inert annotation, fail-closed template settings, exact child revision source, collision-free generated name, and zero references from other Argo YAML/JSON.

## Disposable adversarial scenarios

For each policy mutation, the harness creates a detached worktree at the exact cluster commit. The original checkout remains untouched. Both Zed entry points and the native validator must exit with policy status 2 and report the required rule:

- source target revision differs from the inventory pin — `source.pin-drift`;
- catalog inventory/source pins differ from the indexed gitlink — `inventory.gitlink-drift`;
- broad default AppProject and namespace — `argo.project`, `argo.namespace`;
- automated sync, prune, or self-heal enabled while `pilot-inert` — `migration.inert-sync`;
- an `*-infra` repository classified as a deployable app — `policy.infra-is-not-app`;
- parent-owned static Application path escapes the repository — `migration.static-application`; and
- no catalog records — `catalog.empty`.

Unix runners additionally replace the catalog directory with an escaping symlink. The Zed validator must fail as a tool/configuration error before reading the external records.

## Evidence and isolation

Each runner uploads a JSON record under:

```text
zed-pkg-test/gitops-current-main-adversarial/v1
```

The evidence contains only immutable commits, platform identity, report/preview digests, scenario names, expected rules, and passed check names.

The workflow uses public exact-commit checkouts with persisted credentials disabled. Product subprocesses receive no inherited token, secret, password, private key, access key, API key, authorization, cookie, or Zed credential variables. It performs no private submodule read, publication, registry write, Kubernetes mutation, Argo reconciliation, Cloudflare request, DNS change, R2 access, database write, or persistent namespace operation.

Passing this lane does not authorize activation of the inert ApplicationSet. Activation still requires a separate production change with resource-ownership parity, prune/deletion behavior, and rollback evidence.

## Coordination

- Root dispatcher merge: `zed-pkg/zed-cli#242`
- Exact-parent canary: `zed-pkg-test/zed-pkg-e2e#134`
- Cluster contract merge: `ORESoftware/k8s-cluster#1109`
- Roadmap: `ORESoftware/k8s-cluster#1097`
- Linear: `DEN-2724`, `DEN-2725`, `DEN-630`
