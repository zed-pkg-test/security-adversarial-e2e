# Independent source-render reproduction

This lane reproduces the final DEN-2724 source-byte evidence from a second `zed-pkg-test` repository. It consumes the exact immutable test package rather than copying or reimplementing its fixture logic.

## Exact inputs

```text
zed-pkg-test/zed-pkg-e2e@153d65ad2b3cf5fc139efb0dbdf29fa816ce55d2
ORESoftware/k8s-cluster@0c71eed05f8be50ac22ebe73715ded4a871234a8
daedalus-fab/fabrication-server.rs@cea4a3c772012e1f2f87050bac24e911b8e2e577
```

The test-package commit contains:

- a seven-file private-source snapshot whose Git blob IDs match the owner source commit;
- the exact owner-repo endpoint/NetworkPolicy regression and its unit tests;
- an independent endpoint-policy implementation;
- the checksum-pinned Kustomize installer; and
- the catalog/source/render verifier.

## Matrix

Ubuntu 24.04, macOS 15, and Windows Server 2025 each:

1. verify the immutable test-package and cluster identities;
2. execute the exact owner-repo regression files from the source snapshot;
3. execute the independent test-org endpoint-policy tests;
4. verify NATS 4222 and OTLP HTTP 4318 are permitted by the snapshot NetworkPolicy;
5. download and verify the official Kustomize v5.8.1 platform asset;
6. validate `.gitmodules`, the indexed gitlink, catalog inventory/source, and snapshot revision/repository parity;
7. render twice and require byte-identical namespace-scoped output;
8. reject cluster-scoped resources and plaintext Kubernetes Secrets; and
9. prove the security harness, immutable test package, and cluster checkout remain pristine.

## Isolation

All checkouts disable persisted credentials. This workflow uses no user PAT, private-repository token, registry credential, Kubernetes credential, Cloudflare token, DNS permission, R2 key, or database access. It never performs an apply, push, publication, deployment, or reconciliation operation.

The source snapshot does not claim live private-repository reachability. That remains a separate owner-scoped GitHub App contract.

## Coordination

- Primary test package: `zed-pkg-test/zed-pkg-e2e#155`
- Owner source repair: `daedalus-fab/fabrication-server.rs#11`
- Stacked cluster pin: `ORESoftware/k8s-cluster#1211`
- Baseline catalog/trigger repair: `ORESoftware/k8s-cluster#1209`
- Current-main adversarial matrix: `zed-pkg-test/security-adversarial-e2e#6`
- Linear: `DEN-2724`, `DEN-2725`, `DEN-630`
