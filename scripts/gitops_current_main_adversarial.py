#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from contextlib import contextmanager
from pathlib import Path
from typing import Callable, Iterable, Iterator, Sequence


SENSITIVE_ENV_FRAGMENTS = (
    "TOKEN",
    "SECRET",
    "PASSWORD",
    "PRIVATE_KEY",
    "ACCESS_KEY",
    "API_KEY",
    "AUTHORIZATION",
    "COOKIE",
)


class CertificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificationError(message)


def sanitized_environment() -> dict[str, str]:
    environment = dict(os.environ)
    for key in list(environment):
        upper = key.upper()
        if any(fragment in upper for fragment in SENSITIVE_ENV_FRAGMENTS):
            environment.pop(key, None)
        elif upper.startswith(("ZED_PKG_", "ZED_EXTERNAL_", "ZED_PROBE_")):
            environment.pop(key, None)
    environment["CI"] = "true"
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    return environment


def run(
    command: Sequence[object],
    *,
    environment: dict[str, str],
    cwd: Path | None = None,
    expected: int | Iterable[int] = 0,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    expected_codes = {expected} if isinstance(expected, int) else set(expected)
    result = subprocess.run(
        [str(item) for item in command],
        cwd=cwd,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    if result.returncode not in expected_codes:
        rendered = " ".join(repr(str(item)) for item in command)
        raise CertificationError(
            f"command returned {result.returncode}, expected {sorted(expected_codes)}: {rendered}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def parse_json(result: subprocess.CompletedProcess[str], label: str) -> dict[str, object]:
    try:
        value = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise CertificationError(
            f"{label} did not emit JSON: {error}\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        ) from error
    require(isinstance(value, dict), f"{label} must emit one JSON object")
    return value


def rule_ids(report: dict[str, object]) -> set[str]:
    diagnostics = report.get("diagnostics", [])
    require(isinstance(diagnostics, list), "diagnostics must be a list")
    return {
        str(item.get("rule_id"))
        for item in diagnostics
        if isinstance(item, dict) and item.get("rule_id") is not None
    }


def canonical_digest(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def git_head(root: Path, environment: dict[str, str]) -> str:
    return run(
        ["git", "-C", root, "rev-parse", "HEAD"], environment=environment
    ).stdout.strip()


def validator_command(binary: Path, root: Path, *, through_root: bool) -> list[object]:
    prefix: list[object] = [binary]
    if through_root:
        prefix.extend(["gitops"])
    return [
        *prefix,
        "validate",
        "--root",
        root,
        "--offline",
        "--strict",
        "--format",
        "json",
    ]


def run_zed_pair(
    *,
    zed: Path,
    zed_gitops: Path,
    root: Path,
    environment: dict[str, str],
    expected: int | Iterable[int],
) -> tuple[subprocess.CompletedProcess[str], subprocess.CompletedProcess[str]]:
    direct = run(
        validator_command(zed_gitops, root, through_root=False),
        environment=environment,
        expected=expected,
    )
    routed = run(
        validator_command(zed, root, through_root=True),
        environment=environment,
        expected=expected,
    )
    require(direct.returncode == routed.returncode, "root and direct exit codes differ")
    require(direct.stdout == routed.stdout, "root and direct JSON reports differ")
    require(direct.stderr == routed.stderr, "root and direct stderr differs")
    return direct, routed


def native_check(
    root: Path,
    *,
    environment: dict[str, str],
    expected: int | Iterable[int],
) -> subprocess.CompletedProcess[str]:
    return run(
        [
            sys.executable,
            root / "tools/gitops_composition.py",
            "check",
            "--root",
            root,
            "--format",
            "json",
        ],
        environment=environment,
        expected=expected,
    )


def native_render(root: Path, *, environment: dict[str, str]) -> dict[str, object]:
    result = run(
        [
            sys.executable,
            root / "tools/gitops_composition.py",
            "render",
            "--root",
            root,
        ],
        environment=environment,
    )
    return parse_json(result, "native renderer")


def catalog_record(root: Path) -> Path:
    return root / "catalog/gitops/apps/dd-fabrication-server.json"


def update_record(root: Path, mutation: Callable[[dict[str, object]], None]) -> None:
    path = catalog_record(root)
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), "catalog record must be a JSON object")
    mutation(value)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@contextmanager
def detached_worktree(
    source: Path,
    destination: Path,
    commit: str,
    *,
    environment: dict[str, str],
) -> Iterator[Path]:
    if destination.exists():
        shutil.rmtree(destination)
    run(
        ["git", "-C", source, "worktree", "add", "--detach", destination, commit],
        environment=environment,
    )
    try:
        yield destination
    finally:
        run(
            ["git", "-C", source, "worktree", "remove", "--force", destination],
            environment=environment,
            expected={0},
        )


def verify_pilot_is_inert(cluster: Path) -> list[str]:
    relative = Path(
        "remote/argocd/application-sets/"
        "gitops-composition-catalog-pilot.applicationset.yaml"
    )
    pilot = cluster / relative
    require(pilot.is_file(), f"missing inert ApplicationSet pilot: {relative}")
    text = pilot.read_text(encoding="utf-8")
    for fragment in (
        "name: gitops-composition-catalog-pilot",
        "oresoftware.dev/activation: inert-not-in-bootstrap",
        "missingkey=error",
        "path: catalog/gitops/apps/*.json",
        "targetRevision: '{{ .spec.source.targetRevision }}'",
        "name: 'catalog-pilot-{{ .metadata.name }}'",
    ):
        require(fragment in text, f"ApplicationSet pilot omitted {fragment!r}")

    references: list[str] = []
    argo_root = cluster / "remote/argocd"
    for path in argo_root.rglob("*"):
        if not path.is_file() or path == pilot:
            continue
        if path.suffix.lower() not in {".yaml", ".yml", ".json"}:
            continue
        candidate = path.read_text(encoding="utf-8", errors="replace")
        if "gitops-composition-catalog-pilot" in candidate or relative.name in candidate:
            references.append(path.relative_to(cluster).as_posix())
    require(not references, f"pilot is referenced by live Argo material: {references}")
    return references


def policy_scenario(
    *,
    name: str,
    mutation: Callable[[dict[str, object]], None],
    expected_rules: set[str],
    cluster: Path,
    cluster_commit: str,
    work: Path,
    zed: Path,
    zed_gitops: Path,
    environment: dict[str, str],
) -> dict[str, object]:
    scenario_root = work / name
    with detached_worktree(
        cluster, scenario_root, cluster_commit, environment=environment
    ) as root:
        update_record(root, mutation)
        direct, _ = run_zed_pair(
            zed=zed,
            zed_gitops=zed_gitops,
            root=root,
            environment=environment,
            expected=2,
        )
        native = native_check(root, environment=environment, expected=2)
        direct_report = parse_json(direct, f"{name} zed report")
        native_report = parse_json(native, f"{name} native report")
        zed_rules = rule_ids(direct_report)
        native_rules = rule_ids(native_report)
        require(
            expected_rules <= zed_rules,
            f"{name}: zed omitted rules {sorted(expected_rules - zed_rules)}",
        )
        require(
            expected_rules <= native_rules,
            f"{name}: native validator omitted rules {sorted(expected_rules - native_rules)}",
        )
        return {
            "name": name,
            "expectedRules": sorted(expected_rules),
            "zedRuleCount": len(zed_rules),
            "nativeRuleCount": len(native_rules),
            "zedReportSha256": canonical_digest(direct_report),
            "nativeReportSha256": canonical_digest(native_report),
        }


def certify(args: argparse.Namespace) -> dict[str, object]:
    environment = sanitized_environment()
    zed = args.zed.resolve(strict=True)
    zed_gitops = args.zed_gitops.resolve(strict=True)
    product = args.product.resolve(strict=True)
    cluster = args.cluster.resolve(strict=True)
    work = args.work.resolve()
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    require(git_head(product, environment) == args.product_commit, "product SHA drift")
    require(git_head(cluster, environment) == args.cluster_commit, "cluster SHA drift")

    checks: list[str] = ["immutable-checkouts-match"]

    direct, _ = run_zed_pair(
        zed=zed,
        zed_gitops=zed_gitops,
        root=cluster,
        environment=environment,
        expected=0,
    )
    zed_report = parse_json(direct, "current-main zed report")
    native_result = native_check(cluster, environment=environment, expected=0)
    native_report = parse_json(native_result, "current-dev native report")
    require(zed_report.get("valid") is True, f"zed baseline invalid: {zed_report}")
    require(native_report.get("valid") is True, f"native baseline invalid: {native_report}")
    require(zed_report.get("errors") == 0, f"zed baseline errors: {zed_report}")
    require(native_report.get("errors") == 0, f"native baseline errors: {native_report}")
    require(
        zed_report.get("records") == native_report.get("records"),
        "native and Zed record counts differ",
    )
    checks.extend(
        [
            "current-main-root-and-direct-reports-match",
            "current-dev-native-and-zed-record-counts-match",
        ]
    )

    preview = native_render(cluster, environment=environment)
    items = preview.get("items")
    require(isinstance(items, list), "preview items must be a list")
    require(
        len(items) == zed_report.get("records"),
        "preview count does not match validated record count",
    )
    checks.append("current-dev-preview-is-complete")

    verify_pilot_is_inert(cluster)
    checks.append("applicationset-pilot-remains-inert-and-unreferenced")

    scenarios = [
        policy_scenario(
            name="source-pin-drift",
            mutation=lambda record: record["spec"]["source"].__setitem__(
                "targetRevision", "a" * 40
            ),
            expected_rules={"source.pin-drift"},
            cluster=cluster,
            cluster_commit=args.cluster_commit,
            work=work,
            zed=zed,
            zed_gitops=zed_gitops,
            environment=environment,
        ),
        policy_scenario(
            name="gitlink-inventory-drift",
            mutation=lambda record: (
                record["spec"]["inventory"].__setitem__("revision", "b" * 40),
                record["spec"]["source"].__setitem__("targetRevision", "b" * 40),
            ),
            expected_rules={"inventory.gitlink-drift"},
            cluster=cluster,
            cluster_commit=args.cluster_commit,
            work=work,
            zed=zed,
            zed_gitops=zed_gitops,
            environment=environment,
        ),
        policy_scenario(
            name="default-argo-boundary",
            mutation=lambda record: (
                record["spec"]["argo"].__setitem__("project", "default"),
                record["spec"]["argo"].__setitem__("namespace", "default"),
            ),
            expected_rules={"argo.project", "argo.namespace"},
            cluster=cluster,
            cluster_commit=args.cluster_commit,
            work=work,
            zed=zed,
            zed_gitops=zed_gitops,
            environment=environment,
        ),
        policy_scenario(
            name="inert-sync-enabled",
            mutation=lambda record: (
                record["spec"]["argo"].__setitem__("automated", True),
                record["spec"]["argo"].__setitem__("prune", True),
                record["spec"]["argo"].__setitem__("selfHeal", True),
            ),
            expected_rules={"migration.inert-sync"},
            cluster=cluster,
            cluster_commit=args.cluster_commit,
            work=work,
            zed=zed,
            zed_gitops=zed_gitops,
            environment=environment,
        ),
        policy_scenario(
            name="infra-classified-as-app",
            mutation=lambda record: (
                record["spec"]["inventory"].__setitem__(
                    "repository",
                    "git@github.com:daedalus-fab/fabrication-server-infra.git",
                ),
                record["spec"]["source"].__setitem__(
                    "repository",
                    "git@github.com:daedalus-fab/fabrication-server-infra.git",
                ),
            ),
            expected_rules={"policy.infra-is-not-app"},
            cluster=cluster,
            cluster_commit=args.cluster_commit,
            work=work,
            zed=zed,
            zed_gitops=zed_gitops,
            environment=environment,
        ),
        policy_scenario(
            name="unsafe-static-application-path",
            mutation=lambda record: record["spec"]["migration"].__setitem__(
                "staticApplication", "../outside.yaml"
            ),
            expected_rules={"migration.static-application"},
            cluster=cluster,
            cluster_commit=args.cluster_commit,
            work=work,
            zed=zed,
            zed_gitops=zed_gitops,
            environment=environment,
        ),
    ]
    checks.extend(f"rejects-{scenario['name']}" for scenario in scenarios)

    empty_root = work / "empty-catalog"
    with detached_worktree(
        cluster, empty_root, args.cluster_commit, environment=environment
    ) as root:
        catalog_record(root).unlink()
        direct_empty, _ = run_zed_pair(
            zed=zed,
            zed_gitops=zed_gitops,
            root=root,
            environment=environment,
            expected=2,
        )
        native_empty = native_check(root, environment=environment, expected=2)
        zed_empty_report = parse_json(direct_empty, "empty-catalog zed report")
        native_empty_report = parse_json(native_empty, "empty-catalog native report")
        require("catalog.empty" in rule_ids(zed_empty_report), "zed allowed empty catalog")
        require(
            "catalog.empty" in rule_ids(native_empty_report),
            "native validator allowed empty catalog",
        )
        scenarios.append(
            {
                "name": "empty-catalog",
                "expectedRules": ["catalog.empty"],
                "zedReportSha256": canonical_digest(zed_empty_report),
                "nativeReportSha256": canonical_digest(native_empty_report),
            }
        )
    checks.append("rejects-empty-catalog")

    if os.name != "nt":
        symlink_root = work / "catalog-symlink-escape"
        outside = work / "outside-catalog"
        outside.mkdir(parents=True)
        with detached_worktree(
            cluster, symlink_root, args.cluster_commit, environment=environment
        ) as root:
            source_catalog = root / "catalog/gitops/apps"
            shutil.copy2(catalog_record(root), outside / catalog_record(root).name)
            shutil.rmtree(source_catalog)
            source_catalog.symlink_to(outside, target_is_directory=True)
            direct_escape, _ = run_zed_pair(
                zed=zed,
                zed_gitops=zed_gitops,
                root=root,
                environment=environment,
                expected=1,
            )
            combined = f"{direct_escape.stdout}\n{direct_escape.stderr}"
            require(
                "must be a real directory inside the superproject" in combined
                or "escapes the superproject root" in combined,
                f"unexpected symlink-escape diagnostic: {combined}",
            )
            scenarios.append(
                {
                    "name": "catalog-symlink-escape",
                    "expectedExit": 1,
                    "diagnosticSha256": hashlib.sha256(combined.encode()).hexdigest(),
                }
            )
        checks.append("rejects-catalog-symlink-escape")

    return {
        "$schema": "zed-pkg-test/gitops-current-main-adversarial/v1",
        "productCommit": args.product_commit,
        "clusterCommit": args.cluster_commit,
        "platform": {
            "system": os.environ.get("RUNNER_OS", sys.platform),
            "architecture": os.environ.get("RUNNER_ARCH", "unknown"),
        },
        "result": "passed",
        "recordCount": zed_report["records"],
        "previewCount": len(items),
        "baseline": {
            "zedReportSha256": canonical_digest(zed_report),
            "nativeReportSha256": canonical_digest(native_report),
            "previewSha256": canonical_digest(preview),
        },
        "scenarioCount": len(scenarios),
        "scenarios": scenarios,
        "checkCount": len(checks),
        "checks": checks,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zed", type=Path, required=True)
    parser.add_argument("--zed-gitops", type=Path, required=True)
    parser.add_argument("--product", type=Path, required=True)
    parser.add_argument("--cluster", type=Path, required=True)
    parser.add_argument("--product-commit", required=True)
    parser.add_argument("--cluster-commit", required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        evidence = certify(args)
    except (CertificationError, OSError, subprocess.SubprocessError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    args.evidence.parent.mkdir(parents=True, exist_ok=True)
    args.evidence.write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"certified {evidence['checkCount']} checks and "
        f"{evidence['scenarioCount']} adversarial scenarios"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
