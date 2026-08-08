#!/usr/bin/env python3
"""Verify current public GitHub evidence for the DEN-2797 recovery wave."""

from __future__ import annotations

import argparse
import json
import os
import socket
import time
from datetime import datetime, timezone
from http.client import HTTPResponse
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import HTTPRedirectHandler, Request, build_opener

API_ROOT = "https://api.github.com"
MAX_RESPONSE_BYTES = 1024 * 1024
RECOVERED_REPOSITORIES = (
    "apostille-me/apme-mcp-server.rs",
    "embedded-alerts/eal-mcp-server.rs",
    "evento-globolo/evgl-mcp-server.rs",
    "hacker-house-medellin/hhm-mcp-server.rs",
)
MISSING_REPOSITORIES = (
    "apostille-me/apme-e2e",
    "embedded-alerts/eal-e2e",
    "evento-globolo/evgl-e2e",
    "hacker-house-medellin/hhm-e2e",
)


class AuditError(RuntimeError):
    pass


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(
        self,
        req: Request,
        fp: HTTPResponse,
        code: int,
        msg: str,
        headers: Any,
        newurl: str,
    ) -> None:
        return None


def read_bounded(response: HTTPResponse) -> bytes:
    payload = response.read(MAX_RESPONSE_BYTES + 1)
    if len(payload) > MAX_RESPONSE_BYTES:
        raise AuditError("GitHub API response exceeded the size limit")
    return payload


def request_json(path: str, token: str) -> tuple[int, dict[str, Any] | None]:
    request = Request(
        f"{API_ROOT}{path}",
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "User-Agent": "zed-pkg-test-den-2797-evidence-audit/1",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    opener = build_opener(NoRedirect())
    for attempt in range(3):
        try:
            with opener.open(request, timeout=15) as response:
                status = response.status
                payload = read_bounded(response)
        except HTTPError as exc:
            exc.read(4096)
            if exc.code == 404:
                return 404, None
            if exc.code in {429, 500, 502, 503, 504} and attempt < 2:
                time.sleep(1 + attempt)
                continue
            raise AuditError(f"GitHub API returned HTTP {exc.code} for {path}") from exc
        except (URLError, TimeoutError, socket.timeout) as exc:
            if attempt < 2:
                time.sleep(1 + attempt)
                continue
            raise AuditError(f"GitHub API request failed for {path}") from exc
        if status != 200:
            raise AuditError(f"GitHub API returned HTTP {status} for {path}")
        try:
            value = json.loads(payload)
        except json.JSONDecodeError as exc:
            raise AuditError(f"GitHub API returned invalid JSON for {path}") from exc
        if not isinstance(value, dict):
            raise AuditError(f"GitHub API returned a non-object for {path}")
        return status, value
    raise AssertionError("unreachable retry state")


def validate_sha(value: Any, label: str) -> str:
    if not isinstance(value, str) or len(value) != 40:
        raise AuditError(f"{label} is not a full Git SHA")
    if any(character not in "0123456789abcdef" for character in value):
        raise AuditError(f"{label} is not a lowercase Git SHA")
    return value


def audit(token: str, source_pin: dict[str, Any]) -> dict[str, Any]:
    recovered: list[dict[str, Any]] = []
    missing: list[dict[str, Any]] = []

    for full_name in RECOVERED_REPOSITORIES:
        status, repository = request_json(f"/repos/{full_name}", token)
        if status != 200 or repository is None:
            raise AuditError(f"recovered repository is absent: {full_name}")
        if str(repository.get("full_name", "")).lower() != full_name.lower():
            raise AuditError(f"GitHub returned the wrong repository identity for {full_name}")
        if repository.get("visibility") != "public":
            raise AuditError(f"recovered repository is not public: {full_name}")
        if repository.get("default_branch") != "main":
            raise AuditError(f"recovered repository default branch drifted: {full_name}")
        if repository.get("archived") is True:
            raise AuditError(f"recovered repository is archived: {full_name}")

        _, commit = request_json(f"/repos/{full_name}/commits/main", token)
        if commit is None:
            raise AuditError(f"recovered repository main commit is absent: {full_name}")
        main_sha = validate_sha(commit.get("sha"), f"{full_name} main SHA")

        _, pull = request_json(f"/repos/{full_name}/pulls/1", token)
        if pull is None:
            raise AuditError(f"recovery review PR #1 is absent: {full_name}")
        if pull.get("state") != "closed" or not pull.get("merged_at"):
            raise AuditError(f"recovery review PR #1 is not merged: {full_name}")
        merge_commit_sha = validate_sha(
            pull.get("merge_commit_sha"), f"{full_name} PR #1 merge SHA"
        )
        head = pull.get("head") if isinstance(pull.get("head"), dict) else {}
        head_sha = validate_sha(head.get("sha"), f"{full_name} PR #1 head SHA")

        recovered.append(
            {
                "repository": full_name,
                "repository_id": repository.get("id"),
                "repository_url": repository.get("html_url"),
                "visibility": repository.get("visibility"),
                "default_branch": repository.get("default_branch"),
                "main_sha": main_sha,
                "pull_request": {
                    "number": 1,
                    "url": pull.get("html_url"),
                    "state": pull.get("state"),
                    "merged_at": pull.get("merged_at"),
                    "head_sha": head_sha,
                    "merge_commit_sha": merge_commit_sha,
                },
            }
        )

    for full_name in MISSING_REPOSITORIES:
        status, repository = request_json(f"/repos/{full_name}", token)
        if status != 404 or repository is not None:
            raise AuditError(
                f"recovery source is stale because expected-missing repository now exists: {full_name}"
            )
        missing.append({"repository": full_name, "http_status": 404})

    return {
        "schema_version": "artifact_recovery_github_evidence.v1",
        "observed_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "source_repository": source_pin["repository"],
        "source_commit": source_pin["commit"],
        "linear_issue": source_pin["linear_issue"],
        "recovered": recovered,
        "missing": missing,
        "summary": {
            "recovered_repositories": len(recovered),
            "merged_recovery_pull_requests": len(recovered),
            "missing_repositories": len(missing),
            "failures": 0,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-pin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    token = os.getenv("GITHUB_TOKEN", "")
    if not token:
        print("error: GITHUB_TOKEN is required", file=os.sys.stderr)
        return 2
    try:
        source_pin = json.loads(args.source_pin.read_text(encoding="utf-8"))
        result = audit(token, source_pin)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    except (AuditError, OSError, json.JSONDecodeError, KeyError) as exc:
        print(f"error: {exc}", file=os.sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
