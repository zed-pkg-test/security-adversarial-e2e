#!/usr/bin/env python3
"""Adversarial validation contracts for the DEN-2797 recovery ledger."""

from __future__ import annotations

import argparse
import copy
import sys
import tempfile
import unittest
from pathlib import Path

NOW = "2026-08-08T21:30:00Z"


def configure_source(source_root: Path) -> None:
    source_root = source_root.resolve()
    for path in (source_root / "tools", source_root / "scripts"):
        if not path.is_dir():
            raise RuntimeError(f"missing pinned source directory: {path}")
        sys.path.insert(0, str(path))


class ArtifactRecoveryAdversarialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        import artifact_recovery_ledger as recovery  # type: ignore
        import build_artifact_recovery_backfill as backfill  # type: ignore

        cls.recovery = recovery
        cls.backfill = backfill

    def fixture(self) -> dict:
        return self.backfill.build_fixture()

    @staticmethod
    def identity(item: dict) -> str:
        target = item["target"]
        return f"{target['owner']}/{target['repository']}".lower()

    def item(self, identity: str = "apostille-me/apme-e2e") -> dict:
        return next(
            copy.deepcopy(item)
            for item in self.fixture()["items"]
            if self.identity(item) == identity
        )

    def observation(self, item: dict) -> dict:
        value = self.fixture()
        value["items"] = [item]
        return value

    def reconcile(self, value: dict):
        return self.recovery.reconcile(
            value,
            None,
            now=NOW,
            batch_size=50,
            target_task_id=self.recovery.DEFAULT_CLI_TASK_ID,
        )

    def test_credential_personal_and_private_key_shapes_fail_closed(self) -> None:
        unsafe_values = (
            "gh" + "p_" + ("A" * 32),
            "Bearer " + ("B" * 20),
            "-----BEGIN " + "PRIVATE KEY-----",
            "password" + "=not-a-real-secret",
            "person" + "@" + "example.invalid",
        )
        for unsafe in unsafe_values:
            with self.subTest(kind=unsafe.split(" ", 1)[0].split("=", 1)[0]):
                item = self.item()
                item["note"] = unsafe
                with self.assertRaises(self.recovery.RecoveryError):
                    self.recovery.validate_observation(self.observation(item))

    def test_unsafe_artifact_paths_are_rejected(self) -> None:
        for path in ("../escape", "/absolute/path", "safe/../../escape"):
            with self.subTest(path=path):
                item = self.item()
                artifact = item["local"].get("artifact")
                self.assertIsNotNone(artifact)
                artifact["paths"] = [path]
                with self.assertRaisesRegex(
                    self.recovery.RecoveryError,
                    "safe relative path",
                ):
                    self.recovery.validate_observation(self.observation(item))

    def test_unsafe_branch_shapes_are_rejected(self) -> None:
        unsafe_branches = (
            "/absolute",
            "agent//double",
            "agent/../escape",
            "agent/@{escape}",
            "agent\\escape",
            "agent/trailing/",
        )
        for branch in unsafe_branches:
            with self.subTest(branch=branch):
                item = self.item()
                item["intent"]["branch"] = branch
                with self.assertRaisesRegex(
                    self.recovery.RecoveryError,
                    "invalid Git ref shape",
                ):
                    self.recovery.validate_observation(self.observation(item))

    def test_github_host_spoof_and_cross_repository_claims_are_rejected(self) -> None:
        spoofed = self.item()
        owner = spoofed["target"]["owner"]
        repository = spoofed["target"]["repository"]
        spoofed["remote"]["repository"]["url"] = (
            f"https://github.com.evil.invalid/{owner}/{repository}"
        )
        with self.assertRaisesRegex(
            self.recovery.RecoveryError,
            "not a canonical GitHub URL",
        ):
            self.recovery.validate_observation(self.observation(spoofed))

        cross_repository = self.item()
        cross_repository["claims"]["pull_request_url"] = (
            "https://github.com/other-owner/other-repository/pull/1"
        )
        with self.assertRaisesRegex(
            self.recovery.RecoveryError,
            "points outside",
        ):
            self.recovery.validate_observation(self.observation(cross_repository))

    def test_commit_url_sha_mismatch_is_rejected(self) -> None:
        item = self.item()
        owner = item["target"]["owner"]
        repository = item["target"]["repository"]
        repository_url = f"https://github.com/{owner}/{repository}"
        item["remote"] = {
            "collected": True,
            "repository": {
                "exists": True,
                "visibility": "public",
                "default_branch": "main",
                "url": repository_url,
            },
            "branches": [],
            "commits": [
                {
                    "sha": "a" * 40,
                    "url": f"{repository_url}/commit/{'b' * 40}",
                }
            ],
            "pull_requests": [],
        }
        with self.assertRaisesRegex(
            self.recovery.RecoveryError,
            "URL/SHA mismatch",
        ):
            self.recovery.validate_observation(self.observation(item))

    def test_duplicate_origin_owner_repository_key_is_rejected(self) -> None:
        item = self.item()
        value = self.fixture()
        value["items"] = [item, copy.deepcopy(item)]
        with self.assertRaisesRegex(
            self.recovery.RecoveryError,
            "duplicate origin/owner/repository ledger keys",
        ):
            self.recovery.validate_observation(value)

    def test_unknown_prompt_body_field_is_rejected_before_persistence(self) -> None:
        item = self.item()
        item["prompt_body"] = "not retained"
        with self.assertRaisesRegex(
            self.recovery.RecoveryError,
            "unsupported keys",
        ):
            self.recovery.validate_observation(self.observation(item))

    def test_unverified_claim_is_blocked_and_never_sent_to_cli_recovery(self) -> None:
        item = self.item()
        owner = item["target"]["owner"]
        repository = item["target"]["repository"]
        item["claims"]["repository_url"] = f"https://github.com/{owner}/{repository}"
        ledger, queue = self.reconcile(self.observation(item))
        entry = next(iter(ledger["entries"].values()))
        self.assertEqual(entry["classification"]["status"], "blocked")
        self.assertIn(
            "claimed_repository_unverified",
            entry["classification"]["findings"],
        )
        self.assertEqual(queue["items"], [])

    def test_incomplete_remote_read_is_blocked_not_retried_as_missing(self) -> None:
        item = self.item()
        item["remote"]["collected"] = False
        ledger, queue = self.reconcile(self.observation(item))
        entry = next(iter(ledger["entries"].values()))
        self.assertEqual(entry["classification"]["status"], "blocked")
        self.assertIn(
            "remote_evidence_incomplete",
            entry["classification"]["findings"],
        )
        self.assertEqual(queue["items"], [])

    def test_duplicate_json_keys_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "duplicate.json"
            path.write_text('{"schema_version":"x","schema_version":"y"}')
            with self.assertRaisesRegex(
                self.recovery.RecoveryError,
                "duplicate JSON key",
            ):
                self.recovery.load_json(path)

    def test_current_source_fixture_has_only_four_create_only_e2e_items(self) -> None:
        ledger, queue = self.reconcile(self.fixture())
        self.assertEqual(ledger["summary"]["entries"], 22)
        self.assertEqual(ledger["summary"]["complete"], 18)
        self.assertEqual(ledger["summary"]["actionable"], 4)
        self.assertEqual(queue["summary"], {
            "items": 4,
            "create_repository": 4,
            "recover_local": 0,
        })
        self.assertEqual(
            {
                f"{item['owner'].lower()}/{item['repository'].lower()}"
                for item in queue["items"]
            },
            {
                "apostille-me/apme-e2e",
                "embedded-alerts/eal-e2e",
                "evento-globolo/evgl-e2e",
                "hacker-house-medellin/hhm-e2e",
            },
        )
        self.assertTrue(all(item["visibility"] == "public" for item in queue["items"]))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, required=True)
    args, remaining = parser.parse_known_args()
    configure_source(args.source_root)
    unittest.main(argv=[sys.argv[0], *remaining], verbosity=2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
