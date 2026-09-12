from __future__ import annotations

import hashlib
import unittest

from adversarial.registry_trust_model import (
    CachedArtifact,
    OfflineCacheVerifier,
    TrustRefusal,
    TrustSnapshot,
)


def artifact(*, registry_id: str = "registry-a", publisher: str = "publisher-a", epoch: int = 7, version: str = "1.2.3", payload: bytes = b"immutable-package") -> CachedArtifact:
    return CachedArtifact(
        registry_id=registry_id,
        org="acme",
        name="widget",
        version=version,
        sha256=hashlib.sha256(payload).hexdigest(),
        publisher_key_id=publisher,
        trust_epoch=epoch,
        payload=payload,
    )


def trust(*, registry_id: str = "registry-a", epoch: int = 7, revoked=frozenset(), tombstoned=frozenset(), valid_until: int = 2000) -> TrustSnapshot:
    return TrustSnapshot(
        registry_id=registry_id,
        trust_epoch=epoch,
        revoked_publishers=frozenset(revoked),
        tombstoned_versions=frozenset(tombstoned),
        valid_until_unix=valid_until,
    )


class RegistryTrustAdversarialTests(unittest.TestCase):
    def test_current_trust_allows_exact_cached_bytes(self) -> None:
        candidate = artifact()
        self.assertEqual(
            OfflineCacheVerifier.verify(candidate, trust(), now_unix=1500, online_refresh_succeeded=False),
            candidate.payload,
        )

    def test_cross_registry_cache_replay_is_refused(self) -> None:
        with self.assertRaisesRegex(TrustRefusal, "different registry identity"):
            OfflineCacheVerifier.verify(artifact(registry_id="registry-b"), trust(), now_unix=1500, online_refresh_succeeded=False)

    def test_revoked_publisher_is_refused_even_when_payload_is_cached(self) -> None:
        with self.assertRaisesRegex(TrustRefusal, "publisher key is revoked"):
            OfflineCacheVerifier.verify(
                artifact(publisher="publisher-a"),
                trust(revoked={"publisher-a"}),
                now_unix=1500,
                online_refresh_succeeded=False,
            )

    def test_tombstoned_version_is_refused_even_when_cached(self) -> None:
        with self.assertRaisesRegex(TrustRefusal, "tombstoned"):
            OfflineCacheVerifier.verify(
                artifact(version="1.2.3"),
                trust(tombstoned={("acme", "widget", "1.2.3")}),
                now_unix=1500,
                online_refresh_succeeded=False,
            )

    def test_trust_root_rotation_refuses_old_cache_epoch(self) -> None:
        with self.assertRaisesRegex(TrustRefusal, "stale trust root"):
            OfflineCacheVerifier.verify(artifact(epoch=6), trust(epoch=7), now_unix=1500, online_refresh_succeeded=True)

    def test_offline_stale_trust_state_fails_closed(self) -> None:
        with self.assertRaisesRegex(TrustRefusal, "offline trust metadata is stale"):
            OfflineCacheVerifier.verify(artifact(), trust(valid_until=1000), now_unix=1500, online_refresh_succeeded=False)

    def test_refresh_does_not_override_revocation(self) -> None:
        with self.assertRaisesRegex(TrustRefusal, "publisher key is revoked"):
            OfflineCacheVerifier.verify(
                artifact(),
                trust(revoked={"publisher-a"}, valid_until=1000),
                now_unix=1500,
                online_refresh_succeeded=True,
            )

    def test_tampered_cached_bytes_are_refused(self) -> None:
        candidate = artifact(payload=b"immutable-package")
        tampered = CachedArtifact(**{**candidate.__dict__, "payload": b"tampered"})
        with self.assertRaisesRegex(TrustRefusal, "digest"):
            OfflineCacheVerifier.verify(tampered, trust(), now_unix=1500, online_refresh_succeeded=False)


if __name__ == "__main__":
    unittest.main()
