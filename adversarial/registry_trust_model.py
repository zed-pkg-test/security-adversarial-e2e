from __future__ import annotations

import hashlib
from dataclasses import dataclass


class TrustRefusal(RuntimeError):
    pass


@dataclass(frozen=True)
class CachedArtifact:
    registry_id: str
    org: str
    name: str
    version: str
    sha256: str
    publisher_key_id: str
    trust_epoch: int
    payload: bytes


@dataclass(frozen=True)
class TrustSnapshot:
    registry_id: str
    trust_epoch: int
    revoked_publishers: frozenset[str]
    tombstoned_versions: frozenset[tuple[str, str, str]]
    valid_until_unix: int


class OfflineCacheVerifier:
    """Fail-closed reference model for serving cached immutable package bytes."""

    @staticmethod
    def verify(
        artifact: CachedArtifact,
        trust: TrustSnapshot,
        *,
        now_unix: int,
        online_refresh_succeeded: bool,
    ) -> bytes:
        if artifact.registry_id != trust.registry_id:
            raise TrustRefusal("cached artifact belongs to a different registry identity")

        if now_unix > trust.valid_until_unix and not online_refresh_succeeded:
            raise TrustRefusal("offline trust metadata is stale")

        if artifact.trust_epoch != trust.trust_epoch:
            raise TrustRefusal("cached artifact was verified under a stale trust root")

        coordinate = (artifact.org, artifact.name, artifact.version)
        if coordinate in trust.tombstoned_versions:
            raise TrustRefusal("package version is tombstoned")

        if artifact.publisher_key_id in trust.revoked_publishers:
            raise TrustRefusal("publisher key is revoked")

        actual = hashlib.sha256(artifact.payload).hexdigest()
        if actual != artifact.sha256:
            raise TrustRefusal("cached payload digest does not match immutable identity")

        return artifact.payload
