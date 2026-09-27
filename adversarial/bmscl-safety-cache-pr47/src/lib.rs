#![allow(clippy::needless_return)]

use anyhow::{bail, Context, Result};
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fs::{self, File},
    io::{Read, Write},
    path::{Path, PathBuf},
};
use tempfile::NamedTempFile;
use walkdir::WalkDir;

pub const DEPENDENCY_SAFETY_FORMAT_V1: &str = "bmscl-dependency-safety-v1";
pub const DEPENDENCY_SAFETY_VERDICT_SAFE: &str = "safe";
const MAX_ATTESTATION_BYTES: u64 = 64 * 1024;
const HASH_BUFFER_BYTES: usize = 64 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HashLimits {
    pub max_artifact_bytes: u64,
    pub max_tree_entries: u64,
    pub max_tree_files: u64,
    pub max_tree_bytes: u64,
    pub max_tree_depth: usize,
    pub max_relative_path_bytes: usize,
}

impl Default for HashLimits {
    fn default() -> Self {
        return Self {
            max_artifact_bytes: 256 * 1024 * 1024,
            max_tree_entries: 131_072,
            max_tree_files: 65_536,
            max_tree_bytes: 512 * 1024 * 1024,
            max_tree_depth: 64,
            max_relative_path_bytes: 4096,
        };
    }
}

/// Exact identity of dependency bytes admitted for the Hosted Gleam profile.
///
/// A package name/version is intentionally insufficient. Reuse is valid only
/// when immutable package bytes, extracted source tree, analyzer semantics,
/// current security-analysis policy, trust key, compiler/backend, and hosted
/// profile identity all match.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct DependencySafetyIdentity {
    pub package: String,
    pub version: String,
    pub source: String,
    pub upstream_checksum: String,
    pub artifact_sha256: String,
    pub source_tree_sha256: String,
    pub policy_sha256: String,
    pub analysis_policy_sha256: String,
    pub analyzer_revision: String,
    pub analyzer_key_id: String,
    pub analyzer_public_key_sha256: String,
    pub gleam_version: String,
    pub target: String,
    pub profile: String,
}

impl DependencySafetyIdentity {
    pub fn validate(&self) -> Result<()> {
        if self.package.trim().is_empty() {
            bail!("dependency safety identity requires package name");
        }
        if self.version.trim().is_empty() {
            bail!("dependency safety identity requires package version");
        }
        if self.source != "hex" {
            bail!("dependency safety identity source must be `hex`");
        }
        if self.analyzer_revision.trim().is_empty() {
            bail!("dependency safety identity requires analyzer revision");
        }
        if self.analyzer_key_id.trim().is_empty() {
            bail!("dependency safety identity requires analyzer key id");
        }
        if self.gleam_version.trim().is_empty() {
            bail!("dependency safety identity requires Gleam version");
        }
        if self.target != "erlang" {
            bail!("dependency safety identity target must be `erlang`");
        }
        if self.profile.trim().is_empty() {
            bail!("dependency safety identity requires profile");
        }

        canonical_scalar(&self.package)?;
        canonical_scalar(&self.version)?;
        canonical_scalar(&self.source)?;
        canonical_scalar(&self.analyzer_revision)?;
        canonical_scalar(&self.analyzer_key_id)?;
        canonical_scalar(&self.gleam_version)?;
        canonical_scalar(&self.target)?;
        canonical_scalar(&self.profile)?;

        validate_sha256(&self.upstream_checksum, "upstream_checksum")?;
        validate_sha256(&self.artifact_sha256, "artifact_sha256")?;
        validate_sha256(&self.source_tree_sha256, "source_tree_sha256")?;
        validate_sha256(&self.policy_sha256, "policy_sha256")?;
        validate_sha256(&self.analysis_policy_sha256, "analysis_policy_sha256")?;
        validate_sha256(
            &self.analyzer_public_key_sha256,
            "analyzer_public_key_sha256",
        )?;

        return Ok(());
    }

    /// Stable, line-delimited representation used only for key derivation.
    /// Field order is part of the v1 cache contract.
    pub fn canonical_payload(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let payload = format!(
            concat!(
                "format={DEPENDENCY_SAFETY_FORMAT_V1}\n",
                "package={}\n",
                "version={}\n",
                "source={}\n",
                "upstream_checksum={}\n",
                "artifact_sha256={}\n",
                "source_tree_sha256={}\n",
                "policy_sha256={}\n",
                "analysis_policy_sha256={}\n",
                "analyzer_revision={}\n",
                "analyzer_key_id={}\n",
                "analyzer_public_key_sha256={}\n",
                "gleam_version={}\n",
                "target={}\n",
                "profile={}\n"
            ),
            canonical_scalar(&self.package)?,
            canonical_scalar(&self.version)?,
            canonical_scalar(&self.source)?,
            self.upstream_checksum.to_ascii_lowercase(),
            self.artifact_sha256.to_ascii_lowercase(),
            self.source_tree_sha256.to_ascii_lowercase(),
            self.policy_sha256.to_ascii_lowercase(),
            self.analysis_policy_sha256.to_ascii_lowercase(),
            canonical_scalar(&self.analyzer_revision)?,
            canonical_scalar(&self.analyzer_key_id)?,
            self.analyzer_public_key_sha256.to_ascii_lowercase(),
            canonical_scalar(&self.gleam_version)?,
            canonical_scalar(&self.target)?,
            canonical_scalar(&self.profile)?,
        );
        return Ok(payload.into_bytes());
    }

    pub fn cache_key_sha256(&self) -> Result<String> {
        let payload = self.canonical_payload()?;
        return Ok(sha256_bytes(&payload));
    }
}

/// Positive dependency-safety result signed by the trusted BeamScale analyzer.
///
/// The signature makes a shared cache safe to reuse across nodes even if the
/// CAS object store itself is not a trust root. A valid artifact digest alone
/// proves identity, not that the bytes satisfy the Hosted Gleam policy.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct DependencySafetyAttestation {
    pub format: String,
    pub verdict: String,
    pub key_sha256: String,
    pub identity: DependencySafetyIdentity,
    pub signature_hex: String,
}

impl DependencySafetyAttestation {
    pub fn sign_safe(
        identity: DependencySafetyIdentity,
        signing_key: &SigningKey,
    ) -> Result<Self> {
        identity.validate()?;
        verify_identity_key(&identity, &signing_key.verifying_key())?;

        let key_sha256 = identity.cache_key_sha256()?;
        let payload = signature_payload(&key_sha256)?;
        let signature = signing_key.sign(&payload);

        return Ok(Self {
            format: DEPENDENCY_SAFETY_FORMAT_V1.to_string(),
            verdict: DEPENDENCY_SAFETY_VERDICT_SAFE.to_string(),
            key_sha256,
            identity,
            signature_hex: hex::encode(signature.to_bytes()),
        });
    }

    pub fn verify_safe(
        &self,
        expected_identity: &DependencySafetyIdentity,
        verifying_key: &VerifyingKey,
    ) -> Result<()> {
        if self.format != DEPENDENCY_SAFETY_FORMAT_V1 {
            bail!("unsupported dependency safety attestation format `{}`", self.format);
        }
        if self.verdict != DEPENDENCY_SAFETY_VERDICT_SAFE {
            bail!("dependency safety cache accepts positive `safe` attestations only");
        }

        validate_sha256(&self.key_sha256, "key_sha256")?;
        self.identity.validate()?;
        expected_identity.validate()?;
        verify_identity_key(expected_identity, verifying_key)?;
        verify_identity_key(&self.identity, verifying_key)?;

        let record_key = self.identity.cache_key_sha256()?;
        if record_key != self.key_sha256.to_ascii_lowercase() {
            bail!("dependency safety attestation key does not match embedded identity");
        }

        let expected_key = expected_identity.cache_key_sha256()?;
        if expected_key != record_key {
            bail!("dependency safety attestation does not match requested dependency identity");
        }

        let signature_bytes = hex::decode(&self.signature_hex)
            .context("dependency safety signature must be hexadecimal")?;
        let signature = Signature::from_slice(&signature_bytes)
            .context("dependency safety signature must be exactly 64 bytes")?;
        let payload = signature_payload(&record_key)?;
        verifying_key
            .verify(&payload, &signature)
            .context("dependency safety attestation signature verification failed")?;

        return Ok(());
    }
}

/// Persist a verified positive safety attestation in an immutable local CAS.
/// Existing objects are never overwritten. Shared/distributed stores should
/// preserve the same key + signature contract.
///
/// `root` must already exist as a trusted build-service-owned directory. It
/// must never be a tenant-controlled path. Requiring the configured root to
/// preexist prevents this function from following a tenant-planted root
/// symlink while creating cache directories.
pub fn store_verified(
    root: &Path,
    attestation: &DependencySafetyAttestation,
    verifying_key: &VerifyingKey,
) -> Result<PathBuf> {
    attestation.verify_safe(&attestation.identity, verifying_key)?;
    ensure_directory(root, "dependency safety cache root")?;

    let path = cache_path(root, &attestation.key_sha256)?;
    let parent = path.parent().context("dependency safety cache path has no parent")?;
    fs::create_dir_all(parent)
        .with_context(|| format!("create dependency safety cache directory {}", parent.display()))?;
    ensure_cache_directory_chain(root, parent)?;

    match fs::symlink_metadata(&path) {
        Ok(_) => {
            let existing = load_record_at(&path)?;
            existing.verify_safe(&attestation.identity, verifying_key)?;
            return Ok(path);
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(error)
                .with_context(|| format!("stat dependency safety cache object {}", path.display()));
        }
    }

    let bytes = serde_json::to_vec_pretty(attestation)
        .context("serialize dependency safety attestation")?;
    if bytes.len() as u64 > MAX_ATTESTATION_BYTES {
        bail!("dependency safety attestation exceeds size limit");
    }

    let mut temporary = NamedTempFile::new_in(parent)
        .with_context(|| format!("create temporary cache object in {}", parent.display()))?;
    temporary
        .write_all(&bytes)
        .context("write dependency safety cache object")?;
    temporary
        .as_file_mut()
        .sync_all()
        .context("sync dependency safety cache object")?;

    match temporary.persist_noclobber(&path) {
        Ok(_) => {
            return Ok(path);
        }
        Err(error) if error.error.kind() == std::io::ErrorKind::AlreadyExists => {
            let existing = load_record_at(&path)?;
            existing.verify_safe(&attestation.identity, verifying_key)?;
            return Ok(path);
        }
        Err(error) => {
            return Err(error.error).with_context(|| {
                format!("persist dependency safety cache object {}", path.display())
            });
        }
    }
}

/// Load a cache hit only if identity, trust-key fingerprint, and analyzer
/// signature are valid. Missing objects are ordinary misses; malformed or
/// tampered objects fail closed.
pub fn load_verified(
    root: &Path,
    identity: &DependencySafetyIdentity,
    verifying_key: &VerifyingKey,
) -> Result<Option<DependencySafetyAttestation>> {
    identity.validate()?;
    verify_identity_key(identity, verifying_key)?;

    match fs::symlink_metadata(root) {
        Ok(metadata) => {
            if !metadata.file_type().is_dir() {
                bail!("dependency safety cache root must be a non-symlink directory");
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(None);
        }
        Err(error) => {
            return Err(error)
                .with_context(|| format!("stat dependency safety cache root {}", root.display()));
        }
    }

    let key_sha256 = identity.cache_key_sha256()?;
    let path = cache_path(root, &key_sha256)?;
    match fs::symlink_metadata(&path) {
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(None);
        }
        Err(error) => {
            return Err(error)
                .with_context(|| format!("stat dependency safety cache object {}", path.display()));
        }
    }

    let record = load_record_at(&path)?;
    record.verify_safe(identity, verifying_key)?;
    return Ok(Some(record));
}

pub fn cache_path(root: &Path, key_sha256: &str) -> Result<PathBuf> {
    validate_sha256(key_sha256, "cache key")?;
    let key = key_sha256.to_ascii_lowercase();
    let prefix = &key[..2];
    return Ok(root
        .join("v1")
        .join("sha256")
        .join(prefix)
        .join(format!("{key}.json")));
}

/// SHA-256 of an exact downloaded package artifact, bounded to prevent an
/// attacker-controlled package from forcing an unbounded allocation or read.
pub fn sha256_file(path: &Path) -> Result<String> {
    return sha256_file_with_limit(path, HashLimits::default().max_artifact_bytes);
}

pub fn sha256_file_with_limit(path: &Path, max_bytes: u64) -> Result<String> {
    let (digest, _) = hash_regular_file(path, max_bytes, "dependency artifact")?;
    return Ok(hex::encode(digest));
}

/// Deterministic digest of the extracted dependency source tree.
///
/// Paths and file bytes are both bound into the digest. Symlinks and unusual
/// filesystem object types are rejected. Traversal is bounded by total entry
/// count, file count, depth, aggregate bytes, and relative-path length so a
/// malicious archive cannot turn cache-key derivation into a resource attack.
///
/// The caller must materialize a read-only/frozen snapshot and keep that exact
/// snapshot stable through hashing, analysis, and compilation. A mutable tree
/// would create a hash/analyze/build TOCTOU boundary that no cache key can fix.
pub fn sha256_tree(root: &Path) -> Result<String> {
    return sha256_tree_with_limits(root, HashLimits::default());
}

pub fn sha256_tree_with_limits(root: &Path, limits: HashLimits) -> Result<String> {
    let root_metadata = fs::symlink_metadata(root)
        .with_context(|| format!("stat dependency source tree {}", root.display()))?;
    if !root_metadata.file_type().is_dir() {
        bail!("dependency source tree must be a directory: {}", root.display());
    }

    let mut entries_seen = 0u64;
    let mut files = Vec::new();
    for entry in WalkDir::new(root)
        .follow_links(false)
        .max_depth(limits.max_tree_depth.saturating_add(1))
        .max_open(32)
    {
        let entry = entry.with_context(|| format!("walk dependency source tree {}", root.display()))?;
        if entry.depth() == 0 {
            continue;
        }

        entries_seen = entries_seen
            .checked_add(1)
            .context("dependency source tree entry accounting overflow")?;
        if entries_seen > limits.max_tree_entries {
            bail!("dependency source tree exceeds entry-count limit");
        }
        if entry.depth() > limits.max_tree_depth {
            bail!("dependency source tree exceeds depth limit");
        }

        let file_type = entry.file_type();
        if file_type.is_symlink() {
            bail!("dependency source tree contains symlink: {}", entry.path().display());
        }
        if file_type.is_dir() {
            continue;
        }
        if !file_type.is_file() {
            bail!(
                "dependency source tree contains unsupported filesystem object: {}",
                entry.path().display()
            );
        }

        let relative = entry
            .path()
            .strip_prefix(root)
            .with_context(|| format!("derive relative dependency path {}", entry.path().display()))?;
        let relative = relative
            .to_str()
            .context("dependency source path must be UTF-8")?
            .replace('\\', "/");
        if relative.len() > limits.max_relative_path_bytes {
            bail!("dependency source path exceeds byte limit: {relative}");
        }

        files.push((relative, entry.into_path()));
        if files.len() as u64 > limits.max_tree_files {
            bail!("dependency source tree exceeds file-count limit");
        }
    }

    files.sort_by(|left, right| left.0.cmp(&right.0));
    let mut total_bytes = 0u64;
    let mut hasher = Sha256::new();
    hasher.update(b"bmscl-dependency-source-tree-v1\0");

    for (relative, path) in files {
        let remaining = limits
            .max_tree_bytes
            .checked_sub(total_bytes)
            .context("dependency source tree byte accounting overflow")?;
        let (file_digest, file_bytes) =
            hash_regular_file(&path, remaining, "dependency source file")?;
        total_bytes = total_bytes
            .checked_add(file_bytes)
            .context("dependency source tree byte accounting overflow")?;
        if total_bytes > limits.max_tree_bytes {
            bail!("dependency source tree exceeds aggregate byte limit");
        }

        hasher.update((relative.len() as u64).to_be_bytes());
        hasher.update(relative.as_bytes());
        hasher.update(file_bytes.to_be_bytes());
        hasher.update(file_digest);
    }

    return Ok(hex::encode(hasher.finalize()));
}

fn hash_regular_file(path: &Path, max_bytes: u64, label: &str) -> Result<([u8; 32], u64)> {
    let link_metadata = fs::symlink_metadata(path)
        .with_context(|| format!("stat {label} {}", path.display()))?;
    if !link_metadata.file_type().is_file() {
        bail!("{label} must be a regular file: {}", path.display());
    }
    if link_metadata.len() > max_bytes {
        bail!("{label} exceeds byte limit: {}", path.display());
    }

    let mut file = File::open(path)
        .with_context(|| format!("open {label} {}", path.display()))?;
    let opened_metadata = file
        .metadata()
        .with_context(|| format!("stat open {label} {}", path.display()))?;
    if !opened_metadata.file_type().is_file() {
        bail!("{label} changed away from a regular file: {}", path.display());
    }
    if opened_metadata.len() > max_bytes {
        bail!("{label} exceeds byte limit: {}", path.display());
    }

    let mut hasher = Sha256::new();
    let mut buffer = [0u8; HASH_BUFFER_BYTES];
    let mut total = 0u64;
    loop {
        let read = file
            .read(&mut buffer)
            .with_context(|| format!("read {label} {}", path.display()))?;
        if read == 0 {
            break;
        }
        total = total
            .checked_add(read as u64)
            .context("file byte accounting overflow")?;
        if total > max_bytes {
            bail!("{label} exceeds byte limit: {}", path.display());
        }
        hasher.update(&buffer[..read]);
    }

    return Ok((hasher.finalize().into(), total));
}

fn load_record_at(path: &Path) -> Result<DependencySafetyAttestation> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("stat dependency safety cache object {}", path.display()))?;
    if !metadata.file_type().is_file() {
        bail!("dependency safety cache object must be a regular file: {}", path.display());
    }
    if metadata.len() > MAX_ATTESTATION_BYTES {
        bail!("dependency safety cache object exceeds size limit: {}", path.display());
    }

    let mut bytes = Vec::new();
    File::open(path)
        .with_context(|| format!("open dependency safety cache object {}", path.display()))?
        .take(MAX_ATTESTATION_BYTES + 1)
        .read_to_end(&mut bytes)
        .with_context(|| format!("read dependency safety cache object {}", path.display()))?;
    if bytes.len() as u64 > MAX_ATTESTATION_BYTES {
        bail!("dependency safety cache object exceeds size limit: {}", path.display());
    }

    let record = serde_json::from_slice(&bytes)
        .with_context(|| format!("parse dependency safety cache object {}", path.display()))?;
    return Ok(record);
}

fn ensure_directory(path: &Path, label: &str) -> Result<()> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("stat {label} {}", path.display()))?;
    if !metadata.file_type().is_dir() {
        bail!("{label} must be a non-symlink directory: {}", path.display());
    }
    return Ok(());
}

fn ensure_cache_directory_chain(root: &Path, parent: &Path) -> Result<()> {
    let relative = parent
        .strip_prefix(root)
        .context("dependency safety cache shard escaped configured root")?;
    let mut current = root.to_path_buf();
    for component in relative.components() {
        current.push(component.as_os_str());
        ensure_directory(&current, "dependency safety cache directory")?;
    }
    return Ok(());
}

fn verify_identity_key(
    identity: &DependencySafetyIdentity,
    verifying_key: &VerifyingKey,
) -> Result<()> {
    let actual = public_key_sha256(verifying_key);
    if actual != identity.analyzer_public_key_sha256.to_ascii_lowercase() {
        bail!("dependency safety analyzer public key does not match identity fingerprint");
    }
    return Ok(());
}

pub fn public_key_sha256(verifying_key: &VerifyingKey) -> String {
    return sha256_bytes(&verifying_key.to_bytes());
}

fn signature_payload(key_sha256: &str) -> Result<Vec<u8>> {
    validate_sha256(key_sha256, "key_sha256")?;
    let payload = format!(
        "format={DEPENDENCY_SAFETY_FORMAT_V1}\nverdict={DEPENDENCY_SAFETY_VERDICT_SAFE}\nkey_sha256={}\n",
        key_sha256.to_ascii_lowercase(),
    );
    return Ok(payload.into_bytes());
}

fn canonical_scalar(value: &str) -> Result<&str> {
    if value.contains('\n') || value.contains('\r') || value.contains('\0') {
        bail!("dependency safety identity fields cannot contain control delimiters");
    }
    return Ok(value);
}

fn validate_sha256(value: &str, label: &str) -> Result<()> {
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        bail!("{label} must be exactly 64 hexadecimal characters");
    }
    return Ok(());
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    return hex::encode(hasher.finalize());
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;
    use tempfile::tempdir;

    fn digest(character: char) -> String {
        return std::iter::repeat(character).take(64).collect();
    }

    fn signing_key(byte: u8) -> SigningKey {
        return SigningKey::from_bytes(&[byte; 32]);
    }

    fn identity_for(key: &SigningKey) -> DependencySafetyIdentity {
        return DependencySafetyIdentity {
            package: "gleam_stdlib".into(),
            version: "0.62.1".into(),
            source: "hex".into(),
            upstream_checksum: digest('a'),
            artifact_sha256: digest('b'),
            source_tree_sha256: digest('c'),
            policy_sha256: digest('d'),
            analysis_policy_sha256: digest('e'),
            analyzer_revision: "compiler-rev-123".into(),
            analyzer_key_id: "analyzer-2026-q3".into(),
            analyzer_public_key_sha256: public_key_sha256(&key.verifying_key()),
            gleam_version: "1.18.1".into(),
            target: "erlang".into(),
            profile: "bmscl-hosted-gleam-v3-http-capability".into(),
        };
    }

    #[test]
    fn policy_change_invalidates_cache_key() {
        let key = signing_key(7);
        let first = identity_for(&key);
        let mut second = first.clone();
        second.policy_sha256 = digest('f');

        assert_ne!(
            first.cache_key_sha256().expect("first key"),
            second.cache_key_sha256().expect("second key")
        );
    }

    #[test]
    fn analysis_policy_change_invalidates_cache_key() {
        let key = signing_key(7);
        let first = identity_for(&key);
        let mut second = first.clone();
        second.analysis_policy_sha256 = digest('f');

        assert_ne!(
            first.cache_key_sha256().expect("first key"),
            second.cache_key_sha256().expect("second key")
        );
    }

    #[test]
    fn content_change_invalidates_cache_key() {
        let key = signing_key(7);
        let first = identity_for(&key);
        let mut second = first.clone();
        second.artifact_sha256 = digest('f');

        assert_ne!(
            first.cache_key_sha256().expect("first key"),
            second.cache_key_sha256().expect("second key")
        );
    }

    #[test]
    fn signer_rotation_invalidates_cache_key() {
        let first_key = signing_key(7);
        let second_key = signing_key(8);
        let first = identity_for(&first_key);
        let mut second = identity_for(&second_key);
        second.analyzer_key_id = "analyzer-2026-q4".into();

        assert_ne!(
            first.cache_key_sha256().expect("first key"),
            second.cache_key_sha256().expect("second key")
        );
    }

    #[test]
    fn signed_cache_round_trip() {
        let directory = tempdir().expect("cache tempdir");
        let key = signing_key(7);
        let verifying_key = key.verifying_key();
        let expected = identity_for(&key);
        let attestation = DependencySafetyAttestation::sign_safe(expected.clone(), &key)
            .expect("sign safety attestation");

        store_verified(directory.path(), &attestation, &verifying_key)
            .expect("store safety attestation");
        let loaded = load_verified(directory.path(), &expected, &verifying_key)
            .expect("load safety attestation")
            .expect("cache hit");

        assert_eq!(loaded, attestation);
    }

    #[test]
    fn wrong_trust_key_fails_closed() {
        let directory = tempdir().expect("cache tempdir");
        let key = signing_key(7);
        let wrong_key = signing_key(8);
        let expected = identity_for(&key);
        let attestation = DependencySafetyAttestation::sign_safe(expected.clone(), &key)
            .expect("sign safety attestation");

        let result = store_verified(directory.path(), &attestation, &wrong_key.verifying_key());
        assert!(result.is_err());
    }

    #[test]
    fn identity_mismatch_is_a_cache_miss() {
        let directory = tempdir().expect("cache tempdir");
        let key = signing_key(7);
        let verifying_key = key.verifying_key();
        let original = identity_for(&key);
        let attestation = DependencySafetyAttestation::sign_safe(original.clone(), &key)
            .expect("sign safety attestation");
        store_verified(directory.path(), &attestation, &verifying_key)
            .expect("store safety attestation");

        let mut changed = original;
        changed.policy_sha256 = digest('f');
        let loaded = load_verified(directory.path(), &changed, &verifying_key)
            .expect("load changed identity");

        assert!(loaded.is_none());
    }

    #[test]
    fn tampered_record_fails_closed() {
        let directory = tempdir().expect("cache tempdir");
        let key = signing_key(7);
        let verifying_key = key.verifying_key();
        let expected = identity_for(&key);
        let attestation = DependencySafetyAttestation::sign_safe(expected.clone(), &key)
            .expect("sign safety attestation");
        let path = store_verified(directory.path(), &attestation, &verifying_key)
            .expect("store safety attestation");

        let mut value: Value = serde_json::from_slice(&fs::read(&path).expect("read cache object"))
            .expect("parse cache object");
        value["identity"]["profile"] = Value::String("tampered-profile".into());
        fs::write(&path, serde_json::to_vec_pretty(&value).expect("encode tamper"))
            .expect("write tampered object");

        let result = load_verified(directory.path(), &expected, &verifying_key);
        assert!(result.is_err());
    }

    #[test]
    fn artifact_hashing_is_bounded() {
        let directory = tempdir().expect("artifact tempdir");
        let path = directory.path().join("package.tar");
        fs::write(&path, b"0123456789").expect("write package");

        let result = sha256_file_with_limit(&path, 4);
        assert!(result.is_err());
    }

    #[test]
    fn tree_digest_binds_paths_and_contents() {
        let directory = tempdir().expect("source tempdir");
        fs::create_dir_all(directory.path().join("src")).expect("create src");
        fs::write(directory.path().join("src/main.gleam"), "pub fn main() { Nil }\n")
            .expect("write source");
        let first = sha256_tree(directory.path()).expect("first tree digest");

        fs::write(directory.path().join("src/main.gleam"), "pub fn main() { True }\n")
            .expect("rewrite source");
        let second = sha256_tree(directory.path()).expect("second tree digest");

        assert_ne!(first, second);
    }

    #[test]
    fn tree_file_count_is_bounded() {
        let directory = tempdir().expect("source tempdir");
        fs::write(directory.path().join("a.gleam"), b"1234").expect("write a");
        fs::write(directory.path().join("b.gleam"), b"5678").expect("write b");
        let limits = HashLimits {
            max_artifact_bytes: 16,
            max_tree_entries: 8,
            max_tree_files: 1,
            max_tree_bytes: 16,
            max_tree_depth: 8,
            max_relative_path_bytes: 128,
        };

        let result = sha256_tree_with_limits(directory.path(), limits);
        assert!(result.is_err());
    }

    #[test]
    fn tree_entry_count_is_bounded() {
        let directory = tempdir().expect("source tempdir");
        fs::create_dir_all(directory.path().join("a/b/c")).expect("create nested dirs");
        let limits = HashLimits {
            max_artifact_bytes: 16,
            max_tree_entries: 2,
            max_tree_files: 8,
            max_tree_bytes: 16,
            max_tree_depth: 8,
            max_relative_path_bytes: 128,
        };

        let result = sha256_tree_with_limits(directory.path(), limits);
        assert!(result.is_err());
    }

    #[test]
    fn tree_depth_is_bounded() {
        let directory = tempdir().expect("source tempdir");
        fs::create_dir_all(directory.path().join("a/b/c")).expect("create nested dirs");
        let limits = HashLimits {
            max_artifact_bytes: 16,
            max_tree_entries: 8,
            max_tree_files: 8,
            max_tree_bytes: 16,
            max_tree_depth: 2,
            max_relative_path_bytes: 128,
        };

        let result = sha256_tree_with_limits(directory.path(), limits);
        assert!(result.is_err());
    }

    #[cfg(unix)]
    #[test]
    fn tree_hash_rejects_symlinks() {
        use std::os::unix::fs::symlink;

        let directory = tempdir().expect("source tempdir");
        fs::write(directory.path().join("real.gleam"), b"pub fn x() { Nil }\n")
            .expect("write real source");
        symlink("real.gleam", directory.path().join("alias.gleam"))
            .expect("create source symlink");

        let result = sha256_tree(directory.path());
        assert!(result.is_err());
    }

    #[cfg(unix)]
    #[test]
    fn cache_root_symlink_is_rejected() {
        use std::os::unix::fs::symlink;

        let directory = tempdir().expect("parent tempdir");
        let real = directory.path().join("real-cache");
        let alias = directory.path().join("alias-cache");
        fs::create_dir(&real).expect("create real cache");
        symlink(&real, &alias).expect("create cache symlink");

        let key = signing_key(7);
        let expected = identity_for(&key);
        let attestation = DependencySafetyAttestation::sign_safe(expected, &key)
            .expect("sign safety attestation");
        let result = store_verified(&alias, &attestation, &key.verifying_key());

        assert!(result.is_err());
    }
}
