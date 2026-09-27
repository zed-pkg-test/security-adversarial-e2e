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
        for (name, value) in [
            ("package", self.package.as_str()),
            ("version", self.version.as_str()),
            ("analyzer_revision", self.analyzer_revision.as_str()),
            ("analyzer_key_id", self.analyzer_key_id.as_str()),
            ("gleam_version", self.gleam_version.as_str()),
            ("profile", self.profile.as_str()),
        ] {
            if value.trim().is_empty() {
                bail!("dependency safety identity requires {name}");
            }
            validate_scalar(value, name)?;
        }
        if self.source != "hex" {
            bail!("dependency safety identity source must be `hex`");
        }
        if self.target != "erlang" {
            bail!("dependency safety identity target must be `erlang`");
        }
        for (name, value) in [
            ("upstream_checksum", self.upstream_checksum.as_str()),
            ("artifact_sha256", self.artifact_sha256.as_str()),
            ("source_tree_sha256", self.source_tree_sha256.as_str()),
            ("policy_sha256", self.policy_sha256.as_str()),
            (
                "analysis_policy_sha256",
                self.analysis_policy_sha256.as_str(),
            ),
            (
                "analyzer_public_key_sha256",
                self.analyzer_public_key_sha256.as_str(),
            ),
        ] {
            validate_sha256(value, name)?;
        }
        return Ok(());
    }

    pub fn canonical_payload(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let values = [
            DEPENDENCY_SAFETY_FORMAT_V1.to_string(),
            self.package.clone(),
            self.version.clone(),
            self.source.clone(),
            self.upstream_checksum.to_ascii_lowercase(),
            self.artifact_sha256.to_ascii_lowercase(),
            self.source_tree_sha256.to_ascii_lowercase(),
            self.policy_sha256.to_ascii_lowercase(),
            self.analysis_policy_sha256.to_ascii_lowercase(),
            self.analyzer_revision.clone(),
            self.analyzer_key_id.clone(),
            self.analyzer_public_key_sha256.to_ascii_lowercase(),
            self.gleam_version.clone(),
            self.target.clone(),
            self.profile.clone(),
        ];
        let names = [
            "format",
            "package",
            "version",
            "source",
            "upstream_checksum",
            "artifact_sha256",
            "source_tree_sha256",
            "policy_sha256",
            "analysis_policy_sha256",
            "analyzer_revision",
            "analyzer_key_id",
            "analyzer_public_key_sha256",
            "gleam_version",
            "target",
            "profile",
        ];
        let mut payload = String::new();
        for (name, value) in names.into_iter().zip(values) {
            payload.push_str(name);
            payload.push('=');
            payload.push_str(&value);
            payload.push('\n');
        }
        return Ok(payload.into_bytes());
    }

    pub fn cache_key_sha256(&self) -> Result<String> {
        return Ok(sha256_bytes(&self.canonical_payload()?));
    }
}

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
    pub fn sign_safe(identity: DependencySafetyIdentity, key: &SigningKey) -> Result<Self> {
        identity.validate()?;
        verify_identity_key(&identity, &key.verifying_key())?;
        let key_sha256 = identity.cache_key_sha256()?;
        let signature = key.sign(&signature_payload(&key_sha256)?);
        return Ok(Self {
            format: DEPENDENCY_SAFETY_FORMAT_V1.into(),
            verdict: DEPENDENCY_SAFETY_VERDICT_SAFE.into(),
            key_sha256,
            identity,
            signature_hex: hex::encode(signature.to_bytes()),
        });
    }

    pub fn verify_safe(
        &self,
        expected: &DependencySafetyIdentity,
        key: &VerifyingKey,
    ) -> Result<()> {
        if self.format != DEPENDENCY_SAFETY_FORMAT_V1
            || self.verdict != DEPENDENCY_SAFETY_VERDICT_SAFE
        {
            bail!("dependency safety cache accepts only v1 positive safe attestations");
        }
        self.identity.validate()?;
        expected.validate()?;
        verify_identity_key(expected, key)?;
        verify_identity_key(&self.identity, key)?;
        let actual_key = self.identity.cache_key_sha256()?;
        if actual_key != self.key_sha256.to_ascii_lowercase()
            || actual_key != expected.cache_key_sha256()?
        {
            bail!("dependency safety attestation identity mismatch");
        }
        let bytes = hex::decode(&self.signature_hex)
            .context("dependency safety signature must be hexadecimal")?;
        let signature = Signature::from_slice(&bytes)
            .context("dependency safety signature must be 64 bytes")?;
        key.verify(&signature_payload(&actual_key)?, &signature)
            .context("dependency safety attestation signature verification failed")?;
        return Ok(());
    }
}

pub fn store_verified(
    root: &Path,
    attestation: &DependencySafetyAttestation,
    key: &VerifyingKey,
) -> Result<PathBuf> {
    attestation.verify_safe(&attestation.identity, key)?;
    ensure_directory(root, "dependency safety cache root")?;
    let path = cache_path(root, &attestation.key_sha256)?;
    let parent = path
        .parent()
        .context("dependency safety cache path has no parent")?;
    fs::create_dir_all(parent)
        .with_context(|| format!("create cache directory {}", parent.display()))?;
    ensure_directory_chain(root, parent)?;
    if path_exists(&path)? {
        load_record(&path)?.verify_safe(&attestation.identity, key)?;
        return Ok(path);
    }
    let bytes = serde_json::to_vec_pretty(attestation)
        .context("serialize dependency safety attestation")?;
    if bytes.len() as u64 > MAX_ATTESTATION_BYTES {
        bail!("dependency safety attestation exceeds size limit");
    }
    let mut temp = NamedTempFile::new_in(parent).context("create temporary cache object")?;
    temp.write_all(&bytes)
        .context("write dependency safety cache object")?;
    temp.as_file_mut()
        .sync_all()
        .context("sync dependency safety cache object")?;
    match temp.persist_noclobber(&path) {
        Ok(_) => return Ok(path),
        Err(error) if error.error.kind() == std::io::ErrorKind::AlreadyExists => {
            load_record(&path)?.verify_safe(&attestation.identity, key)?;
            return Ok(path);
        }
        Err(error) => return Err(error.error).context("persist dependency safety cache object"),
    }
}

pub fn load_verified(
    root: &Path,
    identity: &DependencySafetyIdentity,
    key: &VerifyingKey,
) -> Result<Option<DependencySafetyAttestation>> {
    identity.validate()?;
    verify_identity_key(identity, key)?;
    if !path_exists(root)? {
        return Ok(None);
    }
    ensure_directory(root, "dependency safety cache root")?;
    let path = cache_path(root, &identity.cache_key_sha256()?)?;
    if !path_exists(&path)? {
        return Ok(None);
    }
    let record = load_record(&path)?;
    record.verify_safe(identity, key)?;
    return Ok(Some(record));
}

pub fn cache_path(root: &Path, key_sha256: &str) -> Result<PathBuf> {
    validate_sha256(key_sha256, "cache key")?;
    let key = key_sha256.to_ascii_lowercase();
    return Ok(root
        .join("v1/sha256")
        .join(&key[..2])
        .join(format!("{key}.json")));
}

pub fn sha256_file(path: &Path) -> Result<String> {
    return sha256_file_with_limit(path, HashLimits::default().max_artifact_bytes);
}

pub fn sha256_file_with_limit(path: &Path, max_bytes: u64) -> Result<String> {
    let (digest, _) = hash_regular_file(path, max_bytes, "dependency artifact")?;
    return Ok(hex::encode(digest));
}

pub fn sha256_tree(root: &Path) -> Result<String> {
    return sha256_tree_with_limits(root, HashLimits::default());
}

pub fn sha256_tree_with_limits(root: &Path, limits: HashLimits) -> Result<String> {
    ensure_directory(root, "dependency source tree")?;
    let mut entries_seen = 0u64;
    let mut files = Vec::new();
    for entry in WalkDir::new(root)
        .follow_links(false)
        .max_depth(limits.max_tree_depth.saturating_add(1))
        .max_open(32)
    {
        let entry =
            entry.with_context(|| format!("walk dependency source tree {}", root.display()))?;
        if entry.depth() == 0 {
            continue;
        }
        entries_seen = entries_seen
            .checked_add(1)
            .context("dependency entry count overflow")?;
        if entries_seen > limits.max_tree_entries || entry.depth() > limits.max_tree_depth {
            bail!("dependency source tree exceeds traversal limits");
        }
        let kind = entry.file_type();
        if kind.is_symlink() {
            bail!(
                "dependency source tree contains symlink: {}",
                entry.path().display()
            );
        }
        if kind.is_dir() {
            continue;
        }
        if !kind.is_file() {
            bail!(
                "dependency source tree contains special file: {}",
                entry.path().display()
            );
        }
        let relative = entry
            .path()
            .strip_prefix(root)
            .context("derive dependency relative path")?;
        let relative = relative
            .to_str()
            .context("dependency source path must be UTF-8")?
            .replace('\\', "/");
        if relative.len() > limits.max_relative_path_bytes {
            bail!("dependency source path exceeds byte limit");
        }
        files.push((relative, entry.into_path()));
        if files.len() as u64 > limits.max_tree_files {
            bail!("dependency source tree exceeds file-count limit");
        }
    }
    files.sort_by(|left, right| left.0.cmp(&right.0));
    let mut total = 0u64;
    let mut hasher = Sha256::new();
    hasher.update(b"bmscl-dependency-source-tree-v1\0");
    for (relative, path) in files {
        let remaining = limits
            .max_tree_bytes
            .checked_sub(total)
            .context("dependency byte count overflow")?;
        let (digest, bytes) = hash_regular_file(&path, remaining, "dependency source file")?;
        total = total
            .checked_add(bytes)
            .context("dependency byte count overflow")?;
        hasher.update((relative.len() as u64).to_be_bytes());
        hasher.update(relative.as_bytes());
        hasher.update(bytes.to_be_bytes());
        hasher.update(digest);
    }
    return Ok(hex::encode(hasher.finalize()));
}

fn hash_regular_file(path: &Path, max_bytes: u64, label: &str) -> Result<([u8; 32], u64)> {
    let metadata =
        fs::symlink_metadata(path).with_context(|| format!("stat {label} {}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > max_bytes {
        bail!(
            "{label} is not an allowed bounded regular file: {}",
            path.display()
        );
    }
    let mut file = File::open(path).with_context(|| format!("open {label} {}", path.display()))?;
    let opened = file.metadata().context("stat opened file")?;
    if !opened.file_type().is_file() || opened.len() > max_bytes {
        bail!("{label} changed or exceeds byte limit: {}", path.display());
    }
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; HASH_BUFFER_BYTES];
    let mut total = 0u64;
    loop {
        let count = file
            .read(&mut buffer)
            .with_context(|| format!("read {label}"))?;
        if count == 0 {
            break;
        }
        total = total
            .checked_add(count as u64)
            .context("file byte count overflow")?;
        if total > max_bytes {
            bail!("{label} exceeds byte limit");
        }
        hasher.update(&buffer[..count]);
    }
    return Ok((hasher.finalize().into(), total));
}

fn load_record(path: &Path) -> Result<DependencySafetyAttestation> {
    let metadata = fs::symlink_metadata(path).context("stat dependency safety cache object")?;
    if !metadata.file_type().is_file() || metadata.len() > MAX_ATTESTATION_BYTES {
        bail!("dependency safety cache object is not an allowed bounded regular file");
    }
    let mut bytes = Vec::new();
    File::open(path)?
        .take(MAX_ATTESTATION_BYTES + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_ATTESTATION_BYTES {
        bail!("dependency safety cache object exceeds size limit");
    }
    return serde_json::from_slice(&bytes).context("parse dependency safety cache object");
}

fn ensure_directory(path: &Path, label: &str) -> Result<()> {
    let metadata =
        fs::symlink_metadata(path).with_context(|| format!("stat {label} {}", path.display()))?;
    if !metadata.file_type().is_dir() {
        bail!(
            "{label} must be a non-symlink directory: {}",
            path.display()
        );
    }
    return Ok(());
}

fn ensure_directory_chain(root: &Path, parent: &Path) -> Result<()> {
    let relative = parent
        .strip_prefix(root)
        .context("cache shard escaped configured root")?;
    let mut current = root.to_path_buf();
    for component in relative.components() {
        current.push(component.as_os_str());
        ensure_directory(&current, "dependency safety cache directory")?;
    }
    return Ok(());
}

fn path_exists(path: &Path) -> Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => return Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(error).with_context(|| format!("stat {}", path.display())),
    }
}

pub fn public_key_sha256(key: &VerifyingKey) -> String {
    return sha256_bytes(&key.to_bytes());
}

fn verify_identity_key(identity: &DependencySafetyIdentity, key: &VerifyingKey) -> Result<()> {
    if identity.analyzer_public_key_sha256.to_ascii_lowercase() != public_key_sha256(key) {
        bail!("dependency safety analyzer public key does not match identity fingerprint");
    }
    return Ok(());
}

fn signature_payload(key_sha256: &str) -> Result<Vec<u8>> {
    validate_sha256(key_sha256, "key_sha256")?;
    return Ok(format!(
        "format={}\nverdict={}\nkey_sha256={}\n",
        DEPENDENCY_SAFETY_FORMAT_V1,
        DEPENDENCY_SAFETY_VERDICT_SAFE,
        key_sha256.to_ascii_lowercase()
    )
    .into_bytes());
}

fn validate_scalar(value: &str, label: &str) -> Result<()> {
    if value
        .chars()
        .any(|character| matches!(character, '\n' | '\r' | '\0'))
    {
        bail!("dependency safety identity {label} contains a control delimiter");
    }
    return Ok(());
}

fn validate_sha256(value: &str, label: &str) -> Result<()> {
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        bail!("{label} must be exactly 64 hexadecimal characters");
    }
    return Ok(());
}

fn sha256_bytes(bytes: &[u8]) -> String {
    return hex::encode(Sha256::digest(bytes));
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn digest(character: char) -> String {
        return character.to_string().repeat(64);
    }

    fn key(byte: u8) -> SigningKey {
        return SigningKey::from_bytes(&[byte; 32]);
    }

    fn identity(signing_key: &SigningKey) -> DependencySafetyIdentity {
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
            analyzer_public_key_sha256: public_key_sha256(&signing_key.verifying_key()),
            gleam_version: "1.18.1".into(),
            target: "erlang".into(),
            profile: "bmscl-hosted-gleam-v3-http-capability".into(),
        };
    }

    #[test]
    fn identity_changes_invalidate_cache_key() {
        let signing_key = key(7);
        let first = identity(&signing_key);
        for mutate in ["artifact", "policy", "analysis_policy"] {
            let mut changed = first.clone();
            match mutate {
                "artifact" => changed.artifact_sha256 = digest('f'),
                "policy" => changed.policy_sha256 = digest('f'),
                _ => changed.analysis_policy_sha256 = digest('f'),
            }
            assert_ne!(
                first.cache_key_sha256().unwrap(),
                changed.cache_key_sha256().unwrap()
            );
        }
    }

    #[test]
    fn signed_cache_round_trip_and_wrong_key_fail_closed() {
        let directory = tempdir().unwrap();
        let signing_key = key(7);
        let expected = identity(&signing_key);
        let attestation =
            DependencySafetyAttestation::sign_safe(expected.clone(), &signing_key).unwrap();
        store_verified(directory.path(), &attestation, &signing_key.verifying_key()).unwrap();
        assert_eq!(
            load_verified(directory.path(), &expected, &signing_key.verifying_key()).unwrap(),
            Some(attestation.clone())
        );
        assert!(load_verified(directory.path(), &expected, &key(8).verifying_key()).is_err());
    }

    #[test]
    fn tampering_fails_closed() {
        let directory = tempdir().unwrap();
        let signing_key = key(7);
        let expected = identity(&signing_key);
        let attestation =
            DependencySafetyAttestation::sign_safe(expected.clone(), &signing_key).unwrap();
        let path =
            store_verified(directory.path(), &attestation, &signing_key.verifying_key()).unwrap();
        let mut value: serde_json::Value =
            serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        value["identity"]["profile"] = "tampered".into();
        fs::write(path, serde_json::to_vec(&value).unwrap()).unwrap();
        assert!(load_verified(directory.path(), &expected, &signing_key.verifying_key()).is_err());
    }

    #[test]
    fn hash_limits_fail_closed() {
        let directory = tempdir().unwrap();
        let file = directory.path().join("artifact");
        fs::write(&file, b"0123456789").unwrap();
        assert!(sha256_file_with_limit(&file, 4).is_err());
        fs::create_dir_all(directory.path().join("a/b/c")).unwrap();
        let limits = HashLimits {
            max_artifact_bytes: 16,
            max_tree_entries: 2,
            max_tree_files: 8,
            max_tree_bytes: 16,
            max_tree_depth: 2,
            max_relative_path_bytes: 128,
        };
        assert!(sha256_tree_with_limits(directory.path(), limits).is_err());
    }

    #[test]
    fn tree_digest_binds_contents() {
        let directory = tempdir().unwrap();
        fs::write(
            directory.path().join("main.gleam"),
            "pub fn main() { Nil }\n",
        )
        .unwrap();
        let first = sha256_tree(directory.path()).unwrap();
        fs::write(
            directory.path().join("main.gleam"),
            "pub fn main() { True }\n",
        )
        .unwrap();
        assert_ne!(first, sha256_tree(directory.path()).unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn symlinks_are_rejected() {
        use std::os::unix::fs::symlink;

        let directory = tempdir().unwrap();
        fs::write(directory.path().join("real"), b"x").unwrap();
        symlink("real", directory.path().join("alias")).unwrap();
        assert!(sha256_tree(directory.path()).is_err());

        let real_cache = directory.path().join("real-cache");
        let alias_cache = directory.path().join("alias-cache");
        fs::create_dir(&real_cache).unwrap();
        symlink(&real_cache, &alias_cache).unwrap();
        let signing_key = key(7);
        let attestation =
            DependencySafetyAttestation::sign_safe(identity(&signing_key), &signing_key).unwrap();
        assert!(store_verified(&alias_cache, &attestation, &signing_key.verifying_key()).is_err());
    }
}
