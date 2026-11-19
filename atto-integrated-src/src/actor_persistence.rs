//! Portable actor-owned scalar checkpoint layout, schema fingerprint and codec.
//!
//! This is **not** the browser Wasm durable runtime. Disk journals, fsync,
//! mailbox replay, incarnation fencing and suspended storage hooks remain
//! unavailable. The type checker refuses emitting persistent/durable actors.
//!
//! Wire format v1 is deterministic and endian-independent. The checksum
//! catches accidental corruption; it is NOT an authenticity/MAC primitive.
use crate::ast::{ActorDecl, Type};
use crate::diag::{Diagnostic, Pos};

const MAGIC: &[u8; 8] = b"ATTOST01";
const VERSION: u8 = 1;
const MAX_FIELDS: usize = 256;
const MAX_SNAPSHOT_BYTES: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarKind {
    Int,
    Bool,
}
impl ScalarKind {
    fn tag(self) -> u8 {
        match self { Self::Int => 1, Self::Bool => 2 }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateScalar {
    Int(i64),
    Bool(bool),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarField {
    pub name: String,
    pub kind: ScalarKind,
}

/// Compile-time state layout. This is a schema/checkpoint prototype, NOT a
/// live actor heap snapshot. Unrecognized nested objects fail closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActorStateSchema {
    pub actor_name: String,
    pub schema_id: u64,
    pub fields: Vec<ScalarField>,
}

fn fnv64(bytes: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325_u64;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn codec_error(msg: impl Into<String>) -> Diagnostic {
    Diagnostic::new(Pos { line: 1, col: 1 }, "E_PERSISTENCE_IO", msg)
}

impl ActorStateSchema {
    pub fn for_actor(actor: &ActorDecl) -> Result<Self, Diagnostic> {
        if actor.fields.len() > MAX_FIELDS {
            return Err(Diagnostic::new(actor.pos, "E_PERSIST_SCHEMA_LIMIT",
                "actor snapshot field budget exceeded"));
        }
        let mut fields: Vec<ScalarField> = Vec::with_capacity(actor.fields.len());
        let mut signature = Vec::new();
        signature.extend_from_slice(b"atto.actor.state.schema.v1\0");
        let name = actor.name.as_bytes();
        signature.extend_from_slice(&(name.len() as u32).to_le_bytes());
        signature.extend_from_slice(name);
        for f in &actor.fields {
            let kind = match f.ty {
                Type::Int => ScalarKind::Int,
                Type::Bool => ScalarKind::Bool,
                _ => return Err(Diagnostic::new(f.pos, "E_NON_PERSISTABLE_STATE",
                    format!("actor field '{}.{}' has no proven scalar Persistable codec", actor.name, f.name))),
            };
            if fields.iter().any(|previous| previous.name == f.name) {
                return Err(Diagnostic::new(f.pos, "E_DUPLICATE",
                    format!("duplicate state field '{}.{}'", actor.name, f.name)));
            }
            let bytes = f.name.as_bytes();
            signature.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
            signature.extend_from_slice(bytes);
            signature.push(kind.tag());
            fields.push(ScalarField { name: f.name.clone(), kind });
        }
        Ok(Self {
            actor_name: actor.name.clone(),
            schema_id: fnv64(&signature),
            fields,
        })
    }

    /// Encode values in declaration order. Do not use on an actor's live,
    /// borrowed state; the runtime must supply an immutable quiescent copy.
    pub fn encode(&self, values: &[StateScalar]) -> Result<Vec<u8>, Diagnostic> {
        if self.fields.len() != values.len() || values.len() > MAX_FIELDS {
            return Err(codec_error("state field count differs from compiled schema"));
        }
        let mut out = Vec::with_capacity(8 + 1 + 8 + 2 + values.len() * 9 + 8);
        out.extend_from_slice(MAGIC);
        out.push(VERSION);
        out.extend_from_slice(&self.schema_id.to_le_bytes());
        out.extend_from_slice(&(values.len() as u16).to_le_bytes());
        for (field, value) in self.fields.iter().zip(values) {
            out.push(field.kind.tag());
            match (field.kind, value) {
                (ScalarKind::Int, StateScalar::Int(n)) => out.extend_from_slice(&n.to_le_bytes()),
                (ScalarKind::Bool, StateScalar::Bool(b)) => out.push(u8::from(*b)),
                _ => return Err(codec_error("state scalar value/type mismatch")),
            }
        }
        if out.len() + 8 > MAX_SNAPSHOT_BYTES {
            return Err(codec_error("snapshot exceeds fixed v1 byte budget"));
        }
        let checksum = fnv64(&out);
        out.extend_from_slice(&checksum.to_le_bytes());
        Ok(out)
    }

    /// Reject stale-schema, torn, malformed, corrupt, or noncanonical state
    /// before publishing any recovered actor fields.
    pub fn decode(&self, bytes: &[u8]) -> Result<Vec<StateScalar>, Diagnostic> {
        const MIN: usize = 8 + 1 + 8 + 2 + 8;
        if bytes.len() < MIN || bytes.len() > MAX_SNAPSHOT_BYTES {
            return Err(codec_error("invalid snapshot length"));
        }
        if &bytes[..8] != MAGIC.as_slice() || bytes[8] != VERSION {
            return Err(codec_error("invalid snapshot magic/version"));
        }
        let header_schema = u64::from_le_bytes(bytes[9..17].try_into().expect("checked length"));
        if header_schema != self.schema_id {
            return Err(Diagnostic::new(Pos { line: 1, col: 1 },
                "E_PERSIST_SCHEMA_MISMATCH", "snapshot belongs to a different actor state schema"));
        }
        let count = u16::from_le_bytes(bytes[17..19].try_into().expect("checked length")) as usize;
        if count != self.fields.len() {
            return Err(codec_error("snapshot field count differs from compiled schema"));
        }
        let data_end = bytes.len() - 8;
        let checksum = u64::from_le_bytes(bytes[data_end..].try_into().expect("fixed checksum"));
        if fnv64(&bytes[..data_end]) != checksum {
            return Err(codec_error("snapshot checksum mismatch"));
        }
        let mut cursor = 19usize;
        let mut out = Vec::with_capacity(count);
        for field in &self.fields {
            let tag = *bytes.get(cursor).ok_or_else(|| codec_error("truncated field tag"))?;
            cursor += 1;
            if tag != field.kind.tag() {
                return Err(codec_error("state field tag differs from compiled schema"));
            }
            match field.kind {
                ScalarKind::Int => {
                    let data: [u8; 8] = bytes.get(cursor..cursor + 8)
                        .ok_or_else(|| codec_error("truncated integer"))?
                        .try_into().expect("eight bytes selected");
                    cursor += 8;
                    out.push(StateScalar::Int(i64::from_le_bytes(data)));
                }
                ScalarKind::Bool => {
                    let b = *bytes.get(cursor).ok_or_else(|| codec_error("truncated boolean"))?;
                    cursor += 1;
                    if b > 1 { return Err(codec_error("noncanonical boolean encoding")); }
                    out.push(StateScalar::Bool(b == 1));
                }
            }
        }
        if cursor != data_end {
            return Err(codec_error("trailing or missing snapshot payload bytes"));
        }
        Ok(out)
    }
}
