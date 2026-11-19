//! Canonical **model-only** copy! / copy!! descriptor admission for full AOT.
//!
//! This is not a generated deep-copy runtime, a proof of descriptor provenance,
//! a general graph clone implementation, or execution of an AttoLang guest.
//! Each compiler must authenticate the typed field inventory, emit the actual
//! concrete-target copy function and independently enforce ownership and Send.
//! This checker is deliberately closed-world and rejects unknown capabilities.

use std::collections::{BTreeMap, BTreeSet};

pub type TypeId = u32;
pub type FieldId = u32;

pub const MAX_COPY_TYPES: usize = 4096;
pub const MAX_COPY_FIELDS: usize = 65536;
/// Bound recursive *type* traversal independently of distinct-type budget.
pub const MAX_COPY_DEPTH: usize = 128;

/// Mutability / ownership meaning of an actual stored field. Never infer this
/// from raw memory layout, a user annotation, or erased Object type alone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldKind {
    Scalar,
    /// Immutable, lifetime-safe and statically copyable / shareable backing.
    ImmutableShared,
    /// Exclusively-owned mutable object: cannot be duplicated by copy!.
    OwnedMutable(TypeId),
    /// Explicitly share-authorized mutable object: copy! may retain identity,
    /// but copy!! must recursively detach it.
    SharedMutable(TypeId),
    Borrowed,
    Resource,
    Unresolved,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// Stable ID within a concrete declaring type, including private fields.
    pub id: FieldId,
    pub kind: FieldKind,
}

/// Descriptor for one *concrete* AOT type (not a user-provided reflection table).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDescriptor {
    pub id: TypeId,
    /// Verified nominal parent, with a separate compiler-emitted field inventory.
    pub parent: Option<TypeId>,
    pub fields: Vec<Field>,
    /// A closed-world verified witness for a generated whole-concrete-type copy.
    pub deep_copy_witness: bool,
    pub shallow_copy_witness: bool,
    /// Independent, transitive proof supplied by the compiler. Copyable alone
    /// is never a Sendable proof.
    pub sendable: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyMode {
    Shallow,
    Deep,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CopyRequest {
    /// Runtime-concrete type, resolved through an AOT registered witness.
    pub concrete_type: TypeId,
    /// Static receiver used for a superclass call; cannot cause slicing.
    pub static_type: TypeId,
    pub mode: CopyMode,
    /// Actor-mail send requires a *separate* Sendable proof.
    pub actor_send: bool,
}

/// Only a planning receipt. It does not authorize memcpy or make an allocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CopyPlan {
    pub concrete_type: TypeId,
    pub mode: CopyMode,
    pub copied_type_ids: Vec<TypeId>,
    pub actor_send_checked: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Error(pub &'static str);

fn check_type(
    id: TypeId,
    all: &BTreeMap<TypeId, &TypeDescriptor>,
    mode: CopyMode,
    actor_send: bool,
    pending: &mut BTreeSet<TypeId>,
    visited: &mut BTreeSet<TypeId>,
    depth: usize,
) -> Result<(), Error> {
    if depth >= MAX_COPY_DEPTH {
        return Err(Error("E_COPY_GRAPH_BUDGET"));
    }
    if pending.contains(&id) {
        // Type cycles may be legal for a *memoized* graph copier. A caller's
        // actual runtime must register clone shells BEFORE visiting children.
        return Ok(());
    }
    if visited.contains(&id) {
        return Ok(());
    }
    let ty = all.get(&id).ok_or(Error("E_COPY_AOT_WITNESS"))?;
    if actor_send && !ty.sendable {
        return Err(Error("E_COPY_SENDABLE"));
    }
    let witness_proven = match mode {
        CopyMode::Shallow => ty.shallow_copy_witness,
        CopyMode::Deep => ty.deep_copy_witness,
    };
    if !witness_proven {
        return Err(Error("E_COPY_AOT_WITNESS"));
    }
    pending.insert(id);
    if let Some(parent) = ty.parent {
        check_type(parent, all, mode, actor_send, pending, visited, depth + 1)?;
    }
    for field in &ty.fields {
        match field.kind {
            FieldKind::Scalar | FieldKind::ImmutableShared => {}
            FieldKind::SharedMutable(nested) if mode == CopyMode::Shallow => {
                // Shallow references are permitted only because the frontend
                // supplied a verified shared-mutable field kind. They remain
                // subject to the actor-send restriction below.
                if actor_send {
                    return Err(Error("E_COPY_ACTOR_ISOLATION"));
                }
                if nested == 0 || !all.contains_key(&nested) {
                    return Err(Error("E_COPY_AOT_WITNESS"));
                }
            }
            FieldKind::OwnedMutable(_) if mode == CopyMode::Shallow => {
                return Err(Error("E_COPY_SHALLOW_ALIAS"));
            }
            FieldKind::OwnedMutable(nested) | FieldKind::SharedMutable(nested) => {
                check_type(nested, all, mode, actor_send, pending, visited, depth + 1)?;
            }
            FieldKind::Borrowed => return Err(Error("E_COPY_VIEW")),
            FieldKind::Resource => return Err(Error("E_COPY_FORBIDDEN")),
            FieldKind::Unresolved => return Err(Error("E_COPY_UNPROVEN")),
        }
    }
    pending.remove(&id);
    visited.insert(id);
    return Ok(());
}

/// Validate a complete, closed-world set of trusted field descriptors and
/// produce a bounded type-graph plan for the selected copy operation.
///
/// This cannot prove a *runtime instance* graph's work bound, alias separation,
/// Sendable provenance, user overrides or cancellation cleanup. Real compilers
/// must additionally prove and instrument those obligations.
pub fn admit_copy(descriptors: &[TypeDescriptor], request: CopyRequest) -> Result<CopyPlan, Error> {
    if request.static_type == 0 || request.concrete_type == 0 {
        return Err(Error("E_COPY_AOT_WITNESS"));
    }
    if descriptors.is_empty() || descriptors.len() > MAX_COPY_TYPES {
        return Err(Error("E_COPY_GRAPH_BUDGET"));
    }
    let mut all = BTreeMap::new();
    let mut fields_seen = 0usize;
    for ty in descriptors {
        if ty.id == 0 || all.insert(ty.id, ty).is_some() {
            return Err(Error("E_COPY_LAYOUT"));
        }
        fields_seen = fields_seen.saturating_add(ty.fields.len());
        if fields_seen > MAX_COPY_FIELDS {
            return Err(Error("E_COPY_GRAPH_BUDGET"));
        }
        let mut ids = BTreeSet::new();
        for field in &ty.fields {
            if field.id == 0 || !ids.insert(field.id) {
                return Err(Error("E_COPY_LAYOUT"));
            }
        }
        if ty.parent == Some(ty.id) {
            return Err(Error("E_COPY_LAYOUT"));
        }
    }
    // Check *all* nominal parent chains iteratively, even if the selected
    // static type equals the concrete type. A malicious descriptor must not
    // smuggle an inheritance cycle into a generated AOT layout.
    let mut validated_ancestors = BTreeSet::new();
    for ty in descriptors {
        let mut path = BTreeSet::new();
        let mut cur = Some(ty.id);
        while let Some(id) = cur {
            if validated_ancestors.contains(&id) {
                break;
            }
            if !path.insert(id) {
                return Err(Error("E_COPY_LAYOUT"));
            }
            cur = all.get(&id).ok_or(Error("E_COPY_AOT_WITNESS"))?.parent;
        }
        validated_ancestors.extend(path);
    }
    // An upcast may only refer to a verified nominal ancestor. Never slice an
    // unknown or erased Object reference to its declared base class.
    let mut ancestor = Some(request.concrete_type);
    let mut chain = BTreeSet::new();
    let mut is_ancestor = false;
    while let Some(id) = ancestor {
        if !chain.insert(id) || chain.len() > MAX_COPY_TYPES {
            return Err(Error("E_COPY_LAYOUT"));
        }
        if id == request.static_type {
            is_ancestor = true;
            break;
        }
        ancestor = all.get(&id).ok_or(Error("E_COPY_AOT_WITNESS"))?.parent;
    }
    if !is_ancestor {
        return Err(Error("E_COPY_LAYOUT"));
    }
    let mut visited = BTreeSet::new();
    check_type(
        request.concrete_type,
        &all,
        request.mode,
        request.actor_send,
        &mut BTreeSet::new(),
        &mut visited,
        0,
    )?;
    return Ok(CopyPlan {
        concrete_type: request.concrete_type,
        mode: request.mode,
        copied_type_ids: visited.into_iter().collect(),
        actor_send_checked: request.actor_send,
    });
}
