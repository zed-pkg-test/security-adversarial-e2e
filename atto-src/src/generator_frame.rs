//! Bounded generator continuation-frame and handle ABI contract. This module
//! is pure/host-independent; native guest-Wasm new/next/close emission lives in
//! wasm/generator_runtime.rs and enforces a fixed per-instance frame profile.
//!
//! Each generator has its own bounded, 8-byte-aligned frame in its actor/
//! tenant-owned guest arena. A handle is (nonzero generation, 32-bit arena
//! offset), not an unguarded pointer and not a cross-actor capability.
//!
//! Header layout (byte offsets):
//!   0  u32 generator type id
//!   4  u32 resume PC
//!   8  u32 lifecycle status
//!   12 u32 generation
//!   16 i64 last yielded value
//!   24 u32 free-list next offset (meaningful only after cleanup)
//!   28 u32 reserved
//!   32 ... per-generator immutable parameter, legacy local, delegated child
//!   56 ... up to 16 persistent typed i64 slots (184-byte guest frame total)
//!
//! The runtime checks generation + arena bounds on handle dereference,
//! recursively closes live delegates on normal/early close, and increments
//! generations before recycling frames. These pure layout utilities do not
//! by themselves prove the runtime's unwinding or isolation properties.

use crate::diag::{Diagnostic, Pos};

pub const FRAME_HEADER_BYTES: u32 = 32;
pub const FRAME_ALIGNMENT: u32 = 8;
pub const MAX_GENERATOR_FRAME_BYTES: u32 = 64 * 1024;
/// The current fixed guest heap is 16 Wasm pages (1 MiB).
pub const MAX_GUEST_ARENA_BYTES: u32 = 16 * 64 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GeneratorFrameLayout {
    pub parameters_offset: u32,
    pub locals_offset: u32,
    pub delegates_offset: u32,
    pub frame_bytes: u32,
    pub parameters: u32,
    pub locals: u32,
    pub delegates: u32,
}

fn frame_error(pos: Pos, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(pos, "E_GENERATOR_FRAME", message)
}

impl GeneratorFrameLayout {
    /// All slots are 8-byte aligned. Call this AFTER typed IR lowering with
    /// its complete local and temporary count (including hidden iterator
    /// temporaries); an AST-only estimate is a separate admission precheck.
    pub fn new(parameters: u32, locals: u32, delegates: u32, pos: Pos) -> Result<Self, Diagnostic> {
        let end = |base: u32, count: u32| -> Result<u32, Diagnostic> {
            base.checked_add(count.checked_mul(8).ok_or_else(|| frame_error(pos,
                "generator slot byte count overflow"))?).ok_or_else(|| frame_error(pos,
                "generator slot offset overflow"))
        };
        let locals_offset = end(FRAME_HEADER_BYTES, parameters)?;
        let delegates_offset = end(locals_offset, locals)?;
        let frame_bytes = end(delegates_offset, delegates)?;
        if frame_bytes > MAX_GENERATOR_FRAME_BYTES {
            return Err(frame_error(pos, format!(
                "generator frame {} bytes exceeds {}-byte limit",
                frame_bytes, MAX_GENERATOR_FRAME_BYTES
            )));
        }
        Ok(Self {
            parameters_offset: FRAME_HEADER_BYTES,
            locals_offset,
            delegates_offset,
            frame_bytes,
            parameters,
            locals,
            delegates,
        })
    }

    fn offset(&self, base: u32, count: u32, index: u32) -> Option<u32> {
        (index < count).then(|| base + index * 8)
    }

    pub fn parameter_offset(&self, index: u32) -> Option<u32> {
        self.offset(self.parameters_offset, self.parameters, index)
    }

    pub fn local_offset(&self, index: u32) -> Option<u32> {
        self.offset(self.locals_offset, self.locals, index)
    }

    pub fn delegate_offset(&self, index: u32) -> Option<u32> {
        self.offset(self.delegates_offset, self.delegates, index)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GeneratorHandle(u64);

impl GeneratorHandle {
    /// Zero is never a live handle. Reserve the first 8 arena bytes so a
    /// nonzero offset can never alias a null or uninitialized handle.
    pub fn new(offset: u32, generation: u32, pos: Pos) -> Result<Self, Diagnostic> {
        if offset < FRAME_ALIGNMENT || offset % FRAME_ALIGNMENT != 0
            || offset >= MAX_GUEST_ARENA_BYTES || generation == 0 {
            return Err(frame_error(pos,
                "invalid generator arena offset/alignment or zero generation"));
        }
        Ok(Self(((generation as u64) << 32) | offset as u64))
    }

    pub fn from_bits(bits: u64, pos: Pos) -> Result<Self, Diagnostic> {
        let offset = bits as u32;
        let generation = (bits >> 32) as u32;
        Self::new(offset, generation, pos)
    }

    pub fn bits(self) -> u64 { self.0 }
    pub fn arena_offset(self) -> u32 { self.0 as u32 }
    pub fn generation(self) -> u32 { (self.0 >> 32) as u32 }

    pub fn next_generation(self, pos: Pos) -> Result<u32, Diagnostic> {
        self.generation().checked_add(1).ok_or_else(|| frame_error(pos,
            "generator handle generation exhausted; frame reuse prohibited"))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum GeneratorState {
    Created = 0,
    Running = 1,
    Suspended = 2,
    Done = 3,
    Closing = 4,
    Closed = 5,
}

impl GeneratorState {
    fn state_error(self, operation: &str, pos: Pos) -> Diagnostic {
        Diagnostic::new(pos, "E_GENERATOR_STATE",
            format!("cannot {operation} a generator in state {self:?}"))
    }

    /// Successful pull grants exclusive resumption of the generator frame.
    /// A DONE iterator remains DONE on repeated pulls. RUNNING is non-reentrant.
    pub fn begin_pull(self, pos: Pos) -> Result<Self, Diagnostic> {
        match self {
            Self::Created | Self::Suspended => Ok(Self::Running),
            Self::Done => Ok(Self::Done),
            _ => Err(self.state_error("resume", pos)),
        }
    }

    pub fn yield_item(self, pos: Pos) -> Result<Self, Diagnostic> {
        if self == Self::Running { Ok(Self::Suspended) }
        else { Err(self.state_error("yield from", pos)) }
    }

    pub fn finish(self, pos: Pos) -> Result<Self, Diagnostic> {
        if self == Self::Running { Ok(Self::Done) }
        else { Err(self.state_error("finish", pos)) }
    }

    /// For a RUNNING generator, closure first requests cancellation and the
    /// active continuation MUST unwind delegated frames before becoming CLOSED.
    pub fn request_close(self) -> Self {
        match self {
            Self::Running => Self::Closing,
            Self::Closed => Self::Closed,
            Self::Closing => Self::Closing,
            _ => Self::Closed,
        }
    }

    pub fn complete_unwind(self, pos: Pos) -> Result<Self, Diagnostic> {
        if self == Self::Closing { Ok(Self::Closed) }
        else { Err(self.state_error("complete cleanup of", pos)) }
    }
}
