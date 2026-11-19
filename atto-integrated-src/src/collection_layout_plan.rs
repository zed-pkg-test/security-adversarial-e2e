//! Checked *planning only* for physical AoS/SoA/AoSoA scalar record storage.
//!
//! This is not a Wasm allocator, compiled-guest ABI, object graph inversion, or
//! authorization to lower Array<T>. An emitter must independently establish
//! a resolved nominal field schema, ownership and address-space capabilities.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Storage {
    Aos,
    Soa,
    Aosoa(u16),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScalarField {
    pub size: u64,
    pub align: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    pub layout: Storage,
    pub len: u64,
    pub fields: Vec<ScalarField>,
    pub field_offsets: Vec<u64>,
    pub field_strides: Vec<u64>,
    /// AoS record stride or AoSoA block stride. Not applicable to SoA.
    pub row_or_block_stride: u64,
    pub total_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanError {
    InvalidField,
    InvalidBlock,
    SizeOverflow,
}

const MAX_FIELDS: usize = 256;
/// This planner intentionally enforces a 32-bit linear-memory address budget.
const MAX_BYTES: u64 = u32::MAX as u64;

fn aligned(x: u64, align: u64) -> Option<u64> {
    let addend = align.checked_sub(1)?;
    x.checked_add(addend).map(|v| v & !(align - 1))
}

impl Plan {
    pub fn new(layout: Storage, fields: Vec<ScalarField>, len: u64) -> Result<Self, PlanError> {
        if fields.is_empty() || fields.len() > MAX_FIELDS || fields.iter().any(|f|
            f.size == 0 || f.align == 0 || !f.align.is_power_of_two() || f.align > 4096
        ) {
            return Err(PlanError::InvalidField);
        }
        let width = match layout {
            Storage::Aosoa(n) if n == 0 || u64::from(n) > super::collection_layout::MAX_AOSOA_LANES =>
                return Err(PlanError::InvalidBlock),
            Storage::Aosoa(n) => u64::from(n),
            _ => 1,
        };
        let mut offsets = Vec::with_capacity(fields.len());
        let mut strides = Vec::with_capacity(fields.len());
        let max_align = fields.iter().map(|f| f.align).max().unwrap_or(1);
        let mut cursor = 0_u64;
        let result: Result<(u64, u64), PlanError> = (|| {
            for field in &fields {
                let stride = aligned(field.size, field.align).ok_or(PlanError::SizeOverflow)?;
                cursor = aligned(cursor, field.align).ok_or(PlanError::SizeOverflow)?;
                offsets.push(cursor);
                strides.push(stride);
                let count = match layout {
                    Storage::Aos => 1,
                    Storage::Soa => len,
                    Storage::Aosoa(_) => width,
                };
                cursor = cursor.checked_add(stride.checked_mul(count).ok_or(PlanError::SizeOverflow)?)
                    .ok_or(PlanError::SizeOverflow)?;
            }
            match layout {
                Storage::Aos => {
                    let row = aligned(cursor, max_align).ok_or(PlanError::SizeOverflow)?;
                    let bytes = row.checked_mul(len).ok_or(PlanError::SizeOverflow)?;
                    Ok((row, bytes))
                }
                Storage::Soa => Ok((0, cursor)),
                Storage::Aosoa(_) => {
                    let block = aligned(cursor, max_align).ok_or(PlanError::SizeOverflow)?;
                    let blocks = len / width + u64::from(len % width != 0);
                    let bytes = block.checked_mul(blocks).ok_or(PlanError::SizeOverflow)?;
                    Ok((block, bytes))
                }
            }
        })();
        let (row_or_block_stride, total_bytes) = result?;
        if total_bytes > MAX_BYTES {
            return Err(PlanError::SizeOverflow);
        }
        Ok(Self {
            layout, len, fields,
            field_offsets: offsets,
            field_strides: strides,
            row_or_block_stride,
            total_bytes,
        })
    }

    /// Returns the byte offset of an *eligible scalar field*, never a pointer.
    /// Bounds are checked against logical length, not padded block capacity.
    pub fn offset(&self, index: u64, field: usize) -> Option<u64> {
        if index >= self.len || field >= self.fields.len() {
            return None;
        }
        let (base, lane) = match self.layout {
            Storage::Aos => (index.checked_mul(self.row_or_block_stride)?, 0),
            Storage::Soa => (0, index),
            Storage::Aosoa(n) => {
                let lanes = u64::from(n);
                ((index / lanes).checked_mul(self.row_or_block_stride)?, index % lanes)
            }
        };
        let offset = base.checked_add(*self.field_offsets.get(field)?)?
            .checked_add(lane.checked_mul(*self.field_strides.get(field)?)?)?;
        let end = offset.checked_add(self.fields[field].size)?;
        (end <= self.total_bytes).then_some(offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fields() -> Vec<ScalarField> {
        vec![ScalarField { size: 8, align: 8 }, ScalarField { size: 4, align: 4 }]
    }

    #[test]
    fn scalar_columns_are_nonoverlapping_and_addressable() {
        let rows = Plan::new(Storage::Aos, fields(), 5).unwrap();
        assert_eq!(rows.total_bytes, 80);
        assert_eq!(rows.offset(4, 0), Some(64));
        assert_eq!(rows.offset(4, 1), Some(72));

        let cols = Plan::new(Storage::Soa, fields(), 5).unwrap();
        assert_eq!(cols.total_bytes, 60);
        assert_eq!(cols.offset(4, 0), Some(32));
        assert_eq!(cols.offset(4, 1), Some(56));
        assert_eq!(cols.offset(5, 1), None);

        let blocks = Plan::new(Storage::Aosoa(4), fields(), 5).unwrap();
        assert_eq!(blocks.total_bytes, 96);
        assert_eq!(blocks.offset(4, 0), Some(48));
        assert_eq!(blocks.offset(4, 1), Some(80));
        assert_eq!(blocks.offset(5, 0), None); // padded lane is NOT a live element
    }

    #[test]
    fn rejects_invalid_layouts_bounds_and_overflow() {
        assert_eq!(Plan::new(Storage::Aosoa(0), fields(), 1), Err(PlanError::InvalidBlock));
        assert_eq!(Plan::new(Storage::Aosoa(1025), fields(), 1), Err(PlanError::InvalidBlock));
        assert_eq!(Plan::new(Storage::Aos, vec![], 1), Err(PlanError::InvalidField));
        assert_eq!(Plan::new(Storage::Aos, vec![ScalarField { size: 3, align: 3 }], 1), Err(PlanError::InvalidField));
        assert_eq!(Plan::new(Storage::Soa, fields(), u64::MAX), Err(PlanError::SizeOverflow));
        assert_eq!(Plan::new(Storage::Aosoa(16), fields(), u64::MAX), Err(PlanError::SizeOverflow));
        assert_eq!(Plan::new(Storage::Aos, fields(), 0).unwrap().offset(0, 0), None);
    }

    #[test]
    fn all_active_scalar_cells_are_aligned_disjoint_and_in_bounds() {
        let sizes = [
            ScalarField { size: 8, align: 8 },
            ScalarField { size: 9, align: 8 },
            ScalarField { size: 1, align: 1 },
        ];
        for layout in [
            Storage::Aos, Storage::Soa, Storage::Aosoa(1),
            Storage::Aosoa(2), Storage::Aosoa(4), Storage::Aosoa(7),
            Storage::Aosoa(16),
        ] {
            for len in 0..=33_u64 {
                let plan = Plan::new(layout, sizes.to_vec(), len).unwrap();
                let mut ranges = Vec::new();
                for i in 0..len {
                    for (field_index, field) in sizes.iter().enumerate() {
                        let begin = plan.offset(i, field_index).unwrap();
                        assert_eq!(begin % field.align, 0, "{layout:?} len={len}");
                        let end = begin + field.size;
                        assert!(end <= plan.total_bytes);
                        ranges.push((begin, end));
                    }
                }
                ranges.sort_unstable();
                for adjacent in ranges.windows(2) {
                    assert!(adjacent[0].1 <= adjacent[1].0,
                            "overlapping active cells: {layout:?} len={len} {adjacent:?}");
                }
                assert_eq!(plan.offset(len, 0), None);
                assert_eq!(plan.offset(0, sizes.len()), None);
            }
        }
    }

    #[test]
    fn protects_column_alignment_even_for_nonmultiple_sizes() {
        let plan = Plan::new(Storage::Soa,
            vec![ScalarField { size: 9, align: 8 }, ScalarField { size: 1, align: 1 }], 3).unwrap();
        assert_eq!(plan.offset(1, 0), Some(16));
        assert_eq!(plan.offset(2, 0), Some(32));
        assert_eq!(plan.offset(0, 1), Some(48));
    }
}
