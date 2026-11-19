//! Actual owned scalar-record memory for a staged collection-layout runtime.
//!
//! `I64RecordArray` materializes AoS records, SoA field columns and AoSoA
//! blocks. This is an executable RUST storage kernel, NOT Atto-compiled guest
//! execution. Source-level Array remains fail-closed until type checking,
//! lowering, ownership and guest-Wasm emission are integrated.

use crate::collection_layout_plan::{Plan, PlanError, ScalarField, Storage};

/// 16 Wasm pages: upper bound only. A guest emitter must also budget other data.
const MAX_STORAGE_BYTES: u64 = 16 * 65_536;
const MAX_FIELDS: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageError {
    Plan(PlanError),
    Capacity,
    Shape,
    Bounds,
    Overflow,
}
impl From<PlanError> for StorageError {
    fn from(value: PlanError) -> Self { Self::Plan(value) }
}

/// For the first storage profile every nominal struct field is an i64.
/// A single aligned allocation contains ALL active cells, with the physical
/// order determined by Plan. No detached row copies or aliased field vectors.
#[derive(Clone, Debug)]
pub struct I64RecordArray {
    plan: Plan,
    words: Vec<i64>,
}
impl I64RecordArray {
    pub fn new(layout: Storage, field_count: usize, len: u64) -> Result<Self, StorageError> {
        // Prevent an untrusted field_count from allocating before Plan checks it.
        if field_count == 0 || field_count > MAX_FIELDS {
            return Err(StorageError::Plan(PlanError::InvalidField));
        }
        let plan = Plan::new(layout, vec![ScalarField { size: 8, align: 8 }; field_count], len)?;
        if plan.total_bytes > MAX_STORAGE_BYTES { return Err(StorageError::Capacity); }
        let count = usize::try_from(plan.total_bytes / 8).map_err(|_| StorageError::Capacity)?;
        let mut words = Vec::new();
        words.try_reserve_exact(count).map_err(|_| StorageError::Capacity)?;
        words.resize(count, 0);
        Ok(Self { plan, words })
    }

    /// Transpose evaluated logical rows exactly once in row-major input order.
    /// The caller retains responsibility for evaluating guest expressions once.
    pub fn from_rows(layout: Storage, field_count: usize, rows: &[Vec<i64>]) -> Result<Self, StorageError> {
        if rows.iter().any(|r| r.len() != field_count) { return Err(StorageError::Shape); }
        let len = u64::try_from(rows.len()).map_err(|_| StorageError::Capacity)?;
        let mut array = Self::new(layout, field_count, len)?;
        for (row, values) in rows.iter().enumerate() {
            for (field, value) in values.iter().enumerate() {
                array.set(row as u64, field, *value)?;
            }
        }
        Ok(array)
    }

    pub fn plan(&self) -> &Plan { &self.plan }
    pub fn len(&self) -> u64 { self.plan.len }
    pub fn is_empty(&self) -> bool { self.plan.len == 0 }

    fn word_index(&self, row: u64, field: usize) -> Result<usize, StorageError> {
        let offset = self.plan.offset(row, field).ok_or(StorageError::Bounds)?;
        usize::try_from(offset / 8).map_err(|_| StorageError::Bounds)
    }
    pub fn get(&self, row: u64, field: usize) -> Result<i64, StorageError> {
        let index = self.word_index(row, field)?;
        self.words.get(index).copied().ok_or(StorageError::Bounds)
    }
    pub fn set(&mut self, row: u64, field: usize, value: i64) -> Result<(), StorageError> {
        let index = self.word_index(row, field)?;
        *self.words.get_mut(index).ok_or(StorageError::Bounds)? = value;
        Ok(())
    }
    pub fn add_checked(&mut self, row: u64, field: usize, delta: i64) -> Result<(), StorageError> {
        let index = self.word_index(row, field)?;
        let slot = self.words.get_mut(index).ok_or(StorageError::Bounds)?;
        let result = slot.checked_add(delta).ok_or(StorageError::Overflow)?;
        *slot = result;
        Ok(())
    }
    pub fn row(&self, row: u64) -> Result<Row<'_>, StorageError> {
        if row >= self.len() { return Err(StorageError::Bounds); }
        Ok(Row { owner: self, row })
    }
    pub fn row_mut(&mut self, row: u64) -> Result<RowMut<'_>, StorageError> {
        if row >= self.len() { return Err(StorageError::Bounds); }
        Ok(RowMut { owner: self, row })
    }
    pub fn column(&self, field: usize) -> Result<Column<'_>, StorageError> {
        if field >= self.plan.fields.len() { return Err(StorageError::Bounds); }
        Ok(Column { owner: self, field })
    }
    pub fn column_mut(&mut self, field: usize) -> Result<ColumnMut<'_>, StorageError> {
        if field >= self.plan.fields.len() { return Err(StorageError::Bounds); }
        Ok(ColumnMut { owner: self, field })
    }

    /// Internal inspection only. Not a safe AttoLang-level raw-storage API.
    pub fn physical_words(&self) -> &[i64] { &self.words }

    fn soa_range(&self, field: usize) -> Option<std::ops::Range<usize>> {
        if !matches!(self.plan.layout, Storage::Soa) { return None; }
        let begin = usize::try_from(self.plan.field_offsets.get(field)?.checked_div(8)?).ok()?;
        let len = usize::try_from(self.plan.len).ok()?;
        let end = begin.checked_add(len)?;
        (end <= self.words.len()).then_some(begin..end)
    }
}

pub struct Row<'a> { owner: &'a I64RecordArray, row: u64 }
impl Row<'_> {
    pub fn get(&self, field: usize) -> Result<i64, StorageError> {
        self.owner.get(self.row, field)
    }
}
pub struct RowMut<'a> { owner: &'a mut I64RecordArray, row: u64 }
impl RowMut<'_> {
    pub fn get(&self, field: usize) -> Result<i64, StorageError> {
        self.owner.get(self.row, field)
    }
    pub fn set(&mut self, field: usize, value: i64) -> Result<(), StorageError> {
        self.owner.set(self.row, field, value)
    }
    pub fn add_checked(&mut self, field: usize, delta: i64) -> Result<(), StorageError> {
        self.owner.add_checked(self.row, field, delta)
    }
}
pub struct Column<'a> { owner: &'a I64RecordArray, field: usize }
impl Column<'_> {
    pub fn get(&self, row: u64) -> Result<i64, StorageError> {
        self.owner.get(row, self.field)
    }
    /// Only SoA has contiguous field storage; AoS/AoSoA are not rebranded.
    pub fn as_contiguous_slice(&self) -> Option<&[i64]> {
        self.owner.words.get(self.owner.soa_range(self.field)?)
    }
}
pub struct ColumnMut<'a> { owner: &'a mut I64RecordArray, field: usize }
impl ColumnMut<'_> {
    pub fn get(&self, row: u64) -> Result<i64, StorageError> {
        self.owner.get(row, self.field)
    }
    pub fn set(&mut self, row: u64, value: i64) -> Result<(), StorageError> {
        self.owner.set(row, self.field, value)
    }
    pub fn add_checked(&mut self, row: u64, delta: i64) -> Result<(), StorageError> {
        self.owner.add_checked(row, self.field, delta)
    }
    pub fn as_contiguous_slice_mut(&mut self) -> Option<&mut [i64]> {
        let range = self.owner.soa_range(self.field)?;
        self.owner.words.get_mut(range)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn particles() -> Vec<Vec<i64>> { vec![vec![10, 20, 1], vec![30, 40, 2]] }

    #[test]
    fn real_soa_columns_return_fifteen_through_borrowed_row_and_column() {
        let mut array = I64RecordArray::from_rows(Storage::Soa, 3, &particles()).unwrap();
        assert_eq!(array.physical_words(), &[10, 30, 20, 40, 1, 2]);
        array.row_mut(0).unwrap().add_checked(0, 5).unwrap();
        assert_eq!(array.column(0).unwrap().get(0), Ok(15));
        assert_eq!(array.column(0).unwrap().as_contiguous_slice(), Some(&[15, 30][..]));
        assert_eq!(array.physical_words(), &[15, 30, 20, 40, 1, 2]);
    }

    #[test]
    fn aos_is_row_major_and_columns_are_not_a_contiguous_slice() {
        let array = I64RecordArray::from_rows(Storage::Aos, 3, &particles()).unwrap();
        assert_eq!(array.physical_words(), &[10, 20, 1, 30, 40, 2]);
        assert_eq!(array.row(1).unwrap().get(2), Ok(2));
        assert!(array.column(0).unwrap().as_contiguous_slice().is_none());
    }

    #[test]
    fn aosoa_partial_tail_is_padded_but_never_addressable() {
        let rows = (1..=5).map(|x| vec![x, x * 10, x * 100]).collect::<Vec<_>>();
        let mut array = I64RecordArray::from_rows(Storage::Aosoa(4), 3, &rows).unwrap();
        assert_eq!(array.physical_words(), &[
            1, 2, 3, 4, 10, 20, 30, 40, 100, 200, 300, 400,
            5, 0, 0, 0, 50, 0, 0, 0, 500, 0, 0, 0
        ]);
        assert_eq!(array.row(4).unwrap().get(0), Ok(5));
        assert_eq!(array.get(5, 0), Err(StorageError::Bounds));
        assert!(array.column(0).unwrap().as_contiguous_slice().is_none());
        array.column_mut(1).unwrap().set(4, 70).unwrap();
        assert_eq!(array.row(4).unwrap().get(1), Ok(70));
    }

    #[test]
    fn mutable_column_projections_modify_same_storage() {
        let mut array = I64RecordArray::from_rows(Storage::Soa, 3, &particles()).unwrap();
        {
            let mut column = array.column_mut(0).unwrap();
            column.as_contiguous_slice_mut().unwrap()[0] = 77;
        }
        assert_eq!(array.row(0).unwrap().get(0), Ok(77));
    }

    #[test]
    fn rejects_shape_bounds_capacity_and_checked_arithmetic_overflow() {
        assert!(matches!(I64RecordArray::from_rows(Storage::Soa, 3, &[vec![1, 2]]), Err(StorageError::Shape)));
        let mut array = I64RecordArray::new(Storage::Soa, 2, 1).unwrap();
        assert_eq!(array.set(1, 0, 1), Err(StorageError::Bounds));
        assert_eq!(array.get(0, 2), Err(StorageError::Bounds));
        array.set(0, 0, i64::MAX).unwrap();
        assert_eq!(array.add_checked(0, 0, 1), Err(StorageError::Overflow));
        assert_eq!(array.get(0, 0), Ok(i64::MAX));
        assert!(matches!(I64RecordArray::new(Storage::Soa, 3, 200_000), Err(StorageError::Capacity)));
        assert!(matches!(I64RecordArray::new(Storage::Aosoa(0), 3, 1), Err(StorageError::Plan(PlanError::InvalidBlock))));
        assert!(matches!(I64RecordArray::new(Storage::Soa, usize::MAX, 1), Err(StorageError::Plan(PlanError::InvalidField))));
    }

    #[test]
    fn independent_copies_and_empty_arrays() {
        let mut original = I64RecordArray::from_rows(Storage::Soa, 3, &particles()).unwrap();
        let mut copy = original.clone();
        copy.set(0, 0, 99).unwrap();
        assert_eq!(original.get(0, 0), Ok(10));
        original.set(0, 0, -3).unwrap();
        assert_eq!(copy.get(0, 0), Ok(99));
        let empty = I64RecordArray::new(Storage::Aosoa(16), 3, 0).unwrap();
        assert!(empty.is_empty());
        assert_eq!(empty.get(0, 0), Err(StorageError::Bounds));
    }
}
