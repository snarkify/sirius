use std::mem;

use halo2_frontend::plonk::TableError;
use halo2_proofs::plonk::ErrorFront as Error;

/// Wrapper for [`halo2_proofs::plonk::ErrorFront`] to
/// impl [`PartialEq`] & [`Eq`] and be able to use
/// it in [`assert_eq`] and other comparisons
#[derive(Debug)]
pub struct Halo2PlonkError(halo2_proofs::plonk::ErrorFront);

impl PartialEq for Halo2PlonkError {
    fn eq(&self, other: &Self) -> bool {
        let Self(err) = self;
        let Self(other_err) = other;

        match (err, other_err) {
            (
                Error::NotEnoughRowsAvailable {
                    current_k: self_current_k,
                },
                Error::NotEnoughRowsAvailable {
                    current_k: other_current_k,
                },
            ) => self_current_k == other_current_k,
            (Error::ColumnNotInPermutation(self_col), Error::ColumnNotInPermutation(other_col)) => {
                self_col == other_col
            }
            (Error::TableError(left), Error::TableError(right)) => match (left, right) {
                (TableError::ColumnNotAssigned(l), TableError::ColumnNotAssigned(r)) => l.eq(r),
                (TableError::UsedColumn(l), TableError::UsedColumn(r)) => l.eq(r),
                (
                    TableError::UnevenColumnLengths(l1, l2),
                    TableError::UnevenColumnLengths(r1, r2),
                ) => (l1, l2).eq(&(r1, r2)),
                (
                    TableError::OverwriteDefault(l1, l2, l3),
                    TableError::OverwriteDefault(r1, r2, r3),
                ) => (l1, l2, l3).eq(&(r1, r2, r3)),
                _ => false,
            },
            (self_err, other_err) => mem::discriminant(self_err) == mem::discriminant(other_err),
        }
    }
}
impl Eq for Halo2PlonkError {}
impl From<halo2_proofs::plonk::ErrorFront> for Halo2PlonkError {
    fn from(value: halo2_proofs::plonk::ErrorFront) -> Self {
        Self(value)
    }
}
