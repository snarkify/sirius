use std::mem;

use halo2_proofs::plonk::Error;

/// Wrapper for [`halo2_proofs::plonk::Error`] to
/// impl [`PartialEq`] & [`Eq`] and be able to use
/// it in [`assert_eq`] and other comparisons
#[derive(Debug)]
pub struct Halo2PlonkError(halo2_proofs::plonk::Error);

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
            (Error::Transcript(_), Error::Transcript(_)) => false,
            (self_err, other_err) => mem::discriminant(self_err) == mem::discriminant(other_err),
        }
    }
}
impl Eq for Halo2PlonkError {}
impl From<halo2_proofs::plonk::Error> for Halo2PlonkError {
    fn from(value: halo2_proofs::plonk::Error) -> Self {
        Self(value)
    }
}
