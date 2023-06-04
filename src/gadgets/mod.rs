use halo2_proofs::circuit::AssignedCell;
pub mod ecc;
pub(crate) mod utils;


pub type AssignedValue<F> = AssignedCell<F, F>;
