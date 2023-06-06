use halo2_proofs::circuit::AssignedCell;
pub mod ecc;
pub(crate) mod util;


pub type AssignedValue<F> = AssignedCell<F, F>;
