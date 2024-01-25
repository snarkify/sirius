//! NIFS: Non Interactive Folding Scheme
//!
//! NIFS protocal allow us to fold two identical polynomial relations into one
//! e.g. the polynomial relation can be derived from different way, e.g.:
//! - Custom plonkish gate
//! - The permutation polynomial derived from plonk copy constraints
//!
//! For more details look at:
//! - Paragraph '3. Folding scheme' at [Nova whitepaper](https://eprint.iacr.org/2021/370)
//! - [nifs module](https://github.com/microsoft/Nova/blob/main/src/nifs.rs) at [Nova codebase](https://github.com/microsoft/Nova)
use crate::commitment::CommitmentKey;
use crate::plonk::eval::Error as EvalError;
use crate::poseidon::ROTrait;
use crate::sps::Error as SpsError;
use crate::table::TableData;
use halo2_proofs::arithmetic::CurveAffine;
use rayon::prelude::*;

pub mod vanilla;

/// Trait representing the NIFS folding scheme.
trait FoldingScheme<C: CurveAffine, RO: ROTrait<C::Base>> {
    /// Metadata for prover including hash of public params
    type ProverParam;

    /// Metadata for verifier including hash of public params
    type VerifierParam;

    /// Accumulator contains AccumulatorInstance and the corresponding Witness (e.g. [`RelaxedPlonkWitness`])
    type Accumulator;

    /// The Instance of the Accumulator (e.g. [`RelaxedPlonkInstace`])
    type AccumulatorInstance;

    fn setup_params(
        td: &TableData<C::ScalarExt>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error>;

    /// Perform the folding operation as a prover.
    fn prove(
        ck: &CommitmentKey<C>,
        pp: &Self::ProverParam,
        ro_acc: &mut RO,
        accumulator: Self::Accumulator,
        incoming: Self::Accumulator,
    ) -> Result<Self::Accumulator, Error>;

    /// Perform the folding operation as a verifier.
    fn verify(
        vp: &Self::VerifierParam,
        ro_nark: &mut RO,
        ro_acc: &mut RO,
        accumulator: Self::AccumulatorInstance,
        incoming: Self::AccumulatorInstance,
    ) -> Result<Self::AccumulatorInstance, Error>;
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error(transparent)]
    Eval(#[from] EvalError),
    #[error(transparent)]
    Sps(#[from] SpsError),
}

#[cfg(test)]
mod tests;
