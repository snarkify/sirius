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
use halo2_proofs::{arithmetic::CurveAffine, plonk::Error as Halo2Error};
use rayon::prelude::*;

use crate::{
    commitment::{self, CommitmentKey},
    plonk::{eval::Error as EvalError, PlonkInstance, PlonkStructure, PlonkTrace},
    poseidon::ROTrait,
    sps::Error as SpsError,
};

pub mod protogalaxy;
pub mod vanilla;

/// Trait representing the NIFS folding scheme.
pub trait FoldingScheme<C: CurveAffine, const L: usize = 1> {
    type Error;

    /// Metadata for prover including hash of public params
    type ProverParam;

    /// Metadata for verifier including hash of public params
    type VerifierParam;

    /// Accumulator contains AccumulatorInstance and the corresponding Witness (e.g. [`RelaxedPlonkWitness`])
    type Accumulator;

    /// The Instance of the Accumulator (e.g. [`RelaxedPlonkInstace`])
    type AccumulatorInstance;

    /// The proof send from prover to verifier
    type Proof;

    fn setup_params(
        pp_digest: C,
        S: PlonkStructure<C::ScalarExt>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Self::Error>;

    fn generate_plonk_trace(
        ck: &CommitmentKey<C>,
        instance: &[C::ScalarExt],
        witness: &[Vec<C::ScalarExt>],
        pp: &Self::ProverParam,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<PlonkTrace<C>, Self::Error>;

    /// Perform the folding operation as a prover.
    fn prove(
        ck: &CommitmentKey<C>,
        pp: &Self::ProverParam,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: Self::Accumulator,
        incoming: &[PlonkTrace<C>; L],
    ) -> Result<(Self::Accumulator, Self::Proof), Self::Error>;

    /// Perform the folding operation as a verifier.
    fn verify(
        vp: &Self::VerifierParam,
        ro_nark: &mut impl ROTrait<C::Base>,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Self::AccumulatorInstance,
        incoming: &[PlonkInstance<C>; L],
        proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Self::Error>;
}

#[cfg(test)]
mod tests;
