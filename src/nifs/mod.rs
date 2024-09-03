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

pub trait IsSatAccumulator<C: CurveAffine, const L: usize = 1>: FoldingScheme<C, L> {
    type VerifyError;

    fn is_sat_acc(
        S: &PlonkStructure<C::ScalarExt>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Self::VerifyError>;

    fn is_sat_perm(
        S: &PlonkStructure<C::ScalarExt>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Self::VerifyError>;

    fn is_sat_commit(
        ck: &CommitmentKey<C>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Self::VerifyError>;

    fn is_sat(
        ck: &CommitmentKey<C>,
        S: &PlonkStructure<C::ScalarExt>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Vec<Self::VerifyError>> {
        let mut errors = vec![];
        if let Err(err) = Self::is_sat_acc(S, acc) {
            errors.push(err);
        }
        if let Err(err) = Self::is_sat_perm(S, acc) {
            errors.push(err);
        }

        if let Err(err) = Self::is_sat_commit(ck, acc) {
            errors.push(err);
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

#[cfg(test)]
pub(crate) mod tests;
