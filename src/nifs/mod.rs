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
    plonk::{eval::Error as EvalError, PlonkStructure},
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

    /// Type representing the constraint system execution trace
    /// By default can use type [`crate::plonk::PlonkTrace`]
    type Trace;

    /// Type representing the constraint system instance
    /// By default can use type [`crate::plonk::PlonkInstance`]
    type Instance;

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
        instances: &[Vec<C::ScalarExt>],
        witness: &[Vec<C::ScalarExt>],
        pp: &Self::ProverParam,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<Self::Trace, Self::Error>;

    /// Perform the folding operation as a prover.
    fn prove(
        ck: &CommitmentKey<C>,
        pp: &Self::ProverParam,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: Self::Accumulator,
        incoming: &[Self::Trace; L],
    ) -> Result<(Self::Accumulator, Self::Proof), Self::Error>;

    /// Perform the folding operation as a verifier.
    fn verify(
        vp: &Self::VerifierParam,
        ro_nark: &mut impl ROTrait<C::Base>,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Self::AccumulatorInstance,
        incoming: &[Self::Instance; L],
        proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Self::Error>;
}

/// Trait representing the requirements for checking the satisfaction of
/// accumulation relations in a Non-Interactive Folding Scheme (NIFS).
pub trait VerifyAccumulation<C: CurveAffine, const L: usize = 1>: FoldingScheme<C, L> {
    type VerifyError;

    /// Checks if the given accumulator satisfies the specified polynomial
    /// relations.
    ///
    /// This method verifies the accumulation of polynomial relations to ensure
    /// they adhere to the constraints defined in the folding scheme.
    fn is_sat_accumulation(
        S: &PlonkStructure<C::ScalarExt>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Self::VerifyError>;

    /// Checks if the permutation relations in the accumulator are satisfied.
    ///
    /// This method ensures that the permutation relations, which could
    /// originate from copy constraints in the PLONK protocol, are correctly
    /// enforced in the accumulator.
    fn is_sat_permutation(
        S: &PlonkStructure<C::ScalarExt>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Self::VerifyError>;

    /// Checks if the witness commitments in the accumulator are satisfied.
    ///
    /// This method ensures that the commitments to the witness data are
    /// correctly enforced in the accumulator.
    fn is_sat_witness_commit(
        ck: &CommitmentKey<C>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Self::VerifyError>;

    /// Checks that the accumulator for instance columns (public input) is correct
    ///
    /// This method ensure that the instance accumulator in `acc` really contains these public
    /// inputs
    fn is_sat_pub_instances(
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
        pub_instances: &[Vec<Vec<C::ScalarExt>>],
    ) -> Result<(), Self::VerifyError>;
}

/// Trait defining a complete satisfaction check for accumulators
///
/// This trait combines multiple specific satisfaction checks into one method
/// for comprehensive verification of accumulators.
pub trait IsSatAccumulator<C: CurveAffine, const L: usize = 1>: VerifyAccumulation<C, L> {
    /// Comprehensive satisfaction check for an accumulator.
    ///
    /// This method runs multiple checks ([`IsSatAccumulation::is_sat_accumulation`],
    /// [`IsSatAccumulation::is_sat_permutation`], [`IsSatAccumulation::is_sat_witness_commit`]) to
    /// ensure that all required constraints are satisfied in the accumulator.
    fn is_sat(
        ck: &CommitmentKey<C>,
        S: &PlonkStructure<C::ScalarExt>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
        pub_instances: &[Vec<Vec<C::ScalarExt>>],
    ) -> Result<(), Vec<Self::VerifyError>> {
        let mut errors = vec![];

        if let Err(err) = Self::is_sat_accumulation(S, acc) {
            errors.push(err);
        }

        if let Err(err) = Self::is_sat_permutation(S, acc) {
            errors.push(err);
        }

        if let Err(err) = Self::is_sat_witness_commit(ck, acc) {
            errors.push(err);
        }

        if let Err(err) = Self::is_sat_pub_instances(acc, pub_instances) {
            errors.push(err);
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl<C: CurveAffine, const L: usize, F: VerifyAccumulation<C, L>> IsSatAccumulator<C, L> for F {}

#[cfg(test)]
pub(crate) mod tests;
