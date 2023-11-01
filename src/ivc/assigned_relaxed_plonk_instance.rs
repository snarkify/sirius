use std::num::NonZeroUsize;

use ff::{FromUniformBytes, PrimeFieldBits};
use halo2_proofs::circuit::AssignedCell;
use halo2curves::CurveAffine;

use crate::{
    gadgets::{ecc::AssignedPoint, nonnative::bn::big_nat::BigNat},
    main_gate::RegionCtx,
    nifs::CrossTermCommits,
    plonk::{PlonkInstance, RelaxedPlonkInstance},
    poseidon::ROCircuitTrait,
};

use super::SynthesisError;

/// An Allocated Relaxed R1CS Instance
pub(crate) struct AssignedRelaxedPlonkInstance<C: CurveAffine> {
    pub W: AssignedPoint<C>,
    pub E: AssignedPoint<C>,
    pub u: AssignedCell<C::Base, C::Base>,

    pub X0: BigNat<C::Scalar>,
    pub X1: BigNat<C::Scalar>,
}

impl<C: CurveAffine> AssignedRelaxedPlonkInstance<C>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn from_instance(
        _region: &mut RegionCtx<C::Scalar>,
        _instance: PlonkInstance<C>,
        _limb_width: NonZeroUsize,
        _limbs_count: NonZeroUsize,
    ) -> Result<Self, halo2_proofs::plonk::Error> {
        todo!()
    }

    pub fn new(
        _region: &mut RegionCtx<C::Scalar>,
        _instance: RelaxedPlonkInstance<C>,
        _limb_width: NonZeroUsize,
        _limbs_count: NonZeroUsize,
    ) -> Result<Self, halo2_proofs::plonk::Error> {
        todo!()
    }

    fn absorb_in_ro(
        &self,
        _ro_circuit: &mut impl ROCircuitTrait<C::Base>,
    ) -> Result<(), SynthesisError> {
        todo!()
    }

    pub fn fold(
        self,
        _region: &mut RegionCtx<C::Scalar>,
        _ro_circuit: impl ROCircuitTrait<C::Base>,
        _public_params_commit: &C::Base,
        _instance: &PlonkInstance<C>,
        _cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<Self, SynthesisError> {
        todo!()
    }
}
