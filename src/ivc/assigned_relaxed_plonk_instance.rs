use std::num::NonZeroUsize;

use ff::{Field, FromUniformBytes, PrimeFieldBits};
use halo2curves::CurveAffine;

use crate::{
    gadgets::nonnative::bn::big_uint::{self, BigUint},
    main_gate::{MainGateConfig, RegionCtx},
    nifs::CrossTermCommits,
    plonk::{PlonkInstance, RelaxedPlonkInstance},
    poseidon::ROCircuitTrait,
};

use super::SynthesisError;

pub(crate) struct FoldRelaxedPlonkInstanceChip<C: CurveAffine> {
    W: C,
    E: C,
    u: C::Scalar,
    X0: BigUint<C::ScalarExt>,
    X1: BigUint<C::ScalarExt>,

    limb_width: NonZeroUsize,
    limbs_count: NonZeroUsize,
}

pub(crate) struct Config {}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("TODO")]
    BigUint(#[from] big_uint::Error),
}

impl<C: CurveAffine> FoldRelaxedPlonkInstanceChip<C>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new_default(limb_width: NonZeroUsize, limbs_count: NonZeroUsize) -> Self {
        Self {
            W: C::default(),
            E: C::default(),
            u: C::Scalar::ZERO,
            X0: BigUint::zero(limb_width),
            X1: BigUint::zero(limb_width),
            limb_width,
            limbs_count,
        }
    }

    pub fn from_instance(
        plonk_instance: PlonkInstance<C>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        Ok(Self {
            W: plonk_instance.W_commitment,
            E: C::default(),
            u: C::Scalar::ONE,
            X0: BigUint::from_f(plonk_instance.instance[0], limb_width, limbs_count)?,
            X1: BigUint::from_f(plonk_instance.instance[1], limb_width, limbs_count)?,
            limb_width,
            limbs_count,
        })
    }

    pub fn from_relaxed(
        relaxed: RelaxedPlonkInstance<C>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        Ok(Self {
            W: relaxed.W_commitment,
            E: relaxed.E_commitment,
            u: C::Scalar::default(),
            X0: BigUint::from_f(relaxed.instance[0], limb_width, limbs_count)?,
            X1: BigUint::from_f(relaxed.instance[1], limb_width, limbs_count)?,
            limb_width,
            limbs_count,
        })
    }

    fn absorb_in_ro(
        &self,
        _ro_circuit: &mut impl ROCircuitTrait<C::Base>,
    ) -> Result<(), SynthesisError> {
        todo!()
    }

    pub fn fold<const T: usize>(
        self,
        region: &mut RegionCtx<C::Scalar>,
        config: &MainGateConfig<T>,
        ro_circuit: impl ROCircuitTrait<C::Base>,
        public_params_commit: &C::Base,
        instance: &PlonkInstance<C>,
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<Self, SynthesisError> {

        ro_circuit.absorb_base(public_params_commit);
        todo!()
    }
}
