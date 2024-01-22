use std::{fmt, num::NonZeroUsize};

use ff::{FromUniformBytes, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2curves::CurveAffine;
use serde::Serialize;

use crate::{
    commitment::CommitmentKey,
    digest::{self, DigestToCurve},
    poseidon::ROPair,
};

use super::step_circuit::SynthesizeStepParams;

pub(crate) struct CircuitPublicParams<C, RP>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    RP: ROPair<C::Base>,
{
    pub k: u32,
    pub ck: CommitmentKey<C>,
    pub params: SynthesizeStepParams<C, RP::OnCircuit>,
}

impl<C: fmt::Debug, RP> fmt::Debug for CircuitPublicParams<C, RP>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    RP: ROPair<C::Base>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CircuitPublicParams")
            .field("ck", &self.ck)
            .field("params", &self.params)
            .finish()
    }
}

impl<C, RP> CircuitPublicParams<C, RP>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    RP: ROPair<C::Base>,
{
    fn new(
        k: u32,
        commitment_key: CommitmentKey<C>,
        is_primary_circuit: bool,
        ro_constant: RP::Args,
        limb_width: NonZeroUsize,
        n_limbs: NonZeroUsize,
    ) -> Self {
        Self {
            k,
            ck: commitment_key,
            params: SynthesizeStepParams {
                limb_width,
                n_limbs,
                is_primary_circuit,
                ro_constant,
            },
        }
    }
}

pub struct PublicParams<C1, C2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C1::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    RP1: ROPair<C1::Base>,
    RP2: ROPair<C2::Base>,
{
    pub(crate) primary: CircuitPublicParams<C2, RP2>,
    pub(crate) secondary: CircuitPublicParams<C1, RP1>,
}

impl<C1: fmt::Debug, C2: fmt::Debug, RP1, RP2> fmt::Debug for PublicParams<C1, C2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP1: ROPair<C1::Base>,
    RP2: ROPair<C2::Base>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PublicParams")
            .field("primary", &self.primary)
            .field("secondary", &self.secondary)
            .finish()
    }
}

impl<C1, C2, RP1, RP2> serde::Serialize for PublicParams<C1, C2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    RP1: ROPair<C1::Base>,
    RP2: ROPair<C2::Base>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        #[derive(serde::Serialize)]
        #[serde(bound(serialize = ""))]
        struct Wrapper<'l, C1, C2, RP1, RP2>
        where
            C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
            C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

            C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
            C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

            RP1: ROPair<C1::Base>,
            RP2: ROPair<C2::Base>,
        {
            primary_ck: &'l CommitmentKey<C2>,
            primary_params: &'l SynthesizeStepParams<C2, RP2::OnCircuit>,

            secondary_ck: &'l CommitmentKey<C1>,
            secondary_params: &'l SynthesizeStepParams<C1, RP1::OnCircuit>,
        }

        Wrapper::<'_, C1, C2, RP1, RP2> {
            primary_params: &self.primary.params,
            primary_ck: &self.primary.ck,
            secondary_params: &self.secondary.params,
            secondary_ck: &self.secondary.ck,
        }
        .serialize(serializer)
    }
}

impl<C1, C2, R1, R2> PublicParams<C1, C2, R1, R2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    R1: ROPair<C1::Base>,
    R2: ROPair<C2::Base>,
{
    pub fn new(
        k: u32,
        primary_commitment_key: CommitmentKey<C2>,
        secondary_commitment_key: CommitmentKey<C1>,
        primary_ro_constant: R2::Args,
        secondary_ro_constant: R1::Args,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Self {
        Self {
            primary: CircuitPublicParams::<C2, _>::new(
                k,
                primary_commitment_key,
                true,
                primary_ro_constant,
                limb_width,
                limbs_count_limit,
            ),
            secondary: CircuitPublicParams::<C1, _>::new(
                k,
                secondary_commitment_key,
                false,
                secondary_ro_constant,
                limb_width,
                limbs_count_limit,
            ),
        }
    }

    pub fn digest<C: CurveAffine>(&self) -> Result<C, crate::ivc::Error> {
        digest::DefaultHasher::digest_to_curve(self).map_err(crate::ivc::Error::WhileHash)
    }
}
#[cfg(test)]
mod pp_test {
    use halo2curves::{bn256, grumpkin, CurveExt};

    use bn256::G1 as C1;
    use grumpkin::G1 as C2;

    use super::*;

    type C1Affine = <C1 as halo2curves::group::prime::PrimeCurve>::Affine;
    type C2Affine = <C2 as halo2curves::group::prime::PrimeCurve>::Affine;

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
    const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    type RandomOracle<const T: usize, const RATE: usize> = crate::poseidon::PoseidonRO<T, RATE>;

    type RandomOracleConstant<const T: usize, const RATE: usize, F> =
        <RandomOracle<T, RATE> as ROPair<F>>::Args;

    #[test]
    fn digest() {
        let spec1 = RandomOracleConstant::<5, 4, <C1 as CurveExt>::Base>::new(10, 10);
        let spec2 = RandomOracleConstant::<5, 4, <C2 as CurveExt>::Base>::new(10, 10);

        const K: usize = 5;
        PublicParams::<C1Affine, C2Affine, RandomOracle<5, 4>, RandomOracle<5, 4>>::new(
            K as u32,
            CommitmentKey::setup(K, b"1"),
            CommitmentKey::setup(K, b"2"),
            spec2,
            spec1,
            LIMB_WIDTH,
            LIMBS_COUNT_LIMIT,
        )
        .digest::<C1Affine>()
        .unwrap();
    }
}
