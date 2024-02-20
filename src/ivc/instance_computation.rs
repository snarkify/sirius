use ff::{FromUniformBytes, PrimeField, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2curves::CurveAffine;
use serde::Serialize;

use crate::{
    constants::NUM_CHALLENGE_BITS,
    gadgets::ecc::AssignedPoint,
    main_gate::{AssignedValue, MainGate, MainGateConfig, RegionCtx, WrapValue},
    plonk::RelaxedPlonkInstance,
    poseidon::{ROCircuitTrait, ROTrait},
    util,
};

use super::fold_relaxed_plonk_instance_chip::AssignedRelaxedPlonkInstance;

pub(crate) struct AssignedRandomOracleComputationInstance<
    'l,
    RP,
    const A: usize,
    const T: usize,
    C: CurveAffine,
> where
    C::Base: FromUniformBytes<64> + PrimeFieldBits,
    RP: ROCircuitTrait<C::Base, Config = MainGateConfig<T>>,
{
    pub random_oracle_constant: RP::Args,
    pub public_params_hash: &'l AssignedPoint<C>,
    pub step: &'l AssignedValue<C::Base>,
    pub z_0: &'l [AssignedValue<C::Base>; A],
    pub z_i: &'l [AssignedValue<C::Base>; A],
    pub relaxed: &'l AssignedRelaxedPlonkInstance<C>,
}

impl<'l, const A: usize, const T: usize, C: CurveAffine, RO>
    AssignedRandomOracleComputationInstance<'l, RO, A, T, C>
where
    C::Base: FromUniformBytes<64> + PrimeFieldBits,
    RO: ROCircuitTrait<C::Base, Config = MainGateConfig<T>>,
{
    pub fn generate(
        self,
        ctx: &mut RegionCtx<'_, C::Base>,
        config: MainGateConfig<T>,
    ) -> Result<AssignedValue<C::Base>, halo2_proofs::plonk::Error> {
        let bits = RO::new(config.clone(), self.random_oracle_constant)
            .absorb_point(WrapValue::from_assigned_point(self.public_params_hash))
            .absorb_base(WrapValue::Assigned(self.step.clone()))
            .absorb_iter(self.z_0.iter())
            .absorb_iter(self.z_i.iter().cloned())
            .absorb_iter(self.relaxed.iter_wrap_values())
            .squeeze_n_bits(ctx, NUM_CHALLENGE_BITS)?;

        MainGate::new(config.clone()).le_bits_to_num(ctx, &bits)
    }
}

pub(crate) struct RandomOracleComputationInstance<'l, const A: usize, C1, C2, RP>
where
    RP: ROTrait<C1::Scalar>,
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
{
    pub random_oracle_constant: RP::Constants,
    pub public_params_hash: &'l C2,
    pub step: usize,
    pub z_0: &'l [C1::Scalar; A],
    pub z_i: &'l [C1::Scalar; A],
    pub relaxed: &'l RelaxedPlonkInstance<C2>,
}

impl<'l, C1, C2, RP, const A: usize> RandomOracleComputationInstance<'l, A, C1, C2, RP>
where
    RP: ROTrait<C1::Scalar>,
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
{
    pub fn generate<F: PrimeField>(self) -> F {
        util::fe_to_fe(
            &RP::new(self.random_oracle_constant)
                .absorb_point(self.public_params_hash)
                .absorb_field(C1::Scalar::from_u128(self.step as u128))
                .absorb_field_iter(self.z_0.iter().copied())
                .absorb_field_iter(self.z_0.iter().copied())
                .absorb(self.relaxed)
                .squeeze::<C2>(NUM_CHALLENGE_BITS),
        )
        .unwrap()
    }
}
