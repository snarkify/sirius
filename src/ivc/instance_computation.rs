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

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use halo2_proofs::circuit::{floor_planner::single_pass::SingleChipLayouter, Layouter};
    use halo2curves::{bn256, grumpkin};

    type C1 = <bn256::G1 as halo2curves::group::prime::PrimeCurve>::Affine;
    type C2 = <grumpkin::G1 as halo2curves::group::prime::PrimeCurve>::Affine;
    type Base = <C1 as CurveAffine>::Base;
    type Scalar = <C1 as CurveAffine>::ScalarExt;

    use crate::{
        ivc::fold_relaxed_plonk_instance_chip::{
            assign_next_advice_from_point, FoldRelaxedPlonkInstanceChip,
        },
        main_gate::AdviceCyclicAssignor,
        poseidon::{poseidon_circuit::PoseidonChip, PoseidonHash, Spec},
        table::TableData,
    };

    use super::*;

    #[test_log::test]
    fn consistency() {
        let random_oracle_constant = Spec::<Base, 10, 9>::new(10, 10);

        let public_params_hash = C1::random(&mut rand::thread_rng());

        let step = 0x128;
        let z_0 = [Base::from_u128(0x1024); 10];
        let z_i = [Base::from_u128(0x2048); 10];
        let relaxed = RelaxedPlonkInstance::new(2, 10, 10);

        let off_circuit_hash: Base = RandomOracleComputationInstance::<
            '_,
            10,
            C2,
            C1,
            PoseidonHash<<C1 as CurveAffine>::Base, 10, 9>,
        > {
            random_oracle_constant: random_oracle_constant.clone(),
            public_params_hash: &public_params_hash,
            step,
            z_0: &z_0,
            z_i: &z_i,
            relaxed: &relaxed,
        }
        .generate();

        let mut td = TableData::new(15, vec![]);

        let config = td.prepare_assembly(|cs| -> MainGateConfig<10> { MainGate::configure(cs) });

        let on_circuit_hash = SingleChipLayouter::<'_, Base, _>::new(&mut td, vec![])
            .unwrap()
            .assign_region(
                || "test",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let mut advice_columns_assigner = config.advice_cycle_assigner();

                    let public_params_hash = assign_next_advice_from_point(
                        &mut advice_columns_assigner,
                        &mut ctx,
                        &public_params_hash,
                        || "public_params",
                    )
                    .unwrap();

                    let step = advice_columns_assigner
                        .assign_next_advice(&mut ctx, || "step", Base::from_u128(step as u128))
                        .unwrap();

                    let assigned_z_0 = advice_columns_assigner
                        .assign_all_advice(&mut ctx, || "z0", z_0.iter().copied())
                        .map(|inp| inp.try_into().unwrap())
                        .unwrap();

                    let assigned_z_i = advice_columns_assigner
                        .assign_all_advice(&mut ctx, || "zi", z_i.iter().copied())
                        .map(|inp| inp.try_into().unwrap())
                        .unwrap();

                    let assigned_relaxed = FoldRelaxedPlonkInstanceChip::new(
                        relaxed.clone(),
                        NonZeroUsize::new(10).unwrap(),
                        NonZeroUsize::new(10).unwrap(),
                        config.clone(),
                    )
                    .assign_current_relaxed(&mut ctx)
                    .unwrap();

                    AssignedRandomOracleComputationInstance::<
                            PoseidonChip<Base, 10, 9>,
                            10,
                            10,
                            C1,
                        > {
                            random_oracle_constant: random_oracle_constant.clone(),
                            public_params_hash: &public_params_hash,
                            step: &step,
                            z_0: &assigned_z_0,
                            z_i: &assigned_z_i,
                            relaxed: &assigned_relaxed,
                        }
                        .generate(&mut ctx, config.clone())
                },
            )
            .unwrap()
            .value()
            .unwrap()
            .copied()
            .unwrap();

        assert_eq!(on_circuit_hash, off_circuit_hash);
    }
}
