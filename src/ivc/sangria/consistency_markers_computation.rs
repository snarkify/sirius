/// Module name acronym `consistency_marker_computation` -> `consistency_comp`
use std::num::NonZeroUsize;

use serde::Serialize;

use super::fold_relaxed_plonk_instance_chip::AssignedRelaxedPlonkInstance;
use crate::{
    constants::NUM_CHALLENGE_BITS,
    ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
    gadgets::{ecc::AssignedPoint, nonnative::bn::big_uint::BigUint},
    halo2curves::CurveAffine,
    main_gate::{AssignedValue, MainGate, MainGateConfig, RegionCtx, WrapValue},
    nifs::sangria::accumulator::{RelaxedPlonkInstance, SCInstancesHashAcc},
    poseidon::{AbsorbInRO, ROCircuitTrait, ROTrait},
    util::{self, ScalarToBase},
};

pub(crate) struct AssignedConsistencyMarkersComputation<
    'l,
    RP,
    const A: usize,
    const T: usize,
    C: CurveAffine,
    const MARKERS_LEN: usize,
> where
    C::Base: FromUniformBytes<64> + PrimeFieldBits,
    RP: ROCircuitTrait<C::Base, Config = MainGateConfig<T>>,
{
    pub random_oracle_constant: RP::Args,
    pub public_params_hash: &'l AssignedPoint<C>,
    pub step: &'l AssignedValue<C::Base>,
    pub z_0: &'l [AssignedValue<C::Base>; A],
    pub z_i: &'l [AssignedValue<C::Base>; A],
    pub relaxed: &'l AssignedRelaxedPlonkInstance<C, MARKERS_LEN>,
}

impl<const A: usize, const T: usize, C: CurveAffine, RO, const MARKERS_LEN: usize>
    AssignedConsistencyMarkersComputation<'_, RO, A, T, C, MARKERS_LEN>
where
    C::Base: FromUniformBytes<64> + PrimeFieldBits,
    RO: ROCircuitTrait<C::Base, Config = MainGateConfig<T>>,
{
    pub fn generate_with_inspect(
        self,
        ctx: &mut RegionCtx<'_, C::Base>,
        config: MainGateConfig<T>,
        inspect: impl FnOnce(&[C::Base]),
    ) -> Result<AssignedValue<C::Base>, halo2_proofs::plonk::Error> {
        let bits = RO::new(config.clone(), self.random_oracle_constant)
            .absorb_point(WrapValue::from_assigned_point(self.public_params_hash))
            .absorb_base(WrapValue::Assigned(self.step.clone()))
            .absorb_iter(self.z_0.iter())
            .absorb_iter(self.z_i.iter().cloned())
            .absorb_iter(self.relaxed.iter_wrap_values())
            .inspect(inspect)
            .squeeze_n_bits(ctx, NUM_CHALLENGE_BITS)?;

        MainGate::new(config.clone()).le_bits_to_num(ctx, &bits)
    }
    pub fn generate(
        self,
        ctx: &mut RegionCtx<'_, C::Base>,
        config: MainGateConfig<T>,
    ) -> Result<AssignedValue<C::Base>, halo2_proofs::plonk::Error> {
        self.generate_with_inspect(ctx, config, |_| {})
    }
}

pub(crate) struct ConsistencyMarkerComputation<'l, const A: usize, C, RP, const MARKERS_LEN: usize>
where
    RP: ROTrait<C::Base>,
    C: CurveAffine + Serialize,
{
    pub random_oracle_constant: RP::Constants,
    pub public_params_hash: &'l C,
    pub step: usize,
    pub z_0: &'l [C::Base; A],
    pub z_i: &'l [C::Base; A],
    pub relaxed: &'l RelaxedPlonkInstance<C, MARKERS_LEN>,
    pub limb_width: NonZeroUsize,
    pub limbs_count: NonZeroUsize,
}

impl<C, RP, const A: usize, const MARKERS_LEN: usize>
    ConsistencyMarkerComputation<'_, A, C, RP, MARKERS_LEN>
where
    RP: ROTrait<C::Base>,
    C: CurveAffine + Serialize,
{
    pub fn generate_with_inspect<F: PrimeField>(self, inspect: impl FnOnce(&[C::Base])) -> F {
        pub struct RelaxedPlonkInstanceBigUintView<'l, C: CurveAffine> {
            pub(crate) W_commitments: &'l Vec<C>,
            pub(crate) E_commitment: &'l C,
            pub(crate) consistency_markers: Vec<BigUint<C::Base>>,
            pub(crate) challenges: Vec<BigUint<C::Base>>,
            pub(crate) u: &'l C::ScalarExt,
            pub(crate) step_circuit_instances_hash_accumulator:
                SCInstancesHashAcc<&'l C::ScalarExt>,
        }

        impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO>
            for RelaxedPlonkInstanceBigUintView<'_, C>
        {
            fn absorb_into(&self, ro: &mut RO) {
                ro.absorb_point_iter(self.W_commitments.iter())
                    .absorb_point(self.E_commitment)
                    .absorb_field_iter(
                        self.consistency_markers
                            .iter()
                            .flat_map(|bn| bn.limbs().iter())
                            .copied(),
                    )
                    .absorb_field_iter(
                        self.challenges
                            .iter()
                            .flat_map(|bn| bn.limbs().iter())
                            .copied(),
                    )
                    .absorb_field(C::scalar_to_base(self.u).unwrap())
                    .absorb(
                        &self
                            .step_circuit_instances_hash_accumulator
                            .as_ref()
                            .map(|v| C::scalar_to_base(v).unwrap()),
                    );
            }
        }

        let RelaxedPlonkInstance {
            W_commitments,
            consistency_markers,
            challenges,
            E_commitment,
            u,
            step_circuit_instances_hash_accumulator,
        } = &self.relaxed;

        let relaxed = RelaxedPlonkInstanceBigUintView {
            W_commitments,
            E_commitment,
            consistency_markers: consistency_markers
                .iter()
                .map(|v| {
                    BigUint::from_f(
                        &C::scalar_to_base(v).unwrap(),
                        self.limb_width,
                        self.limbs_count,
                    )
                    .unwrap()
                })
                .collect(),
            challenges: challenges
                .iter()
                .map(|v| {
                    BigUint::from_f(
                        &C::scalar_to_base(v).unwrap(),
                        self.limb_width,
                        self.limbs_count,
                    )
                    .unwrap()
                })
                .collect(),
            step_circuit_instances_hash_accumulator: step_circuit_instances_hash_accumulator
                .as_ref(),
            u,
        };

        util::fe_to_fe(
            &RP::new(self.random_oracle_constant)
                .absorb_point(self.public_params_hash)
                .absorb_field(C::Base::from_u128(self.step as u128))
                .absorb_field_iter(self.z_0.iter().copied())
                .absorb_field_iter(self.z_i.iter().copied())
                .absorb(&relaxed)
                .inspect(inspect)
                .squeeze::<C::ScalarExt>(NUM_CHALLENGE_BITS),
        )
        .unwrap()
    }

    pub fn generate<F: PrimeField>(self) -> F {
        self.generate_with_inspect(|_| {})
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use halo2_proofs::{
        circuit::{floor_planner::single_pass::SingleChipLayouter, Layouter},
        halo2curves::group::prime::PrimeCurve,
        plonk::ConstraintSystem,
    };
    use tracing_test::traced_test;

    use crate::{
        ff::Field,
        halo2curves::{bn256, grumpkin},
        nifs::sangria,
    };

    type C1 = <bn256::G1 as PrimeCurve>::Affine;
    type C2 = <grumpkin::G1 as PrimeCurve>::Affine;
    type Base = <C1 as CurveAffine>::Base;
    type Scalar = <C1 as CurveAffine>::ScalarExt;

    const K_TABLE_SIZE: usize = 15;

    use super::*;
    use crate::{
        commitment::CommitmentKey,
        ivc::sangria::fold_relaxed_plonk_instance_chip::FoldRelaxedPlonkInstanceChip,
        main_gate::AdviceCyclicAssignor,
        poseidon::{poseidon_circuit::PoseidonChip, PoseidonHash, Spec},
        table::WitnessCollector,
    };

    #[traced_test]
    #[test]
    fn consistency() {
        let random_oracle_constant = Spec::<Base, 10, 9>::new(10, 10);

        let public_params_hash = C1::random(&mut rand::thread_rng());

        let step = 0x128;
        let z_0 = [Base::from_u128(0x1024); 10];
        let z_i = [Base::from_u128(0x2048); 10];
        let relaxed = RelaxedPlonkInstance {
            W_commitments: vec![CommitmentKey::<C1>::default_value(); 10],
            consistency_markers: [Scalar::from_u128(0x67899); 2],
            challenges: vec![Scalar::from_u128(0x123456); 10],
            E_commitment: CommitmentKey::<C1>::default_value(),
            u: Scalar::from_u128(u128::MAX),
            step_circuit_instances_hash_accumulator: SCInstancesHashAcc::Hash(Scalar::from_u128(
                0xaaaaaaaaaaaaa,
            )),
        };

        let off_circuit_hash: Base = ConsistencyMarkerComputation::<
            '_,
            10,
            C1,
            PoseidonHash<<C1 as CurveAffine>::Base, 10, 9>,
            { sangria::CONSISTENCY_MARKERS_COUNT },
        > {
            random_oracle_constant: random_oracle_constant.clone(),
            public_params_hash: &public_params_hash,
            step,
            z_0: &z_0,
            z_i: &z_i,
            relaxed: &relaxed,
            limb_width: NonZeroUsize::new(10).unwrap(),
            limbs_count: NonZeroUsize::new(10).unwrap(),
        }
        .generate();

        let mut cs = ConstraintSystem::default();
        let config = MainGate::<Base, 10>::configure(&mut cs);

        let mut td = WitnessCollector {
            instances: vec![vec![]],
            advice: vec![vec![Base::ZERO.into(); 1 << K_TABLE_SIZE]; cs.num_advice_columns()],
        };

        let on_circuit_hash = SingleChipLayouter::<'_, Base, _>::new(&mut td, vec![])
            .unwrap()
            .assign_region(
                || "test",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let mut advice_columns_assigner = config.advice_cycle_assigner();

                    let public_params_hash = advice_columns_assigner
                        .assign_next_advice_point(&mut ctx, || "public_params", &public_params_hash)
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

                    AssignedConsistencyMarkersComputation::<
                        PoseidonChip<Base, 10, 9>,
                        10,
                        10,
                        C1,
                        { sangria::CONSISTENCY_MARKERS_COUNT },
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
