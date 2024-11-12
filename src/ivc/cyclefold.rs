use serde::Serialize;

use crate::halo2_proofs::halo2curves::{
    ff::{FromUniformBytes, PrimeFieldBits},
    CurveAffine,
};

pub trait SuitableCurve: CurveAffine<Base = Self::BaseExt> + Serialize {
    type BaseExt: PrimeFieldBits + FromUniformBytes<64> + Serialize;
}

impl<C> SuitableCurve for C
where
    C: CurveAffine + Serialize,
    C::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
{
    type BaseExt = C::Base;
}

/// Circuit for secondary curve, which implements a lightweight version of ecc
pub mod support_circuit {
    use halo2_proofs::plonk::{Column, Instance};

    use crate::{
        gadgets::ecc::EccGate,
        halo2_proofs::{
            circuit::{Chip, Layouter, SimpleFloorPlanner},
            halo2curves::ff::PrimeField,
            plonk::{Circuit, ConstraintSystem, Error as Halo2PlonkError},
        },
    };

    #[derive(Clone, Debug)]
    pub struct Config {
        io: Column<Instance>,
    }

    struct Gate {}

    impl<F: PrimeField> Chip<F> for Gate {
        type Config = Config;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            todo!()
        }

        fn loaded(&self) -> &Self::Loaded {
            todo!()
        }
    }

    impl<F: PrimeField> EccGate<F> for Gate {
        fn new(_config: Self::Config) -> Self {
            todo!()
        }

        fn assign_point<C: halo2_proofs::halo2curves::CurveAffine<Base = F>, AN: Into<String>>(
            &self,
            _ctx: &mut crate::main_gate::RegionCtx<'_, F>,
            _annotation: impl Fn() -> AN,
            _coords: Option<(F, F)>,
        ) -> Result<crate::gadgets::ecc::AssignedPoint<C>, halo2_proofs::plonk::Error> {
            todo!()
        }

        fn conditional_select(
            &self,
            _ctx: &mut crate::main_gate::RegionCtx<'_, F>,
            _lhs: &crate::main_gate::AssignedValue<F>,
            _rhs: &crate::main_gate::AssignedValue<F>,
            _condition: &crate::main_gate::AssignedValue<F>,
        ) -> Result<crate::main_gate::AssignedValue<F>, halo2_proofs::plonk::Error> {
            todo!()
        }

        fn is_infinity_point(
            &self,
            _ctx: &mut crate::main_gate::RegionCtx<'_, F>,
            _x: &crate::main_gate::AssignedValue<F>,
            _y: &crate::main_gate::AssignedValue<F>,
        ) -> Result<crate::main_gate::AssignedValue<F>, halo2_proofs::plonk::Error> {
            todo!()
        }

        fn is_equal_term(
            &self,
            _ctx: &mut crate::main_gate::RegionCtx<'_, F>,
            _a: &crate::main_gate::AssignedValue<F>,
            _b: &crate::main_gate::AssignedValue<F>,
        ) -> Result<crate::main_gate::AssignedValue<F>, halo2_proofs::plonk::Error> {
            todo!()
        }

        unsafe fn unchecked_add<C: halo2_proofs::halo2curves::CurveAffine<Base = F>>(
            &self,
            _ctx: &mut crate::main_gate::RegionCtx<'_, C::Base>,
            _p: &crate::gadgets::ecc::AssignedPoint<C>,
            _q: &crate::gadgets::ecc::AssignedPoint<C>,
        ) -> Result<crate::gadgets::ecc::AssignedPoint<C>, halo2_proofs::plonk::Error> {
            todo!()
        }

        unsafe fn unchecked_double<C: halo2_proofs::halo2curves::CurveAffine<Base = F>>(
            &self,
            _ctx: &mut crate::main_gate::RegionCtx<'_, C::Base>,
            _p: &crate::gadgets::ecc::AssignedPoint<C>,
        ) -> Result<crate::gadgets::ecc::AssignedPoint<C>, halo2_proofs::plonk::Error> {
            todo!()
        }

        fn negate<C: halo2_proofs::halo2curves::CurveAffine<Base = F>>(
            &self,
            _ctx: &mut crate::main_gate::RegionCtx<'_, F>,
            _p: &crate::gadgets::ecc::AssignedPoint<C>,
        ) -> Result<crate::gadgets::ecc::AssignedPoint<C>, halo2_proofs::plonk::Error> {
            todo!()
        }
    }

    pub struct EccCircuit {
        gate: Gate,
    }

    impl<F: PrimeField> Circuit<F> for EccCircuit {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
            todo!()
        }

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl Layouter<F>,
        ) -> Result<(), Halo2PlonkError> {
            todo!()
        }
    }
}

/// Circuit for the primary curve that checks for folding from one to three support-circuit
pub mod delegated_circuit {
    use super::{
        super::sangria::fold_relaxed_plonk_instance_chip::FoldRelaxedPlonkInstanceChip,
        SuitableCurve,
    };
    use crate::{nifs::sangria, poseidon::ROCircuitTrait};

    pub enum Error {}

    pub struct Input<const ARITY: usize, C: SuitableCurve, RO: ROCircuitTrait<C::BaseExt>> {
        pp_digest: C,
        args: RO::Args,
        accumulator: sangria::accumulator::RelaxedPlonkInstance<C>,
        incoming: sangria::accumulator::FoldablePlonkInstance<C>,
        proof: sangria::CrossTermCommits<C>,

        step: usize,
        z_0: [C::BaseExt; ARITY],
        z_i: [C::BaseExt; ARITY],
    }

    pub struct SangriaVerifyChip<
        const ARITY: usize,
        const MAIN_GATE_T: usize,
        C: SuitableCurve,
        RO: ROCircuitTrait<C::BaseExt>,
    > {
        chip: FoldRelaxedPlonkInstanceChip<MAIN_GATE_T, C>,
        input: Input<ARITY, C, RO>,
    }

    impl<
            const ARITY: usize,
            const MAIN_GATE_T: usize,
            C: SuitableCurve,
            RO: ROCircuitTrait<C::BaseExt>,
        > SangriaVerifyChip<ARITY, MAIN_GATE_T, C, RO>
    {
        pub fn fold(&self) -> Result<sangria::accumulator::RelaxedPlonkInstance<C>, Error> {
            todo!()
        }
    }
}

pub mod step_folding_circuit {
    use std::marker::PhantomData;

    use serde::Serialize;

    use super::{public_params::CircuitPublicParams, SuitableCurve};
    use crate::{
        gadgets::ecc::AssignedPoint,
        halo2_proofs::{circuit::floor_planner, plonk::Circuit as Halo2Circuit},
        ivc::{
            protogalaxy::verify_chip::{
                AssignedAccumulatorInstance, AssignedPlonkInstance, AssignedProof,
            },
            StepCircuit,
        },
        main_gate::{AssignedValue, MainGate, MainGateConfig, RegionCtx},
        nifs::protogalaxy,
        plonk::PlonkInstance,
        poseidon::ROCircuitTrait,
    };

    pub struct Input<
        const LENGTH: usize,
        const ARITY: usize,
        C: SuitableCurve,
        RO: ROCircuitTrait<C::BaseExt>,
    > {
        pub pp_digest: C,
        pub args: RO::Args,
        pub accumulator: protogalaxy::AccumulatorInstance<C>,
        pub incoming: [PlonkInstance<C>; LENGTH],
        pub proof: protogalaxy::Proof<C::BaseExt>,

        pub step: usize,
        pub z_0: [C::BaseExt; ARITY],
        pub z_i: [C::BaseExt; ARITY],
    }

    impl<
            const LENGTH: usize,
            const ARITY: usize,
            C: SuitableCurve,
            RO: ROCircuitTrait<C::BaseExt>,
        > Input<LENGTH, ARITY, C, RO>
    {
        fn assign<const MAIN_GATE_T: usize>(
            self,
            _region: &mut RegionCtx<C::BaseExt>,
            _main_gate_config: MainGateConfig<MAIN_GATE_T>,
        ) -> AssignedInput<LENGTH, ARITY, C, RO> {
            todo!()
        }
    }

    pub struct AssignedInput<
        const LENGTH: usize,
        const ARITY: usize,
        C: SuitableCurve,
        RO: ROCircuitTrait<C::BaseExt>,
    > {
        pp_digest: AssignedPoint<C>,
        ro_circuit: RO,
        ro_nark_circuit: RO,
        accumulator: AssignedAccumulatorInstance<C>,
        incoming: [AssignedPlonkInstance<C>; LENGTH],
        proof: AssignedProof<C::BaseExt>,

        step: AssignedValue<C::BaseExt>,
        z_0: [AssignedValue<C::BaseExt>; ARITY],
        z_i: [AssignedValue<C::BaseExt>; ARITY],
    }

    pub struct StepFoldingCircuitConfig<
        const ARITY: usize,
        const MAIN_GATE_T: usize,
        C: SuitableCurve,
        SC: StepCircuit<ARITY, C::BaseExt>,
    >
    where
        SC::Config: Clone,
    {
        sc: SC::Config,
        main: MainGateConfig<MAIN_GATE_T>,
        _p: PhantomData<C::BaseExt>,
    }

    pub struct StepFoldingCircuit<
        'link,
        const LENGTH: usize,
        const ARITY: usize,
        const MAIN_GATE_T: usize,
        C: SuitableCurve,
        SC: StepCircuit<ARITY, C::BaseExt>,
        RO: ROCircuitTrait<C::BaseExt>,
    > {
        pub(crate) sc: &'link SC,
        pub(crate) input: Input<LENGTH, ARITY, C, RO>,
    }

    impl<
            'link,
            const LENGTH: usize,
            const ARITY: usize,
            const MAIN_GATE_T: usize,
            C: SuitableCurve,
            SC: StepCircuit<ARITY, C::BaseExt>,
            RO: ROCircuitTrait<C::BaseExt>,
        > StepFoldingCircuit<'link, LENGTH, ARITY, MAIN_GATE_T, C, SC, RO>
    {
        pub fn without_witness<PairedCircuit: Halo2Circuit<C::Scalar>>(
            _k_table_size: u32,
            _native_num_io: &[usize],
            _step_pp: &'link CircuitPublicParams<C, RO::Args>,
        ) -> Self
        where
            RO::Args: Serialize,
        {
            todo!()
        }
    }

    impl<
            const ARITY: usize,
            const MAIN_GATE_T: usize,
            C: SuitableCurve,
            SC: StepCircuit<ARITY, C::BaseExt>,
        > Clone for StepFoldingCircuitConfig<ARITY, MAIN_GATE_T, C, SC>
    where
        SC::Config: Clone,
    {
        fn clone(&self) -> Self {
            Self {
                sc: self.sc.clone(),
                main: self.main.clone(),
                _p: self._p,
            }
        }
    }

    impl<'l, const L: usize, const A: usize, const T: usize, C, SC, RO> Halo2Circuit<C::BaseExt>
        for StepFoldingCircuit<'l, L, A, T, C, SC, RO>
    where
        C: SuitableCurve,
        SC: StepCircuit<A, C::BaseExt>,
        RO: ROCircuitTrait<C::BaseExt>,
    {
        type Config = StepFoldingCircuitConfig<A, T, C, SC>;
        type FloorPlanner = floor_planner::V1;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<C::BaseExt>) -> Self::Config {
            Self::Config {
                sc: SC::configure(meta),
                main: MainGate::configure(meta),
                _p: PhantomData,
            }
        }

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl halo2_proofs::circuit::Layouter<C::BaseExt>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            todo!()
        }
    }
}

pub mod public_params {
    use std::marker::PhantomData;

    use halo2_proofs::halo2curves::{
        ff::{FromUniformBytes, PrimeFieldBits},
        group::prime::PrimeCurveAffine,
    };
    use serde::Serialize;

    use super::SuitableCurve;
    use crate::{
        ivc::StepCircuit,
        nifs::protogalaxy,
        plonk::{PlonkStructure, PlonkTrace},
        polynomial::univariate::UnivariatePoly,
        poseidon::ROPair,
        prelude::CommitmentKey,
    };

    #[derive(Serialize)]
    #[serde(bound(serialize = ""))]
    pub struct CircuitPublicParams<'key, C, RPArgs>
    where
        C: SuitableCurve,
        RPArgs: Serialize,
    {
        commitment_key: &'key CommitmentKey<C>,
        k_table_size: u32,
        ro_constant: RPArgs,
    }

    impl<'key, C, RPArgs> CircuitPublicParams<'key, C, RPArgs>
    where
        C: SuitableCurve,
        RPArgs: Serialize + Clone,
    {
        pub fn ro_args(&self) -> RPArgs {
            self.ro_constant.clone()
        }

        pub fn initial_proof(&self) -> protogalaxy::Proof<C::Base>
        where
            C::Base: Serialize,
        {
            protogalaxy::Proof {
                poly_F: UnivariatePoly::new_zeroed(10),
                poly_K: UnivariatePoly::new_zeroed(10),
            }
        }
    }

    #[derive(Serialize)]
    #[serde(bound(serialize = ""))]
    pub struct PublicParams<
        'key,
        const ARITY: usize,
        const MAIN_GATE_T: usize,
        C1,
        C2,
        SC,
        RP1,
        RP2,
    >
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar>,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar>,

        SC: StepCircuit<ARITY, C1::BaseExt>,

        C1::BaseExt: PrimeFieldBits + FromUniformBytes<64> + Serialize,
        C2::BaseExt: PrimeFieldBits + FromUniformBytes<64> + Serialize,

        RP1: ROPair<C1::BaseExt>,
        RP2: ROPair<C2::BaseExt>,
    {
        pub(crate) primary: CircuitPublicParams<'key, C1, RP1::Args>,
        pub(crate) secondary: CircuitPublicParams<'key, C2, RP2::Args>,
        _p: PhantomData<(C1, C2, SC, RP1, RP2)>,
    }

    impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C1, C2, SC, RP1, RP2>
        PublicParams<'key, ARITY, MAIN_GATE_T, C1, C2, SC, RP1, RP2>
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar>,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar>,

        SC: StepCircuit<ARITY, C1::BaseExt>,

        C1::BaseExt: PrimeFieldBits + FromUniformBytes<64> + Serialize,
        C2::BaseExt: PrimeFieldBits + FromUniformBytes<64> + Serialize,

        RP1: ROPair<C1::BaseExt>,
        RP2: ROPair<C2::BaseExt>,
    {
        pub fn new(
            _step_circuit: &SC,
            primary: CircuitPublicParams<'key, C1, RP1::Args>,
            secondary: CircuitPublicParams<'key, C2, RP2::Args>,
        ) -> Self {
            Self {
                primary,
                secondary,
                _p: PhantomData,
            }
        }

        pub fn initial_plonk_trace(&self) -> PlonkTrace<C1> {
            todo!()
        }

        pub fn digest(&self) -> C1 {
            todo!()
        }

        pub fn plonk_structure1(&self) -> PlonkStructure<C1::Base> {
            todo!()
        }

        pub fn plonk_structure2(&self) -> PlonkStructure<C2::Base> {
            todo!()
        }
    }
}

pub mod incrementally_verifiable_computation {
    use std::marker::PhantomData;

    use serde::Serialize;

    use super::{public_params::PublicParams, SuitableCurve};
    use crate::{
        halo2_proofs::halo2curves::{
            ff::{FromUniformBytes, PrimeFieldBits},
            group::prime::PrimeCurveAffine,
        },
        ivc::{
            cyclefold::step_folding_circuit::{Input, StepFoldingCircuit},
            StepCircuit,
        },
        nifs::protogalaxy::{AccumulatorArgs, ProtoGalaxy, ProverParam},
        poseidon::{random_oracle::ROTrait, ROPair},
    };

    pub struct IVC<const ARITY: usize, const MAIN_GATE_T: usize, C1, C2, SC>
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar>,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar>,

        SC: StepCircuit<ARITY, C1::Base>,
    {
        _p: PhantomData<(C1, C2, SC)>,
    }

    impl<const ARITY: usize, const MAIN_GATE_T: usize, C1, C2, SC> IVC<ARITY, MAIN_GATE_T, C1, C2, SC>
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar>,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar>,
        C1::BaseExt: PrimeFieldBits + FromUniformBytes<64> + Serialize,
        C2::BaseExt: PrimeFieldBits + FromUniformBytes<64> + Serialize,
        SC: StepCircuit<ARITY, C1::Base>,
    {
        pub fn new<RP1, RP2>(
            pp: &PublicParams<ARITY, MAIN_GATE_T, C1, C2, SC, RP1, RP2>,
            primary: &SC,
            input_z_0: [C1::Base; ARITY],
        ) -> Self
        where
            RP1: ROPair<C1::BaseExt>,
            RP2: ROPair<C2::BaseExt>,
        {
            let initial_plonk_trace = pp.initial_plonk_trace();

            let accumulator = ProtoGalaxy::<C1, 2>::new_accumulator(
                AccumulatorArgs::from(&pp.plonk_structure1()),
                &ProverParam::<C1> {
                    S: pp.plonk_structure1().clone(),
                    pp_digest: pp.digest(),
                },
                &mut RP1::OffCircuit::new(pp.primary.ro_args()),
            );

            let sfc = StepFoldingCircuit::<'_, 1, ARITY, MAIN_GATE_T, C1, SC, RP1::OnCircuit> {
                sc: primary,
                input: Input::<1, ARITY, C1, RP1::OnCircuit> {
                    pp_digest: pp.digest(),
                    args: pp.primary.ro_args(),
                    accumulator: accumulator.into(),
                    incoming: [initial_plonk_trace.u],
                    step: 0,
                    z_0: input_z_0,
                    z_i: input_z_0,
                    proof: pp.primary.initial_proof(),
                },
            };

            todo!()
        }

        pub fn fold_step<RP1, RP2>(
            _pp: &PublicParams<ARITY, MAIN_GATE_T, C1, C2, SC, RP1, RP2>,
            _primary: &SC,
        ) -> Self
        where
            RP1: ROPair<C1::BaseExt>,
            RP2: ROPair<C2::BaseExt>,
        {
            todo!()
        }

        pub fn verify<RP1, RP2>(
            _pp: &PublicParams<ARITY, MAIN_GATE_T, C1, C2, SC, RP1, RP2>,
        ) -> Self
        where
            RP1: ROPair<C1::BaseExt>,
            RP2: ROPair<C2::BaseExt>,
        {
            todo!()
        }
    }
}
