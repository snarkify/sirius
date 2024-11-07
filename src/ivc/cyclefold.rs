use crate::halo2_proofs::halo2curves::{
    ff::{FromUniformBytes, PrimeFieldBits},
    CurveAffine,
};

pub trait SuitableCurve: CurveAffine<Base = Self::BaseExt> {
    type BaseExt: PrimeFieldBits + FromUniformBytes<64>;
}

impl<C> SuitableCurve for C
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    type BaseExt = C::Base;
}

/// Circuit for secondary curve, which implements a lightweight version of ecc
pub mod support_circuit {}

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

    use halo2_proofs::{circuit::floor_planner, plonk::Circuit as Halo2Circuit};

    use super::SuitableCurve;
    use crate::{
        gadgets::ecc::AssignedPoint,
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
        pp_digest: C,
        args: RO::Args,
        accumulator: protogalaxy::AccumulatorInstance<C>,
        incoming: [PlonkInstance<C>; LENGTH],
        proof: protogalaxy::Proof<C::BaseExt>,

        step: usize,
        z_0: [C::BaseExt; ARITY],
        z_i: [C::BaseExt; ARITY],
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

    pub struct StepFoldingCircuit<
        'link,
        const LENGTH: usize,
        const ARITY: usize,
        const MAIN_GATE_T: usize,
        C: SuitableCurve,
        SC: StepCircuit<ARITY, C::BaseExt>,
        RO: ROCircuitTrait<C::BaseExt>,
    > {
        sc: &'link SC,
        input: Input<LENGTH, ARITY, C, RO>,
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
    use crate::{ivc::StepCircuit, poseidon::ROPair};

    #[derive(Serialize)]
    #[serde(bound(serialize = ""))]
    pub struct PublicParams<
        const ARITY1: usize,
        const ARITY2: usize,
        const MAIN_GATE_T: usize,
        C1,
        C2,
        SC1,
        SC2,
        RP1,
        RP2,
    >
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

        C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
        C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

        SC1: StepCircuit<ARITY1, C1::BaseExt>,
        SC2: StepCircuit<ARITY2, C2::BaseExt>,

        RP1: ROPair<C1::BaseExt>,
        RP2: ROPair<C2::BaseExt>,
    {
        _p: PhantomData<(C1, C2, SC1, SC2, RP1, RP2)>,
    }

    impl<
            const ARITY1: usize,
            const ARITY2: usize,
            const MAIN_GATE_T: usize,
            C1,
            C2,
            SC1,
            SC2,
            RP1,
            RP2,
        > PublicParams<ARITY1, ARITY2, MAIN_GATE_T, C1, C2, SC1, SC2, RP1, RP2>
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

        C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
        C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

        SC1: StepCircuit<ARITY1, C1::BaseExt>,
        SC2: StepCircuit<ARITY2, C2::BaseExt>,

        RP1: ROPair<C1::BaseExt>,
        RP2: ROPair<C2::BaseExt>,
    {
    }
}

pub mod incrementally_verifiable_computation {
    use std::marker::PhantomData;

    use halo2_proofs::halo2curves::group::prime::PrimeCurveAffine;

    use super::SuitableCurve;
    use crate::ivc::StepCircuit;

    pub struct IVC<const ARITY: usize, C1, C2, SC>
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar>,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar>,
        SC: StepCircuit<ARITY, C1::Base>,
    {
        _p: PhantomData<(C1, C2, SC)>,
    }

    impl<const ARITY: usize, C1, C2, SC> IVC<ARITY, C1, C2, SC>
    where
        C1: SuitableCurve<BaseExt = <C2 as PrimeCurveAffine>::Scalar>,
        C2: SuitableCurve<BaseExt = <C1 as PrimeCurveAffine>::Scalar>,
        SC: StepCircuit<ARITY, C1::Base>,
    {
    }
}
