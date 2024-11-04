pub mod step_circuit;

pub mod sangria;
pub use sangria::{
    fold_relaxed_plonk_instance_chip, incrementally_verifiable_computation, step_folding_circuit,
};

pub mod protogalaxy;

pub mod cyclefold {
    pub mod delegated_circuit {}

    pub mod step_folding_circuit {
        use std::marker::PhantomData;

        use halo2_proofs::{
            circuit::floor_planner,
            halo2curves::{
                ff::{FromUniformBytes, PrimeFieldBits},
                CurveAffine,
            },
            plonk::Circuit as Halo2Circuit,
        };

        use crate::{
            ivc::StepCircuit,
            main_gate::{MainGate, MainGateConfig},
            nifs::protogalaxy,
            plonk::PlonkInstance,
            poseidon::ROCircuitTrait,
        };

        pub trait SuitableCurve: CurveAffine {
            type BaseExt: PrimeFieldBits + FromUniformBytes<64>;
        }

        impl<C> SuitableCurve for C
        where
            C: CurveAffine,
            C::Base: PrimeFieldBits + FromUniformBytes<64>,
        {
            type BaseExt = C::Base;
        }

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

            fn configure(
                meta: &mut halo2_proofs::plonk::ConstraintSystem<C::BaseExt>,
            ) -> Self::Config {
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

    pub mod incrementally_verifiable_computation {
        use std::marker::PhantomData;

        use halo2_proofs::halo2curves::{
            ff::{FromUniformBytes, PrimeFieldBits},
            group::prime::PrimeCurveAffine,
            CurveAffine,
        };

        use crate::ivc::StepCircuit;

        pub struct IVC<const ARITY: usize, C1, C2, SC>
        where
            C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
            C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
            SC: StepCircuit<ARITY, C1::Scalar>,
            C1::Scalar: PrimeFieldBits + FromUniformBytes<64>,
            C2::Scalar: PrimeFieldBits + FromUniformBytes<64>,
        {
            _p: PhantomData<(C1, C2, SC)>,
        }
    }
}

mod consistency_markers_computation;
pub mod instances_accumulator_computation;
mod public_params;

pub use halo2_proofs::circuit::SimpleFloorPlanner;
pub use incrementally_verifiable_computation::*;
pub use public_params::{CircuitPublicParamsInput, PublicParams};
