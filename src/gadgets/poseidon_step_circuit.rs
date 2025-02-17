use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::ConstraintSystem,
};
use tracing::*;

use crate::{
    ff::{FromUniformBytes, PrimeFieldBits},
    ivc::{StepCircuit, SynthesisError},
    main_gate::{MainGate, MainGateConfig, RegionCtx, WrapValue},
    poseidon::{poseidon_circuit::PoseidonChip, Spec},
};

/// Input and output size for `StepCircuit` within each step
pub const ARITY: usize = 1;

/// Spec for on-circuit poseidon circuit
const POSEIDON_PERMUTATION_WIDTH: usize = 3;
const POSEIDON_RATE: usize = POSEIDON_PERMUTATION_WIDTH - 1;

pub type CircuitPoseidonSpec<F> = Spec<F, POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE>;

const R_F1: usize = 4;
const R_P1: usize = 3;

#[derive(Clone, Debug)]
pub struct TestPoseidonCircuitConfig {
    pconfig: MainGateConfig<POSEIDON_PERMUTATION_WIDTH>,
}

#[derive(Debug, Clone)]
pub struct TestPoseidonCircuit<F: PrimeFieldBits> {
    repeat_count: usize,
    _p: PhantomData<F>,
}

impl<F: PrimeFieldBits> Default for TestPoseidonCircuit<F> {
    fn default() -> Self {
        Self {
            repeat_count: 1,
            _p: Default::default(),
        }
    }
}

impl<F: PrimeFieldBits> TestPoseidonCircuit<F> {
    pub fn new(repeat_count: usize) -> Self {
        Self {
            repeat_count,
            _p: Default::default(),
        }
    }
}

impl<F: PrimeFieldBits + FromUniformBytes<64>> StepCircuit<ARITY, F> for TestPoseidonCircuit<F> {
    type Config = TestPoseidonCircuitConfig;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let pconfig = MainGate::configure(meta);
        Self::Config { pconfig }
    }

    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_in: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError> {
        let spec = CircuitPoseidonSpec::<F>::new(R_F1, R_P1);

        layouter
            .assign_region(
                || "poseidon hash",
                move |region| {
                    let mut z_i = z_in.clone();
                    let ctx = &mut RegionCtx::new(region, 0);

                    for step in 0..=self.repeat_count {
                        let mut pchip = PoseidonChip::new(config.pconfig.clone(), spec.clone());

                        pchip.update(
                            &z_i.iter()
                                .cloned()
                                .map(WrapValue::Assigned)
                                .collect::<Vec<WrapValue<F>>>(),
                        );

                        info!(
                            "offset for {} hash repeat count is {} (log2 = {})",
                            step,
                            ctx.offset(),
                            (ctx.offset() as f64).log2()
                        );

                        z_i = [pchip.squeeze(ctx).inspect_err(|err| {
                            error!("at step {step}: {err:?}");
                        })?];
                    }

                    info!(
                        "total offset for {} hash repeat count is {} (log2 = {})",
                        self.repeat_count,
                        ctx.offset(),
                        (ctx.offset() as f64).log2()
                    );

                    Ok(z_i)
                },
            )
            .map_err(|err| {
                error!("while synth {err:?}");
                SynthesisError::Halo2(err)
            })
    }
}

