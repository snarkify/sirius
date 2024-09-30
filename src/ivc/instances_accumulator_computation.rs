/// Module name acronym `instances_accumulator_computation` -> `inst_acc_comp`
use std::{iter, num::NonZeroUsize};

use halo2_proofs::{
    arithmetic::Field,
    halo2curves::{
        ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
        CurveAffine,
    },
    plonk::Error as Halo2PlonkError,
};
use tracing::{debug, instrument};

use crate::{
    main_gate::{AssignedValue, MainGateConfig, RegionCtx},
    poseidon::{
        poseidon_circuit::PoseidonChip, random_oracle::ROCircuitTrait, PoseidonHash, ROTrait, Spec,
    },
    util,
};

/// Default value for use in [`Spec`] in this module
pub const T: usize = 5;

/// Default value for use in [`Spec`] in this module
pub const RATE: usize = T - 1;

/// Default value for use in [`Spec`] in this module
pub const R_F: usize = 10;

/// Default value for use in [`Spec`] in this module
pub const R_P: usize = 10;

fn default_spec<F: FromUniformBytes<64>>() -> Spec<F, T, RATE> {
    Spec::new(R_F, R_P)
}

#[instrument(skip_all)]
pub fn get_initial_sc_instances_accumulator<C: CurveAffine>() -> C::ScalarExt
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    absorb_in_sc_instances_accumulator::<C>(&C::ScalarExt::ZERO, &[])
}

#[instrument(skip_all)]
pub fn absorb_in_sc_instances_accumulator<C: CurveAffine>(
    instances_hash_accumulator: &C::ScalarExt,
    instances: &[Vec<C::ScalarExt>],
) -> C::ScalarExt
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    let num_bits = NonZeroUsize::new(<C::Base as PrimeField>::NUM_BITS as usize)
        .expect("unattainably: num_bits can't be zero");

    let hash_in_base: C::Base = PoseidonHash::<C::Base, T, RATE>::new(default_spec())
        .absorb_field_iter(
            iter::once(instances_hash_accumulator)
                .chain(instances.iter().flat_map(|instance| instance.iter()))
                .map(|i| util::fe_to_fe(i).unwrap()),
        )
        .inspect(|buf| debug!("off-circuit buf of instances: {buf:?}"))
        .output::<C::Base>(num_bits);

    util::fe_to_fe(&hash_in_base).unwrap()
}

#[instrument(skip_all)]
pub fn absorb_in_assign_sc_instances_accumulator<F>(
    ctx: &mut RegionCtx<'_, F>,
    config: MainGateConfig<T>,
    folded_instances: &AssignedValue<F>,
    input_instances: &[AssignedValue<F>],
) -> Result<AssignedValue<F>, Halo2PlonkError>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    PoseidonChip::<F, T, RATE>::new(config, default_spec())
        .absorb_base(folded_instances.into())
        .absorb_iter(input_instances.iter())
        .inspect(|buf| debug!("on-circuit buf of instances: {buf:?}"))
        .squeeze(ctx)
}

#[cfg(test)]
mod tests {
    use std::{array, ops::Deref};

    use halo2_proofs::{
        arithmetic::Field,
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        halo2curves::{bn256, CurveAffine},
        plonk::{Circuit, Column, ConstraintSystem, Error as Halo2PlonkError, Instance},
    };

    use super::*;
    use crate::main_gate::{AdviceCyclicAssignor, MainGate};

    #[derive(Debug, Clone)]
    struct ConsistencyCheckCircuit<F: PrimeField> {
        instances_hash_accumulator: F,
        instances: Box<[Vec<F>]>,
    }

    impl<F: PrimeField> ConsistencyCheckCircuit<F> {
        fn new<F2: PrimeField>(instances_hash_accumulator: F2, instances: &[Vec<F2>]) -> Self {
            Self {
                instances_hash_accumulator: util::fe_to_fe(&instances_hash_accumulator).unwrap(),
                instances: instances
                    .iter()
                    .map(|col| col.iter().map(|v| util::fe_to_fe(v).unwrap()).collect())
                    .collect(),
            }
        }
    }

    #[derive(Debug, Clone)]
    struct ConsistencyCheckConfig {
        main_gate_config: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    impl Deref for ConsistencyCheckConfig {
        type Target = MainGateConfig<T>;
        fn deref(&self) -> &Self::Target {
            &self.main_gate_config
        }
    }

    impl<F> Circuit<F> for ConsistencyCheckCircuit<F>
    where
        F: PrimeFieldBits + FromUniformBytes<64>,
    {
        /// This is a configuration object that stores things like columns.
        type Config = ConsistencyCheckConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unreachable!("with using of `SimpleFloorPlanner` this fn not needed")
        }

        /// Configure the step circuit. This method initializes necessary
        /// fixed columns and advice columns
        fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = cs.instance_column();
            cs.enable_equality(instance);

            Self::Config {
                main_gate_config: MainGate::configure(cs),
                instance,
            }
        }

        /// Sythesize the circuit for a computation step and return variable
        /// that corresponds to the output of the step z_{i+1}
        /// this method will be called when we synthesize the IVC_Circuit
        ///
        /// Return `z_out` result
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Halo2PlonkError> {
            let (instances_hash_accumulator, instances) = layouter.assign_region(
                || "assign",
                |region| {
                    let mut assigner = config.advice_cycle_assigner();

                    let Self {
                        instances_hash_accumulator,
                        instances,
                    } = self;

                    let mut region = RegionCtx::new(region, 0);

                    let assigned_instances_hash_accumulator = assigner.assign_next_advice(
                        &mut region,
                        || "instances_hash_accumulator",
                        *instances_hash_accumulator,
                    )?;

                    let assigned_instances = assigner.assign_all_advice(
                        &mut region,
                        || "instances_hash_accumulator",
                        instances.iter().flat_map(|col| col.iter()).copied(),
                    )?;

                    Ok((assigned_instances_hash_accumulator, assigned_instances))
                },
            )?;

            let new_instances_hash_accumulator = layouter.assign_region(
                || "fold",
                |region| {
                    absorb_in_assign_sc_instances_accumulator(
                        &mut RegionCtx::new(region, 0),
                        config.main_gate_config.clone(),
                        &instances_hash_accumulator,
                        &instances,
                    )
                },
            )?;

            layouter.constrain_instance(
                new_instances_hash_accumulator.cell(),
                config.instance,
                0,
            )?;

            Ok(())
        }
    }

    type C = bn256::G1Affine;
    type Scalar = <C as CurveAffine>::ScalarExt;
    type Base = <C as CurveAffine>::Base;

    #[test]
    fn consistency() {
        let mut rand = rand::thread_rng();
        let [acc, i1, i2, i3] = array::from_fn(|_| Scalar::random(&mut rand));

        let expected = absorb_in_sc_instances_accumulator::<C>(&acc, &[vec![i1, i2, i3]]);

        MockProver::run(
            10,
            &ConsistencyCheckCircuit::<Base>::new(acc, &[vec![i1, i2, i3]]),
            vec![vec![util::fe_to_fe(&expected).unwrap()]],
        )
        .unwrap()
        .verify()
        .unwrap();
    }
}
