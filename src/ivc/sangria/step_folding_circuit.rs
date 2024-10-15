/// Module name acronym `StepFoldingCircuit` -> `sfc`
use std::{fmt, iter, num::NonZeroUsize};

use halo2_proofs::{
    circuit::{floor_planner, Layouter, Value},
    plonk::{Circuit, Column, ConstraintSystem, Error as Halo2PlonkError, Instance},
};
use itertools::Itertools;
use serde::Serialize;
use tracing::*;

use crate::{
    ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits},
    halo2curves::CurveAffine,
    ivc::{
        consistency_markers_computation::AssignedConsistencyMarkersComputation,
        fold_relaxed_plonk_instance_chip::{
            AssignedRelaxedPlonkInstance, FoldRelaxedPlonkInstanceChip, FoldResult,
        },
        StepCircuit,
    },
    main_gate::{AdviceCyclicAssignor, MainGate, MainGateConfig, RegionCtx},
    nifs::sangria::{
        self,
        accumulator::{FoldablePlonkInstance, RelaxedPlonkInstance},
    },
    plonk::PlonkInstance,
    poseidon::ROCircuitTrait,
    table::ConstraintSystemMetainfo,
};

#[derive(Serialize)]
#[serde(bound(serialize = "RO::Args: Serialize"))]
pub(crate) struct StepParams<F, RO>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
    RO: ROCircuitTrait<F>,
{
    limb_width: NonZeroUsize,
    limbs_count: NonZeroUsize,
    ro_constant: RO::Args,
}

impl<F, RO> StepParams<F, RO>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
    RO: ROCircuitTrait<F>,
{
    pub fn new(limb_width: NonZeroUsize, limbs_count: NonZeroUsize, ro_constant: RO::Args) -> Self {
        Self {
            limb_width,
            limbs_count,
            ro_constant,
        }
    }

    pub fn limb_width(&self) -> NonZeroUsize {
        self.limb_width
    }
    pub fn limbs_count(&self) -> NonZeroUsize {
        self.limbs_count
    }
    pub fn ro_constant(&self) -> &RO::Args {
        &self.ro_constant
    }
}

impl<F, RO> fmt::Debug for StepParams<F, RO>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
    RO: ROCircuitTrait<F>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SynthesizeStepParams")
            .field("limb_width", &self.limb_width)
            .field("n_limbs", &self.limbs_count)
            .field("ro_constant", &self.ro_constant)
            .finish()
    }
}

#[derive(Clone)]
pub(crate) struct StepInputs<'link, const ARITY: usize, C, RO>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C: CurveAffine,
    RO: ROCircuitTrait<C::Base>,
{
    pub step: C::Base,
    pub step_pp: &'link StepParams<C::Base, RO>,
    pub public_params_hash: C,

    pub z_0: [C::Base; ARITY],
    /// Output of previous step & input of current one
    pub z_i: [C::Base; ARITY],

    // TODO docs
    pub U: RelaxedPlonkInstance<C>,

    // TODO docs
    pub u: FoldablePlonkInstance<C>,

    // TODO docs
    pub cross_term_commits: Vec<C>,

    pub step_circuit_instances: Vec<Vec<C::Base>>,
}

impl<'link, const ARITY: usize, C: fmt::Debug, RO> fmt::Debug for StepInputs<'link, ARITY, C, RO>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C: CurveAffine,
    RO: ROCircuitTrait<C::Base>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StepInputs")
            .field("step", &self.step)
            .field("step_pp", &self.step_pp)
            .field("public_params_hash", &self.public_params_hash)
            .field("z_0", &self.z_0)
            .field("z_i", &self.z_i)
            .field("U", &self.U)
            .field("u", &self.u)
            .field("cross_term_commits", &self.cross_term_commits)
            .field("step_circuit_instances", &self.step_circuit_instances)
            .finish()
    }
}

impl<'link, const ARITY: usize, C, RO> StepInputs<'link, ARITY, C, RO>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C: CurveAffine,
    RO: ROCircuitTrait<C::Base>,
{
    pub fn num_io(&self) -> Box<[usize]> {
        iter::once(sangria::CONSISTENCY_MARKERS_COUNT)
            .chain(
                self.step_circuit_instances
                    .iter()
                    .map(|instance| instance.len()),
            )
            .collect()
    }

    pub fn without_witness<PairedCircuit: Circuit<C::Scalar>>(
        k_table_size: u32,
        native_num_io: &[usize],
        paired_num_io: &[usize],
        step_pp: &'link StepParams<C::Base, RO>,
    ) -> Self {
        let mut cs = ConstraintSystem::<C::Scalar>::default();

        PairedCircuit::configure(&mut cs);

        let ConstraintSystemMetainfo {
            num_challenges,
            round_sizes,
            folding_degree,
            ..
        } = ConstraintSystemMetainfo::build(k_table_size as usize, &cs);

        let Some((consistency_markers, step_circuit_instances)) = native_num_io.split_first()
        else {
            panic!("Empty instances not expected, because consistency markers");
        };

        assert_eq!(consistency_markers, &sangria::CONSISTENCY_MARKERS_COUNT);

        Self {
            step: C::Base::ZERO,
            step_pp,
            public_params_hash: C::identity(),
            z_0: [C::Base::ZERO; ARITY],
            z_i: [C::Base::ZERO; ARITY],
            U: RelaxedPlonkInstance::new(num_challenges, round_sizes.len()),
            u: FoldablePlonkInstance::new(PlonkInstance::new(
                paired_num_io,
                num_challenges,
                round_sizes.len(),
            ))
            .expect("you can't use plonk instance without consistency markers"),
            step_circuit_instances: step_circuit_instances
                .iter()
                .map(|len| vec![C::Base::ZERO; *len])
                .collect(),
            cross_term_commits: vec![C::identity(); folding_degree.saturating_sub(1)],
        }
    }
}

pub struct StepConfig<const ARITY: usize, F: PrimeField, SP: StepCircuit<ARITY, F>, const T: usize>
{
    /// This column stores in the 0 row a hash checking the consistency of the input data, and in
    /// the the 1 row hash checks the consistency of the output data
    pub consistency_marker: Column<Instance>,
    pub step_config: SP::Config,
    pub main_gate_config: MainGateConfig<T>,
    pub step_circuit_instances: Box<[Column<Instance>]>,
}

impl<const ARITY: usize, F: PrimeField, SP: StepCircuit<ARITY, F>, const T: usize>
    StepConfig<ARITY, F, SP, T>
{
    /// Returns step circuit instance
    fn get_step_circuit_instance(&self, instance_index: usize) -> Option<Column<Instance>> {
        self.step_circuit_instances.get(instance_index).copied()
    }
}

impl<const ARITY: usize, F: PrimeField + Clone, SP: StepCircuit<ARITY, F>, const T: usize> Clone
    for StepConfig<ARITY, F, SP, T>
where
    SP::Config: Clone,
{
    fn clone(&self) -> Self {
        Self {
            consistency_marker: self.consistency_marker,
            step_config: self.step_config.clone(),
            main_gate_config: self.main_gate_config.clone(),
            step_circuit_instances: self.step_circuit_instances.clone(),
        }
    }
}

impl<const ARITY: usize, F: PrimeField + fmt::Debug, SP: StepCircuit<ARITY, F>, const T: usize>
    fmt::Debug for StepConfig<ARITY, F, SP, T>
where
    SP::Config: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StepConfig")
            .field("step_config", &self.step_config)
            .field("main_gate_config", &self.main_gate_config)
            .finish()
    }
}

/// Circuit that fold [`StepCircuit`] to fold represented the augmented function `F'` in the IVC scheme.
///
/// TODO #32 I will add details abote actions after implementation of trait to directly link
/// methods
///
/// # References
/// - For a detailed understanding of IVC and the context in which a struct
///   [`StepFoldingCircuit`] might be used, refer to the 'Section 5' of
///   [Nova Whitepaper](https://eprint.iacr.org/2023/969.pdf).
///   This trait is representation of `F'` function at 'Figure 4'
///       - `F'` is an augmented version of `F` designed to produce the IVC proofs `P_i` at each step.
///         It takes additional parameters such as \( vk, Ui, ui, (i, z0, zi), \omega_i, T \) and outputs \( x \).
///
/// - For `F'` please look at [`StepFoldingCircuit`]
pub(crate) struct StepFoldingCircuit<'link, const ARITY: usize, C, SC, RO, const T: usize>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    SC: StepCircuit<ARITY, C::Base> + Sized,
    RO: ROCircuitTrait<C::Base>,
{
    pub step_circuit: &'link SC,
    pub input: StepInputs<'link, ARITY, C, RO>,
}

impl<'link, const ARITY: usize, C, SC, RO, const T: usize>
    StepFoldingCircuit<'link, ARITY, C, SC, RO, T>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    SC: StepCircuit<ARITY, C::Base> + Sized,
    RO: ROCircuitTrait<C::Base, Config = MainGateConfig<T>>,
{
    pub fn instances(&self, consistency_markers: [C::Base; 2]) -> Vec<Vec<C::Base>> {
        let mut instances = self.input.step_circuit_instances.clone();
        instances.insert(0, consistency_markers.to_vec());
        instances
    }
}

impl<'link, const ARITY: usize, C, SC, RO, const T: usize> Circuit<C::Base>
    for StepFoldingCircuit<'link, ARITY, C, SC, RO, T>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    SC: StepCircuit<ARITY, C::Base> + Sized,
    RO: ROCircuitTrait<C::Base, Config = MainGateConfig<T>>,
{
    type Config = StepConfig<ARITY, C::Base, SC, T>;
    type FloorPlanner = floor_planner::V1;

    fn without_witnesses(&self) -> Self {
        let mut u = self.input.u.clone();
        u.W_commitments.iter_mut().for_each(|v| *v = C::identity());
        u.instances
            .iter_mut()
            .flat_map(|ins| ins.iter_mut())
            .for_each(|v| *v = C::ScalarExt::ZERO);
        u.challenges
            .iter_mut()
            .for_each(|v| *v = C::ScalarExt::ZERO);

        Self {
            step_circuit: self.step_circuit,
            input: StepInputs {
                step: C::Base::ZERO,
                step_pp: self.input.step_pp,
                public_params_hash: C::identity(),
                z_0: [C::Base::ZERO; ARITY],
                z_i: [C::Base::ZERO; ARITY],
                cross_term_commits: vec![C::identity(); self.input.cross_term_commits.len()],
                U: RelaxedPlonkInstance::new(
                    self.input.U.challenges.len(),
                    self.input.U.W_commitments.len(),
                ),
                u,
                step_circuit_instances: self
                    .input
                    .step_circuit_instances
                    .iter()
                    .map(|instance| vec![C::Base::ZERO; instance.len()])
                    .collect(),
            },
        }
    }

    fn configure(cs: &mut ConstraintSystem<C::Base>) -> Self::Config {
        let consistency_markers = cs.instance_column();
        cs.enable_equality(consistency_markers);

        let main_gate_config = MainGate::configure(cs);
        let before = cs.num_instance_columns();
        let step_config = <SC as StepCircuit<ARITY, C::Base>>::configure(cs);
        let after = cs.num_instance_columns();

        let step_circuit_instances = (1..=(after - before))
            .map(|index| {
                // Because `Column` type doesn't have a constructor, we use a small hack - reuse
                // `consistency_markers`

                let mut i = consistency_markers;
                i.index = index;
                i
            })
            .collect();

        StepConfig {
            consistency_marker: consistency_markers,
            step_config,
            main_gate_config,
            step_circuit_instances,
        }
    }

    #[instrument(skip_all)]
    fn synthesize(
        &self,
        config: StepConfig<ARITY, C::Base, SC, T>,
        mut layouter: impl Layouter<C::Base>,
    ) -> Result<(), Halo2PlonkError> {
        assert_eq!(
            self.input.step_circuit_instances.len(),
            config.step_circuit_instances.len()
        );

        let (assigned_z_0, assigned_z_i, assigned_step_circuit_instances): (
            [_; ARITY],
            [_; ARITY],
            _,
        ) = layouter
            .assign_region(
                || "assign z_0 & z_i",
                |mut region| {
                    let _s = debug_span!("assign z_0 & z_i").entered();

                    config.main_gate_config.name_columns(&mut region);
                    let mut region = RegionCtx::new(region, 0);

                    let mut assigner = config.main_gate_config.advice_cycle_assigner();

                    let z_0 = assigner
                        .assign_all_advice(&mut region, || "z_0", self.input.z_0.iter().copied())
                        .map(|inp| inp.try_into().unwrap())?;

                    let z_i = assigner
                        .assign_all_advice(&mut region, || "z_i", self.input.z_i.iter().copied())
                        .map(|inp| inp.try_into().unwrap())?;

                    let flat_step_circuit_instances = self
                        .input
                        .step_circuit_instances
                        .iter()
                        .enumerate()
                        .try_fold(vec![], |mut all, (column_index, instance_column_values)| {
                            let column_values = instance_column_values.iter().cloned();
                            let instance_column = assigner.assign_all_advice(
                                &mut region,
                                || "step circuit instance[]",
                                column_values,
                            )?;

                            all.extend(
                                instance_column.into_iter().enumerate().map(
                                    |(row_index, assigned)| (assigned, column_index, row_index),
                                ),
                            );

                            Result::<_, Halo2PlonkError>::Ok(all)
                        })?;

                    Ok((z_0, z_i, flat_step_circuit_instances))
                },
            )
            .map_err(|err| {
                error!("while assign z_0 & z_i: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        // We take the instance columns from the step circuit and place them inside the witness as
        // well, verifying within the same step by permuting them
        //
        // This allows us to omit a separate check for correctness of collapsing
        for (assigned, column_index, row_index) in assigned_step_circuit_instances {
            layouter.constrain_instance(
                assigned.cell(),
                config.get_step_circuit_instance(column_index).expect(
                    "The `StepCircuit::instances` sizes and the number of `instance`
                        columns created inside `StepCircuit::configure` do not match",
                ),
                row_index,
            )?;
        }

        let chip = FoldRelaxedPlonkInstanceChip::new(
            self.input.U.clone(),
            self.input.step_pp.limb_width,
            self.input.step_pp.limbs_count,
            config.main_gate_config.clone(),
        );

        let (w, r) = layouter
            .assign_region(
                || "assign witness",
                |mut region| {
                    let _s = debug_span!("assign_witness").entered();
                    config.main_gate_config.name_columns(&mut region);

                    Ok(chip.assign_witness_with_challenge(
                        &mut RegionCtx::new(region, 0),
                        &self.input.public_params_hash,
                        &self.input.u,
                        &self.input.cross_term_commits,
                        RO::new(
                            config.main_gate_config.clone(),
                            self.input.step_pp.ro_constant.clone(),
                        ),
                    )?)
                },
            )
            .map_err(|err| {
                error!("while assigned witness: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        debug!("witness & challenge assigned");

        // Synthesize the circuit for the base case and get the new running instance
        let U_new_base = w.assigned_relaxed.clone();

        let (assigned_step, assigned_next_step) = layouter
            .assign_region(
                || "generate steps",
                |mut region| {
                    let _s = debug_span!("generate steps").entered();
                    config.main_gate_config.name_columns(&mut region);

                    let mut ctx = RegionCtx::new(region, 0);

                    ctx.assign_fixed(|| "1", config.main_gate_config.rc, C::Base::ONE)?;

                    ctx.assign_fixed(|| "1", config.main_gate_config.q_i, C::Base::ONE)?;
                    let assigned_step = ctx.assign_advice(
                        || "step",
                        config.main_gate_config.input,
                        Value::known(self.input.step),
                    )?;

                    ctx.assign_fixed(|| "-1", config.main_gate_config.q_o, -C::Base::ONE)?;
                    let assigned_next_step = ctx.assign_advice(
                        || "result for sum with const",
                        config.main_gate_config.out,
                        Value::known(self.input.step + C::Base::ONE),
                    )?;

                    Ok((assigned_step, assigned_next_step))
                },
            )
            .map_err(|err| {
                error!("while assign step & next step: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        // Check X0 == input_params_hash
        let (base_case_input_check, non_base_case_input_check) = layouter
            .assign_region(
                || "generate input hash",
                |mut region| {
                    let _s = debug_span!("generate input hash").entered();
                    config.main_gate_config.name_columns(&mut region);

                    let mut ctx = RegionCtx::new(region, 0);

                    let base_case_input_check = ctx.assign_advice(
                        || "base_case_input_check - always true",
                        config.main_gate_config.input,
                        Value::known(C::Base::ONE),
                    )?;
                    ctx.next();

                    let expected_X0 =
                        AssignedConsistencyMarkersComputation::<'_, RO, ARITY, T, C> {
                            random_oracle_constant: self.input.step_pp.ro_constant.clone(),
                            public_params_hash: &w.public_params_hash,
                            step: &assigned_step,
                            z_0: &assigned_z_0,
                            z_i: &assigned_z_i,
                            relaxed: &w.assigned_relaxed,
                        }
                        .generate_with_inspect(
                            &mut ctx,
                            config.main_gate_config.clone(),
                            |buf| debug!("expected X0 {buf:?}"),
                        )?;

                    debug!("expected X0: {expected_X0:?}");
                    debug!(
                        "input instance 0: {:?}",
                        w.input_consistency_markers[0].as_value
                    );

                    Ok((
                        base_case_input_check,
                        MainGate::new(config.main_gate_config.clone()).is_equal_term(
                            &mut ctx,
                            &expected_X0,
                            &w.input_consistency_markers[0].as_value,
                        )?,
                    ))
                },
            )
            .map_err(|err| {
                error!("while generate input hash: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let FoldResult {
            assigned_input: assigned_input_witness,
            assigned_result_of_fold: U_new_non_base,
        } = layouter
            .assign_region(
                || "synthesize_step_non_base_case",
                |region| {
                    let _s = debug_span!("synthesize_step_non_base_case").entered();
                    Ok(chip.fold(&mut RegionCtx::new(region, 0), w.clone(), r.clone())?)
                },
            )
            .map_err(|err| {
                error!("while synthesize_step_non_base_case: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        let (assigned_new_U, assigned_input) = layouter
            .assign_region(
                || "make folding",
                |region| {
                    let _s = debug_span!("make folding").entered();

                    let mut region = RegionCtx::new(region, 0);
                    let gate = MainGate::new(config.main_gate_config.clone());

                    let assigned_is_zero_step =
                        gate.is_zero_term(&mut region, assigned_step.clone())?;

                    let new_U = AssignedRelaxedPlonkInstance::<C>::conditional_select(
                        &mut region,
                        &config.main_gate_config,
                        &U_new_base,
                        &U_new_non_base,
                        assigned_is_zero_step.clone(),
                    )?;

                    let input_check = gate.conditional_select(
                        &mut region,
                        &base_case_input_check,
                        &non_base_case_input_check,
                        &assigned_is_zero_step,
                    )?;
                    gate.assert_equal_const(&mut region, input_check, C::Base::ONE)?;

                    let assigned_input: [_; ARITY] = assigned_z_0
                        .iter()
                        .zip_eq(assigned_z_i.iter())
                        .map(|(z_0, z_i)| {
                            gate.conditional_select(&mut region, z_0, z_i, &assigned_is_zero_step)
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .try_into()
                        .unwrap();

                    Ok((new_U, assigned_input))
                },
            )
            .map_err(|err| {
                error!("while folding: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        let z_output = self
            .step_circuit
            .synthesize_step(config.step_config, &mut layouter, &assigned_input)
            .map_err(|err| {
                error!("while synthesize_step: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        let output_hash = layouter
            .assign_region(
                || "generate output hash",
                |region| {
                    let _s = debug_span!("generate output hash").entered();

                    AssignedConsistencyMarkersComputation::<'_, RO, ARITY, T, C> {
                        random_oracle_constant: self.input.step_pp.ro_constant.clone(),
                        public_params_hash: &assigned_input_witness.public_params_hash,
                        step: &assigned_next_step,
                        z_0: &assigned_z_0,
                        z_i: &z_output,
                        relaxed: &assigned_new_U,
                    }
                    .generate_with_inspect(
                        &mut RegionCtx::new(region, 0),
                        config.main_gate_config.clone(),
                        |buf| debug!("new X0 {buf:?}"),
                    )
                },
            )
            .map_err(|err| {
                error!("while generate output hash: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        debug!("output instance 0: {:?}", output_hash);

        // Check that old_X1 == new_X0
        layouter
            .constrain_instance(
                assigned_input_witness.input_consistency_markers[1]
                    .as_value
                    .cell(),
                config.consistency_marker,
                0,
            )
            .map_err(|err| {
                error!("while check that old_X1 == new_X0: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        // Check that new_X1 == output_hash
        layouter
            .constrain_instance(output_hash.cell(), config.consistency_marker, 1)
            .map_err(|err| {
                error!("while check that new_X1 == output_hash: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        Ok(())
    }
}
