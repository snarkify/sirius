use std::{fmt, num::NonZeroUsize};

use ff::{FromUniformBytes, PrimeField, PrimeFieldBits};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::ConstraintSystem,
};
use halo2curves::CurveAffine;
use itertools::Itertools;
use serde::Serialize;

use crate::{
    constants::NUM_CHALLENGE_BITS,
    ivc::fold_relaxed_plonk_instance_chip::FoldRelaxedPlonkInstanceChip,
    main_gate::{AssignedValue, MainGate, MainGateConfig, RegionCtx, WrapValue},
    plonk::{PlonkInstance, RelaxedPlonkInstance},
    poseidon::ROCircuitTrait,
};

use super::{
    floor_planner::FloorPlanner,
    fold_relaxed_plonk_instance_chip::{self, AssignedRelaxedPlonkInstance, FoldResult},
};

#[derive(Debug, thiserror::Error)]
pub enum SynthesisError {
    #[error(transparent)]
    Halo2(#[from] halo2_proofs::plonk::Error),
    #[error(transparent)]
    FoldError(#[from] fold_relaxed_plonk_instance_chip::Error),
}

/// The `StepCircuit` trait represents a step in incremental computation in
/// Incrementally Verifiable Computation (IVC).
///
/// # Overview
/// - The trait is crucial for representing a computation step within an IVC
///   framework.
/// - It provides an abstraction for handling inputs and outputs efficiently
///   at each computation step.
/// - The trait should be implemented by circuits that are intended to represent
///   a step in incremental computation.
///
/// # API
/// Design based on [`halo2_proofs::plonk::Circuit`] and
/// [`nova::traits::circuit`](https://github.com/microsoft/Nova/blob/main/src/traits/circuit.rs#L7)
///
/// # `const ARITY: usize`
/// The number of inputs or outputs of each step. `synthesize` and `output`
/// methods are expected to take as input a vector of size equal to
/// arity and output a vector of size equal to arity.
///
/// # References
/// - For a detailed understanding of IVC and the context in which a trait
///   `StepCircuit` might be used, refer to the 'Section 5' of
///   [Nova Whitepaper](https://eprint.iacr.org/2023/969.pdf).
///   This trait is representation of `F` function at 'Figure 4'
///     - `F` is a polynomial-time function that takes non-deterministic input. It is the function
///       that represents the computation being incrementally verified. In the context of IVC, each
///       step of the incremental computation applies this function FF.
/// - For `F'` please look at [`StepCircuitExt`]
pub trait StepCircuit<const ARITY: usize, F: PrimeField> {
    /// This is a configuration object that stores things like columns.
    ///
    /// TODO improve
    type Config: Clone;

    /// The floor planner used for this circuit.
    /// This is an associated type of the `Circuit` trait because its
    /// behaviour is circuit-critical.
    ///
    /// TODO improve
    ///
    /// If you don't understand what it is, just use [`super::floor_planner::SimpleStepFloorPlanner`]
    type FloorPlanner: FloorPlanner;

    /// Configure the step circuit. This method initializes necessary
    /// fixed columns and advice columns, but does not create any instance
    /// columns.
    ///
    /// This setup is crucial for the functioning of the IVC-based system.
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config;

    /// Sythesize the circuit for a computation step and return variable
    /// that corresponds to the output of the step z_{i+1}
    /// this method will be called when we synthesize the IVC_Circuit
    ///
    /// Return `z_out` result
    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_i: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError>;

    /// An auxiliary function that allows you to perform a calculation step
    /// without using ConstraintSystem.
    ///
    /// By default, performs the step with a dummy `ConstraintSystem`
    fn output(&self, z_i: &[F; ARITY]) -> [F; ARITY] {
        todo!(
            "Default impl with `Self::synthesize` wrap
            and comment about when manual impl needed by {z_i:?}"
        )
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ConfigureError {
    #[error("TODO")]
    InstanceColumnNotAllowed,
}

#[derive(Serialize)]
#[serde(bound(serialize = "RO::Args: Serialize"))]
pub(crate) struct SynthesizeStepParams<F, RO>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
    RO: ROCircuitTrait<F>,
{
    pub limb_width: NonZeroUsize,
    pub limbs_count: NonZeroUsize,
    /// A boolean indicating if this is the primary circuit
    pub is_primary_circuit: bool,
    pub ro_constant: RO::Args,
}

impl<F, RO> fmt::Debug for SynthesizeStepParams<F, RO>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
    RO: ROCircuitTrait<F>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SynthesizeStepParams")
            .field("limb_width", &self.limb_width)
            .field("n_limbs", &self.limbs_count)
            .field("is_primary_circuit", &self.is_primary_circuit)
            .field("ro_constant", &self.ro_constant)
            .finish()
    }
}

pub(crate) struct StepInputs<'link, const ARITY: usize, C: CurveAffine, RO: ROCircuitTrait<C::Base>>
where
    C::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    pub step_public_params: &'link SynthesizeStepParams<C::Base, RO>,
    pub public_params_hash: C,
    pub step: C::Base,

    pub z_0: [AssignedValue<C::Base>; ARITY],
    /// Output of previous step & input of current one
    pub z_i: [AssignedValue<C::Base>; ARITY],

    // TODO docs
    pub U: RelaxedPlonkInstance<C>,

    // TODO docs
    pub u: PlonkInstance<C>,

    // TODO docs
    pub cross_term_commits: Vec<C>,
}

pub struct StepConfig<const ARITY: usize, const T: usize, F: PrimeField, SP: StepCircuit<ARITY, F>>
{
    pub step_config: SP::Config,
    pub main_gate_config: MainGateConfig<T>,
}

impl<const ARITY: usize, F: PrimeField + Clone, SP: StepCircuit<ARITY, F>, const T: usize> Clone
    for StepConfig<ARITY, T, F, SP>
where
    SP::Config: Clone,
{
    fn clone(&self) -> Self {
        Self {
            step_config: self.step_config.clone(),
            main_gate_config: self.main_gate_config.clone(),
        }
    }
}

impl<const ARITY: usize, F: PrimeField + fmt::Debug, SP: StepCircuit<ARITY, F>, const T: usize>
    fmt::Debug for StepConfig<ARITY, T, F, SP>
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

pub struct StepSynthesisResult<const ARITY: usize, F: PrimeField> {
    /// Output of current synthesis step
    pub z_output: [AssignedValue<F>; ARITY],
    pub new_X1: AssignedValue<F>,
    pub new_X0: AssignedValue<F>,
}

/// Trait extends [`StepCircuit`] to represent the augmented function `F'` in the IVC scheme.
///
/// If [`StepCircuit`] is defined by circuit developers, this trait automatically extends
/// the custom type to add the actions needed by IVC.
///
/// TODO #32 I will add details abote actions after implementation of trait to directly link
/// methods
///
/// # References
/// - For a detailed understanding of IVC and the context in which a trait
///   [`StepCircuitExt`] might be used, refer to the 'Section 5' of
///   [Nova Whitepaper](https://eprint.iacr.org/2023/969.pdf).
///   This trait is representation of `F'` function at 'Figure 4'
///       - `F'` is an augmented version of `F` designed to produce the IVC proofs `P_i` at each step.
///         It takes additional parameters such as \( vk, Ui, ui, (i, z0, zi), \omega_i, T \) and outputs \( x \).
///
/// - For `F'` please look at [`StepCircuitExt`]
pub(crate) trait StepCircuitExt<'link, const ARITY: usize, F>:
    StepCircuit<ARITY, F> + Sized
where
    F: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    /// The crate-only expanding trait that checks that no instance columns have
    /// been created during [`StepCircuit::configure`].
    fn configure<const T: usize>(
        cs: &mut ConstraintSystem<F>,
    ) -> Result<StepConfig<ARITY, T, F, Self>, ConfigureError> {
        let before = cs.num_instance_columns();

        let main_gate_config = MainGate::configure(cs);
        let step_config = <Self as StepCircuit<ARITY, F>>::configure(cs);

        if before == cs.num_instance_columns() {
            Ok(StepConfig {
                step_config,
                main_gate_config,
            })
        } else {
            Err(ConfigureError::InstanceColumnNotAllowed)
        }
    }

    fn synthesize<
        const T: usize,
        C: CurveAffine<Base = F>,
        RO: ROCircuitTrait<F, Config = MainGateConfig<T>>,
    >(
        &self,
        config: StepConfig<ARITY, T, F, Self>,
        layouter: &mut impl Layouter<F>,
        input: StepInputs<ARITY, C, RO>,
    ) -> Result<StepSynthesisResult<ARITY, F>, SynthesisError> {
        // Synthesize the circuit for the base case and get the new running instance
        let U_new_base = self.synthesize_step_base_case(
            layouter,
            input.step_public_params,
            &input.u,
            config.main_gate_config.clone(),
        )?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let FoldResult {
            assigned_input: assigned_input_witness,
            assigned_result_of_fold: U_new_non_base,
        } = self.synthesize_step_non_base_case(&config, layouter, &input)?;

        let (assigned_next_step_i, assigned_new_U, assigned_input) = layouter.assign_region(
            || "generate input",
            |region| {
                let mut region = RegionCtx::new(region, 0);
                let gate = MainGate::new(config.main_gate_config.clone());

                let assigned_step_i = region.assign_advice(
                    || "step",
                    config.main_gate_config.input,
                    Value::known(input.step),
                )?;

                let next_step_i = gate.add_with_const(&mut region, &assigned_step_i, F::ONE)?;

                let assigned_is_zero_step = gate.is_zero_term(&mut region, assigned_step_i)?;

                let new_U = AssignedRelaxedPlonkInstance::<C>::conditional_select(
                    &mut region,
                    &config.main_gate_config,
                    &U_new_non_base,
                    &U_new_base,
                    assigned_is_zero_step.clone(),
                )?;

                let assigned_input: [_; ARITY] = input
                    .z_0
                    .iter()
                    .zip_eq(input.z_i.iter())
                    .map(|(z_0, z_i)| {
                        gate.conditional_select(&mut region, z_0, z_i, &assigned_is_zero_step)
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .try_into()
                    .unwrap();

                Ok((next_step_i, new_U, assigned_input))
            },
        )?;

        let z_output = self.synthesize_step(config.step_config, layouter, &assigned_input)?;

        let output_hash = layouter.assign_region(
            || "generate input",
            |region| {
                let mut ctx = RegionCtx::new(region, 0);

                let bits = RO::new(
                    config.main_gate_config.clone(),
                    input.step_public_params.ro_constant.clone(),
                )
                .absorb_point(WrapValue::from_assigned_point(
                    &assigned_input_witness.public_params_hash,
                ))
                .absorb_base(WrapValue::Assigned(assigned_next_step_i.clone()))
                .absorb_iter(input.z_0.iter())
                .absorb_iter(z_output.iter().cloned())
                .absorb_iter(assigned_new_U.iter_wrap_values())
                .squeeze_n_bits(&mut ctx, NUM_CHALLENGE_BITS)?;

                MainGate::new(config.main_gate_config.clone()).le_bits_to_num(&mut ctx, &bits)
            },
        )?;

        Ok(StepSynthesisResult {
            z_output,
            new_X0: assigned_input_witness
                .input_instances
                .first()
                .and_then(|inst| inst.get(1).cloned())
                .unwrap(),
            new_X1: output_hash,
        })
    }

    fn synthesize_step_base_case<
        const T: usize,
        C: CurveAffine<Base = F>,
        RO: ROCircuitTrait<F, Config = MainGateConfig<T>>,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        public_params: &SynthesizeStepParams<F, RO>,
        u: &PlonkInstance<C>,
        config: MainGateConfig<T>,
    ) -> Result<AssignedRelaxedPlonkInstance<C>, SynthesisError> {
        let Unew_base = layouter.assign_region(
            || "synthesize_step_base_case",
            move |region| {
                let chip = if public_params.is_primary_circuit {
                    FoldRelaxedPlonkInstanceChip::new_default(
                        public_params.limb_width,
                        public_params.limbs_count,
                        u.challenges.len(),
                        u.W_commitments.len(),
                        config.clone(),
                    )
                } else {
                    FoldRelaxedPlonkInstanceChip::from_instance(
                        u.clone(),
                        public_params.limb_width,
                        public_params.limbs_count,
                        config.clone(),
                    )
                };

                Ok(chip.assign_current_relaxed(&mut RegionCtx::new(region, 0))?)
            },
        )?;

        Ok(Unew_base)
    }

    fn synthesize_step_non_base_case<
        const T: usize,
        C: CurveAffine<Base = F>,
        RO: ROCircuitTrait<F, Config = MainGateConfig<T>>,
    >(
        &self,
        config: &StepConfig<ARITY, T, F, Self>,
        layouter: &mut impl Layouter<F>,
        input: &StepInputs<ARITY, C, RO>,
    ) -> Result<FoldResult<C>, SynthesisError> {
        let StepInputs {
            U,
            u,
            cross_term_commits,
            public_params_hash,
            ..
        } = input;

        Ok(layouter.assign_region(
            || "synthesize_step_non_base_case",
            move |region| {
                let chip = FoldRelaxedPlonkInstanceChip::from_relaxed(
                    U.clone(),
                    input.step_public_params.limb_width,
                    input.step_public_params.limbs_count,
                    config.main_gate_config.clone(),
                );

                let ro_circuit = RO::new(
                    config.main_gate_config.clone(),
                    input.step_public_params.ro_constant.clone(),
                );

                Ok(chip.fold(
                    &mut RegionCtx::new(region, 0),
                    ro_circuit,
                    public_params_hash,
                    u,
                    cross_term_commits,
                )?)
            },
        )?)
    }
}

// auto-impl for all `StepCircuit` trait `StepCircuitExt`
impl<'link, const ARITY: usize, F: PrimeField, SP: StepCircuit<ARITY, F>>
    StepCircuitExt<'link, ARITY, F> for SP
where
    F: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
}

pub mod trivial {
    use std::marker::PhantomData;

    use ff::PrimeField;
    use halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::ConstraintSystem,
    };

    use crate::ivc::SimpleFloorPlanner;

    use super::{StepCircuit, SynthesisError};

    /// A trivial step circuit that simply returns the input
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct Circuit<const ARITY: usize, F: PrimeField> {
        _p: PhantomData<F>,
    }

    impl<const ARITY: usize, F> StepCircuit<ARITY, F> for Circuit<ARITY, F>
    where
        F: PrimeField,
    {
        /// This is a configuration object that stores things like columns.
        ///
        /// TODO improve
        type Config = ();

        /// The floor planner used for this circuit.
        /// This is an associated type of the `Circuit` trait because its
        /// behaviour is circuit-critical.
        ///
        /// TODO improve
        ///
        /// If you don't understand what it is, just use [`super::floor_planner::SimpleStepFloorPlanner`]
        type FloorPlanner = SimpleFloorPlanner;

        /// Configure the step circuit. This method initializes necessary
        /// fixed columns and advice columns, but does not create any instance
        /// columns.
        ///
        /// This setup is crucial for the functioning of the IVC-based system.
        fn configure(_cs: &mut ConstraintSystem<F>) -> Self::Config {}

        /// Sythesize the circuit for a computation step and return variable
        /// that corresponds to the output of the step z_{i+1}
        /// this method will be called when we synthesize the IVC_Circuit
        ///
        /// Return `z_out` result
        fn synthesize_step(
            &self,
            _config: Self::Config,
            _layouter: &mut impl Layouter<F>,
            z_i: &[AssignedCell<F, F>; ARITY],
        ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError> {
            Ok(z_i.clone())
        }
    }
}
