use std::{io, marker::PhantomData, num::NonZeroUsize};

use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2_proofs::{
    dev::MockProver,
    halo2curves::{ff, group, CurveAffine},
};
use serde::Serialize;
use tracing::*;

use super::instance_computation::RandomOracleComputationInstance;
pub use super::step_circuit::{self, StepCircuit, SynthesisError};
use crate::{
    ivc::{
        public_params::PublicParams,
        step_folding_circuit::{StepFoldingCircuit, StepInputs},
    },
    main_gate::MainGateConfig,
    nifs::{self, vanilla::VanillaFS, FoldingScheme},
    plonk::{self, PlonkTrace, RelaxedPlonkTrace},
    poseidon::{random_oracle::ROTrait, ROPair},
    sps,
    table::CircuitRunner,
    util,
};

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
{
    relaxed_trace: RelaxedPlonkTrace<C>,
    z_0: [C::Scalar; ARITY],
    z_i: [C::Scalar; ARITY],
    _p: PhantomData<SC>,
}

// TODO #31 docs
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("halo2: {0:?}")]
    Halo2(halo2_proofs::plonk::ErrorFront),
    #[error(transparent)]
    Plonk(#[from] crate::plonk::Error),
    #[error(transparent)]
    Step(#[from] step_circuit::SynthesisError),
    #[error("number of steps is not match")]
    NumStepNotMatch,
    #[error("step circuit input not match")]
    SCInputNotMatch,
    #[error("TODO")]
    WhileHash(io::Error),
    #[error("TODO")]
    Sps(#[from] sps::Error),
    #[error("TODO")]
    NIFS(#[from] nifs::Error),
    #[error("TODO")]
    VerifyFailed(Vec<VerificationError>),
}

impl From<halo2_proofs::plonk::ErrorFront> for Error {
    fn from(value: halo2_proofs::plonk::ErrorFront) -> Self {
        Error::Halo2(value)
    }
}

impl Error {
    fn from_mock_verify(
        errors: Vec<halo2_proofs::dev::VerifyFailure>,
        is_primary: bool,
        step: usize,
    ) -> Self {
        Self::VerifyFailed(
            errors
                .into_iter()
                .map(|err| VerificationError::MockRunFailed {
                    err,
                    is_primary,
                    step,
                })
                .collect(),
        )
    }
}

#[derive(Debug, thiserror::Error)]
pub enum VerificationError {
    #[error("TODO")]
    InstanceNotMatch { index: usize, is_primary: bool },
    #[error("TODO")]
    NotSat {
        err: plonk::Error,
        is_primary: bool,
        is_relaxed: bool,
    },
    #[error("TODO")]
    MockRunFailed {
        err: halo2_proofs::dev::VerifyFailure,
        is_primary: bool,
        step: usize,
    },
}

// TODO #31 docs
#[allow(clippy::upper_case_acronyms)]
/// RecursiveSNARK from Nova codebase
pub struct IVC<const A1: usize, const A2: usize, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
{
    primary: StepCircuitContext<A1, C1, SC1>,
    secondary: StepCircuitContext<A2, C2, SC2>,

    step: usize,
    secondary_nifs_pp: <nifs::vanilla::VanillaFS<C2> as FoldingScheme<C2>>::ProverParam,
    primary_nifs_pp: <nifs::vanilla::VanillaFS<C1> as FoldingScheme<C1>>::ProverParam,
    secondary_trace: [PlonkTrace<C2>; 1],

    debug_mode: bool,
}

impl<const A1: usize, const A2: usize, C1, C2, SC1, SC2> IVC<A1, A2, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
    C1::ScalarExt: Serialize,
    C2::ScalarExt: Serialize,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
    C1::Base: PrimeFieldBits + FromUniformBytes<64>,
    C2::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn fold_with_debug_mode<const T: usize, RP1, RP2>(
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        primary_z_0: [C1::Scalar; A1],
        secondary: &SC2,
        secondary_z_0: [C2::Scalar; A2],
        num_steps: NonZeroUsize,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let mut ivc = Self::new(pp, primary, primary_z_0, secondary, secondary_z_0, true)?;
        trace!("IVC created");

        for step in 1..=num_steps.get() {
            trace!("Start fold {step} step");
            ivc.fold_step(pp, primary, secondary)?;
        }

        trace!("Finish folding, start verify");

        ivc.verify(pp)?;

        Ok(())
    }
    pub fn fold<const T: usize, RP1, RP2>(
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        primary_z_0: [C1::Scalar; A1],
        secondary: &SC2,
        secondary_z_0: [C2::Scalar; A2],
        num_steps: NonZeroUsize,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let mut ivc = Self::new(pp, primary, primary_z_0, secondary, secondary_z_0, false)?;
        trace!("IVC created");

        for step in 1..=num_steps.get() {
            trace!("Start fold {step} step");
            ivc.fold_step(pp, primary, secondary)?;
        }

        trace!("Finish folding, start verify");

        ivc.verify(pp)?;

        Ok(())
    }

    #[instrument(name = "ivc_new", skip_all, fields(step = 0))]
    pub fn new<const T: usize, RP1, RP2>(
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        primary_z_0: [C1::Scalar; A1],
        secondary: &SC2,
        secondary_z_0: [C2::Scalar; A2],
        debug_mode: bool,
    ) -> Result<Self, Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let primary_span = info_span!("primary").entered();
        // For use as first version of `U` in primary circuit synthesize
        let secondary_pre_round_plonk_trace = pp.secondary_initial_plonk_trace();

        let primary_z_output = primary.process_step(&primary_z_0, pp.primary.k_table_size())?;
        debug!("primary z output calculated off-circuit");

        // Will be used as input & output `U` of zero-step of IVC
        let secondary_relaxed_trace =
            secondary_pre_round_plonk_trace.to_relax(pp.secondary.k_table_size() as usize);

        // Prepare primary constraint system for folding
        let primary_instance = {
            let _s = info_span!("generate_instance").entered();
            [
                util::fe_to_fe(&secondary_pre_round_plonk_trace.u.instance[1]).unwrap(),
                RandomOracleComputationInstance::<'_, A1, C2, RP1::OffCircuit> {
                    random_oracle_constant: pp.primary.params().ro_constant().clone(),
                    public_params_hash: &pp.digest_2(),
                    step: 1,
                    z_0: &primary_z_0,
                    z_i: &primary_z_output,
                    relaxed: &secondary_relaxed_trace.U,
                    limb_width: pp.primary.params().limb_width(),
                    limbs_count: pp.primary.params().limbs_count(),
                }
                .generate_with_inspect(|buf| debug!("primary X1 zero-step: {buf:?}")),
            ]
        };

        let primary_sfc = StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, T> {
            step_circuit: primary,
            input: StepInputs::<'_, A1, C2, RP1::OnCircuit> {
                step: C2::Base::ZERO,
                step_pp: pp.primary.params(),
                public_params_hash: pp.digest_2(),
                z_0: primary_z_0,
                z_i: primary_z_0,
                U: secondary_relaxed_trace.U.clone(),
                u: secondary_pre_round_plonk_trace.u.clone(),
                cross_term_commits: vec![
                    C2::identity();
                    pp.secondary.S().get_degree_for_folding().saturating_sub(1)
                ],
            },
        };

        if debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.primary.k_table_size(),
                &primary_sfc,
                vec![primary_instance.to_vec()],
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, true, 0))?;
        }

        let primary_witness = CircuitRunner::new(
            pp.primary.k_table_size(),
            primary_sfc,
            primary_instance.to_vec(),
        )
        .try_collect_witness()?;

        let (primary_nifs_pp, _primary_off_circuit_vp) =
            VanillaFS::setup_params(pp.digest_1(), pp.primary.S().clone())?;

        let primary_plonk_trace = VanillaFS::generate_plonk_trace(
            pp.primary.ck(),
            &primary_instance,
            &primary_witness,
            &primary_nifs_pp,
            &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone()),
        )?;

        let primary_relaxed_trace =
            primary_plonk_trace.to_relax(pp.primary.k_table_size() as usize);

        primary_span.exit();
        let _secondary_span = info_span!("secondary").entered();

        let secondary_z_output =
            secondary.process_step(&secondary_z_0, pp.secondary.k_table_size())?;

        // Will be used as input & output `U` of zero-step of IVC
        let secondary_instance = {
            let _s = info_span!("generate_instance");
            [
                util::fe_to_fe(&primary_plonk_trace.u.instance[1]).unwrap(),
                RandomOracleComputationInstance::<'_, A2, C1, RP2::OffCircuit> {
                    random_oracle_constant: pp.secondary.params().ro_constant().clone(),
                    public_params_hash: &pp.digest_1(),
                    step: 1,
                    z_0: &secondary_z_0,
                    z_i: &secondary_z_output,
                    relaxed: &primary_relaxed_trace.U,
                    limb_width: pp.secondary.params().limb_width(),
                    limbs_count: pp.secondary.params().limbs_count(),
                }
                .generate_with_inspect(|buf| debug!("secondary X1 zero-step: {buf:?}")),
            ]
        };

        let secondary_sfc = StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, T> {
            step_circuit: secondary,
            input: StepInputs::<'_, A2, C1, RP2::OnCircuit> {
                step: C1::Base::ZERO,
                step_pp: pp.secondary.params(),
                public_params_hash: pp.digest_1(),
                z_0: secondary_z_0,
                z_i: secondary_z_0,
                U: primary_relaxed_trace.U.clone(),
                u: primary_plonk_trace.u.clone(),
                cross_term_commits: vec![
                    C1::identity();
                    primary_nifs_pp
                        .S
                        .get_degree_for_folding()
                        .saturating_sub(1)
                ],
            },
        };

        if debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.secondary.k_table_size(),
                &secondary_sfc,
                vec![secondary_instance.to_vec()],
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, false, 0))?;
        }

        let secondary_witness = CircuitRunner::new(
            pp.secondary.k_table_size(),
            secondary_sfc,
            secondary_instance.to_vec(),
        )
        .try_collect_witness()?;

        let (secondary_nifs_pp, _nifs_vp) =
            VanillaFS::setup_params(pp.digest_2(), pp.secondary.S().clone())?;

        let secondary_plonk_trace = VanillaFS::generate_plonk_trace(
            pp.secondary.ck(),
            &secondary_instance,
            &secondary_witness,
            &secondary_nifs_pp,
            &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
        )?;

        Ok(Self {
            step: 1,
            debug_mode: false,
            secondary_nifs_pp,
            primary_nifs_pp,
            secondary_trace: [secondary_plonk_trace.clone()],
            primary: StepCircuitContext {
                z_0: primary_z_0,
                z_i: primary_z_output,
                relaxed_trace: primary_relaxed_trace,
                _p: PhantomData,
            },
            secondary: StepCircuitContext {
                z_0: secondary_z_0,
                z_i: secondary_z_output,
                relaxed_trace: secondary_relaxed_trace,
                _p: PhantomData,
            },
        })
    }

    #[instrument(name = "ivc_fold_step", skip_all, fields(step = self.step))]
    pub fn fold_step<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        secondary: &SC2,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let primary_span = info_span!("primary").entered();
        debug!("start fold step with folding 'secondary' by 'primary'");

        let (secondary_new_trace, secondary_cross_term_commits) = nifs::vanilla::VanillaFS::prove(
            pp.secondary.ck(),
            &self.secondary_nifs_pp,
            &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
            &self.secondary.relaxed_trace,
            &self.secondary_trace,
        )?;

        debug!("prepare primary td");

        // Prepare primary constraint system for folding
        let primary_z_next = primary.process_step(&self.primary.z_i, pp.primary.k_table_size())?;

        let primary_instance = {
            let _s = info_span!("generate_instance").entered();
            [
                util::fe_to_fe(&self.secondary_trace[0].u.instance[1]).unwrap(),
                RandomOracleComputationInstance::<'_, A1, C2, RP1::OffCircuit> {
                    random_oracle_constant: pp.primary.params().ro_constant().clone(),
                    public_params_hash: &pp.digest_2(),
                    step: self.step + 1,
                    z_0: &self.primary.z_0,
                    z_i: &primary_z_next,
                    relaxed: &secondary_new_trace.U,
                    limb_width: pp.secondary.params().limb_width(),
                    limbs_count: pp.secondary.params().limbs_count(),
                }
                .generate_with_inspect(|buf| debug!("primary X1 {}+1-step: {buf:?}", self.step)),
            ]
        };

        let primary_sfc = StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, T> {
            step_circuit: primary,
            input: StepInputs::<'_, A1, C2, RP1::OnCircuit> {
                step: C2::Base::from_u128(self.step as u128),
                step_pp: pp.primary.params(),
                public_params_hash: pp.digest_2(),
                z_0: self.primary.z_0,
                z_i: self.primary.z_i,
                U: self.secondary.relaxed_trace.U.clone(),
                u: self.secondary_trace[0].u.clone(),
                cross_term_commits: secondary_cross_term_commits,
            },
        };

        if self.debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.primary.k_table_size(),
                &primary_sfc,
                vec![primary_instance.to_vec()],
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, true, self.step))?;
        }

        let primary_witness = CircuitRunner::new(
            pp.primary.k_table_size(),
            primary_sfc,
            primary_instance.to_vec(),
        )
        .try_collect_witness()?;

        self.primary.z_i = primary_z_next;
        self.secondary.relaxed_trace = secondary_new_trace;

        let primary_plonk_trace = [VanillaFS::generate_plonk_trace(
            pp.primary.ck(),
            &primary_instance,
            &primary_witness,
            &self.primary_nifs_pp,
            &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone()),
        )?];

        let (primary_new_trace, primary_cross_term_commits) = nifs::vanilla::VanillaFS::prove(
            pp.primary.ck(),
            &self.primary_nifs_pp,
            &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone()),
            &self.primary.relaxed_trace,
            &primary_plonk_trace,
        )?;

        primary_span.exit();
        let _secondary_span = info_span!("secondary").entered();

        debug!("start fold step with folding 'primary' by 'secondary'");

        let next_secondary_z_i =
            secondary.process_step(&self.secondary.z_i, pp.secondary.k_table_size())?;

        let secondary_instance = {
            let _s = info_span!("generate_instance");
            [
                util::fe_to_fe(&primary_plonk_trace[0].u.instance[1]).unwrap(),
                RandomOracleComputationInstance::<'_, A2, C1, RP2::OffCircuit> {
                    random_oracle_constant: pp.secondary.params().ro_constant().clone(),
                    public_params_hash: &pp.digest_1(),
                    step: self.step + 1,
                    z_0: &self.secondary.z_0,
                    z_i: &next_secondary_z_i,
                    relaxed: &primary_new_trace.U,
                    limb_width: pp.primary.params().limb_width(),
                    limbs_count: pp.primary.params().limbs_count(),
                }
                .generate_with_inspect(|buf| debug!("secondary X1 {}+1-step: {buf:?}", self.step)),
            ]
        };

        let secondary_sfc = StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, T> {
            step_circuit: secondary,
            input: StepInputs::<'_, A2, C1, RP2::OnCircuit> {
                step: C1::Base::from_u128(self.step as u128),
                step_pp: pp.secondary.params(),
                public_params_hash: pp.digest_1(),
                z_0: self.secondary.z_0,
                z_i: self.secondary.z_i,
                U: self.primary.relaxed_trace.U.clone(),
                u: primary_plonk_trace[0].u.clone(),
                cross_term_commits: primary_cross_term_commits,
            },
        };

        if self.debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.secondary.k_table_size(),
                &secondary_sfc,
                vec![secondary_instance.to_vec()],
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, false, self.step))?;
        }

        let secondary_witness = CircuitRunner::new(
            pp.secondary.k_table_size(),
            secondary_sfc,
            secondary_instance.to_vec(),
        )
        .try_collect_witness()?;

        self.secondary.z_i = next_secondary_z_i;
        self.primary.relaxed_trace = primary_new_trace;

        self.secondary_trace = [VanillaFS::generate_plonk_trace(
            pp.secondary.ck(),
            &secondary_instance,
            &secondary_witness,
            &self.secondary_nifs_pp,
            &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
        )?];

        self.step += 1;

        Ok(())
    }

    #[instrument(name = "ivc_vefify", skip_all)]
    pub fn verify<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let mut errors = vec![];

        RandomOracleComputationInstance::<'_, A1, C2, RP1::OffCircuit> {
            random_oracle_constant: pp.primary.params().ro_constant().clone(),
            public_params_hash: &pp.digest_2(),
            step: self.step,
            z_0: &self.primary.z_0,
            z_i: &self.primary.z_i,
            relaxed: &self.secondary.relaxed_trace.U,
            limb_width: pp.secondary.params().limb_width(),
            limbs_count: pp.secondary.params().limbs_count(),
        }
        .generate_with_inspect::<C2::Scalar>(|buf| {
            debug!("primary X0 verify at {}-step: {buf:?}", self.step)
        })
        .ne(&self.secondary_trace[0].u.instance[0])
        .then(|| {
            errors.push(VerificationError::InstanceNotMatch {
                index: 0,
                is_primary: true,
            })
        });

        RandomOracleComputationInstance::<'_, A2, C1, RP2::OffCircuit> {
            random_oracle_constant: pp.secondary.params().ro_constant().clone(),
            public_params_hash: &pp.digest_1(),
            step: self.step,
            z_0: &self.secondary.z_0,
            z_i: &self.secondary.z_i,
            relaxed: &self.primary.relaxed_trace.U,
            limb_width: pp.secondary.params().limb_width(),
            limbs_count: pp.secondary.params().limbs_count(),
        }
        .generate_with_inspect::<C1::Scalar>(|buf| {
            debug!("primary X1 verify at {}-step: {buf:?}", self.step)
        })
        .ne(&util::fe_to_fe(&self.secondary_trace[0].u.instance[1]).unwrap())
        .then(|| {
            errors.push(VerificationError::InstanceNotMatch {
                index: 1,
                is_primary: false,
            });
        });

        if let Err(err) = pp.primary.S().is_sat_relaxed(
            pp.primary.ck(),
            &self.primary.relaxed_trace.U,
            &self.primary.relaxed_trace.W,
        ) {
            errors.push(VerificationError::NotSat {
                err,
                is_primary: true,
                is_relaxed: false,
            })
        }

        if let Err(err) = pp.secondary.S().is_sat_relaxed(
            pp.secondary.ck(),
            &self.secondary.relaxed_trace.U,
            &self.secondary.relaxed_trace.W,
        ) {
            errors.push(VerificationError::NotSat {
                err,
                is_primary: false,
                is_relaxed: true,
            })
        }

        if let Err(err) = pp.secondary.S().is_sat(
            pp.secondary.ck(),
            &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
            &self.secondary_trace[0].u,
            &self.secondary_trace[0].w,
        ) {
            errors.push(VerificationError::NotSat {
                err,
                is_primary: false,
                is_relaxed: true,
            })
        }

        if let Err(err) = pp
            .primary
            .S()
            .is_sat_perm(&self.primary.relaxed_trace.U, &self.primary.relaxed_trace.W)
        {
            errors.push(VerificationError::NotSat {
                err,
                is_primary: false,
                is_relaxed: true,
            })
        }

        if let Err(err) = pp.secondary.S().is_sat_perm(
            &self.secondary.relaxed_trace.U,
            &self.secondary.relaxed_trace.W,
        ) {
            errors.push(VerificationError::NotSat {
                err,
                is_primary: false,
                is_relaxed: true,
            })
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(Error::VerifyFailed(errors))
        }
    }
}
