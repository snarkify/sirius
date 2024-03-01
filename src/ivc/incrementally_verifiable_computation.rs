use std::{io, num::NonZeroUsize};

use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2curves::CurveAffine;
use log::*;
use serde::Serialize;

use crate::{
    ivc::{
        public_params::PublicParams,
        step_folding_circuit::{StepFoldingCircuit, StepInputs},
    },
    main_gate::MainGateConfig,
    nifs::{self, vanilla::VanillaFS, FoldingScheme},
    plonk::{PlonkTrace, RelaxedPlonkTrace},
    poseidon::{random_oracle::ROTrait, ROPair},
    sps,
    table::CircuitRunner,
};

use super::instance_computation::RandomOracleComputationInstance;
pub use super::step_circuit::StepCircuit;

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::Scalar>,
{
    step_circuit: SC,
    relaxed_trace: RelaxedPlonkTrace<C>,
    z_0: [C::Scalar; ARITY],
    z_i: [C::Scalar; ARITY],
}

// TODO #31 docs
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Halo2(#[from] halo2_proofs::plonk::Error),
    #[error(transparent)]
    Plonk(#[from] crate::plonk::Error),
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
    VerifyFailed(#[from] VerificationError),
}

#[derive(Debug, thiserror::Error)]
pub enum VerificationError {
    #[error("TODO")]
    InstanceNotMatch { index: usize, is_primary: bool },
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
    secondary_trace: PlonkTrace<C2>,
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
    pub fn fold<const T: usize, RP1, RP2>(
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        primary: SC1,
        primary_z_0: [C1::Scalar; A1],
        secondary: SC2,
        secondary_z_0: [C2::Scalar; A2],
        num_steps: NonZeroUsize,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let mut ivc = IVC::new(pp, primary, primary_z_0, secondary, secondary_z_0)?;

        for _step in 1..=num_steps.get() {
            ivc.fold_step(pp)?;
        }

        ivc.verify(pp)?;

        Ok(())
    }

    fn new<const T: usize, RP1, RP2>(
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        primary: SC1,
        primary_z_0: [C1::Scalar; A1],
        secondary: SC2,
        secondary_z_0: [C2::Scalar; A2],
    ) -> Result<Self, Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let primary_public_params_hash = pp.digest1().map_err(Error::WhileHash)?;
        let secondary_public_params_hash = pp.digest2().map_err(Error::WhileHash)?;

        let (u, _w) = pp.secondary.S.dry_run_sps_protocol();
        let secondary_cross_term_commits =
            vec![C2::identity(); pp.secondary.S.get_degree_for_folding().saturating_sub(1)];

        let primary_step_folding_circuit = StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, T> {
            step_circuit: &primary,
            input: StepInputs::<'_, A1, C2, RP1::OnCircuit> {
                step: C2::Base::ZERO,
                step_pp: &pp.primary.params,
                public_params_hash: secondary_public_params_hash,
                z_0: primary_z_0,
                z_i: primary_z_0,
                U: u.to_relax(),
                u: u.clone(),
                cross_term_commits: secondary_cross_term_commits,
            },
        };

        let primary_z_next = primary.process_step(&primary_z_0)?;
        let (primary_X0, primary_X1) = (
            RandomOracleComputationInstance::<'_, A1, _, RP1::OffCircuit> {
                random_oracle_constant: pp.primary.params.ro_constant.clone(),
                public_params_hash: &secondary_public_params_hash,
                step: 0,
                z_0: &primary_z_0,
                z_i: &primary_z_0,
                relaxed: &u.to_relax(),
                limb_width: pp.primary.params.limb_width,
                limbs_count: pp.primary.params.limbs_count,
            }
            .generate(),
            RandomOracleComputationInstance::<'_, A1, _, RP1::OffCircuit> {
                random_oracle_constant: pp.primary.params.ro_constant.clone(),
                public_params_hash: &secondary_public_params_hash,
                step: 1,
                z_0: &primary_z_0,
                z_i: &primary_z_next,
                relaxed: &u.to_relax(),
                limb_width: pp.primary.params.limb_width,
                limbs_count: pp.primary.params.limbs_count,
            }
            .generate(),
        );

        let primary_td = CircuitRunner::new(
            pp.primary.k_table_size,
            primary_step_folding_circuit,
            vec![primary_X0, primary_X1],
        );
        let primary_witness = primary_td.try_collect_witness()?;
        let primary_nifs_pp =
            VanillaFS::setup_params(primary_public_params_hash, pp.primary.S.clone())?.0;
        let primary_trace = VanillaFS::generate_plonk_trace(
            pp.primary.ck,
            &[primary_X0, primary_X1],
            &primary_witness,
            &primary_nifs_pp,
            &mut RP2::OffCircuit::new(pp.secondary.params.ro_constant.clone()),
        )?;

        // Start secondary
        let (u, _w) = pp.primary.S.dry_run_sps_protocol();
        let primary_cross_term_commits =
            vec![C1::identity(); pp.primary.S.get_degree_for_folding().saturating_sub(1)];
        let secondary_step_folding_circuit =
            StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, T> {
                step_circuit: &secondary,
                input: StepInputs::<'_, A2, C1, RP2::OnCircuit> {
                    step: C1::Base::ZERO,
                    step_pp: &pp.secondary.params,
                    public_params_hash: primary_public_params_hash,
                    z_0: secondary_z_0,
                    z_i: secondary_z_0,
                    U: u.to_relax(),
                    u,
                    cross_term_commits: primary_cross_term_commits,
                },
            };

        let secondary_z_next = secondary.process_step(&secondary_z_0)?;
        let (secondary_X0, secondary_X1) = (
            RandomOracleComputationInstance::<'_, A2, _, RP2::OffCircuit> {
                random_oracle_constant: pp.secondary.params.ro_constant.clone(),
                public_params_hash: &primary_public_params_hash,
                step: 0,
                z_0: &secondary_z_0,
                z_i: &secondary_z_0,
                relaxed: &primary_trace.u.to_relax(),
                limb_width: pp.secondary.params.limb_width,
                limbs_count: pp.secondary.params.limbs_count,
            }
            .generate(),
            RandomOracleComputationInstance::<'_, A2, _, RP2::OffCircuit> {
                random_oracle_constant: pp.secondary.params.ro_constant.clone(),
                public_params_hash: &primary_public_params_hash,
                step: 1,
                z_0: &secondary_z_0,
                z_i: &secondary_z_next,
                relaxed: &primary_trace.u.to_relax(),
                limb_width: pp.secondary.params.limb_width,
                limbs_count: pp.secondary.params.limbs_count,
            }
            .generate(),
        );

        let secondary_td = CircuitRunner::new(
            pp.secondary.k_table_size,
            secondary_step_folding_circuit,
            vec![secondary_X0, secondary_X1],
        );
        let secondary_witness = secondary_td.try_collect_witness()?;
        let secondary_nifs_pp =
            VanillaFS::setup_params(secondary_public_params_hash, pp.secondary.S.clone())?.0;
        let secondary_trace = VanillaFS::generate_plonk_trace(
            pp.secondary.ck,
            &[secondary_X0, secondary_X1],
            &secondary_witness,
            &secondary_nifs_pp,
            &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone()),
        )?;

        Ok(Self {
            step: 1,
            primary_nifs_pp,
            secondary_nifs_pp,
            secondary_trace: secondary_trace.clone(),
            primary: StepCircuitContext {
                step_circuit: primary,
                z_0: primary_z_0,
                z_i: primary_z_next,
                relaxed_trace: primary_trace.to_relax(pp.primary.k_table_size as usize),
            },
            secondary: StepCircuitContext {
                step_circuit: secondary,
                z_0: secondary_z_0,
                z_i: secondary_z_next,
                relaxed_trace: secondary_trace.to_relax(pp.secondary.k_table_size as usize),
            },
        })
    }

    fn fold_step<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        debug!("start fold step with folding 'secondary' by 'primary'");

        debug!("start prove secondary trace");
        let (secondary_new_trace, secondary_cross_term_commits) = nifs::vanilla::VanillaFS::prove(
            pp.secondary.ck,
            &self.secondary_nifs_pp,
            &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone()),
            &self.secondary.relaxed_trace,
            &self.secondary_trace,
        )?;

        // Prepare primary constraint system for folding
        let primary_z_next = self.primary.step_circuit.process_step(&self.primary.z_i)?;
        let (primary_X0, primary_X1) = (
            RandomOracleComputationInstance::<'_, A1, _, RP1::OffCircuit> {
                random_oracle_constant: pp.primary.params.ro_constant.clone(),
                public_params_hash: &pp.digest2().map_err(Error::WhileHash)?,
                step: self.step,
                z_0: &self.primary.z_0,
                z_i: &self.primary.z_i,
                relaxed: &self.secondary.relaxed_trace.U,
                limb_width: pp.primary.params.limb_width,
                limbs_count: pp.primary.params.limbs_count,
            }
            .generate(),
            RandomOracleComputationInstance::<'_, A1, _, RP1::OffCircuit> {
                random_oracle_constant: pp.primary.params.ro_constant.clone(),
                public_params_hash: &pp.digest2().map_err(Error::WhileHash)?,
                step: self.step + 1,
                z_0: &self.primary.z_0,
                z_i: &primary_z_next,
                relaxed: &secondary_new_trace.U,
                limb_width: pp.primary.params.limb_width,
                limbs_count: pp.primary.params.limbs_count,
            }
            .generate(),
        );
        let primary_step_folding_circuit = StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, T> {
            step_circuit: &self.primary.step_circuit,
            input: StepInputs::<'_, A1, C2, RP1::OnCircuit> {
                step: C2::Base::from_u128(self.step as u128),
                step_pp: &pp.primary.params,
                public_params_hash: pp.digest2().map_err(Error::WhileHash)?,
                z_0: self.primary.z_0,
                z_i: self.primary.z_i,
                U: self.secondary.relaxed_trace.U.clone(),
                u: self.secondary_trace.u.clone(),
                cross_term_commits: secondary_cross_term_commits,
            },
        };

        debug!("start synthesize of 'step_folding_circuit' for primary");
        let primary_td = CircuitRunner::new(
            pp.primary.k_table_size,
            primary_step_folding_circuit,
            vec![primary_X0, primary_X1],
        );
        let primary_witness = primary_td.try_collect_witness()?;
        self.primary.z_i = primary_z_next;
        self.secondary.relaxed_trace = secondary_new_trace;

        debug!("start generate primary plonk trace");
        let primary_plonk_trace = VanillaFS::generate_plonk_trace(
            pp.primary.ck,
            &[primary_X0, primary_X1],
            &primary_witness,
            &self.primary_nifs_pp,
            &mut RP2::OffCircuit::new(pp.secondary.params.ro_constant.clone()),
        )?;

        debug!("start prove primary trace");
        let (primary_new_trace, primary_cross_term_commits) = nifs::vanilla::VanillaFS::prove(
            pp.primary.ck,
            &self.primary_nifs_pp,
            &mut RP2::OffCircuit::new(pp.secondary.params.ro_constant.clone()),
            &self.primary.relaxed_trace,
            &primary_plonk_trace,
        )?;

        debug!("start fold step with folding 'primary' by 'secondary'");
        let secondary_z_next = self
            .secondary
            .step_circuit
            .process_step(&self.secondary.z_i)?;

        let (secondary_X0, secondary_X1) = (
            RandomOracleComputationInstance::<'_, A2, _, RP2::OffCircuit> {
                random_oracle_constant: pp.secondary.params.ro_constant.clone(),
                public_params_hash: &pp.digest1().map_err(Error::WhileHash)?,
                step: self.step,
                z_0: &self.secondary.z_0,
                z_i: &self.secondary.z_i,
                relaxed: &self.primary.relaxed_trace.U,
                limb_width: pp.secondary.params.limb_width,
                limbs_count: pp.secondary.params.limbs_count,
            }
            .generate(),
            RandomOracleComputationInstance::<'_, A2, _, RP2::OffCircuit> {
                random_oracle_constant: pp.secondary.params.ro_constant.clone(),
                public_params_hash: &pp.digest1().map_err(Error::WhileHash)?,
                step: self.step + 1,
                z_0: &self.secondary.z_0,
                z_i: &self
                    .secondary
                    .step_circuit
                    .process_step(&self.secondary.z_i)?,
                relaxed: &primary_new_trace.U,
                limb_width: pp.secondary.params.limb_width,
                limbs_count: pp.secondary.params.limbs_count,
            }
            .generate(),
        );

        let secondary_step_folding_circuit =
            StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, T> {
                step_circuit: &self.secondary.step_circuit,
                input: StepInputs::<'_, A2, C1, RP2::OnCircuit> {
                    step: C1::Base::from_u128(self.step as u128),
                    step_pp: &pp.secondary.params,
                    public_params_hash: pp.digest1().map_err(Error::WhileHash)?,
                    z_0: self.secondary.z_0,
                    z_i: self.secondary.z_i,
                    U: self.primary.relaxed_trace.U.clone(),
                    u: primary_plonk_trace.u.clone(),
                    cross_term_commits: primary_cross_term_commits,
                },
            };

        debug!("start synthesize of 'step_folding_circuit' for secondary");
        let secondary_td = CircuitRunner::new(
            pp.secondary.k_table_size,
            secondary_step_folding_circuit,
            vec![secondary_X0, secondary_X1],
        );
        let secondary_witness = secondary_td.try_collect_witness()?;
        self.secondary.z_i = secondary_z_next;
        self.primary.relaxed_trace = primary_new_trace;

        debug!("start generate secondary plonk trace");
        self.secondary_trace = VanillaFS::generate_plonk_trace(
            pp.secondary.ck,
            &[secondary_X0, secondary_X1],
            &secondary_witness,
            &self.secondary_nifs_pp,
            &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone()),
        )?;

        Ok(())
    }

    fn verify<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let expected_X0 = RandomOracleComputationInstance::<'_, A1, _, RP1::OffCircuit> {
            random_oracle_constant: pp.primary.params.ro_constant.clone(),
            public_params_hash: &pp.digest2().map_err(Error::WhileHash)?,
            step: self.step,
            z_0: &self.primary.z_0,
            z_i: &self.primary.z_i,
            relaxed: &self.secondary.relaxed_trace.U,
            limb_width: pp.primary.params.limb_width,
            limbs_count: pp.primary.params.limbs_count,
        }
        .generate::<C2::Scalar>();

        if expected_X0 != self.secondary.relaxed_trace.U.instance[0] {
            return Err(Error::VerifyFailed(VerificationError::InstanceNotMatch {
                index: 0,
                is_primary: true,
            }));
        }

        let expected_X1 = RandomOracleComputationInstance::<'_, A2, _, RP2::OffCircuit> {
            random_oracle_constant: pp.secondary.params.ro_constant.clone(),
            public_params_hash: &pp.digest1().map_err(Error::WhileHash)?,
            step: self.step,
            z_0: &self.secondary.z_0,
            z_i: &self.secondary.z_i,
            relaxed: &self.primary.relaxed_trace.U,
            limb_width: pp.secondary.params.limb_width,
            limbs_count: pp.secondary.params.limbs_count,
        }
        .generate::<C1::Scalar>();

        if expected_X1 != self.primary.relaxed_trace.U.instance[1] {
            return Err(Error::VerifyFailed(VerificationError::InstanceNotMatch {
                index: 1,
                is_primary: false,
            }));
        }

        pp.primary.S.is_sat_relaxed(
            pp.primary.ck,
            &self.primary.relaxed_trace.U,
            &self.primary.relaxed_trace.W,
        )?;

        pp.secondary.S.is_sat_relaxed(
            pp.secondary.ck,
            &self.secondary.relaxed_trace.U,
            &self.secondary.relaxed_trace.W,
        )?;

        pp.secondary.S.is_sat(
            pp.secondary.ck,
            &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone()),
            &self.secondary_trace.u,
            &self.secondary_trace.w,
        )?;

        Ok(())
    }
}
