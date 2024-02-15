use std::io;

use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2_proofs::circuit::floor_planner::single_pass::SingleChipLayouter;
use halo2curves::CurveAffine;
use log::*;
use serde::Serialize;

use crate::{
    constants::NUM_CHALLENGE_BITS,
    ivc::{
        public_params::{self, PublicParams},
        step_folding_circuit::{StepConfig, StepFoldingCircuit, StepInputs},
    },
    main_gate::MainGateConfig,
    nifs,
    nifs::{vanilla::VanillaFS, FoldingScheme},
    plonk::RelaxedPlonkTrace,
    poseidon::{random_oracle::ROTrait, AbsorbInRO, ROPair},
    sps,
    table::TableData,
};

pub use super::{
    floor_planner::{FloorPlanner, SimpleFloorPlanner},
    step_circuit::{self, StepCircuit, SynthesisError},
};

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
    Plonk(#[from] halo2_proofs::plonk::Error),
    #[error(transparent)]
    Step(#[from] step_circuit::SynthesisError),
    #[error("IVC Param not match")]
    IVCParamNotMatch,
    #[error("TODO")]
    WhileHash(io::Error),
    #[error("TODO")]
    Sps(#[from] sps::Error),
    #[error("TODO")]
    NIFS(#[from] nifs::Error),
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
    pub fn new<const T: usize, RP1, RP2>(
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
        // Prepare primary constraint system for folding
        let (mut primary_td, primary_step_config) = Self::prepare_primary_td::<T, RP1>(
            pp.primary.k_table_size,
            [C1::Scalar::ZERO, C1::Scalar::ZERO], // TODO #154 #160
        );

        // Prepare secondary constraint system for folding
        // & for take some metadata for zero round of primary circuit
        let (mut secondary_td, secondary_step_config) = Self::prepare_secondary_td::<T, RP2>(
            pp.secondary.k_table_size,
            [C2::Scalar::ZERO, C2::Scalar::ZERO], // TODO #154 #160
        );
        // For pp digest & for cross term commits lenght
        let pre_round_secondary_ps = secondary_td.plonk_structure().unwrap();

        let secondary_cross_term_commits = vec![
            C2::identity();
            pre_round_secondary_ps
                .get_degree_for_folding()
                .saturating_sub(1)
        ];

        // Not use `PublicParams::digest` for re-use calculated before plonk structures
        let pp_wrapper = public_params::PublicParamsDigestWrapper::<'_, C1, C2, RP1, RP2> {
            primary_plonk_struct: primary_td.plonk_structure().unwrap(),
            secondary_plonk_struct: pre_round_secondary_ps,
            primary_params: &pp.primary.params,
            secondary_params: &pp.secondary.params,
        };
        let primary_public_params_hash = pp_wrapper.digest().map_err(Error::WhileHash)?;
        let secondary_public_params_hash = pp_wrapper.digest().map_err(Error::WhileHash)?;

        // For use as first version of `U` in primary circuit synthesize
        let pre_round_secondary_plonk_trace = VanillaFS::generate_plonk_trace(
            pp.secondary.ck,
            &secondary_td,
            &VanillaFS::setup_params(primary_public_params_hash, &secondary_td)?.0,
            &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone()),
        )?;

        let primary_z_output = StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, T> {
            step_circuit: &primary,
            input: StepInputs::<'_, A1, C2, RP1::OnCircuit> {
                step: C2::Base::ZERO,
                step_pp: &pp.primary.params,
                public_params_hash: primary_public_params_hash,
                z_0: primary_z_0,
                z_i: primary_z_0,
                U: pre_round_secondary_plonk_trace.u.to_relax(),
                u: pre_round_secondary_plonk_trace.u,
                cross_term_commits: secondary_cross_term_commits,
            },
        }
        .synthesize(
            primary_step_config,
            &mut SingleChipLayouter::<'_, C1::Scalar, _>::new(&mut primary_td, vec![])?,
        )?;
        primary_td.postpone_assembly();

        // Start secondary
        let (primary_off_circuit_pp, _primary_off_circuit_vp) =
            VanillaFS::setup_params(secondary_public_params_hash, &primary_td)?;

        let primary_plonk_trace = VanillaFS::generate_plonk_trace(
            pp.primary.ck,
            &primary_td,
            &primary_off_circuit_pp,
            &mut RP2::OffCircuit::new(pp.secondary.params.ro_constant.clone()),
        )?;

        let primary_cross_term_commits = vec![
            C1::identity();
            primary_off_circuit_pp
                .S
                .get_degree_for_folding()
                .saturating_sub(1)
        ];

        let secondary_z_output = StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, T> {
            step_circuit: &secondary,
            input: StepInputs::<'_, A2, C1, RP2::OnCircuit> {
                step: C1::Base::ZERO,
                step_pp: &pp.secondary.params,
                public_params_hash: secondary_public_params_hash,
                z_0: secondary_z_0,
                z_i: secondary_z_0,
                U: primary_plonk_trace.u.to_relax(),
                u: primary_plonk_trace.u.clone(),
                cross_term_commits: primary_cross_term_commits,
            },
        }
        .synthesize(
            secondary_step_config,
            &mut SingleChipLayouter::<'_, C2::Scalar, _>::new(&mut secondary_td, vec![])?,
        )?;
        secondary_td.postpone_assembly();

        let secondary_plonk_trace = VanillaFS::generate_plonk_trace(
            pp.secondary.ck,
            &secondary_td,
            &VanillaFS::setup_params(primary_public_params_hash, &secondary_td)?.0,
            &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone()),
        )?;

        Ok(Self {
            step: 1,
            primary: StepCircuitContext {
                step_circuit: primary,
                z_0: primary_z_0,
                z_i: primary_z_output,
                relaxed_trace: primary_plonk_trace.to_relax(pp.primary.k_table_size as usize),
            },
            secondary: StepCircuitContext {
                step_circuit: secondary,
                z_0: secondary_z_0,
                z_i: secondary_z_output,
                relaxed_trace: secondary_plonk_trace.to_relax(pp.secondary.k_table_size as usize),
            },
        })
    }

    pub fn prove_step<const T: usize, RP1, RP2>(
        &mut self,
        _pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        _z0_primary: [C1::Scalar; A1],
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar>,
        RP2: ROPair<C2::Scalar>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::prove_step`")
    }

    pub fn verify<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        num_steps: usize,
        z0_primary: [C1::Scalar; A1],
        z0_secondary: [C2::Scalar; A2],
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let is_step_zero = num_steps == 0;
        let is_num_step_not_match = num_steps != self.step;
        let is_inputs_match = self.primary.z_0 != z0_primary || self.secondary.z_0 != z0_secondary;
        if is_step_zero || is_num_step_not_match || is_inputs_match {
            return Err(Error::IVCParamNotMatch);
        }

        // verify X0
        let ro1 = &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone());
        ro1.absorb_point(&pp.digest::<C2>().unwrap());
        ro1.absorb_field(C1::Scalar::from_u128(num_steps as u128));
        z0_primary.iter().for_each(|val| {
            ro1.absorb_field(*val);
        });
        self.primary
            .z_i
            .iter()
            .for_each(|val| ro1.absorb_field(*val));
        self.secondary.relaxed_trace.U.absorb_into(ro1);
        let _hash_primary = ro1.squeeze::<C2>(NUM_CHALLENGE_BITS);
        // TODO: uncomment after adding secondary_trace field in IVC
        // assert_eq!(hash_primary, self.secondary_trace.U.X0);

        // verify X1
        let ro2 = &mut RP2::OffCircuit::new(pp.secondary.params.ro_constant.clone());
        ro2.absorb_point(&pp.digest::<C1>().unwrap());
        ro2.absorb_field(C2::Scalar::from_u128(num_steps as u128));
        z0_secondary.iter().for_each(|val| {
            ro2.absorb_field(*val);
        });
        self.secondary
            .z_i
            .iter()
            .for_each(|val| ro2.absorb_field(*val));
        self.primary.relaxed_trace.U.absorb_into(ro2);
        let _hash_secondary = ro2.squeeze::<C1>(NUM_CHALLENGE_BITS);
        // TODO: uncomment after adding secondary_trace field in IVC
        // assert_eq!(hash_secondary, self.secondary_trace.U.X1);

        // check satisfiability
        // TODO: avoid create PlonkStructure again
        let (primary_td, _) = Self::prepare_primary_td::<T, RP1>(
            pp.primary.k_table_size,
            [C1::Scalar::ZERO, C1::Scalar::ZERO],
        );
        let S1 = primary_td.plonk_structure().unwrap();
        assert_eq!(
            S1.is_sat_relaxed(
                pp.primary.ck,
                &self.primary.relaxed_trace.U,
                &self.primary.relaxed_trace.W
            )
            .err(),
            None
        );

        let (secondary_td, _) = Self::prepare_secondary_td::<T, RP2>(
            pp.secondary.k_table_size,
            [C2::Scalar::ZERO, C2::Scalar::ZERO],
        );
        let S2 = secondary_td.plonk_structure().unwrap();
        assert_eq!(
            S2.is_sat_relaxed(
                pp.secondary.ck,
                &self.secondary.relaxed_trace.U,
                &self.secondary.relaxed_trace.W
            )
            .err(),
            None
        );
        // TODO: uncomment after adding secondary_trace in IVC
        // assert_eq!(S2.is_sat(pp.secondary.ck, &self.secondary_trace.U, &self.secondary_trace.W).err(), None);

        Ok(())
    }

    fn prepare_primary_td<const T: usize, RP1>(
        k_table_size: u32,
        instance: [C1::Scalar; 2],
    ) -> (TableData<C1::Scalar>, StepConfig<A1, C1::Scalar, SC1, T>)
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
    {
        let mut primary_td = TableData::new(k_table_size, instance.to_vec());
        // TODO #146 Add information about fixed
        let config = primary_td.prepare_assembly(
            <crate::ivc::step_folding_circuit::StepFoldingCircuit<
                '_,
                A1,
                C2,
                SC1,
                RP1::OnCircuit,
                T,
            > as StepCircuit<A1, C1::Scalar>>::configure,
        );

        (primary_td, config)
    }

    fn prepare_secondary_td<const T: usize, RP2>(
        k_table_size: u32,
        instance: [C2::Scalar; 2],
    ) -> (TableData<C2::Scalar>, StepConfig<A2, C2::Scalar, SC2, T>)
    where
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let mut secondary_td = TableData::new(k_table_size, instance.to_vec());

        // TODO #146 Add information about fixed
        let config = secondary_td.prepare_assembly(
            <crate::ivc::step_folding_circuit::StepFoldingCircuit<
                '_,
                A2,
                C1,
                SC2,
                RP2::OnCircuit,
                T,
            > as StepCircuit<A2, C2::Scalar>>::configure,
        );

        (secondary_td, config)
    }
}
