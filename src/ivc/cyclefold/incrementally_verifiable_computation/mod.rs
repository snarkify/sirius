use std::{marker::PhantomData, num::NonZeroUsize};

use tracing::info_span;

use super::{
    ro,
    support_circuit::{self, SupportCircuit},
};
use crate::{
    halo2_proofs::halo2curves::{
        ff::{FromUniformBytes, PrimeFieldBits},
        group::prime::PrimeCurveAffine,
        CurveAffine,
    },
    ivc::{
        cyclefold::sfc::{self, StepFoldingCircuit},
        StepCircuit,
    },
    nifs::{
        self,
        protogalaxy::{AccumulatorArgs, ProtoGalaxy},
        sangria::VanillaFS as SangriaFS,
    },
    plonk::PlonkTrace,
    table::CircuitRunner,
};

mod public_params;
pub use public_params::PublicParams;

pub struct IVC<const ARITY: usize, CMain, CSup, SC>
where
    CMain: CurveAffine<Base = <CSup as PrimeCurveAffine>::Scalar>,
    CSup: CurveAffine<Base = <CMain as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<ARITY, CMain::Scalar>,
    CMain::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    CSup::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    step: NonZeroUsize,
    primary_trace: PlonkTrace<CMain>,
    z_next: [CMain::Scalar; ARITY],
    _p: PhantomData<(CMain, CSup, SC)>,
}

impl<const ARITY: usize, CMain, CSup, SC> IVC<ARITY, CMain, CSup, SC>
where
    CMain: CurveAffine<Base = <CSup as PrimeCurveAffine>::Scalar>,
    CSup: CurveAffine<Base = <CMain as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<ARITY, CMain::Scalar>,
    CMain::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    CSup::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new(
        pp: &PublicParams<ARITY, ARITY, CMain, CSup, SC>,
        sc: &SC,
        z_0: [CMain::ScalarExt; ARITY],
    ) -> Self {
        let _primary_span = info_span!("ivc::new", step = 0).entered();

        let initial_self_acc = ProtoGalaxy::<CMain, 1>::new_accumulator(
            AccumulatorArgs::from(&pp.primary_S),
            &nifs::protogalaxy::ProverParam {
                S: pp.primary_S.clone(),
                pp_digest: pp.cmain_pp_digest(),
            },
            &mut ro(),
        );

        // At zero step cyclefold ivc - output protogalaxy-accumulator is input
        // protogalaxy-accumulator. Bug proof still should be valid.
        let (_new_acc, self_proof) = ProtoGalaxy::prove(
            &pp.primary_ck,
            &nifs::protogalaxy::ProverParam {
                S: pp.primary_S.clone(),
                pp_digest: pp.cmain_pp_digest(),
            },
            &mut ro(),
            initial_self_acc.clone(),
            &[pp.primary_initial_trace.clone()],
        )
        .unwrap();

        // At zero step cyclefold ivc - output sangria-accumulator is input
        // sangria-accumulator. Bug proofs still should be valid.
        //
        // At this block we fold three same support-circuit initial traces (from pp) but result of
        // this folding will be not used in next step, because of zero step
        let paired_incoming = {
            let _support = info_span!("support").entered();
            let mut proofs = Vec::with_capacity(initial_self_acc.W_commitment_len());

            let mut paired_acc_ptr = nifs::sangria::accumulator::RelaxedPlonkTrace::from_regular(
                pp.support_initial_trace.clone(),
                SupportCircuit::<CMain>::MIN_K_TABLE_SIZE as usize,
            );

            for _ in 0..initial_self_acc.W_commitment_len() {
                let (new_acc, paired_proof) =
                    SangriaFS::<CSup, { support_circuit::INSTANCES_LEN }>::prove(
                        &pp.support_ck,
                        &nifs::sangria::ProverParam {
                            S: pp.support_S.clone(),
                            pp_digest: pp.csup_pp_digest(),
                        },
                        &mut ro(),
                        paired_acc_ptr,
                        &[pp.support_initial_trace.clone()],
                    )
                    .unwrap();

                proofs.push((pp.support_initial_trace.u.clone(), paired_proof));

                paired_acc_ptr = new_acc;
            }

            proofs
        };

        let primary_sfc = StepFoldingCircuit::<'_, ARITY, CMain, CSup, SC> {
            sc,
            input: sfc::InputBuilder {
                step: 0,
                pp_digest: pp.csup_pp_digest(),
                self_incoming: &pp.primary_initial_trace.u,
                self_proof,
                paired_acc: &pp.support_initial_trace.u.clone().into(),
                paired_incoming: paired_incoming.as_slice(),
                self_acc: &initial_self_acc.into(),
                z_i: z_0,
                z_0,
            }
            .build(),
            _p: PhantomData,
        };

        let primary_initial_instances = primary_sfc.initial_instances();

        #[cfg(test)]
        {
            let _mock = info_span!("mock-debug").entered();
            crate::halo2_proofs::dev::MockProver::run(
                pp.primary_k_table_size,
                &primary_sfc,
                primary_initial_instances.clone(),
            )
            .unwrap()
            .verify()
            .unwrap();
        }

        let primary_witness = CircuitRunner::new(
            pp.primary_k_table_size,
            primary_sfc,
            primary_initial_instances.clone(),
        )
        .try_collect_witness()
        .unwrap();

        let primary_post_initial_trace = ProtoGalaxy::<CMain, 1>::generate_plonk_trace(
            &pp.primary_ck,
            &primary_initial_instances,
            &primary_witness,
            &pp.protogalaxy_prover_params(),
            &mut ro(),
        )
        .unwrap();

        Self {
            step: NonZeroUsize::new(1).unwrap(),
            z_next: z_0,
            primary_trace: primary_post_initial_trace,
            _p: PhantomData,
        }
    }

    pub fn next(&mut self) {

    }
}

#[cfg(test)]
mod tests {
    use std::{array, path::Path};

    use tracing::*;
    use tracing_test::traced_test;

    use crate::{
        commitment::CommitmentKey,
        halo2_proofs::arithmetic::Field,
        ivc::step_circuit::trivial,
        prelude::bn256::{C1Affine, C1Scalar, C2Affine},
    };

    /// Arity : Input/output size per fold-step for primary step-circuit
    /// For tivial case it can be any number
    const ARITY: usize = 5;

    /// Key size for Primary Circuit
    const PRIMARY_COMMITMENT_KEY_SIZE: usize = 21;
    const SECONDARY_COMMITMENT_KEY_SIZE: usize = 21;

    const PRIMARY_CIRCUIT_TABLE_SIZE: u32 = 18;

    const FOLDER: &str = ".cache/examples";

    #[traced_test]
    #[test]
    fn trivial_zero_step() {
        let sc = trivial::Circuit::<ARITY, C1Scalar>::default();

        let primary_commitment_key = unsafe {
            CommitmentKey::<C1Affine>::load_or_setup_cache(
                Path::new(FOLDER),
                "bn256",
                PRIMARY_COMMITMENT_KEY_SIZE,
            )
            .unwrap()
        };

        let secondary_commitment_key = unsafe {
            CommitmentKey::<C2Affine>::load_or_setup_cache(
                Path::new(FOLDER),
                "grumpkin",
                SECONDARY_COMMITMENT_KEY_SIZE,
            )
            .unwrap()
        };

        info!("ck generated");

        let pp = super::PublicParams::new(
            &sc,
            primary_commitment_key,
            secondary_commitment_key,
            PRIMARY_CIRCUIT_TABLE_SIZE,
        );
        info!("pp created");

        let _ivc = super::IVC::new(&pp, &sc, array::from_fn(|_| C1Scalar::ZERO));
    }
}
