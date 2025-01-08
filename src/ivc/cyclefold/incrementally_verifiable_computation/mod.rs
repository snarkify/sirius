use std::{marker::PhantomData, num::NonZeroUsize};

use itertools::Itertools;
use tracing::{error, info_span, trace};

use super::{
    ro,
    support_circuit::{self, SupportCircuit},
};
use crate::{
    constants::MAX_BITS,
    halo2_proofs::{
        halo2curves::{
            ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits},
            group::prime::PrimeCurveAffine,
            CurveAffine,
        },
        plonk::Error as Halo2PlonkError,
    },
    ivc::{
        cyclefold::sfc::{self, StepFoldingCircuit},
        step_circuit, StepCircuit,
    },
    nifs::{
        self,
        protogalaxy::{AccumulatorArgs, ProtoGalaxy},
        sangria::VanillaFS,
    },
    plonk::{eval, PlonkTrace},
    polynomial::lagrange,
    poseidon::random_oracle::ROTrait,
    prelude::CommitmentKey,
    table::CircuitRunner,
    util,
};

type SangriaFS<C> = VanillaFS<C, { support_circuit::INSTANCES_LEN }>;

type SangriaRelaxedPlonkTrace<C> =
    nifs::sangria::RelaxedPlonkTrace<C, { support_circuit::INSTANCES_LEN }>;

type SangriaFoldablePlonkInstance<C> =
    nifs::sangria::accumulator::FoldablePlonkInstance<C, { support_circuit::INSTANCES_LEN }>;

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

    primary_acc: nifs::protogalaxy::Accumulator<CMain>,
    primary_trace: PlonkTrace<CMain>,
    primary_z_current: [CMain::Scalar; ARITY],
    primary_z_0: [CMain::Scalar; ARITY],

    support_acc: nifs::sangria::RelaxedPlonkTrace<CSup, { support_circuit::INSTANCES_LEN }>,

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
        pp: &mut PublicParams<ARITY, CMain, CSup, SC>,
        sc: &SC,
        z_0: [CMain::ScalarExt; ARITY],
    ) -> Result<Self, Error<CMain>> {
        let _span = info_span!("ivc_new", step = 0).entered();

        let primary_initial_acc = ProtoGalaxy::<CMain, 1>::new_accumulator(
            AccumulatorArgs::from(&pp.primary_S),
            &pp.protogalaxy_prover_params(),
            &mut ro(),
            pp.primary_initial_trace.clone(),
        )
        .map_err(Error::WhileProtoGalaxyAccCreation)?;

        // At zero step cyclefold ivc - output protogalaxy-accumulator is input
        // protogalaxy-accumulator. Bug proof still should be valid.
        let mut random_oracle = ro();
        let (_new_acc, self_proof) = ProtoGalaxy::prove(
            &pp.primary_ck,
            &pp.protogalaxy_prover_params(),
            &mut random_oracle,
            primary_initial_acc.clone(),
            &[pp.primary_initial_trace.clone()],
        )?;

        #[cfg(test)]
        {
            ProtoGalaxy::<CMain, 1>::is_sat(&pp.primary_ck, &pp.primary_S, &_new_acc)
                .expect("initial primary accumulator not corrent");

            assert_eq!(
                ProtoGalaxy::verify(
                    &pp.protogalaxy_verifier_params(),
                    &mut ro(),
                    &mut ro(),
                    &primary_initial_acc.clone().into(),
                    &[pp.primary_initial_trace.u.clone()],
                    &self_proof,
                )
                .expect("while verification after first prove"),
                _new_acc.into()
            );
        }

        let support_initial_acc = nifs::sangria::accumulator::RelaxedPlonkTrace::from_regular(
            pp.support_initial_trace.clone(),
            SupportCircuit::<CMain>::MIN_K_TABLE_SIZE as usize,
        );

        // At zero step cyclefold ivc - output sangria-accumulator is input
        // sangria-accumulator. Bug proofs still should be valid.
        let SupportCircuitFoldResult {
            new_accumulator: _new_new_accumulator,
            incoming: support_incoming,
        } = fold_support_circuit::<CMain, CSup>(
            &pp.support_ck,
            &pp.sangria_prover_params(),
            &support_initial_acc,
            primary_initial_acc
                .u
                .W_commitments
                .iter()
                .copied()
                .zip_eq(pp.primary_initial_trace.u.W_commitments.iter().copied()),
            CMain::Base::ZERO, // for zero step
            CMain::Base::ZERO, // for zero step
        )?;

        let primary_sfc = StepFoldingCircuit::<'_, ARITY, CMain, CSup, SC> {
            sc,
            input: sfc::InputBuilder {
                step: 0,
                pp_digest: pp.pp_digest_coordinates(),
                self_incoming: &pp.primary_initial_trace.u,
                self_proof,
                support_acc: &pp.support_initial_trace.u.clone().into(),
                support_incoming: support_incoming.as_slice(),
                self_acc: &primary_initial_acc.clone().into(),
                z_i: z_0,
                z_0,
            }
            .build(),
            _p: PhantomData,
        };

        let primary_initial_instances = primary_sfc.initial_instances();

        #[cfg(test)]
        {
            let _mock = info_span!("mock_debug").entered();
            crate::halo2_proofs::dev::MockProver::run(
                pp.primary_k_table_size,
                &primary_sfc,
                primary_initial_instances.clone(),
            )
            .unwrap()
            .verify()
            .unwrap();
        }

        let primary_cr = CircuitRunner::new(
            pp.primary_k_table_size,
            primary_sfc,
            primary_initial_instances.clone(),
        );
        let primary_witness = primary_cr
            .try_collect_witness()
            .map_err(|err| Error::WhileCollectPrimaryWitness { step: 0, err })?;
        pp.primary_S = primary_cr
            .try_collect_plonk_structure()
            .map_err(|err| Error::WhileCollectPrimaryS { err })?;

        let primary_post_initial_trace = ProtoGalaxy::<CMain, 1>::generate_plonk_trace(
            &pp.primary_ck,
            &primary_initial_instances,
            &primary_witness,
            &pp.protogalaxy_prover_params(),
            &mut ro(),
        )?;

        Ok(Self {
            step: NonZeroUsize::new(1).expect("safe: 1 != 0"),
            // Because zero step using input values for output without any folding (only formal
            // on-circuit) - we just take initial acc-s & z_0
            primary_z_current: z_0,
            primary_z_0: z_0,
            primary_trace: primary_post_initial_trace,
            primary_acc: primary_initial_acc,
            support_acc: support_initial_acc,
            _p: PhantomData,
        })
    }

    pub fn next(
        self,
        pp: &PublicParams<ARITY, CMain, CSup, SC>,
        sc: &SC,
    ) -> Result<Self, Error<CMain>> {
        let _span = info_span!("ivc_next", step = self.step.get()).entered();

        let Self {
            step,
            primary_acc,
            primary_trace,
            primary_z_current,
            primary_z_0,
            support_acc,
            _p,
        } = self;

        let mut random_oracle = ro();
        let (primary_next_acc, primary_proof) = ProtoGalaxy::prove(
            &pp.primary_ck,
            &pp.protogalaxy_prover_params(),
            &mut random_oracle,
            primary_acc.clone(),
            &[primary_trace.clone()],
        )
        .unwrap();

        // Inside `prove` we use several challenges generated from `random oracle`. Since we
        // delegate the `W_commitment` calculations to the `upport_circuit` we need `gamma` to
        // repeat them. We take advantage of the fact that `gamma` is generated last and thus
        // retrieve it
        let gamma = random_oracle.squeeze::<CMain::ScalarExt>(MAX_BITS);

        // Within protogalaxy::prove there is a calculation of L0(gamma), L1(gamma), we repeat
        // these calculations to reuse them in the support circuit
        let [l0, l1] = lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, 1)
            .take(2)
            .map(|v| util::fe_to_fe(&v).unwrap())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let SupportCircuitFoldResult {
            new_accumulator: support_next_acc,
            incoming: support_incoming,
        } = fold_support_circuit::<CMain, CSup>(
            &pp.support_ck,
            &pp.sangria_prover_params(),
            &support_acc,
            primary_acc
                .u
                .W_commitments
                .iter()
                .copied()
                .zip_eq(primary_trace.u.W_commitments.iter().copied()),
            l0,
            l1,
        )?;

        let primary_z_next = sc.process_step(&primary_z_current, pp.primary_k_table_size)?;

        let primary_sfc = StepFoldingCircuit::<'_, ARITY, CMain, CSup, SC> {
            sc,
            input: sfc::InputBuilder {
                step: step.get(),
                pp_digest: pp.pp_digest_coordinates(),
                z_i: primary_z_current,
                z_0: primary_z_0,
                self_incoming: &primary_trace.u,
                self_proof: primary_proof,
                support_acc: &support_acc.U,
                support_incoming: support_incoming.as_slice(),
                self_acc: &primary_acc.into(),
            }
            .build(),
            _p: PhantomData,
        };

        let primary_instances = primary_sfc.instances(
            &primary_next_acc.clone().into(),
            &support_next_acc.U,
            &primary_z_next,
        );

        #[cfg(test)]
        {
            let _mock = info_span!("mock_debug").entered();
            crate::halo2_proofs::dev::MockProver::run(
                pp.primary_k_table_size,
                &primary_sfc,
                primary_instances.clone(),
            )
            .unwrap()
            .verify()
            .unwrap();
        }

        let primary_witness = CircuitRunner::new(
            pp.primary_k_table_size,
            primary_sfc,
            primary_instances.clone(),
        )
        .try_collect_witness()
        .map_err(|err| Error::WhileCollectPrimaryWitness {
            step: step.get(),
            err,
        })?;

        let primary_next_trace = ProtoGalaxy::<CMain, 1>::generate_plonk_trace(
            &pp.primary_ck,
            &primary_instances,
            &primary_witness,
            &pp.protogalaxy_prover_params(),
            &mut ro(),
        )?;

        Ok(Self {
            step: step.saturating_add(1),
            primary_acc: primary_next_acc,
            primary_trace: primary_next_trace,
            primary_z_current: primary_z_next,
            primary_z_0,
            support_acc: support_next_acc,
            _p,
        })
    }

    pub fn verify(self, pp: &PublicParams<ARITY, CMain, CSup, SC>) -> Result<Self, Error<CMain>> {
        let _span = info_span!("ivc_verify").entered();
        let Self {
            step,
            primary_acc,
            primary_trace,
            primary_z_current,
            primary_z_0,
            support_acc,
            _p,
        } = &self;

        let mut errors: Vec<VerifyError<CMain>> = vec![];

        if let Err(err) = VerifyError::is_mismatch_proto_galaxy_consistency_marker(
            ro().absorb(
                &sfc::InputBuilder {
                    step: step.get(),
                    pp_digest: pp.pp_digest_coordinates(),
                    self_acc: &primary_acc.clone().into(),
                    support_acc: &support_acc.U,
                    z_i: *primary_z_current,
                    z_0: *primary_z_0,

                    // next fields not used in absorb
                    self_incoming: &primary_trace.u,
                    self_proof: nifs::protogalaxy::Proof::default(),
                    support_incoming: &[],
                }
                .build(),
            )
            .inspect(|buf| trace!("buf before marker: {buf:?}"))
            .output(
                NonZeroUsize::new(<CMain::ScalarExt as PrimeField>::NUM_BITS as usize).unwrap(),
            ),
            primary_trace.u.instances[0][0],
        ) {
            errors.push(err);
        }

        if let Err(err) =
            ProtoGalaxy::<CMain, 1>::is_sat(&pp.primary_ck, &pp.primary_S, primary_acc)
        {
            errors.push(VerifyError::WhileProtoGalaxyIsSat(err))
        }

        if let Err(err) = SangriaFS::<CSup>::is_sat(&pp.support_ck, &pp.support_S, support_acc, &[])
        {
            errors.push(VerifyError::WhileSangriaIsSat(err))
        }

        if errors.is_empty() {
            Ok(self)
        } else {
            Err(Error::Verify(errors.into_boxed_slice()))
        }
    }
}

struct SupportCircuitFoldResult<C: CurveAffine> {
    new_accumulator: SangriaRelaxedPlonkTrace<C>,
    incoming: Vec<(
        SangriaFoldablePlonkInstance<C>,
        nifs::sangria::CrossTermCommits<C>,
    )>,
}

fn fold_support_circuit<CMain, CSup>(
    support_ck: &CommitmentKey<CSup>,
    prover_params: &nifs::sangria::ProverParam<CSup>,
    accumulator: &SangriaRelaxedPlonkTrace<CSup>,
    W_commitments_pairs: impl Iterator<Item = (CMain, CMain)>,
    l0: CMain::Base,
    l1: CMain::Base,
) -> Result<SupportCircuitFoldResult<CSup>, nifs::sangria::Error>
where
    CMain: CurveAffine<Base = <CSup as PrimeCurveAffine>::Scalar>,
    CSup: CurveAffine<Base = <CMain as PrimeCurveAffine>::Scalar>,
    CMain::Base: PrimeFieldBits + FromUniformBytes<64>,
    CSup::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    let _support = info_span!("support").entered();

    let traces = W_commitments_pairs
        .map(|(p0, p1)| support_circuit::InstanceInput::<CMain> { p0, p1, l0, l1 }.into_instance())
        .map(|instances| {
            #[cfg(test)]
            {
                let _mock = info_span!("mock_debug").entered();
                crate::halo2_proofs::dev::MockProver::run(
                    SupportCircuit::<CMain>::MIN_K_TABLE_SIZE,
                    &SupportCircuit::<CMain>::default(),
                    instances.clone(),
                )
                .unwrap()
                .verify()
                .unwrap();
            }

            let witness = CircuitRunner::<CMain::Base, _>::new(
                SupportCircuit::<CMain>::MIN_K_TABLE_SIZE,
                SupportCircuit::<CMain>::default(),
                instances.clone(),
            )
            .try_collect_witness()?;

            SangriaFS::<CSup>::generate_plonk_trace(
                support_ck,
                &instances,
                &witness,
                prover_params,
                &mut ro(),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    let mut new_accumulator = accumulator.clone();
    let mut paired_incoming = vec![];
    for trace in traces {
        let (next_acc, proof) = SangriaFS::<CSup>::prove(
            support_ck,
            prover_params,
            &mut ro(),
            new_accumulator,
            &[trace.clone()],
        )?;

        paired_incoming.push((trace.u, proof));

        new_accumulator = next_acc;
    }

    Ok(SupportCircuitFoldResult {
        new_accumulator,
        incoming: paired_incoming,
    })
}

#[derive(thiserror::Error, Debug)]
pub enum Error<CMain: CurveAffine> {
    #[error("Error while verify: {0:?}")]
    Verify(Box<[VerifyError<CMain>]>),

    #[error("Sangria NIFS error: {0:?}")]
    Sangria(#[from] nifs::sangria::Error),

    #[error("ProtoGalaxy NIFS error: {0:?}")]
    ProtoGalaxy(#[from] nifs::protogalaxy::Error),

    #[error("While creating a new protogalaxy acc: {0:?}")]
    WhileProtoGalaxyAccCreation(eval::Error),

    #[error("While collecting witness on the primary circuit at step {step}: {err:?}")]
    WhileCollectPrimaryWitness { step: usize, err: Halo2PlonkError },

    #[error("While collecting plonk structure on the primary circuit: {err:?}")]
    WhileCollectPrimaryS { err: Halo2PlonkError },

    #[error("While step circuit synthesis: {0:?}")]
    WhileStepCircuitSynthesis(#[from] step_circuit::SynthesisError),
}

#[derive(thiserror::Error, Debug)]
pub enum VerifyError<CMain: CurveAffine> {
    #[error("Mismatch proto galaxy consistency marker: {expected:?} != {actual:?}")]
    MismatchProtoGalaxyConsistencyMarker {
        expected: CMain::ScalarExt,
        actual: CMain::ScalarExt,
    },
    #[error("While is sat protogalaxy acc: {0:?}")]
    WhileProtoGalaxyIsSat(Vec<nifs::protogalaxy::VerifyError<CMain::ScalarExt>>),

    #[error("While is sat protogalaxy acc: {0:?}")]
    WhileSangriaIsSat(Vec<nifs::sangria::VerifyError>),
}

impl<CMain: CurveAffine> VerifyError<CMain> {
    fn is_mismatch_proto_galaxy_consistency_marker(
        expected: CMain::ScalarExt,
        actual: CMain::ScalarExt,
    ) -> Result<(), Self> {
        if expected != actual {
            Err(Self::MismatchProtoGalaxyConsistencyMarker { expected, actual })
        } else {
            Ok(())
        }
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
    const PRIMARY_COMMITMENT_KEY_SIZE: usize = 23;
    const SECONDARY_COMMITMENT_KEY_SIZE: usize = 23;

    const PRIMARY_CIRCUIT_TABLE_SIZE: u32 = 20;

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

        let mut pp = super::PublicParams::new(
            &sc,
            primary_commitment_key,
            secondary_commitment_key,
            PRIMARY_CIRCUIT_TABLE_SIZE,
        )
        .unwrap();
        info!("pp created");

        super::IVC::new(&mut pp, &sc, array::from_fn(|_| C1Scalar::ZERO))
            .expect("while step=0")
            .next(&pp, &sc)
            .expect("while step=1")
            .next(&pp, &sc)
            .expect("while step=2")
            .verify(&pp)
            .expect("while verify");
    }
}
