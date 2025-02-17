use std::{io, iter, marker::PhantomData};

use serde::Serialize;
use tracing::info_span;

use crate::{
    constants::NUM_HASH_BITS,
    digest::{self, DigestToBits},
    halo2_proofs::{
        halo2curves::{
            ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits},
            group::prime::PrimeCurveAffine,
            CurveAffine,
        },
        plonk::Error as Halo2PlonkError,
    },
    ivc::{
        cyclefold::{
            sfc::{self, StepFoldingCircuit},
            support_circuit::{self, SupportCircuit},
        },
        StepCircuit,
    },
    nifs::{
        self,
        protogalaxy::ProtoGalaxy,
        sangria::{FoldablePlonkTrace, VanillaFS},
    },
    plonk::{PlonkStructure, PlonkTrace},
    polynomial::Expression,
    poseidon::{PoseidonHash, ROTrait, Spec},
    sangria_prelude::CommitmentKey,
    table::CircuitRunner,
    util,
};

pub struct PublicParams<const ARITY: usize, CMain, CSup, SC>
where
    CMain: CurveAffine<Base = <CSup as PrimeCurveAffine>::Scalar>,
    CSup: CurveAffine<Base = <CMain as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<ARITY, CMain::Scalar>,
    CMain::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    CSup::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    pub primary_ck: CommitmentKey<CMain>,
    pub primary_S: PlonkStructure<CMain::ScalarExt>,
    pub primary_k_table_size: u32,
    pub primary_initial_trace: PlonkTrace<CMain>,

    pub support_ck: CommitmentKey<CSup>,
    pub support_S: PlonkStructure<CSup::ScalarExt>,
    pub support_initial_trace: FoldablePlonkTrace<CSup, { support_circuit::INSTANCES_LEN }>,

    hash_bytes: CMain,

    _p: PhantomData<SC>,
}

const T: usize = 10;
const RATE: usize = T - 1;
const R_F: usize = 10;
const R_P: usize = 10;

fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
    PoseidonHash::<F, T, RATE>::new(Spec::<F, T, RATE>::new(R_F, R_P))
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("While collect plonk structure: {0:?}")]
    WhileCollectS(Halo2PlonkError),

    #[error("While collect witness: {0:?}")]
    WhileCollectWitness(Halo2PlonkError),

    #[error("While nifs::protogalaxy: {0:?}")]
    ProtoGalaxy(#[from] nifs::protogalaxy::Error),

    #[error("While nifs::sangria: {0:?}")]
    Sangria(#[from] nifs::sangria::Error),

    #[error("While calculate digest: {0:?}")]
    Digest(io::Error),
}

impl<const ARITY: usize, CMain, CSup, SC> PublicParams<ARITY, CMain, CSup, SC>
where
    CMain: CurveAffine<Base = <CSup as PrimeCurveAffine>::Scalar>,
    CSup: CurveAffine<Base = <CMain as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<ARITY, CMain::Scalar>,
    CMain::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    CSup::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new(
        primary_sc: &SC,
        ck1: CommitmentKey<CMain>,
        ck2: CommitmentKey<CSup>,
        k_table_size: u32,
    ) -> Result<Self, Error>
    where
        CMain::ScalarExt: Serialize,
        CSup::ScalarExt: Serialize,
    {
        // Trace in C1::Base or C2::Scalar
        let (support_S, support_initial_trace): (
            PlonkStructure<CMain::Base>,
            FoldablePlonkTrace<CSup, { support_circuit::INSTANCES_LEN }>,
        ) = {
            let _support = info_span!("support").entered();
            // Since I want to scalar_multiply points for main::sfc, I take `CMain` as the main curve here
            // CMain::Base or CSupport::Scalar (native for support_circuit)
            //
            // For step zero, cyclefold::sfc expects `C::identity` to be multiplied by zero
            let support_circuit_instances: Vec<Vec<CMain::Base>> = support_circuit::InstanceInput {
                p0: CMain::identity(),
                l0: CMain::Base::ZERO,
                p1: CMain::identity(),
                l1: CMain::Base::ZERO,
            }
            .into_instance();

            #[cfg(test)]
            {
                let _mock = info_span!("mock-debug").entered();
                crate::halo2_proofs::dev::MockProver::run(
                    SupportCircuit::<CMain>::MIN_K_TABLE_SIZE,
                    &SupportCircuit::<CMain>::default(),
                    support_circuit_instances.clone(),
                )
                .unwrap()
                .verify()
                .unwrap();
            }

            let support_cr = CircuitRunner::<CMain::Base, _>::new(
                SupportCircuit::<CMain>::MIN_K_TABLE_SIZE,
                SupportCircuit::<CMain>::default(),
                support_circuit_instances.clone(),
            );
            let S = support_cr
                .try_collect_plonk_structure()
                .map_err(Error::WhileCollectS)?;

            // The trace is generated for `CSup`, since all result types use `C::ScalarExt` in our
            // case it will be `CSup::ScalarExt` or `CMain::Base`
            (
                S,
                VanillaFS::<CSup, { support_circuit::INSTANCES_LEN }>::generate_plonk_trace(
                    &ck2,
                    &support_circuit_instances,
                    &support_cr
                        .try_collect_witness()
                        .map_err(Error::WhileCollectWitness)?,
                    &nifs::sangria::ProverParam {
                        S: support_cr
                            .try_collect_plonk_structure()
                            .map_err(Error::WhileCollectS)?,
                        pp_digest: (CSup::Base::ZERO, CSup::Base::ZERO),
                    },
                    &mut ro(),
                )?,
            )
        };

        let _primary = info_span!("primary").entered();

        let (primary_S, primary_initial_trace) = {
            let mock_S = {
                let _s = info_span!("pre_run_mock").entered();

                let num_io = iter::once(1)
                    .chain(primary_sc.instances().iter().map(|col| col.len()))
                    .collect::<Box<[_]>>();

                let mock_sfc = StepFoldingCircuit::<ARITY, CMain, CSup, SC> {
                    sc: primary_sc,
                    input: sfc::Input::<ARITY, CMain::ScalarExt>::new_initial::<CMain, CSup>(
                        &PlonkStructure {
                            k: k_table_size as usize,
                            num_io,
                            // because with zero gates - calc count is zero - sfc panic
                            gates: vec![Expression::Constant(CMain::ScalarExt::ZERO)],
                            num_challenges: 3,
                            ..Default::default()
                        },
                        &support_S,
                        &support_initial_trace.u,
                    ),
                    _p: PhantomData,
                };

                let mock_instances = mock_sfc.initial_instances();

                #[cfg(test)]
                {
                    let _mock = info_span!("mock-debug").entered();
                    crate::halo2_proofs::dev::MockProver::run(
                        k_table_size,
                        &mock_sfc,
                        mock_instances.clone(),
                    )
                    .unwrap()
                    .verify()
                    .unwrap();
                }

                CircuitRunner::new(k_table_size, mock_sfc, mock_instances)
                    .try_collect_plonk_structure()
                    .map_err(Error::WhileCollectS)?
            };

            let sfc = StepFoldingCircuit::<ARITY, CMain, CSup, SC> {
                sc: primary_sc,
                input: sfc::Input::<ARITY, CMain::ScalarExt>::new_initial::<CMain, CSup>(
                    &mock_S,
                    &support_S,
                    &support_initial_trace.u,
                ),
                _p: PhantomData,
            };

            let primary_instances = sfc.initial_instances();

            #[cfg(test)]
            {
                let _mock = info_span!("mock-debug").entered();
                crate::halo2_proofs::dev::MockProver::run(
                    k_table_size,
                    &sfc,
                    primary_instances.clone(),
                )
                .unwrap()
                .verify()
                .unwrap();
            }

            let primary_cr = CircuitRunner::new(k_table_size, sfc, primary_instances.clone());

            (
                primary_cr
                    .try_collect_plonk_structure()
                    .map_err(Error::WhileCollectS)?,
                ProtoGalaxy::<CMain, 1>::generate_plonk_trace(
                    &ck1,
                    &primary_instances,
                    &primary_cr
                        .try_collect_witness()
                        .map_err(Error::WhileCollectWitness)?,
                    &nifs::protogalaxy::ProverParam {
                        S: primary_cr
                            .try_collect_plonk_structure()
                            .map_err(Error::WhileCollectS)?,
                        pp_digest: (CMain::Base::ZERO, CMain::Base::ZERO),
                    },
                    &mut ro(),
                )?,
            )
        };

        let hash_bytes = {
            let _digest = info_span!("digest").entered();
            use serde::Serialize;

            #[derive(Serialize)]
            struct Meaningful<'link, CMainScalar: PrimeField, CSupScalar: PrimeField>
            where
                CMainScalar: Serialize,
                CSupScalar: Serialize,
            {
                primary_S: &'link PlonkStructure<CMainScalar>,
                primary_k_table_size: &'link u32,
                support_S: &'link PlonkStructure<CSupScalar>,
            }

            let bytes = digest::DefaultHasher::digest_to_bits(&Meaningful {
                primary_S: &primary_S,
                primary_k_table_size: &k_table_size,
                support_S: &support_S,
            })
            .map_err(Error::Digest)?;

            digest::into_curve_from_bits::<CMain>(&bytes, NUM_HASH_BITS)
        };

        Ok(Self {
            primary_ck: ck1,
            support_ck: ck2,
            primary_k_table_size: k_table_size,

            primary_initial_trace,
            support_initial_trace,

            primary_S,
            support_S,

            hash_bytes,

            _p: PhantomData,
        })
    }

    pub fn pp_digest_coordinates<F: PrimeField>(&self) -> (F, F) {
        self.hash_bytes
            .coordinates()
            .map(|c| {
                (
                    util::fe_to_fe(c.x()).unwrap(),
                    util::fe_to_fe(c.y()).unwrap(),
                )
            })
            .unwrap()
    }

    pub fn protogalaxy_prover_params(&self) -> nifs::protogalaxy::ProverParam<CMain> {
        nifs::protogalaxy::ProverParam {
            S: self.primary_S.clone(),
            pp_digest: self.pp_digest_coordinates(),
        }
    }

    pub fn protogalaxy_verifier_params(&self) -> nifs::protogalaxy::VerifierParam<CMain> {
        nifs::protogalaxy::VerifierParam {
            pp_digest: self.pp_digest_coordinates(),
        }
    }

    pub fn sangria_prover_params(&self) -> nifs::sangria::ProverParam<CSup> {
        nifs::sangria::ProverParam {
            S: self.support_S.clone(),
            pp_digest: self.pp_digest_coordinates(),
        }
    }
}
