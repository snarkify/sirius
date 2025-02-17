use std::marker::PhantomData;

use halo2_proofs::halo2curves::ff::PrimeField;
use serde::Serialize;

use crate::{
    constants::NUM_HASH_BITS,
    digest::{self, DigestToBits},
    halo2_proofs::halo2curves::{
        ff::{Field, FromUniformBytes, PrimeFieldBits},
        group::prime::PrimeCurveAffine,
        CurveAffine,
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
    poseidon::{PoseidonHash, ROTrait, Spec},
    prelude::CommitmentKey,
    table::CircuitRunner,
};

pub struct PublicParams<const A1: usize, const A2: usize, CMain, CSup, SC>
where
    CMain: CurveAffine<Base = <CSup as PrimeCurveAffine>::Scalar>,
    CSup: CurveAffine<Base = <CMain as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<A1, CMain::Scalar>,
    CMain::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    CSup::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    pub primary_ck: CommitmentKey<CMain>,
    pub primary_S: PlonkStructure<CMain::ScalarExt>,
    pub primary_k_table_size: u32,
    pub primary_initial_trace: PlonkTrace<CMain>,

    pub support_ck: CommitmentKey<CSup>,
    pub support_S: PlonkStructure<CSup::ScalarExt>,
    pub support_initial_trace: FoldablePlonkTrace<CSup>,

    digest_bytes: Box<[u8]>,

    _p: PhantomData<SC>,
}

const T: usize = 10;
const RATE: usize = T - 1;
const R_F: usize = 10;
const R_P: usize = 10;

fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
    PoseidonHash::<F, T, RATE>::new(Spec::<F, T, RATE>::new(R_F, R_P))
}

impl<const A1: usize, const A2: usize, CMain, CSup, SC> PublicParams<A1, A2, CMain, CSup, SC>
where
    CMain: CurveAffine<Base = <CSup as PrimeCurveAffine>::Scalar>,
    CSup: CurveAffine<Base = <CMain as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<A1, CMain::Scalar>,
    CMain::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    CSup::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new(
        primary_sc: &SC,
        ck1: CommitmentKey<CMain>,
        ck2: CommitmentKey<CSup>,
        k_table_size: u32,
    ) -> Self
    where
        CMain::ScalarExt: Serialize,
        CSup::ScalarExt: Serialize,
    {
        // Trace in C1::Base or C2::Scalar
        let (support_S, support_initial_trace): (
            PlonkStructure<CMain::Base>,
            FoldablePlonkTrace<CSup>,
        ) = {
            // Since I want to scalar_multiply points for main::sfc, I take `CMain` as the main curve here
            // CMain::Base or CSupport::Scalar (native for suppport_circuit)
            let support_circuit_instances: Vec<Vec<CMain::Base>> = support_circuit::InstanceInput {
                p0: CMain::identity(),
                l0: CMain::Base::ZERO,
                p1: CMain::identity(),
                l1: CMain::Base::ZERO,
            }
            .into_instance();

            let support_cr = CircuitRunner::<CMain::Base, _>::new(
                SupportCircuit::<CMain>::MIN_K_TABLE_SIZE,
                SupportCircuit::<CMain>::default(),
                support_circuit_instances.clone(),
            );
            let S = support_cr.try_collect_plonk_structure().unwrap();

            // The trace is generated for `CSup`, since all result types use `C::ScalarExt` in our
            // case it will be `CSup::ScalarExt` or `CMain::Base`
            (
                S,
                VanillaFS::<CSup>::generate_plonk_trace(
                    &ck2,
                    &support_circuit_instances,
                    &support_cr.try_collect_witness().unwrap(),
                    &nifs::sangria::ProverParam {
                        S: support_cr.try_collect_plonk_structure().unwrap(),
                        pp_digest: (CSup::Base::ZERO, CSup::Base::ZERO),
                    },
                    &mut ro(),
                )
                .unwrap(),
            )
        };

        let (primary_S, primary_initial_trace) = {
            let mut mock_sfc = StepFoldingCircuit::<A1, CMain, CSup, SC> {
                sc: primary_sc,
                input: sfc::Input::<A1, CMain::ScalarExt>::new_initial::<CMain, CSup>(
                    &PlonkStructure {
                        k: k_table_size as usize,
                        ..Default::default()
                    },
                    &support_S,
                    &support_initial_trace.u,
                ),
                _p: PhantomData,
            };

            let mock_instances = mock_sfc.initial_instances();

            // Correct `num_io`
            mock_sfc.input = sfc::Input::<A1, CMain::ScalarExt>::new_initial::<CMain, CSup>(
                &PlonkStructure {
                    k: k_table_size as usize,
                    num_io: mock_instances.iter().map(|col| col.len()).collect(),
                    ..Default::default()
                },
                &support_S,
                &support_initial_trace.u,
            );

            let mock_S = CircuitRunner::new(k_table_size, mock_sfc, mock_instances)
                .try_collect_plonk_structure()
                .unwrap();

            let sfc = StepFoldingCircuit::<A1, CMain, CSup, SC> {
                sc: primary_sc,
                input: sfc::Input::<A1, CMain::ScalarExt>::new_initial::<CMain, CSup>(
                    &mock_S,
                    &support_S,
                    &support_initial_trace.u,
                ),
                _p: PhantomData,
            };

            let primary_instances = sfc.initial_instances();
            let primary_cr = CircuitRunner::new(k_table_size, sfc, primary_instances.clone());

            (
                primary_cr.try_collect_plonk_structure().unwrap(),
                ProtoGalaxy::<CMain, 1>::generate_plonk_trace(
                    &ck1,
                    &primary_instances,
                    &primary_cr.try_collect_witness().unwrap(),
                    &nifs::protogalaxy::ProverParam {
                        S: primary_cr.try_collect_plonk_structure().unwrap(),
                        pp_digest: CMain::identity(),
                    },
                    &mut ro(),
                )
                .unwrap(),
            )
        };

        let digest_bytes = {
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

            digest::DefaultHasher::digest_to_bits(&Meaningful {
                primary_S: &primary_S,
                primary_k_table_size: &k_table_size,
                support_S: &support_S,
            })
            .unwrap()
        };

        Self {
            primary_ck: ck1,
            support_ck: ck2,
            primary_k_table_size: k_table_size,

            primary_initial_trace,
            support_initial_trace,

            primary_S,
            support_S,

            digest_bytes,

            _p: PhantomData,
        }
    }

    pub fn cmain_pp_digest(&self) -> CMain {
        digest::into_curve_from_bits(&self.digest_bytes, NUM_HASH_BITS)
    }

    pub fn csup_pp_digest(&self) -> CSup {
        digest::into_curve_from_bits(&self.digest_bytes, NUM_HASH_BITS)
    }

    pub fn cmain_pp_digest_coordinates(&self) -> (CMain::Base, CMain::Base) {
        self.cmain_pp_digest()
            .coordinates()
            .map(|c| (*c.x(), *c.y()))
            .unwrap()
    }

    pub fn csup_pp_digest_coordinates(&self) -> (CSup::Base, CSup::Base) {
        self.csup_pp_digest()
            .coordinates()
            .map(|c| (*c.x(), *c.y()))
            .unwrap()
    }

    pub fn protogalaxy_prover_params(&self) -> nifs::protogalaxy::ProverParam<CMain> {
        nifs::protogalaxy::ProverParam {
            S: self.primary_S.clone(),
            pp_digest: self.cmain_pp_digest(),
        }
    }

    pub fn sangria_prover_params(&self) -> nifs::sangria::ProverParam<CSup> {
        nifs::sangria::ProverParam {
            S: self.support_S.clone(),
            pp_digest: self.csup_pp_digest_coordinates(),
        }
    }
}
