use std::marker::PhantomData;

use crate::{
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

pub struct PublicParams<const A1: usize, const A2: usize, C1, C2, SC>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<A1, C1::Scalar>,
    C1::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    C2::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    ck1: CommitmentKey<C1>,
    primary_S: PlonkStructure<C1::ScalarExt>,
    primary_k_table_size: u32,
    initial_primary_trace: PlonkTrace<C1>,

    ck2: CommitmentKey<C2>,
    secondary_S: PlonkStructure<C2::ScalarExt>,
    initial_secondary_trace: FoldablePlonkTrace<C2>,

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
    /// StepFoldingCircuit {
    ///     step == 0 => init(acc, incoming) => output_trace,
    ///     step != 0 => fold(acc, incoming) => output_trace,
    /// }
    pub fn new(
        primary_sfc: &SC,
        ck1: CommitmentKey<CMain>,
        ck2: CommitmentKey<CSup>,
        k_table_size: u32,
    ) -> Self {
        // Trace in C1::Base or C2::Scalar
        let (support_plonk_structure, initial_support_trace): (
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
                        pp_digest: CSup::identity(),
                    },
                    &mut ro(),
                )
                .unwrap(),
            )
        };

        let (primary_plonk_structure, initial_primary_trace) = {
            let mut mock_sfc = StepFoldingCircuit::<A1, CMain, CSup, SC> {
                sc: primary_sfc,
                input: sfc::Input::<A1, CMain::ScalarExt>::new_initial::<CMain, CSup>(
                    &PlonkStructure {
                        k: k_table_size as usize,
                        ..Default::default()
                    },
                    &support_plonk_structure,
                    &initial_support_trace.u,
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
                &support_plonk_structure,
                &initial_support_trace.u,
            );

            let mock_S = CircuitRunner::new(k_table_size, mock_sfc, mock_instances)
                .try_collect_plonk_structure()
                .unwrap();

            let sfc = StepFoldingCircuit::<A1, CMain, CSup, SC> {
                sc: primary_sfc,
                input: sfc::Input::<A1, CMain::ScalarExt>::new_initial::<CMain, CSup>(
                    &mock_S,
                    &support_plonk_structure,
                    &initial_support_trace.u,
                ),
                _p: PhantomData,
            };

            // TODO #369 Use expected out marker, instead of zero
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

        Self {
            ck1,
            ck2,
            primary_k_table_size: k_table_size,

            initial_primary_trace,
            initial_secondary_trace: initial_support_trace,

            primary_S: primary_plonk_structure,
            secondary_S: support_plonk_structure,

            _p: PhantomData,
        }
    }
}
