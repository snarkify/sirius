use std::marker::PhantomData;

use public_params::PublicParams;
use tracing::info_span;

use super::{
    ro,
    support_circuit::{self, SupportCircuit},
};
use crate::{
    constants::MAX_BITS,
    halo2_proofs::halo2curves::{
        ff::{Field, FromUniformBytes, PrimeFieldBits},
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
        sangria::{FoldablePlonkTrace, VanillaFS},
    },
    poseidon::ROTrait,
    table::CircuitRunner,
};

mod public_params;

pub struct IVC<const ARITY: usize, C1, C2, SC>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<ARITY, C1::Scalar>,
    C1::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    C2::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    _p: PhantomData<(C1, C2, SC)>,
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
        let _primary_span = info_span!("primary").entered();

        let initial_self_acc = ProtoGalaxy::<CMain, 1>::new_accumulator(
            AccumulatorArgs::from(&pp.primary_S),
            &nifs::protogalaxy::ProverParam {
                S: pp.primary_S.clone(),
                pp_digest: pp.cmain_pp_digest(),
            },
            &mut ro(),
        );

        let mut primary_ro = ro();
        let (_new_acc, self_proof) = ProtoGalaxy::prove(
            &pp.primary_ck,
            &nifs::protogalaxy::ProverParam {
                S: pp.primary_S.clone(),
                pp_digest: pp.cmain_pp_digest(),
            },
            &mut primary_ro,
            initial_self_acc.clone(),
            &[pp.primary_initial_trace.clone()],
        )
        .unwrap();
        let _gamma: CMain::ScalarExt = primary_ro.squeeze(MAX_BITS);

        let (_new_acc, paired_proof) = VanillaFS::prove(
            &pp.support_ck,
            &nifs::sangria::ProverParam {
                S: pp.support_S.clone(),
                pp_digest: pp.csup_pp_digest(),
            },
            &mut ro(),
            nifs::sangria::accumulator::RelaxedPlonkTrace::from_regular(
                pp.support_initial_trace.clone(),
                SupportCircuit::<CMain>::MIN_K_TABLE_SIZE as usize,
            ),
            &[pp.support_initial_trace.clone()],
        )
        .unwrap();

        let _primary_sfc = StepFoldingCircuit::<'_, ARITY, CMain, CSup, SC> {
            sc,
            input: sfc::InputBuilder {
                pp_digest: pp.csup_pp_digest(),
                step: 0,
                self_incoming: &pp.primary_initial_trace.u,
                self_proof,
                paired_acc: &pp.support_initial_trace.u.clone().into(),
                paired_incoming: {
                    &vec![
                        (pp.support_initial_trace.u.clone(), paired_proof.clone());
                        initial_self_acc.W_commitment_len()
                    ]
                },
                self_acc: &initial_self_acc.into(),
                z_i: z_0,
                z_0,
            }
            .build(),
            _p: PhantomData,
        };

        let _initial_support_trace: FoldablePlonkTrace<CSup> = {
            let _support_span = info_span!("support").entered();

            let support_circuit_instances: Vec<Vec<CMain::Base>> = support_circuit::InstanceInput {
                p0: CMain::identity(),
                l0: CMain::Base::ZERO,
                p1: CMain::identity(),
                l1: CMain::Base::ZERO,
                p_out: CMain::identity(),
            }
            .into_instance();

            let support_cr = CircuitRunner::<CMain::Base, _>::new(
                SupportCircuit::<CMain>::MIN_K_TABLE_SIZE,
                SupportCircuit::<CMain>::default(),
                support_circuit_instances.clone(),
            );

            VanillaFS::<CSup>::generate_plonk_trace(
                &pp.support_ck,
                &support_circuit_instances,
                &support_cr.try_collect_witness().unwrap(),
                &nifs::sangria::ProverParam {
                    S: support_cr.try_collect_plonk_structure().unwrap(),
                    pp_digest: CSup::identity(),
                },
                &mut ro(),
            )
            .unwrap()
        };

        todo!()
    }
}
