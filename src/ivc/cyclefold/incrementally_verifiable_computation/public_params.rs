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
        _primary_sc: &SC,
        _ck1: CommitmentKey<CMain>,
        _ck2: CommitmentKey<CSup>,
        _k_table_size: u32,
    ) -> Self
    where
        CMain::ScalarExt: Serialize,
        CSup::ScalarExt: Serialize,
    {
        todo!("temporarily removed for the purposes of a simple merge into main")
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
            pp_digest: self.cmain_pp_digest_coordinates(),
        }
    }

    pub fn sangria_prover_params(&self) -> nifs::sangria::ProverParam<CSup> {
        nifs::sangria::ProverParam {
            S: self.support_S.clone(),
            pp_digest: self.csup_pp_digest_coordinates(),
        }
    }
}
