#![allow(unused_imports)]

use std::{marker::PhantomData, num::NonZeroUsize};

use public_params::PublicParams;
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
        _pp: &PublicParams<ARITY, ARITY, CMain, CSup, SC>,
        _sc: &SC,
        _z_0: [CMain::ScalarExt; ARITY],
    ) -> Self {
        todo!("temporarily removed for the purposes of a simple merge into main")
    }
}
