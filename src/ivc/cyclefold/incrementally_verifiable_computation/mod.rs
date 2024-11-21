use std::marker::PhantomData;

use crate::{
    halo2_proofs::halo2curves::{
        ff::{FromUniformBytes, PrimeFieldBits},
        group::prime::PrimeCurveAffine,
        CurveAffine,
    },
    ivc::StepCircuit,
};

mod public_params;

pub struct IVC<const A1: usize, const A2: usize, C1, C2, SC>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC: StepCircuit<A1, C1::Scalar>,
    C1::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    C2::Scalar: PrimeFieldBits + FromUniformBytes<64>,
{
    _p: PhantomData<(C1, C2, SC)>,
}
