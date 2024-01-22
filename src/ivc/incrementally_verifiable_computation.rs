use std::{marker::PhantomData, num::NonZeroUsize};

use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2curves::CurveAffine;

use crate::{
    commitment::CommitmentKey,
    plonk::{PlonkTrace, RelaxedPlonkTrace},
    poseidon::{AbsorbInRO, ROCircuitTrait, ROTrait},
    table::TableData,
};

use super::step_circuit::SynthesizeStepParams;
pub use super::{
    floor_planner::{FloorPlanner, SimpleFloorPlanner},
    step_circuit::{StepCircuit, SynthesisError},
};

// TODO #31 docs
pub struct CircuitPublicParams<C, ROC>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    ROC: ROCircuitTrait<C::Base>,
{
    ck: CommitmentKey<C>,
    td: TableData<C::Scalar>,
    ro_consts: ROC::Args,
    // ro_consts_circuit: ROTrait::Constants, // NOTE: our `ROTraitCircuit` don't have main initializer
    params: SynthesizeStepParams<C, ROC>,
}

impl<AnyCurve, CC, RO, ROC> AbsorbInRO<AnyCurve, RO> for CircuitPublicParams<CC, ROC>
where
    AnyCurve: CurveAffine,
    CC: CurveAffine,
    CC::Base: PrimeFieldBits + FromUniformBytes<64>,
    RO: ROTrait<AnyCurve>,
    ROC: ROCircuitTrait<CC::Base>,
{
    fn absorb_into(&self, _ro: &mut RO) {
        todo!("#32")
    }
}

// TODO #31 docs
pub struct PublicParams<const A1: usize, const A2: usize, C1, C2, R1, R2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    C1::Base: PrimeFieldBits + FromUniformBytes<64>,
    C2::Base: PrimeFieldBits + FromUniformBytes<64>,
    R1: ROCircuitTrait<C1::Base>,
    R2: ROCircuitTrait<C2::Base>,
{
    primary: CircuitPublicParams<C1, R1>,
    secondary: CircuitPublicParams<C2, R2>,

    _p: PhantomData<(C1, C2)>,
}

impl<const A1: usize, const A2: usize, C1, C2, R1, R2> PublicParams<A1, A2, C1, C2, R1, R2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    R1: ROCircuitTrait<C1::Base>,
    R2: ROCircuitTrait<C2::Base>,
    C1::Base: PrimeFieldBits + FromUniformBytes<64>,
    C2::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new<SC1, SC2>(
        _limb_width: NonZeroUsize,
        _limbs_count_limit: NonZeroUsize,
        _primary: &SC1,
        _primary_ro_constant: R1::Args,
        _secondary: &SC2,
        _secondary_ro_constant: R2::Args,
    ) -> Self
    where
        SC1: StepCircuit<A1, C1::Scalar>,
        SC2: StepCircuit<A2, C2::Scalar>,
    {
        // TODO #31 docs
        // https://github.com/microsoft/Nova/blob/fb83e30e16e56b3b21c519b15b83c4ce1f077a13/src/lib.rs#L98
        todo!("Impl creation of pub params")
    }

    pub fn digest<ROT: ROTrait<C1>>(&self, constant: ROT::Constants) -> C1::ScalarExt {
        let mut ro = ROT::new(constant);

        let Self {
            primary,
            secondary,
            _p,
        } = &self;
        primary.absorb_into(&mut ro);
        secondary.absorb_into(&mut ro);

        let bytes_count = C1::Base::ZERO.to_repr().as_ref().len();
        ro.squeeze(NonZeroUsize::new(bytes_count * 8).unwrap())
    }
}

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::Scalar>,
{
    step_circuit: SC,
    relaxed_trace: RelaxedPlonkTrace<C>,
    z_input: [C::Scalar; ARITY],
}

// TODO #31 docs
#[derive(Debug, thiserror::Error)]
pub enum Error {}

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

    trace: PlonkTrace<C2>,

    step: usize,
}

impl<const A1: usize, const A2: usize, C1, C2, SC1, SC2> IVC<A1, A2, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
    C1::Base: PrimeFieldBits + FromUniformBytes<64>,
    C2::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new<RO1, RO2>(
        _pp: &PublicParams<A1, A2, C1, C2, RO1, RO2>,
        _primary: SC1,
        _z0_primary: [C1::Scalar; A1],
        _secondary: SC2,
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<Self, Error>
    where
        RO1: ROCircuitTrait<C1::Base>,
        RO2: ROCircuitTrait<C2::Base>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::new`")
    }

    pub fn prove_step<RO1, RO2>(
        &mut self,
        _pp: &PublicParams<A1, A2, C1, C2, RO1, RO2>,
        _z0_primary: [C1::Scalar; A1],
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<(), Error>
    where
        RO1: ROCircuitTrait<C1::Base>,
        RO2: ROCircuitTrait<C2::Base>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::prove_step`")
    }

    pub fn verify<RO1, RO2>(
        &mut self,
        _pp: &PublicParams<A1, A2, C1, C2, RO1, RO2>,
        _steps_count: usize,
        _z0_primary: [C1::Scalar; A1],
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<(), Error>
    where
        RO1: ROCircuitTrait<C1::Base>,
        RO2: ROCircuitTrait<C2::Base>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::verify`")
    }
}
