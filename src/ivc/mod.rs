pub mod step_circuit;

mod floor_planner;

use std::{marker::PhantomData, num::NonZeroUsize};

use group::prime::PrimeCurveAffine;
use halo2curves::CurveAffine;

use crate::{
    commitment::CommitmentKey,
    plonk::{PlonkInstance, PlonkWitness, RelaxedPlonkInstance, RelaxedPlonkWitness, TableData},
    poseidon::ROTrait,
};

pub use floor_planner::{FloorPlanner, SimpleFloorPlanner};
use step_circuit::SynthesizeStepParams;
pub use step_circuit::{StepCircuit, SynthesisError};

// TODO #31 docs
pub struct CircuitPublicParams<C, RO>
where
    C: CurveAffine,
    RO: ROTrait<C>,
{
    ck: CommitmentKey<C>,
    td: TableData<C::Scalar>,
    ro_consts: RO::Constants,
    // ro_consts_circuit: ROTrait::Constants, // NOTE: our `ROTraitCircuit` don't have main initializer
    params: SynthesizeStepParams<C, RO>,
}

// TODO #31 docs
pub struct PublicParams<const A1: usize, const A2: usize, C1, C2, R1, R2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    R1: ROTrait<C1>,
    R2: ROTrait<C2>,
{
    primary: CircuitPublicParams<C1, R1>,
    secondary: CircuitPublicParams<C2, R2>,

    _p: PhantomData<(C1, C2)>,
}

impl<const A1: usize, const A2: usize, C1, C2, R1, R2> PublicParams<A1, A2, C1, C2, R1, R2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    R1: ROTrait<C1>,
    R2: ROTrait<C2>,
{
    pub fn new<SC1, SC2>(
        _limb_width: NonZeroUsize,
        _limbs_count_limit: NonZeroUsize,
        _primary: &SC1,
        _primary_ro_constant: R1::Constants,
        _secondary: &SC2,
        _secondary_ro_constant: R2::Constants,
    ) -> Self
    where
        SC1: StepCircuit<A1, C1::Scalar>,
        SC2: StepCircuit<A2, C2::Scalar>,
    {
        // TODO #31 docs
        // https://github.com/microsoft/Nova/blob/fb83e30e16e56b3b21c519b15b83c4ce1f077a13/src/lib.rs#L98
        todo!("Impl creation of pub params")
    }
}

// TODO #31 docs
pub struct RelaxedTrace<C: CurveAffine> {
    U: RelaxedPlonkInstance<C>,
    W: RelaxedPlonkWitness<C::Scalar>,
}

// TODO #31 docs
pub struct Trace<C: CurveAffine> {
    u: PlonkInstance<C>,
    w: PlonkWitness<C::Scalar>,
}

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::Scalar>,
{
    step_circuit: SC,
    relaxed_trace: RelaxedTrace<C>,
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

    trace: Trace<C2>,

    step: usize,
}

impl<const A1: usize, const A2: usize, C1, C2, SC1, SC2> IVC<A1, A2, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
{
    pub fn new<RO1, RO2>(
        _pp: &PublicParams<A1, A2, C1, C2, RO1, RO2>,
        _primary: SC1,
        _z0_primary: [C1::Scalar; A1],
        _secondary: SC2,
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<Self, Error>
    where
        RO1: ROTrait<C1>,
        RO2: ROTrait<C2>,
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
        RO1: ROTrait<C1>,
        RO2: ROTrait<C2>,
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
        RO1: ROTrait<C1>,
        RO2: ROTrait<C2>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::verify`")
    }
}
