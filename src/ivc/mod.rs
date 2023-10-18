pub mod step_circuit;

use std::num::NonZeroUsize;

use group::prime::PrimeCurveAffine;
use halo2curves::CurveAffine;

use crate::{
    commitment::CommitmentKey,
    plonk::{PlonkInstance, PlonkWitness, RelaxedPlonkInstance, RelaxedPlonkWitness, TableData},
    poseidon::ROTrait,
};

use step_circuit::{StepCircuit, SynthesizeStepParams};

// TODO docs
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

// TODO docs
pub struct PublicParams<const A1: usize, const A2: usize, SC1, SC2, R1, R2>
where
    SC1: CurveAffine<Base = <SC2 as PrimeCurveAffine>::Scalar>,
    SC2: CurveAffine<Base = <SC1 as PrimeCurveAffine>::Scalar>,
    R1: ROTrait<SC1>,
    R2: ROTrait<SC2>,
{
    primary: CircuitPublicParams<SC1, R1>,
    secondary: CircuitPublicParams<SC2, R2>,
}

impl<const A1: usize, const A2: usize, SC1, SC2, R1, R2> PublicParams<A1, A2, SC1, SC2, R1, R2>
where
    SC1: CurveAffine<Base = <SC2 as PrimeCurveAffine>::Scalar>,
    SC2: CurveAffine<Base = <SC1 as PrimeCurveAffine>::Scalar>,
    R1: ROTrait<SC1>,
    R2: ROTrait<SC2>,
{
    fn new(
        _limb_width: NonZeroUsize,
        _limbs_count_limit: NonZeroUsize,
        _primary: &SC1,
        _primary_ro_constant: R1::Constants,
        _secondary: &SC2,
        _secondary_ro_constant: R2::Constants,
    ) -> Self {
        todo!()
    }
}

// TODO docs
pub struct RelaxedTrace<C: CurveAffine> {
    U: RelaxedPlonkInstance<C>,
    W: RelaxedPlonkWitness<C::Scalar>,
}

// TODO docs
pub struct Trace<C: CurveAffine> {
    u: PlonkInstance<C>,
    w: PlonkWitness<C::Scalar>,
}

// TODO docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::Scalar>,
{
    step_circuit: SC,
    relaxed_trace: RelaxedTrace<C>,
    z_input: [C::Scalar; ARITY],
}

// TODO docs
#[allow(clippy::upper_case_acronyms)]
struct IVC<const A1: usize, const A2: usize, C1, C2, SC1, SC2>
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
    fn new<RO1, RO2>(
        _pp: &PublicParams<A1, A2, C1, C2, RO1, RO2>,
        _primary: C1,
        _z0_primary: [C1::Scalar; A1],
        _secondary: C2,
        _z0_secondary: [C2::Scalar; A2],
    ) -> Self
    where
        RO1: ROTrait<C1>,
        RO2: ROTrait<C2>,
    {
        todo!()
    }
}
