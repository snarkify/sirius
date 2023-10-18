pub mod step_circuit;

use group::prime::PrimeCurveAffine;
use halo2curves::CurveAffine;

use crate::{
    commitment::CommitmentKey,
    plonk::{PlonkInstance, PlonkWitness, RelaxedPlonkInstance, RelaxedPlonkWitness, TableData},
    poseidon::ROTrait,
};

use step_circuit::StepCircuit;

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
    // augmented_circuit_params: NovaAugmentedCircuitParams,
}

// TODO docs
pub struct PublicParams<const A1: usize, const A2: usize, C1, C2, R1, R2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    R1: ROTrait<C1>,
    R2: ROTrait<C2>,
{
    primary: CircuitPublicParams<C1, R1>,
    secondary: CircuitPublicParams<C2, R2>,
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
struct IVCGadget<const A1: usize, const A2: usize, C1, C2, SC1, SC2>
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

impl<const A1: usize, const A2: usize, C1, C2, SC1, SC2> IVCGadget<A1, A2, C1, C2, SC1, SC2>
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
