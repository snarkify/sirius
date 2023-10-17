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
pub struct CircuitPublicParams<G, RO>
where
    G: CurveAffine,
    RO: ROTrait<G>,
{
    ck: CommitmentKey<G>,
    td: TableData<G::Scalar>,
    ro_consts: RO::Constants,
    // ro_consts_circuit: ROTrait::Constants, // NOTE: our `ROTraitCircuit` don't have main initializer
    // augmented_circuit_params: NovaAugmentedCircuitParams,
}

// TODO docs
pub struct PublicParams<const A1: usize, const A2: usize, G1, G2, R1, R2>
where
    G1: CurveAffine<Base = <G2 as PrimeCurveAffine>::Scalar>,
    G2: CurveAffine<Base = <G1 as PrimeCurveAffine>::Scalar>,
    R1: ROTrait<G1>,
    R2: ROTrait<G2>,
{
    primary: CircuitPublicParams<G1, R1>,
    secondary: CircuitPublicParams<G2, R2>,
}

// TODO docs
pub struct RelaxedTrace<G: CurveAffine> {
    U: RelaxedPlonkInstance<G>,
    W: RelaxedPlonkWitness<G::Scalar>,
}

// TODO docs
pub struct Trace<G: CurveAffine> {
    u: PlonkInstance<G>,
    w: PlonkWitness<G::Scalar>,
}

// TODO docs
struct StepCircuitContext<const ARITY: usize, G, C>
where
    G: CurveAffine,
    C: StepCircuit<ARITY, G::Scalar>,
{
    step_circuit: C,
    relaxed_trace: RelaxedTrace<G>,
    z_input: [G::Scalar; ARITY],
}

// TODO docs
struct IVCGadget<const A1: usize, const A2: usize, G1, G2, C1, C2>
where
    G1: CurveAffine<Base = <G2 as PrimeCurveAffine>::Scalar>,
    G2: CurveAffine<Base = <G1 as PrimeCurveAffine>::Scalar>,
    C1: StepCircuit<A1, G1::Scalar>,
    C2: StepCircuit<A2, G2::Scalar>,
{
    primary: StepCircuitContext<A1, G1, C1>,
    secondary: StepCircuitContext<A2, G2, C2>,

    trace: Trace<G2>,

    step: usize,
}

impl<const A1: usize, const A2: usize, G1, G2, C1, C2> IVCGadget<A1, A2, G1, G2, C1, C2>
where
    G1: CurveAffine<Base = <G2 as PrimeCurveAffine>::Scalar>,
    G2: CurveAffine<Base = <G1 as PrimeCurveAffine>::Scalar>,
    C1: StepCircuit<A1, G1::Scalar>,
    C2: StepCircuit<A2, G2::Scalar>,
{
    fn new<RO1, RO2>(
        _pp: &PublicParams<A1, A2, G1, G2, RO1, RO2>,
        _primary: C1,
        _z0_primary: [G1::Scalar; A1],
        _secondary: C2,
        _z0_secondary: [G2::Scalar; A2],
    ) -> Self
    where
        RO1: ROTrait<G1>,
        RO2: ROTrait<G2>,
    {
        todo!()
    }
}
