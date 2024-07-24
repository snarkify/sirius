use halo2_proofs::{
    halo2curves::{
        ff::{FromUniformBytes, PrimeFieldBits},
        group::prime::PrimeCurveAffine,
    },
    plonk::Circuit,
};

use super::{super::tests::*, *};

const T: usize = 3;
const RATE: usize = 2;
const R_F: usize = 4;
const R_P: usize = 3;

use crate::{
    halo2curves::bn256::G1Affine as Affine,
    nifs::tests::random_linear_combination_circuit::RandomLinearCombinationCircuit,
    poseidon::{PoseidonHash, Spec},
    table::{CircuitRunner, Witness},
};

type Scalar = <Affine as CurveAffine>::ScalarExt;
type Base = <Affine as CurveAffine>::Base;

type RO<F> = PoseidonHash<F, T, RATE>;
type Instance<F> = Vec<F>;
const L: usize = 2;

type ProverParam = <ProtoGalaxy<Affine, L> as FoldingScheme<Affine, L>>::ProverParam;
type VerifierParam = <ProtoGalaxy<Affine, L> as FoldingScheme<Affine, L>>::VerifierParam;

struct Mock<CIRCUIT: Circuit<Scalar>> {
    S: PlonkStructure<Scalar>,
    ck: CommitmentKey<Affine>,

    ro_nark_verifier: RO<Base>,
    ro_acc_prover: RO<Base>,
    ro_acc_verifier: RO<Scalar>,

    circuit_meta: [(Witness<Scalar>, Instance<Scalar>); L],

    pp: ProverParam,
    vp: VerifierParam,

    _p: PhantomData<CIRCUIT>,
}

impl<C: Circuit<Scalar>> Mock<C> {
    pub fn new(k_table_size: u32, circuits: [(C, Vec<Scalar>); L]) -> Self {
        let circuits_runners =
            circuits.map(|(circuit, instance)| CircuitRunner::new(k_table_size, circuit, instance));

        let ck = setup_smallest_commitment_key(k_table_size, &circuits_runners[0].cs, b"");
        let S = circuits_runners[0]
            .try_collect_plonk_structure()
            .expect("failed to collect plonk structure");

        let circuit_meta = circuits_runners.map(|cr| {
            (
                cr.try_collect_witness().expect("failed to collect witness"),
                cr.instance,
            )
        });

        let (pp, vp) =
            ProtoGalaxy::<Affine, L>::setup_params(Affine::identity(), S.clone()).unwrap();

        fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
            PoseidonHash::<F, T, RATE>::new(Spec::<F, T, RATE>::new(R_F, R_P))
        }

        Mock {
            ck,
            ro_nark_verifier: ro(),
            ro_acc_prover: ro(),
            ro_acc_verifier: ro(),
            circuit_meta,
            pp,
            vp,
            S,
            _p: PhantomData,
        }
    }

    pub fn generate_plonk_traces(&mut self) -> [PlonkTrace<Affine>; L] {
        self.circuit_meta
            .iter()
            .map(|(witness, instance)| {
                ProtoGalaxy::<Affine, L>::generate_plonk_trace(
                    &self.ck,
                    instance,
                    witness,
                    &self.pp,
                    &mut self.ro_nark_verifier,
                )
                .unwrap()
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }
}

#[test]
fn simple_proto() {
    let inputs1 = (1..10).map(Scalar::from).collect();
    let circuit1 = RandomLinearCombinationCircuit::new(inputs1, Scalar::from_u128(2));
    let public_inputs1 = vec![Scalar::from_u128(4097)];

    let inputs2 = (2..11).map(Scalar::from).collect();
    let circuit2 = RandomLinearCombinationCircuit::new(inputs2, Scalar::from_u128(3));
    let public_inputs2 = vec![Scalar::from_u128(93494)];

    let mut m = Mock::new(10, [(circuit1, public_inputs1), (circuit2, public_inputs2)]);

    let incoming = m.generate_plonk_traces();

    let acc = ProtoGalaxy::<Affine, L>::new_accumulator(
        AccumulatorArgs::from(&m.S),
        &m.pp,
        &mut m.ro_acc_prover,
    );

    let (_new_acc, _proof) =
        ProtoGalaxy::<Affine, L>::prove(&m.ck, &m.pp, &mut m.ro_acc_prover, acc, &incoming)
            .unwrap();
}
