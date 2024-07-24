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

type ProtoGalaxy = crate::nifs::protogalaxy::ProtoGalaxy<Affine, L>;
type ProverParam = <ProtoGalaxy as FoldingScheme<Affine, L>>::ProverParam;
type VerifierParam = <ProtoGalaxy as FoldingScheme<Affine, L>>::VerifierParam;

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

        let (pp, vp) = ProtoGalaxy::setup_params(Affine::identity(), S.clone()).unwrap();

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
                ProtoGalaxy::generate_plonk_trace(
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
fn random_linear_combination() {
    let mut m = Mock::new(
        10,
        [
            (
                RandomLinearCombinationCircuit::new(
                    (1..10).map(Scalar::from).collect(),
                    Scalar::from(2),
                ),
                vec![Scalar::from(4097)],
            ),
            (
                RandomLinearCombinationCircuit::new(
                    (2..11).map(Scalar::from).collect(),
                    Scalar::from(3),
                ),
                vec![Scalar::from(93494)],
            ),
        ],
    );

    let incoming = m.generate_plonk_traces();

    let acc =
        ProtoGalaxy::new_accumulator(AccumulatorArgs::from(&m.S), &m.pp, &mut m.ro_acc_prover);

    let (_new_acc, _proof) = ProtoGalaxy::prove(&m.ck, &m.pp, &mut m.ro_acc_prover, acc, &incoming)
        .expect("`protogalaxy::prove` failed");
}
