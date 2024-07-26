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
    nifs::tests::{
        fibo_circuit::{get_fibo_seq, FiboCircuit},
        fibo_circuit_with_lookup::{get_sequence, FiboCircuitWithLookup},
        random_linear_combination_circuit::RandomLinearCombinationCircuit,
    },
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
type Proof = <ProtoGalaxy as FoldingScheme<Affine, L>>::Proof;
type Accumulator = <ProtoGalaxy as FoldingScheme<Affine, L>>::Accumulator;

struct CircuitCtx {
    witness: Witness<Scalar>,
    instance: Instance<Scalar>,
}

impl CircuitCtx {
    fn collect<CIR: Circuit<Scalar>>(cr: CircuitRunner<Scalar, CIR>) -> Self {
        Self {
            witness: cr.try_collect_witness().expect("failed to collect witness"),
            instance: cr.instance,
        }
    }
}

struct Mock<CIRCUIT: Circuit<Scalar>> {
    S: PlonkStructure<Scalar>,
    ck: CommitmentKey<Affine>,

    ro_nark_verifier: RO<Base>,
    ro_acc_prover: RO<Base>,
    ro_acc_verifier: RO<Scalar>,

    circuits_ctx: [CircuitCtx; L],

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

        let (pp, vp) = ProtoGalaxy::setup_params(Affine::identity(), S.clone()).unwrap();

        fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
            PoseidonHash::<F, T, RATE>::new(Spec::<F, T, RATE>::new(R_F, R_P))
        }

        Mock {
            ck,
            ro_nark_verifier: ro(),
            ro_acc_prover: ro(),
            ro_acc_verifier: ro(),
            circuits_ctx: circuits_runners.map(CircuitCtx::collect),
            pp,
            vp,
            S,
            _p: PhantomData,
        }
    }

    pub fn generate_plonk_traces(&mut self) -> [PlonkTrace<Affine>; L] {
        self.circuits_ctx
            .iter()
            .map(|ctx| {
                ProtoGalaxy::generate_plonk_trace(
                    &self.ck,
                    &ctx.instance,
                    &ctx.witness,
                    &self.pp,
                    &mut self.ro_nark_verifier,
                )
                .unwrap()
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn prove(mut self) -> (Accumulator, Proof) {
        let incoming = self.generate_plonk_traces();

        let acc = ProtoGalaxy::new_accumulator(
            AccumulatorArgs::from(&self.S),
            &self.pp,
            &mut self.ro_acc_prover,
        );

        ProtoGalaxy::prove(&self.ck, &self.pp, &mut self.ro_acc_prover, acc, &incoming)
            .expect("`protogalaxy::prove` failed")
    }
}

#[test]
fn random_linear_combination() {
    let (_new_acc, _proof) = Mock::new(
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
    )
    .prove();
}

#[test]
fn fibo() {
    const K: u32 = 4;
    const SIZE: usize = 16;

    let seq1 = get_fibo_seq(1, 1, SIZE);
    let seq2 = get_fibo_seq(2, 3, SIZE);

    let (_new_acc, _proof) = Mock::new(
        10,
        [
            (
                FiboCircuit {
                    a: Scalar::from(seq1[0]),
                    b: Scalar::from(seq1[1]),
                    num: SIZE,
                },
                vec![Scalar::from(seq1[SIZE - 1])],
            ),
            (
                FiboCircuit {
                    a: Scalar::from(seq2[0]),
                    b: Scalar::from(seq2[1]),
                    num: SIZE,
                },
                vec![Scalar::from(seq2[SIZE - 1])],
            ),
        ],
    )
    .prove();
}

#[test]
fn fibo_lookup() {
    const K: u32 = 5;
    const SIZE: usize = 7;

    // circuit 1
    let seq1 = get_sequence(1, 3, 2, SIZE);
    let seq2 = get_sequence(3, 2, 2, SIZE);

    let (_new_acc, _proof) = Mock::new(
        10,
        [
            (
                FiboCircuitWithLookup {
                    a: Scalar::from(seq1[0]),
                    b: Scalar::from(seq1[1]),
                    c: Scalar::from(seq1[2]),
                    num: SIZE,
                },
                vec![],
            ),
            (
                FiboCircuitWithLookup {
                    a: Scalar::from(seq2[0]),
                    b: Scalar::from(seq2[1]),
                    c: Scalar::from(seq2[2]),
                    num: SIZE,
                },
                vec![],
            ),
        ],
    )
    .prove();
}
