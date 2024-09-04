use halo2_proofs::{
    dev::MockProver,
    halo2curves::{
        ff::{FromUniformBytes, PrimeFieldBits},
        group::prime::PrimeCurveAffine,
    },
    plonk::Circuit,
};
use tracing::info_span;
use tracing_test::traced_test;

use super::*;
use crate::{
    commitment,
    halo2curves::bn256::G1Affine as Affine,
    nifs::tests::{
        fibo_circuit::{get_fibo_seq, FiboCircuit},
        fibo_circuit_with_lookup::{get_sequence, FiboCircuitWithLookup},
        random_linear_combination_circuit::RandomLinearCombinationCircuit,
    },
    poseidon::{PoseidonHash, Spec},
    table::{CircuitRunner, Witness},
};

const T: usize = 3;
const RATE: usize = 2;
const R_F: usize = 4;
const R_P: usize = 3;
const L: usize = 3;

type Scalar = <Affine as CurveAffine>::ScalarExt;
type Base = <Affine as CurveAffine>::Base;

type RO<F> = PoseidonHash<F, T, RATE>;
type Instance<F> = Vec<F>;

type ProtoGalaxy = crate::nifs::protogalaxy::ProtoGalaxy<Affine, L>;
type ProverParam = <ProtoGalaxy as FoldingScheme<Affine, L>>::ProverParam;
type VerifierParam = <ProtoGalaxy as FoldingScheme<Affine, L>>::VerifierParam;
type Proof = <ProtoGalaxy as FoldingScheme<Affine, L>>::Proof;
type Accumulator = <ProtoGalaxy as FoldingScheme<Affine, L>>::Accumulator;

struct CircuitCtx {
    witness: Witness<Scalar>,
    instances: Vec<Instance<Scalar>>,
}

impl CircuitCtx {
    fn collect<CIR: Circuit<Scalar>>(cr: CircuitRunner<Scalar, CIR>) -> Self {
        Self {
            witness: cr.try_collect_witness().expect("failed to collect witness"),
            instances: cr.instances,
        }
    }
}

struct Mock<CIRCUIT: Circuit<Scalar>> {
    S: PlonkStructure<Scalar>,
    ck: CommitmentKey<Affine>,

    circuits_ctx: [CircuitCtx; L],

    pp: ProverParam,
    vp: VerifierParam,

    _p: PhantomData<CIRCUIT>,
}

fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
    PoseidonHash::<F, T, RATE>::new(Spec::<F, T, RATE>::new(R_F, R_P))
}

impl<C: Circuit<Scalar>> Mock<C> {
    pub fn new(k_table_size: u32, circuits: [(C, Vec<Vec<Scalar>>); L]) -> Self {
        let circuits_runners = circuits.map(|(circuit, instances)| {
            MockProver::run(k_table_size, &circuit, instances.clone())
                .unwrap()
                .verify()
                .unwrap();

            CircuitRunner::new(k_table_size, circuit, instances)
        });

        let ck = commitment::setup_smallest_key(k_table_size, &circuits_runners[0].cs, b"");
        let S = circuits_runners[0]
            .try_collect_plonk_structure()
            .expect("failed to collect plonk structure");

        let (pp, vp) = ProtoGalaxy::setup_params(Affine::identity(), S.clone()).unwrap();

        Mock {
            ck,
            circuits_ctx: circuits_runners.map(CircuitCtx::collect),
            pp,
            vp,
            S,
            _p: PhantomData,
        }
    }

    pub fn generate_plonk_traces(&mut self) -> [PlonkTrace<Affine>; L] {
        let mut generate_ro = ro();
        let mut is_sat_ro = ro();
        self.circuits_ctx
            .iter()
            .map(|ctx| {
                ProtoGalaxy::generate_plonk_trace(
                    &self.ck,
                    &ctx.instances,
                    &ctx.witness,
                    &self.pp,
                    &mut generate_ro,
                )
                .unwrap()
            })
            .inspect(|trace| {
                self.S
                    .is_sat(&self.ck, &mut is_sat_ro, &trace.u, &trace.w)
                    .unwrap()
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn run(mut self) {
        let incoming = self.generate_plonk_traces();

        let init_accumulator =
            ProtoGalaxy::new_accumulator(AccumulatorArgs::from(&self.S), &self.pp, &mut ro());

        ProtoGalaxy::is_sat_accumulation(&self.S, &init_accumulator)
            .expect("The newly created accumulator is not satisfactory");

        let (accumulator_from_prove, proof) = ProtoGalaxy::prove(
            &self.ck,
            &self.pp,
            &mut ro(),
            init_accumulator.clone(),
            &incoming,
        )
        .expect("`protogalaxy::prove` failed");

        ProtoGalaxy::is_sat(&self.ck, &self.S, &accumulator_from_prove)
            .expect("The accumulator after calling `prove` is not satisfactory");

        let accumulator_from_verify = ProtoGalaxy::verify(
            &self.vp,
            &mut ro(),
            &mut ro(),
            &init_accumulator.into(),
            &incoming.map(|tr| tr.u),
            &proof,
        )
        .unwrap();

        let accumulator_inst_from_prove = AccumulatorInstance::from(accumulator_from_prove);

        assert_eq!(
            accumulator_inst_from_prove.betas,
            accumulator_from_verify.betas,
        );
        assert_eq!(accumulator_inst_from_prove.e, accumulator_from_verify.e,);
        assert_eq!(accumulator_inst_from_prove.ins, accumulator_from_verify.ins);
    }
}

#[traced_test]
#[test]
fn random_linear_combination() {
    Mock::new(
        10,
        [
            (
                RandomLinearCombinationCircuit::new(
                    (1..10).map(Scalar::from).collect(),
                    Scalar::from(2),
                ),
                vec![vec![Scalar::from(4097)]],
            ),
            (
                RandomLinearCombinationCircuit::new(
                    (1..10).map(Scalar::from).collect(),
                    Scalar::from(2),
                ),
                vec![vec![Scalar::from(4097)]],
            ),
            (
                RandomLinearCombinationCircuit::new(
                    (2..11).map(Scalar::from).collect(),
                    Scalar::from(3),
                ),
                vec![vec![Scalar::from(93494)]],
            ),
        ],
    )
    .run();
}

#[traced_test]
#[test]
fn fibo() {
    let _s = info_span!("fibo").entered();

    const K: u32 = 4;
    const SIZE: usize = 16;

    let seq1 = get_fibo_seq(1, 1, SIZE);
    let seq2 = get_fibo_seq(2, 3, SIZE);
    let seq3 = get_fibo_seq(3, 5, SIZE);

    Mock::new(
        10,
        [
            (
                FiboCircuit {
                    a: Scalar::from(seq1[0]),
                    b: Scalar::from(seq1[1]),
                    num: SIZE,
                },
                vec![vec![Scalar::from(seq1[SIZE - 1])]],
            ),
            (
                FiboCircuit {
                    a: Scalar::from(seq2[0]),
                    b: Scalar::from(seq2[1]),
                    num: SIZE,
                },
                vec![vec![Scalar::from(seq2[SIZE - 1])]],
            ),
            (
                FiboCircuit {
                    a: Scalar::from(seq3[0]),
                    b: Scalar::from(seq3[1]),
                    num: SIZE,
                },
                vec![vec![Scalar::from(seq3[SIZE - 1])]],
            ),
        ],
    )
    .run();
}

#[traced_test]
#[test]
fn fibo_lookup() {
    let _s = info_span!("fibo_lookup").entered();

    const K: u32 = 5;
    const SIZE: usize = 7;

    // circuit 1
    let seq1 = get_sequence(1, 3, 2, SIZE);
    let seq2 = get_sequence(3, 2, 2, SIZE);
    let seq3 = get_sequence(3, 2, 2, SIZE);

    Mock::new(
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
            (
                FiboCircuitWithLookup {
                    a: Scalar::from(seq3[0]),
                    b: Scalar::from(seq3[1]),
                    c: Scalar::from(seq3[2]),
                    num: SIZE,
                },
                vec![],
            ),
        ],
    )
    .run();
}
