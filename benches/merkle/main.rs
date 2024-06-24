use std::{io, iter, num::NonZeroUsize, path::Path};

use bn256::G1 as C1;
use criterion::{black_box, criterion_group, Criterion};
use grumpkin::G1 as C2;
use metadata::LevelFilter;
use rand::Rng;
use sirius::{
    commitment::CommitmentKey,
    halo2_proofs::{circuit::*, plonk::*},
    halo2curves::{
        bn256,
        ff::{Field, FromUniformBytes, PrimeFieldBits},
        grumpkin, CurveAffine, CurveExt,
    },
    ivc::{step_circuit, CircuitPublicParamsInput, PublicParams, StepCircuit, SynthesisError, IVC},
    main_gate::{MainGate, RegionCtx},
    poseidon::ROPair,
};
use tracing::*;

type C1Affine = <C1 as sirius::halo2curves::group::prime::PrimeCurve>::Affine;
type C2Affine = <C2 as sirius::halo2curves::group::prime::PrimeCurve>::Affine;

type C1Scalar = <C1 as sirius::halo2curves::group::Group>::Scalar;
type C2Scalar = <C2 as sirius::halo2curves::group::Group>::Scalar;

type RandomOracle = sirius::poseidon::PoseidonRO<T, RATE>;
type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };
const COMMITMENT_KEY_SIZE: usize = 27;
const INDEX_LIMIT: u32 = 1 << 31;
const ARITY: usize = 1;

const CIRCUIT_TABLE_SIZE1: usize = 18;
const CIRCUIT_TABLE_SIZE2: usize = 17;

use sirius::gadgets::merkle_tree::{
    chip::MerkleTreeUpdateChip,
    off_circuit::{NodeUpdate, Proof, Tree},
    *,
};
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

use crate::{RATE, T};

struct MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    tree: Tree<F>,
    last_proof: Option<Box<[Proof<F>]>>,
    batch_size: usize,
}

impl<F> Default for MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    fn default() -> Self {
        Self {
            tree: Default::default(),
            last_proof: None,
            batch_size: 2,
        }
    }
}

impl<F> MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    pub fn new(batch_size: usize) -> Self {
        Self {
            batch_size,
            ..Default::default()
        }
    }
    fn update_leaves(&mut self, update: impl Iterator<Item = (u32, F)>) -> (F, F) {
        assert!(update.size_hint().0 >= self.batch_size);
        let proofs = update
            .map(|(index, data)| self.tree.update_leaf(index, data))
            .take(self.batch_size)
            .collect::<Box<[_]>>();

        let old = proofs.first().unwrap().root().old;
        let new = proofs.last().unwrap().root().new;

        self.last_proof = Some(proofs);

        (old, new)
    }
}

impl<F> StepCircuit<1, F> for MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    type Config = MainGateConfig;
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        MainGate::configure(cs)
    }

    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_i: &[AssignedCell<F, F>; 1],
    ) -> Result<[AssignedCell<F, F>; 1], SynthesisError> {
        layouter
            .assign_region(
                || "",
                |region| {
                    let mut region = RegionCtx::new(region, 0);

                    let mut prev = z_i[0].clone();
                    for proof in self.last_proof.as_ref().unwrap().iter() {
                        let NodeUpdate { old, new, .. } = MerkleTreeUpdateChip::new(proof.clone())
                            .prove_next_update(&mut region, config.clone())?;

                        region.constrain_equal(prev.cell(), old.cell())?;
                        prev = new;
                    }

                    Ok([prev])
                },
            )
            .map_err(SynthesisError::Halo2)
    }
}

fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    const FOLDER: &str = ".cache/examples";

    unsafe { CommitmentKey::load_or_setup_cache(Path::new(FOLDER), label, k) }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let batch_size: usize = std::env::var("BATCH_SIZE").unwrap().parse().unwrap();
    info!("with batch size = {batch_size}");

    let _span = info_span!("merkle_bench").entered();
    let prepare_span = info_span!("prepare").entered();

    let mut sc1 = MerkleTreeUpdateCircuit::new(batch_size);
    let (sc1_default_root, _) = sc1.update_leaves(iter::repeat_with(|| {
        (rng.gen::<u32>() % INDEX_LIMIT, C1Scalar::random(&mut rng))
    }));

    let sc2 = step_circuit::trivial::Circuit::<ARITY, _>::default();

    let primary_spec = RandomOracleConstant::<<C1 as CurveExt>::ScalarExt>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<<C2 as CurveExt>::ScalarExt>::new(10, 10);

    let primary_commitment_key =
        get_or_create_commitment_key::<bn256::G1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get secondary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<grumpkin::G1Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get primary key");

    let pp = PublicParams::<
        '_,
        ARITY,
        ARITY,
        T,
        C1Affine,
        C2Affine,
        MerkleTreeUpdateCircuit<_>,
        step_circuit::trivial::Circuit<ARITY, _>,
        RandomOracle,
        RandomOracle,
    >::new(
        CircuitPublicParamsInput::new(
            CIRCUIT_TABLE_SIZE1 as u32,
            &primary_commitment_key,
            primary_spec.clone(),
            &sc1,
        ),
        CircuitPublicParamsInput::new(
            CIRCUIT_TABLE_SIZE2 as u32,
            &secondary_commitment_key,
            secondary_spec.clone(),
            &sc2,
        ),
        LIMB_WIDTH,
        LIMBS_COUNT_LIMIT,
    )
    .unwrap();

    prepare_span.exit();

    let mut ivc = IVC::new(&pp, &sc1, [sc1_default_root], &sc2, [C2Scalar::ZERO], true).unwrap();

    let mut group = c.benchmark_group("ivc_of_merkle_tree");
    group.significance_level(0.1).sample_size(30);
    group.bench_function("fold_step_merkle_tree", |b| {
        b.iter(|| {
            let input =
                iter::repeat_with(|| (rng.gen::<u32>() % INDEX_LIMIT, C1Scalar::random(&mut rng)));

            sc1.update_leaves(black_box(input));
            ivc.fold_step(&pp, &sc1, &sc2).unwrap();
        })
    });

    group.bench_function("verify_merkle_tree", |b| {
        b.iter(|| {
            ivc.verify(&pp).unwrap();
        })
    });

    group.finish();
}

criterion_group!(benches, criterion_benchmark);

fn main() {
    tracing_subscriber::fmt()
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        )
        .json()
        .init();

    benches();

    criterion::Criterion::default()
        .configure_from_args()
        .final_summary();
}
