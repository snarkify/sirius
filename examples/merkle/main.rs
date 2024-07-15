use std::{collections::VecDeque, env, io, iter, num::NonZeroUsize, path::Path};

use bn256::G1 as C1;
use grumpkin::G1 as C2;
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
use tracing::{info, info_span};

type C1Affine = <C1 as sirius::halo2curves::group::prime::PrimeCurve>::Affine;
type C2Affine = <C2 as sirius::halo2curves::group::prime::PrimeCurve>::Affine;

pub type C1Scalar = <C1 as sirius::halo2curves::group::Group>::Scalar;
type C2Scalar = <C2 as sirius::halo2curves::group::Group>::Scalar;

type RandomOracle = sirius::poseidon::PoseidonRO<T, RATE>;
type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

const COMMITMENT_KEY_SIZE: usize = 23;

const INDEX_LIMIT: u32 = 1 << 31;
const ARITY: usize = 1;

const CIRCUIT_TABLE_SIZE1: usize = 17;
const CIRCUIT_TABLE_SIZE2: usize = 17;

mod merkle_tree_gadget;

use merkle_tree_gadget::{
    chip::MerkleTreeUpdateChip,
    off_circuit::{NodeUpdate, Proof, Tree},
    *,
};
use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

type ProofBatch<F> = Box<[Proof<F>]>;
pub struct MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    tree: Tree<F>,
    proofs_batches: VecDeque<ProofBatch<F>>,
    batch_size: usize,
}

impl<F> Default for MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    fn default() -> Self {
        Self {
            tree: Default::default(),
            proofs_batches: VecDeque::new(),
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
    pub fn new_with_random_updates(
        rng: &mut impl Rng,
        batch_size: usize,
        batches_count: usize,
    ) -> Self {
        let mut self_ = Self::new(batch_size);

        for _ in 0..=batches_count {
            self_.random_update_leaves(rng);
        }

        self_
    }

    pub fn pop_front_proof_batch(&mut self) -> bool {
        self.proofs_batches.pop_front().is_some()
    }

    pub fn front_proof_batch(&self) -> &ProofBatch<F> {
        self.proofs_batches.front().as_ref().unwrap()
    }

    pub fn random_update_leaves(&mut self, mut rng: &mut impl Rng) {
        self.update_leaves(iter::repeat_with(move || {
            (rng.gen::<u32>() % INDEX_LIMIT, F::random(&mut rng))
        }));
    }

    fn update_leaves(&mut self, update: impl Iterator<Item = (u32, F)>) -> (F, F) {
        assert!(update.size_hint().0 >= self.batch_size);
        let proofs = update
            .map(|(index, data)| self.tree.update_leaf(index, data))
            .take(self.batch_size)
            .collect::<Box<[_]>>();

        let old = proofs.first().unwrap().root().old;
        let new = proofs.last().unwrap().root().new;

        self.proofs_batches.push_back(proofs);

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

    fn process_step(
        &self,
        _z_i: &[F; ARITY],
        _k_table_size: u32,
    ) -> Result<[F; ARITY], SynthesisError> {
        Ok([self.front_proof_batch().last().as_ref().unwrap().root().new])
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
                    for proof in self.front_proof_batch().iter() {
                        let NodeUpdate { old, new, .. } = MerkleTreeUpdateChip::new(proof.clone())
                            .prove_next_update(&mut region, config.clone())?;

                        region.constrain_equal(prev.cell(), old.cell())?;
                        prev = new;
                    }
                    info!("offset = {}", region.offset);

                    Ok([prev])
                },
            )
            .map_err(SynthesisError::Halo2)
    }
}

impl<F> Circuit<F> for MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    type Config = <Self as StepCircuit<1, F>>::Config;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        todo!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        <Self as StepCircuit<1, F>>::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |region| {
                let mut region = RegionCtx::new(region, 0);

                region.next();

                let mut prev = Option::<AssignedCell<F, F>>::None;
                for proof in self.front_proof_batch().iter() {
                    let NodeUpdate { old, new, .. } = MerkleTreeUpdateChip::new(proof.clone())
                        .prove_next_update(&mut region, config.clone())?;

                    if let Some(prev) = prev {
                        region.constrain_equal(prev.cell(), old.cell())?;
                    }
                    prev = Some(new);
                }

                Ok([prev])
            },
        )?;

        Ok(())
    }
}

fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    const FOLDER: &str = ".cache/examples";

    unsafe { CommitmentKey::load_or_setup_cache(Path::new(FOLDER), label, k) }
}

fn main() {
    let builder = tracing_subscriber::fmt()
        // Adds events to track the entry and exit of the span, which are used to build
        // time-profiling
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        // Changes the default level to INFO
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        );

    // Structured logs are needed for time-profiling, while for simple run regular logs are
    // more convenient.
    //
    // So this expr keeps track of the --json argument for turn-on json-logs
    if env::args().any(|arg| arg.eq("--json")) {
        builder.json().init();
    } else {
        builder.init();
    }

    let mut rng = rand::thread_rng();

    let _span = info_span!("merkle_example").entered();
    let prepare_span = info_span!("prepare").entered();

    let step_count = NonZeroUsize::new(2).unwrap();
    let mut sc1 = MerkleTreeUpdateCircuit::new_with_random_updates(&mut rng, 1, step_count.get());

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

    let mut ivc = IVC::new(
        &pp,
        &sc1,
        [*Tree::default().get_root()],
        &sc2,
        [C2Scalar::ZERO],
        false,
    )
    .unwrap();

    for _ in 0..step_count.get() {
        sc1.pop_front_proof_batch();
        ivc.fold_step(&pp, &sc1, &sc2).unwrap();
    }

    ivc.verify(&pp).unwrap();
}
