#![allow(dead_code)]

use std::{array, env, io, iter, marker::PhantomData, path::Path};

use bn256::G1 as C1;
use grumpkin::G1 as C2;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::ConstraintSystem,
};
use metadata::LevelFilter;
use sirius::{
    commitment::CommitmentKey,
    ff::PrimeField,
    group::{prime::PrimeCurve, Group},
    halo2curves::{bn256, grumpkin, CurveAffine},
    ivc::{cyclefold, StepCircuit, SynthesisError},
};
use tracing::*;

mod table16;

const BLOCK_SIZE: usize = 16;
const DIGEST_SIZE: usize = 8;

pub mod sha256 {
    //! The [SHA-256] hash function.
    //!
    //! [SHA-256]: https://tools.ietf.org/html/rfc6234

    use std::{cmp::min, convert::TryInto, fmt};

    use halo2_proofs::{
        arithmetic::Field,
        circuit::{AssignedCell, Chip, Layouter},
        plonk::Error,
    };

    pub use super::table16::{BlockWord, Table16Chip, Table16Config};

    /// The size of a SHA-256 block, in 32-bit words.
    pub const BLOCK_SIZE: usize = 16;
    /// The size of a SHA-256 digest, in 32-bit words.
    const DIGEST_SIZE: usize = 8;

    /// The set of circuit instructions required to use the [`Sha256`] gadget.
    pub trait Sha256Instructions<F: Field>: Chip<F> {
        /// Variable representing the SHA-256 internal state.
        type State: Clone + fmt::Debug;
        /// Variable representing a 32-bit word of the input block to the SHA-256 compression
        /// function.
        type BlockWord: Copy + fmt::Debug + Default;

        /// Places the SHA-256 IV in the circuit, returning the initial state variable.
        fn initialization_vector(
            &self,
            layouter: &mut impl Layouter<F>,
        ) -> Result<Self::State, Error>;

        /// Creates an initial state from the output state of a previous block
        fn initialization(
            &self,
            layouter: &mut impl Layouter<F>,
            init_state: &Self::State,
        ) -> Result<Self::State, Error>;

        /// Starting from the given initialized state, processes a block of input and returns the
        /// final state.
        fn compress(
            &self,
            layouter: &mut impl Layouter<F>,
            initialized_state: &Self::State,
            input: [Self::BlockWord; BLOCK_SIZE],
            input_cells: [AssignedCell<F, F>; BLOCK_SIZE],
        ) -> Result<Self::State, Error>;

        /// Converts the given state into a message digest.
        fn digest(
            &self,
            layouter: &mut impl Layouter<F>,
            state: &Self::State,
        ) -> Result<[Self::BlockWord; DIGEST_SIZE], Error>;

        /// Converts the given state into a message digest.
        fn digest_cells(
            &self,
            layouter: &mut impl Layouter<F>,
            state: &Self::State,
        ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error>;
    }

    /// The output of a SHA-256 circuit invocation.
    #[derive(Debug)]
    pub struct Sha256Digest<BlockWord>([BlockWord; DIGEST_SIZE]);

    /// A gadget that constrains a SHA-256 invocation. It supports input at a granularity of
    /// 32 bits.
    #[derive(Debug)]
    pub struct Sha256<F: Field, CS: Sha256Instructions<F>> {
        chip: CS,
        state: CS::State,
        cur_block: Vec<CS::BlockWord>,
        cur_block_src_cell: Vec<AssignedCell<F, F>>,
        length: usize,
    }

    impl<F: Field, Sha256Chip: Sha256Instructions<F>> Sha256<F, Sha256Chip> {
        /// Create a new hasher instance.
        pub fn new(chip: Sha256Chip, mut layouter: impl Layouter<F>) -> Result<Self, Error> {
            let state = chip.initialization_vector(&mut layouter)?;
            Ok(Sha256 {
                chip,
                state,
                cur_block: Vec::with_capacity(BLOCK_SIZE),
                cur_block_src_cell: Vec::with_capacity(BLOCK_SIZE),
                length: 0,
            })
        }

        /// Digest data, updating the internal state.
        pub fn update(
            &mut self,
            mut layouter: impl Layouter<F>,
            mut input: &[Sha256Chip::BlockWord],
            mut input_cells: &[AssignedCell<F, F>],
        ) -> Result<(), Error> {
            assert_eq!(input.len(), input_cells.len());

            self.length += input.len() * 32;

            // Fill the current block, if possible.
            let cur_block_splitter = min(BLOCK_SIZE - self.cur_block.len(), input.len());
            let (l, r) = input.split_at(cur_block_splitter);
            self.cur_block.extend_from_slice(l);
            input = r;

            // If we still don't have a full block, we are done.
            if self.cur_block.len() < BLOCK_SIZE {
                return Ok(());
            }

            // Check input cells for copy constraint
            let (l_cells, r_cells) = input_cells.split_at(cur_block_splitter);
            input_cells = r_cells;

            // Assign the last `l_cells.len()` of cells to be checked by copy constraint
            self.cur_block_src_cell.extend_from_slice(l_cells);

            // Process the now-full current block.
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
                self.cur_block_src_cell
                    .to_vec()
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
            self.cur_block.clear();

            // Process any additional full blocks.
            let mut chunks_iter = input.chunks_exact(BLOCK_SIZE);
            let mut input_cells_chunks = input_cells.chunks_exact(BLOCK_SIZE);

            for (chunk, cells) in (&mut chunks_iter).zip(&mut input_cells_chunks) {
                self.state = self.chip.initialization(&mut layouter, &self.state)?;
                self.state = self.chip.compress(
                    &mut layouter,
                    &self.state,
                    chunk.try_into().expect("chunk.len() == BLOCK_SIZE"),
                    cells
                        .to_vec()
                        .try_into()
                        .expect("chunk.len() == BLOCK_SIZE"),
                )?;
            }

            // Cache the remaining partial block, if any.
            // TODO Process remainder of `input_cells`
            self.cur_block.extend_from_slice(chunks_iter.remainder());
            self.cur_block_src_cell
                .extend_from_slice(input_cells_chunks.remainder());

            Ok(())
        }

        /// Retrieve result and consume hasher instance.
        pub fn finalize(
            mut self,
            mut layouter: impl Layouter<F>,
        ) -> Result<Sha256Digest<Sha256Chip::BlockWord>, Error> {
            // Pad the remaining block
            if !self.cur_block.is_empty() {
                let padding =
                    vec![Sha256Chip::BlockWord::default(); BLOCK_SIZE - self.cur_block.len()];
                self.cur_block.extend_from_slice(&padding);
                self.state = self.chip.initialization(&mut layouter, &self.state)?;
                self.state = self.chip.compress(
                    &mut layouter,
                    &self.state,
                    self.cur_block[..]
                        .try_into()
                        .expect("cur_block.len() == BLOCK_SIZE"),
                    self.cur_block_src_cell
                        .to_vec()
                        .try_into()
                        .expect("cur_block.len() == BLOCK_SIZE"),
                )?;
            }
            self.chip
                .digest(&mut layouter, &self.state)
                .map(Sha256Digest)
        }
        /// Retrieve result and consume hasher instance.
        pub fn finalize_cells(
            mut self,
            mut layouter: impl Layouter<F>,
        ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error> {
            // Pad the remaining block
            if !self.cur_block.is_empty() {
                let padding =
                    vec![Sha256Chip::BlockWord::default(); BLOCK_SIZE - self.cur_block.len()];
                self.cur_block.extend_from_slice(&padding);
                self.state = self.chip.initialization(&mut layouter, &self.state)?;
                self.state = self.chip.compress(
                    &mut layouter,
                    &self.state,
                    self.cur_block[..]
                        .try_into()
                        .expect("cur_block.len() == BLOCK_SIZE"),
                    self.cur_block_src_cell
                        .to_vec()
                        .try_into()
                        .expect("cur_block.len() == BLOCK_SIZE"),
                )?;
            }
            self.chip.digest_cells(&mut layouter, &self.state)
        }

        /// Convenience function to compute hash of the data. It will handle hasher creation,
        /// data feeding and finalization.
        pub fn digest_cells(
            chip: Sha256Chip,
            mut layouter: impl Layouter<F>,
            data: &[Sha256Chip::BlockWord],
            input_cells: &[AssignedCell<F, F>],
        ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error> {
            let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
            hasher.update(layouter.namespace(|| "update"), data, input_cells)?;
            hasher.finalize_cells(layouter.namespace(|| "finalize"))
        }
    }
}

pub use sha256::{BlockWord, Sha256, Table16Chip, Table16Config};
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

#[derive(Default, Debug)]
struct TestSha256Circuit<F: PrimeField> {
    _p: PhantomData<F>,
}

// TODO
const ARITY: usize = BLOCK_SIZE / 2;

const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 21;
const COMMITMENT_KEY_SIZE: usize = 26;
const FOLD_STEP_COUNT: usize = 5;

impl<F: PrimeField> StepCircuit<ARITY, F> for TestSha256Circuit<F> {
    type Config = Table16Config;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Table16Chip::configure(meta)
    }

    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_in: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError> {
        Table16Chip::load(config.clone(), layouter).map_err(SynthesisError::Halo2)?;
        let table16_chip = Table16Chip::construct(config);

        let input: [AssignedCell<F, F>; BLOCK_SIZE] = iter::repeat(z_in.iter())
            .take(2)
            .flatten()
            .cloned()
            .collect::<Vec<AssignedCell<F, F>>>()
            .try_into()
            .expect("Unreachable, ARITY * 2 == BLOCK_SIZE");

        let values = input
            .iter()
            .map(|cell| cell.value().map(|v| *v).unwrap().unwrap_or_default())
            .map(|field_value| {
                u32::from_be_bytes(
                    field_value
                        .to_repr()
                        .as_ref()
                        .iter()
                        .take(4)
                        .copied()
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                )
            })
            .map(|value| BlockWord(Value::known(value)))
            .collect::<Box<[BlockWord]>>();

        Sha256::digest_cells(
            table16_chip,
            layouter.namespace(|| "'abc' * 2"),
            values.as_ref(),
            &input,
        )
        .map_err(SynthesisError::Halo2)
    }
}

type C1Affine = <C1 as PrimeCurve>::Affine;
type C2Affine = <C2 as PrimeCurve>::Affine;

type C1Scalar = <C1 as Group>::Scalar;
type C2Scalar = <C2 as Group>::Scalar;

const FOLDER: &str = ".cache/examples";

#[instrument]
fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
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

    // To osterize the total execution time of the example
    let _span = info_span!("sha256_example").entered();

    let primary = TestSha256Circuit::default();

    let primary_commitment_key =
        get_or_create_commitment_key::<C1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get primary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<C2Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get secondary key");

    let mut pp = cyclefold::PublicParams::new(
        &primary,
        primary_commitment_key,
        secondary_commitment_key,
        PRIMARY_CIRCUIT_TABLE_SIZE as u32,
    )
    .unwrap();

    let primary_input = array::from_fn(|i| C1Scalar::from(i as u64));

    let mut ivc = cyclefold::IVC::new(&mut pp, &primary, primary_input).expect("while step=0");

    for step in 1..=FOLD_STEP_COUNT {
        ivc = ivc
            .next(&pp, &primary)
            .unwrap_or_else(|err| panic!("while step={step}: {err:?}"));
    }

    ivc.verify(&pp).expect("while verify");
}
