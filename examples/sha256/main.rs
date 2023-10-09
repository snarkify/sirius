#![allow(dead_code)]

use std::iter;

use halo2_gadgets::sha256::BLOCK_SIZE;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error},
};

use halo2curves::pasta::pallas;
use sirius::step_circuit::{StepCircuit, SynthesisError};

mod table16;

const DIGEST_SIZE: usize = 8;

pub mod sha256 {
    //! The [SHA-256] hash function.
    //!
    //! [SHA-256]: https://tools.ietf.org/html/rfc6234

    use std::cmp::min;
    use std::convert::TryInto;
    use std::fmt;

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
            input_cells: Option<[AssignedCell<F, F>; BLOCK_SIZE]>,
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
                length: 0,
            })
        }

        /// Digest data, updating the internal state.
        pub fn update(
            &mut self,
            mut layouter: impl Layouter<F>,
            mut input: &[Sha256Chip::BlockWord],
            _input_cells: Option<[AssignedCell<F, F>; BLOCK_SIZE]>,
        ) -> Result<(), Error> {
            self.length += input.len() * 32;

            // Fill the current block, if possible.
            let remaining = BLOCK_SIZE - self.cur_block.len();
            let (l, r) = input.split_at(min(remaining, input.len()));
            self.cur_block.extend_from_slice(l);
            input = r;

            // If we still don't have a full block, we are done.
            if self.cur_block.len() < BLOCK_SIZE {
                return Ok(());
            }

            // Process the now-full current block.
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
                None, // TODO Pass here first cells
            )?;
            self.cur_block.clear();

            // Process any additional full blocks.
            let mut chunks_iter = input.chunks_exact(BLOCK_SIZE);
            for chunk in &mut chunks_iter {
                self.state = self.chip.initialization(&mut layouter, &self.state)?;
                self.state = self.chip.compress(
                    &mut layouter,
                    &self.state,
                    chunk.try_into().expect("chunk.len() == BLOCK_SIZE"),
                    None, // TODO Pass here rest of cells
                )?;
            }

            // Cache the remaining partial block, if any.
            let rem = chunks_iter.remainder();
            self.cur_block.extend_from_slice(rem);

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
                    None,
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
                    None,
                )?;
            }
            self.chip.digest_cells(&mut layouter, &self.state)
        }

        /// Convenience function to compute hash of the data. It will handle hasher creation,
        /// data feeding and finalization.
        pub fn digest(
            chip: Sha256Chip,
            mut layouter: impl Layouter<F>,
            data: &[Sha256Chip::BlockWord],
        ) -> Result<Sha256Digest<Sha256Chip::BlockWord>, Error> {
            let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
            hasher.update(layouter.namespace(|| "update"), data, None)?;
            hasher.finalize(layouter.namespace(|| "finalize"))
        }

        /// Convenience function to compute hash of the data. It will handle hasher creation,
        /// data feeding and finalization.
        pub fn digest_cells(
            chip: Sha256Chip,
            mut layouter: impl Layouter<F>,
            data: &[Sha256Chip::BlockWord],
            input_cells: Option<[AssignedCell<F, F>; BLOCK_SIZE]>,
        ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error> {
            let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
            hasher.update(layouter.namespace(|| "update"), data, input_cells)?;
            hasher.finalize_cells(layouter.namespace(|| "finalize"))
        }
    }
}

pub use sha256::{BlockWord, Sha256, Table16Chip, Table16Config};

#[derive(Default)]
struct TestSha256Circuit {}

impl Circuit<pallas::Base> for TestSha256Circuit {
    type Config = Table16Config;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self::Config {
        Table16Chip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<pallas::Base>,
    ) -> Result<(), Error> {
        Table16Chip::load(config.clone(), &mut layouter)?;
        let table16_chip = Table16Chip::construct(config);

        // Test vector: "abc", repeated 31 times
        let input = iter::repeat(
            [
                0b01100001011000100110001110000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000000000,
                0b00000000000000000000000000011000,
            ]
            .into_iter()
            .map(|v| BlockWord(Value::known(v))),
        )
        .take(31)
        .flatten()
        .collect::<Box<[_]>>();

        assert_eq!(input.len(), ARITY);

        Sha256::digest(table16_chip, layouter.namespace(|| "'abc' * 2"), &input)?;

        Ok(())
    }
}

type B = pallas::Base;
// TODO
const ARITY: usize = BLOCK_SIZE / 2;

impl StepCircuit<ARITY, B> for TestSha256Circuit {
    type StepConfig = Table16Config;

    fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self::StepConfig {
        Table16Chip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<B>,
        z_in: &[AssignedCell<B, B>; ARITY],
    ) -> Result<[AssignedCell<B, B>; ARITY], SynthesisError> {
        Table16Chip::load(config.clone(), layouter)?;
        let table16_chip = Table16Chip::construct(config);

        let input: [AssignedCell<B, B>; BLOCK_SIZE] = iter::repeat(z_in.iter())
            .take(2)
            .flatten()
            .cloned()
            .collect::<Vec<AssignedCell<B, B>>>()
            .try_into()
            .expect("Unreachable, ARITY * 2 == BLOCK_SIZE");

        Ok(Sha256::digest_cells(
            table16_chip,
            layouter.namespace(|| "'abc' * 2"),
            &[], // TODO Pass here z_in
            Some(input),
        )?)
    }
}

fn main() {
    use halo2_proofs::dev::MockProver;

    const K: u32 = 17;

    let prover = match MockProver::run(K, &TestSha256Circuit {}, vec![]) {
        Ok(prover) => prover,
        Err(err) => panic!("{err:#?}"),
    };

    assert_eq!(prover.verify(), Ok(()));
}
