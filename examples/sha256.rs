#![allow(dead_code)]

use std::iter;

use halo2_gadgets::sha256::BLOCK_SIZE;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error},
};

pub use halo2_gadgets::sha256::{BlockWord, Sha256, Table16Chip, Table16Config};
use halo2curves::pasta::pallas;
use sirius::step_circuit::{StepCircuit, SynthesisError};

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
const ARITY: usize = 31 * BLOCK_SIZE;

impl StepCircuit<ARITY, B> for TestSha256Circuit {
    type StepConfig = Table16Config;

    fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self::StepConfig {
        Table16Chip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        region: Region<'_, B>,
        z_in: &[AssignedCell<B, B>; ARITY],
    ) -> Result<[AssignedCell<B, B>; ARITY], SynthesisError> {
        todo!(
            "Call `Sha256::digest` in {region:?} & {z_in:?} instead of real values use {config:?}"
        )
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
