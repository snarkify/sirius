#![allow(dead_code)]

use std::iter;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error},
};

pub use halo2_gadgets::sha256::{BlockWord, Sha256, Table16Chip, Table16Config};
use halo2curves::pasta::pallas;

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

        Sha256::digest(table16_chip, layouter.namespace(|| "'abc' * 2"), &input)?;

        Ok(())
    }
}

fn main() {
    use halo2_proofs::dev::MockProver;

    const K: u32 = 17;

    let prover = match MockProver::run(K, &TestSha256Circuit {}, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };

    assert_eq!(prover.verify(), Ok(()));
}
