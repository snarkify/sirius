use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance},
};
use halo2curves::group::ff::FromUniformBytes;
use prettytable::{row, Cell, Row, Table};

use crate::{
    main_gate::{MainGate, MainGateConfig, RegionCtx},
    util::trim_leading_zeros,
};

use super::*;

const T: usize = 3;

#[derive(Clone, Debug)]
struct TestCircuitConfig {
    pconfig: MainGateConfig<T>,
    instance: Column<Instance>,
}

struct TestCircuit<F: PrimeField> {
    inputs: Vec<F>,
    r: F,
}

impl<F: PrimeField> TestCircuit<F> {
    fn new(inputs: Vec<F>, r: F) -> Self {
        Self { inputs, r }
    }
}

impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for TestCircuit<F> {
    type Config = TestCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            inputs: Vec::new(),
            r: F::ZERO,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        let pconfig = MainGate::configure(meta);
        Self::Config { pconfig, instance }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let pchip = MainGate::new(config.pconfig);
        let output = layouter.assign_region(
            || "test",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                pchip.random_linear_combination(ctx, self.inputs.clone(), self.r)
            },
        )?;
        layouter.constrain_instance(output.cell(), config.instance, 0)?;
        Ok(())
    }
}

#[test]
fn test_assembly() -> Result<(), Error> {
    use halo2curves::pasta::Fp;

    const K: u32 = 4;
    let mut inputs = Vec::new();
    for i in 1..10 {
        inputs.push(Fp::from(i as u64));
    }
    let circuit = TestCircuit::new(inputs, Fp::ONE);
    let output = Fp::from_str_vartime("45").unwrap();
    let public_inputs = vec![output];

    let td = CircuitRunner::<Fp, _>::new(K, circuit, public_inputs);
    let witness = td.try_collect_witness()?;

    let mut table = Table::new();
    table.add_row(row!["s0", "s1", "s2", "in", "out"]);
    let col = 5;
    for i in 0..2usize.pow(K) {
        let mut row = vec![];
        for j in 0..col {
            if let Some(val) = witness.get(j).and_then(|v| v.get(i)) {
                row.push(trim_leading_zeros(format!("{:?}", val)));
            }
        }
        table.add_row(Row::new(row.iter().map(|s| Cell::new(s)).collect()));
    }
    // table.printstd();
    Ok(())
}
