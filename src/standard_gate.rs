use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Cell, Chip, Region, Value, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Fixed, Instance, Error}, 
    poly::Rotation};
use ff::PrimeField;

#[derive(Debug)]
pub struct RegionCtx<'a, F: PrimeField> {
    region: Region<'a, F>,
    offset: usize,
}

impl<'a, F:PrimeField> RegionCtx<'a, F> {
    pub fn new(region: Region<'a, F>, offset: usize) -> Self {
        RegionCtx {
            region,
            offset,
        }
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn into_region(self) -> Region<'a, F> {
        self.region
    }

     pub fn assign_fixed<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Fixed>,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region
            .assign_fixed(annotation, column, self.offset, || Value::known(value))
    }

    pub fn assign_advice<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region
            .assign_advice(annotation, column, self.offset, || value)
    }

    pub fn constrain_equal(&mut self, cell_0: Cell, cell_1: Cell) -> Result<(), Error> {
        self.region.constrain_equal(cell_0, cell_1)
    }

    pub fn next(&mut self) {
        self.offset += 1
    }
}

#[derive(Debug, Clone)]
pub struct StandardGateConfig {
    pub(crate) a: Column<Advice>,
    pub(crate) b: Column<Advice>,
    pub(crate) c: Column<Advice>,

    pub(crate) sa: Column<Fixed>,
    pub(crate) sb: Column<Fixed>,
    pub(crate) sc: Column<Fixed>,
    pub(crate) s_mul: Column<Fixed>,
    pub(crate) s_const: Column<Fixed>,
    pub(crate) instance: Column<Instance>,
}

#[derive(Debug, Clone)]
pub struct StandardGate<F: PrimeField> {
    config: StandardGateConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Chip<F> for StandardGate<F> {
    type Config = StandardGateConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> StandardGate<F> {
    pub fn new(config: StandardGateConfig) -> Self {
        StandardGate {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> StandardGateConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();
        let s_mul = meta.fixed_column();
        let s_const = meta.fixed_column();

        let instance = meta.instance_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(instance);

        meta.create_gate("s_a·a + s_b·b + s_c·c + s_mul·a·b + s_const = 0", |meta|{
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let sa = meta.query_fixed(sa);
            let sb = meta.query_fixed(sb);
            let sc = meta.query_fixed(sc);
            let s_mul = meta.query_fixed(s_mul);
            let s_const = meta.query_fixed(s_const);
            let instance = meta.query_instance(instance, Rotation::cur());
            vec![sa*a.clone()+sb*b.clone()+sc*c.clone()+s_mul*a*b+s_const]
        });

        StandardGateConfig { a, b, c, sa, sb, sc, s_mul, s_const, instance }

    }

    pub fn add(&self, ctx: &mut RegionCtx<'_, F>, a: Value<F>, b: Value<F>) -> Result<Vec<AssignedCell<F,F>>,Error> {
        ctx.assign_fixed(||"sa", self.config.sa, F::ONE)?;
        ctx.assign_fixed(||"sb", self.config.sb, F::ONE)?;
        ctx.assign_fixed(||"sc", self.config.sc, F::ONE.neg())?;

        let a_cell = ctx.assign_advice(||"a", self.config.a, a)?;
        let b_cell = ctx.assign_advice(||"b", self.config.b, b)?;
        let c = a + b;
        let c_cell = ctx.assign_advice(||"c", self.config.c, c)?;

        ctx.next();
        Ok(vec![a_cell, b_cell, c_cell])
    }

    pub fn mul(&self, ctx: &mut RegionCtx<'_, F>, a: Value<F>, b: Value<F>) -> Result<AssignedCell<F,F>, Error> {
        ctx.assign_fixed(||"sc", self.config.sb, F::ONE.neg())?;
        ctx.assign_fixed(||"s_mul", self.config.s_mul, F::ONE)?;

        ctx.assign_advice(||"a", self.config.a, a)?;
        ctx.assign_advice(||"b", self.config.b, b)?;
        let c = a * b;
        let c_cell = ctx.assign_advice(||"c", self.config.c, c)?;

        ctx.next();
        Ok(c_cell)
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        value: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(value.cell(), config.instance, row)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{plonk::Circuit, circuit::{SimpleFloorPlanner, Layouter}, pasta::Fp};

    #[derive(Clone)]
    struct FibonacciCircuitConfig {
        config: StandardGateConfig,
    }

    impl FibonacciCircuitConfig {
        fn standard_gate<F: PrimeField>(&self) -> StandardGate<F> {
            StandardGate::new(self.config.clone())
        }
    }
    
    #[derive(Default)]
    struct FibonacciCircuit<F: PrimeField> {
        x0: F,
        y0: F,
        x1: F,
        y1: F,
    }

    impl<F: PrimeField> FibonacciCircuit<F> {
        pub fn new(x0: u32, y0: u32) -> Self {
            FibonacciCircuit { 
                x0: F::from(x0 as u64),
                y0: F::from(y0 as u64),
                x1: F::from(y0 as u64),
                y1: F::from(x0 as u64 + y0 as u64),
            }
        }
    }

    impl<F: PrimeField> Circuit<F> for FibonacciCircuit<F> {
        type Config = FibonacciCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let config = StandardGate::<F>::configure(meta);
            FibonacciCircuitConfig { config }
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
            let standard_gate = config.standard_gate();
            let vs = layouter.assign_region(||"region 0", |region|{
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);
                let x0 = Value::known(self.x0);
                let y0 = Value::known(self.y0);
                standard_gate.add(ctx, x0, y0)
            })?;
            standard_gate.expose_public(layouter.namespace(||"y0"), vs[1].clone(), 0)?;
            standard_gate.expose_public(layouter.namespace(||"y1"), vs[2].clone(), 1)?;
            Ok(())
        }
    }

    #[test]
    fn test_fibonacci() {
        use halo2_proofs::pasta::Fp;
        use halo2_proofs::dev::MockProver;
        const K:u32 = 8;
        let x0 = 2;
        let y0 = 3;
        let circuit = FibonacciCircuit::<Fp>::new(x0, y0);
        let public_inputs = vec![vec![circuit.x1, circuit.y1]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

}
