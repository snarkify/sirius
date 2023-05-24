use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Cell, Chip, Region, Value, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Fixed, Instance, Error}, 
    poly::Rotation};
use ff::PrimeField;

#[derive(Debug)]
pub struct RegionCtx<'a, F: PrimeField> {
    pub region: Region<'a, F>,
    pub offset: usize,
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

    pub(crate) fn reset(&mut self, offset: usize) {
        self.offset = offset
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

            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let s_mul = meta.query_fixed(s_mul, Rotation::cur());
            let s_const = meta.query_fixed(s_const, Rotation::cur());
            // let instance = meta.query_instance(instance, Rotation::cur());
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

    pub fn expose_public(
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
    use crate::polynomial::Expression;
    // use pasta_curves::Fp;
    use halo2curves::pasta::Fp;

    fn standard_gate_expressions() -> (Vec<Vec<Expression<Fp>>>,(usize,usize,usize)) {
        let mut cs = ConstraintSystem::<Fp>::default();
        let _ = StandardGate::<Fp>::configure(&mut cs);
        let num_fixed = cs.num_fixed_columns();
        let num_instance = cs.num_instance_columns();
        let num_advice = cs.num_advice_columns();
        let gates: Vec<Vec<Expression<Fp>>> = cs.gates().iter().map(|gate| {
            gate.polynomials().iter().map(|expr| Expression::from_halo2_expr(expr, (num_fixed, num_instance))).collect()
        }).collect();
        (gates, (num_fixed, num_instance, num_advice))
    }

    #[test]
    fn test_standard_gate_expr() {
        let (gates, _) = standard_gate_expressions();
        for (i, gate) in gates.iter().enumerate() {
            for (j, poly) in gate.iter().enumerate() {
                if i == 0 && j == 0 {
                    // i.e. (((((ql * a1) + (qr * b1)) + (qo * c1)) + ((qm * a1) * b1)) + qc)
                    assert_eq!(format!("{}", poly), "(((((Z_0 * Z_6) + (Z_1 * Z_7)) + (Z_2 * Z_8)) + ((Z_3 * Z_6) * Z_7)) + Z_4)");
                }
            }
        }
    }

    #[test]
    fn test_standard_gate_cross_term() {
        let (gates, meta) = standard_gate_expressions();
        let expr = gates[0][0].clone();
        let multipoly = expr.expand();
        let res = multipoly.fold_transform(meta);
        let r_index = meta.0 + 2*(meta.1+meta.2+1);
        let r0 = res.coeff_of((0, r_index), 0);
        let r1 = res.coeff_of((0,r_index), 1);
        let r2 = res.coeff_of((0, r_index), 2);
        // coeff of r^0: (qm)(a1)(b1) + (ql)(a1)(u1) + (qr)(b1)(u1) + (qo)(c1)(u1) + (qc)(u1^2)
        assert_eq!(format!("{}", r0), "(Z_3)(Z_6)(Z_7) + (Z_0)(Z_6)(Z_9) + (Z_1)(Z_7)(Z_9) + (Z_2)(Z_8)(Z_9) + (Z_4)(Z_9^2)");
        // coeff of r^1: (qm)(b1)(a2) + (ql)(u1)(a2) + (qm)(a1)(b2) + (qr)(u1)(b2) + (qo)(u1)(c2) + (ql)(a1)(u2) + (qr)(b1)(u2) + (qo)(c1)(u2) + 0x2(qc)(u1)(u2)
        assert_eq!(format!("{}", r1), "(Z_3)(Z_7)(Z_11) + (Z_0)(Z_9)(Z_11) + (Z_3)(Z_6)(Z_12) + (Z_1)(Z_9)(Z_12) + (Z_2)(Z_9)(Z_13) + (Z_0)(Z_6)(Z_14) + (Z_1)(Z_7)(Z_14) + (Z_2)(Z_8)(Z_14) + 0x2(Z_4)(Z_9)(Z_14)");
        // coeff of r^2: (qm)(a2)(b2) + (ql)(a2)(u2) + (qr)(b2)(u2) + (qo)(c2)(u2) + (qc)(u2^2)
        assert_eq!(format!("{}", r2), "(Z_3)(Z_11)(Z_12) + (Z_0)(Z_11)(Z_14) + (Z_1)(Z_12)(Z_14) + (Z_2)(Z_13)(Z_14) + (Z_4)(Z_14^2)");
    }
}
