use crate::util::normalize_trailing_zeros;
use ff::{PrimeField, PrimeFieldBits};
use halo2_proofs::{
    circuit::{AssignedCell, Cell, Chip, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Instance},
    poly::Rotation,
};
use std::{array, marker::PhantomData};

pub type AssignedValue<F> = AssignedCell<F, F>;
pub type AssignedBit<F> = AssignedCell<F, F>;

#[derive(Debug)]
pub struct RegionCtx<'a, F: PrimeField> {
    pub region: Region<'a, F>,
    pub offset: usize,
}

impl<'a, F: PrimeField> RegionCtx<'a, F> {
    pub fn new(region: Region<'a, F>, offset: usize) -> Self {
        RegionCtx { region, offset }
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
    ) -> Result<AssignedValue<F>, Error>
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
    ) -> Result<AssignedValue<F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region
            .assign_advice(annotation, column, self.offset, || value)
    }

    pub fn assign_advice_from<A, AR>(
        &mut self,
        annotation: A,
        dst: Column<Advice>,
        src: impl AssignAdviceFrom<'a, F>,
    ) -> Result<AssignedCell<F, F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        AssignAdviceFrom::assign_advice_from(self, annotation, dst, src)
    }

    pub fn assign_advice_from_instance<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        instance: Column<Instance>,
        instance_offset: usize,
    ) -> Result<AssignedValue<F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region.assign_advice_from_instance(
            annotation,
            instance,
            instance_offset,
            column,
            self.offset,
        )
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

mod assign_advice_from {
    use super::*;

    pub trait AssignAdviceFrom<'a, F: PrimeField> {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>;
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for &AssignedCell<F, F> {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            let cell = ctx.assign_advice(annotation, dst, src.value().map(|f| *f))?;
            ctx.constrain_equal(cell.cell(), src.cell())?;
            Ok(cell)
        }
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for AssignedCell<F, F> {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            AssignAdviceFrom::assign_advice_from(ctx, annotation, dst, &src)
        }
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for &F {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            AssignAdviceFrom::assign_advice_from(ctx, annotation, dst, *src)
        }
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for F {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            let cell = ctx.assign_advice(annotation, dst, Value::known(src))?;
            Ok(cell)
        }
    }
}
pub use assign_advice_from::AssignAdviceFrom;

#[derive(Clone, Debug)]
pub enum WrapValue<F: PrimeField> {
    Assigned(AssignedValue<F>),
    Unassigned(Value<F>),
    Zero,
}

impl<F: PrimeField> WrapValue<F> {
    pub fn value(&self) -> Value<F> {
        match self {
            WrapValue::Assigned(v) => v.value().copied(),
            WrapValue::Unassigned(v) => *v,
            WrapValue::Zero => Value::known(F::ZERO),
        }
    }
}

impl<F: PrimeField> From<Value<F>> for WrapValue<F> {
    fn from(val: Value<F>) -> Self {
        WrapValue::Unassigned(val)
    }
}

impl<F: PrimeField> From<AssignedValue<F>> for WrapValue<F> {
    fn from(val: AssignedValue<F>) -> Self {
        WrapValue::Assigned(val)
    }
}

impl<F: PrimeField> From<F> for WrapValue<F> {
    fn from(val: F) -> Self {
        WrapValue::Unassigned(Value::known(val))
    }
}

impl<F: PrimeField> From<&AssignedValue<F>> for WrapValue<F> {
    fn from(val: &AssignedValue<F>) -> Self {
        WrapValue::Assigned(val.clone())
    }
}

#[derive(Clone, Debug)]
pub struct MainGateConfig<const T: usize> {
    pub(crate) state: [Column<Advice>; T],
    pub(crate) input: Column<Advice>,
    pub(crate) out: Column<Advice>,
    pub(crate) q_m: Column<Fixed>,
    // for linear term
    pub(crate) q_1: [Column<Fixed>; T],
    // for quintic term
    pub(crate) q_5: [Column<Fixed>; T],
    pub(crate) q_i: Column<Fixed>,
    pub(crate) q_o: Column<Fixed>,
    pub(crate) rc: Column<Fixed>,
}

impl<const T: usize> MainGateConfig<T> {
    pub fn name_columns<F: PrimeField>(&self, region: &mut Region<'_, F>) {
        for i in 0..T {
            region.name_column(|| format!("state[{i}]"), self.state[i]);
            region.name_column(|| format!("q_1[{i}]"), self.q_1[i]);
            region.name_column(|| format!("q_5[{i}]"), self.q_5[i]);
        }
        region.name_column(|| "input", self.input);
        region.name_column(|| "out", self.out);
        region.name_column(|| "q_i", self.q_i);
        region.name_column(|| "q_o", self.q_o);
        region.name_column(|| "q_m", self.q_m);
        region.name_column(|| "rc", self.rc);
    }

    /// Converts the current `MainGateConfig` to a new configuration with a smaller size `N`.
    ///
    /// This method is used to adapt the main gate configuration of a circuit to a different size,
    /// which can be necessary for various circuit optimizations or specific implementations.
    /// It attempts to reconfigure the existing columns and constants to match the new size
    /// while preserving the original configuration's structure and values.
    ///
    /// # Type Parameters
    ///
    /// * `N`: The new, smaller size for the main gate configuration. This determines the number
    ///   of columns and constants in the resized configuration. `N` must be less than or equal
    ///   to `T`.
    ///
    /// # Returns
    ///
    /// If `N > T` return `None`
    /// If `N <= T` return `Some(MainGateConfig<N>)`
    pub fn into_smaller_size<const N: usize>(&self) -> Option<MainGateConfig<N>> {
        Some(MainGateConfig {
            state: self.state.clone().as_slice().try_into().ok()?,
            input: self.input,
            out: self.out,
            q_m: self.q_m,
            q_1: self.q_1.clone().as_slice().try_into().ok()?,
            q_5: self.q_5.clone().as_slice().try_into().ok()?,
            q_i: self.q_i,
            q_o: self.q_o,
            rc: self.rc,
        })
    }
}

#[derive(Debug)]
pub struct MainGate<F: PrimeField, const T: usize> {
    config: MainGateConfig<T>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField, const T: usize> Chip<F> for MainGate<F, T> {
    type Config = MainGateConfig<T>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField, const T: usize> MainGate<F, T> {
    pub fn new(config: MainGateConfig<T>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MainGateConfig<T> {
        assert!(T >= 2);
        let state = array::from_fn(|_| meta.advice_column());
        let input = meta.advice_column();
        let out = meta.advice_column();
        let q_1 = array::from_fn(|_| meta.fixed_column());
        let q_5 = array::from_fn(|_| meta.fixed_column());
        let q_m = meta.fixed_column();
        let q_i = meta.fixed_column();
        let q_o = meta.fixed_column();
        let rc = meta.fixed_column();

        state.map(|s| {
            meta.enable_equality(s);
        });
        meta.enable_equality(input);
        meta.enable_equality(out);

        let pow_5 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2 * v
        };

        meta.create_gate("q_m*s[0]*s[1] + sum_i(q_1[i]*s[i]) + sum_i(q_5[i]*s[i]^5) + rc + q_i*input + q_o*out=0", |meta|{
            let state = state.into_iter().map(|s| meta.query_advice(s, Rotation::cur())).collect::<Vec<_>>();
            let input = meta.query_advice(input, Rotation::cur());
            let out = meta.query_advice(out, Rotation::cur());
            let q_1 = q_1.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_5 = q_5.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_m = meta.query_fixed(q_m, Rotation::cur());
            let q_i = meta.query_fixed(q_i, Rotation::cur());
            let q_o = meta.query_fixed(q_o, Rotation::cur());
            let rc = meta.query_fixed(rc, Rotation::cur());

            let init_term = q_m * state[0].clone() * state[1].clone() + q_i * input + rc + q_o * out;

            let res = state
                .into_iter()
                .zip(q_1)
                .zip(q_5)
                .map(|((s, q1), q5)| {
                    q1 * s.clone()  +  q5 * pow_5(s)
                })
                .fold(init_term, |acc, item| {
                    acc + item
                });

            vec![res]
        });

        MainGateConfig {
            state,
            input,
            out,
            q_m,
            q_1,
            q_5,
            q_i,
            q_o,
            rc,
        }
    }

    // helper function for some usecases: no copy constraints, only return out cell
    // state: (q_1, q_m, state), out: (q_o, out)
    pub fn apply(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: (Option<Vec<F>>, Option<F>, Option<Vec<WrapValue<F>>>),
        rc: Option<F>,
        out: (F, WrapValue<F>),
    ) -> Result<AssignedValue<F>, Error> {
        if let Some(q_1) = state.0 {
            for (i, val) in q_1.iter().enumerate() {
                ctx.assign_fixed(|| "q_1", self.config.q_1[i], *val)?;
            }
        }
        if let Some(q_m_val) = state.1 {
            ctx.assign_fixed(|| "q_m", self.config.q_m, q_m_val)?;
        }
        if let Some(state) = state.2 {
            for (i, val) in state.iter().enumerate() {
                match val {
                    WrapValue::Unassigned(vv) => {
                        ctx.assign_advice(|| "state", self.config.state[i], *vv)?;
                    }
                    WrapValue::Assigned(avv) => {
                        let si = ctx.assign_advice(
                            || "state",
                            self.config.state[i],
                            avv.value().copied(),
                        )?;
                        ctx.constrain_equal(si.cell(), avv.cell())?;
                    }
                    _ => {}
                }
            }
        }

        if let Some(rc_val) = rc {
            ctx.assign_fixed(|| "rc", self.config.rc, rc_val)?;
        }

        ctx.assign_fixed(|| "q_o", self.config.q_o, out.0)?;

        let res = match out.1 {
            WrapValue::Unassigned(vv) => ctx.assign_advice(|| "out", self.config.out, vv)?,
            WrapValue::Assigned(avv) => {
                let out = ctx.assign_advice(|| "out", self.config.out, avv.value().copied())?;
                ctx.constrain_equal(out.cell(), avv.cell())?;
                out
            }
            WrapValue::Zero => {
                unimplemented!() // this is not allowed
            }
        };
        ctx.next();
        Ok(res)
    }

    pub fn apply_with_input(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: (Option<Vec<F>>, Option<F>, Option<Vec<WrapValue<F>>>),
        input: (Option<F>, Option<WrapValue<F>>),
        out: (F, WrapValue<F>),
    ) -> Result<AssignedValue<F>, Error> {
        if let Some(q_1) = state.0 {
            for (i, val) in q_1.iter().enumerate() {
                ctx.assign_fixed(|| "q_1", self.config.q_1[i], *val)?;
            }
        }
        if let Some(q_m_val) = state.1 {
            ctx.assign_fixed(|| "q_m", self.config.q_m, q_m_val)?;
        }
        if let Some(state) = state.2 {
            for (i, val) in state.iter().enumerate() {
                match val {
                    WrapValue::Unassigned(vv) => {
                        ctx.assign_advice(|| "state", self.config.state[i], *vv)?;
                    }
                    WrapValue::Assigned(avv) => {
                        let si = ctx.assign_advice(
                            || "state",
                            self.config.state[i],
                            avv.value().copied(),
                        )?;
                        ctx.constrain_equal(si.cell(), avv.cell())?;
                    }
                    _ => {}
                }
            }
        }

        if let Some(q_i) = input.0 {
            ctx.assign_fixed(|| "rc", self.config.q_i, q_i)?;
        }
        if let Some(inp) = input.1 {
            match inp {
                WrapValue::Unassigned(vv) => {
                    ctx.assign_advice(|| "input", self.config.input, vv)?;
                }
                WrapValue::Assigned(avv) => {
                    let si =
                        ctx.assign_advice(|| "input", self.config.input, avv.value().copied())?;
                    ctx.constrain_equal(si.cell(), avv.cell())?;
                }
                _ => {}
            }
        }

        ctx.assign_fixed(|| "q_o", self.config.q_o, out.0)?;

        let res = match out.1 {
            WrapValue::Unassigned(vv) => ctx.assign_advice(|| "out", self.config.out, vv)?,
            WrapValue::Assigned(avv) => {
                let out = ctx.assign_advice(|| "out", self.config.out, avv.value().copied())?;
                ctx.constrain_equal(out.cell(), avv.cell())?;
                out
            }
            WrapValue::Zero => {
                unimplemented!() // this is not allowed
            }
        };
        ctx.next();
        Ok(res)
    }

    // calculate sum_{i=0}^d r^i terms[i]
    pub fn random_linear_combination(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        terms: Vec<F>,
        r: F,
    ) -> Result<AssignedValue<F>, Error> {
        let d = terms.len();
        let mut out: Option<AssignedValue<F>> = None;
        for i in 1..d {
            let lhs_val = Value::known(terms[d - 1 - i]);
            let rhs_val = if i == 1 {
                Value::known(terms[d - i])
            } else {
                out.as_ref().unwrap().value().copied()
            };
            let r_val = Value::known(r);
            ctx.assign_advice(|| "input", self.config.input, lhs_val)?;
            let rhs = ctx.assign_advice(|| "s[1]", self.config.state[1], rhs_val)?;
            if out.is_some() {
                ctx.constrain_equal(rhs.cell(), out.unwrap().cell())?;
            }
            ctx.assign_advice(|| "s[0]", self.config.state[0], r_val)?;
            out = Some(ctx.assign_advice(
                || "out=s[0]*s[1]+input",
                self.config.out,
                lhs_val + r_val * rhs_val,
            )?);

            ctx.assign_fixed(|| "q_i", self.config.q_i, F::ONE)?;
            ctx.assign_fixed(|| "q_m", self.config.q_m, F::ONE)?;
            ctx.assign_fixed(|| "q_o", self.config.q_o, -F::ONE)?;
            ctx.next();
        }
        Ok(out.unwrap())
    }
}

impl<F: PrimeFieldBits, const T: usize> MainGate<F, T> {
    pub fn assign_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &[bool],
    ) -> Result<Vec<AssignedValue<F>>, Error> {
        let mut res = vec![];
        for bit in bits.iter() {
            if *bit {
                let tmp = self.assign_bit(ctx, Value::known(F::ONE))?;
                res.push(tmp);
            } else {
                let tmp = self.assign_bit(ctx, Value::known(F::ZERO))?;
                res.push(tmp);
            }
        }
        Ok(res)
    }

    pub fn le_bits_to_num(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &Vec<AssignedValue<F>>,
    ) -> Result<AssignedValue<F>, Error> {
        let accumulate = |acc: &mut Value<F>, bs: Vec<AssignedValue<F>>, ps: &Vec<F>| {
            for (b, p) in bs.iter().zip(ps) {
                *acc = *acc + b.value().copied() * Value::known(p);
            }
        };
        let length = bits.len();
        let mut mult = F::ONE;
        let powers: Vec<F> = (0..length)
            .map(|_| {
                let pow = mult;
                mult = mult + mult;
                pow
            })
            .collect();
        let mut acc = Value::known(F::ZERO);
        let mut old_acc = self.assign_value(ctx, acc)?;
        for (bs, ps) in bits.chunks(T).zip(powers.chunks(T)) {
            let bvs = bs.to_vec();
            let pvs = ps.to_vec();
            accumulate(&mut acc, bvs, &pvs);
            let state = bs.to_vec().iter().map(|bit| bit.into()).collect::<Vec<_>>();
            let state_terms = (Some(pvs), None, Some(state));
            old_acc = self.apply_with_input(
                ctx,
                state_terms,
                (Some(F::ONE), Some(old_acc.into())),
                (-F::ONE, acc.into()),
            )?;
        }
        Ok(old_acc)
    }
    pub fn le_num_to_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedValue<F>,
        bit_len: usize,
    ) -> Result<Vec<AssignedValue<F>>, Error> {
        // TODO: ensure a is less than F.size() - 1
        let mut length = 0;
        let bits: Vec<Value<bool>> = a
            .value()
            .map(|a| {
                let bits = a.to_le_bits();
                length = bits.len();
                bits
            })
            .transpose_vec(length);
        let mut bits = bits
            .iter()
            .map(|bit| bit.unwrap().unwrap())
            .collect::<Vec<_>>();
        normalize_trailing_zeros(&mut bits, bit_len);
        let bits = self.assign_bits(ctx, &bits)?;
        let num = self.le_bits_to_num(ctx, &bits)?;
        assert_eq!(num.value().unwrap(), a.value().unwrap());
        ctx.constrain_equal(a.cell(), num.cell())?;
        Ok(bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::Expression;
    // use pasta_curves::Fp;
    use halo2curves::pasta::Fp;

    fn main_gate_expressions() -> (Vec<Vec<Expression<Fp>>>, (usize, usize, usize)) {
        const T: usize = 2;
        const RATE: usize = 2;
        let mut cs = ConstraintSystem::<Fp>::default();
        let _: MainGateConfig<T> = MainGate::configure(&mut cs);
        let num_selector = cs.num_selectors(); // is zero for current main_gate design
        let num_fixed = cs.num_fixed_columns();
        let num_instance = cs.num_instance_columns();
        let num_advice = cs.num_advice_columns();
        let gates: Vec<Vec<Expression<Fp>>> = cs
            .gates()
            .iter()
            .map(|gate| {
                gate.polynomials()
                    .iter()
                    .map(|expr| Expression::from_halo2_expr(expr, num_selector, num_fixed))
                    .collect()
            })
            .collect();
        (gates, (num_fixed, num_instance, num_advice))
    }

    #[test]
    fn test_main_gate_expr() {
        let (gates, _) = main_gate_expressions();
        for (i, gate) in gates.iter().enumerate() {
            for (j, poly) in gate.iter().enumerate() {
                if i == 0 && j == 0 {
                    // i.e. qm * s1_0 * s1_1 + qi * in1 + rc + qo * out1 + q1_0 * s1_0 + q5_0 * s1_0^5
                    // + q1_1 * s1_1 + q5_1 * s1_1^5
                    assert_eq!(format!("{}", poly), "(((((((Z_4 * Z_8) * Z_9) + (Z_5 * Z_10)) + Z_7) + (Z_6 * Z_11)) + ((Z_0 * Z_8) + (Z_2 * (((Z_8 * Z_8) * (Z_8 * Z_8)) * Z_8)))) + ((Z_1 * Z_9) + (Z_3 * (((Z_9 * Z_9) * (Z_9 * Z_9)) * Z_9))))");
                }
            }
        }
    }

    #[test]
    fn test_main_gate_cross_term() {
        let (gates, meta) = main_gate_expressions();
        let expr = gates[0][0].clone();
        let multipoly = expr.expand();
        let num_fixed = meta.0;
        let num_vars = meta.1 + meta.2;
        let res = multipoly.fold_transform(num_fixed, num_vars);
        let r_index = meta.0 + 2 * (meta.1 + meta.2 + 1);
        let e1 = res.coeff_of((0, r_index), 0);
        let e2 = res.coeff_of((0, r_index), 5);
        // E1: (q5_0)(s1_0^5) + (q5_1)(s1_1^5) + (qm)(s1_0)(s1_1)(u1^3) + (q1_0)(s1_0)(u1^4) + (q1_1)(s1_1)(u1^4) + (qi)(in1)(u1^4) + (qo)(out1)(u1^4) + (rc)(u1^5)
        assert_eq!(format!("{}", e1), "(Z_2)(Z_8^5) + (Z_3)(Z_9^5) + (Z_4)(Z_8)(Z_9)(Z_12^3) + (Z_0)(Z_8)(Z_12^4) + (Z_1)(Z_9)(Z_12^4) + (Z_5)(Z_10)(Z_12^4) + (Z_6)(Z_11)(Z_12^4) + (Z_7)(Z_12^5)");
        // E2: (q5_0)(s2_0^5) + (q5_1)(s2_1^5) + (qm)(s2_0)(s2_1)(u2^3) + (q1_0)(s2_0)(u2^4) + (q1_1)(s2_1)(u2^4) + (qi)(in2)(u2^4) + (qo)(out2)(u2^4) + (rc)(u2^5)
        assert_eq!(format!("{}", e2), "(Z_2)(Z_13^5) + (Z_3)(Z_14^5) + (Z_4)(Z_13)(Z_14)(Z_17^3) + (Z_0)(Z_13)(Z_17^4) + (Z_1)(Z_14)(Z_17^4) + (Z_5)(Z_15)(Z_17^4) + (Z_6)(Z_16)(Z_17^4) + (Z_7)(Z_17^5)");
    }
}
