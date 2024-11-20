use std::{array, marker::PhantomData, num::NonZeroUsize};

use halo2_proofs::plonk::Selector;
use itertools::Itertools;
use tracing::{error, instrument};

use crate::{
    gadgets::ecc::{AssignedPoint, EccGate},
    halo2_proofs::{
        circuit::{Chip, Value},
        halo2curves::{
            ff::{PrimeField, PrimeFieldBits},
            CurveAffine,
        },
        plonk::{Advice, Column, ConstraintSystem, Error as Halo2PlonkError, Fixed, Instance},
        poly::Rotation,
    },
    main_gate::{AssignAdviceFrom, AssignedValue, RegionCtx},
    util,
};

#[derive(Clone, Debug)]
pub struct Config {
    s: Selector,
    pub(crate) state: [Column<Advice>; 2],
    mul: Column<Fixed>,
    sum: [Column<Fixed>; 2],
    pub(crate) output: Column<Advice>,
    rc: Column<Fixed>,
}

pub struct Gate<F: PrimeField> {
    config: Config,
    _p: PhantomData<F>,
}

impl<F: PrimeField> Gate<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Config {
        let config = Config {
            state: array::from_fn(|_| {
                let c = meta.advice_column();
                meta.enable_equality(c);
                c
            }),
            mul: meta.fixed_column(),
            sum: array::from_fn(|_| meta.fixed_column()),
            output: {
                let c = meta.advice_column();
                meta.enable_equality(c);
                c
            },
            rc: meta.fixed_column(),
            s: meta.selector(),
        };

        meta.create_gate(
            "s[0] * s[1] * mul + s[0] * sum[0] + s[1] * sum[1] + rc - output = 0",
            |meta| {
                let Config {
                    s,
                    state,
                    mul,
                    sum,
                    output,
                    rc,
                } = config.clone();

                let s = meta.query_selector(s);
                let [state0, state1] = state.map(|c| meta.query_advice(c, Rotation::cur()));
                let mul = meta.query_fixed(mul, Rotation::cur());
                let [sum0, sum1] = sum.map(|c| meta.query_fixed(c, Rotation::cur()));
                let output = meta.query_advice(output, Rotation::cur());
                let rc = meta.query_fixed(rc, Rotation::cur());

                [s * ((state0.clone() * state1.clone() * mul)
                    + (state0 * sum0)
                    + (state1 * sum1)
                    + rc
                    - output)]
            },
        );

        config
    }

    fn mul<'a>(
        &self,
        ctx: &mut RegionCtx<'a, F>,
        lhs: impl AssignAdviceFrom<'a, F>,
        rhs: impl AssignAdviceFrom<'a, F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let Config {
            s,
            state: [state0, state1],
            mul,
            output,
            sum: [sum0, sum1],
            rc,
        } = self.config();

        ctx.enable_selector(s)?;
        ctx.assign_fixed(|| "one", *mul, F::ONE)?;
        let l = ctx.assign_advice_from(|| "mul.lhs", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "mul.rhs", *state1, rhs)?;

        let res = ctx.assign_advice(|| "mul.out", *output, l.value().copied() * r.value());

        ctx.assign_fixed(|| "one", *sum0, F::ZERO)?;
        ctx.assign_fixed(|| "one", *sum1, F::ZERO)?;
        ctx.assign_fixed(|| "one", *rc, F::ZERO)?;

        ctx.next();

        res
    }

    fn add_with_const(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        lhs_coeff: &F,
        rhs: &F,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let Config {
            s,
            state: [state0, state1],
            sum: [sum0, sum1],
            output,
            rc,
            mul,
        } = self.config();

        ctx.enable_selector(s)?;
        ctx.assign_fixed(|| "add_with_const.lhs_coeff", *sum0, *lhs_coeff)?;

        let l = ctx.assign_advice_from(|| "add_with_const.lhs", *state0, lhs)?;
        let r = ctx.assign_fixed(|| "add_with_const.rc", *rc, *rhs)?;

        let res = ctx.assign_advice(
            || "add_with_const.out",
            *output,
            l.value().copied() + r.value(),
        );

        ctx.assign_fixed(|| "", *mul, F::ZERO)?;
        ctx.assign_fixed(|| "", *sum1, F::ZERO)?;
        ctx.assign_advice(|| "", *state1, Value::known(F::ZERO))?;

        ctx.next();

        res
    }

    fn add(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let Config {
            s,
            state: [state0, state1],
            sum: [sum0, sum1],
            output,
            mul,
            rc,
        } = self.config();

        ctx.enable_selector(s)?;
        ctx.assign_fixed(|| "add.sum0", *sum0, F::ONE)?;
        ctx.assign_fixed(|| "add.sum1", *sum1, F::ONE)?;

        let l = ctx.assign_advice_from(|| "add.lhs", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "add.rhs", *state1, rhs)?;

        let res = ctx.assign_advice(|| "add.out", *output, l.value().copied() + r.value());

        ctx.assign_fixed(|| "", *mul, F::ZERO)?;
        ctx.assign_fixed(|| "", *rc, F::ZERO)?;

        ctx.next();

        res
    }

    fn sub(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let Config {
            s,
            state: [state0, state1],
            sum: [sum0, sum1],
            output,
            mul,
            rc,
        } = self.config();

        ctx.enable_selector(s)?;
        ctx.assign_fixed(|| "sub.sum0", *sum0, F::ONE)?;
        ctx.assign_fixed(|| "sub.sum1", *sum1, -F::ONE)?;

        let l = ctx.assign_advice_from(|| "sub.lhs", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "sub.rhs", *state1, rhs)?;

        let res = ctx.assign_advice(|| "sub.out", *output, l.value().copied() - r.value());

        ctx.assign_fixed(|| "", *mul, F::ZERO)?;
        ctx.assign_fixed(|| "", *rc, F::ZERO)?;

        ctx.next();

        res
    }

    fn check_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        value: &AssignedValue<F>,
    ) -> Result<(), Halo2PlonkError> {
        let Config {
            s,
            state: [state0, state1],
            sum: [sum0, sum1],
            output,
            mul,
            rc,
        } = self.config();

        ctx.enable_selector(s)?;
        ctx.assign_advice_from(|| "check_zero.state0", *state0, value)?;
        ctx.assign_fixed(|| "check_zero.sum0", *sum0, F::ONE)?;

        ctx.assign_advice(|| "", *state1, Value::known(F::ZERO))?;
        ctx.assign_advice(|| "", *output, Value::known(F::ZERO))?;
        ctx.assign_fixed(|| "", *sum1, F::ZERO)?;
        ctx.assign_fixed(|| "", *mul, F::ZERO)?;
        ctx.assign_fixed(|| "", *rc, F::ZERO)?;

        ctx.next();

        Ok(())
    }

    fn is_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        value: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        Ok(self.invert_with_flag(ctx, value)?.0)
    }

    pub fn assign_values<'a, const L: usize>(
        &self,
        ctx: &mut RegionCtx<'a, F>,
        values: &[impl Clone + AssignAdviceFrom<'a, F>; L],
    ) -> Result<[AssignedValue<F>; L], Halo2PlonkError> {
        let mut advice = self.config().state.to_vec();
        advice.push(self.config().output);

        let mut result = Vec::with_capacity(values.len());
        for chunk in values.chunks(advice.len()) {
            for (value, col) in chunk.iter().zip(advice.iter()) {
                result.push(ctx.assign_advice_from(|| "assign_value.val", *col, value.clone())?);
            }
            ctx.next();
        }

        Ok(result.try_into().unwrap())
    }

    pub fn assign_values_from_instance<const L: usize>(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        instance: Column<Instance>,
        offset: usize,
    ) -> Result<[AssignedValue<F>; L], Halo2PlonkError> {
        let mut advice = self.config().state.to_vec();
        advice.push(self.config().output);

        let mut result = Vec::with_capacity(L);
        for chunk in &(0..L).chunks(advice.len()) {
            for (intance_row, col) in chunk.zip(advice.iter()) {
                result.push(ctx.assign_advice_from_instance(
                    || "assign_value.val",
                    *col,
                    instance,
                    offset + intance_row,
                )?);
            }
            ctx.next();
        }

        Ok(result.try_into().unwrap())
    }

    fn assign_bit<'a>(
        &self,
        ctx: &mut RegionCtx<'a, F>,
        a: impl AssignAdviceFrom<'a, F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let Config {
            s,
            state: [state0, state1],
            mul,
            output,
            sum: [sum0, sum1],
            rc,
        } = self.config();

        ctx.enable_selector(s)?;

        // s0*s1 - out = 0
        let a = ctx.assign_advice_from(|| "bit", *state0, a)?;
        ctx.assign_advice_from(|| "bit", *state1, &a)?;
        ctx.assign_fixed(|| "one", *mul, F::ONE)?;

        let out = ctx.assign_advice_from(|| "bit", *output, &a)?;

        ctx.assign_fixed(|| "one", *sum0, F::ZERO)?;
        ctx.assign_fixed(|| "one", *sum1, F::ZERO)?;
        ctx.assign_fixed(|| "one", *rc, F::ZERO)?;

        ctx.next();
        Ok(out)
    }

    fn invert_with_flag(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<(AssignedValue<F>, AssignedValue<F>), Halo2PlonkError> {
        let a_inv = a.value().unwrap().and_then(|v| v.invert().into());

        let is_zero = self.assign_bit(ctx, if a_inv.is_some() { F::ZERO } else { F::ONE })?;
        let [a_inv] = self.assign_values(ctx, &[a_inv.unwrap_or(F::ONE)])?;

        // a * a' = 1 - r
        let left = self.mul(ctx, a, &a_inv)?.cell();
        let right = self
            .add_with_const(ctx, &is_zero, &-F::ONE, &F::ONE)?
            .cell();
        ctx.constrain_equal(left, right)?;

        // r * a' = r
        let left = self.mul(ctx, &is_zero, &a_inv)?.cell();
        ctx.constrain_equal(left, is_zero.cell())?;

        Ok((is_zero, a_inv))
    }

    pub fn divide(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let (is_zero, b_inv) = self.invert_with_flag(ctx, &b.clone())?;
        self.check_zero(ctx, &is_zero)?;
        self.mul(ctx, a, &b_inv)
    }

    pub fn square(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        self.mul(ctx, a, a)
    }

    pub fn mul_with_const(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: F,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let Config {
            s,
            state: [state0, state1],
            sum: [sum0, sum1],
            output,
            mul,
            rc,
        } = self.config();

        ctx.enable_selector(s)?;
        // s0*s1 - out = 0
        let a = ctx.assign_advice_from(|| "bit", *state0, lhs)?;
        ctx.assign_fixed(|| "one", *sum0, rhs)?;

        let out = ctx.assign_advice(|| "bit", *output, a.value().copied() * Value::known(rhs))?;

        ctx.assign_advice(|| "bit", *state1, Value::known(F::ZERO))?;
        ctx.assign_fixed(|| "", *sum1, F::ZERO)?;
        ctx.assign_fixed(|| "", *mul, F::ZERO)?;
        ctx.assign_fixed(|| "", *rc, F::ZERO)?;

        ctx.next();
        Ok(out)
    }

    pub fn le_num_to_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        input: &AssignedValue<F>,
        bit_len: NonZeroUsize,
    ) -> Result<Vec<AssignedValue<F>>, Halo2PlonkError>
    where
        F: PrimeFieldBits,
    {
        // TODO: ensure a is less than F.size() - 1

        let mut bits: Vec<bool> = input
            .value()
            .unwrap()
            .map(|a| a.to_le_bits().into_iter().collect())
            .unwrap_or_default();

        util::normalize_trailing_zeros(&mut bits, bit_len);

        let bits = bits
            .iter()
            .map(|bit| self.assign_bit(ctx, if *bit { F::ONE } else { F::ZERO }))
            .collect::<Result<Vec<_>, _>>()?;

        let num = self.le_bits_to_num(ctx, &bits)?;

        assert_eq!(num.value().unwrap(), input.value().unwrap());

        ctx.constrain_equal(input.cell(), num.cell())?;

        Ok(bits)
    }

    pub fn le_bits_to_num(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &[AssignedValue<F>],
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        bits.iter()
            .zip(util::get_power_of_two_iter::<F>())
            .try_fold(
                None,
                |acc, (val, shift)| -> Result<Option<AssignedValue<F>>, Halo2PlonkError> {
                    let shifted_val = self.mul_with_const(ctx, val, shift)?;
                    match acc {
                        Some(acc) => Ok(Some(self.add(ctx, &acc, &shifted_val)?)),
                        None => Ok(Some(shifted_val)),
                    }
                },
            )?
            .ok_or_else(|| {
                error!("empty bits input, Synthesis error in le_bits_to_num");
                Halo2PlonkError::Synthesis
            })
    }
}

impl<F: PrimeField> Chip<F> for Gate<F> {
    type Config = Config;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> EccGate<F> for Gate<F> {
    fn new(config: Self::Config) -> Self {
        Gate {
            config,
            _p: PhantomData,
        }
    }

    #[instrument(skip_all)]
    fn assign_point<C: CurveAffine<Base = F>, AN: Into<String>>(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        annotation: impl Fn() -> AN,
        coords: Option<(F, F)>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        let (x, y) = match coords {
            Some((x, y)) => (Value::known(x), Value::known(y)),
            None => (Value::known(F::ZERO), Value::known(F::ZERO)),
        };

        let [state0, state1] = self.config().state;

        let x = ctx.assign_advice(|| format!("{}.x", annotation().into()), state0, x)?;
        let y = ctx.assign_advice(|| format!("{}.y", annotation().into()), state1, y)?;

        ctx.next();

        Ok(AssignedPoint { x, y })
    }

    #[instrument(skip_all)]
    fn conditional_select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
        condition: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        // 1 - condition
        let one_sub_cond = self.add_with_const(ctx, condition, &-F::ONE, &F::ONE)?;

        // rhs * (1 - condition)
        let rhs_mul_mcond = self.mul(ctx, rhs, &one_sub_cond)?;

        // lhs * condition
        let lhs_mul_cond = self.mul(ctx, lhs, condition)?;
        self.add(ctx, &lhs_mul_cond, &rhs_mul_mcond)
    }

    #[instrument(skip_all)]
    fn is_infinity_point(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedValue<F>,
        y: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let is_x_zero = self.is_zero(ctx, x)?;
        let is_y_zero = self.is_zero(ctx, y)?;
        self.mul(ctx, is_x_zero, is_y_zero)
    }

    #[instrument(skip_all)]
    fn is_equal_term(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let diff = self.sub(ctx, a, b)?;
        self.is_zero(ctx, &diff)
    }

    /// # Safety
    /// The proof will be invalid if `p.x` & `q.x` not equal
    #[instrument(skip_all)]
    unsafe fn unchecked_add<C: CurveAffine<Base = F>>(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
        q: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        let yd = self.sub(ctx, &p.y, &q.y)?;
        let xd = self.sub(ctx, &p.x, &q.x)?;
        let lambda = self.divide(ctx, &yd, &xd)?;
        let lambda2 = self.square(ctx, &lambda)?;
        let tmp1 = self.sub(ctx, &lambda2, &p.x)?;
        let xr = self.sub(ctx, &tmp1, &q.x)?;
        let tmp2 = self.sub(ctx, &p.x, &xr)?;
        let tmp3 = self.mul(ctx, &lambda, &tmp2)?;
        let yr = self.sub(ctx, &tmp3, &p.y)?;
        Ok(AssignedPoint { x: xr, y: yr })
    }

    // assume a = 0 in weierstrass curve y^2 = x^3 + ax + b
    //
    // # Safety:
    // The proof will be invalid if `p.y == 0`.
    #[instrument(skip_all)]
    unsafe fn unchecked_double<C: CurveAffine<Base = F>>(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        let xp2 = self.square(ctx, &p.x)?;
        let lnum = self.mul_with_const(ctx, &xp2, C::Base::from(3))?;
        let lden = self.add(ctx, &p.y, &p.y)?;
        let lambda = self.divide(ctx, &lnum, &lden)?;
        let lambda2 = self.square(ctx, &lambda)?;

        let tmp1 = self.sub(ctx, &lambda2, &p.x)?;
        let xr = self.sub(ctx, &tmp1, &p.x)?;
        let tmp2 = self.sub(ctx, &p.x, &xr)?;
        let tmp3 = self.mul(ctx, &lambda, &tmp2)?;
        let yr = self.sub(ctx, &tmp3, &p.y)?;
        Ok(AssignedPoint { x: xr, y: yr })
    }

    #[instrument(skip_all)]
    fn negate<C: CurveAffine<Base = F>>(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        let AssignedPoint { x, y } = p;

        Ok(AssignedPoint {
            x: x.clone(),
            y: self.mul_with_const(ctx, y, -F::ONE)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::halo2_proofs::{
        arithmetic::Field,
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        halo2curves::pasta::Fq,
        plonk::Circuit,
    };

    macro_rules! generate_gate_test {
        ($test_name:ident, $region_name:expr, $gate_operation:expr) => {
            #[test]
            fn $test_name() {
                #[derive(Default)]
                struct CircuitTest<F: PrimeField>(PhantomData<F>);

                impl Circuit<Fq> for CircuitTest<Fq> {
                    type Config = Config;
                    type FloorPlanner = SimpleFloorPlanner;

                    fn without_witnesses(&self) -> Self {
                        todo!()
                    }

                    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
                        Gate::configure(meta)
                    }

                    fn synthesize(
                        &self,
                        config: Self::Config,
                        mut layouter: impl Layouter<Fq>,
                    ) -> Result<(), Halo2PlonkError> {
                        layouter.assign_region(
                            || $region_name,
                            |region| {
                                let mut ctx = RegionCtx::new(region, 0);
                                let gate = Gate::new(config.clone());

                                let [lhs, rhs] = gate
                                    .assign_values(
                                        &mut ctx,
                                        &[Fq::from_u128(100), Fq::from_u128(50)],
                                    )
                                    .unwrap();

                                // Execute the gate operation closure passed to the macro
                                $gate_operation(ctx, &gate, &lhs, &rhs);

                                Ok(())
                            },
                        )
                    }
                }

                MockProver::<Fq>::run(10, &CircuitTest::<Fq>::default(), vec![])
                    .unwrap()
                    .verify()
                    .unwrap();
            }
        };
    }

    generate_gate_test!(
        test_add_with_const,
        "add_with_const region",
        |mut ctx, gate: &Gate<Fq>, lhs, _rhs| {
            gate.add_with_const(&mut ctx, lhs, &Fq::ONE, &Fq::ONE)
                .unwrap();
        }
    );

    generate_gate_test!(
        test_add,
        "add region",
        |mut ctx, gate: &Gate<Fq>, lhs, rhs| {
            gate.add(&mut ctx, lhs, rhs).unwrap();
        }
    );

    generate_gate_test!(
        test_mul,
        "mul region",
        |mut ctx, gate: &Gate<Fq>, lhs, rhs| {
            gate.mul(&mut ctx, lhs, rhs).unwrap();
        }
    );

    generate_gate_test!(
        test_sub,
        "sub region",
        |mut ctx, gate: &Gate<Fq>, lhs, rhs| {
            gate.sub(&mut ctx, lhs, rhs).unwrap();
        }
    );

    generate_gate_test!(
        test_is_zero,
        "is_zero region",
        |mut ctx, gate: &Gate<Fq>, lhs, _rhs| {
            gate.is_zero(&mut ctx, lhs).unwrap();
        }
    );

    generate_gate_test!(
        test_assign_bit,
        "assign_bit region",
        |mut ctx, gate: &Gate<Fq>, _lhs, _rhs| {
            let [one, zero] = gate.assign_values(&mut ctx, &[Fq::ONE, Fq::ZERO]).unwrap();
            gate.assign_bit(&mut ctx, one).unwrap();
            gate.assign_bit(&mut ctx, zero).unwrap();
        }
    );

    generate_gate_test!(
        test_invert_with_flag,
        "invert_with_flag region",
        |mut ctx, gate: &Gate<Fq>, lhs, _rhs| {
            gate.invert_with_flag(&mut ctx, lhs).unwrap();
        }
    );

    generate_gate_test!(
        test_divide,
        "divide region",
        |mut ctx, gate: &Gate<Fq>, lhs, rhs| {
            gate.divide(&mut ctx, lhs, rhs).unwrap();
        }
    );

    generate_gate_test!(
        test_square,
        "square region",
        |mut ctx, gate: &Gate<Fq>, lhs, _rhs| {
            gate.square(&mut ctx, lhs).unwrap();
        }
    );

    generate_gate_test!(
        test_le_num_to_bits,
        "le_num_to_bits region",
        |mut ctx, gate: &Gate<Fq>, lhs, _rhs| {
            gate.le_num_to_bits(
                &mut ctx,
                lhs,
                NonZeroUsize::new(Fq::NUM_BITS as usize).unwrap(),
            )
            .unwrap();
        }
    );
}
