use std::{array, marker::PhantomData};

use halo2_proofs::{circuit::Value, plonk::ConstraintSystem, poly::Rotation};

use crate::{
    gadgets::ecc::{AssignedPoint, EccGate},
    halo2_proofs::{
        circuit::Chip,
        halo2curves::{ff::PrimeField, CurveAffine},
        plonk::{Advice, Column, Error as Halo2PlonkError, Fixed},
    },
    main_gate::{AssignAdviceFrom, AssignedValue, RegionCtx},
};

#[derive(Clone, Debug)]
pub struct Config {
    state: [Column<Advice>; 2],
    mul: Column<Fixed>,
    sum: [Column<Fixed>; 2],
    output: Column<Advice>,
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
        };

        meta.create_gate(
            "s[0] * s[1] * mul + s[0] * sum[0] + s[1] * sum[1] + rc - output = 0",
            |meta| {
                let Config {
                    state,
                    mul,
                    sum,
                    output,
                    rc,
                } = config.clone();

                let [state0, state1] = state.map(|c| meta.query_advice(c, Rotation::cur()));
                let mul = meta.query_fixed(mul, Rotation::cur());
                let [sum0, sum1] = sum.map(|c| meta.query_fixed(c, Rotation::cur()));
                let output = meta.query_advice(output, Rotation::cur());
                let rc = meta.query_fixed(rc, Rotation::cur());

                [
                    (state0.clone() * state1.clone() * mul)
                        + (state0 * sum0)
                        + (state1 * sum1)
                        + rc
                        - output,
                ]
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
            state: [state0, state1],
            mul,
            output,
            ..
        } = self.config();

        ctx.assign_fixed(|| "", *mul, F::ONE)?;
        let l = ctx.assign_advice_from(|| "", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "", *state1, rhs)?;

        let res = ctx.assign_advice(|| "", *output, l.value().copied() * r.value());

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
            state: [state0, _],
            sum: [sum0, _],
            output,
            rc,
            ..
        } = self.config();

        ctx.assign_fixed(|| "", *sum0, *lhs_coeff)?;

        let l = ctx.assign_advice_from(|| "", *state0, lhs)?;
        let r = ctx.assign_fixed(|| "", *rc, *rhs)?;

        let res = ctx.assign_advice(|| "", *output, l.value().copied() + r.value());

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
            state: [state0, state1],
            sum: [sum0, sum1],
            output,
            ..
        } = self.config();

        ctx.assign_fixed(|| "", *sum0, F::ONE)?;
        ctx.assign_fixed(|| "", *sum1, F::ONE)?;

        let l = ctx.assign_advice_from(|| "", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "", *state1, rhs)?;

        let res = ctx.assign_advice(|| "", *output, l.value().copied() + r.value());

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
            state: [state0, state1],
            sum: [sum0, sum1],
            output,
            ..
        } = self.config();

        ctx.assign_fixed(|| "", *sum0, F::ONE)?;
        ctx.assign_fixed(|| "", *sum1, -F::ONE)?;

        let l = ctx.assign_advice_from(|| "", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "", *state1, rhs)?;

        let res = ctx.assign_advice(|| "", *output, l.value().copied() + r.value());

        ctx.next();

        res
    }

    fn check_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        value: &AssignedValue<F>,
    ) -> Result<(), Halo2PlonkError> {
        let Config {
            state: [state0, ..],
            sum: [sum0, ..],
            ..
        } = self.config();

        ctx.assign_advice_from(|| "", *state0, value)?;
        ctx.assign_fixed(|| "", *sum0, F::ONE)?;

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

    fn assign_values<'a, const L: usize>(
        &self,
        ctx: &mut RegionCtx<'a, F>,
        values: &[impl Clone + AssignAdviceFrom<'a, F>; L],
    ) -> Result<[AssignedValue<F>; L], Halo2PlonkError> {
        let mut advice = self.config().state.to_vec();
        advice.push(self.config().output);

        let mut result = Vec::with_capacity(values.len());
        for chunk in values.chunks(advice.len()) {
            for (value, col) in chunk.iter().zip(advice.iter()) {
                result.push(ctx.assign_advice_from(|| "", *col, value.clone())?);
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
            state: [state0, state1],
            mul,
            output,
            ..
        } = self.config();

        // s0*s1 - out = 0
        let a = ctx.assign_advice_from(|| "bit", *state0, a)?;
        ctx.assign_advice_from(|| "bit", *state1, &a)?;
        ctx.assign_fixed(|| "one", *mul, F::ONE)?;

        let out = ctx.assign_advice_from(|| "bit", *output, &a)?;

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
            state: [state0, ..],
            sum: [sum0, ..],
            output,
            ..
        } = self.config();

        // s0*s1 - out = 0
        let a = ctx.assign_advice_from(|| "bit", *state0, lhs)?;
        ctx.assign_fixed(|| "one", *sum0, rhs)?;

        let out = ctx.assign_advice(|| "bit", *output, a.value().copied() * Value::known(rhs))?;

        ctx.next();
        Ok(out)
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

    fn assign_point<C: CurveAffine<Base = F>, AN: Into<String>>(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        annotation: impl Fn() -> AN,
        coords: Option<(F, F)>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        let (x, y) = match coords {
            Some((x, y)) => (Value::known(x), Value::known(y)),
            None => (Value::unknown(), Value::unknown()),
        };

        let [state0, state1] = self.config().state;

        let x = ctx.assign_advice(|| format!("{}.x", annotation().into()), state0, x)?;
        let y = ctx.assign_advice(|| format!("{}.y", annotation().into()), state1, y)?;

        ctx.next();

        Ok(AssignedPoint { x, y })
    }

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
