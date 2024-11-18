use std::{array, marker::PhantomData};

use halo2_proofs::{circuit::Value, plonk::ConstraintSystem, poly::Rotation};

use crate::{
    gadgets::ecc::{AssignedPoint, EccGate},
    halo2_proofs::{
        circuit::Chip,
        halo2curves::{ff::PrimeField, CurveAffine},
        plonk::{Advice, Column, Error as Halo2PlonkError, Fixed},
    },
    main_gate::{AssignedValue, RegionCtx},
};

#[derive(Clone, Debug)]
struct Config {
    state: [Column<Advice>; 2],
    mul: Column<Fixed>,
    sum: [Column<Fixed>; 2],
    output: Column<Advice>,
    output_coeff: Column<Fixed>,
}

struct Gate<F: PrimeField> {
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
            output_coeff: meta.fixed_column(),
        };

        meta.create_gate(
            "s[0] * s[1] * mul + s[0] * sum[0] + s[1] * sum[1] - output = 0",
            |meta| {
                let Config {
                    state,
                    mul,
                    sum,
                    output,
                    output_coeff,
                } = config.clone();

                let [state0, state1] = state.map(|c| meta.query_advice(c, Rotation::cur()));
                let mul = meta.query_fixed(mul, Rotation::cur());
                let [sum0, sum1] = sum.map(|c| meta.query_fixed(c, Rotation::cur()));
                let output = meta.query_advice(output, Rotation::cur());
                let output_coeff = meta.query_fixed(output_coeff, Rotation::cur());

                [
                    (state0.clone() * state1.clone() * mul) + (state0 * sum0) + (state1 * sum1)
                        - (output * output_coeff),
                ]
            },
        );

        config
    }

    fn mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        let Config {
            state: [state0, state1],
            mul,
            output,
            output_coeff,
            ..
        } = self.config();

        ctx.assign_fixed(|| "", *mul, F::ONE)?;
        let l = ctx.assign_advice_from(|| "", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "", *state1, rhs)?;

        ctx.assign_fixed(|| "", *output_coeff, -F::ONE)?;
        let res = ctx.assign_advice(|| "", *output, l.value().copied() * r.value());

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
            output_coeff,
            ..
        } = self.config();

        ctx.assign_fixed(|| "", *sum0, F::ONE)?;
        ctx.assign_fixed(|| "", *sum1, F::ONE)?;

        let l = ctx.assign_advice_from(|| "", *state0, lhs)?;
        let r = ctx.assign_advice_from(|| "", *state1, rhs)?;

        ctx.assign_fixed(|| "", *output_coeff, -F::ONE)?;
        let res = ctx.assign_advice(|| "", *output, l.value().copied() + r.value());

        ctx.next();

        res
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

        let x = ctx.assign_advice(
            || format!("{}.x", annotation().into()),
            self.config().state[0],
            x,
        )?;

        let y = ctx.assign_advice(
            || format!("{}.y", annotation().into()),
            self.config().state[1],
            y,
        )?;

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
        let one_sub_cond = {
            let Config {
                state: [state0, state1],
                sum: [sum0, sum1],
                output,
                output_coeff,
                ..
            } = self.config();

            ctx.assign_fixed(|| "", *sum0, -F::ONE)?;
            ctx.assign_fixed(|| "", *sum1, F::ONE)?;
            ctx.assign_fixed(|| "", *output_coeff, -F::ONE)?;

            ctx.assign_advice_from(|| "", *state0, condition)?;
            ctx.assign_advice(|| "", *state1, Value::known(F::ONE))?;

            ctx.assign_advice(|| "", *output, Value::known(F::ONE) - condition.value())?
        };
        ctx.next();

        // rhs * (1 - condition)
        let rhs_mul_mcond = self.mul(ctx, rhs, &one_sub_cond)?;

        // lhs * condition
        let lhs_mul_cond = self.mul(ctx, lhs, condition)?;
        self.add(ctx, &lhs_mul_cond, &rhs_mul_mcond)
    }

    fn is_infinity_point(
        &self,
        _ctx: &mut RegionCtx<'_, F>,
        _x: &AssignedValue<F>,
        _y: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        todo!()
    }

    fn is_equal_term(
        &self,
        _ctx: &mut RegionCtx<'_, F>,
        _a: &AssignedValue<F>,
        _b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        todo!()
    }

    unsafe fn unchecked_add<C: halo2_proofs::halo2curves::CurveAffine<Base = F>>(
        &self,
        _ctx: &mut RegionCtx<'_, C::Base>,
        _p: &AssignedPoint<C>,
        _q: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        todo!()
    }

    unsafe fn unchecked_double<C: halo2_proofs::halo2curves::CurveAffine<Base = F>>(
        &self,
        _ctx: &mut RegionCtx<'_, C::Base>,
        _p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        todo!()
    }

    fn negate<C: CurveAffine<Base = F>>(
        &self,
        _ctx: &mut RegionCtx<'_, F>,
        _p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        todo!()
    }
}
