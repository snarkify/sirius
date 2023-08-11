use crate::main_gate::{AssignedValue, MainGate, RegionCtx};
use ff::PrimeField;
use halo2_proofs::{
    circuit::{Chip, Value},
    plonk::Error,
};

impl<F: PrimeField, const T: usize> MainGate<F, T> {
    pub fn assign_value(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: Value<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let out = ctx.assign_advice(|| "out", self.config().out, a)?;
        ctx.next();
        Ok(out)
    }

    pub fn assign_bit(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: Value<F>,
    ) -> Result<AssignedValue<F>, Error> {
        // s0*s1 - out = 0
        let s0 = ctx.assign_advice(|| "is_inf", self.config().state[0], a)?;
        let s1 = ctx.assign_advice(|| "is_inf", self.config().state[0], a)?;
        let out = ctx.assign_advice(|| "is_inf", self.config().out, a)?;
        ctx.constrain_equal(s0.cell(), out.cell())?;
        ctx.constrain_equal(s1.cell(), out.cell())?;

        ctx.assign_fixed(|| "q_m", self.config().q_m, F::ONE)?;
        ctx.assign_fixed(|| "q_o", self.config().q_m, -F::ONE)?;
        ctx.next();
        Ok(out)
    }

    pub fn assert_equal_const(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedValue<F>,
        c: F,
    ) -> Result<(), Error> {
        self.apply(ctx, (None, None, None), Some(c), (-F::ONE, a.into()))?;
        Ok(())
    }

    // r = 1 <=> zero; r = 0 <=> non-zero
    pub fn invert_with_flag(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedValue<F>,
    ) -> Result<(AssignedValue<F>, AssignedValue<F>), Error> {
        let (one, zero) = (F::ONE, F::ZERO);
        let (r, a_inv) = a
            .value()
            .map(|a| {
                Option::from(a.invert())
                    .map(|a_inverted| (zero, a_inverted))
                    .unwrap_or_else(|| (one, one))
            })
            .unzip();

        let r = self.assign_bit(ctx, r)?;
        let a_inv = self.assign_value(ctx, a_inv)?;

        // a * a' = 1 - r
        let state = Some(vec![a.clone().into(), a_inv.clone().into()]);
        let state_terms = (None, Some(F::ONE), state);
        self.apply(ctx, state_terms, Some(-F::ONE), (F::ONE, r.clone().into()))?;

        // r * a' = r
        let state = Some(vec![r.clone().into(), a_inv.clone().into()]);
        let state_terms = (None, Some(F::ONE), state);
        self.apply(ctx, state_terms, None, (-F::ONE, r.clone().into()))?;
        Ok((r, a_inv))
    }

    pub fn is_zero_term(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let (r, _) = self.invert_with_flag(ctx, a)?;
        Ok(r)
    }

    pub fn is_equal_term(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let diff = self.sub(ctx, a, b)?;
        self.is_zero_term(ctx, diff)
    }

    // cond must be either 0 or 1 (e.g. return value from is_zero_term)
    pub fn conditional_select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        cond: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        // res = cond * a + (1-cond) * b
        let state = Some(vec![a.into(), cond.into()]);
        let val1 = cond.value().copied() * a.value().copied();
        let res1 = self.apply(
            ctx,
            (None, Some(F::ONE), state),
            None,
            (-F::ONE, val1.into()),
        )?;

        let state = Some(vec![b.into(), cond.into()]);
        let val2 = (Value::known(F::ONE) - cond.value().copied()) * b.value().copied();
        let res2 = self.apply(
            ctx,
            (Some(vec![F::ONE]), Some(-F::ONE), state),
            None,
            (-F::ONE, val2.into()),
        )?;
        self.add(ctx, &res1, &res2)
    }

    // is_inf => 1, otherwise => 0
    pub fn is_infinity_point(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedValue<F>,
        y: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let r1 = self.is_zero_term(ctx, x.clone())?;
        let r2 = self.is_zero_term(ctx, y.clone())?;
        self.mul(ctx, &r1, &r2)
    }

    pub fn assert_not_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedValue<F>,
    ) -> Result<(), Error> {
        let r = self.is_zero_term(ctx, a)?;
        // r = 0
        self.assert_equal_const(ctx, r, F::ZERO)?;
        Ok(())
    }

    pub fn assert_not_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<(), Error> {
        let diff = self.sub(ctx, a, b)?;
        self.assert_not_zero(ctx, diff)?; // We know diff is not None
        Ok(())
    }

    pub fn add(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        // a + b = r
        let q_1 = Some(vec![F::ONE, F::ONE]);
        let state = Some(vec![a.clone().into(), b.clone().into()]);
        let state_terms = (q_1, None, state);
        let out_val = a.value().copied() + b.value().copied();
        let out_terms = (-F::ONE, out_val.into());
        let out = self.apply(ctx, state_terms, None, out_terms)?;
        Ok(out)
    }

    pub fn sub(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        // a - b = r
        let q_1 = Some(vec![F::ONE, -F::ONE]);
        let state = Some(vec![a.clone().into(), b.clone().into()]);
        let state_terms = (q_1, None, state);
        let out_val = a.value().copied() - b.value().copied();
        let out_terms = (-F::ONE, out_val.into());
        let out = self.apply(ctx, state_terms, None, out_terms)?;
        Ok(out)
    }

    pub fn mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let state = Some(vec![a.clone().into(), b.clone().into()]);
        let state_terms = (None, Some(F::ONE), state);
        let out_val = a.value().copied() * b.value().copied();
        let out_terms = (-F::ONE, out_val.into());
        let out = self.apply(ctx, state_terms, None, out_terms)?;
        Ok(out)
    }

    pub fn mul_by_const(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: F,
    ) -> Result<AssignedValue<F>, Error> {
        let state = Some(vec![a.clone().into()]);
        let state_terms = (Some(vec![b]), None, state);
        let out_val = a.value().copied() * Value::known(b);
        let out_terms = (-F::ONE, out_val.into());
        let out = self.apply(ctx, state_terms, None, out_terms)?;
        Ok(out)
    }

    pub fn square(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        self.mul(ctx, a, a)
    }

    pub fn divide(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let (_, b_inv) = self.invert_with_flag(ctx, b.clone())?;
        self.mul(ctx, &a, &b_inv)
    }
}
