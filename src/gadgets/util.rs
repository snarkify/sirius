use halo2_proofs::{
    circuit::{Chip, Value},
    plonk::Error,
};

use crate::{
    ff::PrimeField,
    main_gate::{AssignedValue, MainGate, MainGateConfig, RegionCtx},
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
        let MainGateConfig {
            state,
            q_m,
            q_o,
            out,
            ..
        } = self.config();

        // s0*s1 - out = 0
        let s0 = ctx.assign_advice(|| "bit", state[0], a)?;
        let s1 = ctx.assign_advice(|| "bit", state[1], a)?;
        ctx.assign_fixed(|| "one", q_m[0], F::ONE)?;

        ctx.assign_fixed(|| "minus one", *q_o, -F::ONE)?;
        let out = ctx.assign_advice(|| "bit", *out, a)?;

        ctx.constrain_equal(s0.cell(), out.cell())?;
        ctx.constrain_equal(s1.cell(), out.cell())?;

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
        let (r, a_inv) = a
            .value()
            .map(|a| {
                Option::from(a.invert())
                    .map(|a_inverted| (F::ZERO, a_inverted))
                    .unwrap_or_else(|| (F::ONE, F::ONE))
            })
            .unzip();

        let r = self.assign_bit(ctx, r)?;
        let a_inv = self.assign_value(ctx, a_inv)?;

        // a * a' = 1 - r
        let state = Some(vec![a.clone().into(), a_inv.clone().into()]);
        let state_terms = (None, Some(vec![F::ONE]), state);
        self.apply(ctx, state_terms, Some(-F::ONE), (F::ONE, r.clone().into()))?;

        // r * a' = r
        let state = Some(vec![r.clone().into(), a_inv.clone().into()]);
        let state_terms = (None, Some(vec![F::ONE]), state);
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

    pub fn is_not_zero_term(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let is_zero = self.is_zero_term(ctx, a)?;

        let lhs = self.mul_by_const(ctx, &is_zero, -F::ONE)?;
        self.add_with_const(ctx, &lhs, F::ONE)
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
    // require T >= 4
    pub fn conditional_select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        cond: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let state = Some(vec![a.into(), cond.into(), b.into(), cond.into()]);
        // val = cond * a + (1-cond) * b
        let val = cond.value().copied() * a.value().copied()
            + (Value::known(F::ONE) - cond.value().copied()) * b.value().copied();
        self.apply(
            ctx,
            (
                Some(vec![F::ZERO, F::ZERO, F::ONE]),
                Some(vec![F::ONE, -F::ONE]),
                state,
            ),
            None,
            (-F::ONE, val.into()),
        )
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
        let state_terms = (None, Some(vec![F::ONE]), state);
        let out_val = a.value().copied() * b.value().copied();
        let out_terms = (-F::ONE, out_val.into());
        let out = self.apply(ctx, state_terms, None, out_terms)?;
        Ok(out)
    }

    /// Add `lhs` assigned value to `rhs` constant
    ///
    /// By one row with simple expression
    /// ```markdown
    /// input * q_i + output * q_o + rc  = 0
    /// lhs   * 1   + sum    * -1  + rhs = 0
    /// ```
    pub fn add_with_const(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: F,
    ) -> Result<AssignedValue<F>, Error> {
        let config = self.config();

        ctx.assign_fixed(|| "q_i", config.q_i, F::ONE)?;
        ctx.assign_fixed(|| "q_o", config.q_o, -F::ONE)?;

        let assigned_lhs =
            ctx.assign_advice_from(|| "lhs for sum with const", config.input, lhs)?;
        ctx.assign_fixed(|| "rhs for sum with const", config.rc, rhs)?;

        let sum = assigned_lhs.value().copied() + Value::known(rhs);
        let assigned_res = ctx.assign_advice(|| "result for sum with const", config.out, sum)?;

        ctx.next();
        Ok(assigned_res)
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
        self.mul(ctx, a, &b_inv)
    }
}
