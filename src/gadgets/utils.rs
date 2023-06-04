use ff::PrimeField;
use halo2_proofs::{
    circuit::Value,
    plonk::Error,
};
use crate::aux_gate::{RegionCtx, AuxChip};
use crate::gadgets::AssignedValue;

impl<F: PrimeField, const T: usize, const RATE: usize> AuxChip<F,T,RATE> {
    pub fn assert_equal_const(&self, ctx: &mut RegionCtx<'_, F>, a: Value<F>, c: F) -> Result<(), Error> {
        self.apply(ctx, (None, None, None, None), (None, None), Some(c), (-F::ONE, a))?;
        Ok(())
    }

    pub fn assign_bit(&self, ctx: &mut RegionCtx<'_, F>, a: Value<F>) -> Result<AssignedValue<F>, Error> {
        // s0*s1 - out = 0
        let s0 = ctx.assign_advice(||"is_inf", self.config.state[0], a)?;
        let s1 = ctx.assign_advice(||"is_inf", self.config.state[0], a)?;
        let out = ctx.assign_advice(||"is_inf", self.config.out, a)?;
        ctx.constrain_equal(s0.cell(), out.cell())?;
        ctx.constrain_equal(s1.cell(), out.cell())?;

        ctx.assign_fixed(||"q_m", self.config.q_m, F::ONE)?;
        ctx.assign_fixed(||"q_o", self.config.q_m, -F::ONE)?;
        ctx.next();
        Ok(out)
    }
    pub fn assert_not_zero(&self, ctx: &mut RegionCtx<'_, F>, a: AssignedValue<F>) -> Result<(), Error> {
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

        // a * a' = 1 - r
        let state = Some(vec![a.value().copied(), a_inv]);
        let state_terms = (None, None, Some(F::ONE), state);
        self.apply(ctx, state_terms, (None, None), Some(-F::ONE), (F::ONE, r.value().copied()))?;

        // r * a' = r
        let r1 = ctx.assign_advice(||"r", self.config.state[0], r.value().copied())?;
        ctx.assign_advice(||"a_inv", self.config.state[1], a_inv)?;
        let r2 = ctx.assign_advice(||"r", self.config.out, r.value().copied())?;
        ctx.constrain_equal(r1.cell(), r2.cell())?;

        ctx.assign_fixed(||"q_m", self.config.q_m, F::ONE)?;
        ctx.assign_fixed(||"q_o", self.config.q_o, -F::ONE)?;
        ctx.next();
        
        // r = 0
        self.assert_equal_const(ctx, r1.value().copied(), F::ZERO)?;

        Ok(())
    }

    pub fn assert_not_equal(&self, ctx: &mut RegionCtx<'_, F>, a: AssignedValue<F>, b: AssignedValue<F>) -> Result<(), Error> {
        let q_1 = Some(vec![F::ONE, -F::ONE]);
        let state = Some(vec![a.value().copied(), b.value().copied()]);
        let state_terms = (q_1, None, None, state);
        let out_terms = (-F::ONE, a.value().copied() - b.value().copied());

        let diff = self.apply(ctx, state_terms, (None, None), None, out_terms)?;
        self.assert_not_zero(ctx, diff)?;
        Ok(())
    }
}
