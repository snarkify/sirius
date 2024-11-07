use halo2_proofs::circuit::Value;

use super::AssignedPoint;
use crate::{
    halo2_proofs::{
        circuit::Chip,
        halo2curves::{ff::PrimeField, CurveAffine},
        plonk::Error as Halo2PlonkError,
    },
    main_gate::{AssignedValue, MainGate, RegionCtx},
};

pub trait EccGate<F: PrimeField>: Chip<F> {
    fn new(config: Self::Config) -> Self;

    fn assign_point<C: CurveAffine<Base = F>, AN: Into<String>>(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        annotation: impl Fn() -> AN,
        coords: Option<(F, F)>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError>;

    fn conditional_select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
        condition: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError>;

    fn is_infinity_point(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedValue<F>,
        y: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError>;

    fn is_equal_term(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError>;

    /// # Safety
    ///
    /// TODO
    unsafe fn unchecked_add<C: CurveAffine<Base = F>>(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
        q: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError>;

    /// # Safety
    ///
    /// TODO
    unsafe fn unchecked_double<C: CurveAffine<Base = F>>(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError>;

    fn negate<C: CurveAffine<Base = F>>(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError>;
}

impl<const T: usize, F: PrimeField> EccGate<F> for MainGate<F, T> {
    fn new(config: Self::Config) -> Self {
        MainGate::new(config)
    }

    fn assign_point<C: CurveAffine<Base = F>, AN: Into<String>>(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        annotation: impl Fn() -> AN,
        coords: Option<(C::Base, C::Base)>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        let x = ctx.assign_advice(
            || format!("{}.x", annotation().into()),
            self.config().state[0],
            Value::known(coords.map_or(C::Base::ZERO, |c| c.0)),
        )?;
        let y = ctx.assign_advice(
            || format!("{}.y", annotation().into()),
            self.config().state[1],
            Value::known(coords.map_or(C::Base::ZERO, |c| c.1)),
        )?;
        ctx.next();

        Ok(AssignedPoint { x, y })
    }

    fn conditional_select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        cond: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        MainGate::conditional_select(self, ctx, a, b, cond)
    }

    fn is_infinity_point(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedValue<F>,
        y: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        MainGate::is_infinity_point(self, ctx, x, y)
    }

    fn is_equal_term(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Halo2PlonkError> {
        MainGate::is_equal_term(self, ctx, a, b)
    }

    /// # Safety
    ///
    /// TODO
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
    // # Safety:
    // TODO
    unsafe fn unchecked_double<C: CurveAffine<Base = F>>(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Halo2PlonkError> {
        let xp2 = self.square(ctx, &p.x)?;
        let lnum = self.mul_by_const(ctx, &xp2, C::Base::from(3))?;
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
        let x = p.clone().x;
        let y = &p.y;
        let y_minus_val: Value<C::Base> = -y.value().copied();
        let y = self.apply(
            ctx,
            (Some(vec![C::Base::ONE]), None, Some(vec![y.into()])),
            None,
            (C::Base::ONE, y_minus_val.into()),
        )?;
        Ok(AssignedPoint { x, y })
    }
}
