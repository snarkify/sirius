use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::{Chip, Value},
    plonk::Error,
};
use ff::Field;
use crate::{
    main_gate::{RegionCtx, MainGate},
    gadgets::AssignedValue,
};

#[derive(Clone)]
pub struct AssignedPoint<C: CurveAffine> {
    pub(crate) x: AssignedValue<C::Base>,
    pub(crate) y: AssignedValue<C::Base>,
}

impl<C: CurveAffine> AssignedPoint<C> {

    pub fn coordinates(&self) -> (&AssignedValue<C::Base>, &AssignedValue<C::Base>) {
        (&self.x, &self.y)
    }


}

pub struct EccChip<C: CurveAffine, const T: usize> {
    main_gate: MainGate<C::Base, T>,
}

impl<C: CurveAffine, const T: usize> EccChip<C, T> {
    pub fn assign_point(&self, ctx: &mut RegionCtx<'_, C::Base>, coords: Option<(C::Base, C::Base)>) -> Result<AssignedPoint<C>, Error> {
        let x = ctx.assign_advice(||"x", self.main_gate.config().state[0], Value::known(coords.map_or(C::Base::ZERO,|c|c.0)))?;
        let y = ctx.assign_advice(||"y", self.main_gate.config().state[1], Value::known(coords.map_or(C::Base::ZERO, |c|c.1)))?;
        ctx.next();

        Ok(AssignedPoint {
            x,
            y,
        })
    }

    pub fn add(&self, ctx: &mut RegionCtx<'_, C::Base>, a: &AssignedPoint<C>, b: &AssignedPoint<C>) -> Result<AssignedPoint<C>, Error> {
        self.main_gate.assert_not_equal(ctx, &a.x, &b.x)?;
        self._add_unsafe(ctx, a, b)
    }

    fn _add_unsafe(&self, ctx: &mut RegionCtx<'_, C::Base>, a: &AssignedPoint<C>, b: &AssignedPoint<C>) -> Result<AssignedPoint<C>, Error> {
        unimplemented!()
    }
}
