use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::Value,
    plonk::Error,
};
use ff::{Field, PrimeField};
use crate::{
    aux_gate::{RegionCtx, AuxChip},
    gadgets::AssignedValue,
};

#[derive(Clone)]
pub struct AssignedPoint<C: CurveAffine> {
    pub(crate) x: AssignedValue<C::Base>,
    pub(crate) y: AssignedValue<C::Base>,
}

impl<C: CurveAffine> AssignedPoint<C> {
    pub fn assign<const T:usize,const RATE: usize>(ctx: &mut RegionCtx<'_, C::Base>, chip: AuxChip<C::Base,T,RATE>, coords: Option<(C::Base, C::Base, bool)>) -> Result<Self, Error> {
        let x = ctx.assign_advice(||"x", chip.config.state[0], Value::known(coords.map_or(C::Base::ZERO,|c|c.0)))?;
        let y = ctx.assign_advice(||"y", chip.config.state[1], Value::known(coords.map_or(C::Base::ZERO, |c|c.1)))?;
        ctx.next();

        Ok(Self {
            x,
            y,
        })
    }

    pub fn coordinates(&self) -> (&AssignedValue<C::Base>, &AssignedValue<C::Base>) {
        (&self.x, &self.y)
    }

    pub fn add<const T:usize, const RATE:usize>(&self, ctx: &mut RegionCtx<'_, C::Base>, chip: AuxChip<C::Base,T,RATE>, other: &AssignedPoint<C>) -> Result<Self, Error> {
        chip.assert_not_equal(ctx, &self.x, &other.x)?;
        Ok(self.clone())
    }

}

