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
    pub(crate) is_inf: AssignedValue<C::Base>, // one for true, zero for false
}

impl<C: CurveAffine> AssignedPoint<C> {
    pub fn assign<F: PrimeField,const T:usize,const RATE: usize>(ctx: &mut RegionCtx<'_, C::Base>, chip: AuxChip<F,T,RATE>, coords: Option<(C::Base, C::Base, bool)>) -> Result<Self, Error> {
        assert!(chip.config.state.len() >= 4);
        let is_inf_val = if coords.map_or(true, |c| c.2) {
            C::Base::ONE
        } else {
            C::Base::ZERO
        };
        let s0 = ctx.assign_advice(||"is_inf", chip.config.state[0], Value::known(is_inf_val))?;
        let s1 = ctx.assign_advice(||"is_inf", chip.config.state[0], Value::known(is_inf_val))?;
        let out = ctx.assign_advice(||"is_inf", chip.config.out, Value::known(is_inf_val))?;
        ctx.constrain_equal(s0.cell(), out.cell())?;
        ctx.constrain_equal(s1.cell(), out.cell())?;

        let x = ctx.assign_advice(||"x", chip.config.state[2], Value::known(coords.map_or(C::Base::ZERO,|c|c.0)))?;
        let y = ctx.assign_advice(||"y", chip.config.state[2], Value::known(coords.map_or(C::Base::ZERO, |c|c.1)))?;

        ctx.assign_fixed(||"q_m", chip.config.q_m, C::Base::ONE)?;
        ctx.assign_fixed(||"q_o", chip.config.q_m, -C::Base::ONE)?;
        ctx.next();

        Ok(Self {
            x,
            y,
            is_inf: out
        })
    }

    pub fn coordinates(&self) -> (&AssignedValue<C::Base>, &AssignedValue<C::Base>, &AssignedValue<C::Base>) {
        (&self.x, &self.y, &self.is_inf)
    }

    pub fn add(&self, ctx: &mut RegionCtx<'_, C::Base>, other: &AssignedPoint<C>) -> Result<Self, Error> {
        Ok(self.clone())
    }
}

