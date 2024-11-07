use halo2_proofs::halo2curves::CurveAffine;

use crate::main_gate::AssignedValue;

// assume point is not infinity
#[derive(Clone, Debug)]
pub struct AssignedPoint<C: CurveAffine> {
    pub(crate) x: AssignedValue<C::Base>,
    pub(crate) y: AssignedValue<C::Base>,
}

impl<C: CurveAffine> AssignedPoint<C> {
    pub fn coordinates(&self) -> (&AssignedValue<C::Base>, &AssignedValue<C::Base>) {
        (&self.x, &self.y)
    }

    pub fn coordinates_values(&self) -> Option<(C::Base, C::Base)> {
        let x = self.x.value().copied().unwrap();
        let y = self.y.value().copied().unwrap();

        Some((x?, y?))
    }

    pub fn to_curve(&self) -> Option<C> {
        let (x, y) = self.coordinates();
        C::from_xy(x.value().unwrap().copied()?, y.value().unwrap().copied()?).into()
    }
}
