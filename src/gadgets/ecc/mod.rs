use std::{cmp, marker::PhantomData};

use rand_core::OsRng;
use tracing::*;

use crate::{
    halo2_proofs::{
        arithmetic::{CurveAffine, Field},
        circuit::Chip,
        halo2curves::ff::{PrimeField, PrimeFieldBits},
        plonk::Error,
    },
    main_gate::{AssignedValue, RegionCtx},
};

mod point;
pub use point::AssignedPoint;

mod gate;
pub use gate::EccGate;

pub struct EccChip<C: CurveAffine, G: EccGate<C::Base>> {
    pub(crate) gate: G,
    _p: PhantomData<C>,
}

impl<C: CurveAffine, G: EccGate<C::Base>> EccChip<C, G> {
    pub fn new(config: G::Config) -> Self {
        Self {
            gate: G::new(config),
            _p: PhantomData,
        }
    }

    pub fn config(&self) -> <G as Chip<C::Base>>::Config {
        self.gate.config().clone()
    }

    pub fn assign_from_curve<AN: Into<String>>(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        annotation: impl Fn() -> AN,
        value: &C,
    ) -> Result<AssignedPoint<C>, Error> {
        let coordinates: Option<_> = value
            .coordinates()
            .map(|coordinates| (*coordinates.x(), *coordinates.y()))
            .into();
        self.gate.assign_point(ctx, annotation, coordinates)
    }

    pub fn negate(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Error> {
        self.gate.negate(ctx, p)
    }

    #[instrument(skip_all)]
    pub fn add(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        lhs: &AssignedPoint<C>,
        rhs: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Error> {
        let is_lhs_inf = self
            .gate
            .is_infinity_point(ctx, &lhs.x, &lhs.y)
            .inspect_err(|err| error!("while is_infinity p: {err:?}"))?;
        trace!("after `is_infinity_point` for p offset is {}", ctx.offset());

        let is_rhs_inf = self
            .gate
            .is_infinity_point(ctx, &rhs.x, &rhs.y)
            .inspect_err(|err| error!("while is_infinity q: {err:?}"))?;
        trace!("after `is_infinity_point` for q offset is {}", ctx.offset());

        let is_equal_x = self
            .gate
            .is_equal_term(ctx, &lhs.x, &rhs.x)
            .inspect_err(|err| error!("while is_equal p.x == q.x: {err:?}"))?;
        trace!(
            "after `is_equal_term` for p.x == q.x offset is {}",
            ctx.offset()
        );

        let is_equal_y = self
            .gate
            .is_equal_term(ctx, &lhs.y, &rhs.y)
            .inspect_err(|err| error!("while is_equal p.y == q.y: {err:?}"))?;

        trace!(
            "after `is_equal_term` for p.y == q.y offset is {}",
            ctx.offset()
        );

        let inf = self
            .gate
            .assign_point::<C, _>(ctx, || "inf", None)
            .inspect_err(|err| error!("while assigning point `inf`: {err:?}"))?;
        trace!("after `assign_point` for `inf` offset is {}", ctx.offset());

        // Нужно переделать логику
        // Не использовать результат только если is_equal_x
        // А вызывать функцию с правильными параметрами
        // Для этого надо разобраться с тем как сумма точек работает
        let unchecked_add_result = {
            //let p_input = self.conditional_select(ctx, p, p, &is_equal_x)?;
            //let q_input = self.conditional_select(ctx, q, p, &is_equal_x)?;

            // # Safety:
            // We check at the bottom of this fn, what p.x == q.x
            unsafe { self.gate.unchecked_add(ctx, &lhs, &rhs) }
                .inspect_err(|err| error!("while unchecked add p & q: {err:?}"))
        }?;

        trace!("after `unchecked_add` for p & q offset is {}", ctx.offset());

        let doubled_lhs = self.double(ctx, lhs)?;
        trace!("after `double` for p offset is {}", ctx.offset());

        let x1 = self
            .gate
            .conditional_select(ctx, &doubled_lhs.x, &inf.x, &is_equal_y)
            .inspect_err(|err| error!("while conditional select p2.x & inf.x: {err:?}"))?;

        trace!(
            "after `conditional_select` for p2.x & inf.x offset is {}",
            ctx.offset()
        );

        let y1 = self
            .gate
            .conditional_select(ctx, &doubled_lhs.y, &inf.y, &is_equal_y)
            .inspect_err(|err| error!("while conditional select p2.y & inf.y: {err:?}"))?;

        trace!(
            "after `conditional_select` for p2.y & inf.y offset is {}",
            ctx.offset()
        );

        let x2 = self
            .gate
            .conditional_select(ctx, &x1, &unchecked_add_result.x, &is_equal_x)
            .inspect_err(|err| error!("while conditional select x1 & r.x: {err:?}"))?;

        trace!(
            "after `conditional_select` for x1 & r.x offset is {}",
            ctx.offset()
        );

        let y2 = self
            .gate
            .conditional_select(ctx, &y1, &unchecked_add_result.y, &is_equal_x)
            .inspect_err(|err| error!("while conditional select y1 & r.y: {err:?}"))?;

        trace!(
            "after `conditional_select` for y1 & r.y offset is {}",
            ctx.offset()
        );

        let x3 = self
            .gate
            .conditional_select(ctx, &lhs.x, &x2, &is_rhs_inf)
            .inspect_err(|err| error!("while conditional select p.x & x2: {err:?}"))?;

        trace!(
            "after `conditional_select` for p.x & x2 offset is {}",
            ctx.offset()
        );

        let y3 = self
            .gate
            .conditional_select(ctx, &lhs.y, &y2, &is_rhs_inf)
            .inspect_err(|err| error!("while conditional select p.y & y2: {err:?}"))?;

        trace!(
            "after `conditional_select` for p.y & y2 offset is {}",
            ctx.offset()
        );

        let result_x = self
            .gate
            .conditional_select(ctx, &rhs.x, &x3, &is_lhs_inf)
            .inspect_err(|err| error!("while conditional select q.x & x3: {err:?}"))?;

        trace!(
            "after `conditional_select` for q.x & x3 offset is {}",
            ctx.offset()
        );

        let result_y = self
            .gate
            .conditional_select(ctx, &rhs.y, &y3, &is_lhs_inf)
            .inspect_err(|err| error!("while conditional select q.y & y3: {err:?}"))?;

        trace!(
            "after `conditional_select` for q.y & y3 offset is {}",
            ctx.offset()
        );

        Ok(AssignedPoint { x: result_x, y: result_y })
    }

    fn double(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Error> {
        let is_inf = self.gate.is_infinity_point(ctx, &p.x, &p.y)?;
        let any_point =
            self.gate
                .assign_point(ctx, || "any point", Some((C::Base::ONE, C::Base::ONE)))?;

        let input = self.conditional_select(ctx, &any_point, p, &is_inf)?;

        // Safety:
        // This value will be used only if `is_inf = false`
        // `is_inf` false, only if p.x & p.y not zero
        let p2 = unsafe { self.gate.unchecked_double(ctx, &input) }?;

        let x = self.gate.conditional_select(ctx, &p.x, &p2.x, &is_inf)?;
        let y = self.gate.conditional_select(ctx, &p.y, &p2.y, &is_inf)?;

        Ok(AssignedPoint { x, y })
    }

    pub fn conditional_select(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        lhs: &AssignedPoint<C>,
        rhs: &AssignedPoint<C>,
        condition: &AssignedValue<C::Base>,
    ) -> Result<AssignedPoint<C>, Error> {
        Ok(AssignedPoint {
            x: self
                .gate
                .conditional_select(ctx, &lhs.x, &rhs.x, condition)?,
            y: self
                .gate
                .conditional_select(ctx, &lhs.y, &rhs.y, condition)?,
        })
    }

    // optimization here is analogous to
    /// https://github.com/arkworks-rs/r1cs-std/blob/6d64f379a27011b3629cf4c9cb38b7b7b695d5a0/src/groups/curves/short_weierstrass/mod.rs#L295
    pub fn scalar_mul(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        lhs: &AssignedPoint<C>,
        scalar_bits: &[AssignedValue<C::Base>],
    ) -> Result<AssignedPoint<C>, Error> {
        let split_len = cmp::min(scalar_bits.len(), (C::Base::NUM_BITS - 2) as usize);
        let (incomplete_bits, complete_bits) = scalar_bits.split_at(split_len);

        let mut acc = lhs.clone();
        let is_lhs_infinity = self
            .gate
            .is_infinity_point(ctx, &lhs.x, &lhs.y)
            .inspect_err(|err| {
                error!("Failed to check if lhs is infinity in scalar_mul: {err:?}")
            })?;
        trace!("after `is_infinity_point` offset is {}", ctx.offset());

        let one_point = self
            .gate
            .assign_point(ctx, || "one point", Some((C::Base::ONE, C::Base::ONE)))
            .inspect_err(|err| error!("Failed to assign one point in scalar_mul: {err:?}"))?;
        trace!("after `assign_point` offset is {}", ctx.offset());

        let lhs_non_zero = self
            .conditional_select(ctx, &one_point, lhs, &is_lhs_infinity)
            .inspect_err(|err| {
                error!("Failed to conditionally select lhs_non_zero in scalar_mul: {err:?}")
            })?;
        trace!(
            "after `conditional_select` for lhs_non_zero offset is {}",
            ctx.offset()
        );

        let mut p = unsafe {
            self.gate
                .unchecked_double(ctx, &lhs_non_zero)
                .inspect_err(|err| {
                    error!("Failed to double initial point in scalar_mul: {err:?}")
                })?
        };
        trace!("after `unchecked_double` offset is {}", ctx.offset());

        for (i, bit) in incomplete_bits.iter().skip(1).enumerate() {
            let tmp = unsafe {
                self.gate.unchecked_add(ctx, &acc, &p).inspect_err(|err| {
                    error!("Failed to add points in iteration {i} of scalar_mul: {err:?}")
                })?
            };
            trace!(
                "after `unchecked_add` in iteration {i} offset is {}",
                ctx.offset()
            );

            acc = AssignedPoint {
            x: self
                .gate
                .conditional_select(ctx, &tmp.x, &acc.x, bit)
                .inspect_err(|err| error!(
                    "Failed to conditionally select x-coordinate in iteration {i} of scalar_mul: {err:?}"
                ))?,
            y: self
                .gate
                .conditional_select(ctx, &tmp.y, &acc.y, bit)
                .inspect_err(|err| error!(
                    "Failed to conditionally select y-coordinate in iteration {i} of scalar_mul: {err:?}"
                ))?,
        };
            trace!(
                "after `conditional_select` in iteration {i} offset is {}",
                ctx.offset()
            );

            p = unsafe {
                self.gate.unchecked_double(ctx, &p).inspect_err(|err| {
                    error!("Failed to double point p in iteration {i} of scalar_mul: {err:?}")
                })?
            };
            trace!(
                "after `unchecked_double` in iteration {i} offset is {}",
                ctx.offset()
            );
        }

        let res: AssignedPoint<C> = {
            let acc_minus_initial = {
                let neg = self.negate(ctx, &lhs_non_zero).inspect_err(|err| {
                    error!("Failed to negate initial point in scalar_mul: {err:?}")
                })?;
                trace!("after `negate` offset is {}", ctx.offset());

                self.add(ctx, &acc, &neg).inspect_err(|err| {
                    error!("Failed to add acc and negated point in scalar_mul: {err:?}")
                })?
            };

            trace!(
                "after `add` for acc_minus_initial offset is {}",
                ctx.offset()
            );

            let x = self
                .gate
                .conditional_select(ctx, &acc.x, &acc_minus_initial.x, &scalar_bits[0])
                .inspect_err(|err| {
                    error!(
                "Failed to conditionally select x-coordinate for correction in scalar_mul: {err:?}"
            )
                })?;
            let y = self
                .gate
                .conditional_select(ctx, &acc.y, &acc_minus_initial.y, &scalar_bits[0])
                .inspect_err(|err| {
                    error!(
                "Failed to conditionally select y-coordinate for correction in scalar_mul: {err:?}"
            )
                })?;
            trace!(
                "after `conditional_select` for correction offset is {}",
                ctx.offset()
            );

            AssignedPoint { x, y }
        };

        let infp = self
            .gate
            .assign_point::<C, _>(ctx, || "infp", None)
            .inspect_err(|err| error!("Failed to assign infinity point in scalar_mul: {err:?}"))?;
        trace!(
            "after `assign_point` for infinity point offset is {}",
            ctx.offset()
        );

        let is_p_iden = self
            .gate
            .is_infinity_point(ctx, &lhs_non_zero.x, &lhs_non_zero.y)
            .inspect_err(|err| {
                error!("Failed to check if point is infinity in scalar_mul: {err:?}")
            })?;
        trace!(
            "after `is_infinity_point` for infinity case offset is {}",
            ctx.offset()
        );

        let x = self
            .gate
            .conditional_select(ctx, &infp.x, &res.x, &is_p_iden)
            .inspect_err(|err| {
                error!(
            "Failed to conditionally select x-coordinate for infinity case in scalar_mul: {err:?}"
        )
            })?;
        let y = self
            .gate
            .conditional_select(ctx, &infp.y, &res.y, &is_p_iden)
            .inspect_err(|err| {
                error!(
            "Failed to conditionally select y-coordinate for infinity case in scalar_mul: {err:?}"
        )
            })?;
        trace!(
            "after `conditional_select` for infinity case offset is {}",
            ctx.offset()
        );

        acc = AssignedPoint { x, y };

        for (i, bit) in complete_bits.iter().enumerate() {
            let tmp = self.add(ctx, &acc, &p).inspect_err(|err| {
                error!(
                    "Failed to add acc and p in complete_bits iteration {i} of scalar_mul: {err:?}"
                )
            })?;
            trace!(
                "after `add` in complete_bits iteration {i} offset is {}",
                ctx.offset()
            );

            let x = self
            .gate
            .conditional_select(ctx, &tmp.x, &acc.x, bit)
            .inspect_err(|err| error!(
                "Failed to conditionally select x-coordinate in complete_bits iteration {i} of scalar_mul: {err:?}"
            ))?;
            let y = self
            .gate
            .conditional_select(ctx, &tmp.y, &acc.y, bit)
            .inspect_err(|err| error!(
                "Failed to conditionally select y-coordinate in complete_bits iteration {i} of scalar_mul: {err:?}"
            ))?;
            trace!(
                "after `conditional_select` in complete_bits iteration {i} offset is {}",
                ctx.offset()
            );

            acc = AssignedPoint { x, y };

            p = self.double(ctx, &p).inspect_err(|err| {
                error!(
            "Failed to double point p in complete_bits iteration {i} of scalar_mul: {err:?}"
        )
            })?;
            trace!(
                "after `double` in complete_bits iteration {i} offset is {}",
                ctx.offset()
            );
        }

        self.conditional_select(ctx, lhs, &acc, &is_lhs_infinity)
            .inspect_err(|err| {
                error!(
                    "Failed to return conditional result for infinity case in scalar_mul: {err:?}"
                )
            })
    }

    // scalar_mul for non_zero point
    // we assume the point p0 is not infinity here
    #[instrument(skip_all)]
    pub fn scalar_mul_non_zero(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p0: &AssignedPoint<C>,
        scalar_bits: &[AssignedValue<C::Base>],
    ) -> Result<AssignedPoint<C>, Error> {
        debug!("start at {} offset", ctx.offset());

        if let Some((x, y)) = p0.coordinates_values() {
            if x == C::Base::ZERO && y == C::Base::ZERO {
                error!("point cannot be zero");
                return Err(Error::Synthesis);
            }
        }

        let split_len = cmp::min(scalar_bits.len(), (C::Base::NUM_BITS - 2) as usize);
        let (incomplete_bits, complete_bits) = scalar_bits.split_at(split_len);

        let mut acc = p0.clone();
        // # Safety:
        // (1) assume p0 is not infinity
        // assume first bit of scalar_bits is 1 for now
        // so we can use unsafe_add later
        let mut p = unsafe { self.gate.unchecked_double(ctx, p0) }.inspect_err(|err| {
            error!("while unchecked_double: {err:?}");
        })?;

        // the size of incomplete_bits ensures a + b != 0
        for bit in incomplete_bits.iter().skip(1) {
            // # Safety:
            // (1) assume p0 is not infinity
            // assume first bit of scalar_bits is 1 for now
            // so we can use unsafe_add later
            let sum = unsafe { self.gate.unchecked_add(ctx, &acc, &p) }.inspect_err(|err| {
                error!("while unchecked_add: {err:?}");
            })?;
            acc = AssignedPoint {
                x: self
                    .gate
                    .conditional_select(ctx, &sum.x, &acc.x, bit)
                    .inspect_err(|err| error!("conditional select x: {err:?}"))?,
                y: self
                    .gate
                    .conditional_select(ctx, &sum.y, &acc.y, bit)
                    .inspect_err(|err| error!("conditional select x: {err:?}"))?,
            };
            // # Safety:
            // (1) assume p0 is not infinity
            // assume first bit of scalar_bits is 1 for now
            // so we can use unsafe_add later
            p = unsafe { self.gate.unchecked_double(ctx, &p) }
                .inspect_err(|err| error!("while unchecked double in cycle: {err:?}"))?;
        }

        // make correction if first bit is 0
        acc = {
            let acc_minus_initial = {
                let neg = self
                    .negate(ctx, p0)
                    .inspect_err(|err| error!("while negate: {err:?}"))?;
                self.add(ctx, &acc, &neg)
                    .inspect_err(|err| error!("while add acc & neg: {err:?}"))?
            };
            AssignedPoint {
                x: self
                    .gate
                    .conditional_select(ctx, &acc.x, &acc_minus_initial.x, &scalar_bits[0])
                    .inspect_err(|err| error!("while conditional select 'x': {err:?}"))?,
                y: self
                    .gate
                    .conditional_select(ctx, &acc.y, &acc_minus_initial.y, &scalar_bits[0])
                    .inspect_err(|err| error!("while conditional select 'y': {err:?}"))?,
            }
        };

        // (2) finish the rest bits
        for bit in complete_bits {
            let sum = self
                .add(ctx, &acc, &p)
                .inspect_err(|err| error!("while add acc & p: {err:?}"))?;
            acc = AssignedPoint {
                x: self
                    .gate
                    .conditional_select(ctx, &sum.x, &acc.x, bit)
                    .inspect_err(|err| error!("while conditional select 'x' in acc: {err:?}"))?,
                y: self
                    .gate
                    .conditional_select(ctx, &sum.y, &acc.y, bit)
                    .inspect_err(|err| error!("while conditional select 'y' in acc: {err:?}"))?,
            };
            p = self
                .double(ctx, &p)
                .inspect_err(|err| error!("while double at the end: {err:?}"))?;
        }

        Ok(acc)
    }
}

/// Auxiliary class that performs the off-circuit version of ecc gadget calculations
#[derive(Clone, Debug)]
pub(crate) struct Point<C: CurveAffine> {
    x: C::Base,
    y: C::Base,
    is_inf: bool,
}
impl<C: CurveAffine> From<C> for Point<C> {
    fn from(value: C) -> Self {
        let c = value.coordinates().unwrap();

        Self {
            x: *c.x(),
            y: *c.y(),
            is_inf: value.is_identity().into(),
        }
    }
}

impl<C: CurveAffine> Point<C> {
    pub fn into_curve(self) -> C {
        let Self { x, y, is_inf: _ } = self;
        C::from_xy(x, y).unwrap()
    }
    pub fn into_pair(self) -> (C::Base, C::Base) {
        (self.x, self.y)
    }
}

impl<C: CurveAffine> Point<C> {
    fn default() -> Self {
        Self {
            x: C::Base::ZERO,
            y: C::Base::ZERO,
            is_inf: true,
        }
    }

    /// Add any two points
    pub fn add(&self, other: &Point<C>) -> Self {
        if self.x == other.x {
            // If self == other then call double
            if self.y == other.y {
                self.double()
            } else {
                // if self.x == other.x and self.y != other.y then return infinity
                Self {
                    x: C::Base::ZERO,
                    y: C::Base::ZERO,
                    is_inf: true,
                }
            }
        } else {
            self.add_internal(other)
        }
    }

    /// Add two different points
    pub fn add_internal(&self, other: &Point<C>) -> Self {
        if self.is_inf {
            return other.clone();
        }

        if other.is_inf {
            return self.clone();
        }

        let lambda = (other.y - self.y) * (other.x - self.x).invert().unwrap();
        let x = lambda * lambda - self.x - other.x;
        let y = lambda * (self.x - x) - self.y;
        Self {
            x,
            y,
            is_inf: false,
        }
    }

    pub fn double(&self) -> Self {
        if self.is_inf {
            return Self {
                x: C::Base::ZERO,
                y: C::Base::ZERO,
                is_inf: true,
            };
        }

        let lambda = C::Base::from(3)
            * self.x
            * self.x
            * ((C::Base::ONE + C::Base::ONE) * self.y).invert().unwrap();
        let x = lambda * lambda - self.x - self.x;
        let y = lambda * (self.x - x) - self.y;
        Self {
            x,
            y,
            is_inf: false,
        }
    }

    pub fn scalar_mul<F: PrimeFieldBits>(&self, scalar: &F) -> Self {
        let mut res = Self {
            x: C::Base::ZERO,
            y: C::Base::ZERO,
            is_inf: true,
        };

        let bits = scalar.to_le_bits();
        for i in (0..bits.len()).rev() {
            res = res.double();
            if bits[i] {
                res = self.add(&res);
            }
        }
        res
    }

    fn random_vartime() -> Self {
        loop {
            let x = C::Base::random(&mut OsRng);
            let y = (x.square() * x + C::b()).sqrt();
            if y.is_some().unwrap_u8() == 1 {
                return Self {
                    x,
                    y: y.unwrap(),
                    is_inf: false,
                };
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::num::NonZeroUsize;

    use halo2_proofs::{circuit::Value, halo2curves::ff::PrimeFieldBits};
    use rand_core::OsRng;
    use tracing_test::traced_test;

    use super::*;
    use crate::{
        create_and_verify_proof,
        ff::Field,
        halo2_proofs::{
            circuit::{Chip, Layouter, SimpleFloorPlanner},
            plonk::{Circuit, Column, ConstraintSystem, Instance},
        },
        halo2curves::pasta::{pallas, EqAffine, Fp, Fq},
        main_gate::{MainGate, MainGateConfig},
        run_mock_prover_test,
        util::ScalarToBase,
    };

    const T: usize = 4;
    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
        config: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    enum TestCase {
        Add,
        ScalarMul,
    }

    struct TestCircuit<C: CurveAffine<Base = F>, F: PrimeFieldBits> {
        a: Point<C>,
        b: Point<C>,
        lambda: C::Scalar,
        test_case: TestCase,
    }
    impl<C: CurveAffine<Base = F>, F: PrimeFieldBits> TestCircuit<C, F> {
        fn new(a: Point<C>, b: Point<C>, lambda: C::Scalar, test_case: TestCase) -> Self {
            Self {
                a,
                b,
                lambda,
                test_case,
            }
        }
    }

    impl<C: CurveAffine<Base = F>, F: PrimeFieldBits> Circuit<C::Base> for TestCircuit<C, F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            TestCircuit::new(
                Point::default(),
                Point::default(),
                C::Scalar::ZERO,
                TestCase::Add,
            )
        }

        fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let config = MainGate::configure(meta);
            Self::Config { config, instance }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<C::Base>,
        ) -> Result<(), Error> {
            let ecc_chip = EccChip::<C, MainGate<F, T>>::new(config.config);
            let output = layouter.assign_region(
                || "ecc test circuit",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    let ax = ctx.assign_advice(
                        || "a.x",
                        ecc_chip.gate.config().state[0],
                        Value::known(self.a.x),
                    )?;
                    let ay = ctx.assign_advice(
                        || "a.y",
                        ecc_chip.gate.config().state[1],
                        Value::known(self.a.y),
                    )?;
                    let a = AssignedPoint { x: ax, y: ay };
                    match self.test_case {
                        TestCase::Add => {
                            let bx = ctx.assign_advice(
                                || "b.x",
                                ecc_chip.gate.config().state[2],
                                Value::known(self.b.x),
                            )?;
                            let by = ctx.assign_advice(
                                || "b.y",
                                ecc_chip.gate.config().state[3],
                                Value::known(self.b.y),
                            )?;
                            let b = AssignedPoint { x: bx, y: by };
                            ctx.next();
                            ecc_chip.add(ctx, &a, &b)
                        }
                        TestCase::ScalarMul => {
                            let lambda: C::Base = C::scalar_to_base(&self.lambda).unwrap();
                            let bit_len =
                                NonZeroUsize::new(lambda.to_le_bits().len()).expect("Non Zero");
                            let lambda = ctx.assign_advice(
                                || "lambda",
                                ecc_chip.gate.config().state[2],
                                Value::known(lambda),
                            )?;
                            ctx.next();
                            let bits = ecc_chip.gate.le_num_to_bits(ctx, lambda, bit_len)?;
                            ecc_chip.scalar_mul(ctx, &a, &bits)
                        }
                    }
                },
            )?;
            layouter.constrain_instance(output.x.cell(), config.instance, 0)?;
            layouter.constrain_instance(output.y.cell(), config.instance, 1)?;
            Ok(())
        }
    }

    #[traced_test]
    #[test]
    #[ignore = "cause it takes a few minutes to run"]
    fn test_ecc_op() {
        println!("-----running ECC Circuit-----");
        let p: Point<pallas::Affine> = Point::random_vartime();
        let q: Point<pallas::Affine> = Point {
            x: Fp::ZERO,
            y: Fp::ZERO,
            is_inf: true,
        };
        //let q: Point<pallas::Affine> = Point { x: p.x, y: -p.y, is_inf: false };
        let lambda = Fq::random(&mut OsRng);
        let r = p.scalar_mul(&lambda);
        let circuit = TestCircuit::new(p, q, lambda, TestCase::ScalarMul);
        let public_inputs: &[&[Fp]] = &[&[r.x, r.y]];

        let K: u32 = 14;
        create_and_verify_proof!(IPA, K, circuit, public_inputs, EqAffine);
        println!("-----ECC circuit works fine-----");
    }

    #[test]
    fn test_ecc_mock() {
        let K: u32 = 14;
        let p: Point<pallas::Affine> = Point::random_vartime();
        let q: Point<pallas::Affine> = Point {
            x: Fp::ZERO,
            y: Fp::ZERO,
            is_inf: true,
        };
        // here lambda = p - 1 , p is base field size
        //let lambda = Fq::from_raw([11037532056220336128, 2469829653914515739, 0, 4611686018427387904]);
        let lambda = Fq::from(1);
        let r = p.scalar_mul(&lambda);
        let circuit = TestCircuit::new(p, q, lambda, TestCase::ScalarMul);
        let public_inputs = vec![vec![r.x, r.y]];
        run_mock_prover_test!(K, circuit, public_inputs);
    }
}
