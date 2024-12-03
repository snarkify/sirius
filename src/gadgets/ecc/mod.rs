use std::{cmp, marker::PhantomData};

use tracing::*;

use crate::{
    halo2_proofs::{
        arithmetic::{CurveAffine, Field},
        circuit::Chip,
        halo2curves::ff::PrimeField,
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
        p: &AssignedPoint<C>,
        q: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Error> {
        let is_p_iden = self
            .gate
            .is_infinity_point(ctx, &p.x, &p.y)
            .inspect_err(|err| error!("while is_infinity p: {err:?}"))?;
        let is_q_iden = self
            .gate
            .is_infinity_point(ctx, &q.x, &q.y)
            .inspect_err(|err| error!("while is_infinity q: {err:?}"))?;
        let is_equal_x = self
            .gate
            .is_equal_term(ctx, &p.x, &q.x)
            .inspect_err(|err| error!("while is_equal p.q == q.x: {err:?}"))?;
        let is_equal_y = self
            .gate
            .is_equal_term(ctx, &p.y, &q.y)
            .inspect_err(|err| error!("while is_infinity p.y == q.y: {err:?}"))?;

        let inf = self
            .gate
            .assign_point::<C, _>(ctx, || "inf", None)
            .inspect_err(|err| error!("while assigned point `inf`: {err:?}"))?;
        // # Safety
        // We check at the bottom of this fn, what p.x == q.x
        let r = unsafe { self.gate.unchecked_add(ctx, p, q) }
            .inspect_err(|err| error!("while unchecked add p & q: {err:?}"))?;
        let p2 = self.double(ctx, p)?;

        let x1 = self
            .gate
            .conditional_select(ctx, &p2.x, &inf.x, &is_equal_y)
            .inspect_err(|err| error!("while conditional select p2.x & inf.x: {err:?}"))?;
        let y1 = self
            .gate
            .conditional_select(ctx, &p2.y, &inf.y, &is_equal_y)
            .inspect_err(|err| error!("while conditional select p2.y & inf.y: {err:?}"))?;
        let x2 = self
            .gate
            .conditional_select(ctx, &x1, &r.x, &is_equal_x)
            .inspect_err(|err| error!("while conditional select x1 & r.x: {err:?}"))?;
        let y2 = self
            .gate
            .conditional_select(ctx, &y1, &r.y, &is_equal_x)
            .inspect_err(|err| error!("while conditional select y1 & r.y: {err:?}"))?;
        let x3 = self
            .gate
            .conditional_select(ctx, &p.x, &x2, &is_q_iden)
            .inspect_err(|err| error!("while conditional select p.x & x2: {err:?}"))?;
        let y3 = self
            .gate
            .conditional_select(ctx, &p.y, &y2, &is_q_iden)
            .inspect_err(|err| error!("while conditional select p.y & y2: {err:?}"))?;
        let x = self
            .gate
            .conditional_select(ctx, &q.x, &x3, &is_p_iden)
            .inspect_err(|err| error!("while conditional select q.x & x3: {err:?}"))?;
        let y = self
            .gate
            .conditional_select(ctx, &q.y, &y3, &is_p_iden)
            .inspect_err(|err| error!("while conditional select q.y & y3: {err:?}"))?;

        Ok(AssignedPoint { x, y })
    }

    fn double(
        &self,
        ctx: &mut RegionCtx<'_, C::Base>,
        p: &AssignedPoint<C>,
    ) -> Result<AssignedPoint<C>, Error> {
        let is_inf = self.gate.is_infinity_point(ctx, &p.x, &p.y)?;
        let inf = self.gate.assign_point::<C, _>(ctx, || "inf", None)?;
        // Safety:
        // This value will be used only if `is_inf = false`
        // `is_inf` false, only if p.x & p.y not zero
        let p2 = unsafe { self.gate.unchecked_double(ctx, p) }?;

        let x = self.gate.conditional_select(ctx, &inf.x, &p2.x, &is_inf)?;
        let y = self.gate.conditional_select(ctx, &inf.y, &p2.y, &is_inf)?;
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
        p0: &AssignedPoint<C>,
        scalar_bits: &[AssignedValue<C::Base>],
    ) -> Result<AssignedPoint<C>, Error> {
        let split_len = cmp::min(scalar_bits.len(), (C::Base::NUM_BITS - 2) as usize);
        let (incomplete_bits, complete_bits) = scalar_bits.split_at(split_len);

        let mut acc = p0.clone();
        // # Safety:
        // (1) assume p0 is not infinity
        // assume first bit of scalar_bits is 1 for now
        // so we can use unsafe_add later
        let mut p = unsafe { self.gate.unchecked_double(ctx, p0) }?;

        // the size of incomplete_bits ensures a + b != 0
        for bit in incomplete_bits.iter().skip(1) {
            // # Safety:
            // (1) assume p0 is not infinity
            // assume first bit of scalar_bits is 1 for now
            // so we can use unsafe_add later
            let tmp = unsafe { self.gate.unchecked_add(ctx, &acc, &p) }?;
            acc = AssignedPoint {
                x: self.gate.conditional_select(ctx, &tmp.x, &acc.x, bit)?,
                y: self.gate.conditional_select(ctx, &tmp.y, &acc.y, bit)?,
            };
            // # Safety:
            // (1) assume p0 is not infinity
            // assume first bit of scalar_bits is 1 for now
            // so we can use unsafe_add later
            p = unsafe { self.gate.unchecked_double(ctx, &p) }?;
        }

        // make correction if first bit is 0
        let res: AssignedPoint<C> = {
            let acc_minus_initial = {
                let neg = self.negate(ctx, p0)?;
                self.add(ctx, &acc, &neg)?
            };
            let x =
                self.gate
                    .conditional_select(ctx, &acc.x, &acc_minus_initial.x, &scalar_bits[0])?;
            let y =
                self.gate
                    .conditional_select(ctx, &acc.y, &acc_minus_initial.y, &scalar_bits[0])?;
            AssignedPoint { x, y }
        };

        // (2) modify acc and p if p0 is infinity
        let infp = self.gate.assign_point::<C, _>(ctx, || "infp", None)?;
        let is_p_iden = self.gate.is_infinity_point(ctx, &p0.x, &p0.y)?;
        let x = self
            .gate
            .conditional_select(ctx, &infp.x, &res.x, &is_p_iden)?;
        let y = self
            .gate
            .conditional_select(ctx, &infp.y, &res.y, &is_p_iden)?;
        acc = AssignedPoint { x, y };
        let x = self
            .gate
            .conditional_select(ctx, &infp.x, &p.x, &is_p_iden)?;
        let y = self
            .gate
            .conditional_select(ctx, &infp.y, &p.y, &is_p_iden)?;
        p = AssignedPoint { x, y };

        // (3) finish the rest bits
        for bit in complete_bits {
            let tmp = self.add(ctx, &acc, &p)?;
            let x = self.gate.conditional_select(ctx, &tmp.x, &acc.x, bit)?;
            let y = self.gate.conditional_select(ctx, &tmp.y, &acc.y, bit)?;
            acc = AssignedPoint { x, y };
            p = self.double(ctx, &p)?;
        }

        Ok(acc)
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
