use std::{array, iter, marker::PhantomData, num::NonZeroUsize};

use halo2_proofs::{
    circuit::{AssignedCell, Cell, Chip, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector},
    poly::Rotation,
};
use itertools::Itertools;

use crate::{
    ff::{PrimeField, PrimeFieldBits},
    gadgets::ecc::AssignedPoint,
    halo2curves::{Coordinates, CurveAffine},
    util::{self, normalize_trailing_zeros},
};

pub type AssignedValue<F> = AssignedCell<F, F>;
pub type AssignedBit<F> = AssignedCell<F, F>;

#[derive(Debug)]
pub struct RegionCtx<'a, F: PrimeField> {
    pub region: Region<'a, F>,
    pub offset: usize,
}

impl<'a, F: PrimeField> RegionCtx<'a, F> {
    pub fn new(region: Region<'a, F>, offset: usize) -> Self {
        RegionCtx { region, offset }
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn into_region(self) -> Region<'a, F> {
        self.region
    }

    pub fn enable_selector(&mut self, selector: &Selector) -> Result<(), Error> {
        let offset = self.offset();
        selector.enable(&mut self.region, offset)
    }

    pub fn assign_fixed<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Fixed>,
        value: F,
    ) -> Result<AssignedValue<F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region
            .assign_fixed(annotation, column, self.offset, || Value::known(value))
    }

    pub fn assign_advice<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        value: Value<F>,
    ) -> Result<AssignedValue<F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region
            .assign_advice(annotation, column, self.offset, || value)
    }

    pub fn assign_advice_from<A, AR>(
        &mut self,
        annotation: A,
        dst: Column<Advice>,
        src: impl AssignAdviceFrom<'a, F>,
    ) -> Result<AssignedCell<F, F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        AssignAdviceFrom::assign_advice_from(self, annotation, dst, src)
    }

    pub fn assign_advice_from_instance<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        instance: Column<Instance>,
        instance_offset: usize,
    ) -> Result<AssignedValue<F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region.assign_advice_from_instance(
            annotation,
            instance,
            instance_offset,
            column,
            self.offset,
        )
    }

    pub fn constrain_equal(&mut self, cell_0: Cell, cell_1: Cell) -> Result<(), Error> {
        self.region.constrain_equal(cell_0, cell_1)
    }

    pub fn next(&mut self) {
        self.offset += 1
    }

    pub(crate) fn reset(&mut self, offset: usize) {
        self.offset = offset
    }
}

mod assign_advice_from {
    use super::*;

    pub trait AssignAdviceFrom<'a, F: PrimeField> {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>;
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for &AssignedCell<F, F> {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            let cell = ctx.assign_advice(annotation, dst, src.value().map(|f| *f))?;
            ctx.constrain_equal(cell.cell(), src.cell())?;
            Ok(cell)
        }
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for AssignedCell<F, F> {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            AssignAdviceFrom::assign_advice_from(ctx, annotation, dst, &src)
        }
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for &F {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            AssignAdviceFrom::assign_advice_from(ctx, annotation, dst, *src)
        }
    }

    impl<'a, F: PrimeField> AssignAdviceFrom<'a, F> for F {
        fn assign_advice_from<A, AR>(
            ctx: &mut RegionCtx<'a, F>,
            annotation: A,
            dst: Column<Advice>,
            src: Self,
        ) -> Result<AssignedCell<F, F>, Error>
        where
            A: Fn() -> AR,
            AR: Into<String>,
        {
            let cell = ctx.assign_advice(annotation, dst, Value::known(src))?;
            Ok(cell)
        }
    }
}
pub use assign_advice_from::AssignAdviceFrom;

#[derive(Clone, Debug)]
pub enum WrapValue<F: PrimeField> {
    Assigned(AssignedValue<F>),
    Unassigned(Value<F>),
    Zero,
}

impl<F: PrimeField> WrapValue<F> {
    pub fn from_point<C>(input: &C) -> Option<(Self, Self)>
    where
        C: CurveAffine<Base = F>,
    {
        let coordinates: Coordinates<_> = Option::from(input.coordinates())?;
        Some((
            Self::Unassigned(Value::known(*coordinates.x())),
            Self::Unassigned(Value::known(*coordinates.y())),
        ))
    }

    pub fn from_assigned_point<C>(input: &AssignedPoint<C>) -> [Self; 2]
    where
        C: CurveAffine<Base = F>,
    {
        [
            Self::Assigned(input.x.clone()),
            Self::Assigned(input.y.clone()),
        ]
    }

    pub fn value(&self) -> Value<F> {
        match self {
            WrapValue::Assigned(v) => v.value().copied(),
            WrapValue::Unassigned(v) => *v,
            WrapValue::Zero => Value::known(F::ZERO),
        }
    }
}

impl<F: PrimeField> From<Value<F>> for WrapValue<F> {
    fn from(val: Value<F>) -> Self {
        WrapValue::Unassigned(val)
    }
}

impl<F: PrimeField> From<AssignedValue<F>> for WrapValue<F> {
    fn from(val: AssignedValue<F>) -> Self {
        WrapValue::Assigned(val)
    }
}

impl<F: PrimeField> From<F> for WrapValue<F> {
    fn from(val: F) -> Self {
        WrapValue::Unassigned(Value::known(val))
    }
}

impl<F: PrimeField> From<&AssignedValue<F>> for WrapValue<F> {
    fn from(val: &AssignedValue<F>) -> Self {
        WrapValue::Assigned(val.clone())
    }
}

const MULTIPLICATION_COUNT: usize = 2;

#[derive(Clone, Debug)]
pub struct MainGateConfig<const T: usize> {
    pub(crate) state: [Column<Advice>; T],
    pub(crate) input: Column<Advice>,
    pub(crate) out: Column<Advice>,
    pub(crate) q_m: [Column<Fixed>; MULTIPLICATION_COUNT],
    // for linear term
    pub(crate) q_1: [Column<Fixed>; T],
    // for quintic term
    pub(crate) q_5: [Column<Fixed>; T],
    pub(crate) q_i: Column<Fixed>,
    pub(crate) q_o: Column<Fixed>,
    pub(crate) rc: Column<Fixed>,
}

impl<const T: usize> MainGateConfig<T> {
    /// Names the columns in the `MainGateConfig` for easier debugging and more informative error messages.
    ///
    /// This function is particularly useful during interactions within a region. By naming each column,
    /// it helps to identify them quickly in error messages or debugging output, making the debugging
    /// process more intuitive and efficient.
    pub fn name_columns<F: PrimeField>(&self, region: &mut Region<'_, F>) {
        // Internal macro to name a column based on field name
        macro_rules! name_column {
            ($field:ident[$index:expr]) => {
                let name = format!("{}[{}]", stringify!($field), $index);
                region.name_column(|| &name, self.$field[$index]);
            };
            ($field:ident) => {
                region.name_column(|| stringify!($field), self.$field);
            };
        }

        for i in 0..T {
            name_column!(state[i]);
            name_column!(q_1[i]);
            name_column!(q_5[i]);
        }

        name_column!(input);
        name_column!(out);
        name_column!(q_i);
        name_column!(q_o);

        for i in 0..MULTIPLICATION_COUNT {
            name_column!(q_m[i]);
        }

        name_column!(rc);
    }

    /// Converts the current `MainGateConfig` to a new configuration with a smaller size `N`.
    ///
    /// This method is used to adapt the main gate configuration of a circuit to a different size,
    /// which can be necessary for various circuit optimizations or specific implementations.
    /// It attempts to reconfigure the existing columns and constants to match the new size
    /// while preserving the original configuration's structure and values.
    ///
    /// # Type Parameters
    ///
    /// * `N`: The new, smaller size for the main gate configuration. This determines the number
    ///   of columns and constants in the resized configuration. `N` must be less than or equal
    ///   to `T`.
    ///
    /// # Returns
    ///
    /// If `N > T` return `None`
    /// If `N <= T` return `Some(MainGateConfig<N>)`
    pub fn into_smaller_size<const N: usize>(&self) -> Option<MainGateConfig<N>> {
        if N > T {
            return None;
        }

        Some(MainGateConfig::<N> {
            state: self.state[..N].try_into().ok()?,
            input: self.input,
            out: self.out,
            q_m: self.q_m,
            q_1: self.q_1[..N].try_into().ok()?,
            q_5: self.q_5[..N].try_into().ok()?,
            q_i: self.q_i,
            q_o: self.q_o,
            rc: self.rc,
        })
    }

    /// Iterated over all fixed columns in config
    pub fn iter_fixed_columns(&self) -> impl Clone + Iterator<Item = &Column<Fixed>> {
        self.q_1
            .iter()
            .chain(self.q_5.iter())
            .chain(self.q_m.iter())
            .chain(iter::once(&self.q_i))
            .chain(iter::once(&self.q_o))
            .chain(iter::once(&self.rc))
    }

    /// Iterated over all advice columns in config
    pub fn iter_advice_columns(&self) -> impl Clone + Iterator<Item = &Column<Advice>> {
        self.state
            .iter()
            .chain(iter::once(&self.input))
            .chain(iter::once(&self.out))
    }

    /// Return an auxiliary struct that allow to cyclically assign values to any [`Advice`] column,
    /// inrement rows via [`RegionCtx::next`] when run out of columns.
    pub fn advice_cycle_assigner<'s, F: PrimeField>(&'s self) -> impl 's + AdviceCyclicAssignor<F> {
        AdviceCyclicAssignorIter::<'s, _> {
            iter: self.iter_advice_columns().enumerate().cycle(),
            first_pass: true,
        }
    }

    /// Return an auxiliary struct that allow to cyclically assign values to any [`Fixed`] column,
    /// inrement rows via [`RegionCtx::next`] when run out of columns.
    pub fn fixed_cycle_assigner<'s, F: PrimeField>(&'s self) -> impl 's + FixedCyclicAssignor<F> {
        FixedCyclicAssignorIter::<'s, _> {
            iter: self.iter_fixed_columns().enumerate().cycle(),
            first_pass: true,
        }
    }
}

// Macro to create structs and impl for both fixed and advice columns
macro_rules! create_column_cycle {
    (
        $struct_name:ident,
        $trait_name:ident,
        $column_type:ty,
        $assign_next_fn_name:ident,
        $assign_point_fn_name:ident,
        $assign_next_collection_fn_name:ident,
        $region_assign_fn:ident,
        $value_wrapper:expr
    ) => {
        struct $struct_name<'a, I: Iterator<Item = (usize, &'a Column<$column_type>)>> {
            iter: I,
            first_pass: bool,
        }

        pub trait $trait_name<F: PrimeField> {
            fn $assign_next_fn_name<AR: Into<String>>(
                &mut self,
                region: &mut RegionCtx<'_, F>,
                annotation: impl Fn() -> AR,
                value: F,
            ) -> Result<AssignedCell<F, F>, halo2_proofs::plonk::Error>;

            fn $assign_next_collection_fn_name<AR: Into<String>>(
                &mut self,
                region: &mut RegionCtx<'_, F>,
                annotation: impl Clone + Fn() -> AR,
                values: impl Iterator<Item = F>,
            ) -> Result<Vec<AssignedCell<F, F>>, halo2_proofs::plonk::Error>;

            fn $assign_point_fn_name<C: CurveAffine, AR: Into<String>>(
                &mut self,
                region: &mut RegionCtx<'_, C::Base>,
                annotation: impl Fn() -> AR,
                point: &C,
            ) -> Result<AssignedPoint<C>, halo2_proofs::plonk::Error>;
        }

        impl<'a, I, F> $trait_name<F> for $struct_name<'a, I>
        where
            I: Iterator<Item = (usize, &'a Column<$column_type>)>,
            F: PrimeField,
        {
            fn $assign_next_fn_name<AR: Into<String>>(
                &mut self,
                region: &mut RegionCtx<'_, F>,
                annotation: impl Fn() -> AR,
                value: F,
            ) -> Result<AssignedCell<F, F>, halo2_proofs::plonk::Error> {
                let (index, column) = self.iter.by_ref().next().expect("Safe because cycle");

                if !self.first_pass && index == 0 {
                    region.next();
                }

                self.first_pass = false;

                let wrapper = $value_wrapper;
                region.$region_assign_fn(annotation, *column, wrapper(value))
            }

            fn $assign_next_collection_fn_name<AR: Into<String>>(
                &mut self,
                region: &mut RegionCtx<'_, F>,
                annotation: impl Clone + Fn() -> AR,
                values: impl Iterator<Item = F>,
            ) -> Result<Vec<AssignedCell<F, F>>, halo2_proofs::plonk::Error> {
                values
                    .map(|val| self.$assign_next_fn_name(region, annotation.clone(), val))
                    .collect()
            }

            fn $assign_point_fn_name<C: CurveAffine, AR: Into<String>>(
                &mut self,
                region: &mut RegionCtx<'_, C::Base>,
                annotation: impl Fn() -> AR,
                point: &C,
            ) -> Result<AssignedPoint<C>, halo2_proofs::plonk::Error> {
                let annotation = annotation().into();
                let coordinates = point.coordinates().unwrap();

                Ok(AssignedPoint {
                    x: self.$assign_next_fn_name(
                        region,
                        || format!("{}.x", annotation),
                        *coordinates.x(),
                    )?,
                    y: self.$assign_next_fn_name(
                        region,
                        || format!("{}.y", annotation),
                        *coordinates.y(),
                    )?,
                })
            }
        }
    };
}

create_column_cycle!(
    FixedCyclicAssignorIter,
    FixedCyclicAssignor,
    Fixed,
    assign_next_fixed,
    assign_next_fixed_point,
    assign_all_fixed,
    assign_fixed,
    |value| value
);

create_column_cycle!(
    AdviceCyclicAssignorIter,
    AdviceCyclicAssignor,
    Advice,
    assign_next_advice,
    assign_next_advice_point,
    assign_all_advice,
    assign_advice,
    |value| Value::known(value)
);

#[derive(Debug)]
pub struct MainGate<F: PrimeField, const T: usize> {
    config: MainGateConfig<T>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField, const T: usize> Chip<F> for MainGate<F, T> {
    type Config = MainGateConfig<T>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField, const T: usize> MainGate<F, T> {
    pub fn new(config: MainGateConfig<T>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MainGateConfig<T> {
        assert!(T >= 2);
        let state = array::from_fn(|_| meta.advice_column());
        let input = meta.advice_column();
        let out = meta.advice_column();
        let q_1 = array::from_fn(|_| meta.fixed_column());
        let q_5 = array::from_fn(|_| meta.fixed_column());
        let q_m = array::from_fn(|_| meta.fixed_column());
        let q_i = meta.fixed_column();
        let q_o = meta.fixed_column();
        let rc = meta.fixed_column();

        state.map(|s| {
            meta.enable_equality(s);
        });
        meta.enable_equality(input);
        meta.enable_equality(out);

        let pow_5 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2 * v
        };

        meta.create_gate("q_m[0]*s[0]*s[1] + q_m[1]*s[2]*s[3] + sum_i(q_1[i]*s[i]) + sum_i(q_5[i]*s[i]^5) + rc + q_i*input + q_o*out=0", |meta|{
            let state = state.into_iter().map(|s| meta.query_advice(s, Rotation::cur())).collect::<Vec<_>>();
            let input = meta.query_advice(input, Rotation::cur());
            let out = meta.query_advice(out, Rotation::cur());
            let q_1 = q_1.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_5 = q_5.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_m = q_m.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_i = meta.query_fixed(q_i, Rotation::cur());
            let q_o = meta.query_fixed(q_o, Rotation::cur());
            let rc = meta.query_fixed(rc, Rotation::cur());

            let mut init_term = q_m[0].clone() * state[0].clone() * state[1].clone() + q_i * input + rc + q_o * out;

            if T >= 4 {
                init_term = q_m[1].clone() * state[2].clone() * state[3].clone() + init_term;
            }

            vec![itertools::multizip((state, q_1, q_5))
                .map(|(s, q1, q5)| {
                    q1 * s.clone()  +  q5 * pow_5(s)
                })
                .fold(init_term, |acc, item| {
                    acc + item
                })
            ]
        });

        MainGateConfig {
            state,
            input,
            out,
            q_m,
            q_1,
            q_5,
            q_i,
            q_o,
            rc,
        }
    }

    // helper function for some usecases: no copy constraints, only return out cell
    // state: (q_1, q_m, state), out: (q_o, out)
    pub fn apply(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: (Option<Vec<F>>, Option<Vec<F>>, Option<Vec<WrapValue<F>>>),
        rc: Option<F>,
        out: (F, WrapValue<F>),
    ) -> Result<AssignedValue<F>, Error> {
        if let Some(q_1) = state.0 {
            for (i, val) in q_1.iter().enumerate() {
                ctx.assign_fixed(|| "q_1", self.config.q_1[i], *val)?;
            }
        }

        if let Some(q_m) = state.1 {
            q_m.iter()
                .zip(self.config.q_m.iter())
                .try_for_each(|(val, column)| {
                    ctx.assign_fixed(|| "q_m", *column, *val)?;
                    Result::<_, Error>::Ok(())
                })?;
        }

        if let Some(state) = state.2 {
            for (i, val) in state.iter().enumerate() {
                match val {
                    WrapValue::Unassigned(vv) => {
                        ctx.assign_advice(|| "state", self.config.state[i], *vv)?;
                    }
                    WrapValue::Assigned(avv) => {
                        let si = ctx.assign_advice(
                            || "state",
                            self.config.state[i],
                            avv.value().copied(),
                        )?;
                        ctx.constrain_equal(si.cell(), avv.cell())?;
                    }
                    _ => {}
                }
            }
        }

        if let Some(rc_val) = rc {
            ctx.assign_fixed(|| "rc", self.config.rc, rc_val)?;
        }

        ctx.assign_fixed(|| "q_o", self.config.q_o, out.0)?;

        let res = match out.1 {
            WrapValue::Unassigned(vv) => ctx.assign_advice(|| "out", self.config.out, vv)?,
            WrapValue::Assigned(avv) => {
                let out = ctx.assign_advice(|| "out", self.config.out, avv.value().copied())?;
                ctx.constrain_equal(out.cell(), avv.cell())?;
                out
            }
            WrapValue::Zero => {
                unimplemented!() // this is not allowed
            }
        };
        ctx.next();
        Ok(res)
    }

    pub fn apply_with_input(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: (Option<Vec<F>>, Option<F>, Option<Vec<WrapValue<F>>>),
        input: (Option<F>, Option<WrapValue<F>>),
        out: (F, WrapValue<F>),
    ) -> Result<AssignedValue<F>, Error> {
        if let Some(q_1) = state.0 {
            for (i, val) in q_1.iter().enumerate() {
                ctx.assign_fixed(|| "q_1", self.config.q_1[i], *val)?;
            }
        }
        if let Some(q_m_val) = state.1 {
            ctx.assign_fixed(|| "q_m", self.config.q_m[0], q_m_val)?;
        }
        if let Some(state) = state.2 {
            for (i, val) in state.iter().enumerate() {
                match val {
                    WrapValue::Unassigned(vv) => {
                        ctx.assign_advice(|| "state", self.config.state[i], *vv)?;
                    }
                    WrapValue::Assigned(avv) => {
                        let si = ctx.assign_advice(
                            || "state",
                            self.config.state[i],
                            avv.value().copied(),
                        )?;
                        ctx.constrain_equal(si.cell(), avv.cell())?;
                    }
                    _ => {}
                }
            }
        }

        if let Some(q_i) = input.0 {
            ctx.assign_fixed(|| "rc", self.config.q_i, q_i)?;
        }
        if let Some(inp) = input.1 {
            match inp {
                WrapValue::Unassigned(vv) => {
                    ctx.assign_advice(|| "input", self.config.input, vv)?;
                }
                WrapValue::Assigned(avv) => {
                    let si =
                        ctx.assign_advice(|| "input", self.config.input, avv.value().copied())?;
                    ctx.constrain_equal(si.cell(), avv.cell())?;
                }
                _ => {}
            }
        }

        ctx.assign_fixed(|| "q_o", self.config.q_o, out.0)?;

        let res = match out.1 {
            WrapValue::Unassigned(vv) => ctx.assign_advice(|| "out", self.config.out, vv)?,
            WrapValue::Assigned(avv) => {
                let out = ctx.assign_advice(|| "out", self.config.out, avv.value().copied())?;
                ctx.constrain_equal(out.cell(), avv.cell())?;
                out
            }
            WrapValue::Zero => {
                unimplemented!() // this is not allowed
            }
        };
        ctx.next();
        Ok(res)
    }

    // calculate sum_{i=0}^d r^i terms[i]
    pub fn random_linear_combination(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        terms: Vec<F>,
        r: F,
    ) -> Result<AssignedValue<F>, Error> {
        let d = terms.len();
        let mut out: Option<AssignedValue<F>> = None;
        for i in 1..d {
            let lhs_val = Value::known(terms[d - 1 - i]);
            let rhs_val = if i == 1 {
                Value::known(terms[d - i])
            } else {
                out.as_ref().unwrap().value().copied()
            };
            let r_val = Value::known(r);
            ctx.assign_advice(|| "input", self.config.input, lhs_val)?;
            let rhs = ctx.assign_advice(|| "s[1]", self.config.state[1], rhs_val)?;
            if out.is_some() {
                ctx.constrain_equal(rhs.cell(), out.unwrap().cell())?;
            }
            ctx.assign_advice(|| "s[0]", self.config.state[0], r_val)?;
            out = Some(ctx.assign_advice(
                || "out=s[0]*s[1]+input",
                self.config.out,
                lhs_val + r_val * rhs_val,
            )?);

            ctx.assign_fixed(|| "q_i", self.config.q_i, F::ONE)?;
            ctx.assign_fixed(|| "q_m", self.config.q_m[0], F::ONE)?;
            ctx.assign_fixed(|| "q_o", self.config.q_o, -F::ONE)?;
            ctx.next();
        }
        Ok(out.unwrap())
    }
}

impl<F: PrimeFieldBits, const T: usize> MainGate<F, T> {
    pub fn assign_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &[bool],
    ) -> Result<Vec<AssignedValue<F>>, Error> {
        bits.iter()
            .map(|bit| self.assign_bit(ctx, Value::known(if *bit { F::ONE } else { F::ZERO })))
            .collect()
    }

    pub fn le_bits_to_num(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &[AssignedValue<F>],
    ) -> Result<AssignedValue<F>, Error> {
        bits.iter()
            .zip(util::get_power_of_two_iter::<F>())
            .chunks(T)
            .into_iter()
            .try_fold(
                self.assign_value(ctx, Value::known(F::ZERO))?,
                |acc, chunk| {
                    let mut acc_value = acc.value().copied();

                    let (bits, shifts) = chunk
                        .map(|(bit, shift)| {
                            acc_value = acc_value + (Value::known(shift) * bit.value());
                            (bit.into(), shift)
                        })
                        .unzip();

                    self.apply_with_input(
                        ctx,
                        (Some(shifts), None, Some(bits)),
                        (Some(F::ONE), Some(acc.into())),
                        (-F::ONE, acc_value.into()),
                    )
                },
            )
    }

    pub fn le_num_to_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        input: AssignedValue<F>,
        bit_len: NonZeroUsize,
    ) -> Result<Vec<AssignedValue<F>>, Error> {
        // TODO: ensure a is less than F.size() - 1

        let mut bits: Vec<bool> = input
            .value()
            .unwrap()
            .map(|a| a.to_le_bits().into_iter().collect())
            .unwrap_or_default();

        normalize_trailing_zeros(&mut bits, bit_len);

        let bits = self.assign_bits(ctx, &bits)?;
        let num = self.le_bits_to_num(ctx, &bits)?;

        assert_eq!(num.value().unwrap(), input.value().unwrap());

        ctx.constrain_equal(input.cell(), num.cell())?;

        Ok(bits)
    }
}

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;
    use crate::{
        halo2curves::pasta::Fp,
        plonk::CompressedGates,
        polynomial::{expression::QueryIndexContext, Expression},
    };

    #[traced_test]
    #[test]
    fn main_gate_size_change() {
        const T: usize = 10;
        const RATE: usize = 2;
        let mut cs = ConstraintSystem::<Fp>::default();
        let config: MainGateConfig<T> = MainGate::configure(&mut cs);

        let _ = config.into_smaller_size::<{ T - 1 }>().unwrap();
        assert!(config.into_smaller_size::<{ T + 1 }>().is_none());
    }

    fn main_gate_expressions() -> (Vec<Vec<Expression<Fp>>>, usize, QueryIndexContext) {
        const T: usize = 2;
        const RATE: usize = 2;
        let mut cs = ConstraintSystem::<Fp>::default();
        let _: MainGateConfig<T> = MainGate::configure(&mut cs);
        let num_selector = cs.num_selectors; // is zero for current main_gate design
        let num_fixed = cs.num_fixed_columns();
        let num_instance = cs.num_instance_columns();
        let num_advice = cs.num_advice_columns();
        let gates: Vec<Vec<Expression<Fp>>> = cs
            .gates()
            .iter()
            .map(|gate| {
                gate.polynomials()
                    .iter()
                    .map(|expr| Expression::from_halo2_expr(expr, num_selector, num_fixed))
                    .collect()
            })
            .collect();
        (
            gates,
            num_instance,
            QueryIndexContext {
                num_fixed,
                num_advice,
                num_selectors: cs.num_selectors,
                num_challenges: cs.num_challenges(),
                num_lookups: 0,
            },
        )
    }

    #[test]
    fn test_main_gate_expr() {
        let (gates, _, _) = main_gate_expressions();
        for (i, gate) in gates.iter().enumerate() {
            for (j, poly) in gate.iter().enumerate() {
                if i == 0 && j == 0 {
                    // i.e. qm * s1_0 * s1_1 + qi * in1 + rc + qo * out1 + q1_0 * s1_0 + q5_0 * s1_0^5
                    // + q1_1 * s1_1 + q5_1 * s1_1^5
                    assert_eq!(
                         poly.to_string(),
                        "Z_4 * Z_9 * Z_10 + Z_6 * Z_11 + Z_8 + Z_7 * Z_12 + Z_0 * Z_9 + Z_2 * Z_9 * Z_9 * Z_9 * Z_9 * Z_9 + Z_1 * Z_10 + Z_3 * Z_10 * Z_10 * Z_10 * Z_10 * Z_10"
                    );
                }
            }
        }
    }

    #[test]
    fn test_main_gate_cross_term() {
        let (gates, _num_instance, mut ctx) = main_gate_expressions();
        let expr = gates[0][0].clone();
        let compressed = CompressedGates::new(&[expr], &mut ctx);

        let e1 = compressed.grouped().get(0).unwrap();
        let e2 = compressed.grouped().get(5).unwrap();

        assert_eq!(
            e1.to_string(),
            "r_0 * r_0 * r_0 * (Z_10 * Z_9 * Z_4 + r_0 * Z_11 * Z_6 + r_0 * r_0 * Z_8 + r_0 * Z_12 * Z_7) + r_0 * r_0 * r_0 * r_0 * Z_9 * Z_0 + Z_9 * Z_9 * Z_9 * Z_9 * Z_9 * Z_2 + r_0 * r_0 * r_0 * r_0 * Z_10 * Z_1 + Z_10 * Z_10 * Z_10 * Z_10 * Z_10 * Z_3"
        );

        assert_eq!(
            e2.to_string(),
            "r_1 * r_1 * r_1 * (Z_14 * Z_13 * Z_4 + r_1 * Z_15 * Z_6 + r_1 * r_1 * Z_8 + r_1 * Z_16 * Z_7) + r_1 * r_1 * r_1 * r_1 * Z_13 * Z_0 + Z_13 * Z_13 * Z_13 * Z_13 * Z_13 * Z_2 + r_1 * r_1 * r_1 * r_1 * Z_14 * Z_1 + Z_14 * Z_14 * Z_14 * Z_14 * Z_14 * Z_3"
        );
    }
}
