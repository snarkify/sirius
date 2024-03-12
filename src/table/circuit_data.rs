use ff::PrimeField;
use halo2_proofs::{
    circuit::Value,
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge, Column, Error, Fixed, Instance, Selector,
    },
};
use tracing::*;

use crate::plonk;

pub struct CircuitData<F: PrimeField> {
    pub(crate) k: u32,
    pub(crate) num_io: usize,
    pub(crate) fixed: Vec<Vec<Assigned<F>>>,
    pub(crate) selector: Vec<Vec<bool>>,
    pub(crate) permutation: plonk::permutation::Assembly,
}

impl<F: PrimeField> Assignment<F> for CircuitData<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.selector[selector.index()][row] = true;
        Ok(())
    }

    fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        // currently only support single instance column
        if column.index() == 0 && row < self.num_io {
            Ok(Value::unknown())
        } else {
            Err(Error::BoundsFailure)
        }
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _annotation: A,
        _column: Column<Advice>,
        _row: usize,
        _to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        *self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or_else(|| {
                error!(
                    "Error while assign fixed {} in column {column:?} & row {row}",
                    annotation().into()
                );
                Error::BoundsFailure
            })? = to().into_field().assign()?;
        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        self.permutation
            .copy(left_column, left_row, right_column, right_row)
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, _: Challenge) -> Value<F> {
        Value::unknown()
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}
