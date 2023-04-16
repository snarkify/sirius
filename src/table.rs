use ff::PrimeField;
use halo2_proofs::{
    circuit::Value,
    plonk::{Advice, Assignment, Assigned, Any, Circuit, ConstraintSystem, Challenge, Column, 
        FloorPlanner, Fixed, Instance, Selector, Error},
};
use std::collections::HashMap;


pub struct TableData<F:PrimeField> {
    // TODO: without usable_rows still safe?
    k: u32,
    fixed: Vec<Vec<Assigned<F>>>,
    instance: Vec<Vec<F>>,
    advice: Vec<Vec<Assigned<F>>>,
    challenges: HashMap<usize, F>,
}

impl<F: PrimeField> TableData<F> {
    pub fn new(k: u32, instance: Vec<Vec<F>>) -> Self {
        TableData {
            k,
            instance,
            fixed: vec![],
            advice: vec![],
            challenges: HashMap::new(),
        }
    }

    pub fn assembly<ConcreteCircuit: Circuit<F>>(&mut self, circuit: &ConcreteCircuit) -> Result<(), Error> {
        let mut meta = ConstraintSystem::default();
        let config = ConcreteCircuit::configure(&mut meta);
        ConcreteCircuit::FloorPlanner::synthesize(
            self,
            circuit,
            config.clone(),
            vec![], // TODO: make sure constants not needed
        )?;
        Ok(())
    }
}

impl<F: PrimeField> Assignment<F> for TableData<F> {
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

        fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            // TODO: add selector support when needed

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
            self.instance
                .get(column.index())
                .and_then(|column| column.get(row))
                .map(|v| Value::known(*v))
                .ok_or(Error::BoundsFailure)
        }

        fn assign_advice<V, VR, A, AR>(
            &mut self,
            _: A,
            column: Column<Advice>,
            row: usize,
            to: V,
        ) -> Result<(), Error>
        where
            V: FnOnce() -> Value<VR>,
            VR: Into<Assigned<F>>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            // TODO: do we need to support phases 
             *self
                .advice
                .get_mut(column.index())
                .and_then(|v| v.get_mut(row))
                .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

            Ok(())
        }

        fn assign_fixed<V, VR, A, AR>(
            &mut self,
            _: A,
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
                .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;
            Ok(())
        }

        fn copy(
            &mut self,
            _: Column<Any>,
            _: usize,
            _: Column<Any>,
            _: usize,
        ) -> Result<(), Error> {
            // TODO: needed to constrain instance column 

            Ok(())
        }

        fn fill_from_row(
            &mut self,
            _: Column<Fixed>,
            _: usize,
            _: Value<Assigned<F>>,
        ) -> Result<(), Error> {
            Ok(())
        }

        fn get_challenge(&self, challenge: Challenge) -> Value<F> {
            self.challenges
                .get(&challenge.index())
                .cloned()
                .map(Value::known)
                .unwrap_or_else(Value::unknown)
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

#[cfg(test)]
mod tests {
    use super::*;



}
