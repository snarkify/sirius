use ff::Field;
use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::Value,
    plonk::{Advice, Assignment, Assigned, Any, Circuit, ConstraintSystem, Challenge, Column, 
        FloorPlanner, Fixed, Instance, Selector, Error},
};
use std::collections::HashMap;
use crate::{
    commitment::CommitmentKey,
    poseidon::{ROTrait, AbsorbInRO},
    utils::batch_invert_assigned,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkStructure<C: CurveAffine> {
    pub(crate) fixed_commitments: Vec<C>,
}

#[derive(Clone, Debug)]
pub struct PlonkInstance<C: CurveAffine> {
    pub(crate) advice_commitments: Vec<C>,
    pub(crate) instance: Vec<C::Scalar>, // inst = [X0, X1]
}


#[derive(Clone, Debug)]
pub struct PlonkWitness<C:CurveAffine> {
    pub(crate) advice_columns: Vec<Vec<C::Scalar>>,
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkInstance<C:CurveAffine> {
    pub(crate) advice_commitments: Vec<C>,
    pub(crate) instance: Vec<C::Scalar>,
    pub(crate) E_commitment: C,
    pub(crate) u: C::Scalar,
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkWitness<C:CurveAffine> {
    pub(crate) advice_columns: Vec<Vec<C::Scalar>>,
    pub(crate) instance_columns: Vec<Vec<C::Scalar>>,
    pub(crate) E: Vec<C::Scalar>,
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for PlonkStructure<C> {
    fn absorb_into(&self, ro: &mut RO) {
        for point in &self.fixed_commitments {
            ro.absorb_point(*point);
        }
    }
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for PlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        for point in self.advice_commitments.iter() {
            ro.absorb_point(*point);
        }
        for inst in self.instance.iter().take(2) {
            ro.absorb_scalar(*inst);
        }
    }
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        for point in self.advice_commitments.iter() {
            ro.absorb_point(*point);
        }
        for inst in self.instance.iter().take(2) {
            ro.absorb_scalar(*inst);
        }
        ro.absorb_scalar(self.u); 
        ro.absorb_point(self.E_commitment);
    }
}


pub struct TableData<C:CurveAffine> {
    // TODO: without usable_rows still safe?
    k: u32,
    fixed: Vec<Vec<Assigned<C::Scalar>>>,
    instance: Vec<C::Scalar>,
    advice: Vec<Vec<Assigned<C::Scalar>>>,
    challenges: HashMap<usize, C::Scalar>,
}

impl<C: CurveAffine> TableData<C> {
    pub fn new(k: u32, instance: Vec<C::Scalar>) -> Self {
        TableData {
            k,
            instance,
            fixed: vec![],
            advice: vec![],
            challenges: HashMap::new(),
        }
    }

    pub fn assembly<ConcreteCircuit: Circuit<C::Scalar>>(&mut self, circuit: &ConcreteCircuit) -> Result<(), Error> {
        let mut meta = ConstraintSystem::default();
        let config = ConcreteCircuit::configure(&mut meta);
        let n = 1u64 << self.k;
        assert!(meta.num_instance_columns() == 1);
        self.fixed = vec![vec![<C::Scalar as Field>::ZERO.into(); n as usize]; meta.num_fixed_columns()];  
        self.instance = vec![<C::Scalar as Field>::ZERO; 2]; 
        self.advice = vec![vec![<C::Scalar as Field>::ZERO.into(); n as usize]; meta.num_advice_columns()];  
        ConcreteCircuit::FloorPlanner::synthesize(
            self,
            circuit,
            config.clone(),
            vec![], // TODO: make sure constants not needed
        )?;
        Ok(())
    }

    pub fn plonk_structure(
        &self,
        ck: CommitmentKey<C>
    ) -> PlonkStructure<C> {
        let fixed_columns = batch_invert_assigned(&self.fixed);
        let mut fixed_commitments: Vec<C> = Vec::new();
        for col in fixed_columns.iter() {
            let tmp = ck.commit(&col[..]);
            fixed_commitments.push(tmp);
        }
        PlonkStructure {
            fixed_commitments,
        }
    }

    pub fn plonk_instance(
        &self,
        ck: CommitmentKey<C>
    ) -> PlonkInstance<C> {
        let advice_columns = batch_invert_assigned(&self.advice);
        let mut advice_commitments: Vec<C> = Vec::new();
        let mut instance: Vec<C::Scalar> = Vec::new();
        for col in advice_columns.iter() {
            let tmp = ck.commit(&col[..]);
            advice_commitments.push(tmp);
        }
        assert!(self.instance.len() >= 2);
        for inst in self.instance.iter().take(2) {
            instance.push(*inst)
        }
        PlonkInstance {
            advice_commitments,
            instance,
        }
    }

    pub fn plonk_witness(
        &self,
    ) -> PlonkWitness<C> {
        let advice_columns = batch_invert_assigned(&self.advice);
        PlonkWitness {
            advice_columns
        }
    }
}

impl<C: CurveAffine> Assignment<C::Scalar> for TableData<C> {
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
            // TODO: add selector support by converting to selector to fixed column 

            Ok(())
        }

        fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            // Do nothing
        }

        fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<C::Scalar>, Error> {
            assert!(column.index() == 0); // require just single instance
            self.instance.get(row)
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
            VR: Into<Assigned<C::Scalar>>,
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
            VR: Into<Assigned<C::Scalar>>,
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
            _: Value<Assigned<C::Scalar>>,
        ) -> Result<(), Error> {
            Ok(())
        }

        fn get_challenge(&self, challenge: Challenge) -> Value<C::Scalar> {
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
    use ff::PrimeField;
    use prettytable::{Table, row, Row, Cell};
    use halo2_proofs::plonk::{ConstraintSystem, Column, Circuit, Instance};
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2curves::group::ff::FromUniformBytes;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};
    use crate::utils::trim_leading_zeros;

    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
       pconfig: MainGateConfig<T>,
       instance: Column<Instance>
    }

    struct TestCircuit<F: PrimeField> {
        inputs: Vec<F>,
        r: F,
    }

    impl<F:PrimeField> TestCircuit<F> {
        fn new(inputs: Vec<F>, r: F) -> Self {
            Self {
                inputs,
                r
            }
        }
    }

    impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;


        fn without_witnesses(&self) -> Self {
            Self {
                inputs: Vec::new(),
                r: F::ZERO
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let mut adv_cols = [(); T+2].map(|_| meta.advice_column()).into_iter();
            let mut fix_cols = [(); 2*T+4].map(|_| meta.fixed_column()).into_iter();
            let pconfig = MainGate::configure(meta, &mut adv_cols, &mut fix_cols);
            Self::Config {
                pconfig,
                instance,
            }
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
             let pchip = MainGate::new(config.pconfig);
             let output = layouter.assign_region(||"test", |region|{
                 let ctx = &mut RegionCtx::new(region, 0);
                 pchip.random_linear_combination(ctx, self.inputs.clone(), self.r)
             })?;
             layouter.constrain_instance(output.cell(), config.instance, 0)?;
             Ok(())
        }
    }


    #[test]
    fn test_assembly() {
        use halo2curves::pasta::{EqAffine, Fp};
        
        const K:u32 = 4;
        let mut inputs = Vec::new();
        for i in 1..10 {
            inputs.push(Fp::from(i as u64));
        }
        let circuit = TestCircuit::new(inputs, Fp::ONE);
        let out_hash = Fp::from_str_vartime("45").unwrap();
        let public_inputs = vec![out_hash];

        let mut td = TableData::<EqAffine>::new(K, public_inputs);
        let _ = td.assembly(&circuit);

        let mut table = Table::new();
        table.add_row(row![ "s0", "s1", "s2", "in", "out"]);
        let col = 5;
        for i in 0..2usize.pow(K) {
            let mut row = vec![];
            for j in 0..col {
                if let Some(val) = td.advice.get(j).and_then(|v| v.get(i)) {
                    row.push(trim_leading_zeros(format!("{:?}", val.evaluate())));
                }
            }
            table.add_row(Row::new(row.iter().map(|s| Cell::new(s)).collect()));
        }
        // table.printstd();
    }

}
