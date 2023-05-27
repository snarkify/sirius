use ff::Field;
use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::Value,
    plonk::{Advice, Assignment, Assigned, Any, Circuit, ConstraintSystem, Challenge, Column, 
        FloorPlanner, Fixed, Instance, Selector, Error},
};
use std::io;
use std::collections::HashMap;
use crate::transcript::{Transcript, AbsorbInTranscript};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkStructure<C: CurveAffine> {
    pub(crate) fixed_columns: Vec<Vec<C::Scalar>>,
    pub(crate) fixed_commitments: Vec<C>,
}

#[derive(Clone, Debug)]
pub struct PlonkInstance<C: CurveAffine> {
    pub(crate) advice_commitments: Vec<C>,
    pub(crate) instance_commitments: Vec<C>,
    pub(crate) X: Vec<C>,
}


#[derive(Clone, Debug)]
pub struct PlonkWitness<C:CurveAffine> {
    pub(crate) advice_columns: Vec<Vec<C::Scalar>>,
    pub(crate) instance_columns: Vec<Vec<C::Scalar>>,
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkInstance<C:CurveAffine> {
    pub(crate) advice_commitments: Vec<C>,
    pub(crate) instance_commitments: Vec<C>,
    pub(crate) E_commitment: C,
    pub(crate) u: C::Scalar,
    pub(crate) X: Vec<C>
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkWitness<C:CurveAffine> {
    pub(crate) advice_columns: Vec<Vec<C::Scalar>>,
    pub(crate) instance_columns: Vec<Vec<C::Scalar>>,
    pub(crate) E: Vec<C::Scalar>,
}

impl<C: CurveAffine, T: Transcript<C>> AbsorbInTranscript<C,T> for PlonkStructure<C> {
    fn absorb_into(&self, transcript: &mut T) -> io::Result<()> {
        for point in &self.fixed_commitments {
            transcript.common_point(*point)?;
        }
        Ok(())
    }
}

impl<C: CurveAffine, T: Transcript<C>> AbsorbInTranscript<C,T> for PlonkInstance<C> {
    fn absorb_into(&self, transcript: &mut T) -> io::Result<()> {
        for point in self.advice_commitments.iter().chain(self.instance_commitments.iter()).chain(self.X.iter()) {
            transcript.common_point(*point)?;
        }
        Ok(())
    }
}

impl<C: CurveAffine, T: Transcript<C>> AbsorbInTranscript<C,T> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, transcript: &mut T) -> io::Result<()> {
        for point in self.advice_commitments.iter().chain(self.instance_commitments.iter()).chain(self.X.iter()) {
            transcript.common_point(*point)?;
        }
        transcript.common_scalar(self.u)?;
        transcript.common_point(self.E_commitment)?;
        Ok(())
    }
}


pub struct TableData<C:CurveAffine> {
    // TODO: without usable_rows still safe?
    k: u32,
    fixed: Vec<Vec<Assigned<C::Scalar>>>,
    instance: Vec<Vec<C::Scalar>>,
    advice: Vec<Vec<Assigned<C::Scalar>>>,
    challenges: HashMap<usize, C::Scalar>,
}

impl<C: CurveAffine> TableData<C> {
    pub fn new(k: u32, instance: Vec<Vec<C::Scalar>>) -> Self {
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
        self.fixed = vec![vec![<C::Scalar as Field>::ZERO.into(); n as usize]; meta.num_fixed_columns()];  
        self.instance = vec![vec![<C::Scalar as Field>::ZERO; n as usize]; meta.num_instance_columns()];  
        self.advice = vec![vec![<C::Scalar as Field>::ZERO.into(); n as usize]; meta.num_advice_columns()];  
        ConcreteCircuit::FloorPlanner::synthesize(
            self,
            circuit,
            config.clone(),
            vec![], // TODO: make sure constants not needed
        )?;
        Ok(())
    }

    pub fn fold_instance(
        &self,
        U2: &PlonkInstance<C>,
        comm_T: &C,
        r: &C::Scalar,
    ) -> Option<RelaxedPlonkInstance<C>> {
        None
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
    use poseidon::Spec;
    use halo2_proofs::plonk::{ConstraintSystem, Column, Circuit, Instance};
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2curves::group::ff::FromUniformBytes;
    use crate::aux_gate::{AuxChip, AuxConfig, RegionCtx};
    use crate::utils::trim_leading_zeros;

    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig<F: PrimeField> {
       pconfig: AuxConfig<F, T, RATE>,
       instance: Column<Instance>
    }

    struct TestCircuit<F: PrimeField> {
        inputs: Vec<F>,
    }

    impl<F:PrimeField> TestCircuit<F> {
        fn new(inputs: Vec<F>) -> Self {
            Self {
                inputs,
            }
        }
    }

    impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;


        fn without_witnesses(&self) -> Self {
            Self {
                inputs: Vec::new(),
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let mut adv_cols = [(); T+2].map(|_| meta.advice_column()).into_iter();
            let mut fix_cols = [(); 2*T+4].map(|_| meta.fixed_column()).into_iter();
            let pconfig = AuxChip::configure(meta, &mut adv_cols, &mut fix_cols);
            Self::Config {
                pconfig,
                instance,
            }
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
             let spec = Spec::new(R_F, R_P);
             let mut pchip = AuxChip::new(config.pconfig, spec);
             pchip.update(self.inputs.clone());
             let output = layouter.assign_region(||"poseidon hash", |region|{
                 let ctx = &mut RegionCtx::new(region, 0);
                 pchip.squeeze(ctx)
             })?;
             layouter.constrain_instance(output.cell(), config.instance, 0)?;
             Ok(())
        }
    }


    #[test]
    fn test_assembly() {
        use halo2curves::pasta::{EqAffine, Fp};
        
        const K:u32 = 7;
        let mut inputs = Vec::new();
        for i in 0..5 {
            inputs.push(Fp::from(i as u64));
        }
        let circuit = TestCircuit::new(inputs);
        // hex = 0x1cd3150d8e12454ff385da8a4d864af6d0f021529207b16dd6c3d8f2b52cfc67
        let out_hash = Fp::from_str_vartime("13037709793114148810823325920380362524528554380279235267325741570708489436263").unwrap();
        let public_inputs = vec![vec![out_hash]];

        let mut td = TableData::<EqAffine>::new(K, public_inputs);
        let _ = td.assembly(&circuit);

        let mut table = Table::new();
        table.add_row(row![ "s0", "s1", "s2", "in", "out"]);
        let col = 5;
        for i in 0..127 {
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
