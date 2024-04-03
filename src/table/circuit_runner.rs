use ff::PrimeField;
use halo2_proofs::plonk::{Circuit, ConstraintSystem, Error, FloorPlanner};

use crate::{
    plonk::{self, PlonkStructure},
    util::batch_invert_assigned,
};

use super::{circuit_data::CircuitData, ConstraintSystemMetainfo, WitnessCollector};

pub type Witness<F> = Vec<Vec<F>>;

#[derive(Debug, Clone)]
pub struct CircuitRunner<F: PrimeField, CT: Circuit<F>> {
    pub(crate) k: u32,
    pub(crate) circuit: CT,
    pub(crate) cs: ConstraintSystem<F>,
    pub(crate) config: CT::Config,
    pub(crate) instance: Vec<F>,
}

impl<F: PrimeField, CT: Circuit<F>> CircuitRunner<F, CT> {
    pub fn new(k: u32, circuit: CT, instance: Vec<F>) -> Self {
        let mut cs = ConstraintSystem::default();

        CircuitRunner {
            config: CT::configure(&mut cs),
            k,
            circuit,
            cs,
            instance,
        }
    }

    pub fn try_collect_plonk_structure(&self) -> Result<PlonkStructure<F>, Error> {
        let ConstraintSystemMetainfo {
            num_challenges,
            round_sizes,
            custom_gates_lookup_compressed,
            ..
        } = ConstraintSystemMetainfo::build(self.k as usize, &self.cs);

        let mut S = PlonkStructure {
            k: self.k as usize,
            num_io: self.instance.len(),
            selectors: vec![],
            fixed_columns: vec![],
            num_advice_columns: self.cs.num_advice_columns(),
            num_challenges,
            round_sizes,
            custom_gates_lookup_compressed,
            permutation_matrix: vec![],
            lookup_arguments: plonk::lookup::Arguments::compress_from(&self.cs),
        };

        self.try_collect_preprocessing(&mut S)?;

        Ok(S)
    }

    pub fn try_collect_witness(&self) -> Result<Witness<F>, Error> {
        let mut witness = WitnessCollector {
            instance: self.instance.clone(),
            advice: vec![vec![F::ZERO.into(); 1 << self.k]; self.cs.num_advice_columns()],
        };

        CT::FloorPlanner::synthesize(&mut witness, &self.circuit, self.config.clone(), vec![])?;

        Ok(batch_invert_assigned(&witness.advice))
    }

    fn try_collect_preprocessing(&self, S: &mut PlonkStructure<F>) -> Result<(), Error> {
        let nrow = 1 << self.k;

        let mut circuit_data = CircuitData {
            k: self.k,
            num_io: self.instance.len(),
            fixed: vec![vec![F::ZERO.into(); nrow]; self.cs.num_fixed_columns()],
            selector: vec![vec![false; nrow]; self.cs.num_selectors()],
            permutation: plonk::permutation::Assembly::new(nrow, &self.cs.permutation),
        };

        CT::FloorPlanner::synthesize(
            &mut circuit_data,
            &self.circuit,
            self.config.clone(),
            vec![],
        )?;

        S.permutation_matrix = plonk::util::construct_permutation_matrix(
            self.k as usize,
            self.instance.len(),
            &self.cs,
            &circuit_data.permutation,
        );
        S.fixed_columns = batch_invert_assigned(&circuit_data.fixed);
        S.selectors = circuit_data.selector;

        Ok(())
    }
}
