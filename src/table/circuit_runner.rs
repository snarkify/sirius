use tracing::*;

use super::{circuit_data::CircuitData, ConstraintSystemMetainfo, WitnessCollector};
use crate::{
    ff::PrimeField,
    halo2_proofs::plonk::{Circuit, ConstraintSystem, Error, FloorPlanner},
    plonk::{self, permutation::PermutationData, PlonkStructure},
    util::batch_invert_assigned,
};

pub type Witness<F> = Vec<Vec<F>>;

#[derive(Debug, Clone)]
pub struct CircuitRunner<F: PrimeField, CT: Circuit<F>> {
    pub(crate) k: u32,
    pub(crate) circuit: CT,
    pub(crate) cs: ConstraintSystem<F>,
    pub(crate) config: CT::Config,
    pub(crate) instances: Vec<Vec<F>>,
}

impl<F: PrimeField, CT: Circuit<F>> CircuitRunner<F, CT> {
    pub fn new(k: u32, circuit: CT, instances: Vec<Vec<F>>) -> Self {
        let mut cs = ConstraintSystem::default();

        CircuitRunner {
            config: CT::configure(&mut cs),
            k,
            circuit,
            cs,
            instances,
        }
    }

    #[instrument(name = "circuit_collect_plonk_struct", skip_all)]
    pub fn try_collect_plonk_structure(&self) -> Result<PlonkStructure<F>, Error> {
        debug!("start build metainfo");
        let ConstraintSystemMetainfo {
            num_challenges,
            round_sizes,
            gates,
            custom_gates_lookup_compressed,
            ..
        } = ConstraintSystemMetainfo::build(self.k as usize, &self.cs);
        debug!("meta info is ready");

        debug!("start preprocessing");
        let PreprocessingData {
            fixed_columns,
            selectors,
            permutation_data,
        } = self.try_collect_preprocessing()?;
        debug!("preprocessing is ready");

        Ok(PlonkStructure {
            k: self.k as usize,
            num_io: self.instances.iter().map(|l| l.len()).collect(),
            selectors,
            fixed_columns,
            num_advice_columns: self.cs.num_advice_columns(),
            num_challenges,
            round_sizes,
            custom_gates_lookup_compressed,
            gates,
            permutation_data,
            lookup_arguments: plonk::lookup::Arguments::compress_from(&self.cs),
        })
    }

    #[instrument(name = "circuit_collect_witness", skip_all)]
    pub fn try_collect_witness(&self) -> Result<Witness<F>, Error> {
        let mut witness = WitnessCollector {
            instances: self.instances.clone(),
            advice: vec![vec![F::ZERO.into(); 1 << self.k]; self.cs.num_advice_columns()],
        };

        CT::FloorPlanner::synthesize(&mut witness, &self.circuit, self.config.clone(), vec![])?;

        Ok(batch_invert_assigned(&witness.advice))
    }

    fn try_collect_preprocessing(&self) -> Result<PreprocessingData<F>, Error> {
        let nrow = 1 << self.k;

        let mut circuit_data = CircuitData {
            k: self.k,
            num_io: self.instances.iter().map(|i| i.len()).collect(),
            fixed: vec![vec![F::ZERO.into(); nrow]; self.cs.num_fixed_columns()],
            selector: vec![vec![false; nrow]; self.cs.num_selectors],
            permutation: plonk::permutation::Assembly::new(nrow, &self.cs.permutation),
        };

        CT::FloorPlanner::synthesize(
            &mut circuit_data,
            &self.circuit,
            self.config.clone(),
            vec![],
        )?;

        Ok(PreprocessingData {
            permutation_data: PermutationData::from(&circuit_data.permutation),
            fixed_columns: batch_invert_assigned(&circuit_data.fixed),
            selectors: circuit_data.selector,
        })
    }
}

struct PreprocessingData<F: PrimeField> {
    pub(crate) permutation_data: PermutationData,
    pub(crate) fixed_columns: Vec<Vec<F>>,
    pub(crate) selectors: Vec<Vec<bool>>,
}
