//! This module implements the core functionalities to (1) obtain all necessary information from halo2
//! circuits and (2) run special soundness protocols.
//! It centers around the `TableData` struct, which encapsulates the PLONK constraint system and
//! handles the construction and operation of various PLONK components. Key features include:
//!
//! - Preparation and assembly of the constraint system
//! - Implementation of special soundness protocols (`run_sps_protocol_*` functions), essential for
//!   generating instance/witnesses/challenges securely
//! - Construction of permutation matrices, ensuring copy constraints consistency in the constraint system.
//! - Construction of lookup Arguments when the circuits contains lookup argument
//!
//! The module is the intermediate data representation of plonkish constrain system defined by the
//! circuits

use log::*;

use ff::PrimeField;
use halo2_proofs::{
    circuit::Value,
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge, Circuit, Column, ConstraintSystem, Error,
        Fixed, FloorPlanner, Instance, Selector,
    },
};

use crate::{
    concat_vec,
    plonk::{
        self,
        util::{compress_expression, permutation_matrix},
        PlonkStructure,
    },
    polynomial::{Expression, MultiPolynomial},
    util::batch_invert_assigned,
};

pub struct CircuitData<F: PrimeField> {
    pub(crate) k: u32,
    pub(crate) num_io: usize,
    pub(crate) fixed: Vec<Vec<Assigned<F>>>,
    pub(crate) selector: Vec<Vec<bool>>,
    pub(crate) permutation: plonk::permutation::Assembly,
}

pub struct WitnessData<F: PrimeField> {
    pub(crate) instance: Vec<F>,
    pub(crate) advice: Vec<Vec<Assigned<F>>>,
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

impl<F: PrimeField> Assignment<F> for WitnessData<F> {
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

    fn enable_selector<A, AR>(
        &mut self,
        _: A,
        _selector: &Selector,
        _row: usize,
    ) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
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
        assert!(column.index() == 0); // require just single instance
        self.instance
            .get(row)
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        annotation: A,
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
        // TODO: support phases
        *self
            .advice
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or_else(|| {
                error!(
                    "Error while assign advice {} in column {column:?} & row {row}",
                    annotation().into()
                );
                Error::BoundsFailure
            })? = to().into_field().assign()?;

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _annotation: A,
        _column: Column<Fixed>,
        _row: usize,
        _to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
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

#[derive(Debug, Clone)]
pub struct TableData<F: PrimeField, CT: Circuit<F>> {
    pub(crate) k: u32,
    pub(crate) circuit: CT,
    pub(crate) cs: ConstraintSystem<F>,
    pub(crate) config: CT::Config,
    pub(crate) instance: Vec<F>,
}

/// The separation of this function from circuit_info is to remove dependency on PlonkStructure
/// it is used to kickstart the Folding Circuit initialization
/// return (num_challenges, round_sizes, folding_degree)
pub fn circuit_meta_info<F: PrimeField>(
    k: usize,
    cs: &ConstraintSystem<F>,
) -> (usize, Vec<usize>, usize, MultiPolynomial<F>) {
    let num_gates = cs
        .gates()
        .iter()
        .flat_map(|gate| gate.polynomials().iter())
        .count();
    let lookup_arguments = plonk::lookup::Arguments::compress_from(cs);
    let (num_lookups, has_vector_lookup, lookup_exprs) = lookup_arguments
        .as_ref()
        .map(|arg| {
            (
                arg.lookup_polys.len(),
                arg.has_vector_lookup,
                concat_vec!(
                    &arg.vanishing_lookup_polys(cs),
                    &arg.log_derivative_lhs_and_rhs(cs)
                ),
            )
        })
        .unwrap_or((0, false, vec![]));
    let exprs = cs
        .gates()
        .iter()
        .flat_map(|gate| gate.polynomials().iter().cloned())
        .map(|expr| Expression::from_halo2_expr(&expr, cs.num_selectors(), cs.num_fixed_columns()))
        .chain(lookup_exprs)
        .collect::<Vec<_>>();

    let num_challenges = if has_vector_lookup {
        3
    } else if num_lookups > 0 {
        2
    } else if num_gates > 1 {
        1
    } else {
        0
    };

    // we have at most 3 prover rounds
    let nrow = 1 << k;
    let mut round_sizes = Vec::new();
    if has_vector_lookup {
        // advice columns
        round_sizes.push(cs.num_advice_columns() * nrow);
        // (l_i, t_i, m_i), see [`lookup.rs::Arguments::log_derivative_expr`]
        round_sizes.push(3 * num_lookups * nrow);
        // (h_i, g_i), see [`lookup.rs::Arguments::log_derivative_expr`]
        round_sizes.push(2 * num_lookups * nrow);
    } else if num_lookups > 0 {
        // advice columns || (l_i, t_i, m_i)
        round_sizes.push((cs.num_advice_columns() + 3 * num_lookups) * nrow);
        // (h_i, g_i)
        round_sizes.push(2 * num_lookups * nrow);
    } else {
        // advice columns
        round_sizes.push(cs.num_advice_columns() * nrow);
    };

    // we use r3 to combine all custom gates and lookup expressions
    // find the challenge index of r3
    let challenge_index = if num_challenges > 0 {
        num_challenges - 1
    } else {
        0
    };

    let poly = compress_expression(&exprs, challenge_index).expand();

    let folding_degree = poly.degree_for_folding(cs.num_fixed_columns() + cs.num_selectors());

    (num_challenges, round_sizes, folding_degree, poly)
}

impl<F: PrimeField, CT: Circuit<F>> TableData<F, CT> {
    pub fn new(k: u32, circuit: CT, instance: Vec<F>) -> Self {
        let mut cs = ConstraintSystem::default();
        let config = CT::configure(&mut cs);
        TableData {
            k,
            circuit,
            cs,
            config,
            instance,
        }
    }

    fn circuit_info(&self) -> PlonkStructure<F> {
        let (num_challenges, round_sizes, dd, poly) = circuit_meta_info(self.k as usize, &self.cs);
        println!(
            "hehe, num_challenges={}, round_sizes={:?}, dd={}, poly={}",
            num_challenges, round_sizes, dd, &poly
        );

        PlonkStructure {
            k: self.k as usize,
            num_io: self.instance.len(),
            selectors: vec![],
            fixed_columns: vec![],
            num_advice_columns: self.cs.num_advice_columns(),
            num_challenges,
            round_sizes,
            poly,
            permutation_matrix: vec![],
            lookup_arguments: plonk::lookup::Arguments::compress_from(&self.cs),
        }
    }

    fn collect_preprocessing(&self, S: &mut PlonkStructure<F>) -> Result<(), Error> {
        let mut circuit_data = CircuitData {
            k: self.k,
            num_io: self.instance.len(),
            fixed: vec![vec![F::ZERO.into(); 1 << self.k]; self.cs.num_fixed_columns()],
            selector: vec![vec![false; 1 << self.k]; self.cs.num_selectors()],
            permutation: plonk::permutation::Assembly::new(1 << self.k, &self.cs.permutation),
        };

        CT::FloorPlanner::synthesize(
            &mut circuit_data,
            &self.circuit,
            self.config.clone(),
            vec![],
        )?;

        S.permutation_matrix = permutation_matrix(
            self.k as usize,
            self.instance.len(),
            &self.cs,
            &circuit_data.permutation,
        );
        S.fixed_columns = batch_invert_assigned(&circuit_data.fixed);
        S.selectors = circuit_data.selector;
        Ok(())
    }

    pub fn plonk_structure(&self) -> Result<PlonkStructure<F>, Error> {
        let mut S = self.circuit_info();
        self.collect_preprocessing(&mut S)?;
        Ok(S)
    }

    pub fn collect_witness(&self) -> Result<Vec<Vec<F>>, Error> {
        let mut witness = WitnessData {
            instance: self.instance.clone(),
            advice: vec![vec![F::ZERO.into(); 1 << self.k]; self.cs.num_advice_columns()],
        };

        CT::FloorPlanner::synthesize(&mut witness, &self.circuit, self.config.clone(), vec![])?;
        Ok(batch_invert_assigned(&witness.advice))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};
    use crate::util::trim_leading_zeros;
    use ff::Field;
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Instance};
    use halo2curves::group::ff::FromUniformBytes;
    use prettytable::{row, Cell, Row, Table};

    const T: usize = 3;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
        pconfig: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    struct TestCircuit<F: PrimeField> {
        inputs: Vec<F>,
        r: F,
    }

    impl<F: PrimeField> TestCircuit<F> {
        fn new(inputs: Vec<F>, r: F) -> Self {
            Self { inputs, r }
        }
    }

    impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: Vec::new(),
                r: F::ZERO,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let pconfig = MainGate::configure(meta);
            Self::Config { pconfig, instance }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let pchip = MainGate::new(config.pconfig);
            let output = layouter.assign_region(
                || "test",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    pchip.random_linear_combination(ctx, self.inputs.clone(), self.r)
                },
            )?;
            layouter.constrain_instance(output.cell(), config.instance, 0)?;
            Ok(())
        }
    }

    #[test]
    fn test_assembly() -> Result<(), Error> {
        use halo2curves::pasta::Fp;

        const K: u32 = 4;
        let mut inputs = Vec::new();
        for i in 1..10 {
            inputs.push(Fp::from(i as u64));
        }
        let circuit = TestCircuit::new(inputs, Fp::ONE);
        let output = Fp::from_str_vartime("45").unwrap();
        let public_inputs = vec![output];

        let td = TableData::<Fp, _>::new(K, circuit, public_inputs);
        let witness = td.collect_witness()?;

        let mut table = Table::new();
        table.add_row(row!["s0", "s1", "s2", "in", "out"]);
        let col = 5;
        for i in 0..2usize.pow(K) {
            let mut row = vec![];
            for j in 0..col {
                if let Some(val) = witness.get(j).and_then(|v| v.get(i)) {
                    row.push(trim_leading_zeros(format!("{:?}", val)));
                }
            }
            table.add_row(Row::new(row.iter().map(|s| Cell::new(s)).collect()));
        }
        // table.printstd();
        Ok(())
    }
}
