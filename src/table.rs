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

use crate::{
    commitment::CommitmentKey,
    concat_vec,
    constants::NUM_CHALLENGE_BITS,
    plonk::{
        self,
        util::{
            cell_to_z_idx, column_index, compress_expression, fill_sparse_matrix,
            instance_column_index,
        },
        PlonkInstance, PlonkStructure, PlonkWitness,
    },
    polynomial::{sparse::SparseMatrix, Expression},
    poseidon::ROTrait,
    sps::Error as SpsError,
    util::{batch_invert_assigned, concatenate_with_padding, fe_to_fe},
};
use ff::PrimeField;
use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::Value,
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge, Circuit, Column, ConstraintSystem, Error,
        Fixed, FloorPlanner, Instance, Selector,
    },
};
use log::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct TableData<F: PrimeField> {
    // TODO: without usable_rows still safe?
    pub(crate) k: u32,
    pub(crate) cs: ConstraintSystem<F>,
    pub(crate) fixed: Vec<Vec<Assigned<F>>>,
    pub(crate) fixed_columns: Vec<Vec<F>>,
    pub(crate) selector: Vec<Vec<bool>>,
    pub(crate) instance: Vec<F>,
    pub(crate) advice: Vec<Vec<Assigned<F>>>,
    pub(crate) advice_columns: Vec<Vec<F>>,
    pub(crate) challenges: HashMap<usize, F>,
    pub(crate) permutation: Option<plonk::permutation::Assembly>,
    pub(crate) lookup_arguments: Option<plonk::lookup::Arguments<F>>,
}

impl<F: PrimeField> TableData<F> {
    pub fn new(k: u32, instance: Vec<F>) -> Self {
        let cs = ConstraintSystem::default();
        TableData {
            k,
            cs,
            instance,
            fixed: vec![],
            fixed_columns: vec![],
            selector: vec![],
            advice: vec![],
            advice_columns: vec![],
            challenges: HashMap::new(),
            permutation: None,
            lookup_arguments: None,
        }
    }

    /// indicates whether the original constrain system contains vector lookup
    pub fn has_vector_lookup(&self) -> bool {
        self.lookup_arguments
            .as_ref()
            .map(|arg| arg.has_vector_lookup)
            .unwrap_or(false)
    }

    pub fn num_lookups(&self) -> usize {
        if self.lookup_arguments.is_none() {
            0
        } else {
            self.lookup_arguments.as_ref().unwrap().lookup_polys.len()
        }
    }

    pub fn lookup_exprs(&self, cs: &ConstraintSystem<F>) -> Vec<Expression<F>> {
        if let Some(lookup_arguments) = self.lookup_arguments.as_ref() {
            concat_vec!(
                &lookup_arguments.vanishing_lookup_polys(cs),
                &lookup_arguments.log_derivative_lhs_and_rhs(cs)
            )
        } else {
            vec![]
        }
    }

    /// Prepares the constraint system for a new configuration.
    ///
    /// This function initializes various components of the constraint system
    /// such as the permutation assembly, lookup arguments, and column vectors
    /// for fixed, selector, and advice columns based on the provided configuration.
    /// It must be called before using the constraint system for any computations.
    ///
    /// # Arguments
    ///
    /// * `configure` - A closure that takes a mutable reference to the `ConstraintSystem`
    ///   and returns a configuration object `C`. This allows for flexible and customized
    ///   setup of the constraint system.
    ///
    /// # Returns
    ///
    /// Returns the configuration object `C` as determined by the `configure` closure.
    ///
    /// # Panics
    ///
    /// This function will panic if the number of instance columns is not equal to 1.
    /// This is a temporary restriction and support for user-defined instance columns
    /// should be added in the future.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// // Assuming `cs` is a mutable reference to a ConstraintSystem object
    /// let config = cs.prepare(|cs| {
    ///     // Configure the constraint system
    ///     // ...
    ///     ConcreteCircuit::configure(cs)
    /// });
    /// ```
    pub(crate) fn configure<C>(
        &mut self,
        configure: impl FnOnce(&mut ConstraintSystem<F>) -> C,
    ) -> C {
        let config = configure(&mut self.cs);
        self.permutation = Some(plonk::permutation::Assembly::new(
            1 << self.k,
            &self.cs.permutation,
        ));
        self.lookup_arguments = plonk::lookup::Arguments::compress_from(&self.cs);
        let n = 1 << self.k;
        // TODO: add support for user defined instance columns
        assert!(self.cs.num_instance_columns() <= 1);
        self.fixed = vec![vec![F::ZERO.into(); n]; self.cs.num_fixed_columns()];
        self.selector = vec![vec![false; n]; self.cs.num_selectors()];
        self.advice = vec![vec![F::ZERO.into(); n]; self.cs.num_advice_columns()];
        config
    }

    pub(crate) fn batch_invert_assigned(&mut self) {
        let Self {
            advice_columns,
            fixed_columns,
            fixed,
            advice,
            ..
        } = self;

        rayon::join(
            || *fixed_columns = batch_invert_assigned(fixed),
            || *advice_columns = batch_invert_assigned(advice),
        );
    }

    pub fn assembly<ConcreteCircuit: Circuit<F>>(
        &mut self,
        circuit: &ConcreteCircuit,
    ) -> Result<(), Error> {
        let config = self.configure(ConcreteCircuit::configure);

        ConcreteCircuit::FloorPlanner::synthesize(
            self,
            circuit,
            config.clone(),
            vec![], // TODO: make sure constants not needed
        )?;

        self.batch_invert_assigned();

        Ok(())
    }

    pub fn plonk_structure(&self) -> Option<PlonkStructure<F>> {
        if self.advice.is_empty() {
            return None;
        }
        let num_gates = self
            .cs
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter())
            .count();
        let num_lookups = self.num_lookups();
        // we have at most 3 challenges: see [`PlonkInstance::challenges`]
        let num_challenges = if self.has_vector_lookup() {
            3
        } else if num_lookups > 0 {
            2
        } else if num_gates > 1 {
            1
        } else {
            0
        };

        // we have at most 3 prover rounds
        let nrow = 2usize.pow(self.k);
        let mut round_sizes = Vec::new();
        if self.has_vector_lookup() {
            // advice columns
            round_sizes.push(self.cs.num_advice_columns() * nrow);
            // (l_i, t_i, m_i), see [`lookup.rs::Arguments::log_derivative_expr`]
            round_sizes.push(3 * num_lookups * nrow);
            // (h_i, g_i), see [`lookup.rs::Arguments::log_derivative_expr`]
            round_sizes.push(2 * num_lookups * nrow);
        } else if num_lookups > 0 {
            // advice columns || (l_i, t_i, m_i)
            round_sizes.push((self.cs.num_advice_columns() + 3 * num_lookups) * nrow);
            // (h_i, g_i)
            round_sizes.push(2 * num_lookups * nrow);
        } else {
            // advice columns
            round_sizes.push(self.cs.num_advice_columns() * nrow);
        };

        let exprs = self
            .cs
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter().cloned())
            .map(|expr| {
                Expression::from_halo2_expr(
                    &expr,
                    self.cs.num_selectors(),
                    self.cs.num_fixed_columns(),
                )
            })
            .chain(self.lookup_exprs(&self.cs))
            .collect::<Vec<_>>();

        // we use r3 to combine all custom gates and lookup expressions
        // find the challenge index of r3
        let challenge_index = if num_challenges > 0 {
            num_challenges - 1
        } else {
            0
        };
        let poly = compress_expression(&exprs, challenge_index).expand();
        let permutation_matrix = self.permutation_matrix();

        Some(PlonkStructure {
            k: self.k as usize,
            selectors: self.selector.clone(),
            fixed_columns: self.fixed_columns.clone(),
            num_advice_columns: self.cs.num_advice_columns(),
            num_challenges,
            round_sizes,
            poly,
            permutation_matrix,
            lookup_arguments: self.lookup_arguments.clone(),
        })
    }

    /// run 0-round special soundness protocol
    /// w.r.t single custom gate + no lookup
    fn run_sps_protocol_0<C: CurveAffine<ScalarExt = F>>(
        &self,
        ck: &CommitmentKey<C>,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        let W1 = concatenate_with_padding(&self.advice_columns, 2usize.pow(self.k));
        let C1 = ck
            .commit(&W1)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W1",
                err,
            })?;

        Ok((
            PlonkInstance {
                W_commitments: vec![C1],
                instance: self.instance.clone(),
                challenges: vec![],
            },
            PlonkWitness { W: vec![W1] },
        ))
    }

    /// run 1-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C] -> ]r1[
    /// w.r.t multiple gates + no lookup
    fn run_sps_protocol_1<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        let (mut plonk_instance, plonk_witness) = self.run_sps_protocol_0(ck)?;

        self.instance.iter().for_each(|inst| {
            ro_nark.absorb_field(fe_to_fe(inst).unwrap());
        });
        plonk_instance.W_commitments.iter().for_each(|C| {
            ro_nark.absorb_point(C);
        });

        plonk_instance
            .challenges
            .push(ro_nark.squeeze::<C>(NUM_CHALLENGE_BITS));

        Ok((plonk_instance, plonk_witness))
    }

    /// run 2-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C1] -> ]r1[ -> [C2] -> ]r2[
    /// w.r.t has lookup but no vector lookup
    fn run_sps_protocol_2<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        let k_power_of_2 = 2usize.pow(self.k);

        // round 1
        let lookup_coeff = self
            .lookup_arguments
            .as_ref()
            .map(|la| la.evaluate_coefficient_1(self, F::ZERO))
            .transpose()?
            .ok_or(SpsError::LackOfLookupArguments)?;

        let W1 = [
            concatenate_with_padding(&self.advice_columns, k_power_of_2),
            concatenate_with_padding(
                &concat_vec!(&lookup_coeff.ls, &lookup_coeff.ts, &lookup_coeff.ms),
                k_power_of_2,
            ),
        ]
        .concat();

        let C1 = ck
            .commit(&W1)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W1",
                err,
            })?;

        self.instance.iter().for_each(|inst| {
            ro_nark.absorb_field(fe_to_fe(inst).unwrap());
        });
        ro_nark.absorb_point(&C1);
        let r1 = ro_nark.squeeze::<C>(NUM_CHALLENGE_BITS);

        // round 2
        let lookup_coeff = lookup_coeff.evaluate_coefficient_2(r1);

        let W2 = concatenate_with_padding(
            &concat_vec!(&lookup_coeff.hs, &lookup_coeff.gs),
            k_power_of_2,
        );

        let C2 = ck
            .commit(&W2)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W2",
                err,
            })?;
        ro_nark.absorb_point(&C2);
        let r2 = ro_nark.squeeze::<C>(NUM_CHALLENGE_BITS);

        Ok((
            PlonkInstance {
                W_commitments: vec![C1, C2],
                instance: self.instance.clone(),
                challenges: vec![r1, r2],
            },
            PlonkWitness { W: vec![W1, W2] },
        ))
    }

    /// run 3-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C1] -> ]r1[ -> [C2] -> ]r2[ -> [C3] -> ]r3[
    fn run_sps_protocol_3<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        self.instance.iter().for_each(|inst| {
            ro_nark.absorb_field(fe_to_fe(inst).unwrap());
        });

        let k_power_of_2 = 2usize.pow(self.k);

        // round 1
        let W1 = concatenate_with_padding(&self.advice_columns, k_power_of_2);
        let C1 = ck
            .commit(&W1)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W1",
                err,
            })?;
        ro_nark.absorb_point(&C1);
        let r1 = ro_nark.squeeze::<C>(NUM_CHALLENGE_BITS);

        // round 2
        let lookup_coeff = self
            .lookup_arguments
            .as_ref()
            .map(|la| la.evaluate_coefficient_1(self, r1))
            .transpose()?
            .ok_or(SpsError::LackOfLookupArguments)?;

        let W2 = concatenate_with_padding(
            &concat_vec!(&lookup_coeff.ls, &lookup_coeff.ts, &lookup_coeff.ms),
            k_power_of_2,
        );
        let C2 = ck
            .commit(&W2)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W2",
                err,
            })?;
        ro_nark.absorb_point(&C2);
        let r2 = ro_nark.squeeze::<C>(NUM_CHALLENGE_BITS);

        // round 3
        let lookup_coeff = lookup_coeff.evaluate_coefficient_2(r2);

        let W3 = concatenate_with_padding(
            &concat_vec!(&lookup_coeff.hs, &lookup_coeff.gs),
            k_power_of_2,
        );

        let C3 = ck
            .commit(&W3)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W3",
                err,
            })?;
        ro_nark.absorb_point(&C3);
        let r3 = ro_nark.squeeze::<C>(NUM_CHALLENGE_BITS);

        Ok((
            PlonkInstance {
                W_commitments: vec![C1, C2, C3],
                instance: self.instance.clone(),
                challenges: vec![r1, r2, r3],
            },
            PlonkWitness {
                W: vec![W1, W2, W3],
            },
        ))
    }

    /// run special soundness protocol to generate witnesses and challenges
    /// depending on whether we have multiple gates, lookup arguments and whether
    /// we have vector lookup, we will call different sub-sps protocol
    pub fn run_sps_protocol<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
        num_challenges: usize,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        match num_challenges {
            0 => self.run_sps_protocol_0(ck),
            1 => self.run_sps_protocol_1(ck, ro_nark),
            2 => self.run_sps_protocol_2(ck, ro_nark),
            3 => self.run_sps_protocol_3(ck, ro_nark),
            challenges_count => Err(SpsError::UnsupportedChallengesCount { challenges_count }),
        }
    }

    /// construct sparse matrix P (size N*N) from copy constraints
    /// since folding will change values of advice/instance column while keep fixed column values
    /// we don't allow fixed column to be in the copy constraint here
    /// suppose we have 1 instance column, n advice columns
    /// and there are total of r rows. notice the instance column only contains `num_io = io` items
    /// N = num_io + r*n. Let (i_1,...,i_{io}) be all values of the instance columns
    /// and (x_1,...,x_{n*r}) be concatenate of advice columns.
    /// define vector Z = (i_1,...,i_{io}, x_1,...,x_{n*r})
    /// This function is to find the permutation matrix P such that the copy constraints are
    /// equivalent to P * Z - Z = 0. This is invariant relation under our folding scheme
    fn permutation_matrix(&self) -> SparseMatrix<F> {
        let mut sparse_matrix_p = Vec::new();
        let num_advice = self.cs.num_advice_columns();
        let num_rows = self.advice[0].len();
        let num_io = self.instance.len();
        let columns = &self.cs.permutation.columns;
        let instance_column_idx = instance_column_index(columns);

        for (left_col, vec) in self
            .permutation
            .as_ref()
            .unwrap()
            .mapping
            .iter()
            .enumerate()
        {
            for (left_row, cycle) in vec.iter().enumerate() {
                // skip rows that beyond the num_io in instance column
                if let Some(idx) = instance_column_idx {
                    if left_col == idx && left_row >= num_io {
                        continue;
                    }
                }
                let left_col = column_index(left_col, columns);
                let right_col = column_index(cycle.0, columns);
                let left_z_idx = cell_to_z_idx(left_col, left_row, num_rows, num_io);
                let right_z_idx = cell_to_z_idx(right_col, cycle.1, num_rows, num_io);
                sparse_matrix_p.push((left_z_idx, right_z_idx, F::ONE));
            }
        }

        fill_sparse_matrix(&mut sparse_matrix_p, num_advice, num_rows, num_io, columns);
        sparse_matrix_p
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
        if let Some(permutation) = self.permutation.as_mut() {
            permutation.copy(left_column, left_row, right_column, right_row)
        } else {
            error!("permutation is not initialized properly");
            Err(Error::Synthesis)
        }
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
    fn test_assembly() {
        use halo2curves::pasta::Fp;

        const K: u32 = 4;
        let mut inputs = Vec::new();
        for i in 1..10 {
            inputs.push(Fp::from(i as u64));
        }
        let circuit = TestCircuit::new(inputs, Fp::ONE);
        let output = Fp::from_str_vartime("45").unwrap();
        let public_inputs = vec![output];

        let mut td = TableData::<Fp>::new(K, public_inputs);
        let _ = td.assembly(&circuit);

        let mut table = Table::new();
        table.add_row(row!["s0", "s1", "s2", "in", "out"]);
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
