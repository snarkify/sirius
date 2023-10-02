//! This module defines the TableData and Plonk related types for working with
//! halo2 circuits. It provides functionality to retrieve PlonkStructure and witness
//! data, as well as defining various methods used by the folding scheme.
//!
//! The main types defined in this module are:
//! - PlonkStructure: Represents the structure of a Plonk circuit and its associated data.
//! - PlonkInstance: Represents an instance of a Plonk circuit.
//! - PlonkWitness: Represents the witness data for a Plonk circuit.
//! - RelaxedPlonkInstance: Represents an instance of a relaxed Plonk circuit.
//! - RelaxedPlonkWitness: Represents the witness data for a relaxed Plonk circuit.
//!
//! The module also provides implementations of the AbsorbInRO trait for
//! PlonkStructure, PlonkInstance, and RelaxedPlonkInstance.
//!
//! Additionally, it defines a method is_sat on PlonkStructure to determine if
//! a given Plonk instance and witness satisfy the circuit constraints.
use crate::{
    commitment::CommitmentKey,
    plonk::util::{cell_to_z_idx, column_index, fill_sparse_matrix},
    polynomial::{
        sparse::{matrix_multiply, SparseMatrix},
        Expression, MultiPolynomial, Query,
    },
    poseidon::{AbsorbInRO, ROTrait},
    util::{batch_invert_assigned, fe_to_fe},
};
use ff::{Field, PrimeField};
use group::Curve;
use halo2_proofs::{
    arithmetic::{best_multiexp, CurveAffine},
    circuit::Value,
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge, Circuit, Column, ConstraintSystem, Error,
        Fixed, FloorPlanner, Instance, Selector,
    },
    poly::Rotation,
};
use rayon::prelude::*;
use std::collections::HashMap;
pub mod permutation;
pub mod util;

#[derive(Clone, PartialEq)]
pub struct PlonkStructure<C: CurveAffine> {
    // k is a parameter such that 2^k is the total number of rows
    pub(crate) k: usize,
    pub(crate) fixed_columns: Vec<Vec<C::ScalarExt>>,
    pub(crate) num_advice_columns: usize,
    pub(crate) gate: MultiPolynomial<C::ScalarExt>,
    pub(crate) fixed_commitment: C, // concatenate num_fixed_columns together, then commit
    pub(crate) permutation_matrix: SparseMatrix<C::ScalarExt>,
}

#[derive(Clone, Debug)]
pub struct PlonkInstance<C: CurveAffine> {
    pub(crate) W_commitment: C, // concatenate num_advice_columns together, then commit
    pub(crate) instance: Vec<C::ScalarExt>, // inst = [X0, X1]
    pub(crate) y: C::ScalarExt,
}

#[derive(Clone, Debug)]
pub struct PlonkWitness<F: PrimeField> {
    pub(crate) num_advice_columns: usize,
    pub(crate) W: Vec<F>, // concatenate num_advice_columns together
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelaxedPlonkInstance<C: CurveAffine> {
    pub(crate) W_commitment: C,
    pub(crate) instance: Vec<C::ScalarExt>,
    pub(crate) E_commitment: C,
    pub(crate) u: C::ScalarExt,
    pub(crate) y: C::ScalarExt,
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkWitness<F: PrimeField> {
    pub(crate) num_advice_columns: usize,
    pub(crate) W: Vec<F>,
    pub(crate) E: Vec<F>,
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for PlonkStructure<C> {
    // TODO: add hash of other fields including gates
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point(self.fixed_commitment);
    }
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for PlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point(self.W_commitment);
        for inst in self.instance.iter().take(2) {
            ro.absorb_base(fe_to_fe(*inst));
        }
    }
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point(self.W_commitment);
        for inst in self.instance.iter().take(2) {
            ro.absorb_base(fe_to_fe(*inst));
        }
        ro.absorb_base(fe_to_fe(self.u));
        ro.absorb_point(self.E_commitment);
    }
}

impl<C: CurveAffine> PlonkStructure<C> {
    pub fn is_sat<F>(
        &self,
        ck: &CommitmentKey<C>,
        U: &PlonkInstance<C>,
        W: &PlonkWitness<F>,
    ) -> Result<(), String>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        let nrow = 2usize.pow(self.k as u32);
        let U2 = RelaxedPlonkInstance::new(U.instance.len());
        let W2 = RelaxedPlonkWitness::new(self.k as u32, self.num_advice_columns);
        let res: usize = (0..nrow)
            .into_par_iter()
            .map(|row| {
                self.gate
                    .eval(row, self, &U.to_relax(), &W.to_relax(), &U2, &W2)
            })
            .filter(|v| F::ZERO.ne(v))
            .count();

        if U.W_commitment == ck.commit(&W.W) && res == 0 {
            Ok(())
        } else {
            Err("plonk relation not satisfied".to_string())
        }
    }

    pub fn is_sat_relaxed<F>(
        &self,
        ck: &CommitmentKey<C>,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), String>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        let nrow = 2usize.pow(self.k as u32);
        let U2 = RelaxedPlonkInstance::new(U.instance.len());
        let W2 = RelaxedPlonkWitness::new(self.k as u32, self.num_advice_columns);
        let num_fixed = self.fixed_columns.len();
        let u_index = num_fixed + self.num_advice_columns + 1;
        let poly = self.gate.homogeneous(num_fixed, u_index);
        let res: usize = (0..nrow)
            .into_par_iter()
            .map(|row| poly.eval(row, self, U, W, &U2, &W2))
            .enumerate()
            .filter(|(i, v)| W.E[*i].ne(v))
            .count();

        let actual_W_commit = ck.commit(&W.W);
        let actual_E_commit = ck.commit(&W.E);

        match (
            res == 0,
            U.W_commitment.eq(&actual_W_commit),
            U.E_commitment.eq(&actual_E_commit),
        ) {
            (true, true, true) => Ok(()),
            (false, _, _) => Err(format!(
                "relaxed plonk relation not satisfied on {} out of {} rows",
                res, nrow
            )),
            (true, false, false) => Err(format!(
                "both commitment of witnesses W & E is not match:
                    W: Expected: {:?}, Actual: {:?},
                    E: Expected: {:?}, Actual: {:?}",
                U.W_commitment, actual_W_commit, U.E_commitment, actual_E_commit
            )),
            (true, false, true) => Err(format!(
                "commitment of witness W is not match: Expected: {:?}, Actual: {:?}",
                U.W_commitment, actual_W_commit
            )),
            (true, true, false) => Err(format!(
                "commitment of witness E is not match: Expected: {:?}, Actual: {:?}",
                U.E_commitment, actual_E_commit
            )),
        }
    }

    // permutation check for folding instance-witness pair
    pub fn is_sat_perm<F>(
        &self,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), String>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        let Z = U
            .instance
            .clone()
            .into_iter()
            .chain(W.W.clone())
            .collect::<Vec<_>>();
        let y = matrix_multiply(&self.permutation_matrix, &Z[..]);
        let diff = y
            .into_iter()
            .zip(Z)
            .map(|(y, z)| y - z)
            .enumerate()
            .filter(|(_, d)| F::ZERO.ne(d))
            .count();
        if diff == 0 {
            Ok(())
        } else {
            Err("permutation check failed".to_string())
        }
    }
}

impl<C: CurveAffine> PlonkInstance<C> {
    pub fn to_relax(&self) -> RelaxedPlonkInstance<C> {
        RelaxedPlonkInstance {
            W_commitment: self.W_commitment,
            instance: self.instance.clone(),
            E_commitment: C::identity(),
            u: C::ScalarExt::ONE,
            y: self.y,
        }
    }
}

impl<C: CurveAffine> RelaxedPlonkInstance<C> {
    pub fn new(num_io: usize) -> Self {
        Self {
            W_commitment: CommitmentKey::<C>::default_value(),
            E_commitment: CommitmentKey::<C>::default_value(),
            u: C::ScalarExt::ONE,
            instance: vec![C::ScalarExt::ZERO; num_io],
            y: C::ScalarExt::ONE,
        }
    }

    /// Folds a `RelaxedPlonkInstance` with another `PlonkInstance` while preserving their Plonk relation.
    ///
    /// This function combines the current relaxed Plonk instance with a given Plonk instance by
    /// computing new commitments, instances, and scalar values using provided cross-term
    /// commitments and random value `r`.
    ///
    /// # Arguments
    /// * `U2`: A `PlonkInstance` used to combine with the current relaxed Plonk instance.
    /// * `cross_term_commits`: The commitments of the cross terms used to calculate the folded
    /// value comm_E
    /// * `r`: A random scalar value used for combining the instances and commitments.
    ///
    /// # Returns
    /// The folded `RelaxedPlonkInstance` after combining the instances and commitments.
    /// for detail of how fold works, please refer to: [nifs](https://hackmd.io/d7syox5tTeaxkepc9nLvHw?view#31-NIFS)
    pub fn fold(&self, U2: &PlonkInstance<C>, cross_term_commits: &[C], r: &C::ScalarExt) -> Self {
        let comm_W = self.W_commitment + best_multiexp(&[*r], &[U2.W_commitment]).into();
        let instance = self
            .instance
            .par_iter()
            .zip(&U2.instance)
            .map(|(a, b)| *a + *r * b)
            .collect::<Vec<C::ScalarExt>>();
        let u = self.u + *r;
        let y = self.y + *r * U2.y;

        let comm_E = cross_term_commits
            .iter()
            .enumerate()
            .map(|(k, tk)| best_multiexp(&[r.pow([k as u64 + 1, 0, 0, 0])], &[*tk]).into())
            .fold(self.E_commitment, |acc, x| (acc + x).into());

        RelaxedPlonkInstance {
            W_commitment: comm_W.to_affine(),
            instance,
            E_commitment: comm_E,
            u,
            y,
        }
    }
}

impl<F: PrimeField> PlonkWitness<F> {
    pub fn to_relax(&self) -> RelaxedPlonkWitness<F> {
        let num_advice_columns = self.num_advice_columns;
        let len_E = self.W.len() / num_advice_columns;
        let E = vec![F::ZERO; len_E];
        RelaxedPlonkWitness {
            num_advice_columns,
            W: self.W.clone(), // TODO: avoid clone
            E,
        }
    }
}

impl<F: PrimeField> RelaxedPlonkWitness<F> {
    // nc: num_advice_columns in plonk gate
    pub fn new(k: u32, nc: usize) -> Self {
        let mut W = Vec::new();
        let mut E = Vec::new();
        W.resize(2usize.pow(k) * nc, F::ZERO);
        E.resize(2usize.pow(k), F::ZERO);
        Self {
            num_advice_columns: nc,
            W,
            E,
        }
    }

    pub fn fold(&self, W2: &PlonkWitness<F>, cross_terms: &[Vec<F>], r: &F) -> Self {
        let W = self
            .W
            .par_iter()
            .zip(W2.W.par_iter())
            .map(|(w1, w2)| *w1 + *r * *w2)
            .collect::<Vec<_>>();
        let E = self
            .E
            .par_iter()
            .enumerate()
            .map(|(i, ei)| {
                let mut r_power = F::ONE;
                cross_terms.iter().fold(*ei, |acc, tk| {
                    r_power *= *r;
                    acc + r_power * tk[i]
                })
            })
            .collect::<Vec<_>>();

        RelaxedPlonkWitness {
            W,
            num_advice_columns: self.num_advice_columns,
            E,
        }
    }
}

pub struct TableData<F: PrimeField> {
    // TODO: without usable_rows still safe?
    pub(crate) k: u32,
    pub(crate) cs: ConstraintSystem<F>,
    pub(crate) fixed: Vec<Vec<Assigned<F>>>,
    pub(crate) instance: Vec<F>,
    pub(crate) advice: Vec<Vec<Assigned<F>>>,
    pub(crate) challenges: HashMap<usize, F>,
    pub(crate) permutation: Option<permutation::Assembly>,
}

impl<F: PrimeField> TableData<F> {
    pub fn new(k: u32, instance: Vec<F>) -> Self {
        let cs = ConstraintSystem::default();
        TableData {
            k,
            cs,
            instance,
            fixed: vec![],
            advice: vec![],
            challenges: HashMap::new(),
            permutation: None,
        }
    }

    pub fn assembly<ConcreteCircuit: Circuit<F>>(
        &mut self,
        circuit: &ConcreteCircuit,
    ) -> Result<(), Error> {
        let config = ConcreteCircuit::configure(&mut self.cs);
        self.permutation = Some(permutation::Assembly::new(
            (1 << self.k) as usize,
            &self.cs.permutation,
        ));
        let n = 1u64 << self.k;
        assert!(self.cs.num_instance_columns() == 1);
        self.fixed = vec![vec![F::ZERO.into(); n as usize]; self.cs.num_fixed_columns()];
        self.advice = vec![vec![F::ZERO.into(); n as usize]; self.cs.num_advice_columns()];
        ConcreteCircuit::FloorPlanner::synthesize(
            self,
            circuit,
            config.clone(),
            vec![], // TODO: make sure constants not needed
        )?;
        Ok(())
    }

    pub fn plonk_structure<C: CurveAffine<ScalarExt = F>>(
        &self,
        ck: &CommitmentKey<C>,
    ) -> PlonkStructure<C> {
        let fixed_columns = batch_invert_assigned(&self.fixed);
        // TODO: avoid clone
        let fixed_commitment = ck.commit(
            &fixed_columns
                .clone()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>()[..],
        );
        let num_fixed = self.cs.num_fixed_columns();
        let num_advice = self.cs.num_advice_columns();
        let y = Expression::Polynomial(Query {
            index: num_fixed + num_advice,
            rotation: Rotation(0),
        });
        // suppose we have n polynomial expression: p_1,p_2,...,p_n
        // we combined them together as one: combined_poly = p_1*y^{n-1}+p_2*y^{n-2}+...+p_n
        let combined_poly: MultiPolynomial<C::ScalarExt> = self
            .cs
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter())
            .map(|expr| Expression::from_halo2_expr(expr, num_fixed))
            .fold(Expression::Constant(F::ZERO), |acc, expr| {
                Expression::Sum(
                    Box::new(expr),
                    Box::new(Expression::Product(Box::new(acc), Box::new(y.clone()))),
                )
            })
            .expand();
        let permutation_matrix = self.permutation_matrix();

        PlonkStructure {
            k: self.k as usize,
            fixed_columns,
            num_advice_columns: self.cs.num_advice_columns(),
            gate: combined_poly,
            fixed_commitment,
            permutation_matrix,
        }
    }

    pub fn plonk_instance<C: CurveAffine<ScalarExt = F>>(
        &self,
        ck: &CommitmentKey<C>,
    ) -> PlonkInstance<C> {
        let W = self.plonk_witness().W;
        let W_commitment = ck.commit(&W[..]);
        let mut instance: Vec<C::ScalarExt> = Vec::new();
        for inst in self.instance.iter() {
            instance.push(*inst)
        }
        PlonkInstance {
            W_commitment,
            instance,
            y: F::ONE, // just a place holder, will be replaced later
        }
    }

    pub fn plonk_witness(&self) -> PlonkWitness<F> {
        assert!(!self.advice.is_empty()); // should call TableData.assembly() first
        let mut advice_columns = batch_invert_assigned(&self.advice);
        let W = advice_columns
            .iter_mut()
            .flat_map(|w_i| {
                w_i.resize(2usize.pow(self.k), F::ZERO);
                w_i.drain(..)
            })
            .collect::<Vec<_>>();
        PlonkWitness {
            num_advice_columns: self.advice[0].len(),
            W,
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
    pub(crate) fn permutation_matrix(&self) -> SparseMatrix<F> {
        let mut sparse_matrix_p = Vec::new();
        let num_advice = self.cs.num_advice_columns();
        let num_rows = self.advice[0].len();
        let num_io = self.instance.len();
        let columns = &self.cs.permutation.columns;

        for (left_col, vec) in self
            .permutation
            .as_ref()
            .unwrap()
            .mapping
            .iter()
            .enumerate()
        {
            for (left_row, cycle) in vec.iter().enumerate() {
                // skip because we don't account for row that beyond the num_io in instance column
                if left_col == 0 && left_row >= num_io {
                    continue;
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

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        assert!(column.index() == 0); // require just single instance
        self.instance
            .get(row)
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
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        if let Some(permutation) = self.permutation.as_mut() {
            permutation.copy(left_column, left_row, right_column, right_row)
        } else {
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
    use ff::PrimeField;
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
        use ff::Field;
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
