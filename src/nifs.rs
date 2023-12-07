//! NIFS: Non Interactive Folding Scheme
//!
//! NIFS protocal allow us to fold two identical polynomial relations into one
//! e.g. the polynomial relation can be derived from different way, e.g.:
//! - Custom plonkish gate
//! - The permutation polynomial derived from plonk copy constraints
//!
//! For more details look at:
//! - Paragraph '3. Folding scheme' at [Nova whitepaper](https://eprint.iacr.org/2021/370)
//! - [nifs module](https://github.com/microsoft/Nova/blob/main/src/nifs.rs) at [Nova codebase](https://github.com/microsoft/Nova)
use crate::commitment::CommitmentKey;
use crate::constants::NUM_CHALLENGE_BITS;
use crate::plonk::{
    PlonkEvalDomain, PlonkInstance, PlonkStructure, PlonkWitness, RelaxedPlonkInstance,
    RelaxedPlonkWitness, TableData,
};
use crate::polynomial::CHALLENGE_TYPE;
use crate::poseidon::{AbsorbInRO, ROTrait};
use halo2_proofs::arithmetic::CurveAffine;
use rayon::prelude::*;
use std::marker::PhantomData;

/// Represent intermediate polynomial terms that arise when folding
/// two polynomial relations into one.
///
/// In the context of the NIFS protocol, when two identical
/// polynomial relations are folded, certain terms (referred
/// to as cross terms) emerge that capture the interaction between
/// the two original polynomials.
pub type CrossTerms<C> = Vec<Vec<<C as CurveAffine>::ScalarExt>>;

/// Cryptographic commitments to the [`CrossTerms`].
pub type CrossTermCommits<C> = Vec<C>;

/// NIFS: Non Interactive Folding Scheme
///
/// Given a polynomial relation `P(x_1,...,x_n)` with polynomial degree `d.
/// After folding two such (identical) relations, we have:
/// - `P(x_1 + r*y_1, ..., x_n + r * y_n) = P(x_1, ..., x_n) + \sum_{k=1}^{d-1} T_k + r^d * P(y_1,...,y_n)`
/// - `cross_term = [T_1,...,T_{d-1}]`
/// - `cross_term_commits = [Comm(T_1),...,Comm(T_{d-1})]`
///
/// Please refer to: [notes](https://hackmd.io/@chaosma/BJvWmnw_h#31-NIFS)
// TODO Replace links to either the documentation right here, or the official Snarkify resource
#[derive(Clone, Debug)]
pub struct NIFS<C: CurveAffine, RO: ROTrait<C>> {
    pub(crate) cross_term_commits: CrossTermCommits<C>,
    _marker: PhantomData<RO>,
}

impl<C: CurveAffine, RO: ROTrait<C>> NIFS<C, RO> {
    /// Commits to the cross terms between two Plonk instance-witness pairs.
    ///
    /// This method calculates the cross terms and their commitments, which
    /// are essential for the folding process.
    ///
    /// # Arguments
    /// * `ck`: The commitment key.
    /// * `S`: the Plonk structure shared by both instance-witness pairs.
    /// * `U1`: The first relaxed Plonk instance.
    /// * `W1`: The witness for the first relaxed Plonk instance.
    /// * `U2`: The second Plonk instance.
    /// * `W2`: The witness for the second Plonk instance.
    ///
    /// # Returns
    /// A tuple containing the cross terms and their commitments.
    ///
    /// # Context
    /// The cross terms are derived from the polynomial relations
    /// of the two instance-witness pairs. They play a crucial role
    /// in the folding process, allowing two polynomial relations
    /// to be combined into one.
    pub fn commit_cross_terms(
        ck: &CommitmentKey<C>,
        S: &PlonkStructure<C>,
        U1: &RelaxedPlonkInstance<C>,
        W1: &RelaxedPlonkWitness<C::ScalarExt>,
        U2: &PlonkInstance<C>,
        W2: &PlonkWitness<C::ScalarExt>,
    ) -> (CrossTerms<C>, CrossTermCommits<C>) {
        let offset = S.fixed_offset();
        let num_row = S.fixed_columns[0].len();
        let normalized = S.poly.fold_transform(offset, S.num_fold_vars());
        let r_index = normalized.num_challenges() - 1;
        let degree = S.poly.degree_for_folding(offset);
        let data = PlonkEvalDomain {
            S,
            U1,
            W1,
            U2: &U2.to_relax(),
            W2: &W2.to_relax(S.k),
        };
        let cross_terms: Vec<Vec<C::ScalarExt>> = (1..degree)
            .map(|k| normalized.coeff_of((0, r_index, CHALLENGE_TYPE), k))
            .map(|multipoly| {
                (0..num_row)
                    .into_par_iter()
                    .map(|row| multipoly.eval(row, &data))
                    .collect()
            })
            .collect();
        let cross_term_commits: Vec<C> = cross_terms.iter().map(|v| ck.commit(v)).collect();
        (cross_terms, cross_term_commits)
    }

    /// Generates a proof of correct folding using the NIFS protocol.
    ///
    /// This method takes two relaxed Plonk instance-witness pairs and calculates the folded instance and witness.
    /// It also computes the cross terms and their commitments.
    ///
    /// # Arguments
    /// * `ck`: The commitment key.
    /// * `ro`: A mutable reference to the random oracle.
    /// * `td`: Table data associated with the (strict not relaxed) plonk instance to be folded
    /// * `U1`: The first relaxed Plonk instance.
    /// * `W1`: The witness for the first relaxed Plonk instance.
    ///
    /// # Returns
    /// A tuple containing the NIFS instance and the folded relaxed Plonk instance-witness pair.
    ///
    /// # Context
    /// The prove function is central to the NIFS protocol. It demonstrates
    /// that two polynomial relations have been correctly folded into one,
    /// providing cryptographic evidence of this fact.
    pub fn prove(
        ck: &CommitmentKey<C>,
        ro: &mut RO,
        td: &TableData<C::ScalarExt>,
        U1: &RelaxedPlonkInstance<C>,
        W1: &RelaxedPlonkWitness<C::ScalarExt>,
    ) -> (
        Self,
        (RelaxedPlonkInstance<C>, RelaxedPlonkWitness<C::ScalarExt>),
    ) {
        // TODO: hash gate into ro
        let S = td.plonk_structure(ck);
        S.absorb_into(ro);

        let (U2, W2) = td.run_sps_protocol_0(ck);
        U2.absorb_into(ro);
        U1.absorb_into(ro);
        let (cross_terms, cross_term_commits) = Self::commit_cross_terms(ck, &S, U1, W1, &U2, &W2);
        cross_term_commits
            .iter()
            .for_each(|cm| ro.absorb_point(*cm));
        let r = ro.squeeze(NUM_CHALLENGE_BITS);
        let U = U1.fold(&U2, &cross_term_commits, &r);
        let W = W1.fold(&W2, &cross_terms, &r);
        (
            Self {
                cross_term_commits,
                _marker: PhantomData,
            },
            (U, W),
        )
    }

    /// Verifies the correctness of the folding using the NIFS protocol.
    ///
    /// This method takes a relaxed Plonk instance and a Plonk instance and verifies if they have been correctly folded.
    ///
    /// # Arguments
    /// * `ro`: A mutable reference to the random oracle.
    /// * `S`: The Plonk structure shared by both instances.
    /// * `U1`: The relaxed Plonk instance.
    /// * `U2`: The Plonk instance.
    ///
    /// # Returns
    /// The folded relaxed Plonk instance.
    pub fn verify(
        &self,
        ro: &mut RO,
        S: &PlonkStructure<C>,
        U1: RelaxedPlonkInstance<C>,
        U2: PlonkInstance<C>,
    ) -> RelaxedPlonkInstance<C> {
        S.absorb_into(ro);
        U2.absorb_into(ro);
        /*
        if S.num_challenges > 0 {
            // the first challenge is used to combined multiple gates for instance U2
            U2.challenges = vec![ro.squeeze(NUM_CHALLENGE_BITS)];
        }
        */

        U1.absorb_into(ro);
        self.cross_term_commits
            .iter()
            .for_each(|cm| ro.absorb_point(*cm));
        let r = ro.squeeze(NUM_CHALLENGE_BITS);
        U1.fold(&U2, &self.cross_term_commits, &r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};
    use ff::PrimeField;
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Error, Instance};
    use halo2curves::group::ff::FromUniformBytes;

    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

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
            Self::Config {
                pconfig: MainGate::configure(meta),
                instance,
            }
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

    /// this function will fold two plonk witness-instance pairs consecutively
    /// it folds the first instance into a default relaxed plonk instance to get folded (f_U, f_W)
    /// next it folds the second instance into the first folded (f_U, f_W)
    /// there are several things to be checked: whether two such instances satisfy plonk relation
    /// (i.e. is_sat), whether two such folded instance satisfy relaxed plonk relation (i.e.
    /// is_sat_relax)
    /// We have to check:
    /// (1) each of the two individual witness-instance pairs satisfy custom gates relation as well
    /// as copy constrains relation (i.e. permutation relation)
    /// (2) the first folded witness-instance pair satisfies the relaxed polynomial relation and
    /// copy constrains relation
    /// (3) the second folded witness-instance pair satisfies the relaxed polynomial relation  and
    /// copy constrains relation
    fn fold_instances<C: CurveAffine<ScalarExt = F>, F: PrimeField, RO: ROTrait<C>>(
        ck: &CommitmentKey<C>,
        ro1: &mut RO,
        ro2: &mut RO,
        td1: &TableData<F>,
        td2: &TableData<F>,
    ) {
        let S = td1.plonk_structure(ck);
        let mut f_U =
            RelaxedPlonkInstance::new(td1.instance.len(), S.num_challenges, S.round_sizes.len());
        let mut f_W = RelaxedPlonkWitness::new(td1.k, &S.round_sizes);
        let (U1, W1) = td1.run_sps_protocol_0(ck);
        let res = S.is_sat(ck, &U1, &W1);
        assert!(res.is_ok());

        let (nifs, (_U, W)) = NIFS::prove(ck, ro1, td1, &f_U, &f_W);
        let U = nifs.verify(ro2, &S, f_U, U1);
        assert_eq!(U, _U);

        f_U = U;
        f_W = W;
        let res = S.is_sat_relaxed(ck, &f_U, &f_W);
        assert!(res.is_ok());
        let perm_res = S.is_sat_perm(&f_U, &f_W);
        assert!(perm_res.is_ok());

        let (U1, W1) = td2.run_sps_protocol_0(ck);
        let res = S.is_sat(ck, &U1, &W1);
        assert!(res.is_ok());

        let (nifs, (_U, _W)) = NIFS::prove(ck, ro1, td2, &f_U, &f_W);
        let U = nifs.verify(ro2, &S, f_U, U1);
        assert_eq!(U, _U);

        f_U = _U;
        f_W = _W;
        let res = S.is_sat_relaxed(ck, &f_U, &f_W);
        assert!(res.is_ok());
        let perm_res = S.is_sat_perm(&f_U, &f_W);
        assert!(perm_res.is_ok());
    }

    /// calculate smallest w such that 2^w >= n*(2^K)
    fn smallest_power(n: usize, K: u32) -> usize {
        let n_f64 = n as f64;
        let mul_res = n_f64 * (2f64.powi(K as i32));
        let log_result = mul_res.log2().ceil();
        log_result as usize
    }

    #[test]
    fn test_nifs_no_lookup() {
        use crate::poseidon::PoseidonHash;
        use halo2curves::pasta::{EqAffine, Fp, Fq};
        use poseidon::Spec;

        const K: u32 = 4;
        let mut inputs1 = Vec::new();
        let mut inputs2 = Vec::new();
        for i in 1..10 {
            inputs1.push(Fp::from(i));
            inputs2.push(Fp::from(i + 1));
        }
        let circuit1 = TestCircuit::new(inputs1, Fp::from_str_vartime("2").unwrap());
        let output1 = Fp::from_str_vartime("4097").unwrap();
        let public_inputs1 = vec![output1];
        let mut td1 = TableData::<Fp>::new(K, public_inputs1);
        let _ = td1.assembly(&circuit1);

        let circuit2 = TestCircuit::new(inputs2, Fp::from_str_vartime("3").unwrap());
        let output2 = Fp::from_str_vartime("93494").unwrap();
        let public_inputs2 = vec![output2];
        let mut td2 = TableData::<Fp>::new(K, public_inputs2);
        let _ = td2.assembly(&circuit2);

        let p1 = smallest_power(td1.cs.num_advice_columns(), K);
        let p2 = smallest_power(td1.cs.num_selectors() + td1.cs.num_fixed_columns(), K);
        let ck = CommitmentKey::<EqAffine>::setup(p1.max(p2), b"test");

        type PH = PoseidonHash<EqAffine, Fq, T, RATE>;
        let spec = Spec::<Fq, T, RATE>::new(R_F, R_P);
        let mut ro1 = PH::new(spec.clone());
        let mut ro2 = PH::new(spec);
        fold_instances(&ck, &mut ro1, &mut ro2, &td1, &td2);
    }
}
