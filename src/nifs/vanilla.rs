use std::marker::PhantomData;

use halo2_proofs::arithmetic::CurveAffine;
use tracing::*;

use super::*;
use crate::{
    commitment::CommitmentKey,
    concat_vec,
    constants::NUM_CHALLENGE_BITS,
    ff::Field,
    plonk::{
        eval::{GetDataForEval, PlonkEvalDomain},
        PlonkInstance, PlonkStructure, PlonkTrace, PlonkWitness, RelaxedPlonkInstance,
        RelaxedPlonkTrace, RelaxedPlonkWitness,
    },
    polynomial::graph_evaluator::GraphEvaluator,
    poseidon::ROTrait,
    sps::SpecialSoundnessVerifier,
};

/// Represent intermediate polynomial terms that arise when folding
/// two polynomial relations into one.
///
/// In the context of the NIFS protocol, when two identical
/// polynomial relations are folded, certain terms (referred
/// to as cross terms) emerge that capture the interaction between
/// the two original polynomials.
pub type CrossTerms<C> = Vec<Box<[<C as CurveAffine>::ScalarExt]>>;

/// Cryptographic commitments to the [`CrossTerms`].
pub type CrossTermCommits<C> = Vec<C>;

/// VanillaFS: Vanilla version of Non Interactive Folding Scheme
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
pub struct VanillaFS<C: CurveAffine> {
    _marker: PhantomData<C>,
}

pub struct VanillaFSProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// digest of public parameter of IVC circuit
    pp_digest: C,
}

impl<C: CurveAffine> VanillaFS<C> {
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
    #[instrument(skip_all)]
    pub fn commit_cross_terms(
        ck: &CommitmentKey<C>,
        S: &PlonkStructure<C::ScalarExt>,
        U1: &RelaxedPlonkInstance<C>,
        W1: &RelaxedPlonkWitness<C::ScalarExt>,
        U2: &PlonkInstance<C>,
        W2: &PlonkWitness<C::ScalarExt>,
    ) -> Result<(CrossTerms<C>, CrossTermCommits<C>), Error> {
        let data = PlonkEvalDomain {
            num_advice: S.num_advice_columns,
            num_lookup: S.num_lookups(),
            challenges: &concat_vec!(&U1.challenges, &[U1.u], &U2.challenges, &[U2.to_relax().u]),
            selectors: &S.selectors,
            fixed: &S.fixed_columns,
            W1s: &W1.W,
            W2s: &W2.W,
        };

        let row_size = data.row_size();

        let evaluation_span = info_span!("evaluation").entered();
        let cross_terms = S
            .custom_gates_lookup_compressed
            .grouped()
            .iter_from_first()
            .map(|optional_expr| match optional_expr {
                Some(expr) => {
                    let evaluator = GraphEvaluator::new(expr);

                    (0..row_size)
                        .into_par_iter()
                        .map(|row_index| {
                            let evaluated = evaluator.evaluate(&data, row_index)?;
                            trace!("row {row_index} evaluated: {evaluated:?}");
                            Result::<_, Error>::Ok(evaluated)
                        })
                        .collect::<Result<Box<[_]>, _>>()
                }
                None => Ok(vec![C::ScalarExt::ZERO; row_size].into_boxed_slice()),
            })
            .collect::<Result<CrossTerms<C>, _>>()?;
        evaluation_span.exit();

        let commit_span = info_span!("commit").entered();
        let cross_term_commits: Vec<C> = cross_terms
            .iter()
            .map(|v| ck.commit(v))
            .collect::<Result<Vec<_>, _>>()?;
        commit_span.exit();

        Ok((cross_terms, cross_term_commits))
    }

    /// Absorb all fields into RandomOracle `RO` & generate challenge based on that
    #[instrument(skip_all)]
    pub(crate) fn generate_challenge(
        pp_digest: &C,
        ro_acc: &mut impl ROTrait<C::Base>,
        U1: &RelaxedPlonkInstance<C>,
        U2: &PlonkInstance<C>,
        cross_term_commits: &[C],
    ) -> Result<<C as CurveAffine>::ScalarExt, Error> {
        Ok(ro_acc
            .absorb_point(pp_digest)
            .absorb(U1)
            .absorb(U2)
            .absorb_point_iter(cross_term_commits.iter())
            .squeeze::<C>(NUM_CHALLENGE_BITS))
    }
}

impl<C: CurveAffine> FoldingScheme<C> for VanillaFS<C> {
    type ProverParam = VanillaFSProverParam<C>;
    type VerifierParam = C;
    type Accumulator = RelaxedPlonkTrace<C>;
    type AccumulatorInstance = RelaxedPlonkInstance<C>;
    type Proof = CrossTermCommits<C>;

    fn setup_params(
        pp_digest: C,
        S: PlonkStructure<C::ScalarExt>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        Ok((VanillaFSProverParam { S, pp_digest }, pp_digest))
    }

    #[instrument(skip_all)]
    fn generate_plonk_trace(
        ck: &CommitmentKey<C>,
        instance: &[C::ScalarExt],
        witness: &[Vec<C::ScalarExt>],
        pp: &VanillaFSProverParam<C>,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<PlonkTrace<C>, Error> {
        Ok(pp
            .S
            .run_sps_protocol(ck, instance, witness, ro_nark, pp.S.num_challenges)?)
    }

    /// Generates a proof of correct folding using the NIFS protocol.
    ///
    /// This method takes two relaxed Plonk instance-witness pairs and calculates the folded instance and witness.
    /// It also computes the cross terms and their commitments.
    ///
    /// # Arguments
    /// * `ck`: The commitment key.
    /// * `pp`: The prover parameter.
    /// * `ro_acc`: The random oracle for the accumulation scheme. Used to securely combine
    ///             multiple verification steps or proofs into a single, updated accumulator.
    /// * `accumulator`: The instance-witness pair for accumulator
    /// * `incoming`: The instance-witness pair from synthesize of circuit
    ///
    /// # Returns
    /// A tuple containing folded accumulator and proof for the folding scheme verifier
    #[instrument(skip_all)]
    fn prove(
        ck: &CommitmentKey<C>,
        pp: &Self::ProverParam,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Self::Accumulator,
        incoming: &[PlonkTrace<C>; 1],
    ) -> Result<(Self::Accumulator, Self::Proof), Error> {
        let incoming = &incoming[0];

        let U1 = &accumulator.U;
        let W1 = &accumulator.W;
        let U2 = &incoming.u;
        let W2 = &incoming.w;

        let (cross_terms, cross_term_commits) =
            Self::commit_cross_terms(ck, &pp.S, U1, W1, U2, W2)?;

        let r = VanillaFS::generate_challenge(&pp.pp_digest, ro_acc, U1, U2, &cross_term_commits)?;

        let U = U1.fold(U2, &cross_term_commits, &r);
        let W = W1.fold(W2, &cross_terms, &r);

        Ok((RelaxedPlonkTrace { U, W }, cross_term_commits))
    }

    /// Verifies the correctness of the folding using the NIFS protocol.
    ///
    /// This method takes a relaxed Plonk instance and a Plonk instance and verifies if they have been correctly folded.
    ///
    /// # Arguments
    /// * `vp`: verifier parameter
    /// * `ro_acc`: The random oracle for the accumulation scheme. Used to securely combine
    ///             multiple verification steps or proofs into a single, updated accumulator.
    /// * `ro_nark`: The random oracle used within the non-interactive argument of knowledge (NARK)
    ///              system. Facilitates the Fiat-Shamir transformation, converting interactive
    ///              proofs to non-interactive by deterministically generating challenges based
    ///              on the protocol's messages.
    /// * `U1`: The relaxed Plonk instance.
    /// * `U2`: The Plonk instance.
    ///
    /// # Returns
    /// The folded relaxed Plonk instance.
    fn verify(
        vp: &Self::VerifierParam,
        ro_nark: &mut impl ROTrait<C::Base>,
        ro_acc: &mut impl ROTrait<C::Base>,
        U1: &Self::AccumulatorInstance,
        U2: &[PlonkInstance<C>; 1],
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<Self::AccumulatorInstance, Error> {
        let U2 = &U2[0];

        U2.sps_verify(ro_nark)?;

        let r = VanillaFS::generate_challenge(vp, ro_acc, U1, U2, cross_term_commits)?;

        Ok(U1.fold(U2, cross_term_commits, &r))
    }
}
