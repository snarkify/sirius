use std::iter;
use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::arithmetic::CurveAffine;

use crate::{
    commitment::CommitmentKey,
    fft::{get_omega_or_inv, ifft},
    plonk::{
        GetChallenges, GetWitness, PlonkStructure, PlonkTrace, RelaxedPlonkInstance,
        RelaxedPlonkTrace,
    },
    polynomial::{
        expression::QueryIndexContext, lagrange::iter_eval_lagrange_polynomials_for_cyclic_group,
    },
};

use super::*;

mod pow_i;
pub use pow_i::{iter_eval_of_pow_i, Error as PowIError};

/// ProtoGalaxy: Non Interactive Folding Scheme that implements main protocol defined in paper
/// [protogalaxy](https://eprint.iacr.org/2023/1106)
///
#[derive(Clone, Debug)]
pub struct ProtoGalaxy<C: CurveAffine> {
    _marker: PhantomData<C>,
}

pub struct ProtoGalaxyProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// digest of public parameter of IVC circuit
    pp_digest: C,
}

pub struct ProtoGalaxyProof<F: PrimeField> {
    // TODO: add comments
    pub poly_F: Vec<F>,
    pub poly_K: Vec<F>,
}

impl<C: CurveAffine> FoldingScheme<C> for ProtoGalaxy<C> {
    type ProverParam = ProtoGalaxyProverParam<C>;
    type VerifierParam = C;
    type Accumulator = RelaxedPlonkTrace<C>;
    type AccumulatorInstance = RelaxedPlonkInstance<C>;
    type Proof = ProtoGalaxyProof<C::ScalarExt>;

    fn setup_params(
        pp_digest: C,
        S: PlonkStructure<C::ScalarExt>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        Ok((ProtoGalaxyProverParam { S, pp_digest }, pp_digest))
    }

    // TODO: if this function turned out to be the same, consider move to trait
    fn generate_plonk_trace(
        ck: &CommitmentKey<C>,
        instance: &[C::ScalarExt],
        witness: &[Vec<C::ScalarExt>],
        pp: &Self::ProverParam,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<PlonkTrace<C>, Error> {
        let (u, w) =
            pp.S.run_sps_protocol(ck, instance, witness, ro_nark, pp.S.num_challenges)?;
        Ok(PlonkTrace { u, w })
    }

    fn prove(
        ck: &CommitmentKey<C>,
        pp: &Self::ProverParam,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Self::Accumulator,
        incoming: &PlonkTrace<C>,
    ) -> Result<(Self::Accumulator, Self::Proof), Error> {
        // TODO: avoid clone of the trace?
        Self::prove_mult(ck, pp, ro_acc, accumulator, &[incoming.clone()])
    }

    fn verify(
        vp: &Self::VerifierParam,
        ro_nark: &mut impl ROTrait<C::Base>,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Self::AccumulatorInstance,
        incoming: &PlonkInstance<C>,
        proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Error> {
        Self::verify_mult(vp, ro_nark, ro_acc, accumulator, &[incoming.clone()], proof)
    }
}

impl<C: CurveAffine> MultifoldingScheme<C> for ProtoGalaxy<C> {
    /// Generates multi-folding proof using the protogalaxy protocol.
    ///
    /// This method takes one accumulator instance-witness pair and multiple incoming instance-witness pair
    /// then output the new folded accumulator instance-witness pair
    ///
    /// # Arguments
    /// * `ck`: The commitment key.
    /// * `pp`: The prover parameter.
    /// * `ro_acc`: The random oracle for the accumulation scheme. Used to securely combine
    ///             multiple verification steps or proofs into a single, updated accumulator.
    /// * `accumulator`: The instance-witness pair for accumulator
    /// * `incoming`: a vector of instance-witness pair from synthesize of circuit
    ///
    /// # Returns
    /// A tuple containing folded accumulator and proof for the multi-folding verifier
    fn prove_mult(
        _ck: &CommitmentKey<C>,
        _pp: &Self::ProverParam,
        _ro_acc: &mut impl ROTrait<C::Base>,
        _accumulator: &Self::Accumulator,
        _incoming: &[PlonkTrace<C>],
    ) -> Result<(Self::Accumulator, Self::Proof), Error> {
        todo!()
    }

    /// Verifies the correctness of the multi-folding prover defined in the protogalaxy protocol.
    ///
    /// This method takes a accumulator instance and multiple incoming instances
    /// then it generated the new accumulator instance
    ///
    /// # Arguments
    /// * `vp`: verifier parameter
    /// * `ro_acc`: The random oracle for the accumulation scheme. Used to securely combine
    ///             multiple verification steps or proofs into a single, updated accumulator.
    /// * `ro_nark`: The random oracle used within the non-interactive argument of knowledge (NARK)
    ///              system. Facilitates the Fiat-Shamir transformation, converting interactive
    ///              proofs to non-interactive by deterministically generating challenges based
    ///              on the protocol's messages.
    /// * `accumulator`: The Accumulator instance.
    /// * `incoming`:  a vector of instances to be folded
    /// * `proof`:   the proof generated by prove_mult
    ///
    /// # Returns
    /// The new folded accumulator instance
    fn verify_mult(
        _vp: &Self::VerifierParam,
        _ro_nark: &mut impl ROTrait<C::Base>,
        _ro_acc: &mut impl ROTrait<C::Base>,
        _accumulator: &Self::AccumulatorInstance,
        _incoming: &[PlonkInstance<C>],
        _proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Error> {
        todo!()
    }
}

// TODO: consider remove this scope before merge
mod compute_g {
    use super::*;

    /// given a vector of {w_i}, here w_i is a vector
    /// compute weighted sum: sum_i L_i(gamma)c_i
    /// Here w_i can be vector of challenges or vector of witnesses
    /// # Parameters
    ///
    /// - `gamma` - eval Lagrange polynomials at this point
    /// - `log_n` - `log2(n+1)`, where `n` - number of instances to be folded
    /// - `ws` - `{w_0,..., w_n}`, vector of vector of F
    ///
    /// # Result
    ///
    /// the vector of weighted sum
    /// `L_0(gamma)w_0 + L_1(gamma)w_1, ..., L_n(gamma)w_n`
    fn fold_vectors<F: PrimeField>(gamma: F, log_n: usize, ws: &[Vec<F>]) -> Vec<F> {
        let ll: Vec<F> = iter_eval_lagrange_polynomials_for_cyclic_group(gamma, log_n).collect();
        (0..ws[0].len())
            .into_par_iter()
            .map(|idx| {
                ll.iter()
                    .zip(ws.iter())
                    .map(|(l_i, w_i)| *l_i * w_i[idx])
                    .fold(F::ZERO, |sum, val| sum + val)
            })
            .collect()
    }

    /// given a vector of {w_i}, here witness w_i is vector of vector
    /// compute and return vector sum_i L_i(gamma)w_i
    fn fold_witnesses<F: PrimeField>(gamma: F, log_n: usize, wss: &[&[Vec<F>]]) -> Vec<Vec<F>> {
        let ll: Vec<F> = iter_eval_lagrange_polynomials_for_cyclic_group(gamma, log_n).collect();
        (0..wss[0].len())
            .into_par_iter()
            .map(|ii| {
                (0..wss[0][ii].len())
                    .into_par_iter()
                    .map(|jj| {
                        ll.iter()
                            .zip(wss.iter())
                            .map(|(l_k, w_k)| *l_k * w_k[ii][jj])
                            .fold(F::ZERO, |sum, val| sum + val)
                    })
                    .collect()
            })
            .collect()
    }

    fn evaluate_G_poly<F: PrimeField>(
        beta: F,
        gamma: F,
        S: &PlonkStructure<F>,
        traces: &[(impl GetChallenges<F> + GetWitness<F>)],
    ) -> F {
        let num_instances = traces.len().next_power_of_two();
        //let witnesses = traces.iter().map(|trace| trace.get_witness()).collect();
        //let folded_w = fold_vectors(gamma, num_instances, witnesses);
        F::ZERO
    }

    fn compute_G_poly<F: PrimeField>(
        // number of instances to be folded
        k: usize,
        // beta: the folded beta value
        beta: F,
        S: &PlonkStructure<F>,
        // first one is accumulator, the rest k traces are instances to be folded
        traces: &[(impl GetChallenges<F> + GetWitness<F>)],
    ) -> Vec<F> {
        let ctx = QueryIndexContext {
            num_fixed: S.fixed_columns.len(),
            num_advice: S.num_advice_columns,
            num_selectors: S.selectors.len(),
            num_challenges: S.num_challenges,
            num_lookups: S.num_lookups(),
        };
        let d = S.gates.iter().map(|poly| poly.degree(&ctx)).max().unwrap();
        let num_pts = (k * d + 1).next_power_of_two();
        let log_n = num_pts.checked_ilog2().unwrap();
        let generator: F = get_omega_or_inv(log_n, true);
        // TODO: we can skip k+1 of the evaluations because already know them:
        // {F(alpha), 0,...,0}
        let mut a: Vec<F> = iter::successors(Some(F::ONE), move |val| Some(*val * generator))
            .take(num_pts)
            .map(|pt| evaluate_G_poly(beta, pt, S, traces))
            .collect();
        ifft(&mut a, log_n);
        a
    }
}
