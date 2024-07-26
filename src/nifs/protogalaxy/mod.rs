use std::{iter, marker::PhantomData};

use halo2_proofs::arithmetic::{self, CurveAffine, Field};
use tracing::instrument;

use super::*;
use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    ff::PrimeField,
    plonk::{
        PlonkStructure, PlonkTrace, PlonkWitness, RelaxedPlonkInstance, RelaxedPlonkTrace,
        RelaxedPlonkWitness,
    },
    polynomial::{lagrange, univariate::UnivariatePoly},
    sps, util,
};

mod accumulator;
pub(crate) mod poly;

pub use accumulator::{Accumulator, AccumulatorArgs};

/// ProtoGalaxy: Non-Interactive Folding Scheme that implements the main protocol defined in the
/// paper [protogalaxy.pdf](https://eprint.iacr.org/2023/1106).
///
/// # Generic Parameters
///
/// - `C`: 'Curve' - represents the elliptic curve used in the protocol.
///                  Circuit will be proved in `C::Scalar` field
///
/// - `L`: 'Length' - constant representing the number of instances to
///                   fold in a single `prove`
#[derive(Clone, Debug)]
pub struct ProtoGalaxy<C: CurveAffine, const L: usize> {
    _marker: PhantomData<C>,
}

impl<C: CurveAffine, const L: usize> ProtoGalaxy<C, L> {
    #[instrument(skip_all)]
    pub(crate) fn generate_challenge<'i>(
        pp_digest: &C,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Accumulator<C>,
        instances: impl Iterator<Item = &'i PlonkInstance<C>>,
    ) -> <C as CurveAffine>::ScalarExt {
        ro_acc
            .absorb_point(pp_digest)
            .absorb(accumulator)
            .absorb_iter(instances)
            .squeeze::<C>(NUM_CHALLENGE_BITS)
    }

    fn get_count_of_valuation(S: &PlonkStructure<C::ScalarExt>) -> usize {
        let count_of_rows = 2usize.pow(S.k as u32);
        let count_of_gates = S.gates.len();

        count_of_rows * count_of_gates
    }

    pub(crate) fn new_accumulator(
        args: AccumulatorArgs,
        params: &ProtoGalaxyProverParam<C>,
        ro_acc: &mut impl ROTrait<C::Base>,
    ) -> Accumulator<C> {
        let mut accumulator = Accumulator::new(args, Self::get_count_of_valuation(&params.S));

        let beta = Self::generate_challenge(&params.pp_digest, ro_acc, &accumulator, iter::empty());

        accumulator
            .betas
            .iter_mut()
            .zip(iter::successors(Some(beta), |acc| Some(acc.double())))
            .for_each(|(b, beta_pow)| *b = beta_pow);

        accumulator
    }

    fn fold_trace(
        acc: RelaxedPlonkTrace<C>,
        incoming: &[PlonkTrace<C>],
        gamma: C::ScalarExt,
        log_n: u32,
    ) -> RelaxedPlonkTrace<C> {
        let mut lagrange = lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, log_n);
        let l_0: C::ScalarExt = lagrange
            .next()
            .expect("safe, because len of lagrange is `2^log_n`");

        let ecc_mul =
            |pt: C, val: C::ScalarExt| -> C { arithmetic::best_multiexp(&[val], &[pt]).into() };

        let new_accumulator = RelaxedPlonkTrace::<C> {
            U: RelaxedPlonkInstance {
                W_commitments: acc
                    .U
                    .W_commitments
                    .into_iter()
                    .map(|w| ecc_mul(w, l_0))
                    .collect(),
                instance: acc.U.instance.into_iter().map(|i| i * l_0).collect(),
                challenges: acc.U.challenges.into_iter().map(|c| c * l_0).collect(),
                u: acc.U.u * l_0,
                // Ignore for protogalaxy
                E_commitment: C::identity(),
            },
            W: RelaxedPlonkWitness {
                W: acc
                    .W
                    .W
                    .into_iter()
                    .map(|r| r.into_iter().map(|w| w * l_0).collect())
                    .collect(),
                E: acc.W.E.iter().map(|e| *e * l_0).collect(),
            },
        };

        incoming
            .iter()
            .zip(lagrange)
            .fold(new_accumulator, |mut acc, (tr, l_n)| {
                let PlonkTrace {
                    u:
                        PlonkInstance {
                            W_commitments,
                            instance,
                            challenges,
                        },
                    w: PlonkWitness { W },
                } = tr;

                acc.U
                    .W_commitments
                    .iter_mut()
                    .zip(W_commitments.iter())
                    .for_each(|(acc_Wc, Wc)| {
                        *acc_Wc = (*acc_Wc + ecc_mul(*Wc, l_n)).into();
                    });

                acc.U
                    .instance
                    .iter_mut()
                    .zip(instance.iter())
                    .for_each(|(acc_inst, inst)| {
                        *acc_inst += *inst * l_n;
                    });

                acc.U
                    .challenges
                    .iter_mut()
                    .zip(challenges.iter())
                    .for_each(|(acc_cha, cha)| {
                        *acc_cha += *cha * l_n;
                    });

                acc.W
                    .W
                    .iter_mut()
                    .zip(W.iter())
                    .for_each(|(acc_W_row, W_row)| {
                        acc_W_row
                            .iter_mut()
                            .zip(W_row.iter())
                            .for_each(|(acc_cell, cell)| {
                                *acc_cell += *cell * l_n;
                            });
                    });

                acc
            })
    }
}

pub struct ProtoGalaxyProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// digest of public parameter of IVC circuit
    pp_digest: C,
}

pub struct ProtoGalaxyProof<F: PrimeField> {
    pub poly_F: UnivariatePoly<F>,
    pub poly_K: UnivariatePoly<F>,
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Sps(#[from] sps::Error),
    #[error(transparent)]
    Poly(#[from] poly::Error),
}

impl<C: CurveAffine, const L: usize> FoldingScheme<C, L> for ProtoGalaxy<C, L> {
    type Error = Error;
    type ProverParam = ProtoGalaxyProverParam<C>;
    type VerifierParam = C;
    type Accumulator = Accumulator<C>;
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
        Ok(pp
            .S
            .run_sps_protocol(ck, instance, witness, ro_nark, pp.S.num_challenges)?)
    }

    fn prove(
        _ck: &CommitmentKey<C>,
        pp: &Self::ProverParam,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: Self::Accumulator,
        incoming: &[PlonkTrace<C>; L],
    ) -> Result<(Self::Accumulator, Self::Proof), Error> {
        let log_n = Self::get_count_of_valuation(&pp.S)
            .next_power_of_two()
            .ilog2();

        let delta = Self::generate_challenge(
            &pp.pp_digest,
            ro_acc,
            &accumulator,
            incoming.iter().map(|t| &t.u),
        );

        let poly_F = poly::compute_F::<C::ScalarExt>(
            accumulator.betas.iter().copied(),
            delta,
            &pp.S,
            &accumulator.trace,
        )?;

        let alpha = ro_acc
            .absorb_field_iter(
                poly_F
                    .iter()
                    .map(|v| util::fe_to_fe::<C::ScalarExt, C::Base>(v).unwrap()),
            )
            .squeeze::<C>(NUM_CHALLENGE_BITS);

        let betas_stroke = poly::PolyChallenges {
            betas: accumulator.betas.clone(),
            delta,
            alpha,
        }
        .iter_beta_stroke()
        .collect::<Box<[_]>>();

        let poly_K = poly::compute_K::<C::ScalarExt>(
            &pp.S,
            alpha,
            betas_stroke.iter().copied(),
            &accumulator.trace,
            incoming,
        )?;

        let gamma = ro_acc
            .absorb_field_iter(poly_K.iter().map(|v| util::fe_to_fe(v).unwrap()))
            .squeeze::<C>(NUM_CHALLENGE_BITS);

        let poly_F_alpha = poly_F.eval(alpha);
        let lagrange_zero_for_gamma =
            lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, log_n)
                .next()
                .unwrap();
        let poly_Z_for_gamma = lagrange::eval_vanish_polynomial(log_n, gamma);
        let poly_K_gamma = poly_K.eval(gamma);

        Ok((
            Accumulator {
                betas: betas_stroke,
                e: (poly_F_alpha * lagrange_zero_for_gamma) + (poly_Z_for_gamma * poly_K_gamma),
                trace: Self::fold_trace(accumulator.trace, incoming, gamma, log_n),
            },
            ProtoGalaxyProof { poly_F, poly_K },
        ))
    }

    fn verify(
        _vp: &Self::VerifierParam,
        _ro_nark: &mut impl ROTrait<C::Base>,
        _ro_acc: &mut impl ROTrait<C::Base>,
        _accumulator: &Self::AccumulatorInstance,
        _incoming: &[PlonkInstance<C>; L],
        _proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Error> {
        todo!()
    }
}

#[cfg(test)]
mod tests;
