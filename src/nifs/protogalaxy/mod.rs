use std::{iter, marker::PhantomData};

use halo2_proofs::arithmetic::{self, CurveAffine, Field};
use itertools::Itertools;
use tracing::instrument;

use self::accumulator::AccumulatorInstance;
use super::*;
use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    ff::PrimeField,
    plonk::{PlonkStructure, PlonkTrace, PlonkWitness},
    polynomial::{lagrange, univariate::UnivariatePoly},
    poseidon::AbsorbInRO,
    sps::{self, SpecialSoundnessVerifier},
    util,
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
    pub(crate) fn generate_challenge<'i, RO: ROTrait<C::Base>>(
        pp_digest: &C,
        ro_acc: &mut RO,
        accumulator: &impl AbsorbInRO<C::Base, RO>,
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
        params: &ProverParam<C>,
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

    fn fold_witness<'i>(
        acc: PlonkWitness<C::Scalar>,
        incoming: impl Iterator<Item = &'i PlonkWitness<C::Scalar>>,
        mut lagrange_for_gamma: impl Iterator<Item = C::Scalar>,
    ) -> PlonkWitness<C::Scalar> {
        let l_0: C::ScalarExt = lagrange_for_gamma
            .next()
            .expect("safe, because len of lagrange is `2^log_n`");

        let new_accumulator = PlonkWitness {
            W: acc
                .W
                .into_iter()
                .map(|r| r.into_iter().map(|w| w * l_0).collect())
                .collect(),
        };

        incoming
            .zip(lagrange_for_gamma)
            .fold(new_accumulator, |mut acc, (w, l_n)| {
                acc.W
                    .iter_mut()
                    .zip_eq(w.W.iter())
                    .for_each(|(acc_W_row, W_row)| {
                        acc_W_row
                            .iter_mut()
                            .zip_eq(W_row.iter())
                            .for_each(|(acc_cell, cell)| {
                                *acc_cell += *cell * l_n;
                            });
                    });

                acc
            })
    }

    fn fold_instance<'i>(
        acc: PlonkInstance<C>,
        incoming: impl Iterator<Item = &'i PlonkInstance<C>>,
        mut lagrange_for_gamma: impl Iterator<Item = C::Scalar>,
    ) -> PlonkInstance<C> {
        let l_0: C::ScalarExt = lagrange_for_gamma
            .next()
            .expect("safe, because len of lagrange is `2^log_n`");

        let ecc_mul =
            |pt: C, val: C::ScalarExt| -> C { arithmetic::best_multiexp(&[val], &[pt]).into() };

        let new_accumulator = PlonkInstance {
            W_commitments: acc
                .W_commitments
                .into_iter()
                .map(|w| ecc_mul(w, l_0))
                .collect(),
            instance: acc.instance.into_iter().map(|i| i * l_0).collect(),
            challenges: acc.challenges.into_iter().map(|c| c * l_0).collect(),
        };

        incoming
            .zip(lagrange_for_gamma)
            .fold(new_accumulator, |mut acc, (u, l_n)| {
                let PlonkInstance {
                    W_commitments,
                    instance,
                    challenges,
                } = u;

                acc.W_commitments
                    .iter_mut()
                    .zip_eq(W_commitments.iter())
                    .for_each(|(acc_Wc, Wc)| {
                        *acc_Wc = (*acc_Wc + ecc_mul(*Wc, l_n)).into();
                    });

                acc.instance
                    .iter_mut()
                    .zip_eq(instance.iter())
                    .for_each(|(acc_inst, inst)| {
                        *acc_inst += *inst * l_n;
                    });

                acc.challenges
                    .iter_mut()
                    .zip_eq(challenges.iter())
                    .for_each(|(acc_cha, cha)| {
                        *acc_cha += *cha * l_n;
                    });

                acc
            })
    }

    pub fn verify_sps<'l>(
        incoming: impl Iterator<Item = &'l PlonkInstance<C>>,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<(), Error> {
        let errors = incoming
            .enumerate()
            .filter_map(|(i, plonk_instance)| Some((i, plonk_instance.sps_verify(ro_nark).err()?)))
            .collect::<Box<[_]>>();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(Error::VerifySps(errors))
        }
    }
}

pub struct ProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// Digest of public parameter of IVC circuit
    pp_digest: C,
}

pub struct VerifierParam<C: CurveAffine> {
    /// This field, `log_n`, represents the base-2 logarithm of the next power of two
    /// that is greater than or equal to the product of the number of rows and the number of gates.
    ///
    /// In formula terms, it is calculated using:
    /// (Count_of_rows * Count_of_gates).next_power_of_two().ilog2()
    log_n: u32,
    /// Digest of public parameter of IVC circuit
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
    #[error("Error while verify plonk instance with sps: {0:?}")]
    VerifySps(Box<[(usize, sps::Error)]>),
}

impl<C: CurveAffine, const L: usize> FoldingScheme<C, L> for ProtoGalaxy<C, L> {
    type Error = Error;
    type ProverParam = ProverParam<C>;
    type VerifierParam = VerifierParam<C>;
    type Accumulator = Accumulator<C>;
    type AccumulatorInstance = AccumulatorInstance<C>;
    type Proof = ProtoGalaxyProof<C::ScalarExt>;

    fn setup_params(
        pp_digest: C,
        S: PlonkStructure<C::ScalarExt>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let log_n = Self::get_count_of_valuation(&S).next_power_of_two().ilog2();

        Ok((
            ProverParam { S, pp_digest },
            VerifierParam { pp_digest, log_n },
        ))
    }

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

    /// Proves a statement using the ProtoGalaxy protocol.
    ///
    /// # Algorithm
    ///
    /// The logic of the proof generation follows several key steps:
    ///
    /// 1. **Generate Delta:**
    ///     - **RO Seeds**: includes all input parameters except `ck` & witness from `incoming`
    ///     - `delta = ro_acc.squeeze()`
    ///
    /// 2. **Compute Polynomial F:**
    ///     - `F = [`poly::compute_F`]`
    ///
    /// 3. **Generate Alpha:**
    ///     - **RO Update**: absorb `poly_F`
    ///     - `alpha = ro_acc.squeeze()`
    ///
    /// 4. **Update Beta* Values:**
    ///     - `beta*[i] = beta[i] + alpha * delta[i]`
    ///
    /// 5. **Compute Polynomial K:**
    ///     - `G = [`poly::compute_G`]
    ///     - `K = [`poly::compute_K`]
    ///
    /// 6. **Generate Gamma:**
    ///     - **RO Update**: Absorb `poly_K`
    ///     - `gamma = ro_acc.squeeze()`
    ///
    /// 7. **Fold the Trace:**
    ///     - [`ProtoGalaxy::fold_witness`] & [`ProtoGalaxy::fold_instance`]
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

        let lagrange_for_gamma = lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, log_n)
            .take(L + 1)
            .collect::<Box<[_]>>();

        Ok((
            Accumulator {
                e: calculate_e::<C>(&poly_F, &poly_K, gamma, alpha, log_n),
                betas: betas_stroke,
                trace: PlonkTrace {
                    u: Self::fold_instance(
                        accumulator.trace.u,
                        incoming.iter().map(|tr| &tr.u),
                        lagrange_for_gamma.iter().copied(),
                    ),
                    w: Self::fold_witness(
                        accumulator.trace.w,
                        incoming.iter().map(|tr| &tr.w),
                        lagrange_for_gamma.iter().copied(),
                    ),
                },
            },
            ProtoGalaxyProof { poly_F, poly_K },
        ))
    }

    /// Verifies a statement using the ProtoGalaxy protocol.
    ///
    /// # Algorithm
    ///
    /// The logic of the proof generation follows several key steps:
    ///
    /// 1. **Verify SPS**
    ///     - Verify SPS correctness in `incoming` plonk instances
    ///
    /// 2. **Generate Delta:**
    ///     - **RO Seeds**: includes all input parameters except `ck`
    ///     - `delta = ro_acc.squeeze()`
    ///
    /// 3. **Generate Alpha:**
    ///     - **RO Update**: absorb `proof.poly_F`
    ///     - `alpha = ro_acc.squeeze()`
    ///
    /// 4. **Update Beta* Values:**
    ///     - `beta*[i] = beta[i] + alpha * delta[i]`
    ///
    /// 5. **Generate Gamma:**
    ///     - **RO Update**: Absorb `proof.poly_K`
    ///     - `gamma = ro_acc.squeeze()`
    ///
    /// 6. **Fold the Instance:**
    ///     - [`ProtoGalaxy::fold_instance`]
    fn verify(
        vp: &Self::VerifierParam,
        ro_nark: &mut impl ROTrait<C::Base>,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Self::AccumulatorInstance,
        incoming: &[PlonkInstance<C>; L],
        proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Error> {
        Self::verify_sps(incoming.iter(), ro_nark)?;

        let delta = Self::generate_challenge(&vp.pp_digest, ro_acc, accumulator, incoming.iter());
        let alpha = ro_acc
            .absorb_field_iter(
                proof
                    .poly_F
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

        let gamma = ro_acc
            .absorb_field_iter(proof.poly_K.iter().map(|v| util::fe_to_fe(v).unwrap()))
            .squeeze::<C>(NUM_CHALLENGE_BITS);

        Ok(AccumulatorInstance {
            betas: betas_stroke,
            ins: Self::fold_instance(
                accumulator.ins.clone(),
                incoming.iter(),
                lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, vp.log_n),
            ),
            e: calculate_e::<C>(&proof.poly_F, &proof.poly_K, gamma, alpha, vp.log_n),
        })
    }
}

// F(alpha) * L(gamma) + Z(gamma) * K(gamma)
fn calculate_e<C: CurveAffine>(
    poly_F: &UnivariatePoly<C::Scalar>,
    poly_K: &UnivariatePoly<C::Scalar>,
    gamma: C::Scalar,
    alpha: C::Scalar,
    log_n: u32,
) -> C::Scalar {
    let lagrange_zero_for_gamma = lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, log_n)
        .next()
        .unwrap();

    let poly_F_alpha = poly_F.eval(alpha);
    let poly_Z_gamma = lagrange::eval_vanish_polynomial(log_n, gamma);
    let poly_K_gamma = poly_K.eval(gamma);

    (poly_F_alpha * lagrange_zero_for_gamma) + (poly_Z_gamma * poly_K_gamma)
}

#[cfg(test)]
mod tests;
