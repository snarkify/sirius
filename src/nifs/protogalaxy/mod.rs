use std::{
    iter,
    marker::PhantomData,
    ops::{Not, Sub},
};

use itertools::Itertools;
use tracing::{instrument, warn};

use self::accumulator::AccumulatorInstance;
use super::*;
use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    ff::PrimeField,
    halo2_proofs::arithmetic::{self, CurveAffine, Field},
    nifs::protogalaxy::poly::PolyContext,
    plonk::{self, PlonkStructure, PlonkTrace, PlonkWitness},
    polynomial::{lagrange, sparse, univariate::UnivariatePoly},
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
            instances: acc
                .instances
                .into_iter()
                .map(|instance| instance.into_iter().map(|val| val * l_0).collect())
                .collect(),
            challenges: acc.challenges.into_iter().map(|c| c * l_0).collect(),
        };

        incoming
            .zip(lagrange_for_gamma)
            .fold(new_accumulator, |mut acc, (u, l_n)| {
                let PlonkInstance {
                    W_commitments,
                    instances: instance,
                    challenges,
                } = u;

                acc.W_commitments
                    .iter_mut()
                    .zip_eq(W_commitments.iter())
                    .for_each(|(acc_Wc, Wc)| {
                        *acc_Wc = (*acc_Wc + ecc_mul(*Wc, l_n)).into();
                    });

                acc.instances
                    .iter_mut()
                    .flatten()
                    .zip_eq(instance.iter().flatten())
                    .for_each(|(acc_instance, instance)| {
                        *acc_instance += *instance * l_n;
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
        Ok((ProverParam { S, pp_digest }, VerifierParam { pp_digest }))
    }

    fn generate_plonk_trace(
        ck: &CommitmentKey<C>,
        instances: &[Vec<C::ScalarExt>],
        witness: &[Vec<C::ScalarExt>],
        pp: &Self::ProverParam,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<PlonkTrace<C>, Error> {
        assert!(instances.len() <= 1, "TODO #316");

        Ok(pp
            .S
            .run_sps_protocol(ck, instances, witness, ro_nark, pp.S.num_challenges)?)
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
        let ctx = PolyContext::new(&pp.S, incoming);

        let delta = Self::generate_challenge(
            &pp.pp_digest,
            ro_acc,
            &accumulator,
            incoming.iter().map(|t| &t.u),
        );

        let poly_F = poly::compute_F::<C::ScalarExt>(
            &ctx,
            accumulator.betas.iter().copied(),
            delta,
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
            &ctx,
            poly_F.eval(alpha),
            betas_stroke.iter().copied(),
            &accumulator.trace,
            incoming,
        )?;

        let gamma = ro_acc
            .absorb_field_iter(poly_K.iter().map(|v| util::fe_to_fe(v).unwrap()))
            .squeeze::<C>(NUM_CHALLENGE_BITS);

        let polys_L_in_gamma =
            lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, ctx.lagrange_domain())
                .take(L + 1)
                .collect::<Box<[_]>>();

        let Accumulator {
            trace: PlonkTrace { u, w },
            betas: _,
            e: _,
        } = accumulator;

        Ok((
            Accumulator {
                e: calculate_e::<C>(&poly_F, &poly_K, gamma, alpha, ctx.lagrange_domain()),
                betas: betas_stroke,
                trace: PlonkTrace {
                    u: Self::fold_instance(
                        u,
                        incoming.iter().map(|tr| &tr.u),
                        polys_L_in_gamma.iter().copied(),
                    ),
                    w: Self::fold_witness(
                        w,
                        incoming.iter().map(|tr| &tr.w),
                        polys_L_in_gamma.iter().copied(),
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
        let lagrange_domain = PolyContext::<C::Base>::get_lagrange_domain::<L>();

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
                lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, lagrange_domain),
            ),
            e: calculate_e::<C>(&proof.poly_F, &proof.poly_K, gamma, alpha, lagrange_domain),
        })
    }
}

#[derive(Debug, thiserror::Error)]
pub enum VerifyError<F: PrimeField> {
    #[error("Error while evaluate witness: {0:?}")]
    PlonkEval(plonk::eval::Error),
    #[error("Expected `e` {expected_e:?}, but evaluated is {evaluated_e:?}")]
    MismatchE { expected_e: F, evaluated_e: F },
    #[error("Permutation check failed")]
    Perm(plonk::Error),
    #[error("Commitment of")]
    WitnessCommitmentMismatch(Box<[usize]>),
}

impl<C: CurveAffine, const L: usize> VerifyAccumulation<C, L> for ProtoGalaxy<C, L> {
    type VerifyError = VerifyError<C::ScalarExt>;

    fn is_sat_accumulation(
        S: &PlonkStructure<C::ScalarExt>,
        acc: &Accumulator<C>,
    ) -> Result<(), Self::VerifyError> {
        struct Node<F: PrimeField> {
            value: F,
            height: usize,
        }

        let evaluated_e = plonk::iter_evaluate_witness::<C::ScalarExt>(S, &acc.trace)
            .map(|result_with_evaluated_gate| {
                result_with_evaluated_gate.map(|value| Node { value, height: 0 })
            })
            // TODO #324 Migrate to a parallel algorithm
            // TODO #324 Implement `try_tree_reduce` to stop on the first error
            .tree_reduce(|left_w, right_w| {
                let (mut left_n, right_n) = (left_w?, right_w?);

                if left_n.height != right_n.height {
                    unreachable!(
                        "must be unreachable, since the number of rows is the degree of 2, but: {l_height} != {r_height}",
                        l_height = left_n.height,
                        r_height = right_n.height
                    )
                }

                left_n.value += right_n.value * acc.betas[right_n.height];
                left_n.height += 1;

                Ok(left_n)
            })
            .transpose()
            .map_err(VerifyError::PlonkEval)?
            .map(|n| n.value)
            .unwrap_or_default();

        if evaluated_e == acc.e {
            Ok(())
        } else {
            Err(VerifyError::MismatchE {
                expected_e: acc.e,
                evaluated_e,
            })
        }
    }

    fn is_sat_permutation(
        S: &PlonkStructure<<C as CurveAffine>::ScalarExt>,
        acc: &Accumulator<C>,
    ) -> Result<(), Self::VerifyError> {
        let PlonkTrace { u, w } = &acc.trace;

        let Z = u
            .instances
            .iter()
            .flat_map(|instance| instance.iter())
            .chain(w.W[0].iter().take((1 << S.k) * S.num_advice_columns))
            .copied()
            .collect::<Box<[_]>>();

        let y = sparse::matrix_multiply(&S.permutation_matrix, &Z[..]);
        let mismatch_count = y
            .into_iter()
            .zip(Z)
            .filter(|(y, z)| y.sub(z).is_zero_vartime().not())
            .count();

        if mismatch_count == 0 {
            Ok(())
        } else {
            Err(Self::VerifyError::Perm(plonk::Error::PermCheckFail {
                mismatch_count,
            }))
        }
    }

    fn is_sat_witness_commit(
        ck: &CommitmentKey<C>,
        acc: &<Self as FoldingScheme<C, L>>::Accumulator,
    ) -> Result<(), Self::VerifyError> {
        let Accumulator {
            trace: PlonkTrace { u, w },
            ..
        } = acc;

        let errors = u
            .W_commitments
            .iter()
            .zip_eq(&w.W)
            .enumerate()
            .filter_map(|(i, (Ci, Wi))| ck.commit(Wi).unwrap().ne(Ci).then_some(i))
            .collect::<Box<[_]>>();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(VerifyError::WitnessCommitmentMismatch(errors))
        }
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
    let poly_L0_in_gamma = lagrange::iter_eval_lagrange_poly_for_cyclic_group(gamma, log_n)
        .next()
        .unwrap();

    let poly_F_alpha = poly_F.eval(alpha);
    let poly_Z_gamma = lagrange::eval_vanish_polynomial(1 << log_n, gamma);
    let poly_K_gamma = poly_K.eval(gamma);

    (poly_F_alpha * poly_L0_in_gamma) + (poly_Z_gamma * poly_K_gamma)
}

#[cfg(test)]
mod tests;
