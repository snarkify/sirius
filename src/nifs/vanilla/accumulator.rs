use std::{iter, ops};

use halo2_proofs::arithmetic::{best_multiexp, CurveAffine};
use itertools::Itertools;
use rayon::prelude::*;
use tracing::{debug, instrument, warn};

use super::GetConsistencyMarkers;
use crate::{
    commitment::CommitmentKey,
    ff::{Field, PrimeField},
    plonk::{
        self, GetChallenges, GetWitness, PlonkInstance, PlonkStructure, PlonkTrace, PlonkWitness,
    },
    poseidon::{AbsorbInRO, ROTrait},
    util,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelaxedPlonkInstance<C: CurveAffine> {
    /// `W_commitments = round_sizes.len()`, see [`PlonkStructure::round_sizes`]
    pub(crate) W_commitments: Vec<C>,
    pub(crate) consistency_markers: [C::ScalarExt; 2],
    /// challenges generated in special soundness protocol
    /// we will have 0 ~ 3 challenges depending on different cases:
    /// name them as r1, r2, r3.
    /// r1: compress vector lookup, e.g. (a_1, a_2, a_3) -> a_1 + r1*a_2 + r1^2*a_3
    /// r2: challenge to calculate h and g in log-derivative relation
    /// r3: combine all custom gates (P_i) and lookup relations (L_i), e.g.:
    /// (P_1, P_2, L_1, L_2) -> P_1 + r3*P_2 + r3^2*L_1 + r3^3*L_2
    pub(crate) challenges: Vec<C::ScalarExt>,
    pub(crate) E_commitment: C,
    /// homogenous variable u
    pub(crate) u: C::ScalarExt,
}

impl<C: CurveAffine> TryFrom<PlonkInstance<C>> for RelaxedPlonkInstance<C> {
    type Error = PlonkInstance<C>;

    fn try_from(inner: PlonkInstance<C>) -> Result<Self, Self::Error> {
        let Some(consistency_markers) = inner.get_consistency_markers() else {
            return Err(inner);
        };

        Ok(RelaxedPlonkInstance {
            E_commitment: C::identity(),
            u: C::ScalarExt::ONE,
            W_commitments: inner.W_commitments,
            consistency_markers,
            challenges: inner.challenges,
        })
    }
}

impl<C: CurveAffine> RelaxedPlonkInstance<C> {
    pub fn try_new(num_io: &[usize], num_challenges: usize, num_witness: usize) -> Option<Self> {
        Some(Self {
            consistency_markers: match num_io.first() {
                Some(2) => [C::ScalarExt::ZERO, C::ScalarExt::ZERO],
                Some(_) | None => {
                    return None;
                }
            },
            W_commitments: vec![CommitmentKey::<C>::default_value(); num_witness],
            challenges: vec![C::ScalarExt::ZERO; num_challenges],
            E_commitment: CommitmentKey::<C>::default_value(),
            u: Self::DEFAULT_u,
        })
    }

    // In order not to confuse `U` & `u`, which means different things in Sirius, non upper
    // case is allowed here.
    #[allow(non_upper_case_globals)]
    pub const DEFAULT_u: C::ScalarExt = C::ScalarExt::ONE;

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
    #[instrument(name = "fold_plonk_instance", skip_all)]
    pub fn fold(&self, U2: &PlonkInstance<C>, cross_term_commits: &[C], r: &C::ScalarExt) -> Self {
        let W_commitments = self
            .W_commitments
            .iter()
            .zip(U2.W_commitments.clone())
            .enumerate()
            .map(|(W_index, (W1, W2))| {
                let rW = best_multiexp(&[*r], &[W2]).into();
                let res = *W1 + rW;
                debug!(
                    "W1 = {W1:?}; W2 = {W2:?}; rW2[{W_index}] = {rW:?}; rW1 + rW2 * r = {res:?}"
                );
                res.into()
            })
            .collect::<Vec<C>>();

        assert_eq!(U2.instances.len(), 1, "TODO #316");
        assert_eq!(U2.instances[0].len(), 2, "TODO #316");
        let consistency_markers = self
            .consistency_markers
            .iter()
            .zip_eq(&U2.get_consistency_markers().expect("TODO #316"))
            .map(|(a, b)| *a + *r * b)
            .collect::<Vec<C::ScalarExt>>()
            .try_into()
            .unwrap();

        let challenges = self
            .challenges
            .iter()
            .zip_eq(U2.challenges.iter())
            .map(|(a, b)| *a + *r * b)
            .collect::<Vec<C::ScalarExt>>();

        let u = self.u + *r;

        let comm_E = cross_term_commits
            .iter()
            .zip(iter::successors(Some(*r), |el| Some(*el * *r))) // r^1, r^2, ...
            .map(|(tk, power_of_r)| best_multiexp(&[power_of_r], &[*tk]).into())
            .fold(self.E_commitment, |acc, x| (acc + x).into());

        RelaxedPlonkInstance {
            W_commitments,
            challenges,
            u,
            consistency_markers,
            E_commitment: comm_E,
        }
    }

    pub fn instances(&self) -> Vec<Vec<C::ScalarExt>> {
        vec![self.consistency_markers.to_vec()]
    }
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkWitness<F: PrimeField> {
    /// each vector element in W is a vector folded from an old [`RelaxedPlonkWitness.W`] and [`PlonkWitness.W`]
    pub(crate) inner: PlonkWitness<F>,
    pub(crate) E: Box<[F]>,
}

impl<F: PrimeField> ops::Deref for RelaxedPlonkWitness<F> {
    type Target = PlonkWitness<F>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<F: PrimeField> RelaxedPlonkWitness<F> {
    fn from_regular(inner: PlonkWitness<F>, k_table_size: usize) -> Self {
        Self {
            inner,
            E: vec![F::ZERO; 1 << k_table_size].into_boxed_slice(),
        }
    }
}

// TODO #31 docs
#[derive(Debug, Clone)]
pub struct RelaxedPlonkTrace<C: CurveAffine> {
    pub U: RelaxedPlonkInstance<C>,
    pub W: RelaxedPlonkWitness<C::Scalar>,
}

impl<C: CurveAffine> RelaxedPlonkTrace<C> {
    pub fn from_regular(tr: PlonkTrace<C>, k_table_size: usize) -> RelaxedPlonkTrace<C> {
        RelaxedPlonkTrace {
            U: RelaxedPlonkInstance::try_from(tr.u).expect("TODO #316"),
            W: RelaxedPlonkWitness::from_regular(tr.w, k_table_size),
        }
    }
}

pub type RelaxedPlonkTraceArgs = plonk::PlonkTraceArgs;

impl<C: CurveAffine> RelaxedPlonkTrace<C> {
    pub fn new(args: RelaxedPlonkTraceArgs) -> Self {
        Self {
            U: RelaxedPlonkInstance::try_new(&args.num_io, args.num_challenges, args.num_witness)
                .expect("TODO #316"),
            W: RelaxedPlonkWitness::new(args.k_table_size, &args.round_sizes),
        }
    }
}

impl<C: CurveAffine> From<&PlonkStructure<C::ScalarExt>> for RelaxedPlonkTrace<C> {
    fn from(value: &PlonkStructure<C::ScalarExt>) -> Self {
        Self::new(RelaxedPlonkTraceArgs::from(value))
    }
}

impl<F: PrimeField> GetWitness<F> for RelaxedPlonkWitness<F> {
    fn get_witness(&self) -> &[Vec<F>] {
        &self.W
    }
}

impl<C: CurveAffine> GetWitness<C::ScalarExt> for RelaxedPlonkTrace<C> {
    fn get_witness(&self) -> &[Vec<C::ScalarExt>] {
        self.W.get_witness()
    }
}

impl<C: CurveAffine> GetChallenges<C::ScalarExt> for RelaxedPlonkInstance<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        &self.challenges
    }
}

impl<C: CurveAffine> GetChallenges<C::ScalarExt> for RelaxedPlonkTrace<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        self.U.get_challenges()
    }
}

impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            W_commitments,
            consistency_markers,
            challenges,
            E_commitment,
            u,
        } = self;
        ro.absorb_point_iter(W_commitments.iter())
            .absorb_point(E_commitment)
            .absorb_field_iter(
                consistency_markers
                    .iter()
                    .chain(challenges.iter())
                    .chain(iter::once(u))
                    .map(|m| util::fe_to_fe(m).unwrap()),
            );
    }
}

impl<F: PrimeField> RelaxedPlonkWitness<F> {
    /// round_sizes: specify the size of witness vector for each round
    /// in special soundness protocol.
    /// In current version, we have either one round (without lookup)
    /// or two rounds (with lookup)
    pub fn new(k_table_size: usize, round_sizes: &[usize]) -> Self {
        Self {
            inner: PlonkWitness {
                W: round_sizes.iter().map(|sz| vec![F::ZERO; *sz]).collect(),
            },
            E: iter::repeat(F::ZERO).take(1 << k_table_size).collect(),
        }
    }

    #[instrument(name = "fold_witness", skip_all)]
    pub fn fold(&self, W2: &PlonkWitness<F>, cross_terms: &[Box<[F]>], r: &F) -> Self {
        debug!("start W: {} len", self.W.len());
        let W = self
            .W
            .iter()
            .zip_eq(W2.W.iter())
            .map(|(vec1, vec2)| {
                vec1.par_iter()
                    .zip_eq(vec2.par_iter())
                    .map(|(w1, w2)| *w1 + *r * *w2)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        debug!(
            "start E {} len & cross term {} len",
            self.E.len(),
            cross_terms.len()
        );

        // r^1, r^2, ...
        let powers_or_r = iter::successors(Some(*r), |el| Some(*el * r))
            .take(cross_terms.len())
            .collect::<Box<[_]>>();
        let E = self
            .E
            .par_iter()
            .enumerate()
            .map(|(i, ei)| {
                cross_terms
                    .iter()
                    .zip_eq(powers_or_r.iter().copied())
                    .fold(*ei, |acc, (tk, power_of_r)| acc + power_of_r * tk[i])
            })
            .collect();

        RelaxedPlonkWitness {
            inner: PlonkWitness { W },
            E,
        }
    }
}
