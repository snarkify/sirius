use std::{
    array, iter,
    ops::{self, Deref, DerefMut},
};

use halo2_proofs::{
    arithmetic::{best_multiexp, CurveAffine},
    halo2curves::ff::{FromUniformBytes, PrimeFieldBits},
};
use itertools::Itertools;
use rayon::prelude::*;
use tracing::{debug, instrument, warn};

use super::{GetConsistencyMarkers, GetStepCircuitInstances, CONSISTENCY_MARKERS_COUNT};
use crate::{
    commitment::CommitmentKey,
    ff::{Field, PrimeField},
    ivc::sangria::instances_accumulator_computation,
    main_gate::{AssignedValue, WrapValue},
    plonk::{self, GetChallenges, GetWitness, PlonkInstance, PlonkTrace, PlonkWitness},
    poseidon::{AbsorbInRO, ROTrait},
    util::ScalarToBase,
};

/// Accumulator for step-circuit instance columns
///
/// Since the first column is folded directly via `r` and the rest (step-circuit instances columns)
/// are accumulated via hash, in case of absence of any columns except the first one, we don't need
/// additional costs for accumulation of other instance columns.
///
/// This will make it easier to use sangria IVC code in other IVCs, instead of calculating a chain
/// of hashes from empty sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SCInstancesHashAcc<F> {
    /// If StepCircuit does not possess sc_instances will be None
    None,
    Hash(F),
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for SCInstancesHashAcc<F> {
    fn absorb_into(&self, ro: &mut RO) {
        match self {
            Self::None => {
                ro.absorb_field(F::ZERO);
            }
            Self::Hash(hash) => {
                ro.absorb_field(*hash);
            }
        }
    }
}

impl<'l, F: PrimeField> From<&'l SCInstancesHashAcc<AssignedValue<F>>> for WrapValue<F> {
    fn from(val: &'l SCInstancesHashAcc<AssignedValue<F>>) -> Self {
        match &val {
            SCInstancesHashAcc::None => WrapValue::Zero,
            SCInstancesHashAcc::Hash(hash) => WrapValue::Assigned(hash.clone()),
        }
    }
}

impl<F> SCInstancesHashAcc<F> {
    pub fn as_ref(&self) -> SCInstancesHashAcc<&F> {
        match self {
            SCInstancesHashAcc::None => SCInstancesHashAcc::None,
            SCInstancesHashAcc::Hash(h) => SCInstancesHashAcc::Hash(h),
        }
    }

    pub fn zip<'l>(lhs: &'l Self, rhs: &'l Self) -> SCInstancesHashAcc<(&'l F, &'l F)> {
        match (lhs, rhs) {
            (Self::Hash(l), Self::Hash(r)) => SCInstancesHashAcc::Hash((l, r)),
            _ => SCInstancesHashAcc::None,
        }
    }
    pub fn map<O>(self, f: impl FnOnce(F) -> O) -> SCInstancesHashAcc<O> {
        match self {
            SCInstancesHashAcc::None => SCInstancesHashAcc::None,
            SCInstancesHashAcc::Hash(h) => SCInstancesHashAcc::Hash(f(h)),
        }
    }
}

/// Accumulated version of Plonk Instance
///
/// `MARKERS_LEN` - the first column of instance is folded separately, the length of this column is
/// regulated by this parameter
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelaxedPlonkInstance<
    C: CurveAffine,
    const MARKERS_LEN: usize = CONSISTENCY_MARKERS_COUNT,
> {
    /// `W_commitments = round_sizes.len()`, see [`PlonkStructure::round_sizes`]
    pub(crate) W_commitments: Vec<C>,
    /// First instance column [`crate::ivc::step_folding_circuit::StepFoldingCircuit`] reserved for
    /// markers
    ///
    /// These are the two values that allow for proof of acceptance
    /// The null is a hash of all input parameters per folding step
    /// The first one is a hash of all output parameters for each folding step
    pub(crate) consistency_markers: [C::ScalarExt; MARKERS_LEN],
    /// Challenges generated in special soundness protocol (sps)
    /// we will have 0 ~ 3 challenges depending on different cases:
    /// name them as r1, r2, r3:
    ///
    /// - r1: compress vector lookup, e.g. (a_1, a_2, a_3) -> a_1 + r1*a_2 + r1^2*a_3
    /// - r2: challenge to calculate h and g in log-derivative relation
    /// - r3: combine all custom gates (P_i) and lookup relations (L_i), e.g.:
    ///
    /// (P_1, P_2, L_1, L_2) -> P_1 + r3*P_2 + r3^2*L_1 + r3^3*L_2
    pub(crate) challenges: Vec<C::ScalarExt>,
    pub(crate) E_commitment: C,
    /// homogenous variable u
    pub(crate) u: C::ScalarExt,
    /// This is a hash-based accumulator for step circuit instance columns
    ///
    /// Unlike consistency markers, instance columns belonging to the step circuit itself are not
    /// folded, but are accumulated using the hash function.
    pub(crate) step_circuit_instances_hash_accumulator: SCInstancesHashAcc<C::ScalarExt>,
}

impl<C: CurveAffine, const MARKERS_LEN: usize> From<FoldablePlonkInstance<C, MARKERS_LEN>>
    for RelaxedPlonkInstance<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    fn from(inner: FoldablePlonkInstance<C, MARKERS_LEN>) -> Self {
        let step_circuit_instances = inner.get_step_circuit_instances();
        let step_circuit_instances_hash_accumulator = if step_circuit_instances.is_empty() {
            SCInstancesHashAcc::None
        } else {
            SCInstancesHashAcc::Hash(
                instances_accumulator_computation::absorb_in_sc_instances_accumulator::<C>(
                    &C::ScalarExt::ZERO,
                    step_circuit_instances,
                ),
            )
        };

        let consistency_markers = inner.get_consistency_markers();
        let FoldablePlonkInstance(PlonkInstance {
            W_commitments,
            challenges,
            instances: _,
        }) = inner;

        RelaxedPlonkInstance {
            consistency_markers,
            E_commitment: C::identity(),
            u: C::ScalarExt::ONE,
            step_circuit_instances_hash_accumulator,
            W_commitments,
            challenges,
        }
    }
}

impl<C: CurveAffine, const MARKERS_LEN: usize> RelaxedPlonkInstance<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new(num_challenges: usize, num_witness: usize, num_sc_instances: usize) -> Self {
        let step_circuit_instances_hash_accumulator = match num_sc_instances {
            0 => SCInstancesHashAcc::None,
            _any => SCInstancesHashAcc::Hash(
                instances_accumulator_computation::get_initial_sc_instances_accumulator::<C>(),
            ),
        };

        Self {
            consistency_markers: array::from_fn(|_| C::ScalarExt::ZERO),
            W_commitments: vec![CommitmentKey::<C>::default_value(); num_witness],
            challenges: vec![C::ScalarExt::ZERO; num_challenges],
            E_commitment: CommitmentKey::<C>::default_value(),
            u: Self::DEFAULT_u,
            step_circuit_instances_hash_accumulator,
        }
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
    pub fn fold(
        &self,
        U2: &FoldablePlonkInstance<C, MARKERS_LEN>,
        cross_term_commits: &[C],
        r: &C::ScalarExt,
    ) -> Self {
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

        let consistency_markers = self
            .consistency_markers
            .iter()
            .zip_eq(GetConsistencyMarkers::<MARKERS_LEN, _>::get_consistency_markers(U2))
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

        let step_circuit_instances_hash_accumulator = self
            .step_circuit_instances_hash_accumulator
            .as_ref()
            .map(|acc| {
                instances_accumulator_computation::absorb_in_sc_instances_accumulator::<C>(
                    acc,
                    U2.get_step_circuit_instances(),
                )
            });

        RelaxedPlonkInstance {
            W_commitments,
            challenges,
            u,
            consistency_markers,
            E_commitment: comm_E,
            step_circuit_instances_hash_accumulator,
        }
    }

    pub fn instances(&self) -> Vec<Vec<C::ScalarExt>> {
        vec![self.consistency_markers.to_vec()]
    }
}

// TODO #31 docs
#[derive(Debug, Clone)]
pub struct RelaxedPlonkTrace<C: CurveAffine, const MARKERS_LEN: usize = CONSISTENCY_MARKERS_COUNT> {
    pub U: RelaxedPlonkInstance<C, MARKERS_LEN>,
    pub W: RelaxedPlonkWitness<C::Scalar>,
}

impl<C: CurveAffine, const MARKERS_LEN: usize> RelaxedPlonkTrace<C, MARKERS_LEN> {
    pub fn from_regular(
        tr: FoldablePlonkTrace<C, { MARKERS_LEN }>,
        k_table_size: usize,
    ) -> RelaxedPlonkTrace<C, MARKERS_LEN>
    where
        C::Base: PrimeFieldBits + FromUniformBytes<64>,
    {
        RelaxedPlonkTrace {
            U: RelaxedPlonkInstance::from(tr.u),
            W: RelaxedPlonkWitness::from_regular(tr.w, k_table_size),
        }
    }
}

pub type RelaxedPlonkTraceArgs = plonk::PlonkTraceArgs;

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

impl<C: CurveAffine, RO: ROTrait<C::Base>, const MARKERS_LEN: usize> AbsorbInRO<C::Base, RO>
    for RelaxedPlonkInstance<C, MARKERS_LEN>
{
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            W_commitments,
            consistency_markers,
            challenges,
            E_commitment,
            u,
            step_circuit_instances_hash_accumulator,
        } = self;

        ro.absorb_point_iter(W_commitments.iter())
            .absorb_field_iter(
                consistency_markers
                    .iter()
                    .chain(challenges.iter())
                    .chain(iter::once(u))
                    .map(|m| C::scalar_to_base(m).unwrap()),
            )
            .absorb_point(E_commitment)
            .absorb(
                &step_circuit_instances_hash_accumulator
                    .as_ref()
                    .map(|acc| C::scalar_to_base(acc).unwrap()),
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

/// A newtype wrapper around `PlonkInstance` ensuring that the first instance
/// column has exactly two elements.
///
/// # Consistency Markers
/// - Ensures that `instances.first().len() == MARKERS_LEN` for `PlonkInstance`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldablePlonkInstance<
    C: CurveAffine,
    const MARKERS_LEN: usize = CONSISTENCY_MARKERS_COUNT,
>(PlonkInstance<C>);

impl<C: CurveAffine, const MARKERS_LEN: usize> FoldablePlonkInstance<C, MARKERS_LEN> {
    /// Creates a new `FoldablePlonkInstance` from a `PlonkInstance`.
    ///
    /// # Consistency Markers
    /// - Ensures that `instances.first().len() == MARKERS_LEN` for `FoldablePlonkInstance`.
    pub fn new(pl: PlonkInstance<C>) -> Option<Self> {
        matches!(pl.instances.first(), Some(instance) if instance.len() == MARKERS_LEN)
            .then_some(Self(pl))
    }
}

impl<C: CurveAffine, const MARKERS_LEN: usize> Deref for FoldablePlonkInstance<C, MARKERS_LEN> {
    type Target = PlonkInstance<C>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<C: CurveAffine, const MARKERS_LEN: usize> DerefMut for FoldablePlonkInstance<C, MARKERS_LEN> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// A structure representing a foldable PLONK trace containing an instance
/// and witness.
///
/// # Consistency Markers
/// - Contains a `FoldablePlonkInstance` and a `PlonkWitness`.
#[derive(Debug, Clone)]
pub struct FoldablePlonkTrace<C: CurveAffine, const MARKERS_LEN: usize = CONSISTENCY_MARKERS_COUNT>
{
    /// The foldable PLONK instance, ensuring the first instance column has exactly two elements.
    ///
    /// # Consistency Markers
    /// - Holds a `FoldablePlonkInstance` to enforce first-instance column length.
    pub u: FoldablePlonkInstance<C, MARKERS_LEN>,
    pub w: PlonkWitness<C::Scalar>,
}

impl<C: CurveAffine, const MARKERS_LEN: usize> From<FoldablePlonkTrace<C, MARKERS_LEN>>
    for PlonkTrace<C>
{
    /// Converts a `FoldablePlonkTrace` into a `PlonkTrace`.
    fn from(value: FoldablePlonkTrace<C, MARKERS_LEN>) -> Self {
        PlonkTrace {
            u: value.u.0,
            w: value.w,
        }
    }
}

impl<C: CurveAffine, const MARKERS_LEN: usize> FoldablePlonkTrace<C, MARKERS_LEN> {
    /// Creates a new `FoldablePlonkTrace` from a `PlonkTrace`.
    ///
    /// # Consistency Markers
    /// - Ensures the input `PlonkTrace` satisfies the requirements for a `FoldablePlonkTrace`.
    pub fn new(pl: PlonkTrace<C>) -> Option<Self> {
        Some(Self {
            u: FoldablePlonkInstance::new(pl.u)?,
            w: pl.w,
        })
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
