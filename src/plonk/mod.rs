//! This module defines the Plonk related types for working with
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
use std::{iter, num::NonZeroUsize, time::Instant};

use count_to_non_zero::*;
use ff::{Field, PrimeField};
use halo2_proofs::{
    arithmetic::{best_multiexp, CurveAffine},
    halo2curves::ff,
};
use itertools::Itertools;
use rayon::prelude::*;
use serde::Serialize;
use some_to_err::*;
use tracing::{debug, error, info, info_span, instrument, warn};

use crate::{
    commitment::CommitmentKey,
    concat_vec,
    constants::NUM_CHALLENGE_BITS,
    plonk::{
        self,
        eval::{Error as EvalError, GetDataForEval, PlonkEvalDomain},
    },
    polynomial::{
        expression::{HomogeneousExpression, QueryIndexContext},
        graph_evaluator::GraphEvaluator,
        grouped_poly::GroupedPoly,
        sparse::{matrix_multiply, SparseMatrix},
        Expression,
    },
    poseidon::{AbsorbInRO, ROTrait},
    sps::{Error as SpsError, SpecialSoundnessVerifier},
    util::{concatenate_with_padding, fe_to_fe},
};

pub mod eval;
pub mod lookup;
pub mod permutation;
pub mod util;

#[derive(Debug, thiserror::Error, PartialEq)]
pub enum Error {
    #[error(transparent)]
    Sps(#[from] SpsError),
    #[error(transparent)]
    Eval(#[from] EvalError),
    #[error("(Relaxed) plonk relation not satisfied: commitment mismatch")]
    CommitmentMismatch { mismatch_count: NonZeroUsize },
    #[error("(Relaxed) plonk relation not satisfied: commitment of E")]
    ECommitmentMismatch,
    #[error("log derivative relation not satisfied")]
    LogDerivativeNotSat,
    #[error("Permutation check fail: mismatch_count {mismatch_count}")]
    PermCheckFail { mismatch_count: usize },
    #[error("(Relaxed) plonk relation not satisfied: mismatch_count {mismatch_count}, total_row {total_row}")]
    EvaluationMismatch {
        mismatch_count: NonZeroUsize,
        total_row: usize,
    },
}

/// This structure is a representation of a compressed set of custom gates & lookup
#[derive(Clone, PartialEq, Serialize, Default)]
pub(crate) struct CompressedGates<F: PrimeField> {
    /// The original custom gates & lookup expressions grouped using random linear combination
    compressed: Expression<F>,
    /// A homogeneous version of the `compressed` expression, achieved by adding another challenge
    /// if necessary
    #[serde(skip_serializing)]
    homogeneous: HomogeneousExpression<F>,
    /// A degree-grouped version of the `homogeneous` expression, adds another expression, but
    /// implicitly
    #[serde(skip_serializing)]
    grouped: GroupedPoly<F>,
}

impl<F: PrimeField> CompressedGates<F> {
    #[instrument(name = "compressed_gates", skip_all)]
    pub fn new(original_expressions: &[Expression<F>], ctx: &mut QueryIndexContext) -> Self {
        let timer = Instant::now();
        debug!("input num_challenges: {}", ctx.num_challenges);
        let compressed = plonk::util::compress_expression(original_expressions, ctx.num_challenges);
        info!(
            "custom gates compressed in {} ns",
            timer.elapsed().as_nanos()
        );
        ctx.num_challenges = compressed.num_challenges();

        let homogeneous = compressed.homogeneous(ctx);
        info!(
            "compressed made homogeneous in {} ns",
            timer.elapsed().as_nanos()
        );
        ctx.num_challenges = homogeneous.num_challenges();

        let grouped = GroupedPoly::new(&homogeneous, ctx);
        info!(
            "homogeneous made grouped in {} ns",
            timer.elapsed().as_nanos()
        );

        Self {
            compressed,
            grouped,
            homogeneous,
        }
    }
    pub fn compressed(&self) -> &Expression<F> {
        &self.compressed
    }

    pub fn homogeneous(&self) -> &Expression<F> {
        &self.homogeneous
    }

    pub fn grouped(&self) -> &GroupedPoly<F> {
        &self.grouped
    }
}

#[derive(Clone, PartialEq, Serialize, Default)]
#[serde(bound(serialize = "
    F: Serialize
"))]
pub struct PlonkStructure<F: PrimeField> {
    /// k is a parameter such that 2^k is the total number of rows
    pub(crate) k: usize,
    pub(crate) num_io: usize,
    pub(crate) selectors: Vec<Vec<bool>>,
    pub(crate) fixed_columns: Vec<Vec<F>>,

    pub(crate) num_advice_columns: usize,

    /// We follow the special soundness protocol(SPS), section 3.1 in [Protostar](https://eprint.iacr.org/2023/620)
    /// let k = num_challenges; when k > 0, we add extra verifier round, this is slightly different
    /// from protostar paper.
    /// see [`PlonkInstance::challenges`] for detail
    pub(crate) num_challenges: usize,
    /// specify the witness size of each prover round
    pub(crate) round_sizes: Vec<usize>,

    pub(crate) custom_gates_lookup_compressed: CompressedGates<F>,

    /// TODO #262: after we switch from Sangaria IVC to IVC with cyclefold + protogalaxy
    /// we will remove the field custom_gates_lookup_compressed and make gates field serializable
    /// instead
    /// we use uncompressed gates instead of
    /// custom_gates_lookup_compressed in protogalaxy folding scheme
    #[serde(skip_serializing)]
    pub(crate) gates: Vec<Expression<F>>,

    pub(crate) permutation_matrix: SparseMatrix<F>,
    pub(crate) lookup_arguments: Option<lookup::Arguments<F>>,
}

#[derive(Clone, Debug)]
pub struct PlonkInstance<C: CurveAffine> {
    /// `W_commitments = round_sizes.len()`, see [`PlonkStructure::round_sizes`]
    pub(crate) W_commitments: Vec<C>,
    /// inst = [X0, X1]
    pub(crate) instance: Vec<C::ScalarExt>,
    /// challenges generated in special soundness protocol
    /// we will have 0 ~ 3 challenges depending on different cases:
    /// name them as r1, r2, r3.
    /// r1: compress vector lookup, e.g. (a_1, a_2, a_3) -> a_1 + r1*a_2 + r1^2*a_3
    /// r2: challenge to calculate h and g in log-derivative relation
    /// r3: combine all custom gates (P_i) and lookup relations (L_i), e.g.:
    /// (P_1, P_2, L_1, L_2) -> P_1 + r3*P_2 + r3^2*L_1 + r3^3*L_2
    pub(crate) challenges: Vec<C::ScalarExt>,
}

impl<C: CurveAffine> Default for PlonkInstance<C> {
    fn default() -> Self {
        Self {
            W_commitments: vec![],
            instance: vec![C::ScalarExt::ZERO, C::ScalarExt::ZERO], // TODO Fix Me
            challenges: vec![],
        }
    }
}

#[derive(Clone, Debug)]
pub struct PlonkWitness<F: PrimeField> {
    /// length of W equals number of prover rounds, see [`PlonkStructure`]
    pub(crate) W: Vec<Vec<F>>,
}

impl<F: PrimeField> PlonkWitness<F> {
    pub fn new(round_sizes: &[usize]) -> Self {
        Self {
            W: round_sizes.iter().map(|sz| vec![F::ZERO; *sz]).collect(),
        }
    }

    pub fn to_relax(&self, k_table_size: usize) -> RelaxedPlonkWitness<F> {
        RelaxedPlonkWitness {
            W: self.W.clone(),
            E: vec![F::ZERO; 1 << k_table_size].into_boxed_slice(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelaxedPlonkInstance<C: CurveAffine> {
    pub(crate) W_commitments: Vec<C>,
    pub(crate) E_commitment: C,
    pub(crate) instance: Vec<C::ScalarExt>,
    /// contains challenges
    pub(crate) challenges: Vec<C::ScalarExt>,
    /// homogenous variable u
    pub(crate) u: C::ScalarExt,
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkWitness<F: PrimeField> {
    /// each vector element in W is a vector folded from an old [`RelaxedPlonkWitness.W`] and [`PlonkWitness.W`]
    pub(crate) W: Vec<Vec<F>>,
    pub(crate) E: Box<[F]>,
}

// TODO #31 docs
pub struct RelaxedPlonkTrace<C: CurveAffine> {
    pub U: RelaxedPlonkInstance<C>,
    pub W: RelaxedPlonkWitness<C::Scalar>,
}

// TODO #31 docs
#[derive(Debug, Clone)]
pub struct PlonkTrace<C: CurveAffine> {
    pub u: PlonkInstance<C>,
    pub w: PlonkWitness<C::Scalar>,
}

/// Generalized trait to get witness
///
/// Used to generalize:
/// - [`PlonkWitness`]
/// - [`RelaxedPlonkWitness`]
/// - [`RelaxedPlonkTrace`]
/// - [`PlonkTrace`]
pub(crate) trait GetWitness<F: PrimeField> {
    fn get_witness(&self) -> &[Vec<F>];
}
impl<F: PrimeField> GetWitness<F> for PlonkWitness<F> {
    fn get_witness(&self) -> &[Vec<F>] {
        &self.W
    }
}
impl<F: PrimeField> GetWitness<F> for RelaxedPlonkWitness<F> {
    fn get_witness(&self) -> &[Vec<F>] {
        &self.W
    }
}
impl<C: CurveAffine> GetWitness<C::ScalarExt> for PlonkTrace<C> {
    fn get_witness(&self) -> &[Vec<C::ScalarExt>] {
        self.w.get_witness()
    }
}
impl<C: CurveAffine> GetWitness<C::ScalarExt> for RelaxedPlonkTrace<C> {
    fn get_witness(&self) -> &[Vec<C::ScalarExt>] {
        self.W.get_witness()
    }
}

/// Generalized trait to get challenges
///
/// Used to generalize:
/// - [`PlonkWitness`]
/// - [`RelaxedPlonkWitness`]
/// - [`RelaxedPlonkTrace`]
/// - [`PlonkTrace`]
pub(crate) trait GetChallenges<F: PrimeField> {
    fn get_challenges(&self) -> &[F];
}
impl<C: CurveAffine> GetChallenges<C::ScalarExt> for PlonkInstance<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        &self.challenges
    }
}
impl<C: CurveAffine> GetChallenges<C::ScalarExt> for RelaxedPlonkInstance<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        &self.challenges
    }
}

impl<C: CurveAffine> GetChallenges<C::ScalarExt> for PlonkTrace<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        self.u.get_challenges()
    }
}
impl<C: CurveAffine> GetChallenges<C::ScalarExt> for RelaxedPlonkTrace<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        self.U.get_challenges()
    }
}

impl<C: CurveAffine> PlonkTrace<C> {
    pub fn to_relax(&self, k: usize) -> RelaxedPlonkTrace<C> {
        RelaxedPlonkTrace {
            U: self.u.to_relax(),
            W: self.w.to_relax(k),
        }
    }
}

impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO> for PlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point_iter(self.W_commitments.iter())
            .absorb_field_iter(self.instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_field_iter(self.challenges.iter().map(|cha| fe_to_fe(cha).unwrap()));
    }
}

impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point_iter(self.W_commitments.iter())
            .absorb_point(&self.E_commitment)
            .absorb_field_iter(self.instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_field_iter(self.challenges.iter().map(|cha| fe_to_fe(cha).unwrap()))
            .absorb_field(fe_to_fe(&self.u).unwrap());
    }
}

impl<F: PrimeField> PlonkStructure<F> {
    /// return the index offset of fixed variables(i.e. not folded)
    pub fn num_non_fold_vars(&self) -> usize {
        self.fixed_columns.len() + self.selectors.len()
    }

    /// return the number of variables to be folded
    /// each lookup argument will add 5 variables (l,t,m,h,g)
    pub fn num_fold_vars(&self) -> usize {
        self.num_advice_columns + 5 * self.num_lookups()
    }

    pub fn num_lookups(&self) -> usize {
        if self.lookup_arguments.is_none() {
            0
        } else {
            self.lookup_arguments.as_ref().unwrap().lookup_polys.len()
        }
    }

    /// indicates whether the original constrain system contains vector lookup
    pub fn has_vector_lookup(&self) -> bool {
        self.lookup_arguments
            .as_ref()
            .map(|arg| arg.has_vector_lookup)
            .unwrap_or(false)
    }

    pub fn is_sat<C, RO: ROTrait<C::Base>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
        U: &PlonkInstance<C>,
        W: &PlonkWitness<F>,
    ) -> Result<(), Error>
    where
        C: CurveAffine<ScalarExt = F>,
    {
        U.sps_verify(ro_nark)?;

        let data = PlonkEvalDomain {
            num_advice: self.num_advice_columns,
            num_lookup: self.num_lookups(),
            challenges: &U.challenges,
            selectors: &self.selectors,
            fixed: &self.fixed_columns,
            W1s: &W.W,
            W2s: &[],
        };

        let total_row = 1 << self.k;

        let evaluator = GraphEvaluator::new(self.custom_gates_lookup_compressed.compressed());
        (0..total_row)
            .into_par_iter()
            .map(|row| {
                evaluator
                    .evaluate(&data, row)
                    .map(|row_result| if row_result.eq(&F::ZERO) { 0 } else { 1 })
            })
            .try_reduce(
                || 0,
                |mismatch_count, is_missed| Ok(mismatch_count + is_missed),
            )
            .map(|mismatch_count| {
                Some(Error::EvaluationMismatch {
                    mismatch_count: NonZeroUsize::new(mismatch_count)?,
                    total_row,
                })
            })?
            .err_or(())?;

        if !self.is_sat_log_derivative(&W.W) {
            return Err(Error::LogDerivativeNotSat);
        }

        U.W_commitments
            .iter()
            .zip_eq(W.W.iter())
            .filter_map(|(Ci, Wi)| ck.commit(Wi).unwrap().ne(Ci).then_some(()))
            .count_to_non_zero()
            .map(|mismatch_count| Error::CommitmentMismatch { mismatch_count })
            .err_or(())?;

        Ok(())
    }

    pub fn is_sat_relaxed<C>(
        &self,
        ck: &CommitmentKey<C>,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), Error>
    where
        C: CurveAffine<ScalarExt = F>,
    {
        let total_row = 1 << self.k;

        let data = PlonkEvalDomain {
            num_advice: self.num_advice_columns,
            num_lookup: self.num_lookups(),
            challenges: &concat_vec!(&U.challenges, &[U.u]),
            selectors: &self.selectors,
            fixed: &self.fixed_columns,
            W1s: &W.W,
            W2s: &[],
        };

        let evaluator = GraphEvaluator::new(self.custom_gates_lookup_compressed.homogeneous());
        (0..total_row)
            .into_par_iter()
            .map(|row| {
                evaluator.evaluate(&data, row).map(|eval_of_row| {
                    let expected = W.E[row];

                    if eval_of_row.eq(&expected) {
                        0
                    } else {
                        warn!("row {row} invalid: expected {expected:?}, but {eval_of_row:?}");
                        1
                    }
                })
            })
            .try_reduce(
                || 0,
                |mismatch_count, is_missed| Ok(mismatch_count + is_missed),
            )
            .map(|mismatch_count| {
                Some(Error::EvaluationMismatch {
                    mismatch_count: NonZeroUsize::new(mismatch_count)?,
                    total_row,
                })
            })?
            .err_or(())?;

        if !self.is_sat_log_derivative(&W.W) {
            return Err(Error::LogDerivativeNotSat);
        }

        U.W_commitments
            .iter()
            .zip_eq(W.W.iter())
            .filter_map(|(Ci, Wi)| ck.commit(Wi).unwrap().ne(Ci).then_some(()))
            .count_to_non_zero()
            .map(|mismatch_count| Error::CommitmentMismatch { mismatch_count })
            .err_or(())?;

        if ck.commit(&W.E).unwrap().ne(&U.E_commitment) {
            return Err(Error::ECommitmentMismatch);
        }

        Ok(())
    }

    // permutation check for folding instance-witness pair
    pub fn is_sat_perm<C>(
        &self,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), Error>
    where
        C: CurveAffine<ScalarExt = F>,
    {
        let Z = U
            .instance
            .clone()
            .into_iter()
            .chain(W.W[0][..(1 << self.k) * self.num_advice_columns].to_vec())
            .collect::<Vec<_>>();
        let y = matrix_multiply(&self.permutation_matrix, &Z[..]);
        let mismatch_count = y
            .into_iter()
            .zip(Z)
            .map(|(y, z)| y - z)
            .filter(|d| F::ZERO.ne(d))
            .count();
        if mismatch_count == 0 {
            Ok(())
        } else {
            Err(Error::PermCheckFail { mismatch_count })
        }
    }

    /// check whether the log-derivative equation is satisfied
    pub fn is_sat_log_derivative(&self, W: &[Vec<F>]) -> bool {
        let nrow = 1 << self.k;
        let check_is_zero = |hs: &[Vec<F>], gs: &[Vec<F>]| -> bool {
            hs.iter().zip(gs).all(|(h, g)| {
                // check sum_i h_i = sum_i g_i for each lookup
                h.iter()
                    .zip_eq(g)
                    .map(|(hi, gi)| *hi - *gi)
                    .sum::<F>()
                    .eq(&F::ZERO)
            })
        };
        let gather_vectors = |W: &Vec<F>, start_index: usize| -> Vec<Vec<F>> {
            iter::successors(Some(start_index), |idx| Some(idx + 2))
                .take(self.num_lookups())
                .map(|idx| W[idx * nrow..(idx * nrow + nrow)].to_vec())
                .collect::<Vec<_>>()
        };

        if self.has_vector_lookup() {
            let hs = gather_vectors(&W[2], 0);
            let gs = gather_vectors(&W[2], 1);
            check_is_zero(&hs, &gs)
        } else if self.num_lookups() > 0 {
            let hs = gather_vectors(&W[1], 0);
            let gs = gather_vectors(&W[1], 1);
            check_is_zero(&hs, &gs)
        } else {
            true
        }
    }

    pub fn get_degree_for_folding(&self) -> usize {
        self.custom_gates_lookup_compressed.grouped().len()
    }

    pub fn dry_run_sps_protocol<C: CurveAffine<ScalarExt = F>>(&self) -> PlonkTrace<C> {
        PlonkTrace {
            u: PlonkInstance::new(self.num_io, self.num_challenges, self.round_sizes.len()),
            w: PlonkWitness::new(&self.round_sizes),
        }
    }

    /// run special soundness protocol to generate witnesses and challenges
    /// depending on whether we have multiple gates, lookup arguments and whether
    /// we have vector lookup, we will call different sub-sps protocol
    #[instrument(name = "sps", skip_all)]
    pub fn run_sps_protocol<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        ck: &CommitmentKey<C>,
        instance: &[F],
        advice: &[Vec<F>],
        ro_nark: &mut RO,
        num_challenges: usize,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        debug!("run sps protocol with {num_challenges} challenges");
        match num_challenges {
            0 => self.run_sps_protocol_0(instance, advice, ck),
            1 => self.run_sps_protocol_1(instance, advice, ck, ro_nark),
            2 => self.run_sps_protocol_2(instance, advice, ck, ro_nark),
            3 => self.run_sps_protocol_3(instance, advice, ck, ro_nark),
            challenges_count => Err(SpsError::UnsupportedChallengesCount { challenges_count }),
        }
    }

    /// run 0-round special soundness protocol
    /// w.r.t single custom gate + no lookup
    #[instrument(name = "0", skip_all)]
    fn run_sps_protocol_0<C: CurveAffine<ScalarExt = F>>(
        &self,
        instance: &[F],
        advice: &[Vec<F>],
        ck: &CommitmentKey<C>,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        let _span = info_span!("witness_commit").entered();

        let W1 = concatenate_with_padding(advice, 1 << self.k);
        let C1 = ck
            .commit(&W1)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W1",
                err,
            })?;

        Ok((
            PlonkInstance {
                W_commitments: vec![C1],
                instance: instance.to_vec(),
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
    #[instrument(name = "1", skip_all)]
    fn run_sps_protocol_1<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        instance: &[F],
        advice: &[Vec<F>],
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        let (mut plonk_instance, plonk_witness) = self.run_sps_protocol_0(instance, advice, ck)?;

        let _span = info_span!("instance_commit").entered();
        ro_nark
            .absorb_field_iter(instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_point_iter(plonk_instance.W_commitments.iter());

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
    #[instrument(name = "2", skip_all)]
    fn run_sps_protocol_2<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        instance: &[F],
        advice: &[Vec<F>],
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        let k_power_of_2 = 1 << self.k;

        // round 1
        let lookup_coeff = self
            .lookup_arguments
            .as_ref()
            .map(|la| la.evaluate_coefficient_1(self, advice, F::ZERO))
            .transpose()?
            .ok_or(SpsError::LackOfLookupArguments)?;

        let W1 = [
            concatenate_with_padding(advice, k_power_of_2),
            concatenate_with_padding(
                &concat_vec!(&lookup_coeff.ls, &lookup_coeff.ts, &lookup_coeff.ms),
                k_power_of_2,
            ),
        ]
        .concat();

        let C1 = {
            let _s = info_span!("lookup+witness_commit").entered();
            ck.commit(&W1).map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W1",
                err,
            })
        }?;

        let r1 = ro_nark
            .absorb_field_iter(instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_point(&C1)
            .squeeze::<C>(NUM_CHALLENGE_BITS);

        // round 2
        let lookup_coeff = lookup_coeff.evaluate_coefficient_2(r1);

        let W2 = concatenate_with_padding(
            &concat_vec!(&lookup_coeff.hs, &lookup_coeff.gs),
            k_power_of_2,
        );

        let C2 = {
            let _s = info_span!("lookup_commit").entered();
            ck.commit(&W2).map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W2",
                err,
            })
        }?;
        let r2 = ro_nark.absorb_point(&C2).squeeze::<C>(NUM_CHALLENGE_BITS);

        Ok((
            PlonkInstance {
                W_commitments: vec![C1, C2],
                instance: instance.to_vec(),
                challenges: vec![r1, r2],
            },
            PlonkWitness { W: vec![W1, W2] },
        ))
    }

    /// run 3-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C1] -> ]r1[ -> [C2] -> ]r2[ -> [C3] -> ]r3[
    #[instrument(name = "3", skip_all)]
    fn run_sps_protocol_3<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C::Base>>(
        &self,
        instance: &[F],
        advice: &[Vec<F>],
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        ro_nark.absorb_field_iter(instance.iter().map(|inst| fe_to_fe(inst).unwrap()));

        let k_power_of_2 = 1 << self.k;

        // round 1
        let W1 = concatenate_with_padding(advice, k_power_of_2);
        let C1 = {
            let _s = info_span!("witness_commit").entered();
            ck.commit(&W1).map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W1",
                err,
            })
        }?;
        let r1 = ro_nark.absorb_point(&C1).squeeze::<C>(NUM_CHALLENGE_BITS);

        // round 2
        let lookup_coeff = self
            .lookup_arguments
            .as_ref()
            .map(|la| la.evaluate_coefficient_1(self, advice, r1))
            .transpose()?
            .ok_or(SpsError::LackOfLookupArguments)?;

        let W2 = concatenate_with_padding(
            &concat_vec!(&lookup_coeff.ls, &lookup_coeff.ts, &lookup_coeff.ms),
            k_power_of_2,
        );
        let C2 = {
            let _s = info_span!("lookup_commit").entered();
            ck.commit(&W2).map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W2",
                err,
            })
        }?;
        let r2 = ro_nark.absorb_point(&C2).squeeze::<C>(NUM_CHALLENGE_BITS);

        // round 3
        let lookup_coeff = lookup_coeff.evaluate_coefficient_2(r2);

        let W3 = concatenate_with_padding(
            &concat_vec!(&lookup_coeff.hs, &lookup_coeff.gs),
            k_power_of_2,
        );

        let C3 = {
            let _s = info_span!("lookup_commit").entered();
            ck.commit(&W3).map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W3",
                err,
            })
        }?;
        let r3 = ro_nark.absorb_point(&C3).squeeze::<C>(NUM_CHALLENGE_BITS);

        Ok((
            PlonkInstance {
                W_commitments: vec![C1, C2, C3],
                instance: instance.to_vec(),
                challenges: vec![r1, r2, r3],
            },
            PlonkWitness {
                W: vec![W1, W2, W3],
            },
        ))
    }
}

impl<C: CurveAffine> PlonkInstance<C> {
    pub fn new(num_io: usize, num_challenges: usize, num_witness: usize) -> Self {
        Self {
            W_commitments: vec![CommitmentKey::<C>::default_value(); num_witness],
            instance: vec![C::ScalarExt::ZERO; num_io],
            challenges: vec![C::ScalarExt::ZERO; num_challenges],
        }
    }

    pub fn to_relax(&self) -> RelaxedPlonkInstance<C> {
        RelaxedPlonkInstance {
            W_commitments: self.W_commitments.clone(),
            E_commitment: C::identity(),
            instance: self.instance.clone(),
            challenges: self.challenges.clone(),
            u: C::ScalarExt::ONE,
        }
    }
}

impl<C: CurveAffine> RelaxedPlonkInstance<C> {
    pub fn new(num_io: usize, num_challenges: usize, num_witness: usize) -> Self {
        Self {
            W_commitments: vec![CommitmentKey::<C>::default_value(); num_witness],
            E_commitment: CommitmentKey::<C>::default_value(),
            instance: vec![C::ScalarExt::ZERO; num_io],
            challenges: vec![C::ScalarExt::ZERO; num_challenges],
            u: C::ScalarExt::ZERO,
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

        let instance = self
            .instance
            .par_iter()
            .zip(&U2.instance)
            .map(|(a, b)| *a + *r * b)
            .collect::<Vec<C::ScalarExt>>();

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
            E_commitment: comm_E,
            instance,
            u,
            challenges,
        }
    }
}

impl<F: PrimeField> RelaxedPlonkWitness<F> {
    /// round_sizes: specify the size of witness vector for each round
    /// in special soundness protocol.
    /// In current version, we have either one round (without lookup)
    /// or two rounds (with lookup)
    pub fn new(k_table_size: usize, round_sizes: &[usize]) -> Self {
        Self {
            W: round_sizes.iter().map(|sz| vec![F::ZERO; *sz]).collect(),
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

        RelaxedPlonkWitness { W, E }
    }
}

// Evaluates the witness data for each gate in the PLONK structure.
///
/// This function iterates through the gates of a provided [`PlonkStructure`],
/// evaluating the witness data for each gate. It returns an iterator over the results
/// of these evaluations.
///
/// # Type Parameters
/// - `C`: A curve affine type that implements the [`CurveAffine`] trait.
///
/// # Parameters
/// - `S`: A reference to a [`PlonkStructure`] containing the circuit structure and gates.
/// - `trace`: An object that provides both challenges and witness values through the
///            [`GetChallenges`] and [`GetWitness`] traits. In can be: [`PlonkWitness`],
///            [`RelaxedPlonkWitness`], [`RelaxedPlonkTrace`], [`PlonkTrace`] etc
///
/// # Returns
/// An iterator that produces [`Result<C::ScalarExt, eval::Error>`] items. Each item is either the
/// result of evaluating the witness for a specific gate and row, or an error if the evaluation
/// fails.
///
/// In other words iterator: `[gate1(row0), ..., gate1(rowN), gate2(0), ...]`
pub(crate) fn iter_evaluate_witness<'link, F: PrimeField>(
    S: &'link PlonkStructure<F>,
    trace: &'link (impl Sync + GetChallenges<F> + GetWitness<F>),
) -> impl 'link + Send + Iterator<Item = Result<F, eval::Error>> {
    S.gates.iter().flat_map(|gate| {
        let eval_domain = PlonkEvalDomain {
            num_advice: S.num_advice_columns,
            num_lookup: S.num_lookups(),
            selectors: &S.selectors,
            fixed: &S.fixed_columns,
            challenges: trace.get_challenges(),
            W1s: trace.get_witness(),
            W2s: &[],
        };

        let evaluator = GraphEvaluator::new(gate);

        (0..eval_domain.row_size())
            .map(move |row_index| evaluator.evaluate(&eval_domain, row_index))
    })
}

#[cfg(test)]
pub(crate) mod test_eval_witness {
    pub mod poseidon_circuit {
        use std::{array, marker::PhantomData};

        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            plonk::{Circuit, ConstraintSystem},
        };

        use crate::{
            ff::{FromUniformBytes, PrimeFieldBits},
            main_gate::{MainGate, MainGateConfig, RegionCtx, WrapValue},
            poseidon::{poseidon_circuit::PoseidonChip, Spec},
        };

        /// Input and output size for `StepCircuit` within each step
        pub const ARITY: usize = 1;

        /// Spec for on-circuit poseidon circuit
        const POSEIDON_PERMUTATION_WIDTH: usize = 3;
        const POSEIDON_RATE: usize = POSEIDON_PERMUTATION_WIDTH - 1;

        pub type CircuitPoseidonSpec<F> = Spec<F, POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE>;

        const R_F1: usize = 4;
        const R_P1: usize = 3;

        #[derive(Clone, Debug)]
        pub struct TestPoseidonCircuitConfig {
            pconfig: MainGateConfig<POSEIDON_PERMUTATION_WIDTH>,
        }

        #[derive(Debug, Default)]
        pub struct TestPoseidonCircuit<F: PrimeFieldBits> {
            _p: PhantomData<F>,
        }

        impl<F: PrimeFieldBits + FromUniformBytes<64>> Circuit<F> for TestPoseidonCircuit<F> {
            type Config = TestPoseidonCircuitConfig;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                todo!()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let pconfig = MainGate::configure(meta);
                Self::Config { pconfig }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), halo2_proofs::plonk::Error> {
                let spec = CircuitPoseidonSpec::<F>::new(R_F1, R_P1);

                layouter.assign_region(
                    || "poseidon hash",
                    move |region| {
                        let z_i: [F; 50] = array::from_fn(|i| F::from(i as u64));
                        let ctx = &mut RegionCtx::new(region, 0);

                        let mut pchip = PoseidonChip::new(config.pconfig.clone(), spec.clone());

                        pchip.update(
                            &z_i.iter()
                                .cloned()
                                .map(|f: F| WrapValue::Unassigned(Value::known(f)))
                                .collect::<Vec<WrapValue<F>>>(),
                        );

                        pchip.squeeze(ctx)?;

                        Ok(())
                    },
                )
            }
        }
    }

    use crate::{
        commitment::CommitmentKey,
        ff::Field as _Field,
        halo2curves::{bn256, CurveAffine},
        plonk::PlonkTrace,
        poseidon::{
            random_oracle::{self, ROTrait},
            PoseidonRO, Spec,
        },
        table::CircuitRunner,
    };

    type Curve = bn256::G1Affine;
    type Field = <Curve as CurveAffine>::ScalarExt;

    /// Spec for off-circuit poseidon
    const POSEIDON_PERMUTATION_WIDTH: usize = 3;
    const POSEIDON_RATE: usize = POSEIDON_PERMUTATION_WIDTH - 1;

    const R_F1: usize = 4;
    const R_P1: usize = 3;
    pub type PoseidonSpec = Spec<
        <Curve as crate::halo2curves::CurveAffine>::Base,
        POSEIDON_PERMUTATION_WIDTH,
        POSEIDON_RATE,
    >;

    type RO = <PoseidonRO<POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE> as random_oracle::ROPair<
        <Curve as crate::halo2curves::CurveAffine>::Base,
    >>::OffCircuit;

    #[test]
    fn basic() {
        let runner = CircuitRunner::<Field, _>::new(
            12,
            poseidon_circuit::TestPoseidonCircuit::default(),
            vec![],
        );

        let S = runner.try_collect_plonk_structure().unwrap();

        let witness = runner.try_collect_witness().unwrap();

        let (u, w) = S
            .run_sps_protocol(
                &CommitmentKey::<Curve>::setup(15, b"k"),
                &[],
                &witness,
                &mut RO::new(PoseidonSpec::new(R_F1, R_P1)),
                S.num_challenges,
            )
            .unwrap();

        use rayon::prelude::*;
        super::iter_evaluate_witness::<Field>(&S, &PlonkTrace { u, w })
            .par_bridge()
            .for_each(|v| {
                assert_eq!(v, Ok(Field::ZERO));
            });
    }
}
