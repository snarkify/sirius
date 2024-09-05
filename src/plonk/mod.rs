//! This module defines the Plonk related types for working with
//! halo2 circuits. It provides functionality to retrieve PlonkStructure and witness
//! data, as well as defining various methods used by the folding scheme.
//!
//! The main types defined in this module are:
//! - PlonkStructure: Represents the structure of a Plonk circuit and its associated data.
//! - PlonkInstance: Represents an instance of a Plonk circuit.
//! - PlonkWitness: Represents the witness data for a Plonk circuit.
//!
//! Additionally, it defines a method is_sat on PlonkStructure to determine if
//! a given Plonk instance and witness satisfy the circuit constraints.
use std::{iter, num::NonZeroUsize, time::Instant};

use count_to_non_zero::*;
use halo2_proofs::arithmetic::CurveAffine;
use itertools::Itertools;
use rayon::prelude::*;
use serde::Serialize;
use some_to_err::*;
use tracing::{debug, error, info, info_span, instrument, warn};

use crate::{
    commitment::CommitmentKey,
    concat_vec,
    constants::NUM_CHALLENGE_BITS,
    ff::{Field, PrimeField},
    plonk::{
        self,
        eval::{Error as EvalError, GetDataForEval, PlonkEvalDomain},
    },
    polynomial::{
        expression::{HomogeneousExpression, QueryIndexContext},
        graph_evaluator::GraphEvaluator,
        grouped_poly::GroupedPoly,
        sparse::SparseMatrix,
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
    // TODO #329 Remove this field
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

#[derive(Clone, Debug, PartialEq, Eq)]
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
}

// TODO #31 docs
#[derive(Debug, Clone)]
pub struct PlonkTrace<C: CurveAffine> {
    pub u: PlonkInstance<C>,
    pub w: PlonkWitness<C::Scalar>,
}

#[derive(Debug)]
pub struct PlonkTraceArgs {
    pub num_io: usize,
    pub num_challenges: usize,
    pub num_witness: usize,
    pub k_table_size: usize,
    pub round_sizes: Box<[usize]>,
}

impl<F: PrimeField> From<&PlonkStructure<F>> for PlonkTraceArgs {
    fn from(value: &PlonkStructure<F>) -> Self {
        Self {
            num_io: value.num_io,
            num_challenges: value.num_challenges,
            num_witness: value.round_sizes.len(),
            k_table_size: value.k,
            round_sizes: value.round_sizes.clone().into_boxed_slice(),
        }
    }
}

impl<C: CurveAffine> PlonkTrace<C> {
    pub fn new(args: PlonkTraceArgs) -> Self {
        Self {
            u: PlonkInstance::new(args.num_io, args.num_challenges, args.num_witness),
            w: PlonkWitness::new(&args.round_sizes),
        }
    }
}

/// Generalized trait to get witness
///
/// Used to generalize:
/// - [`PlonkWitness`]
/// - [`PlonkTrace`]
pub(crate) trait GetWitness<F: PrimeField> {
    fn get_witness(&self) -> &[Vec<F>];
}
impl<F: PrimeField> GetWitness<F> for PlonkWitness<F> {
    fn get_witness(&self) -> &[Vec<F>] {
        &self.W
    }
}
impl<C: CurveAffine> GetWitness<C::ScalarExt> for PlonkTrace<C> {
    fn get_witness(&self) -> &[Vec<C::ScalarExt>] {
        self.w.get_witness()
    }
}

/// Generalized trait to get challenges
///
/// Used to generalize:
/// - [`PlonkWitness`]
/// - [`PlonkTrace`]
pub(crate) trait GetChallenges<F: PrimeField> {
    fn get_challenges(&self) -> &[F];
}
impl<C: CurveAffine> GetChallenges<C::ScalarExt> for PlonkInstance<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        &self.challenges
    }
}

impl<C: CurveAffine> GetChallenges<C::ScalarExt> for PlonkTrace<C> {
    fn get_challenges(&self) -> &[C::ScalarExt] {
        self.u.get_challenges()
    }
}

impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO> for PlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point_iter(self.W_commitments.iter())
            .absorb_field_iter(self.instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_field_iter(self.challenges.iter().map(|cha| fe_to_fe(cha).unwrap()));
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

    // permutation check for folding instance-witness pair

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
    ) -> Result<PlonkTrace<C>, SpsError> {
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
    ) -> Result<PlonkTrace<C>, SpsError> {
        let _span = info_span!("witness_commit").entered();

        let W1 = concatenate_with_padding(advice, 1 << self.k);
        let C1 = ck
            .commit(&W1)
            .map_err(|err| SpsError::WrongCommitmentSize {
                annotation: "W1",
                err,
            })?;

        Ok(PlonkTrace {
            u: PlonkInstance {
                W_commitments: vec![C1],
                instance: instance.to_vec(),
                challenges: vec![],
            },
            w: PlonkWitness { W: vec![W1] },
        })
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
    ) -> Result<PlonkTrace<C>, SpsError> {
        let PlonkTrace {
            u: mut plonk_instance,
            w: plonk_witness,
        } = self.run_sps_protocol_0(instance, advice, ck)?;

        let _span = info_span!("instance_commit").entered();
        ro_nark
            .absorb_field_iter(instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_point_iter(plonk_instance.W_commitments.iter());

        plonk_instance
            .challenges
            .push(ro_nark.squeeze::<C>(NUM_CHALLENGE_BITS));

        Ok(PlonkTrace {
            u: plonk_instance,
            w: plonk_witness,
        })
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
    ) -> Result<PlonkTrace<C>, SpsError> {
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

        Ok(PlonkTrace {
            u: PlonkInstance {
                W_commitments: vec![C1, C2],
                instance: instance.to_vec(),
                challenges: vec![r1, r2],
            },
            w: PlonkWitness { W: vec![W1, W2] },
        })
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
    ) -> Result<PlonkTrace<C>, SpsError> {
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

        Ok(PlonkTrace {
            u: PlonkInstance {
                W_commitments: vec![C1, C2, C3],
                instance: instance.to_vec(),
                challenges: vec![r1, r2, r3],
            },
            w: PlonkWitness {
                W: vec![W1, W2, W3],
            },
        })
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
        pub struct TestPoseidonCircuit<F: PrimeFieldBits, const L: usize = 50> {
            _p: PhantomData<F>,
        }

        impl<F: PrimeFieldBits + FromUniformBytes<64>, const L: usize> Circuit<F>
            for TestPoseidonCircuit<F, L>
        {
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
                        let z_i: [F; L] = array::from_fn(|i| F::from(i as u64));
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
    pub type PoseidonSpec =
        Spec<<Curve as CurveAffine>::Base, POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE>;

    type RO = <PoseidonRO<POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE> as random_oracle::ROPair<
        <Curve as CurveAffine>::Base,
    >>::OffCircuit;

    #[test]
    fn basic() {
        let runner = CircuitRunner::<Field, _>::new(
            12,
            poseidon_circuit::TestPoseidonCircuit::<_, 50>::default(),
            vec![],
        );

        let S = runner.try_collect_plonk_structure().unwrap();

        let witness = runner.try_collect_witness().unwrap();

        let PlonkTrace { u, w } = S
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
