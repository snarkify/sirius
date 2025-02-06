//! # Fold Relaxed PLONK Instance Chip
//!
//! This module implements the folding mechanism for a relaxed PLONK instance from a PLONKish circuit,
//! specifically designed to work within the halo2 proof framework. The folding process is
//! crucial in constructing recursive SNARKs, enabling the combination of multiple instances into
//! a single proof.
//!
//! ## Overview
//!
//! The main component of this module is the [`FoldRelaxedPlonkInstanceChip`]. This chip is responsible
//! for performing the fold operation on a relaxed PLONK instance, which involves several computational
//! and cryptographic steps, essential for building recursive proofs in SNARKs.
//!
//! ### Folding Algorithm
//!
//! The folding algorithm works by combining running accumulator with [`PlonkInstance`]
//! derived from previous step of IVC circuit
//!
//! This process involves several steps:
//!
//! 1. **Assigning Witnesses**: Assigns all necessary values and points, including the public parameters
//!    commitments, elliptic curve points, and big number representations of the instance values.
//! 2. **Generating Challenges**: Utilizes a random oracle circuit to generate cryptographic challenges,
//!    essential for the security of the fold operation.
//! 3. **Elliptic Curve Computations**: Performs scalar multiplications and additions on elliptic curve
//!    points, crucial for encoding the folded proof.
//! 4. **Big Number Operations**: Executes modular arithmetic on large integers, represented as big
//!    numbers, a key step in handling the arithmetic of cryptographic primitives.
//!
//! ### Variables and Structures
//!
//! - [`FoldRelaxedPlonkInstanceChip`]: The primary structure used for folding a PLONK instance.
//! - [`PlonkInstance`]: Represents a standard PLONK proof instance with its commitments and parameters.
//! - [`RelaxedPlonkInstance`]: A variant of `PlonkInstance` adjusted for the folding process.
//! - [`AssignedWitness`]: Holds the assigned variables and points required for the folding operation.
//!
//! ### References
//!
//! The folding algorithm and its implementation are heavily inspired by and based on concepts described
//! in the Nova whitepaper:
//!
//! - [**Nova: Recursive Zero-Knowledge Arguments from Folding Schemes**](https://eprint.iacr.org/2021/370) (Sections 3 and 4)
//!   This paper provides the foundational cryptographic framework and theoretical basis for the folding
//!   mechanism used in this module.

use std::{iter, num::NonZeroUsize, ops};

use itertools::Itertools;
use num_traits::Num;
use tracing::*;

use crate::{
    constants::NUM_CHALLENGE_BITS,
    ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits},
    gadgets::{
        ecc::{AssignedPoint, EccChip},
        nonnative::bn::{
            big_uint::{self, BigUint},
            big_uint_mul_mod_chip::{self, BigUintMulModChip, OverflowingBigUint},
        },
    },
    halo2_proofs::circuit::AssignedCell,
    halo2curves::CurveAffine,
    ivc::sangria::instances_accumulator_computation,
    main_gate::{
        AdviceCyclicAssignor, AssignedBit, AssignedValue, MainGate, MainGateConfig, RegionCtx,
        WrapValue,
    },
    nifs::sangria::{
        accumulator::{FoldablePlonkInstance, RelaxedPlonkInstance, SCInstancesHashAcc},
        GetConsistencyMarkers, GetStepCircuitInstances, CONSISTENCY_MARKERS_COUNT,
    },
    poseidon::ROCircuitTrait,
    util::{self, CellsValuesView},
};

/// `MARKERS_LEN` - the first column of instance is folded separately, the length of this column is
/// regulated by this parameter
pub(crate) struct FoldRelaxedPlonkInstanceChip<
    const T: usize,
    C: CurveAffine,
    const MARKERS_LEN: usize,
> where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    relaxed: RelaxedPlonkInstance<C, MARKERS_LEN>,
    config: MainGateConfig<T>,
    bn_chip: BigUintMulModChip<C::Base>,

    limb_width: NonZeroUsize,
    limbs_count: NonZeroUsize,
}

/// Holds the assigned values and points resulting from the folding process.
#[derive(Debug, Clone)]
pub(crate) struct AssignedRelaxedPlonkInstance<C: CurveAffine, const MARKERS_LEN: usize> {
    /// Assigned point representing the folded accumulator W.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::W`]
    pub folded_W: Vec<AssignedPoint<C>>,

    /// Assigned point representing the folded accumulator E.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::E`]
    pub folded_E: AssignedPoint<C>,

    /// Assigned value of the folded scalar u.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::u`]
    pub folded_u: AssignedValue<C::Base>,

    /// Vector of vectors of assigned values for each limb of the folded challenges.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::challenges`].
    pub folded_challenges: Vec<Vec<AssignedValue<C::Base>>>,

    /// Vector of assigned values for each limb of the folded big number X0 & X1.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::consistency_markers`]
    pub folded_consistency_markers: [Vec<AssignedValue<C::Base>>; MARKERS_LEN],

    /// Assigned value of the step circuit instances hash accumulator
    /// Derived from [`FoldRelaxedPlonkInstanceChip::step_circuit_instances_hash_accumulator`]
    pub folded_step_circuit_instances_hash_accumulator: SCInstancesHashAcc<AssignedValue<C::Base>>,
}

impl<C: CurveAffine, const MARKERS: usize> AssignedRelaxedPlonkInstance<C, MARKERS> {
    pub fn conditional_select<const T: usize>(
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        lhs: &Self,
        rhs: &Self,
        condition: AssignedValue<C::Base>,
    ) -> Result<Self, Error>
    where
        C::Base: PrimeFieldBits,
    {
        let ecc = EccChip::<C, MainGate<C::Base, T>>::new(config.clone());
        let gate = MainGate::<C::Base, T>::new(config.clone());

        let Self {
            folded_W: lhs_folded_W,
            folded_E: lhs_folded_E,
            folded_u: lhs_folded_u,
            folded_challenges: lhs_folded_challenges,
            folded_consistency_markers: lhs_folded_consistency_markers,
            folded_step_circuit_instances_hash_accumulator:
                lhs_step_circuit_instances_hash_accumulator,
        } = lhs;

        let Self {
            folded_W: rhs_folded_W,
            folded_E: rhs_folded_E,
            folded_u: rhs_folded_u,
            folded_challenges: rhs_folded_challenges,
            folded_consistency_markers: rhs_folded_consistency_markers,
            folded_step_circuit_instances_hash_accumulator:
                rhs_step_circuit_instances_hash_accumulator,
        } = rhs;

        let folded_W = lhs_folded_W
            .iter()
            .zip_eq(rhs_folded_W.iter())
            .map(|(lhs_Wi, rhs_Wi)| ecc.conditional_select(region, lhs_Wi, rhs_Wi, &condition))
            .collect::<Result<Vec<_>, _>>()?;

        let folded_E = ecc.conditional_select(region, lhs_folded_E, rhs_folded_E, &condition)?;

        let folded_u = gate.conditional_select(region, lhs_folded_u, rhs_folded_u, &condition)?;

        let folded_challenges = lhs_folded_challenges
            .iter()
            .zip_eq(rhs_folded_challenges.iter())
            .map(|(lhs_challenge, rhs_challenge)| {
                lhs_challenge
                    .iter()
                    .zip_eq(rhs_challenge.iter())
                    .map(|(lhs, rhs)| gate.conditional_select(region, lhs, rhs, &condition))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        let folded_consistency_markers = lhs_folded_consistency_markers
            .iter()
            .zip_eq(rhs_folded_consistency_markers.iter())
            .map(|(lhs, rhs)| {
                lhs.iter()
                    .zip_eq(rhs)
                    .map(|(lhs, rhs)| gate.conditional_select(region, lhs, rhs, &condition))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .unwrap();

        let folded_step_circuit_instances_hash_accumulator = match SCInstancesHashAcc::zip(
            lhs_step_circuit_instances_hash_accumulator,
            rhs_step_circuit_instances_hash_accumulator,
        ) {
            SCInstancesHashAcc::Hash((lhs, rhs)) => {
                SCInstancesHashAcc::Hash(gate.conditional_select(region, lhs, rhs, &condition)?)
            }
            SCInstancesHashAcc::None => SCInstancesHashAcc::None,
        };

        Ok(Self {
            folded_W,
            folded_E,
            folded_u,
            folded_challenges,
            folded_consistency_markers,
            folded_step_circuit_instances_hash_accumulator,
        })
    }

    pub fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<C::Base>>
    where
        <C as CurveAffine>::Base: PrimeFieldBits + FromUniformBytes<64>,
    {
        let Self {
            folded_W,
            folded_E,
            folded_u,
            folded_challenges,
            folded_consistency_markers,
            folded_step_circuit_instances_hash_accumulator,
        } = self;

        folded_W
            .iter()
            .flat_map(|W| WrapValue::from_assigned_point(W))
            .chain(WrapValue::from_assigned_point(folded_E))
            .chain(
                folded_consistency_markers
                    .iter()
                    .flatten()
                    .map(|v| v.into()),
            )
            .chain(folded_challenges.iter().flatten().map(Into::into))
            .chain(iter::once(WrapValue::from(folded_u)))
            .chain(iter::once(
                folded_step_circuit_instances_hash_accumulator.into(),
            ))
    }
}
impl<C: CurveAffine, const MARKERS_LEN: usize> AssignedRelaxedPlonkInstance<C, MARKERS_LEN> {
    #[cfg(test)]
    fn to_relaxed_plonk_instance(
        &self,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Option<RelaxedPlonkInstance<C, MARKERS_LEN>>, Error> {
        let Self {
            folded_W,
            folded_E,
            folded_u,
            folded_challenges,
            folded_consistency_markers,
            folded_step_circuit_instances_hash_accumulator,
        } = self;

        macro_rules! unwrap_result_option {
            ($input:expr) => {{
                match $input {
                    Some(val) => val,
                    None => {
                        return Ok((None));
                    }
                }
            }};
        }

        let folded_consistency_markers: [_; MARKERS_LEN] =
            unwrap_result_option!(folded_consistency_markers
                .iter()
                .map(|val| { BigUint::from_assigned_cells(val, limb_width, limbs_count) })
                .collect::<Result<Option<Vec<_>>, _>>()?)
            .try_into()
            .unwrap();

        let to_diff_bn =
            |bn: &[ AssignedCell<C::Base, C::Base> ]| -> Option<Result<C::ScalarExt, big_uint::Error>> {
                let limbs = bn
                    .iter()
                    .map(|limb_cell| limb_cell.value().unwrap().copied())
                    .map(|limb| {
                        limb.map(|limb| util::fe_to_fe_safe(&limb).expect("fields same bytes len"))
                    })
                    .collect::<Option<Vec<_>>>()?;

                let bn = BigUint::<C::ScalarExt>::from_limbs(limbs.into_iter(), limb_width, limbs_count);

                let bn_f = bn.map(|r| {
                    r.into_f().expect(
                        "since biguint calculations are modulo the scalar field, any result must fit",
                    )
                });

                Some(bn_f)
            };

        Ok(Some(RelaxedPlonkInstance {
            W_commitments: unwrap_result_option!(folded_W
                .iter()
                .map(AssignedPoint::to_curve)
                .collect()),
            consistency_markers: folded_consistency_markers.map(|X| {
                util::fe_to_fe_safe(&X.into_f().expect(
                    "since biguint calculations are modulo the scalar field, any result must fit",
                ))
                .expect("fields same bytes len")
            }),
            challenges: folded_challenges
                .iter()
                .flat_map(|c| to_diff_bn(c))
                .collect::<Result<Vec<_>, _>>()?,
            E_commitment: unwrap_result_option!(folded_E.to_curve()),
            u: util::fe_to_fe_safe(&unwrap_result_option!(folded_u.value().unwrap().copied()))
                .expect("fields same bytes len"),
            step_circuit_instances_hash_accumulator:
                match folded_step_circuit_instances_hash_accumulator {
                    SCInstancesHashAcc::None => SCInstancesHashAcc::None,
                    SCInstancesHashAcc::Hash(hash) => SCInstancesHashAcc::Hash({
                        util::fe_to_fe_safe(&unwrap_result_option!(hash.value().unwrap().copied()))
                            .expect("fields same bytes len")
                    }),
                },
        }))
    }
}

#[derive(Debug, Clone)]
pub(crate) struct AssignedConsistencyMarkerView<F: PrimeField> {
    pub as_value: AssignedValue<F>,
    pub as_bn_limbs: Vec<AssignedValue<F>>,
}

/// Holds the assigned values and points resulting from the folding process.
#[derive(Clone)]
pub(crate) struct AssignedWitness<C: CurveAffine, const MARKERS: usize> {
    /// Assigned value of the public parameters commitment.
    /// Sourced directly from the `public_params_hash` argument of [`FoldRelaxedPlonkInstanceChip::fold`].
    pub public_params_hash: AssignedPoint<C>,

    /// Assigned [`RelaxedPlonkInstance`]
    pub assigned_relaxed: AssignedRelaxedPlonkInstance<C, MARKERS>,

    /// Assigned point representing the commitment to the `W` value of the input PLONK instance.
    /// Sourced directly from [`PlonkInstance::W_commitments`] provided to [`FoldRelaxedPlonkInstanceChip::fold`].
    input_W_commitments: Vec<AssignedPoint<C>>,

    /// Vector of vectors of assigned values for each limb of the input instances.
    /// Sourced directly from [`PlonkInstance::instance`] provided to [`FoldRelaxedPlonkInstanceChip::fold`].
    ///
    /// The zero element is the input validator
    /// The first element is the output validator
    pub input_consistency_markers: [AssignedConsistencyMarkerView<C::Base>; MARKERS],

    /// Vector of vectors of assigned values for each limb of the input challenges.
    /// Sourced directly from [`PlonkInstance::challenges`] provided to [`FoldRelaxedPlonkInstanceChip::fold`].
    pub input_challenges: Vec<Vec<AssignedValue<C::Base>>>,

    /// Vector of assigned points representing the commitments to the cross terms.
    /// Sourced directly from the `cross_term_commits` argument of [`FoldRelaxedPlonkInstanceChip::fold`].
    cross_terms_commits: Vec<AssignedPoint<C>>,

    /// TODO #319
    pub input_step_circuit_instances: Vec<AssignedValue<C::Base>>,
}

impl<C: CurveAffine, const MARKERS_LEN: usize> ops::Deref for AssignedWitness<C, MARKERS_LEN> {
    type Target = AssignedRelaxedPlonkInstance<C, MARKERS_LEN>;
    fn deref(&self) -> &Self::Target {
        &self.assigned_relaxed
    }
}

/// Enumerates possible errors that can occur during the folding process
/// in the fold algorithm.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("BigUint Error: {0:?}")]
    BigUint(#[from] big_uint::Error),

    #[error("BigUint Chip Error: {0:?}")]
    BigUintChip(#[from] big_uint_mul_mod_chip::Error),

    #[error("Halo2 proof system error: {0:?}")]
    Halo2(#[from] halo2_proofs::plonk::Error),

    #[error("Error constructing elliptic curve coordinates for {variable_name}: {variable_str}")]
    CantBuildCoordinates {
        variable_name: String,
        variable_str: String,
    },

    #[error("Error converting scalar to base field element for {variable_name}: {variable_str}")]
    WhileScalarToBase {
        variable_name: String,
        variable_str: String,
    },
}
impl From<Error> for halo2_proofs::plonk::Error {
    fn from(err: Error) -> halo2_proofs::plonk::Error {
        error!("downcast error: {err:?} to `Synthesis`");
        halo2_proofs::plonk::Error::Synthesis
    }
}

impl<const T: usize, C: CurveAffine, const MARKERS_LEN: usize>
    FoldRelaxedPlonkInstanceChip<T, C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new(
        relaxed: RelaxedPlonkInstance<C, MARKERS_LEN>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
        config: MainGateConfig<T>,
    ) -> Self {
        let bn_chip = BigUintMulModChip::<C::Base>::new(
            config
                .into_smaller_size::<{ big_uint_mul_mod_chip::MAIN_GATE_T }>()
                .expect("Only T>=4 allowed for this chip"),
            limb_width,
            limbs_count,
        );

        Self {
            bn_chip,
            config,
            relaxed,
            limb_width,
            limbs_count,
        }
    }

    /// Fold [`RelaxedPlonkInstance::W_commitments`] & [`PlonkInstance::W_commitments`]
    ///
    /// # Description
    ///
    /// This function is responsible for combining the current `folded_W` accumulator with `input_W_commitments`.
    /// This is achieved through a scalar multiplication followed by an elliptic curve addition.
    /// The scalar multiplication is defined by a random scalar `r`.
    ///
    /// # Implementation Details
    ///
    /// 1. **Scalar Multiplication**: Each `W` component from `input_W_commitments` is multiplied
    ///    by random the scalar `r` (challenge). This is executed using the [`EccChip`] for elliptic curve operations.
    /// 2. **Accumulation**: The result of the scalar multiplication is then added to the corresponding component in
    ///    the current `folded_W` accumulator. This is executed using the [`EccChip`] for elliptic curve operations.
    ///
    /// ```markdown
    /// new_folded_W[i] = folded_W[i] + input_W[i] * r
    /// ```
    pub fn fold_W(
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        folded_W: &[AssignedPoint<C>],
        input_W_commitments: &[AssignedPoint<C>],
        r: &[AssignedCell<C::Base, C::Base>],
    ) -> Result<Vec<AssignedPoint<C>>, Error> {
        let ecc = EccChip::<C, MainGate<C::Base, T>>::new(config.clone());

        folded_W
            .iter()
            .zip_eq(input_W_commitments)
            .enumerate()
            .map(|(W_index, (W1, W2))| -> Result<AssignedPoint<C>, Error> {
                let rW = ecc.scalar_mul(region, W2, r)?;
                let res = ecc.add(region, W1, &rW)?;
                debug!(
                    "W1 = {W1:?}; W2 = {W2:?}; rW2[{W_index}] = {rW:?}; rW1 + rW2 * r = {res:?}"
                );
                Ok(res)
            })
            .collect()
    }

    /// Fold consistency markers
    ///
    /// # Description
    ///
    /// This function is responsible for combining the current `folded_consistency_markers` accumulator with
    /// `input_consistency_marker`. This is achieved through a [`FoldRelaxedPlonkInstanceChip::fold_via_biguint`]
    /// fn call.
    ///
    /// ```markdown
    /// new_folded_consistency_marker[i] = fold_via_biguin(folded_consistency_marker[i], input_consistency_marker[i], m, r)
    /// ```
    ///
    /// Please check [`FoldRelaxedPlonkInstanceChip::fold_via_biguint`] for more details
    fn fold_consistency_markers(
        region: &mut RegionCtx<C::Base>,
        bn_chip: &BigUintMulModChip<C::Base>,
        input_consistency_marker: [Vec<AssignedValue<C::Base>>; MARKERS_LEN],
        folded_consistency_marker: [Vec<AssignedValue<C::Base>>; MARKERS_LEN],
        r_as_bn: &[AssignedCell<C::Base, C::Base>],
        m_bn: &BigUint<C::Base>,
        limb_width: NonZeroUsize,
    ) -> Result<[Vec<AssignedCell<C::Base, C::Base>>; MARKERS_LEN], Error> {
        let new_folded_markers = input_consistency_marker
            .into_iter()
            .zip_eq(folded_consistency_marker.iter())
            .enumerate()
            .map(|(i, (input_marker, folded_marker))| {
                fold_via_biguint(
                    region,
                    bn_chip,
                    &input_marker,
                    folded_marker.to_vec(),
                    m_bn,
                    r_as_bn,
                    limb_width,
                )
                .inspect_err(|err| error!("Error while folding marker {i}: {err:?}"))
                .inspect(|new_folded_marker| {
                    debug!(
                        "fold: Marker {i} folded: {:?}",
                        CellsValuesView::from(new_folded_marker.as_slice())
                    );
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(new_folded_markers.try_into().unwrap())
    }

    /// Fold [`RelaxedPlonkInstance::E_commitments`] & [`CrossTermCommits`]
    ///
    /// # Description
    ///
    /// This function is responsible for combining the current `folded_W` accumulator with
    /// `cross_term_commits`. This is achieved through a scalar multiplication followed by
    /// an elliptic curve addition. The scalar multiplication is defined by a random
    /// scalar `r` in power of cross term commit index.
    ///
    /// # Implementation Details
    ///
    /// 1. **Multiplication & Conversion to bits**: Form a vector of degrees `r` and their representations as bits
    /// 2. **Scalar Multiplication**: Each element of `cross_term_commits` is multiplied by power of random scalar
    ///    `r` (challenge) in bits representation. This is executed using the [`EccChip`] for elliptic curve operations.
    /// 3. **Accumulation**: The result of the scalar multiplication is then added to the corresponding component in
    ///    the current `folded_E` accumulator. This is executed using the [`EccChip`] for elliptic curve operations.
    ///
    /// ```markdown
    /// new_folded_E = folded_E + Sum [ cross_term_commits[i] * (r ^ i) ]
    /// ```
    pub fn fold_E(
        &self,
        region: &mut RegionCtx<C::Base>,
        folded_E: AssignedPoint<C>,
        cross_term_commits: &[AssignedPoint<C>],
        r: BigUintView<C::Base>,
        m_bn: &BigUint<C::Base>,
    ) -> Result<AssignedPoint<C>, Error> {
        debug!("Start calculate r^i from {r:?}");
        fold_E(
            region,
            &self.bn_chip,
            &EccChip::<C, MainGate<C::Base, T>>::new(self.config.clone()),
            folded_E,
            cross_term_commits,
            r,
            m_bn,
        )
    }

    fn fold_step_circuit_instances(
        ctx: &mut RegionCtx<C::Base>,
        config: MainGateConfig<T>,
        input_instances: &[AssignedValue<C::Base>],
        folded_instances: &SCInstancesHashAcc<AssignedValue<C::Base>>,
    ) -> Result<SCInstancesHashAcc<AssignedValue<C::Base>>, Error> {
        Ok(match folded_instances {
            SCInstancesHashAcc::None => {
                assert!(input_instances.is_empty());
                SCInstancesHashAcc::None
            }
            SCInstancesHashAcc::Hash(folded_instances) => SCInstancesHashAcc::Hash(
                instances_accumulator_computation::absorb_in_assign_sc_instances_accumulator(
                    ctx,
                    config.into_smaller_size().unwrap(),
                    folded_instances,
                    input_instances,
                )?,
            ),
        })
    }

    /// Fold [`RelaxedPlonkInstance::challenges`] & [`PlonkInstance::challenges`]
    ///
    /// # Description
    ///
    /// This function is responsible for combining the current `folded_challenges` accumulator with
    /// `input_challenges`. This is achieved through a [`FoldRelaxedPlonkInstanceChip::fold_via_biguint`]
    /// fn call.
    ///
    /// ```markdown
    /// new_folded_challenges[i] = fold_via_biguin(folded_challenges[i], input_challenges[i], m, r)
    /// ```
    ///
    /// Please check [`FoldRelaxedPlonkInstanceChip::fold_via_biguint`] for more details
    pub fn fold_challenges(
        region: &mut RegionCtx<C::Base>,
        bn_chip: &BigUintMulModChip<C::Base>,
        input_challenges: Vec<Vec<AssignedValue<C::Base>>>,
        folded_challenges: Vec<Vec<AssignedValue<C::Base>>>,
        r_as_bn: &[AssignedValue<C::Base>],
        m_bn: &BigUint<C::Base>,
        limb_width: NonZeroUsize,
    ) -> Result<Vec<Vec<AssignedValue<C::Base>>>, Error> {
        folded_challenges
            .into_iter()
            .zip_eq(input_challenges)
            .map(|(folded_challenge, input_challange)| {
                fold_via_biguint(
                    region,
                    bn_chip,
                    &input_challange,
                    folded_challenge,
                    m_bn,
                    r_as_bn,
                    limb_width,
                )
            })
            .collect::<Result<Vec<_>, Error>>()
    }

    // TODO #32 rustdoc
    pub fn fold(
        &self,
        region: &mut RegionCtx<C::Base>,
        w: AssignedWitness<C, MARKERS_LEN>,
        r: Vec<AssignedBit<C::Base>>,
    ) -> Result<FoldResult<C, MARKERS_LEN>, Error> {
        debug!("fold: Assigned & Generated challenge: {r:?}");

        let gate = MainGate::new(self.config.clone());

        let r_value = gate.le_bits_to_num(region, &r)?;
        debug!("sangria on-circuir r: {:?}", r_value.value());

        let r = BigUintView {
            as_bn_limbs: self
                .bn_chip
                .from_assigned_value_to_limbs(region, &r_value)?,
            as_bits: r.clone(),
        };

        let new_folded_W = Self::fold_W(
            region,
            &self.config,
            &w.assigned_relaxed.folded_W,
            &w.input_W_commitments,
            &r,
        )?;

        debug!("fold: W folded: {new_folded_W:?}");

        let m_bn = scalar_module_as_bn::<C>(self.limb_width, self.limbs_count).unwrap();

        let new_folded_E = self.fold_E(
            region,
            w.folded_E.clone(),
            &w.cross_terms_commits,
            r.clone(),
            &m_bn,
        )?;
        debug!("fold: E folded: {new_folded_W:?}");

        let new_folded_u = gate.add(region, &w.folded_u, &r_value)?;
        debug!("fold: u folded: {new_folded_u:?}");

        let folded_consistency_markers = Self::fold_consistency_markers(
            region,
            &self.bn_chip,
            w.input_consistency_markers
                .clone()
                .map(|instance| instance.as_bn_limbs),
            w.folded_consistency_markers.clone(),
            &r.as_bn_limbs,
            &m_bn,
            self.limb_width,
        )
        .inspect_err(|err| error!("while fold consistency markers: {err:?}"))?;

        let new_folded_challenges = Self::fold_challenges(
            region,
            &self.bn_chip,
            w.input_challenges.clone(),
            w.folded_challenges.clone(),
            &r.as_bn_limbs,
            &m_bn,
            self.limb_width,
        )
        .inspect_err(|err| error!("while fold challenges: {err:?}"))?;
        debug!("fold: challenges folded: {new_folded_challenges:?}");

        let new_folded_instances = Self::fold_step_circuit_instances(
            region,
            self.config.clone(),
            &w.input_step_circuit_instances,
            &w.assigned_relaxed
                .folded_step_circuit_instances_hash_accumulator,
        )
        .inspect_err(|err| error!("while fold instances: {err:?}"))?;

        let assigned_result_of_fold = AssignedRelaxedPlonkInstance {
            folded_W: new_folded_W.clone(),
            folded_E: new_folded_E.clone(),
            folded_consistency_markers: folded_consistency_markers.clone(),
            folded_challenges: new_folded_challenges.clone(),
            folded_u: new_folded_u.clone(),
            folded_step_circuit_instances_hash_accumulator: new_folded_instances.clone(),
        };

        Ok(FoldResult {
            assigned_input: w,
            assigned_result_of_fold,
        })
    }

    /// Assign [FoldRelaxedPlonkInstanceChip::relaxed`]
    ///
    /// The advice columns from `config: &MainGateConfig` are used for assignment in cycle.
    pub fn assign_current_relaxed(
        &self,
        region: &mut RegionCtx<C::Base>,
    ) -> Result<AssignedRelaxedPlonkInstance<C, MARKERS_LEN>, Error> {
        let mut advice_columns_assigner = self.config.advice_cycle_assigner();

        macro_rules! assign_point {
            ($input:expr) => {{
                advice_columns_assigner.assign_next_advice_point(
                    region,
                    || stringify!($input),
                    $input,
                )
            }};
        }

        macro_rules! assign_diff_field {
            ($input:expr, $annot:expr) => {{
                assign_next_advice_from_diff_field::<C, _>(
                    &mut advice_columns_assigner,
                    region,
                    $input,
                    $annot,
                )
            }};
        }

        macro_rules! assign_diff_field_as_bn {
            ($input:expr, $annot:expr) => {{
                let assigned_cell = assign_diff_field!($input, $annot)?;

                let assigned_bn = self
                    .bn_chip
                    .from_assigned_value_to_limbs(region, &assigned_cell)?;

                Result::<_, Error>::Ok(assigned_bn)
            }};
        }

        let assigned_W = self
            .relaxed
            .W_commitments
            .iter()
            .map(|W| assign_point!(W))
            .collect::<Result<Vec<_>, _>>()?;
        let assigned_E = assign_point!(&self.relaxed.E_commitment)?;

        let consistency_markers = self.relaxed.get_consistency_markers();
        let assigned_consistency_markers = consistency_markers
            .iter()
            .map(|marker| assign_diff_field_as_bn!(marker, || "X0"))
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .unwrap();

        let assigned_challenges = self
            .relaxed
            .challenges
            .iter()
            .map(|challenge| assign_diff_field_as_bn!(challenge, || "one of challanges"))
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_u = assign_diff_field!(&self.relaxed.u, || "relaxed u")?;

        let assigned_step_circuit_instances =
            match self.relaxed.step_circuit_instances_hash_accumulator {
                SCInstancesHashAcc::None => SCInstancesHashAcc::None,
                SCInstancesHashAcc::Hash(hash) => {
                    SCInstancesHashAcc::Hash(assign_diff_field!(&hash, || {
                        "step_circuit_instances_hash_accumulator"
                    })?)
                }
            };

        Ok(AssignedRelaxedPlonkInstance {
            folded_W: assigned_W,
            folded_E: assigned_E,
            folded_u: assigned_u,
            folded_challenges: assigned_challenges,
            folded_consistency_markers: assigned_consistency_markers,
            folded_step_circuit_instances_hash_accumulator: assigned_step_circuit_instances,
        })
    }

    /// Assign all input arguments and generate challenge by random oracle circuit (`ro_circuit`)
    ///
    /// The advice columns from `config: &MainGateConfig` are used for assignment in cycle.
    /// The number of rows required for this depends on the input.
    pub fn assign_witness_with_challenge(
        &self,
        region: &mut RegionCtx<C::Base>,
        public_params_hash: &C,
        input_plonk: &FoldablePlonkInstance<C, MARKERS_LEN>,
        cross_term_commits: &[C],
        mut ro_circuit: impl ROCircuitTrait<C::Base>,
    ) -> Result<(AssignedWitness<C, MARKERS_LEN>, Vec<AssignedBit<C::Base>>), Error> {
        let mut advice_columns_assigner = self.config.advice_cycle_assigner();

        macro_rules! assign_and_absorb_point {
            ($input:expr) => {{
                let output = advice_columns_assigner.assign_next_advice_point(
                    region,
                    || stringify!($input),
                    $input,
                )?;

                ro_circuit.absorb_point([
                    WrapValue::Assigned(output.x.clone()),
                    WrapValue::Assigned(output.y.clone()),
                ]);

                Result::<_, Error>::Ok(output)
            }};
        }

        macro_rules! assign_and_absorb_diff_field {
            ($input:expr, $annot:expr) => {{
                let assigned: AssignedValue<C::Base> = assign_next_advice_from_diff_field::<C, _>(
                    &mut advice_columns_assigner,
                    region,
                    $input,
                    $annot,
                )?;

                ro_circuit.absorb_base(WrapValue::Assigned(assigned.clone()));

                Result::<_, Error>::Ok(assigned)
            }};
        }

        macro_rules! assign_and_absorb_diff_field_as_bn {
            ($input:expr, $annot:expr) => {{
                let assigned_cell = assign_and_absorb_diff_field!($input, $annot)?;

                region.next();
                let assigned_bn = self
                    .bn_chip
                    .from_assigned_value_to_limbs(region, &assigned_cell)?;

                Result::<_, Error>::Ok((assigned_cell, assigned_bn))
            }};
        }

        let assigned_public_params_hash = assign_and_absorb_point!(public_params_hash)?;

        let assigned_W = self
            .relaxed
            .W_commitments
            .iter()
            .map(|W| assign_and_absorb_point!(W))
            .collect::<Result<Vec<_>, _>>()?;

        let consistency_markers = self.relaxed.get_consistency_markers();
        let assigned_consistency_markers = consistency_markers
            .iter()
            .enumerate()
            .map(|(i, marker)| -> Result<_, Error> {
                Ok(assign_and_absorb_diff_field_as_bn!(marker, || format!("marker[{i}]"))?.1)
            })
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .unwrap();

        let assigned_challenges = self
            .relaxed
            .challenges
            .iter()
            .map(|challenge| {
                assign_and_absorb_diff_field_as_bn!(challenge, || "one of challanges")
                    .map(|bn| bn.1)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_u = assign_and_absorb_diff_field!(&self.relaxed.u, || "relaxed u")?;

        let assigned_E = assign_and_absorb_point!(&self.relaxed.E_commitment)?;

        let assigned_step_circuit_instances =
            match self.relaxed.step_circuit_instances_hash_accumulator {
                SCInstancesHashAcc::None => {
                    assign_and_absorb_diff_field!(&C::Base::ZERO, || {
                        "empty step_circuit_instances"
                    })?;
                    SCInstancesHashAcc::None
                }
                SCInstancesHashAcc::Hash(hash) => {
                    SCInstancesHashAcc::Hash(assign_and_absorb_diff_field!(&hash, || {
                        "step_circuit_instances"
                    })?)
                }
            };

        let assigned_relaxed = AssignedRelaxedPlonkInstance {
            folded_W: assigned_W,
            folded_E: assigned_E,
            folded_u: assigned_u,
            folded_challenges: assigned_challenges,
            folded_consistency_markers: assigned_consistency_markers,
            folded_step_circuit_instances_hash_accumulator: assigned_step_circuit_instances,
        };

        let assigned_instance_W_commitment_coordinates = input_plonk
            .W_commitments
            .iter()
            .map(|com| assign_and_absorb_point!(com))
            .collect::<Result<Vec<_>, _>>()?;

        let consistency_markers: [C::ScalarExt; MARKERS_LEN] =
            input_plonk.get_consistency_markers();

        let assigned_consistency_markers = consistency_markers
            .iter()
            .enumerate()
            .map(|(index, instance)| {
                let annot = format!("instance {index} value");
                assign_and_absorb_diff_field_as_bn!(instance, || annot.clone()).map(
                    |(as_value, as_limbs)| AssignedConsistencyMarkerView {
                        as_value,
                        as_bn_limbs: as_limbs,
                    },
                )
            })
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .expect("from array to array");

        let assigned_step_circuit_instances = input_plonk
            .get_step_circuit_instances()
            .iter()
            .flat_map(|instance| instance.iter().enumerate())
            .enumerate()
            .map(|(column_index, (row_index, instance))| {
                let annot = format!("instance[{column_index}][{row_index}] value");
                assign_and_absorb_diff_field!(instance, || annot.clone())
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_challanges_instance = input_plonk
            .challenges
            .iter()
            .enumerate()
            .map(|(index, challenge)| {
                let annot = format!("instance {index} value");
                assign_and_absorb_diff_field_as_bn!(challenge, || annot.clone()).map(|bn| bn.1)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_cross_term_commits = cross_term_commits
            .iter()
            .map(|cross_term_commit| assign_and_absorb_point!(cross_term_commit))
            .collect::<Result<Vec<_>, _>>()?;

        region.next();
        let r = ro_circuit.squeeze_n_bits(region, NUM_CHALLENGE_BITS)?;
        region.next();

        Ok((
            AssignedWitness {
                public_params_hash: assigned_public_params_hash,
                assigned_relaxed,
                input_challenges: assigned_challanges_instance,
                input_W_commitments: assigned_instance_W_commitment_coordinates,
                input_consistency_markers: assigned_consistency_markers,
                cross_terms_commits: assigned_cross_term_commits,
                input_step_circuit_instances: assigned_step_circuit_instances,
            },
            r,
        ))
    }
}

/// Fold [`RelaxedPlonkInstance::E_commitments`] & [`CrossTermCommits`]
///
/// # Description
///
/// This function is responsible for combining the current `folded_W` accumulator with
/// `cross_term_commits`. This is achieved through a scalar multiplication followed by
/// an elliptic curve addition. The scalar multiplication is defined by a random
/// scalar `r` in power of cross term commit index.
///
/// # Implementation Details
///
/// 1. **Multiplication & Conversion to bits**: Form a vector of degrees `r` and their representations as bits
/// 2. **Scalar Multiplication**: Each element of `cross_term_commits` is multiplied by power of random scalar
///    `r` (challenge) in bits representation. This is executed using the [`EccChip`] for elliptic curve operations.
/// 3. **Accumulation**: The result of the scalar multiplication is then added to the corresponding component in
///    the current `folded_E` accumulator. This is executed using the [`EccChip`] for elliptic curve operations.
///
/// ```markdown
/// new_folded_E = folded_E + Sum [ cross_term_commits[i] * (r ^ i) ]
/// ```
pub fn fold_E<const T: usize, C: CurveAffine>(
    region: &mut RegionCtx<C::Base>,
    bn_chip: &BigUintMulModChip<C::Base>,
    ecc_chip: &EccChip<C, MainGate<C::Base, T>>,
    folded_E: AssignedPoint<C>,
    cross_term_commits: &[AssignedPoint<C>],
    r: BigUintView<C::Base>,
    m_bn: &BigUint<C::Base>,
) -> Result<AssignedPoint<C>, Error>
where
    C::Base: PrimeFieldBits,
{
    debug!("Start calculate r^i from {r:?}");

    let powers_of_r = iter::successors(Some(Ok(r.clone())), |val| {
        Some(Ok(val.as_ref().ok()?).and_then(|r_pow_i| {
            let BigUintView {
                as_bn_limbs,
                as_bits: _,
            } = r_pow_i;

            let next = bn_chip
                .mult_mod(region, as_bn_limbs, &r.as_bn_limbs, m_bn)?
                .remainder;

            debug!("Next r^i from {next:?}");

            Result::<_, Error>::Ok(BigUintView {
                as_bits: bn_chip.to_le_bits(region, &next)?,
                as_bn_limbs: next,
            })
        }))
    })
    .take(cross_term_commits.len())
    .collect::<Result<Vec<_>, _>>()?;

    // TODO Check what with all commits
    let rT = cross_term_commits
        .iter()
        .zip(powers_of_r.into_iter())
        .map(|(commit, r_pow_i)| ecc_chip.scalar_mul(region, commit, &r_pow_i))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(rT.into_iter().try_fold(folded_E, |folded_E, rT_i| {
        ecc_chip.add(region, &folded_E, &rT_i)
    })?)
}

/// Fold `input` with `folded` in bn form
///
/// # Implementation Details
///
/// 1. Multiplies a part of the PLONK instance (`$input`) by a randomized value (`r_as_bn`),
///    and then takes the remainder modulo a specified modulus (`m_bn`).
/// 2. Sums this multiplication result with a pre-assigned part of the instance (`$folded`).
/// 3. Reduces the sum modulo the modulus (`m_bn`) to get the final folded value.
///
/// ```markdown
/// new_folded = folded + (input * r mod m) mod m
/// ```
///
/// # Notes
///
/// We call this function in the chip if we need to perform the fold on a `Scalar` field.
pub fn fold_via_biguint<F: PrimeField>(
    region: &mut RegionCtx<F>,
    bn_chip: &BigUintMulModChip<F>,
    input: &[AssignedValue<F>],
    folded: Vec<AssignedValue<F>>,
    m_bn: &BigUint<F>,
    r_as_bn: &[AssignedValue<F>],
    limb_width: NonZeroUsize,
) -> Result<Vec<AssignedValue<F>>, Error> {
    debug!(
        "fold: via bn input: input = {:?} folded = {:?}, r = {:?}",
        CellsValuesView::from(input),
        CellsValuesView::from(folded.as_slice()),
        CellsValuesView::from(r_as_bn)
    );
    // Multiply the part of the instance by the randomized value
    let part_mult_r = bn_chip
        .mult_mod(region, input, r_as_bn, m_bn)
        .inspect_err(|err| error!("while mult: input * r mod m: {err:?}"))?
        .remainder;
    debug!(
        "fold: mult mod: {:?}",
        CellsValuesView::from(part_mult_r.as_slice())
    );

    // Sum the multiplication result with the assigned part
    let part_mult_r_sum_part = bn_chip
        .assign_sum(
            region,
            &OverflowingBigUint::new(folded, limb_width),
            &part_mult_r,
        )?
        .res;

    debug!(
        "fold: assign_sum {:?}",
        CellsValuesView::from(part_mult_r_sum_part.cells.as_slice())
    );

    // Reduce the sum modulo the modulus
    Ok(bn_chip
        .red_mod(region, part_mult_r_sum_part, m_bn)?
        .remainder)
}

#[derive(Debug, Clone)]
pub struct BigUintView<F: Field> {
    pub as_bn_limbs: Vec<AssignedValue<F>>,
    pub as_bits: Vec<AssignedValue<F>>,
}
impl<F: Field> ops::Deref for BigUintView<F> {
    type Target = [AssignedValue<F>];

    fn deref(&self) -> &Self::Target {
        &self.as_bits
    }
}

fn scalar_module_as_bn<C: CurveAffine>(
    limb_width: NonZeroUsize,
    limbs_count: NonZeroUsize,
) -> Result<BigUint<C::Base>, big_uint::Error> {
    BigUint::<C::Base>::from_biguint(
        &num_bigint::BigUint::from_str_radix(
            <C::Scalar as PrimeField>::MODULUS.trim_start_matches("0x"),
            16,
        )
        .unwrap(),
        limb_width,
        limbs_count,
    )
}

fn scalar_module_as_limbs<C: CurveAffine>(
    limb_width: NonZeroUsize,
    limbs_count: NonZeroUsize,
) -> Result<Vec<C::Base>, big_uint::Error> {
    Ok(scalar_module_as_bn::<C>(limb_width, limbs_count)?
        .limbs()
        .to_vec())
}

fn assign_next_advice_from_diff_field<C: CurveAffine, AR: Into<String>>(
    assignor: &mut impl AdviceCyclicAssignor<C::Base>,
    region: &mut RegionCtx<C::Base>,
    input: &impl PrimeField,
    annotation: impl Fn() -> AR,
) -> Result<AssignedValue<C::Base>, Error> {
    let val: C::Base = util::fe_to_fe_safe(input).ok_or(Error::WhileScalarToBase {
        variable_name: annotation().into(),
        variable_str: format!("{:?}", input),
    })?;

    Ok(assignor.assign_next_advice(region, annotation, val)?)
}

pub struct FoldResult<C: CurveAffine, const MARKERS_LEN: usize = CONSISTENCY_MARKERS_COUNT> {
    pub(crate) assigned_input: AssignedWitness<C, MARKERS_LEN>,
    pub(crate) assigned_result_of_fold: AssignedRelaxedPlonkInstance<C, MARKERS_LEN>,
}

#[cfg(test)]
mod tests {
    use bitter::{BitReader, LittleEndianReader};
    use halo2_proofs::{
        circuit::{floor_planner::single_pass::SingleChipLayouter, Layouter, Value},
        plonk::ConstraintSystem,
    };
    use rand::{rngs::ThreadRng, Rng};
    use tracing_test::traced_test;

    use super::*;
    use crate::{
        commitment::CommitmentKey,
        ff::Field,
        halo2curves::{bn256::G1Affine as C1, CurveAffine},
        nifs::sangria::{self, VanillaFS, CONSISTENCY_MARKERS_COUNT},
        plonk::PlonkInstance,
        poseidon::{poseidon_circuit::PoseidonChip, PoseidonHash, ROTrait, Spec},
        table::WitnessCollector,
        util::ScalarToBase,
    };

    type Base = <C1 as CurveAffine>::Base;
    type ScalarExt = <C1 as CurveAffine>::ScalarExt;

    const T: usize = 6;
    const NUM_WITNESS: usize = 5;
    const NUM_MARKERS: usize = CONSISTENCY_MARKERS_COUNT;
    const NUM_INSTANCES: usize = 10;
    const NUM_CHALLENGES: usize = 5;
    /// When the number of fold rounds increases, `K` must be increased too
    /// as the number of required rows in the table grows.
    const NUM_OF_FOLD_ROUNDS: usize = 3;
    /// 2 ^ K is count of table rows in [`TableData`]
    const K: u32 = 21;

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(64) };
    const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    fn get_witness_collector() -> (WitnessCollector<Base>, MainGateConfig<T>) {
        let mut cs = ConstraintSystem::default();
        let config = MainGate::<Base, T>::configure(&mut cs);
        let witness = WitnessCollector {
            instances: vec![vec![]],
            advice: vec![vec![Base::ZERO.into(); 1 << K]; cs.num_advice_columns()],
        };

        (witness, config)
    }

    fn random_curve_vec(mut rnd: impl Rng) -> Vec<C1> {
        iter::repeat_with(|| C1::random(&mut rnd))
            .take(NUM_WITNESS)
            .collect::<Vec<_>>()
    }

    fn assign_curve_points<C, const T: usize>(
        ctx: &mut RegionCtx<C::Base>,
        ecc: &EccChip<C, MainGate<C::Base, T>>,
        points: &[C],
        var_prefix: &str,
    ) -> Result<Vec<AssignedPoint<C>>, halo2_proofs::plonk::Error>
    where
        C: CurveAffine,
        C::Base: PrimeFieldBits + FromUniformBytes<64>,
    {
        points
            .iter()
            .enumerate()
            .map(|(i, point)| ecc.assign_from_curve(ctx, || format!("{var_prefix}[{i}]"), point))
            .collect()
    }

    /// The test utility struct
    /// It provides a convenient setup for testing the functionality of `FoldRelaxedPlonkInstanceChip`.
    /// Includes configured table data, a main gate config, random number generator, ECC and gate chips, and a random scalar.
    /// Used for setting up test scenarios, generating random inputs, and initializing necessary components for testing etc
    struct Fixture {
        ws: WitnessCollector<Base>,
        config: MainGateConfig<T>,
        rnd: ThreadRng,
        ecc: EccChip<C1, MainGate<Base, T>>,
        gate: MainGate<Base, T>,
        r: ScalarExt,
    }

    impl Default for Fixture {
        fn default() -> Self {
            let (ws, config) = get_witness_collector();
            let mut rnd = rand::thread_rng();

            Self {
                ws,
                r: ScalarExt::from_u128(rnd.gen()),
                ecc: EccChip::<C1, MainGate<Base, T>>::new(config.clone()),
                gate: MainGate::new(config.clone()),
                config,
                rnd,
            }
        }
    }

    fn generate_random_plonk_instance(mut rnd: &mut ThreadRng) -> FoldablePlonkInstance<C1> {
        // 'allow' is necessary, because otherwise the closure captures rnd and we have to copy it
        #[allow(clippy::needless_borrows_for_generic_args)]
        FoldablePlonkInstance::new(PlonkInstance {
            W_commitments: iter::repeat_with(|| C1::random(&mut rnd))
                .take(NUM_WITNESS)
                .collect(),
            instances: iter::once(
                iter::repeat_with(|| ScalarExt::random(&mut rnd))
                    .take(NUM_MARKERS)
                    .collect_vec(),
            )
            .chain(
                iter::repeat_with(|| ScalarExt::random(&mut rnd))
                    .chunks(10)
                    .into_iter()
                    .take(NUM_INSTANCES)
                    .map(|ch| ch.into_iter().collect_vec())
                    .collect_vec(),
            )
            .collect_vec(),
            challenges: iter::repeat_with(|| ScalarExt::random(&mut rnd))
                .take(NUM_CHALLENGES)
                .collect(),
        })
        .unwrap()
    }

    #[traced_test]
    #[test]
    fn generate_challenge() {
        let mut rnd = rand::thread_rng();

        let relaxed = RelaxedPlonkInstance::from(generate_random_plonk_instance(&mut rnd));

        let (mut ws, config) = get_witness_collector();

        let chip =
            FoldRelaxedPlonkInstanceChip::<T, C1, { sangria::CONSISTENCY_MARKERS_COUNT }>::new(
                relaxed.clone(),
                LIMB_WIDTH,
                LIMBS_COUNT,
                config.clone(),
            );

        let mut layouter = SingleChipLayouter::new(&mut ws, vec![]).unwrap();

        let spec = Spec::<Base, T, 5>::new(10, 10);

        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let plonk = generate_random_plonk_instance(&mut rnd);
            let cross_term_commits = random_curve_vec(&mut rnd);
            let pp_hash = C1::random(&mut rnd);

            let on_circuit_challenge = layouter
                .assign_region(
                    || "assign_witness_with_challenge",
                    |region| {
                        let assigned_witness = chip
                            .assign_witness_with_challenge(
                                &mut RegionCtx::new(region, 0),
                                &pp_hash,
                                &plonk,
                                &cross_term_commits,
                                PoseidonChip::new(config.clone(), spec.clone()),
                            )
                            .unwrap();
                        Ok(assigned_witness)
                    },
                )
                .unwrap()
                .1
                .iter()
                .map(|cell| cell.value().unwrap().copied().unwrap())
                .map(|bit| match bit {
                    Base::ONE => true,
                    Base::ZERO => false,
                    _ => unreachable!("only bits here"),
                })
                .collect::<Vec<bool>>();

            let off_circuit_challenge = {
                let challenge = generate_off_circuit_challenge(
                    &spec,
                    pp_hash,
                    &relaxed,
                    &plonk,
                    &cross_term_commits,
                )
                .to_repr()
                .as_ref()
                .to_vec();

                let mut reader = LittleEndianReader::new(&challenge);
                iter::repeat_with(|| reader.read_bit())
                    .map_while(|mut b| b.take())
                    .take(NUM_CHALLENGE_BITS.into())
                    .collect::<Vec<_>>()
            };

            assert_eq!(off_circuit_challenge.len(), on_circuit_challenge.len());
            assert_eq!(off_circuit_challenge, on_circuit_challenge);
        }
    }

    #[traced_test]
    #[test]
    fn fold_W_test() {
        let Fixture {
            mut ws,
            config,
            mut rnd,
            ecc,
            gate,
            r,
        } = Fixture::default();

        let mut folded_W = vec![CommitmentKey::<C1>::default_value(); NUM_WITNESS];

        let mut layouter = SingleChipLayouter::new(&mut ws, vec![]).unwrap();

        let mut plonk = RelaxedPlonkInstance::<C1>::new(0, NUM_WITNESS, 0);

        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let input_W = random_curve_vec(&mut rnd);

            let on_circuit_W_cell = layouter.assign_region(
                || "fold W test",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let folded = assign_curve_points(&mut ctx, &ecc, &folded_W, "folded_W")?;
                    let input = assign_curve_points(&mut ctx, &ecc, &input_W, "input_W")?;

                    let assigned_r = ctx.assign_advice(
                        || "r",
                        config.state[0],
                        Value::known(C1::scalar_to_base(&r).unwrap()),
                    )?;

                    let r = gate.le_num_to_bits(&mut ctx, assigned_r, NUM_CHALLENGE_BITS)?;

                    Ok(FoldRelaxedPlonkInstanceChip::<
                            T,
                            C1,
                            { sangria::CONSISTENCY_MARKERS_COUNT },
                        >::fold_W(&mut ctx, &config, &folded, &input, &r)
                        .unwrap())
                },
            );

            assert_eq!(plonk.W_commitments, folded_W);

            plonk = plonk.fold(
                &FoldablePlonkInstance::new(PlonkInstance {
                    W_commitments: input_W.clone(),
                    instances: vec![vec![ScalarExt::ZERO, ScalarExt::ZERO]],
                    challenges: vec![],
                })
                .unwrap(),
                &[],
                &r,
            );

            let off_circuit_W = plonk
                .W_commitments
                .iter()
                .map(|c| {
                    let coordinates = c.coordinates().unwrap();
                    (*coordinates.x(), *coordinates.y())
                })
                .collect::<Vec<_>>();

            let on_circuit_W_cell = on_circuit_W_cell
                .unwrap()
                .into_iter()
                .map(|c| c.coordinates_values().unwrap())
                .collect::<Vec<_>>();

            assert_eq!(off_circuit_W, on_circuit_W_cell);

            folded_W.clone_from(&plonk.W_commitments);
        }
    }

    #[traced_test]
    #[test]
    fn fold_E_test() {
        let Fixture {
            mut ws,
            config,
            mut rnd,
            ecc,
            gate,
            r,
        } = Fixture::default();

        let mut folded_E = C1::default();

        let mut layouter = SingleChipLayouter::new(&mut ws, vec![]).unwrap();

        let mut plonk = RelaxedPlonkInstance::<C1>::new(0, 0, 0);

        let chip =
            FoldRelaxedPlonkInstanceChip::<T, C1, { sangria::CONSISTENCY_MARKERS_COUNT }>::new(
                RelaxedPlonkInstance::new(0, 0, 0),
                LIMB_WIDTH,
                LIMBS_COUNT,
                config.clone(),
            );

        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let cross_term_commits = random_curve_vec(&mut rnd);

            let on_circuit_E_cell = layouter.assign_region(
                || "fold E test",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let folded_E = ecc.assign_from_curve(&mut ctx, || "folded_E", &folded_E)?;
                    let cross_term_commits =
                        assign_curve_points(&mut ctx, &ecc, &cross_term_commits, "input_W")?;

                    let assigned_r = ctx.assign_advice(
                        || "r",
                        config.state[0],
                        Value::known(C1::scalar_to_base(&r).unwrap()),
                    )?;

                    let r =
                        gate.le_num_to_bits(&mut ctx, assigned_r.clone(), NUM_CHALLENGE_BITS)?;
                    let r_vv = BigUintView {
                        as_bn_limbs: chip
                            .bn_chip
                            .from_assigned_value_to_limbs(&mut ctx, &assigned_r)
                            .unwrap(),
                        as_bits: r,
                    };

                    let m_bn = scalar_module_as_bn::<C1>(LIMB_WIDTH, LIMBS_COUNT).unwrap();

                    Ok(chip
                        .fold_E(&mut ctx, folded_E, &cross_term_commits, r_vv, &m_bn)
                        .unwrap())
                },
            );

            assert_eq!(plonk.E_commitment, folded_E);

            plonk = plonk.fold(
                &FoldablePlonkInstance::new(PlonkInstance {
                    W_commitments: vec![],
                    instances: vec![vec![ScalarExt::ONE, ScalarExt::ONE]],
                    challenges: vec![],
                })
                .unwrap(),
                &cross_term_commits,
                &r,
            );

            let off_circuit_E_coordinates = plonk.E_commitment.coordinates().unwrap();
            let off_circuit_E_x = *off_circuit_E_coordinates.x();
            let off_circuit_E_y = *off_circuit_E_coordinates.y();

            let (on_circuit_E_cell_x, on_circuit_E_cell_y) =
                on_circuit_E_cell.unwrap().coordinates_values().unwrap();

            assert_eq!(off_circuit_E_x, on_circuit_E_cell_x);
            assert_eq!(off_circuit_E_y, on_circuit_E_cell_y);

            folded_E = plonk.E_commitment;
        }
    }

    #[traced_test]
    #[test]
    fn fold_consistency_markers_test() {
        let Fixture {
            mut ws,
            config,
            mut rnd,
            r,
            ..
        } = Fixture::default();

        let mut layouter = SingleChipLayouter::new(&mut ws, vec![]).unwrap();

        let mut relaxed_plonk = RelaxedPlonkInstance::<C1>::new(0, 0, 0);

        let bn_chip = BigUintMulModChip::<Base>::new(
            config
                .into_smaller_size::<{ big_uint_mul_mod_chip::MAIN_GATE_T }>()
                .unwrap(),
            LIMB_WIDTH,
            LIMBS_COUNT,
        );

        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let consistency_marker = [ScalarExt::random(&mut rnd), ScalarExt::random(&mut rnd)];

            let on_circuit_instances_cell = layouter.assign_region(
                || "fold instances test",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let mut advice_columns_assigner = config.advice_cycle_assigner();

                    macro_rules! assign_scalar_as_bn {
                        ($region:expr, $input:expr, $annotation_prefix:expr) => {{
                            advice_columns_assigner.assign_all_advice(
                                $region,
                                || $annotation_prefix,
                                BigUint::from_f(
                                    &util::fe_to_fe_safe::<_, Base>($input).unwrap(),
                                    LIMB_WIDTH,
                                    LIMBS_COUNT,
                                )
                                .unwrap()
                                .limbs()
                                .iter()
                                .map(|limb| {
                                    util::fe_to_fe_safe(limb)
                                        .ok_or(Error::WhileScalarToBase {
                                            variable_name: $annotation_prefix,
                                            variable_str: format!("{limb:?}"),
                                        })
                                        .unwrap()
                                }),
                            )
                        }};
                    }

                    let assigned_r = advice_columns_assigner
                        .assign_next_advice(&mut ctx, || "r", C1::scalar_to_base(&r).unwrap())
                        .unwrap();

                    let assigned_consistency_markers = relaxed_plonk
                        .get_consistency_markers()
                        .iter()
                        .map(|instance| {
                            assign_scalar_as_bn!(&mut ctx, instance, "folded instance".to_owned())
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .try_into()
                        .unwrap();

                    let assigned_input_instance = consistency_marker
                        .iter()
                        .map(|instance| {
                            assign_scalar_as_bn!(&mut ctx, instance, "input instance".to_owned())
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .try_into()
                        .unwrap();

                    let m_bn = scalar_module_as_bn::<C1>(LIMB_WIDTH, LIMBS_COUNT).unwrap();

                    ctx.next();

                    let r_as_bn = bn_chip
                        .from_assigned_value_to_limbs(&mut ctx, &assigned_r)
                        .unwrap();

                    Ok(FoldRelaxedPlonkInstanceChip::<
                            T,
                            C1,
                            { sangria::CONSISTENCY_MARKERS_COUNT },
                        >::fold_consistency_markers(
                            &mut ctx,
                            &bn_chip,
                            assigned_input_instance,
                            assigned_consistency_markers,
                            &r_as_bn,
                            &m_bn,
                            LIMB_WIDTH,
                        )
                        .unwrap())
                },
            );

            relaxed_plonk = relaxed_plonk.fold(
                &FoldablePlonkInstance::new(PlonkInstance {
                    W_commitments: vec![],
                    instances: vec![consistency_marker.to_vec()],
                    challenges: vec![],
                })
                .unwrap(),
                &[],
                &r,
            );

            let off_circuit_instances = relaxed_plonk
                .get_consistency_markers()
                .iter()
                .map(|instance| {
                    BigUint::from_f(
                        &util::fe_to_fe_safe::<ScalarExt, Base>(instance).unwrap(),
                        LIMB_WIDTH,
                        LIMBS_COUNT,
                    )
                    .unwrap()
                    .limbs()
                    .to_vec()
                })
                .collect::<Vec<_>>();

            let on_circuit_instances = on_circuit_instances_cell
                .unwrap()
                .into_iter()
                .map(|c| {
                    c.into_iter()
                        .map(|cell| *cell.value().unwrap().unwrap())
                        .collect::<Vec<Base>>()
                })
                .collect::<Vec<Vec<Base>>>();

            assert_eq!(off_circuit_instances, on_circuit_instances);
        }
    }

    #[traced_test]
    #[test]
    fn fold_challenges_test() {
        let Fixture {
            mut ws,
            config,
            mut rnd,
            r,
            ..
        } = Fixture::default();

        let mut layouter = SingleChipLayouter::new(&mut ws, vec![]).unwrap();

        let mut relaxed_plonk = RelaxedPlonkInstance::<C1>::new(NUM_CHALLENGES, 0, 0);

        let bn_chip = BigUintMulModChip::<Base>::new(
            config
                .into_smaller_size::<{ big_uint_mul_mod_chip::MAIN_GATE_T }>()
                .unwrap(),
            LIMB_WIDTH,
            LIMBS_COUNT,
        );

        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let input_challenges = iter::repeat_with(|| ScalarExt::random(&mut rnd))
                .take(NUM_CHALLENGES)
                .collect::<Vec<_>>();

            // Run twice for setup & real run
            let on_circuit_challanges_cell = layouter.assign_region(
                || "fold challenges test",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let mut advice_columns_assigner = config.advice_cycle_assigner();

                    macro_rules! assign_scalar_as_bn {
                        ($region:expr, $input:expr, $annotation_prefix:expr) => {{
                            advice_columns_assigner.assign_all_advice(
                                $region,
                                || $annotation_prefix,
                                BigUint::from_f(
                                    &util::fe_to_fe_safe::<_, Base>($input).unwrap(),
                                    LIMB_WIDTH,
                                    LIMBS_COUNT,
                                )
                                .unwrap()
                                .limbs()
                                .iter()
                                .map(|limb| {
                                    util::fe_to_fe_safe(limb)
                                        .ok_or(Error::WhileScalarToBase {
                                            variable_name: $annotation_prefix,
                                            variable_str: format!("{limb:?}"),
                                        })
                                        .unwrap()
                                }),
                            )
                        }};
                    }

                    let assigned_r = advice_columns_assigner
                        .assign_next_advice(&mut ctx, || "r", C1::scalar_to_base(&r).unwrap())
                        .unwrap();

                    let assigned_fold_challenges = relaxed_plonk
                        .challenges
                        .iter()
                        .map(|instance| {
                            assign_scalar_as_bn!(&mut ctx, instance, "folded instance".to_owned())
                        })
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();

                    let assigned_input_instance = input_challenges
                        .iter()
                        .map(|instance| {
                            assign_scalar_as_bn!(&mut ctx, instance, "input instance".to_owned())
                        })
                        .collect::<Result<Vec<_>, _>>()?;

                    ctx.next();

                    let r_as_bn = bn_chip
                        .from_assigned_value_to_limbs(&mut ctx, &assigned_r)
                        .unwrap();

                    let m_bn = scalar_module_as_bn::<C1>(LIMB_WIDTH, LIMBS_COUNT).unwrap();

                    Ok(FoldRelaxedPlonkInstanceChip::<
                            T,
                            C1,
                            { sangria::CONSISTENCY_MARKERS_COUNT },
                        >::fold_challenges(
                            &mut ctx,
                            &bn_chip,
                            assigned_input_instance,
                            assigned_fold_challenges,
                            &r_as_bn,
                            &m_bn,
                            LIMB_WIDTH,
                        )
                        .unwrap())
                },
            );

            relaxed_plonk = relaxed_plonk.fold(
                &FoldablePlonkInstance::new(PlonkInstance {
                    W_commitments: vec![],
                    instances: vec![vec![ScalarExt::ONE, ScalarExt::ONE]],
                    challenges: input_challenges.to_vec(),
                })
                .unwrap(),
                &[],
                &r,
            );

            let off_circuit_challenges = relaxed_plonk
                .challenges
                .iter()
                .map(|instance| {
                    BigUint::from_f(
                        &C1::scalar_to_base(instance).unwrap(),
                        LIMB_WIDTH,
                        LIMBS_COUNT,
                    )
                    .unwrap()
                    .limbs()
                    .to_vec()
                })
                .collect::<Vec<_>>();

            let on_circuit_challenges = on_circuit_challanges_cell
                .unwrap()
                .into_iter()
                .map(|c| {
                    c.into_iter()
                        .map(|cell| *cell.value().unwrap().unwrap())
                        .collect::<Vec<Base>>()
                })
                .collect::<Vec<Vec<Base>>>();

            assert_eq!(off_circuit_challenges, on_circuit_challenges);
        }
    }

    #[traced_test]
    #[test]
    fn fold_all() {
        const T: usize = 6;

        let Fixture {
            mut ws,
            config,
            mut rnd,
            ..
        } = Fixture::default();
        let mut layouter = SingleChipLayouter::new(&mut ws, vec![]).unwrap();

        let spec = Spec::<Base, T, { T - 1 }>::new(10, 10);

        let mut relaxed = RelaxedPlonkInstance::new(NUM_CHALLENGES, NUM_WITNESS, NUM_INSTANCES);

        let pp_hash = C1::random(&mut rnd);
        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let input_plonk = generate_random_plonk_instance(&mut rnd);
            let cross_term_commits = random_curve_vec(&mut rnd);

            let on_circuit_relaxed = layouter
                .assign_region(
                    || "fold",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        let chip = FoldRelaxedPlonkInstanceChip::<
                            T,
                            C1,
                            { sangria::CONSISTENCY_MARKERS_COUNT },
                        >::new(
                            relaxed.clone(), LIMB_WIDTH, LIMBS_COUNT, config.clone()
                        );

                        let (w, r) = chip.assign_witness_with_challenge(
                            &mut region,
                            &pp_hash,
                            &input_plonk,
                            &cross_term_commits,
                            PoseidonChip::new(config.clone(), spec.clone()),
                        )?;

                        Ok(chip.fold(&mut region, w, r).unwrap())
                    },
                )
                .unwrap()
                .assigned_result_of_fold
                .to_relaxed_plonk_instance(LIMB_WIDTH, LIMBS_COUNT)
                .unwrap()
                .unwrap();

            let off_circuit_r = generate_off_circuit_challenge(
                &spec,
                pp_hash,
                &relaxed,
                &input_plonk,
                &cross_term_commits,
            );
            debug!("sangria off-circuir r: {off_circuit_r:?}");

            relaxed = relaxed.fold(&input_plonk, &cross_term_commits, &off_circuit_r);

            assert_eq!(on_circuit_relaxed, relaxed);
        }
    }

    fn generate_off_circuit_challenge(
        spec: &Spec<Base, T, { T - 1 }>,
        pp_hash: C1,
        relaxed: &RelaxedPlonkInstance<C1>,
        input: &PlonkInstance<C1>,
        cross_term_commits: &[C1],
    ) -> ScalarExt {
        const K: usize = 5;

        let mut ro = PoseidonHash::new(spec.clone());

        let pp_hash = pp_hash.coordinates().map(|c| (*c.x(), *c.y())).unwrap();

        VanillaFS::generate_challenge(&pp_hash, &mut ro, relaxed, input, cross_term_commits)
            .unwrap()
    }
}
