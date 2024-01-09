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

use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use halo2_proofs::circuit::{AssignedCell, Value};
use halo2curves::{Coordinates, CurveAffine};
use itertools::Itertools;
use log::*;
use num_traits::Num;

use crate::{
    constants::NUM_CHALLENGE_BITS,
    gadgets::{
        ecc::{AssignedPoint, EccChip},
        nonnative::bn::{
            big_uint::{self, BigUint},
            big_uint_mul_mod_chip::{self, BigUintMulModChip, OverflowingBigUint},
        },
    },
    main_gate::{AssignedBit, AssignedValue, MainGate, MainGateConfig, RegionCtx, WrapValue},
    nifs::CrossTermCommits,
    plonk::{PlonkInstance, RelaxedPlonkInstance},
    poseidon::ROCircuitTrait,
    util,
};

pub(crate) struct FoldRelaxedPlonkInstanceChip<C: CurveAffine>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    W: Vec<C>,
    E: C,
    u: C::ScalarExt,
    challenges: Vec<BigUint<C::ScalarExt>>,
    X0: BigUint<C::ScalarExt>,
    X1: BigUint<C::ScalarExt>,

    limb_width: NonZeroUsize,
    limbs_count: NonZeroUsize,
}

/// Holds the assigned values and points resulting from the folding process.
pub(crate) struct AssignedWitness<C: CurveAffine> {
    /// Assigned value of the public parameters commitment.
    /// Sourced directly from the `public_params_hash` argument of [`FoldRelaxedPlonkInstanceChip::fold`].
    public_params_hash: AssignedValue<C::Base>,

    /// Assigned point representing the folded accumulator W.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::W`]
    folded_W: Vec<AssignedPoint<C>>,

    /// Assigned point representing the folded accumulator E.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::E`]
    folded_E: AssignedPoint<C>,

    /// Assigned value of the folded scalar u.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::u`]
    folded_u: AssignedValue<C::Base>,

    /// Vector of vectors of assigned values for each limb of the folded challenges.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::challenges`].
    folded_challenges: Vec<Vec<AssignedValue<C::Base>>>,

    /// Vector of assigned values for each limb of the folded big number X0.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::X0`]
    folded_X0: Vec<AssignedValue<C::Base>>,

    /// Vector of assigned values for each limb of the folded big number X1.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::X1`]
    folded_X1: Vec<AssignedValue<C::Base>>,

    /// Assigned point representing the commitment to the `W` value of the input PLONK instance.
    /// Sourced directly from [`PlonkInstance::W_commitments`] provided to [`FoldRelaxedPlonkInstanceChip::fold`].
    input_W_commitments: Vec<AssignedPoint<C>>,

    /// Vector of vectors of assigned values for each limb of the input instances.
    /// Sourced directly from [`PlonkInstance::instance`] provided to [`FoldRelaxedPlonkInstanceChip::fold`].
    input_instances: Vec<Vec<AssignedValue<C::Base>>>,

    /// Vector of vectors of assigned values for each limb of the input challenges.
    /// Sourced directly from [`PlonkInstance::challenges`] provided to [`FoldRelaxedPlonkInstanceChip::fold`].
    input_challenges: Vec<Vec<AssignedValue<C::Base>>>,

    /// Vector of assigned points representing the commitments to the cross terms.
    /// Sourced directly from the `cross_term_commits` argument of [`FoldRelaxedPlonkInstanceChip::fold`].
    cross_terms_commits: Vec<AssignedPoint<C>>,

    /// Vector of assigned values representing the modulus in big number form.
    ///
    /// Field modulus from another curve within the IVC scheme
    /// Derived internally within the [`FoldRelaxedPlonkInstanceChip::fold`] method.
    m_bn: Vec<AssignedValue<C::Base>>,

    /// Vector of assigned bits representing the challenge `r`.
    /// Generated by [`ROCircuitTrait`] provided into [`FoldRelaxedPlonkInstanceChip::fold`] method.
    /// All params in this structure used as part of seeds for generate this challenge
    r: Vec<AssignedBit<C::Base>>,
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
        variable_name: &'static str,
        variable_str: String,
    },

    #[error("Error converting scalar to base field element for {variable_name}: {variable_str}")]
    WhileScalarToBase {
        variable_name: &'static str,
        variable_str: String,
    },
}

impl<C: CurveAffine> FoldRelaxedPlonkInstanceChip<C>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new_default(
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
        num_challenges: usize,
        num_witness: usize,
    ) -> Self {
        Self {
            W: vec![C::default(); num_witness],
            E: C::default(),
            u: C::Scalar::ZERO,
            challenges: iter::repeat_with(|| BigUint::zero(limb_width))
                .take(num_challenges)
                .collect(),
            X0: BigUint::zero(limb_width),
            X1: BigUint::zero(limb_width),
            limb_width,
            limbs_count,
        }
    }

    pub fn from_instance(
        plonk_instance: PlonkInstance<C>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        Ok(Self {
            W: plonk_instance.W_commitments.clone(),
            E: C::default(),
            u: C::Scalar::ONE,
            challenges: plonk_instance
                .challenges
                .iter()
                .map(|ch| BigUint::from_f(ch, limb_width, limbs_count))
                .collect::<Result<Vec<_>, _>>()?,
            X0: BigUint::from_f(&plonk_instance.instance[0], limb_width, limbs_count)?,
            X1: BigUint::from_f(&plonk_instance.instance[1], limb_width, limbs_count)?,
            limb_width,
            limbs_count,
        })
    }

    pub fn from_relaxed(
        relaxed: RelaxedPlonkInstance<C>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        Ok(Self {
            W: relaxed.W_commitments.clone(),
            E: relaxed.E_commitment,
            u: relaxed.u,
            challenges: relaxed
                .challenges
                .iter()
                .map(|ch| BigUint::from_f(ch, limb_width, limbs_count))
                .collect::<Result<Vec<_>, _>>()?,
            X0: BigUint::from_f(&relaxed.instance[0], limb_width, limbs_count)?,
            X1: BigUint::from_f(&relaxed.instance[1], limb_width, limbs_count)?,
            limb_width,
            limbs_count,
        })
    }

    /// Fold with proof [`RelaxedPlonkInstance::W_commitments`] & [`PlonkInstance::W_commitments`]
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
    fn fold_W<const T: usize>(
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        folded_W: &[AssignedPoint<C>],
        input_W_commitments: &[AssignedPoint<C>],
        r: &[AssignedCell<C::Base, C::Base>],
    ) -> Result<Vec<AssignedPoint<C>>, Error> {
        let ecc = EccChip::<C, C::Base, T>::new(config.clone());

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

    /// Fold with proof [`RelaxedPlonkInstance::E_commitments`] & [`CrossTermCommits`]
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
    /// new_folded_E[i] = folded_E[i] + cross_term_commits[i] * (r ^ i)
    /// ```
    fn fold_E<const T: usize>(
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        bn_chip: &BigUintMulModChip<C::Base>,
        folded_E: AssignedPoint<C>,
        cross_term_commits: &[AssignedPoint<C>],
        r: BigUintView<C::Base>,
        m_bn: &[AssignedValue<C::Base>],
    ) -> Result<AssignedPoint<C>, Error> {
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

        let ecc = EccChip::<C, C::Base, T>::new(config.clone());
        // TODO Check what with all commits
        let rT = cross_term_commits
            .iter()
            .zip(powers_of_r.into_iter())
            .map(|(commit, r_pow_i)| ecc.scalar_mul(region, commit, &r_pow_i))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(rT
            .into_iter()
            .try_fold(folded_E, |folded_E, rT_i| ecc.add(region, &folded_E, &rT_i))?)
    }

    // TODO #32 rustdoc
    /// 1. Multiplies a part of the PLONK instance (`$input`) by a randomized value (`r_as_bn`),
    ///    and then takes the remainder modulo a specified modulus (`m_bn`).
    /// 2. Sums this multiplication result with a pre-assigned part of the instance (`$folded`).
    /// 3. Reduces the sum modulo the modulus (`m_bn`) to get the final folded value.
    fn fold_via_biguint(
        bn_chip: &BigUintMulModChip<C::Base>,
        region: &mut RegionCtx<C::Base>,
        input: &[AssignedValue<C::Base>],
        folded: Vec<AssignedValue<C::Base>>,
        m_bn: &[AssignedValue<C::Base>],
        r_as_bn: &[AssignedValue<C::Base>],
        limb_width: NonZeroUsize,
    ) -> Result<Vec<AssignedCell<C::Base, C::Base>>, Error> {
        // Multiply the part of the instance by the randomized value
        let part_mult_r = bn_chip.mult_mod(region, input, r_as_bn, m_bn)?.remainder;
        debug!("fold: mult mod: {}", part_mult_r.len());

        // Sum the multiplication result with the assigned part
        let part_mult_r_sum_part = bn_chip
            .assign_sum(
                region,
                &OverflowingBigUint::new(folded, limb_width),
                &part_mult_r,
            )?
            .res;
        debug!("fold: assign_sum {}", part_mult_r_sum_part.cells.len());

        // Reduce the sum modulo the modulus
        Ok(bn_chip
            .red_mod(region, part_mult_r_sum_part, m_bn)?
            .remainder)
    }

    // TODO #32 rustdoc
    fn fold_instances(
        bn_chip: &BigUintMulModChip<C::Base>,
        region: &mut RegionCtx<C::Base>,
        input_instances: [Vec<AssignedValue<C::Base>>; 2],
        folded_instances: [Vec<AssignedValue<C::Base>>; 2],
        r_as_bn: &[AssignedCell<C::Base, C::Base>],
        m_bn: &[AssignedCell<C::Base, C::Base>],
        limb_width: NonZeroUsize,
    ) -> Result<[Vec<AssignedCell<C::Base, C::Base>>; 2], Error> {
        let [input_X0, input_X1] = input_instances;
        let [folded_X0, folded_X1] = folded_instances;

        let new_folded_X0 = Self::fold_via_biguint(
            bn_chip, region, &input_X0, folded_X0, m_bn, r_as_bn, limb_width,
        )?;
        debug!("fold: X0 folded: {new_folded_X0:?}");

        let new_folded_X1 = Self::fold_via_biguint(
            bn_chip, region, &input_X1, folded_X1, m_bn, r_as_bn, limb_width,
        )?;
        debug!("fold: X1 folded: {new_folded_X1:?}");

        Ok([new_folded_X0, new_folded_X1])
    }

    // TODO #32 rustdoc
    fn fold_challenges(
        bn_chip: &BigUintMulModChip<C::Base>,
        region: &mut RegionCtx<C::Base>,
        folded_challenges: Vec<Vec<AssignedValue<C::Base>>>,
        input_challenges: Vec<Vec<AssignedValue<C::Base>>>,
        r_as_bn: &[AssignedValue<C::Base>],
        m_bn: &[AssignedValue<C::Base>],
        limb_width: NonZeroUsize,
    ) -> Result<Vec<Vec<AssignedValue<C::Base>>>, Error> {
        folded_challenges
            .into_iter()
            .zip_eq(input_challenges)
            .map(|(folded_challenge, input_challange)| {
                Self::fold_via_biguint(
                    bn_chip,
                    region,
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
    pub fn fold<const T: usize>(
        self,
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        ro_circuit: impl ROCircuitTrait<C::Base>,
        public_params_hash: &C::Base,
        input_plonk: &PlonkInstance<C>,
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<Option<Self>, Error> {
        assert!(T >= 4); // TODO remaster, if possible

        let AssignedWitness {
            public_params_hash: _, // TODO Check don't use in scheme
            folded_W,
            folded_E,
            folded_u,
            folded_X0,
            folded_X1,
            input_W_commitments,
            input_instances,
            input_challenges,
            folded_challenges,
            cross_terms_commits,
            r,
            m_bn,
        } = self.assign_witness_with_challenge(
            region,
            config,
            ro_circuit,
            public_params_hash,
            input_plonk,
            cross_term_commits,
        )?;

        debug!("fold: Assigned & Generated challenge: {r:?}");

        let gate = MainGate::new(config.clone());

        let bn_chip = BigUintMulModChip::<C::Base>::new(
            config
                .into_smaller_size::<{ big_uint_mul_mod_chip::MAIN_GATE_T }>()
                .unwrap(),
            self.limb_width,
            self.limbs_count,
        );

        let r_value = gate.le_bits_to_num(region, &r)?;
        let r = BigUintView {
            as_bn_limbs: bn_chip.from_assigned_cell_to_limbs(region, &r_value)?,
            as_bits: r,
        };

        let new_folded_W = Self::fold_W(region, config, &folded_W, &input_W_commitments, &r)?;

        debug!("fold: W folded: {new_folded_W:?}");

        let new_folded_E = Self::fold_E(
            region,
            config,
            &bn_chip,
            folded_E,
            &cross_terms_commits,
            r.clone(),
            &m_bn,
        )?;
        debug!("fold: E folded: {new_folded_W:?}");

        let new_folded_u = gate.add(region, &folded_u, &r_value)?;
        debug!("fold: u folded: {new_folded_u:?}");

        let r_as_bn = bn_chip.from_assigned_cell_to_limbs(region, &r_value)?;
        let [new_folded_X0, new_folded_X1] = Self::fold_instances(
            &bn_chip,
            region,
            input_instances.try_into().unwrap(),
            [folded_X0, folded_X1],
            &r,
            &m_bn,
            self.limb_width,
        )?;

        let new_folded_challanges = Self::fold_challenges(
            &bn_chip,
            region,
            folded_challenges,
            input_challenges,
            &r_as_bn,
            &m_bn,
            self.limb_width,
        )?;
        debug!("fold: challenges folded: {new_folded_challanges:?}");

        let to_diff_bn = |bn: Vec<AssignedCell<C::Base, C::Base>>| {
            Some(BigUint::from_limbs(
                bn.into_iter()
                    .map(|limb_cell| -> Option<C::Base> { limb_cell.value().unwrap().copied() })
                    .map(|limb| limb.and_then(|limb| util::fe_to_fe_safe(&limb)))
                    .collect::<Option<Vec<_>>>()?
                    .into_iter(),
                self.limb_width,
            ))
        };

        macro_rules! unwrap_result_option {
            ($input:expr) => {{
                match $input {
                    Some(val) => val,
                    None => {
                        return Ok(None);
                    }
                }
            }};
        }

        // TODO
        // - Rm all `unwrap`
        // - Unpack todo
        // - Understand how return all ctx from chip
        Ok(Some(Self {
            W: unwrap_result_option!(new_folded_W.iter().map(AssignedPoint::to_curve).collect()),
            E: unwrap_result_option!(new_folded_E.to_curve()),
            u: unwrap_result_option!(util::fe_to_fe_safe(&unwrap_result_option!(new_folded_u
                .value()
                .unwrap()
                .copied()))),
            X0: unwrap_result_option!(to_diff_bn(new_folded_X0))?,
            X1: unwrap_result_option!(to_diff_bn(new_folded_X1))?,
            challenges: new_folded_challanges
                .into_iter()
                .flat_map(to_diff_bn)
                .collect::<Result<Vec<_>, _>>()?,
            limb_width: self.limb_width,
            limbs_count: self.limbs_count,
        }))
    }

    /// Assign all input arguments and generate challenge by random oracle circuit (`ro_circuit`)
    ///
    /// The advice columns from `config: &MainGateConfig` are used for assignment in cycle.
    /// The number of rows required for this depends on the input.
    fn assign_witness_with_challenge<const T: usize>(
        &self,
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        mut ro_circuit: impl ROCircuitTrait<C::Base>,
        public_params_hash: &C::Base,
        instance: &PlonkInstance<C>,
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<AssignedWitness<C>, Error> {
        let mut advice_columns = config.iter_advice_columns().enumerate().cycle();

        // A closure using a cyclic iterator that allows you to take available advice columns
        // regardless of `T`, making as few row offsets as possible
        let mut assign_next_advice =
            move |annotation: &str, region: &mut RegionCtx<C::Base>, val| {
                let (index, column) = advice_columns.by_ref().next().expect("Safe because cycle");

                if index == 0 {
                    region.next();
                }

                region.assign_advice(|| annotation.to_owned(), *column, Value::known(val))
            };

        macro_rules! assign_and_absorb_point {
            ($input:expr) => {{
                let coordinates: Coordinates<C> =
                    Option::from($input.coordinates()).ok_or(Error::CantBuildCoordinates {
                        variable_name: stringify!($input),
                        variable_str: format!("{:?}", $input),
                    })?;

                let output = AssignedPoint::<C> {
                    x: assign_next_advice(
                        concat!(stringify!($input), ".x"),
                        region,
                        *coordinates.x(),
                    )?,
                    y: assign_next_advice(
                        concat!(stringify!($input), ".y"),
                        region,
                        *coordinates.y(),
                    )?,
                };

                ro_circuit.absorb_point(
                    WrapValue::Assigned(output.x.clone()),
                    WrapValue::Assigned(output.y.clone()),
                );

                Result::<_, Error>::Ok(output)
            }};
        }

        macro_rules! assign_and_absorb_diff_field {
            ($input:expr) => {{
                let val: C::Base =
                    util::fe_to_fe_safe(&$input).ok_or(Error::WhileScalarToBase {
                        variable_name: stringify!($input),
                        variable_str: format!("{:?}", $input),
                    })?;

                let assigned = assign_next_advice(stringify!($input), region, val)?;

                ro_circuit.absorb_base(WrapValue::Assigned(assigned.clone()));

                Result::<_, Error>::Ok(assigned)
            }};
        }

        let assigned_public_params_hash = assign_next_advice(
            "Assigned public params commit for absorb",
            region,
            *public_params_hash,
        )?;
        ro_circuit.absorb_base(WrapValue::Assigned(assigned_public_params_hash.clone()));

        let assigned_W = self
            .W
            .iter()
            .map(|W| assign_and_absorb_point!(W))
            .collect::<Result<Vec<_>, _>>()?;
        let assigned_E = assign_and_absorb_point!(self.E)?;
        let assigned_u = assign_and_absorb_diff_field!(self.u)?;

        /// Macro to assign and absorb big integer limbs.
        macro_rules! assign_and_absorb_biguint {
            ($biguint:expr, $annotation_prefix:expr) => {{
                $biguint
                    .limbs()
                    .iter()
                    .enumerate()
                    .map(|(limb_index, limb)| {
                        let limb = util::fe_to_fe_safe(limb).ok_or(Error::WhileScalarToBase {
                            variable_name: $annotation_prefix,
                            variable_str: format!("{limb:?}"),
                        })?;

                        let limb_cell = assign_next_advice(
                            format!("{}, limb {limb_index}", $annotation_prefix).as_str(),
                            region,
                            limb,
                        )?;

                        ro_circuit.absorb_base(WrapValue::Assigned(limb_cell.clone()));

                        Result::<_, Error>::Ok(limb_cell)
                    })
                    .collect::<Result<Vec<_>, _>>()
            }};
        }

        let assigned_X0 = assign_and_absorb_biguint!(self.X0, "X0")?;
        let assigned_X1 = assign_and_absorb_biguint!(self.X1, "X1")?;
        let assigned_challenges = self
            .challenges
            .iter()
            .map(|challenge| assign_and_absorb_biguint!(challenge, "one of challanges"))
            .collect::<Result<Vec<_>, _>>()?;

        macro_rules! assign_and_absorb_diff_field_as_bn {
            ($input:expr, $annot:expr) => {{
                let val: C::Base = util::fe_to_fe_safe($input).unwrap();
                let limbs = BigUint::from_f(&val, self.limb_width, self.limbs_count)?
                    .limbs()
                    .iter()
                    .enumerate()
                    .map(|(limb_index, limb)| {
                        let limb_cell = assign_next_advice(
                            format!("{}, limb {limb_index}", $annot).as_str(),
                            region,
                            *limb,
                        )?;

                        ro_circuit.absorb_base(WrapValue::Assigned(limb_cell.clone()));

                        Result::<_, Error>::Ok(limb_cell)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Result::<_, Error>::Ok(limbs)
            }};
        }

        let assigned_challanges_instance = instance
            .challenges
            .iter()
            .enumerate()
            .map(|(index, challenge)| {
                assign_and_absorb_diff_field_as_bn!(challenge, format!("challenge {index} value"))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_instance_W_commitment_coordinates = instance
            .W_commitments
            .iter()
            .map(|com| assign_and_absorb_point!(com))
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_input_instance = instance
            .instance
            .iter()
            .enumerate()
            .map(|(index, instance)| {
                assign_and_absorb_diff_field_as_bn!(instance, format!("instance {index} value"))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_cross_term_commits = cross_term_commits
            .iter()
            .map(|cross_term_commit| assign_and_absorb_point!(cross_term_commit))
            .collect::<Result<Vec<_>, _>>()?;

        region.next();

        let r = ro_circuit.squeeze_n_bits(region, NUM_CHALLENGE_BITS)?;

        let mut fixed_columns = config.iter_fixed_columns().enumerate().cycle();

        // A closure using a cyclic iterator that allows you to take available advice columns
        // regardless of `T`, making as few row offsets as possible
        let mut assign_next_fixed =
            move |annotation: &str, region: &mut RegionCtx<C::Base>, val| {
                let (index, column) = fixed_columns.by_ref().next().expect("Safe because cycle");

                if index == 0 {
                    region.next();
                }

                region.assign_fixed(|| annotation.to_owned(), *column, val)
            };

        // TODO Check correctness
        let m_bn = BigUint::<C::Base>::from_biguint(
            &num_bigint::BigUint::from_str_radix(
                <C::Scalar as PrimeField>::MODULUS.trim_start_matches("0x"),
                16,
            )
            .unwrap(),
            self.limb_width,
            self.limbs_count,
        )?
        .limbs()
        .iter()
        .enumerate()
        .map(|(limb_index, limb)| {
            assign_next_fixed(format!("{limb_index}").as_str(), region, *limb)
        })
        .collect::<Result<Vec<_>, _>>()?;

        region.next();

        Ok(AssignedWitness {
            public_params_hash: assigned_public_params_hash,
            folded_W: assigned_W,
            folded_E: assigned_E,
            folded_u: assigned_u,
            folded_challenges: assigned_challenges,
            input_challenges: assigned_challanges_instance,
            folded_X0: assigned_X0,
            folded_X1: assigned_X1,
            input_W_commitments: assigned_instance_W_commitment_coordinates,
            input_instances: assigned_input_instance,
            cross_terms_commits: assigned_cross_term_commits,
            r,
            m_bn,
        })
    }
}

#[derive(Debug, Clone)]
struct BigUintView<F: ff::Field> {
    as_bn_limbs: Vec<AssignedValue<F>>,
    as_bits: Vec<AssignedValue<F>>,
}
impl<F: ff::Field> ops::Deref for BigUintView<F> {
    type Target = [AssignedValue<F>];

    fn deref(&self) -> &Self::Target {
        &self.as_bits
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::circuit::{
        floor_planner::single_pass::SingleChipLayouter,
        layouter::{RegionLayouter, RegionShape},
        Layouter, Region, RegionIndex,
    };
    use halo2curves::{bn256::G1Affine as C1, CurveAffine};
    use poseidon::Spec;
    use rand::rngs::ThreadRng;
    use rand::Rng;

    use crate::{
        commitment::CommitmentKey, constants::MAX_BITS, plonk::TableData,
        poseidon::poseidon_circuit::PoseidonChip,
    };

    use super::*;

    type Base = <C1 as CurveAffine>::Base;
    type ScalarExt = <C1 as CurveAffine>::ScalarExt;

    const T: usize = 6;
    const NUM_WITNESS: usize = 5;
    /// When the number of fold rounds increases, `K` must be increased too
    /// as the number of required rows in the table grows.
    const NUM_OF_FOLD_ROUNDS: usize = 1;
    /// 2 ^ K is count of table rows in [`TableData`]
    const K: u32 = 20;

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(64) };
    const LIMB_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    fn get_table_data() -> (TableData<Base>, MainGateConfig<T>) {
        let mut td = TableData::new(K, vec![]);
        let _ = td.cs.instance_column();
        let config = td.prepare_assembly(MainGate::<Base, T>::configure);

        (td, config)
    }

    fn random_curve_vec(mut rnd: impl Rng) -> Vec<C1> {
        iter::repeat_with(|| C1::random(&mut rnd))
            .take(NUM_WITNESS)
            .collect::<Vec<_>>()
    }

    fn assign_curve_points<C, const T: usize>(
        ctx: &mut RegionCtx<C::Base>,
        ecc: &EccChip<C, C::Base, T>,
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
        td: TableData<Base>,
        config: MainGateConfig<T>,
        rnd: ThreadRng,
        ecc: EccChip<C1, Base, T>,
        gate: MainGate<Base, T>,
        r: ScalarExt,
    }

    impl Default for Fixture {
        fn default() -> Self {
            let (td, config) = get_table_data();
            let mut rnd = rand::thread_rng();

            Self {
                td,
                r: ScalarExt::from_u128(rnd.gen()),
                ecc: EccChip::<C1, Base, T>::new(config.clone()),
                gate: MainGate::new(config.clone()),
                config,
                rnd,
            }
        }
    }

    #[test]
    fn generate_challenge() {
        let mut rnd = rand::thread_rng();

        let chip = FoldRelaxedPlonkInstanceChip::<C1>::from_instance(
            PlonkInstance {
                W_commitments: vec![C1::random(&mut rnd)],
                instance: vec![ScalarExt::random(&mut rnd), ScalarExt::random(&mut rnd)],
                challenges: vec![<C1 as CurveAffine>::ScalarExt::random(&mut rnd)],
            },
            LIMB_WIDTH,
            LIMB_LIMIT,
        )
        .unwrap();

        let (mut td, config) = get_table_data();

        let mut layouter = SingleChipLayouter::new(&mut td, vec![]).unwrap();

        let spec = Spec::<Base, T, 5>::new(10, 10);

        let plonk = PlonkInstance {
            W_commitments: vec![C1::random(&mut rnd)],
            instance: vec![ScalarExt::random(&mut rnd), ScalarExt::random(&mut rnd)],
            challenges: vec![<C1 as CurveAffine>::ScalarExt::random(&mut rnd)],
        };
        let cross_term_commits = vec![
            C1::random(&mut rnd),
            C1::random(&mut rnd),
            C1::random(&mut rnd),
        ];
        let pp_hash = Base::random(&mut rnd);
        for _ in 0..=1 {
            layouter
                .assign_region(
                    || "assign_witness_with_challenge",
                    |region| {
                        let _assigned_challenge = chip
                            .assign_witness_with_challenge(
                                &mut RegionCtx::new(region, 0),
                                &config.clone(),
                                PoseidonChip::new(config.clone(), spec.clone()),
                                &pp_hash,
                                &plonk,
                                &cross_term_commits,
                            )
                            .unwrap();
                        Ok(())
                    },
                )
                .unwrap();
        }
    }

    #[test_log::test]
    fn fold_W_test() {
        let Fixture {
            mut td,
            config,
            mut rnd,
            ecc,
            gate,
            r,
        } = Fixture::default();

        let mut folded_W = vec![CommitmentKey::<C1>::default_value(); NUM_WITNESS];

        let mut layouter = SingleChipLayouter::new(&mut td, vec![]).unwrap();

        let mut plonk = RelaxedPlonkInstance::<C1>::new(0, 0, NUM_WITNESS);

        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let mut on_circuit_W_cell = None;
            let input_W = random_curve_vec(&mut rnd);

            // Run twice for setup & real run
            for _ in 0..=1 {
                on_circuit_W_cell = Some(
                    layouter
                        .assign_region(
                            || "fold W test",
                            |region| {
                                let mut ctx = RegionCtx::new(region, 0);

                                let folded =
                                    assign_curve_points(&mut ctx, &ecc, &folded_W, "folded_W")?;
                                let input =
                                    assign_curve_points(&mut ctx, &ecc, &input_W, "input_W")?;

                                let assigned_r = ctx.assign_advice(
                                    || "r",
                                    config.state[0],
                                    Value::known(util::fe_to_fe(&r).unwrap()),
                                )?;

                                let r = gate.le_num_to_bits(&mut ctx, assigned_r, MAX_BITS)?;

                                Ok(FoldRelaxedPlonkInstanceChip::<C1>::fold_W(
                                    &mut ctx, &config, &folded, &input, &r,
                                )
                                .unwrap())
                            },
                        )
                        .unwrap(),
                );
            }

            assert_eq!(plonk.W_commitments, folded_W);

            plonk = plonk.fold(
                &PlonkInstance {
                    W_commitments: input_W.clone(),
                    instance: vec![],
                    challenges: vec![],
                },
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

            folded_W = plonk.W_commitments.clone();
        }
    }

    #[test_log::test]
    fn fold_E_test() {
        let Fixture {
            mut td,
            config,
            mut rnd,
            ecc,
            gate,
            r,
        } = Fixture::default();

        let mut folded_E = C1::default();

        let mut layouter = SingleChipLayouter::new(&mut td, vec![]).unwrap();

        let mut plonk = RelaxedPlonkInstance::<C1>::new(0, 0, 0);

        let bn_chip = BigUintMulModChip::<Base>::new(
            config
                .into_smaller_size::<{ big_uint_mul_mod_chip::MAIN_GATE_T }>()
                .unwrap(),
            LIMB_WIDTH,
            LIMB_LIMIT,
        );

        for _round in 0..=NUM_OF_FOLD_ROUNDS {
            let mut on_circuit_E_cell = None;
            let cross_term_commits = random_curve_vec(&mut rnd);

            // Run twice for setup & real run
            for _ in 0..=1 {
                on_circuit_E_cell = Some(
                    layouter
                        .assign_region(
                            || "fold E test",
                            |region| {
                                let mut ctx = RegionCtx::new(region, 0);

                                let folded_E =
                                    ecc.assign_from_curve(&mut ctx, || "folded_E", &folded_E)?;
                                let cross_term_commits = assign_curve_points(
                                    &mut ctx,
                                    &ecc,
                                    &cross_term_commits,
                                    "input_W",
                                )?;

                                let assigned_r = ctx.assign_advice(
                                    || "r",
                                    config.state[0],
                                    Value::known(util::fe_to_fe(&r).unwrap()),
                                )?;

                                let r = gate.le_num_to_bits(
                                    &mut ctx,
                                    assigned_r.clone(),
                                    NUM_CHALLENGE_BITS,
                                )?;
                                let r_vv = BigUintView {
                                    as_bn_limbs: bn_chip
                                        .from_assigned_cell_to_limbs(&mut ctx, &assigned_r)
                                        .unwrap(),
                                    as_bits: r,
                                };

                                let mut fixed_columns =
                                    config.iter_fixed_columns().enumerate().cycle();

                                let mut assign_next_fixed =
                                    move |annotation: &str, region: &mut RegionCtx<Base>, val| {
                                        let (index, column) = fixed_columns
                                            .by_ref()
                                            .next()
                                            .expect("Safe because cycle");

                                        if index == 0 {
                                            region.next();
                                        }

                                        region.assign_fixed(|| annotation.to_owned(), *column, val)
                                    };

                                let m_bn = BigUint::<Base>::from_biguint(
                                    &num_bigint::BigUint::from_str_radix(
                                        <ScalarExt as PrimeField>::MODULUS.trim_start_matches("0x"),
                                        16,
                                    )
                                    .unwrap(),
                                    LIMB_WIDTH,
                                    LIMB_LIMIT,
                                )
                                .unwrap()
                                .limbs()
                                .iter()
                                .enumerate()
                                .map(|(limb_index, limb)| {
                                    assign_next_fixed(
                                        &format!("m_bn [{limb_index}"),
                                        &mut ctx,
                                        *limb,
                                    )
                                })
                                .collect::<Result<Vec<_>, _>>()?;

                                Ok(FoldRelaxedPlonkInstanceChip::<C1>::fold_E(
                                    &mut ctx,
                                    &config,
                                    &bn_chip,
                                    folded_E,
                                    &cross_term_commits,
                                    r_vv,
                                    &m_bn,
                                )
                                .unwrap())
                            },
                        )
                        .unwrap(),
                );
            }

            assert_eq!(plonk.E_commitment, folded_E);

            plonk = plonk.fold(
                &PlonkInstance {
                    W_commitments: vec![],
                    instance: vec![],
                    challenges: vec![],
                },
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

    #[test_log::test]
    fn fold() {
        debug!("start");
        const T: usize = 6;
        let mut rnd = rand::thread_rng();

        let chip = FoldRelaxedPlonkInstanceChip::<C1>::from_instance(
            PlonkInstance {
                W_commitments: vec![C1::random(&mut rnd)],
                instance: vec![ScalarExt::random(&mut rnd), ScalarExt::random(&mut rnd)],
                challenges: vec![<C1 as CurveAffine>::ScalarExt::random(&mut rnd)],
            },
            NonZeroUsize::new(64).unwrap(),
            NonZeroUsize::new(256).unwrap(),
        )
        .unwrap();

        let mut td = TableData::new(10, vec![]);
        let mut shape: Box<dyn RegionLayouter<_>> =
            Box::new(RegionShape::new(RegionIndex::from(0)));
        let shape_mut: &mut dyn RegionLayouter<_> = shape.as_mut();

        let region = Region::from(shape_mut);

        let config = MainGate::<Base, T>::configure(&mut td.cs);
        let spec = Spec::<Base, T, { T - 1 }>::new(10, 10);

        let _fold_result = chip
            .fold::<T>(
                &mut RegionCtx::new(region, 0),
                &config.clone(),
                PoseidonChip::new(config, spec),
                &Base::random(&mut rnd),
                &PlonkInstance {
                    W_commitments: vec![C1::random(&mut rnd)],
                    instance: vec![ScalarExt::random(&mut rnd), ScalarExt::random(&mut rnd)],
                    challenges: vec![<C1 as CurveAffine>::ScalarExt::random(&mut rnd)],
                },
                &vec![
                    C1::random(&mut rnd),
                    C1::random(&mut rnd),
                    C1::random(&mut rnd),
                ],
            )
            .unwrap();
        // TODO #32 match result with NIFS
    }
}
