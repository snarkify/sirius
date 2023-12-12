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
    W: C,
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
    /// Sourced directly from the `public_params_commit` argument of [`FoldRelaxedPlonkInstanceChip::fold`].
    public_params_commit: AssignedValue<C::Base>,

    /// Assigned point representing the folded accumulator W.
    /// Derived from [`FoldRelaxedPlonkInstanceChip::W`]
    folded_W: AssignedPoint<C>,

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
    /// Sourced directly from [`PlonkInstance::W_commitment`] provided to [`FoldRelaxedPlonkInstanceChip::fold`].
    input_W_commitment: AssignedPoint<C>,

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
    ) -> Self {
        Self {
            W: C::default(),
            E: C::default(),
            u: C::Scalar::ZERO,
            challenges: iter::repeat_with(|| BigUint::one(limb_width))
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
            W: plonk_instance.W_commitment,
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
            W: relaxed.W_commitment,
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

    fn fold_W<const T: usize>(
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        folded_W: &AssignedPoint<C>,
        input_W_commitment: &AssignedPoint<C>,
        r: &[AssignedCell<C::Base, C::Base>],
    ) -> Result<AssignedPoint<C>, Error> {
        let ecc = EccChip::<C, C::Base, T>::new(config.clone());
        let rW = ecc.scalar_mul(region, input_W_commitment, r)?;
        Ok(ecc.add(region, folded_W, &rW)?)
    }

    fn fold_E<const T: usize>(
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        folded_E: AssignedPoint<C>,
        cross_term_commits: &[AssignedPoint<C>],
        r: ValueView<C::Base>,
    ) -> Result<AssignedPoint<C>, Error> {
        let ecc = EccChip::<C, C::Base, T>::new(config.clone());
        let gate = MainGate::new(config.clone());

        let powers_of_r = iter::successors(Some(Ok(r.clone())), |val| {
            Some(Ok(val.as_ref().ok()?).and_then(|r_pow_i| {
                let ValueView { value, bits } = r_pow_i;

                let current = gate.mul(region, value, &r.value)?;
                let current_bits = gate.le_num_to_bits(region, current.clone(), bits.len())?;

                Result::<_, Error>::Ok(ValueView {
                    value: current,
                    bits: current_bits,
                })
            }))
        })
        .take(cross_term_commits.len())
        .collect::<Result<Vec<_>, _>>()?;

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

    pub fn fold<const T: usize>(
        self,
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        ro_circuit: impl ROCircuitTrait<C::Base>,
        public_params_commit: &C::Base,
        input_plonk: &PlonkInstance<C>,
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<Self, Error> {
        assert!(T >= 4); // TODO remaster, if possible

        let AssignedWitness {
            public_params_commit: _, // TODO Check don't use in scheme
            folded_W,
            folded_E,
            folded_u,
            folded_X0,
            folded_X1,
            input_W_commitment,
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
            public_params_commit,
            input_plonk,
            cross_term_commits,
        )?;

        debug!("fold: Assigned & Generated challenge: {r:?}");

        let gate = MainGate::new(config.clone());

        let r = ValueView {
            value: gate.le_bits_to_num(region, &r)?,
            bits: r,
        };

        let new_folded_W = Self::fold_W(region, config, &folded_W, &input_W_commitment, &r)?;

        debug!("fold: W folded: {new_folded_W:?}");

        let new_folded_E = Self::fold_E(region, config, folded_E, &cross_terms_commits, r.clone())?;
        debug!("fold: E folded: {new_folded_W:?}");

        let new_folded_u = gate.add(region, &folded_u, &r.value)?;
        debug!("fold: u folded: {new_folded_u:?}");

        let bn_chip = BigUintMulModChip::<C::Base>::new(
            config
                .into_smaller_size::<{ big_uint_mul_mod_chip::MAIN_GATE_T }>()
                .unwrap(),
            self.limb_width,
            self.limbs_count,
        );

        let r_as_bn = bn_chip.from_assigned_cell_to_limbs(region, &r.value)?;
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

        // TODO
        // - Rm all `unwrap`
        // - Unpack todo
        // - Understand how return all ctx from chip
        todo!(
            "Ok(Self {{
            W: {new_folded_W:?}.to_curve().unwrap(),
            E: {new_folded_E:?}.to_curve().unwrap(),
            u: util::fe_to_fe_safe(&{new_folded_u:?}.value().unwrap().copied().unwrap()).unwrap(),
            X0: BigUint::from_assigned_cells(&{new_folded_X0:?}, self.limb_width, self.limbs_count)?
                .unwrap(),
            X1: BigUint::from_assigned_cells(&{new_folded_X1:?}, self.limb_width, self.limbs_count)?
                .unwrap(),
            challenges: {new_folded_challanges:?}
                .into_iter()
                .map(|ch| {{
                    BigUint::from_assigned_cells(&ch, self.limb_width, self.limbs_count)?.unwrap()
                }})
                .collect::<Result<Vec<_>, _>>()?,
            limb_width: self.limb_width,
            limbs_count: self.limbs_count,
        }})"
        )
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
        public_params_commit: &C::Base,
        instance: &PlonkInstance<C>,
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<AssignedWitness<C>, Error> {
        let mut advice_columns = config
            .state
            .iter()
            .chain(iter::once(&config.input))
            .chain(iter::once(&config.out))
            .enumerate()
            .cycle();

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

        macro_rules! assign_point {
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

        macro_rules! assign_diff_field {
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

        let assigned_public_params_commit = assign_next_advice(
            "Assigned public params commit for absorb",
            region,
            *public_params_commit,
        )?;
        ro_circuit.absorb_base(WrapValue::Assigned(assigned_public_params_commit.clone()));

        let assigned_W = assign_point!(self.W)?;
        let assigned_E = assign_point!(self.E)?;
        let assigned_u = assign_diff_field!(self.u)?;

        /// Macro to assign and absorb big integer limbs.
        macro_rules! assign_biguint {
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

        let assigned_X0 = assign_biguint!(self.X0, "X0")?;
        let assigned_X1 = assign_biguint!(self.X1, "X1")?;
        let assigned_challenges = self
            .challenges
            .iter()
            .map(|challenge| assign_biguint!(challenge, "one of challanges"))
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_challanges_instance = instance
            .challenges
            .iter()
            .enumerate()
            .map(|(index, challenge)| {
                let val: C::Base = util::fe_to_fe_safe(challenge).unwrap();
                let limbs = BigUint::from_f(&val, self.limb_width, self.limbs_count)?
                    .limbs()
                    .iter()
                    .enumerate()
                    .map(|(limb_index, limb)| {
                        let limb_cell = assign_next_advice(
                            format!("instance {index} value, limb {limb_index}").as_str(),
                            region,
                            *limb,
                        )?;

                        ro_circuit.absorb_base(WrapValue::Assigned(limb_cell.clone()));

                        Result::<_, Error>::Ok(limb_cell)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Result::<_, Error>::Ok(limbs)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_instance_W_commitment_coordinates = assign_point!(instance.W_commitment)?;
        let assigned_input_instance = instance
            .instance
            .iter()
            .enumerate()
            .map(|(index, val)| {
                let val: C::Base = util::fe_to_fe_safe(val).unwrap();
                let limbs = BigUint::from_f(&val, self.limb_width, self.limbs_count)?
                    .limbs()
                    .iter()
                    .enumerate()
                    .map(|(limb_index, limb)| {
                        let limb_cell = assign_next_advice(
                            format!("instance {index} value, limb {limb_index}").as_str(),
                            region,
                            *limb,
                        )?;

                        ro_circuit.absorb_base(WrapValue::Assigned(limb_cell.clone()));

                        Result::<_, Error>::Ok(limb_cell)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Result::<_, Error>::Ok(limbs)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_cross_term_commits = cross_term_commits
            .iter()
            .map(|cross_term_commit| assign_point!(cross_term_commit))
            .collect::<Result<Vec<_>, _>>()?;

        region.next();

        let r = ro_circuit.squeeze_n_bits(region, NUM_CHALLENGE_BITS)?;

        let mut fixed_columns = config
            .q_1
            .iter()
            .chain(config.q_5.iter())
            .chain(iter::once(&config.q_m))
            .chain(iter::once(&config.q_i))
            .chain(iter::once(&config.q_o))
            .chain(iter::once(&config.rc))
            .enumerate()
            .cycle();

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
            public_params_commit: assigned_public_params_commit,
            folded_W: assigned_W,
            folded_E: assigned_E,
            folded_u: assigned_u,
            folded_challenges: assigned_challenges,
            input_challenges: assigned_challanges_instance,
            folded_X0: assigned_X0,
            folded_X1: assigned_X1,
            input_W_commitment: assigned_instance_W_commitment_coordinates,
            input_instances: assigned_input_instance,
            cross_terms_commits: assigned_cross_term_commits,
            r,
            m_bn,
        })
    }
}

#[derive(Debug, Clone)]
struct ValueView<F: ff::Field> {
    value: AssignedValue<F>,
    bits: Vec<AssignedValue<F>>,
}
impl<F: ff::Field> ops::Deref for ValueView<F> {
    type Target = [AssignedValue<F>];

    fn deref(&self) -> &Self::Target {
        &self.bits
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::circuit::{
        layouter::{RegionLayouter, RegionShape},
        Region, RegionIndex,
    };
    use halo2curves::bn256::G1Affine as C1;

    type Base = <C1 as CurveAffine>::Base;
    type ScalarExt = <C1 as CurveAffine>::ScalarExt;

    use poseidon::Spec;

    use crate::{plonk::TableData, poseidon::poseidon_circuit::PoseidonChip};

    use super::*;

    #[test]
    fn generate_challenge() {
        let mut rnd = rand::thread_rng();

        let chip = FoldRelaxedPlonkInstanceChip::<C1>::from_instance(
            PlonkInstance {
                W_commitment: C1::random(&mut rnd),
                instance: vec![ScalarExt::random(&mut rnd), ScalarExt::random(&mut rnd)],
                challenges: vec![<C1 as CurveAffine>::ScalarExt::random(&mut rnd)],
            },
            NonZeroUsize::new(64).unwrap(),
            NonZeroUsize::new(4).unwrap(),
        )
        .unwrap();

        let mut td = TableData::new(10, vec![]);
        let mut shape: Box<dyn RegionLayouter<_>> =
            Box::new(RegionShape::new(RegionIndex::from(0)));
        let shape_mut: &mut dyn RegionLayouter<_> = shape.as_mut();

        let region = Region::from(shape_mut);

        let config = MainGate::<Base, 5>::configure(&mut td.cs);
        let spec = Spec::<Base, 5, 4>::new(10, 10);

        let _assigned_challenge = chip
            .assign_witness_with_challenge(
                &mut RegionCtx::new(region, 0),
                &config.clone(),
                PoseidonChip::new(config, spec),
                &Base::random(&mut rnd),
                &PlonkInstance {
                    W_commitment: C1::random(&mut rnd),
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
    }

    #[test_log::test]
    fn fold() {
        debug!("start");
        const T: usize = 6;
        let mut rnd = rand::thread_rng();

        let chip = FoldRelaxedPlonkInstanceChip::<C1>::from_instance(
            PlonkInstance {
                W_commitment: C1::random(&mut rnd),
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
                    W_commitment: C1::random(&mut rnd),
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
    }
}
