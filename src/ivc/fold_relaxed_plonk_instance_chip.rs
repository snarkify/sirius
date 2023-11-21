use std::{iter, num::NonZeroUsize};

use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use halo2_proofs::circuit::Value;
use halo2curves::{Coordinates, CurveAffine};
use num_traits::Num;

use crate::{
    constants::NUM_CHALLENGE_BITS,
    gadgets::{
        ecc::{AssignedPoint, EccChip},
        nonnative::bn::{
            big_uint::{self, BigUint},
            big_uint_mul_mod_chip::{self, BigUintMulModChip, ModOperationResult},
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
    X0: BigUint<C::ScalarExt>,
    X1: BigUint<C::ScalarExt>,

    limb_width: NonZeroUsize,
    limbs_count: NonZeroUsize,
}

struct AssignedWitness<C: CurveAffine> {
    public_params_commit: AssignedValue<C::Base>,
    W: AssignedPoint<C>,
    E: AssignedPoint<C>,
    u: AssignedValue<C::Base>,
    assigned_X0: Vec<AssignedValue<C::Base>>,
    assigned_X1: Vec<AssignedValue<C::Base>>,

    plonk_W_commitment: AssignedPoint<C>,
    plonk_instance: Vec<Vec<AssignedValue<C::Base>>>,
    cross_terms_commits: Vec<AssignedPoint<C>>,

    r: Vec<AssignedBit<C::Base>>,
    m_bn: Vec<AssignedValue<C::Base>>,
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
    pub fn new_default(limb_width: NonZeroUsize, limbs_count: NonZeroUsize) -> Self {
        Self {
            W: C::default(),
            E: C::default(),
            u: C::Scalar::ZERO,
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
            u: C::Scalar::default(),
            X0: BigUint::from_f(&relaxed.instance[0], limb_width, limbs_count)?,
            X1: BigUint::from_f(&relaxed.instance[1], limb_width, limbs_count)?,
            limb_width,
            limbs_count,
        })
    }

    #[allow(unused_variables)]
    pub fn fold<const T: usize>(
        self,
        region: &mut RegionCtx<C::Base>,
        config: &MainGateConfig<T>,
        ro_circuit: impl ROCircuitTrait<C::Base>,
        public_params_commit: &C::Base,
        instance: &PlonkInstance<C>,
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<Self, Error> {
        assert!(T >= 4); // TODO remaster, if possible

        let AssignedWitness {
            public_params_commit,
            W,
            E,
            u,
            assigned_X0,
            assigned_X1,
            plonk_W_commitment,
            plonk_instance,
            cross_terms_commits,
            r,
            m_bn,
        } = self.assign_witness_with_challenge(
            region,
            config,
            ro_circuit,
            public_params_commit,
            instance,
            cross_term_commits,
        )?;

        let ecc = EccChip::<C, C::Base, T>::new(config.clone());

        let rW = ecc.scalar_mul(region, &plonk_W_commitment, &r)?;
        let W_fold = ecc.add(region, &W, &rW);

        // TODO Check what with all commits
        let rT = ecc.scalar_mul(region, &cross_terms_commits[0], &r)?;
        let E_fold = ecc.add(region, &E, &rT);

        let gate = MainGate::new(config.clone());

        let r_val = gate.le_bits_to_num(region, &r)?;
        let u_fold = gate.add(region, &u, &r_val)?;

        let bn_chip = BigUintMulModChip::<C::Base>::new(
            config.into_smaller_size().unwrap(),
            self.limb_width,
            self.limbs_count,
        );

        let r_bn = bn_chip.from_assigned_cell_to_limbs(region, &r_val)?;

        let X0_bn =
            BigUint::from_assigned_cells(&assigned_X0, self.limb_width, self.limbs_count)?.unwrap();
        let X1_bn =
            BigUint::from_assigned_cells(&assigned_X1, self.limb_width, self.limbs_count)?.unwrap();

        let ModOperationResult {
            quotient: _,
            remainder: remainder_1,
        } = bn_chip.mult_mod(region, &assigned_X0, &r_bn, &m_bn)?;

        todo!("WIP: part of #32")
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

        let assigned_X0 = self
            .X0
            .limbs()
            .iter()
            .zip(iter::repeat("X0"))
            .enumerate()
            .map(|(limb_index, (limb, annot))| {
                let limb = util::fe_to_fe_safe(limb).ok_or(Error::WhileScalarToBase {
                    variable_name: annot,
                    variable_str: format!("{limb:?}"),
                })?;

                let limb_cell = assign_next_advice(
                    format!("{annot}, limb {limb_index}").as_str(),
                    region,
                    limb,
                )?;

                ro_circuit.absorb_base(WrapValue::Assigned(limb_cell.clone()));

                Result::<_, Error>::Ok(limb_cell)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let assigned_X1 = self
            .X0
            .limbs()
            .iter()
            .zip(iter::repeat("X0"))
            .enumerate()
            .map(|(limb_index, (limb, annot))| {
                let limb = util::fe_to_fe_safe(limb).ok_or(Error::WhileScalarToBase {
                    variable_name: annot,
                    variable_str: format!("{limb:?}"),
                })?;

                let limb_cell = assign_next_advice(
                    format!("{annot}, limb {limb_index}").as_str(),
                    region,
                    limb,
                )?;

                ro_circuit.absorb_base(WrapValue::Assigned(limb_cell.clone()));

                Result::<_, Error>::Ok(limb_cell)
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
            W: assigned_W,
            E: assigned_E,
            u: assigned_u,
            assigned_X0,
            assigned_X1,
            plonk_W_commitment: assigned_instance_W_commitment_coordinates,
            plonk_instance: assigned_input_instance,
            cross_terms_commits: assigned_cross_term_commits,
            r,
            m_bn,
        })
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
                y: <C1 as CurveAffine>::ScalarExt::random(&mut rnd),
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
                    y: <C1 as CurveAffine>::ScalarExt::random(&mut rnd),
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
