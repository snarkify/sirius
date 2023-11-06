use std::{iter, num::NonZeroUsize};

use ff::{Field, FromUniformBytes, PrimeFieldBits, WithSmallOrderMulGroup};
use halo2_proofs::circuit::Value;
use halo2curves::{Coordinates, CurveAffine};

use crate::{
    constants::NUM_CHALLENGE_BITS,
    gadgets::{
        ecc::{AssignedPoint, EccChip},
        nonnative::bn::{
            big_uint::{self, BigUint},
            big_uint_mul_mod_chip::BigUintMulModChip,
        },
    },
    main_gate::{AssignedBit, AssignedValue, MainGate, MainGateConfig, RegionCtx, WrapValue},
    nifs::CrossTermCommits,
    plonk::{PlonkInstance, RelaxedPlonkInstance},
    poseidon::ROCircuitTrait,
    util,
};

pub(crate) struct FoldRelaxedPlonkInstanceChip<C: CurveAffine> {
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
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("TODO")]
    BigUint(#[from] big_uint::Error),
    #[error(transparent)]
    Halo2(#[from] halo2_proofs::plonk::Error),
    #[error("TODO")]
    CantBuildCoordinates { variable_name: &'static str },
    #[error("TODO")]
    WhileScalarToBase { variable_name: &'static str },
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
            X0: BigUint::from_f(plonk_instance.instance[0], limb_width, limbs_count)?,
            X1: BigUint::from_f(plonk_instance.instance[1], limb_width, limbs_count)?,
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
            X0: BigUint::from_f(relaxed.instance[0], limb_width, limbs_count)?,
            X1: BigUint::from_f(relaxed.instance[1], limb_width, limbs_count)?,
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
        } = self.generate_challenge(
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

        // TODO Copy constraint
        let r_bn = BigUint::from_assigned_cells(&[r_val], self.limb_width, self.limbs_count)?;

        // TODO Chagne `ZETA` to `m`
        let m_bn = BigUint::from_f(C::Base::ZETA, self.limb_width, self.limbs_count);

        let _bn_chip = BigUintMulModChip::<C::Base>::new(
            config.into_size().unwrap(),
            self.limb_width,
            self.limbs_count,
        );

        todo!()
    }

    fn generate_challenge<const T: usize>(
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

                if index != 0 && index % (T + 2) == 0 {
                    region.next();
                }

                region.assign_advice(|| annotation.to_owned(), *column, Value::known(val))
            };

        macro_rules! assign_point {
            ($input:expr) => {{
                let coordinates: Coordinates<C> =
                    Option::from($input.coordinates()).ok_or(Error::CantBuildCoordinates {
                        variable_name: stringify!($input),
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
                let limbs = BigUint::from_f(val, self.limb_width, self.limbs_count)?
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
        })
    }
}
