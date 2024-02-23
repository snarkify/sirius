use std::{fmt, io, marker::PhantomData, num::NonZeroUsize};

use ff::{FromUniformBytes, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2_proofs::plonk::Error as Halo2Error;
use halo2curves::CurveAffine;
use log::*;
use once_cell::sync::OnceCell;
use serde::Serialize;

use crate::{
    commitment::CommitmentKey,
    digest::{self, DigestToCurve},
    ivc::{step_circuit::StepCircuit, step_folding_circuit::StepFoldingCircuit},
    main_gate::MainGateConfig,
    plonk::PlonkStructure,
    poseidon::ROPair,
    table::TableData,
};

use super::step_folding_circuit::StepParams;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Plonk(#[from] Halo2Error),
}

pub(crate) struct CircuitPublicParams<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP>
where
    C: CurveAffine,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    RP: ROPair<C::Scalar>,
{
    pub k_table_size: u32,
    pub S: PlonkStructure<C::Scalar>,
    pub ck: &'key CommitmentKey<C>,
    pub params: StepParams<C::Scalar, RP::OnCircuit>,
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP> fmt::Debug
    for CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, RP>
where
    C: fmt::Debug + CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    RP: ROPair<C::Scalar>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CircuitPublicParams")
            .field("ck_len", &self.ck.len())
            .field("params", &self.params)
            .finish()
    }
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP>
    CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, RP>
where
    C: fmt::Debug + CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    RP: ROPair<C::Scalar, Config = MainGateConfig<MAIN_GATE_T>>,
{
    fn new(
        k_table_size: u32,
        S: PlonkStructure<C::Scalar>,
        commitment_key: &'key CommitmentKey<C>,
        ro_constant: RP::Args,
        limb_width: NonZeroUsize,
        n_limbs: NonZeroUsize,
    ) -> Result<Self, Error> {
        debug!("start creating circuit pp");

        Ok(Self {
            k_table_size,
            S,
            ck: commitment_key,
            params: StepParams {
                limb_width,
                limbs_count: n_limbs,
                ro_constant,
            },
        })
    }
}

pub struct PublicParams<
    'key,
    const A1: usize,
    const A2: usize,
    const MAIN_GATE_T: usize,
    C1,
    C2,
    SC1,
    SC2,
    RP1,
    RP2,
> where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    pub(crate) primary: CircuitPublicParams<'key, A1, MAIN_GATE_T, C1, RP1>,
    pub(crate) secondary: CircuitPublicParams<'key, A2, MAIN_GATE_T, C2, RP2>,
    // TODO: change C1::Scalar after adding digest_to_scalar
    // we only need one digest in scalar representation
    pub(crate) digest1: OnceCell<C1>,
    pub(crate) digest2: OnceCell<C2>,
    _p: PhantomData<(SC1, SC2)>,
}

impl<
        'key,
        const A1: usize,
        const A2: usize,
        const MAIN_GATE_T: usize,
        C1,
        C2,
        SC1,
        SC2,
        RP1,
        RP2,
    > fmt::Debug for PublicParams<'key, A1, A2, MAIN_GATE_T, C1, C2, SC1, SC2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
    C1: fmt::Debug,
    C2: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicParams")
            .field("primary", &self.primary)
            .field("secondary", &self.secondary)
            .finish()
    }
}

pub struct CircuitPublicParamsInput<'key, const ARITY: usize, C, RPArgs, SC>
where
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::ScalarExt>,
{
    pub commitment_key: &'key CommitmentKey<C>,
    pub k_table_size: u32,
    pub ro_constant: RPArgs,
    pub circuit: SC,
}

impl<
        'key,
        const A1: usize,
        const A2: usize,
        const MAIN_GATE_T: usize,
        C1,
        C2,
        SC1,
        SC2,
        RP1,
        RP2,
    > PublicParams<'key, A1, A2, MAIN_GATE_T, C1, C2, SC1, SC2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,

    RP1: ROPair<C1::Scalar, Config = MainGateConfig<MAIN_GATE_T>>,
    RP2: ROPair<C2::Scalar, Config = MainGateConfig<MAIN_GATE_T>>,
{
    pub fn new(
        primary: CircuitPublicParamsInput<'key, A1, C1, RP1::Args, SC1>,
        secondary: CircuitPublicParamsInput<'key, A2, C2, RP2::Args, SC2>,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Result<Self, Error> {
        debug!("start creating pp");
        let sp1 = StepParams {
            limb_width,
            limbs_count: limbs_count_limit,
            ro_constant: primary.ro_constant.clone(),
        };
        let primary_circuit =
            StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, MAIN_GATE_T>::new(
                primary.k_table_size as usize,
                &primary.circuit,
                &sp1,
            );

        let sp2 = StepParams {
            limb_width,
            limbs_count: limbs_count_limit,
            ro_constant: secondary.ro_constant.clone(),
        };
        let secondary_circuit =
            StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, MAIN_GATE_T>::new(
                secondary.k_table_size as usize,
                &secondary.circuit,
                &sp2,
            );
        let td1 = TableData::new(primary.k_table_size, primary_circuit, vec![]);
        let S1 = td1.plonk_structure()?;
        let td2 = TableData::new(secondary.k_table_size, secondary_circuit, vec![]);
        let S2 = td2.plonk_structure()?;
        Ok(Self {
            primary: CircuitPublicParams::new(
                primary.k_table_size,
                S1,
                primary.commitment_key,
                primary.ro_constant,
                limb_width,
                limbs_count_limit,
            )?,
            secondary: CircuitPublicParams::new(
                secondary.k_table_size,
                S2,
                secondary.commitment_key,
                secondary.ro_constant,
                limb_width,
                limbs_count_limit,
            )?,
            digest1: OnceCell::new(),
            digest2: OnceCell::new(),
            _p: PhantomData,
        })
    }

    /// This method calculate digest of [`PublicParams`], but ignore [`CircuitPublicParams::ck`]
    /// from both step circuits params
    /// TODO: this is hacking for now;
    /// modify it to digest_to_scalar instead
    /// instead of two methods
    pub fn digest1(&self) -> Result<C1, io::Error> {
        let digest = self.digest1.get_or_try_init(|| {
            PublicParamsDigestWrapper::<'_, C1, C2, RP1, RP2> {
                primary_plonk_struct: &self.primary.S,
                secondary_plonk_struct: &self.secondary.S,
                primary_params: &self.primary.params,
                secondary_params: &self.secondary.params,
            }
            .digest()
        })?;
        Ok(*digest)
    }

    pub fn digest2(&self) -> Result<C2, io::Error> {
        let digest = self.digest2.get_or_try_init(|| {
            PublicParamsDigestWrapper::<'_, C1, C2, RP1, RP2> {
                primary_plonk_struct: &self.primary.S,
                secondary_plonk_struct: &self.secondary.S,
                primary_params: &self.primary.params,
                secondary_params: &self.secondary.params,
            }
            .digest()
        })?;
        Ok(*digest)
    }
}

#[derive(serde::Serialize)]
#[serde(bound(serialize = ""))]
pub(crate) struct PublicParamsDigestWrapper<'l, C1, C2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    pub primary_plonk_struct: &'l PlonkStructure<C1::Scalar>,
    pub secondary_plonk_struct: &'l PlonkStructure<C2::Scalar>,
    pub primary_params: &'l StepParams<C1::Scalar, RP1::OnCircuit>,
    pub secondary_params: &'l StepParams<C2::Scalar, RP2::OnCircuit>,
}

impl<'l, C1, C2, RP1, RP2> PublicParamsDigestWrapper<'l, C1, C2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    pub fn digest<C: CurveAffine>(&self) -> Result<C, io::Error> {
        digest::DefaultHasher::digest_to_curve(self)
    }
}

#[cfg(test)]
mod pp_test {
    use group::Group;
    use halo2curves::{bn256, grumpkin};

    use crate::ivc::step_circuit;
    use bn256::G1 as C1;
    use grumpkin::G1 as C2;

    use super::*;

    type C1Affine = <C1 as halo2curves::group::prime::PrimeCurve>::Affine;
    type C2Affine = <C2 as halo2curves::group::prime::PrimeCurve>::Affine;

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
    const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    type RandomOracle<const T: usize, const RATE: usize> = crate::poseidon::PoseidonRO<T, RATE>;

    type RandomOracleConstant<const T: usize, const RATE: usize, F> =
        <RandomOracle<T, RATE> as ROPair<F>>::Args;

    #[test]
    #[ignore = "cause it takes a few minutes to run"]
    fn digest() {
        type Scalar1 = <C1 as Group>::Scalar;
        type Scalar2 = <C2 as Group>::Scalar;

        let spec1 = RandomOracleConstant::<5, 4, Scalar1>::new(10, 10);
        let spec2 = RandomOracleConstant::<5, 4, Scalar2>::new(10, 10);

        let sc1 = step_circuit::trivial::Circuit::<1, _>::default();
        let sc2 = step_circuit::trivial::Circuit::<1, _>::default();

        const K: usize = 16;

        PublicParams::<
            '_,
            1,
            1,
            5,
            C1Affine,
            C2Affine,
            step_circuit::trivial::Circuit<1, Scalar1>,
            step_circuit::trivial::Circuit<1, Scalar2>,
            RandomOracle<5, 4>,
            RandomOracle<5, 4>,
        >::new(
            CircuitPublicParamsInput {
                k_table_size: K as u32,
                commitment_key: &CommitmentKey::setup(K, b"1"),
                ro_constant: spec1,
                circuit: sc1,
            },
            CircuitPublicParamsInput {
                k_table_size: K as u32,
                commitment_key: &CommitmentKey::setup(K, b"2"),
                ro_constant: spec2,
                circuit: sc2,
            },
            LIMB_WIDTH,
            LIMBS_COUNT_LIMIT,
        )
        .unwrap()
        .digest1()
        .unwrap();
    }
}
