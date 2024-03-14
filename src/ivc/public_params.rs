use std::{fmt, io, marker::PhantomData, num::NonZeroUsize};

use ff::{Field, FromUniformBytes, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2_proofs::plonk;
use halo2curves::CurveAffine;
use serde::Serialize;
use tracing::*;

use crate::{
    commitment::CommitmentKey,
    digest::{self, DigestToCurve},
    ivc::{
        step_folding_circuit::{StepFoldingCircuit, StepInputs},
        NUM_IO,
    },
    main_gate::MainGateConfig,
    plonk::PlonkStructure,
    poseidon::ROPair,
    table::CircuitRunner,
};

use super::{step_folding_circuit::StepParams, StepCircuit};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Plonk(#[from] plonk::Error),
    #[error("Error while calculate digest of pp")]
    WhileDigest(#[from] io::Error),
}

#[derive(Serialize)]
pub(crate) struct CircuitPublicParams<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP>
where
    C: CurveAffine,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP: ROPair<C::Scalar>,
{
    S: PlonkStructure<C::Scalar>,
    ck: &'key CommitmentKey<C>,
    params: StepParams<C::Scalar, RP::OnCircuit>,
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP>
    CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, RP>
where
    C: CurveAffine,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP: ROPair<C::Scalar>,
{
    pub fn k_table_size(&self) -> u32 {
        self.S.k as u32
    }
    pub fn ck(&self) -> &'key CommitmentKey<C> {
        self.ck
    }
    pub fn params(&self) -> &StepParams<C::Scalar, RP::OnCircuit> {
        &self.params
    }
    pub fn S(&self) -> &PlonkStructure<C::Scalar> {
        &self.S
    }
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP> fmt::Debug
    for CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, RP>
where
    C: fmt::Debug + CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
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
    C::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP: ROPair<C::Scalar, Config = MainGateConfig<MAIN_GATE_T>>,
{
    fn new(
        S: PlonkStructure<C::Scalar>,
        commitment_key: &'key CommitmentKey<C>,
        ro_constant: RP::Args,
        limb_width: NonZeroUsize,
        n_limbs: NonZeroUsize,
    ) -> Result<Self, Error> {
        debug!("start creating circuit pp");

        let params = StepParams::new(limb_width, n_limbs, ro_constant);

        Ok(Self {
            S,
            ck: commitment_key,
            params,
        })
    }
}

#[derive(serde::Serialize)]
#[serde(bound(serialize = ""))]
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
    _p: PhantomData<(SC1, SC2)>,

    #[serde(skip_serializing)]
    digest_1: C1,
    #[serde(skip_serializing)]
    digest_2: C2,
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

pub struct CircuitPublicParamsInput<
    'key,
    'circuit,
    const A: usize,
    C: CurveAffine,
    RPArgs,
    SC: StepCircuit<A, C::Scalar>,
> {
    step_circuit: &'circuit SC,
    commitment_key: &'key CommitmentKey<C>,
    k_table_size: u32,
    ro_constant: RPArgs,
}

impl<'key, 'circuit, const A: usize, C: CurveAffine, RPArgs, SC: StepCircuit<A, C::Scalar>>
    CircuitPublicParamsInput<'key, 'circuit, A, C, RPArgs, SC>
{
    pub fn new(
        k_table_size: u32,
        commitment_key: &'key CommitmentKey<C>,
        ro_constant: RPArgs,
        step_circuit: &'circuit SC,
    ) -> Self {
        Self {
            commitment_key,
            k_table_size,
            step_circuit,
            ro_constant,
        }
    }
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
        primary: CircuitPublicParamsInput<'key, '_, A1, C1, RP1::Args, SC1>,
        secondary: CircuitPublicParamsInput<'key, '_, A2, C2, RP2::Args, SC2>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        let primary_S = CircuitRunner::new(
            primary.k_table_size,
            StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, MAIN_GATE_T> {
                step_circuit: primary.step_circuit,
                input: StepInputs::without_witness::<SC1>(
                    primary.k_table_size,
                    NUM_IO,
                    &StepParams::new(limb_width, limbs_count, primary.ro_constant.clone()),
                ),
            },
            vec![C1::Scalar::ZERO, C1::Scalar::ZERO],
        )
        .try_collect_plonk_structure()?;

        let secondary_S = CircuitRunner::new(
            primary.k_table_size,
            StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, MAIN_GATE_T> {
                step_circuit: secondary.step_circuit,
                input: StepInputs::without_witness::<SC2>(
                    secondary.k_table_size,
                    NUM_IO,
                    &StepParams::new(limb_width, limbs_count, secondary.ro_constant.clone()),
                ),
            },
            vec![C2::Scalar::ZERO, C2::Scalar::ZERO],
        )
        .try_collect_plonk_structure()?;

        debug!("start creating pp");
        let mut self_ = Self {
            primary: CircuitPublicParams::new(
                primary_S,
                primary.commitment_key,
                primary.ro_constant,
                limb_width,
                limbs_count,
            )?,
            secondary: CircuitPublicParams::new(
                secondary_S,
                secondary.commitment_key,
                secondary.ro_constant,
                limb_width,
                limbs_count,
            )?,
            digest_1: C1::identity(),
            digest_2: C2::identity(),
            _p: PhantomData,
        };

        self_.digest_1 = self_.digest()?;
        self_.digest_2 = self_.digest()?;

        Ok(self_)
    }

    pub fn digest_1(&self) -> C1 {
        self.digest_1
    }

    pub fn digest_2(&self) -> C2 {
        self.digest_2
    }

    /// This method calculate digest of [`PublicParams`], but ignore [`CircuitPublicParams::ck`]
    /// from both step circuits params
    pub fn digest<C: CurveAffine>(&self) -> Result<C, io::Error> {
        digest::DefaultHasher::digest_to_curve(self)
    }
}

#[derive(Serialize)]
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
    primary_plonk_struct: PlonkStructure<C1::Scalar>,
    secondary_plonk_struct: PlonkStructure<C2::Scalar>,
    primary_params: &'l StepParams<C1::Scalar, RP1::OnCircuit>,
    secondary_params: &'l StepParams<C2::Scalar, RP2::OnCircuit>,
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

    use crate::ivc::step_circuit::{self, trivial};
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

    #[test_log::test]
    fn digest() {
        type Scalar1 = <C1 as Group>::Scalar;
        type Scalar2 = <C2 as Group>::Scalar;

        let spec1 = RandomOracleConstant::<5, 4, Scalar1>::new(10, 10);
        let spec2 = RandomOracleConstant::<5, 4, Scalar2>::new(10, 10);

        const K: usize = 15;

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
                step_circuit: &trivial::Circuit::default(),
                k_table_size: K as u32,
                commitment_key: &CommitmentKey::setup(K, b"1"),
                ro_constant: spec1,
            },
            CircuitPublicParamsInput {
                step_circuit: &trivial::Circuit::default(),
                k_table_size: K as u32,
                commitment_key: &CommitmentKey::setup(K, b"2"),
                ro_constant: spec2,
            },
            LIMB_WIDTH,
            LIMBS_COUNT_LIMIT,
        )
        .unwrap()
        .digest::<C1Affine>()
        .unwrap();
    }
}
