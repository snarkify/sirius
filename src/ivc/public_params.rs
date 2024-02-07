use std::{fmt, io, num::NonZeroUsize};

use ff::{Field, FromUniformBytes, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2_proofs::plonk::{Column, Instance};
use halo2curves::CurveAffine;
use log::*;
use serde::Serialize;

use crate::{
    commitment::CommitmentKey,
    digest::{self, DigestToCurve},
    ivc::step_circuit::StepCircuitExt,
    plonk::PlonkStructure,
    poseidon::ROPair,
    table::TableData,
};

use super::{
    step_circuit::{self, StepConfig, SynthesizeStepParams},
    StepCircuit,
};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("While configure table data: {0:?}")]
    Configure(#[from] step_circuit::ConfigureError),
}

pub(crate) struct CircuitPublicParams<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, SC, RP>
where
    C: CurveAffine,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    SC: StepCircuit<ARITY, C::Scalar>,
    RP: ROPair<C::Scalar>,
{
    ck: &'key CommitmentKey<C>,
    params: SynthesizeStepParams<C::Scalar, RP::OnCircuit>,

    td: TableData<C::Scalar>,
    X0: Column<Instance>,
    config: StepConfig<ARITY, MAIN_GATE_T, C::Scalar, SC>,
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, SC, RP> fmt::Debug
    for CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, SC, RP>
where
    C: fmt::Debug + CurveAffine,
    C::ScalarExt: PrimeFieldBits + FromUniformBytes<64>,
    SC: StepCircuit<ARITY, C::ScalarExt>,
    RP: ROPair<C::ScalarExt>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CircuitPublicParams")
            .field("ck_len", &self.ck.len())
            .field("td_k", &self.td.k)
            .field("params", &self.params)
            .finish()
    }
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, SC, RP>
    CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, SC, RP>
where
    C: fmt::Debug + CurveAffine,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64>,
    SC: StepCircuit<ARITY, C::Scalar>,
    RP: ROPair<C::Scalar>,
{
    fn new(
        k_table_size: u32,
        commitment_key: &'key CommitmentKey<C>,
        is_primary_circuit: bool,
        ro_constant: RP::Args,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        debug!("start creating circuit pp");

        let mut td = TableData::new(k_table_size, vec![C::Scalar::ZERO, C::Scalar::ZERO]);

        let (X0, config) = td.configure(|cs| {
            let instance = cs.instance_column();
            cs.enable_equality(instance);

            (
                instance,
                <SC as StepCircuitExt<'_, ARITY, C::Scalar>>::configure::<MAIN_GATE_T>(cs),
            )
        });

        Ok(Self {
            td,
            X0,
            config: config?,
            ck: commitment_key,
            params: SynthesizeStepParams {
                limb_width,
                limbs_count,
                is_primary_circuit,
                ro_constant,
            },
        })
    }

    pub fn td_k(&self) -> u32 {
        self.td.k
    }

    pub fn prepare_td(
        &self,
        instance_columns: &[C::Scalar],
    ) -> (
        StepConfig<ARITY, MAIN_GATE_T, C::Scalar, SC>,
        TableData<C::Scalar>,
        Column<Instance>,
    ) {
        let mut td = self.td.clone();
        td.instance = instance_columns.to_vec();
        (self.config.clone(), td, self.X0)
    }

    pub fn params(&self) -> &SynthesizeStepParams<C::Scalar, RP::OnCircuit> {
        &self.params
    }

    pub fn ck(&self) -> &'key CommitmentKey<C> {
        self.ck
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
    pub(crate) primary: CircuitPublicParams<'key, A1, MAIN_GATE_T, C1, SC1, RP1>,
    pub(crate) secondary: CircuitPublicParams<'key, A2, MAIN_GATE_T, C2, SC2, RP2>,
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

pub struct CircuitPublicParamsInput<'key, C: CurveAffine, RPArgs> {
    pub commitment_key: &'key CommitmentKey<C>,
    pub k_table_size: u32,
    pub ro_constant: RPArgs,
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

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    pub fn new(
        primary: CircuitPublicParamsInput<'key, C1, RP1::Args>,
        secondary: CircuitPublicParamsInput<'key, C2, RP2::Args>,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Result<Self, Error> {
        debug!("start creating pp");
        Ok(Self {
            primary: CircuitPublicParams::new(
                primary.k_table_size,
                primary.commitment_key,
                true,
                primary.ro_constant,
                limb_width,
                limbs_count_limit,
            )?,
            secondary: CircuitPublicParams::new(
                secondary.k_table_size,
                secondary.commitment_key,
                false,
                secondary.ro_constant,
                limb_width,
                limbs_count_limit,
            )?,
        })
    }

    /// This method calculate digest of [`PublicParams`], but ignore [`CircuitPublicParams::ck`]
    /// from both step circuits params
    pub fn digest<C: CurveAffine>(&self) -> Result<C, io::Error> {
        calc_digest::<C1, C2, C, RP1, RP2>(
            &self.primary.params,
            &self
                .primary
                .td
                .plonk_structure()
                .expect("unrechable, prepared in constructor"),
            &self.secondary.params,
            &self
                .secondary
                .td
                .plonk_structure()
                .expect("unrechable, prepared in constructor"),
        )
    }
}

pub fn calc_digest<C1: CurveAffine, C2: CurveAffine, CO: CurveAffine, RP1, RP2>(
    primary_params: &SynthesizeStepParams<C1::Scalar, RP1::OnCircuit>,
    primary_plonk_struct: &PlonkStructure<C1::Scalar>,
    secondary_params: &SynthesizeStepParams<C2::Scalar, RP2::OnCircuit>,
    secondary_plonk_struct: &PlonkStructure<C2::Scalar>,
) -> Result<CO, io::Error>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    #[derive(serde::Serialize)]
    #[serde(bound(serialize = ""))]
    struct SerializableWrapper<'l, C1, C2, RP1, RP2>
    where
        C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
        C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

        C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
        C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

        RP1: ROPair<C1::Scalar>,
        RP2: ROPair<C2::Scalar>,
    {
        primary_plonk_struct: &'l PlonkStructure<C1::Scalar>,
        secondary_plonk_struct: &'l PlonkStructure<C2::Scalar>,
        primary_params: &'l SynthesizeStepParams<C1::Scalar, RP1::OnCircuit>,
        secondary_params: &'l SynthesizeStepParams<C2::Scalar, RP2::OnCircuit>,
    }

    digest::DefaultHasher::digest_to_curve(&SerializableWrapper::<'_, C1, C2, RP1, RP2> {
        primary_plonk_struct,
        secondary_plonk_struct,
        primary_params,
        secondary_params,
    })
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
    fn digest() {
        type Scalar1 = <C1 as Group>::Scalar;
        type Scalar2 = <C2 as Group>::Scalar;

        let spec1 = RandomOracleConstant::<5, 4, Scalar1>::new(10, 10);
        let spec2 = RandomOracleConstant::<5, 4, Scalar2>::new(10, 10);

        const K: usize = 5;

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
            },
            CircuitPublicParamsInput {
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
