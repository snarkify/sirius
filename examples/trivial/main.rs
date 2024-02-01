use std::{array, num::NonZeroUsize};

use ff::PrimeField;
use halo2_gadgets::sha256::BLOCK_SIZE;

use halo2curves::{bn256, grumpkin, CurveExt};

use bn256::G1 as C1;
use grumpkin::G1 as C2;

use log::*;
use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit, PublicParams, IVC},
    poseidon::{self, ROPair},
};

const ARITY: usize = BLOCK_SIZE / 2;

const CIRCUIT_TABLE_SIZE: usize = 20;
const COMMITMENT_KEY_SIZE: usize = 25;
const T: usize = 5;
const RATE: usize = 4;

type RandomOracle = poseidon::PoseidonRO<T, RATE>;

type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

type C1Affine = <C1 as halo2curves::group::prime::PrimeCurve>::Affine;
type C2Affine = <C2 as halo2curves::group::prime::PrimeCurve>::Affine;

type C1Scalar = <C1 as halo2curves::group::Group>::Scalar;
type C2Scalar = <C2 as halo2curves::group::Group>::Scalar;

fn main() {
    env_logger::init();
    log::info!("Start");
    // C1
    let sc1 = step_circuit::trivial::Circuit::<ARITY, _>::default();
    // C2
    let sc2 = step_circuit::trivial::Circuit::<ARITY, _>::default();

    let primary_spec = RandomOracleConstant::<<C2 as CurveExt>::Base>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<<C1 as CurveExt>::Base>::new(10, 10);

    let primary_commitment_key = CommitmentKey::setup(COMMITMENT_KEY_SIZE, b"primary");
    let secondary_commitment_key = CommitmentKey::setup(COMMITMENT_KEY_SIZE, b"secondary");

    let pp = PublicParams::<C1Affine, C2Affine, RandomOracle, RandomOracle>::new(
        CIRCUIT_TABLE_SIZE as u32,
        &primary_commitment_key,
        &secondary_commitment_key,
        primary_spec,
        secondary_spec,
        LIMB_WIDTH,
        LIMBS_COUNT_LIMIT,
    );
    info!("public params: {pp:?}");

    debug!("start ivc");
    let _ivc = IVC::new(
        &pp,
        sc1,
        array::from_fn(|i| C1Scalar::from_u128(i as u128)),
        sc2,
        array::from_fn(|i| C2Scalar::from_u128(i as u128)),
    )
    .unwrap();

    debug!("base case ready");
}
