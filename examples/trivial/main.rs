#![allow(dead_code)]

use std::{array, fs, io, num::NonZeroUsize, path::Path};

use ff::PrimeField;
use halo2_gadgets::sha256::BLOCK_SIZE;

use halo2curves::{bn256, grumpkin, CurveAffine, CurveExt};

use bn256::G1 as C1;
use grumpkin::G1 as C2;

use log::*;
use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit, CircuitPublicParamsInput, PublicParams, IVC},
    poseidon::{self, ROPair},
};

const ARITY: usize = BLOCK_SIZE / 2;

const CIRCUIT_TABLE_SIZE1: usize = 20;
const CIRCUIT_TABLE_SIZE2: usize = 20;
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

fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    const FOLDER: &str = ".cache/examples";

    let file_path = Path::new(FOLDER).join(label).join(format!("{k}.bin"));

    if file_path.exists() {
        debug!("{file_path:?} exists, load key");
        unsafe { CommitmentKey::load_from_file(&file_path, k) }
    } else {
        debug!("{file_path:?} not exists, start generate");
        let key = CommitmentKey::setup(k, label.as_bytes());
        fs::create_dir_all(file_path.parent().unwrap())?;
        unsafe {
            key.save_to_file(&file_path)?;
        }
        Ok(key)
    }
}

fn main() {
    env_logger::init();
    log::info!("Start");
    // C1
    let sc1 = step_circuit::trivial::Circuit::<ARITY, _>::default();
    // C2
    let sc2 = step_circuit::trivial::Circuit::<ARITY, _>::default();

    let primary_spec = RandomOracleConstant::<<C1 as CurveExt>::ScalarExt>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<<C2 as CurveExt>::ScalarExt>::new(10, 10);

    info!("Start generate");
    let primary_commitment_key = get_or_create_commitment_key(COMMITMENT_KEY_SIZE, "grumpkin")
        .expect("Failed to get primary key");
    info!("Primary generated");
    let secondary_commitment_key = get_or_create_commitment_key(COMMITMENT_KEY_SIZE, "bn256")
        .expect("Failed to get secondary key");
    info!("Secondary generated");

    let pp = PublicParams::<
        '_,
        ARITY,
        ARITY,
        T,
        C1Affine,
        C2Affine,
        step_circuit::trivial::Circuit<ARITY, _>,
        step_circuit::trivial::Circuit<ARITY, _>,
        RandomOracle,
        RandomOracle,
    >::new(
        CircuitPublicParamsInput {
            k_table_size: CIRCUIT_TABLE_SIZE1 as u32,
            commitment_key: &primary_commitment_key,
            ro_constant: primary_spec,
        },
        CircuitPublicParamsInput {
            k_table_size: CIRCUIT_TABLE_SIZE2 as u32,
            commitment_key: &secondary_commitment_key,
            ro_constant: secondary_spec,
        },
        LIMB_WIDTH,
        LIMBS_COUNT_LIMIT,
    )
    .unwrap();
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
