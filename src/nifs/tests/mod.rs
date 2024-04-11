use ff::{PrimeField, PrimeFieldBits};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};
use halo2curves::bn256::{Fr, G1Affine};
use halo2curves::group::ff::FromUniformBytes;
use std::marker::PhantomData;
use tracing::*;

use crate::nifs::{vanilla::VanillaFS, Error as NIFSError};
use crate::plonk::{
    PlonkStructure, PlonkTrace, RelaxedPlonkInstance, RelaxedPlonkTrace, RelaxedPlonkWitness,
};
use crate::table::CircuitRunner;
use crate::util::create_ro;

use super::*;

#[instrument(name = "prepare trace", skip_all)]
fn prepare_trace<C, F1, F2, CT>(
    K: u32,
    circuit1: CT,
    circuit2: CT,
    public_inputs1: Vec<F1>,
    public_inputs2: Vec<F1>,
    pp_digest: C,
) -> Result<
    (
        CommitmentKey<C>,
        PlonkStructure<F1>,
        PlonkTrace<C>,
        PlonkTrace<C>,
    ),
    NIFSError,
>
where
    C: CurveAffine<ScalarExt = F1, Base = F2>,
    F1: PrimeField,
    F2: PrimeFieldBits + FromUniformBytes<64>,
    CT: Circuit<F1>,
{
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    let td1 = CircuitRunner::new(K, circuit1, public_inputs1.clone());
    let num_lookup = td1.cs.lookups().len();
    let p1 = smallest_power(td1.cs.num_advice_columns() + 5 * num_lookup, K);
    let p2 = smallest_power(td1.cs.num_selectors() + td1.cs.num_fixed_columns(), K);
    let ck = CommitmentKey::<C>::setup(p1.max(p2), b"prepare_trace");

    let S = td1.try_collect_plonk_structure()?;
    let W1 = td1.try_collect_witness()?;

    let td2 = CircuitRunner::new(K, circuit2, public_inputs2.clone());
    let W2 = td2.try_collect_witness()?;

    let mut ro_nark_prepare = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_nark_decider = create_ro::<C::Base, T, RATE, R_F, R_P>();

    let (pp, _vp) = VanillaFS::setup_params(pp_digest, S.clone())?;
    let pair1 =
        VanillaFS::generate_plonk_trace(&ck, &public_inputs1, &W1, &pp, &mut ro_nark_prepare)?;
    assert_eq!(
        S.is_sat(&ck, &mut ro_nark_decider, &pair1.u, &pair1.w)
            .err(),
        None
    );
    let pair1_relaxed = pair1.to_relax(S.k);
    assert_eq!(
        S.is_sat_perm(&pair1_relaxed.U, &pair1_relaxed.W).err(),
        None
    );
    let pair2 =
        VanillaFS::generate_plonk_trace(&ck, &public_inputs2, &W2, &pp, &mut ro_nark_prepare)?;
    assert_eq!(
        S.is_sat(&ck, &mut ro_nark_decider, &pair2.u, &pair2.w)
            .err(),
        None
    );
    let pair2_relaxed = pair2.to_relax(S.k);
    assert_eq!(
        S.is_sat_perm(&pair2_relaxed.U, &pair2_relaxed.W).err(),
        None
    );

    Ok((ck, S, pair1, pair2))
}

/// this function will fold two plonk witness-instance pairs consecutively
/// it folds the first instance into a default relaxed plonk instance to get folded (f_U, f_W)
/// next it folds the second instance into the first folded (f_U, f_W)
/// there are several things to be checked: whether two such instances satisfy plonk relation
/// (i.e. is_sat), whether two such folded instance satisfy relaxed plonk relation (i.e.
/// is_sat_relax)
/// We have to check:
/// (1) each of the two individual witness-instance pairs satisfy custom gates relation as well
/// as copy constrains relation (i.e. permutation relation)
/// (2) the first folded witness-instance pair satisfies the relaxed polynomial relation and
/// copy constrains relation
/// (3) the second folded witness-instance pair satisfies the relaxed polynomial relation  and
/// copy constrains relation
#[instrument(name = "fold_instances", skip_all)]
fn fold_instances<C, F1, F2>(
    ck: &CommitmentKey<C>,
    S: &PlonkStructure<F1>,
    pair1: &PlonkTrace<C>,
    pair2: &PlonkTrace<C>,
    pp_digest: C,
) -> Result<(), NIFSError>
where
    C: CurveAffine<ScalarExt = F1, Base = F2>,
    F1: PrimeField,
    F2: PrimeFieldBits + FromUniformBytes<64>,
{
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    let mut f_U = RelaxedPlonkInstance::new(S.num_io, S.num_challenges, S.round_sizes.len());
    let mut f_W = RelaxedPlonkWitness::new(S.k, &S.round_sizes);

    let mut ro_nark_verifier = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_acc_prover = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_acc_verifier = create_ro::<C::Base, T, RATE, R_F, R_P>();

    let (pp, vp) = VanillaFS::setup_params(pp_digest, S.clone())?;

    let (RelaxedPlonkTrace { U: U_from_prove, W }, cross_term_commits) = VanillaFS::prove(
        ck,
        &pp,
        &mut ro_acc_prover,
        &RelaxedPlonkTrace {
            U: f_U.clone(),
            W: f_W.clone(),
        },
        pair1,
    )?;

    let U_from_verify = VanillaFS::verify(
        &vp,
        &mut ro_nark_verifier,
        &mut ro_acc_verifier,
        &f_U,
        &pair1.u,
        &cross_term_commits,
    )
    .unwrap();
    assert_eq!(U_from_prove, U_from_verify);

    f_U = U_from_verify;
    f_W = W;
    assert_eq!(S.is_sat_relaxed(ck, &f_U, &f_W), Ok(()));
    assert_eq!(S.is_sat_perm(&f_U, &f_W), Ok(()));

    let (
        RelaxedPlonkTrace {
            U: U_from_prove,
            W: W_from_prove,
        },
        cross_term_commits,
    ) = VanillaFS::prove(
        ck,
        &pp,
        &mut ro_acc_prover,
        &RelaxedPlonkTrace {
            U: f_U.clone(),
            W: f_W,
        },
        pair2,
    )?;

    let U_from_verify = VanillaFS::verify(
        &vp,
        &mut ro_nark_verifier,
        &mut ro_acc_verifier,
        &f_U,
        &pair2.u,
        &cross_term_commits,
    )
    .unwrap();
    assert_eq!(U_from_prove, U_from_verify);

    f_U = U_from_verify;
    f_W = W_from_prove;
    assert_eq!(S.is_sat_perm(&f_U, &f_W), Ok(()));
    assert_eq!(S.is_sat_relaxed(ck, &f_U, &f_W), Ok(()));

    Ok(())
}

/// calculate smallest w such that 2^w >= n*(2^K)
fn smallest_power(n: usize, K: u32) -> usize {
    let n_f64 = n as f64;
    let mul_res = n_f64 * (2f64.powi(K as i32));
    let log_result = mul_res.log2().ceil();
    log_result as usize
}

// test with single custom gate without lookup
mod zero_round_test;

// test multiple gates without lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
mod one_round_test;

// test vector lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
mod three_rounds_test;
