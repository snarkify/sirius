use halo2_proofs::plonk::{self, Circuit};
use some_to_err::*;
use tracing_test::traced_test;

use super::*;
use crate::{
    commitment,
    ff::{PrimeField, PrimeFieldBits},
    halo2curves::{
        bn256::{Fr, G1Affine},
        group::ff::FromUniformBytes,
    },
    nifs::{
        self,
        vanilla::{
            accumulator::{RelaxedPlonkInstance, RelaxedPlonkTrace, RelaxedPlonkWitness},
            VanillaFS,
        },
    },
    plonk::{PlonkStructure, PlonkTrace},
    table::CircuitRunner,
    util::create_ro,
};

#[derive(thiserror::Error, Debug)]
enum Error<C: CurveAffine> {
    #[error(transparent)]
    Nifs(#[from] nifs::vanilla::Error),
    #[error(transparent)]
    Plonk(#[from] plonk::Error),
    #[error("while verify: {errors:?}")]
    Verify {
        errors: Vec<(&'static str, crate::plonk::Error)>,
    },
    #[error("not equal: {from_verify:?} != {from_prove:?}")]
    VerifyProveNotMatch {
        from_verify: Box<RelaxedPlonkInstance<C>>,
        from_prove: Box<RelaxedPlonkInstance<C>>,
    },
}

impl<C: CurveAffine> Error<C> {
    fn check_equality(
        from_verify: &RelaxedPlonkInstance<C>,
        from_prove: &RelaxedPlonkInstance<C>,
    ) -> Result<(), Self> {
        from_verify
            .ne(from_prove)
            .then(|| Self::VerifyProveNotMatch {
                from_verify: Box::new(from_verify.clone()),
                from_prove: Box::new(from_prove.clone()),
            })
            .err_or(())
    }
}

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
    Error<C>,
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

    let td1 = CircuitRunner::new(K, circuit1, vec![public_inputs1.clone()]);
    let ck = commitment::setup_smallest_key(K, &td1.cs, b"prepare_trace");

    let S = td1.try_collect_plonk_structure()?;
    let W1 = td1.try_collect_witness()?;

    let td2 = CircuitRunner::new(K, circuit2, vec![public_inputs2.clone()]);
    let W2 = td2.try_collect_witness()?;

    let mut ro_nark_prepare = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_nark_decider = create_ro::<C::Base, T, RATE, R_F, R_P>();

    let (pp, _vp) = VanillaFS::setup_params(pp_digest, S.clone())?;

    let pair1 =
        VanillaFS::generate_plonk_trace(&ck, &[public_inputs1], &W1, &pp, &mut ro_nark_prepare)?;
    let pair1_relaxed = RelaxedPlonkTrace::from_regular(pair1.clone(), S.k);

    let pair2 =
        VanillaFS::generate_plonk_trace(&ck, &[public_inputs2], &W2, &pp, &mut ro_nark_prepare)?;
    let pair2_relaxed = RelaxedPlonkTrace::from_regular(pair2.clone(), S.k);

    let mut errors = Vec::new();

    if let Err(err) = S.is_sat(&ck, &mut ro_nark_decider, &pair1.u, &pair1.w) {
        errors.push(("is_sat_pair1", err));
    }
    if let Err(err) = VanillaFS::is_sat_permutation(&S, &pair1_relaxed) {
        errors.push(("is_sat_perm_pair1", err));
    }
    if let Err(err) = S.is_sat(&ck, &mut ro_nark_decider, &pair2.u, &pair2.w) {
        errors.push(("is_sat_pair2", err));
    }
    if let Err(err) = VanillaFS::is_sat_permutation(&S, &pair2_relaxed) {
        errors.push(("is_sat_perm_pair2", err));
    }

    if errors.is_empty() {
        Ok((ck, S, pair1, pair2))
    } else {
        Err(Error::Verify { errors })
    }
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
fn fold_instances<C, F1, F2>(
    ck: &CommitmentKey<C>,
    S: &PlonkStructure<F1>,
    pair1: PlonkTrace<C>,
    pair2: PlonkTrace<C>,
    pp_digest: C,
) -> Result<(), Error<C>>
where
    C: CurveAffine<ScalarExt = F1, Base = F2>,
    F1: PrimeField,
    F2: PrimeFieldBits + FromUniformBytes<64>,
{
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    let mut f_tr = RelaxedPlonkTrace {
        U: RelaxedPlonkInstance::new(2, S.num_challenges, S.round_sizes.len()),
        W: RelaxedPlonkWitness::new(S.k, &S.round_sizes),
    };

    let mut ro_nark_verifier = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_acc_prover = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_acc_verifier = create_ro::<C::Base, T, RATE, R_F, R_P>();

    let (pp, vp) = VanillaFS::setup_params(pp_digest, S.clone())?;

    let pair1 = [pair1];
    let (RelaxedPlonkTrace { U: U_from_prove, W }, cross_term_commits) =
        VanillaFS::prove(ck, &pp, &mut ro_acc_prover, f_tr.clone(), &pair1)?;

    let U_from_verify = VanillaFS::verify(
        &vp,
        &mut ro_nark_verifier,
        &mut ro_acc_verifier,
        &f_tr.U,
        &pair1.map(|p| p.u),
        &cross_term_commits,
    )?;
    Error::check_equality(&U_from_verify, &U_from_prove)?;

    f_tr.U = U_from_verify;
    f_tr.W = W;

    let mut errors = Vec::new();

    if let Err(err) = VanillaFS::is_sat(ck, S, &f_tr) {
        errors.extend(err.into_iter().map(|err| ("f_tr", err)));
    }

    let pair2 = [pair2];
    let (
        RelaxedPlonkTrace {
            U: U_from_prove,
            W: _W,
        },
        cross_term_commits,
    ) = VanillaFS::prove(
        ck,
        &pp,
        &mut ro_acc_prover,
        RelaxedPlonkTrace {
            U: f_tr.U.clone(),
            W: f_tr.W,
        },
        &pair2,
    )?;

    let U_from_verify = VanillaFS::verify(
        &vp,
        &mut ro_nark_verifier,
        &mut ro_acc_verifier,
        &f_tr.U,
        &pair2.map(|p| p.u),
        &cross_term_commits,
    )?;
    assert_eq!(U_from_prove, U_from_verify);

    f_tr.U = U_from_verify;
    f_tr.W = _W;

    if let Err(err) = VanillaFS::is_sat(ck, S, &f_tr) {
        errors.extend(err.into_iter().map(|err| ("f_tr", err)));
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(Error::Verify { errors })
    }
}

// test with single custom gate without lookup

use super::super::tests::{
    fibo_circuit::{get_fibo_seq, FiboCircuit},
    fibo_circuit_with_lookup::{get_sequence, FiboCircuitWithLookup},
    random_linear_combination_circuit::RandomLinearCombinationCircuit,
};

#[traced_test]
#[test]
fn zero_round_test() -> Result<(), Error<G1Affine>> {
    const K: u32 = 4;
    let inputs1 = (1..10).map(Fr::from).collect();
    let inputs2 = (2..11).map(Fr::from).collect();
    let circuit1 = RandomLinearCombinationCircuit::new(inputs1, Fr::from_u128(2));
    let output1 = Fr::from_u128(4097);
    let public_inputs1 = vec![output1];

    let circuit2 = RandomLinearCombinationCircuit::new(inputs2, Fr::from_u128(3));
    let output2 = Fr::from_u128(93494);
    let public_inputs2 = vec![output2];

    let (ck, S, pair1, pair2) = prepare_trace(
        K,
        circuit1,
        circuit2,
        public_inputs1,
        public_inputs2,
        G1Affine::default(),
    )?;
    fold_instances(&ck, &S, pair1, pair2, G1Affine::default())
}

#[traced_test]
#[test]
fn one_round_test() -> Result<(), Error<G1Affine>> {
    const K: u32 = 4;
    const SIZE: usize = 16;
    // circuit 1
    let seq = get_fibo_seq(1, 1, SIZE);
    let circuit1 = FiboCircuit {
        a: Fr::from(seq[0]),
        b: Fr::from(seq[1]),
        num: SIZE,
    };
    let public_inputs1 = vec![Fr::from(seq[SIZE - 1])];

    // circuit 2
    let seq = get_fibo_seq(2, 3, SIZE);
    let circuit2 = FiboCircuit {
        a: Fr::from(seq[0]),
        b: Fr::from(seq[1]),
        num: SIZE,
    };
    let public_inputs2 = vec![Fr::from(seq[SIZE - 1])];

    let (ck, S, pair1, pair2) = prepare_trace(
        K,
        circuit1,
        circuit2,
        public_inputs1,
        public_inputs2,
        G1Affine::default(),
    )?;
    fold_instances(&ck, &S, pair1, pair2, G1Affine::default())
}

#[traced_test]
#[test]
fn three_rounds_test() -> Result<(), Error<G1Affine>> {
    const K: u32 = 5;
    const NUM: usize = 7;

    // circuit 1
    let seq = get_sequence(1, 3, 2, NUM);
    let circuit1 = FiboCircuitWithLookup {
        a: Fr::from(seq[0]),
        b: Fr::from(seq[1]),
        c: Fr::from(seq[2]),
        num: NUM,
    };

    // circuit 2
    let seq = get_sequence(3, 2, 2, NUM);
    let circuit2 = FiboCircuitWithLookup {
        a: Fr::from(seq[0]),
        b: Fr::from(seq[1]),
        c: Fr::from(seq[2]),
        num: NUM,
    };

    let (ck, S, pair1, pair2) =
        prepare_trace(K, circuit1, circuit2, vec![], vec![], G1Affine::default())?;
    fold_instances(&ck, &S, pair1, pair2, G1Affine::default())
}
