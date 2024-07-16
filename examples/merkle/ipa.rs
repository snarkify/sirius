use bn256::G1 as C1;
use halo2_proofs::{
    plonk,
    poly::{
        commitment::ParamsProver,
        ipa::{
            commitment::{IPACommitmentScheme, ParamsIPA},
            multiopen::ProverIPA,
            strategy::SingleStrategy,
        },
        VerificationStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use rand_core::OsRng;
use sirius::{
    self,
    group::{prime::PrimeCurve, Group},
    halo2curves::bn256,
};
use tracing::*;

use crate::circuit::MerkleTreeUpdateCircuit;

type C1Affine = <C1 as PrimeCurve>::Affine;
type C1Scalar = <C1 as Group>::Scalar;

/// Approximately manually calculated number of lines needed for merkle-tree-circuit
/// Used to find the minimum required `k_table_size`
const ROWS: usize = 20838;

pub fn run(repeat_count: usize) {
    info!("start merkle-circuit prove&verify with halo2-ipa");
    let circuit = MerkleTreeUpdateCircuit::<C1Scalar>::new_with_random_updates(
        &mut rand::thread_rng(),
        repeat_count,
        1,
    );

    info!("circuit created");

    let k_table_size = (ROWS * repeat_count).next_power_of_two().ilog2();
    info!("k table size is {k_table_size}");

    let keygen = info_span!("keygen").entered();

    let params: ParamsIPA<C1Affine> = ParamsIPA::<C1Affine>::new(k_table_size);
    let vk = plonk::keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = plonk::keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");

    keygen.exit();

    let prove = info_span!("prove").entered();

    let mut transcript = Blake2bWrite::<_, C1Affine, Challenge255<_>>::init(vec![]);
    plonk::create_proof::<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[(&[])],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();

    prove.exit();

    let verify = info_span!("verify").entered();

    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    let strategy = SingleStrategy::new(&params);
    plonk::verify_proof(&params, pk.get_vk(), strategy, &[(&[])], &mut transcript).unwrap();

    verify.exit();
}
