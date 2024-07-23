use std::{fs, io::Write, path::Path};

use clap::Parser;
use halo2_proofs::{
    halo2curves::bn256::{self, Bn256, G1Affine},
    plonk,
    poly::kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG},
        multiopen::{ProverSHPLONK, VerifierSHPLONK},
        strategy::SingleStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
    SerdeFormat,
};
use rand_core::OsRng;
use tracing::*;

use crate::circuit::MerkleTreeUpdateCircuit;

type C1Scalar = bn256::Fr;
type C1Affine = bn256::G1Affine;

/// Approximately manually calculated number of lines needed for merkle-tree-circuit
/// Used to find the minimum required `k_table_size`
const ROWS: usize = 20838;

const FOLDER: &str = ".cache/examples";

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(long, default_value_t = 1)]
    repeat_count: usize,
    #[arg(long, default_value_t = false)]
    clean_cache: bool,
}

fn get_or_create_params(
    k_table_size: u32,
    path_params: &Path,
    clean_cache: bool,
) -> ParamsKZG<Bn256> {
    if path_params.exists() && !clean_cache {
        info!("load params from file");
        let mut file = fs::File::open(path_params).expect("failed to open the params file");
        ParamsKZG::<Bn256>::read_custom(&mut file, SerdeFormat::Processed)
            .expect("failed to deserialize the params")
    } else {
        info!("generate params");
        let params = ParamsKZG::<Bn256>::setup(k_table_size, OsRng);
        // Save the `params` bytes to a file
        let mut params_bytes = vec![];
        params
            .write_custom(&mut params_bytes, SerdeFormat::Processed)
            .expect("failed to serialize the params");
        fs::create_dir_all(path_params.parent().unwrap()).expect("failed to create directories");
        let mut file = fs::File::create(path_params).expect("failed to create the params file");
        file.write_all(&params_bytes)
            .expect("failed to write to the params file");
        params
    }
}

fn get_or_create_pk(
    k_table_size: u32,
    path_pk: &Path,
    clean_cache: bool,
    params: &ParamsKZG<Bn256>,
    circuit: &MerkleTreeUpdateCircuit<C1Scalar>,
) -> plonk::ProvingKey<C1Affine> {
    if path_pk.exists() && !clean_cache {
        info!("load pk from file");
        // Read the file and parse `pk` from it
        let mut file = fs::File::open(path_pk).expect("failed to open the pk file");
        plonk::pk_read::<_, _, MerkleTreeUpdateCircuit<C1Scalar>>(
            &mut file,
            SerdeFormat::Processed,
            k_table_size,
            circuit,
            true,
        )
        .expect("failed to deserialize the proving key")
    } else {
        info!("generate pk");
        let keygen = info_span!("keygen").entered();

        let pk = plonk::keygen_pk(
            params,
            plonk::keygen_vk(params, circuit).expect("keygen_vk should not fail"),
            circuit,
        )
        .expect("keygen_pk should not fail");

        // Save the `pk` bytes to a file
        fs::create_dir_all(path_pk.parent().unwrap()).expect("failed to create directories");
        let mut file = fs::File::create(path_pk).expect("failed to create the pk file");
        pk.write(&mut file, SerdeFormat::Processed).unwrap();

        keygen.exit();

        pk
    }
}

pub fn run(repeat_count: usize, clean_cache: bool) {
    info!("start merkle-circuit({repeat_count}) prove&verify with halo2-kzg");

    let k_table_size = (ROWS * repeat_count).next_power_of_two().ilog2();
    info!("k table size is {k_table_size}");

    let circuit = MerkleTreeUpdateCircuit::<C1Scalar>::new_with_random_updates(
        &mut rand::thread_rng(),
        repeat_count,
        1,
    );

    info!("circuit created");

    let _s = info_span!(
        "kzg",
        repeat_count = repeat_count,
        k_table_size = k_table_size
    )
    .entered();

    let cache = Path::new(FOLDER).join("merkle").join("kzg");

    // Setup
    let mut rng = rand::thread_rng();
    let params = get_or_create_params(
        k_table_size,
        &cache.join(format!("{}.params", repeat_count)),
        clean_cache,
    );

    let pk = get_or_create_pk(
        k_table_size,
        &cache.join(format!("{}.pk", repeat_count)),
        clean_cache,
        &params,
        &circuit,
    );

    let prove = info_span!("prove").entered();
    let instances = vec![vec![]];

    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    plonk::create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        instances.as_slice(),
        &mut rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();
    prove.exit();

    let verify = info_span!("verify").entered();

    // Verify
    let mut verifier_transcript =
        Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof.as_slice());
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(&verifier_params);

    plonk::verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<Bn256>, _, _, _>(
        &verifier_params,
        pk.get_vk(),
        strategy,
        instances.as_slice(),
        &mut verifier_transcript,
    )
    .expect("verify failed");

    verify.exit();

    info!("success");
}
