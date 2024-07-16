use std::{fs, io::Write, path::Path};

use bn256::G1 as C1;
use clap::Parser;
use halo2_proofs::{
    halo2curves::bn256::{self, Bn256},
    plonk,
    poly::kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG},
        multiopen::{ProverGWC, VerifierGWC},
        strategy::SingleStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
    SerdeFormat,
};
use rand_core::OsRng;
use sirius::group::{prime::PrimeCurve, Group};
use tracing::*;

use crate::circuit::MerkleTreeUpdateCircuit;

type C1Scalar = <C1 as Group>::Scalar;
type C1Affine = <C1 as PrimeCurve>::Affine;

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
    path_pk: &Path,
    clean_cache: bool,
    params: &ParamsKZG<Bn256>,
    circuit: &MerkleTreeUpdateCircuit<C1Scalar>,
) -> plonk::ProvingKey<C1Affine> {
    if path_pk.exists() && !clean_cache {
        info!("load pk from file");
        // Read the file and parse `pk` from it
        let mut file = fs::File::open(path_pk).expect("failed to open the pk file");
        plonk::ProvingKey::read::<_, MerkleTreeUpdateCircuit<C1Scalar>>(
            &mut file,
            SerdeFormat::Processed,
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
        let pk_bytes = pk.to_bytes(SerdeFormat::Processed);
        fs::create_dir_all(path_pk.parent().unwrap()).expect("failed to create directories");
        let mut file = fs::File::create(path_pk).expect("failed to create the pk file");
        file.write_all(&pk_bytes)
            .expect("failed to write to the pk file");

        keygen.exit();

        pk
    }
}

pub fn run(repeat_count: usize, clean_cache: bool) {
    info!("start merkle-circuit prove&verify with halo2-kzg");

    let circuit = MerkleTreeUpdateCircuit::<C1Scalar>::new_with_random_updates(
        &mut rand::thread_rng(),
        repeat_count,
        1,
    );

    info!("circuit created");

    let k_table_size = (ROWS * repeat_count).next_power_of_two().ilog2();
    info!("k table size is {k_table_size}");

    let _span = info_span!("{repeat_count}_1_{k_table_size}",).entered();

    let cache = Path::new(FOLDER).join("kzg");

    let params = get_or_create_params(
        k_table_size,
        &cache.join(format!("{}.params", repeat_count)),
        clean_cache,
    );
    let pk = get_or_create_pk(
        &cache.join(format!("{}.pk", repeat_count)),
        clean_cache,
        &params,
        &circuit,
    );

    let prove = info_span!("prove").entered();

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    plonk::create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverGWC<'_, Bn256>,
        Challenge255<C1Affine>,
        OsRng,
        Blake2bWrite<Vec<u8>, C1Affine, Challenge255<_>>,
        _,
    >(&params, &pk, &[circuit], &[], OsRng, &mut transcript)
    .expect("proof generation should not fail");
    let proof = transcript.finalize();

    prove.exit();

    let verify = info_span!("verify").entered();
    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<&[u8], C1Affine, Challenge255<C1Affine>>::init(&proof[..]);

    assert!(plonk::verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierGWC<'_, Bn256>,
        Challenge255<C1Affine>,
        Blake2bRead<&[u8], C1Affine, Challenge255<C1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(&params, pk.get_vk(), strategy, &[], &mut transcript)
    .is_ok());

    verify.exit();
}
