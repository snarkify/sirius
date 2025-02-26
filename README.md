<img width="200" alt="logo" src="https://github.com/snarkify/sirius/assets/3767044/6afd527d-1ff3-4a1f-886a-071060121c91">

> Sirius, renowned as the most luminous star in the night sky,
> deceives the naked eye by appearing as a solitary point of light when,
> in fact, it is a binary star system. Inspired by this duality,
> our project bears the name Sirius, capturing the essence of folded instances
> that give the illusion of being a singular entity.

# Introduction

Sirius is an open-source **Plonkish Folding Framework** for Incrementally Verifiable Computation [[IVC](https://iacr.org/archive/tcc2008/49480001/49480001.pdf)]. 

<p align="center">
<img width="500" alt="fig1" src="https://github.com/snarkify/sirius/assets/3767044/5adba269-ec82-45e2-9b05-427a05104553">
</p>


Within the context of an IVC scheme, the prover's role is to demonstrate that, upon consecutively applying a step function `F` exactly `n` times to an initial value $z_0$, the result is $z_n$. Here, the step function `F` takes two inputs $z_i$ and $w$, and yields an output $z_{i+1}$.

# Architecture

The `Sirius` folding framework is designed with a three-tiered architecture.

<p align="center">
<img width="800" alt="fig2" src="https://github.com/snarkify/sirius/assets/3767044/85381c56-053c-4399-8947-1509eec958bc">
</p>

- **Arithmetization Layer**: This layer serves as the interface of the constraint system. User-defined circuits and witness data are converted into an intermediate representation format defined by the folding scheme. Our current implementation follows the _special-sound interactive protocol_ (SPS) from [Protostar](https://eprint.iacr.org/2023/620).
- **Folding Scheme Layer**: At the heart of the framework is the folding scheme IVC circuit that accumulates the computations of multiple steps. At each step, the prover first calculates the instance-witness pairs from the previous step and folds them into the accumulator, then computes the cross terms and error vector for the folded instance-witness pairs. An IVC circuit then takes the outputs from the prover and performs the following steps: apply the step function `F`, fold the previous step's instance into the accumulator instance, and verify the inputs of the IVC circuit.
- **SNARK Layer**: The SNARK layer leverages Polynomial Interactive Oracle Proofs (PIOP) and Polynomial Commitment Schemes (PCS) to generate zkSNARKs for succinct and zero-knowledge verification. Polynomial relation checks of the IVC decider are converted to the _multivariate sum-check protocol_. The evaluation phase of the sum-check protocol depends on the polynomial commitment scheme (PCS) we choose, e.g. [Hyrax](https://eprint.iacr.org/2017/1132.pdf). It is worth noting that when the polynomials are sparse, we can use the Spark compiler from [Spartan](https://eprint.iacr.org/2019/550) to handle them efficiently. 

## Emerging Architectures for IVC

Sirius has evolved to support multiple IVC schemes that combine folding techniques with novel optimizations:

### Sangria

Sangria adapts Nova's folding scheme for the more flexible PLONKish arithmetization. By incorporating relaxed gate equations with a scaling factor `u` and an error vector `e`, Sangria supports custom gates and higher-arity circuits while managing the additional cross-terms introduced by higher-degree constraints.

### Cyclefold + Protogalaxy

Cyclefold represents a significant advancement in our folding scheme evolution. Its key insight is that folding-based recursive arguments can function without needing a full cycle of elliptic curves for every operation. Instead, Cyclefold delegates expensive non-native scalar multiplication and point addition operations to a compact "co-processor" circuit defined over a secondary elliptic curve. This dramatically reduces the size of the verifier circuit on the non-pairing-friendly curve and simplifies security reasoning.

While Cyclefold targets the efficiency of recursive proof composition, Protogalaxy NIFS focuses on optimizing high-degree gate constraints. In many PLONKish circuits, custom gates may have degrees higher than two—and naive folding would increase cryptographic work linearly with the degree. Protogalaxy NIFS introduces optimizations that reduce this overhead nearly to a constant cost per high-degree gate.

Together, these IVC schemes form the foundation of Sirius, offering different trade-offs between flexibility, efficiency, and security to meet diverse application needs.

# Roadmap
- [x] 2023Q4 - [halo2](https://github.com/privacy-scaling-explorations/halo2) frontend support
- [x] 2023Q4 - folding scheme for plonkish custom gates
- [x] 2023Q4 - folding scheme for lookup arguments
- [x] 2024Q1 - IVC circuit
- [x] 2024Q1 - IVC Benchmarks
- [x] [2024Q2](https://github.com/snarkify/sirius/milestone/2) - high-degree gates optimization from [Protogalaxy](https://eprint.iacr.org/2023/1106)
- [x] [2024Q3](https://github.com/snarkify/sirius/milestone/3) - IVC with cyclefold

_The estimated timeline is subject to change_.

# Getting Started

## Install Rust

Use [rustup](https://rustup.rs/)

## Add dependency

```bash
cargo add --git https://github.com/snarkify/sirius.git --tag v0.2.0 sirius
```

## Implement `StepCircuit` trait

```rust,no_run
use sirius::ff::PrimeField;
use sirius::ivc::step_circuit::{ConstraintSystem, Layouter, AssignedCell, SynthesisError};

/// To allow your circuit to be folded, impl this trait
/// `ARITY` - size of input & output
pub trait StepCircuit<const ARITY: usize, F: PrimeField> {
    type Config: Clone;
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config;
    /// This method represents step function `F: z_i -> z_{i+1}`
    ///
    /// Unlike `halo2::Circuit`, it takes array of assigned cells
    /// and returns array of assigned cells
    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_in: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError>;
}
``` 

## Setup and run `IVC` instance

For runnable examples, please check [examples](examples) folder.

Sirius supports multiple IVC schemes: **Sangria** & **Cyclefold**

### Run `Sangria IVC`

```rust,no_run
// Example showing how to use Sangria IVC
use std::{array, num::NonZeroUsize};
use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit::trivial, SangriaIVC},
    sangria_prelude::bn256::{new_default_pp, C1Affine, C1Scalar, C2Affine, C2Scalar},
    ff::Field,
};

// Example constants - in a real application, define these appropriately
const A1: usize = 5; // Arity for primary circuit
const A2: usize = 1; // Arity for secondary circuit
const PRIMARY_COMMITMENT_KEY_SIZE: usize = 21;
const SECONDARY_COMMITMENT_KEY_SIZE: usize = 21;
const PRIMARY_CIRCUIT_TABLE_SIZE: u32 = 17;
const SECONDARY_CIRCUIT_TABLE_SIZE: u32 = 17;

// Initialize your primary and secondary circuits
let sc1 = trivial::Circuit::<A1, C1Scalar>::default();
let sc2 = trivial::Circuit::<A2, C2Scalar>::default();

// Set up commitment keys
let primary_commitment_key =
    CommitmentKey::<C1Affine>::setup(PRIMARY_COMMITMENT_KEY_SIZE, b"bn256");
let secondary_commitment_key =
    CommitmentKey::<C2Affine>::setup(SECONDARY_COMMITMENT_KEY_SIZE, b"grumpkin");

// Set up public parameters with helper function
let pp = new_default_pp::<A1, _, A2, _>(
    SECONDARY_CIRCUIT_TABLE_SIZE,
    &primary_commitment_key,
    &sc1,
    PRIMARY_CIRCUIT_TABLE_SIZE,
    &secondary_commitment_key,
    &sc2,
);

SangriaIVC::fold_with_debug_mode(
    &pp,
    &sc1,
    array::from_fn(|i| C1Scalar::from(i as u64)),
    &sc2,
    array::from_fn(|i| C2Scalar::from(i as u64)),
    NonZeroUsize::new(10).unwrap(), // fold step count
)
.unwrap();
```

### Run `Cyclefold IVC`

```rust,no_run
// Example showing how to use Cyclefold IVC
use std::array;
use sirius::{
    commitment::CommitmentKey,
    ivc::step_circuit::trivial,
    cyclefold_prelude::{
        bn256::{C1Affine, C1Scalar, C2Affine},
        PublicParams, IVC,
    },
    ff::Field,
};

// Example constants - in a real application, define these appropriately
const A1: usize = 5; // Arity for circuit
const PRIMARY_COMMITMENT_KEY_SIZE: usize = 21;
const SECONDARY_COMMITMENT_KEY_SIZE: usize = 21;
const PRIMARY_CIRCUIT_TABLE_SIZE: u32 = 17;

// Initialize your circuit (only one needed)
let sc = trivial::Circuit::<A1, C1Scalar>::default();

// Set up commitment keys
let primary_commitment_key =
    CommitmentKey::<C1Affine>::setup(PRIMARY_COMMITMENT_KEY_SIZE, b"bn256");
let secondary_commitment_key =
    CommitmentKey::<C2Affine>::setup(SECONDARY_COMMITMENT_KEY_SIZE, b"grumpkin");

// Set up public parameters
let mut pp = PublicParams::new(
    &sc,
    primary_commitment_key,
    secondary_commitment_key,
    PRIMARY_CIRCUIT_TABLE_SIZE,
)
.unwrap();

// Initialize IVC, run one step, and verify
IVC::new(&mut pp, &sc, array::from_fn(|_| C1Scalar::ZERO))
    .expect("while step=0")
    .next(&pp, &sc)
    .expect("while step=1")
    .verify(&pp)
    .expect("while verify");
```

Both examples show how to initialize and run IVC instances. The Cyclefold scheme is simpler as it requires only one circuit, while Sangria uses a two-circuit approach. The examples demonstrate setting up commitment keys, creating public parameters, and running computation steps with verification.

# Run examples

For runnable examples, please check [examples](examples) folder.

```bash
# 're' is short for 'run example'

# Alias to run IVC with parameterization via cli arguments
cargo re-cli --help

# Alias for run the IVC for trivial `StepCircuit` (just returns its input unchanged)
cargo re-trivial

# Alias for run the IVC for the poseidon-circuit
cargo re-poseidon
```

# Time-Profiling 

Span lifetime tracking implemented, which allows you to understand in detail
how long a particular step takes to complete.

```bash
# 're' is short for 'run example'

# By default, it will output all spans with a lifetime greater than 1s
cargo re-poseidon | python3 .scripts/build_profiling.py

# It is possible to specify the bottom border of the output span
cargo re-poseidon | python3 .scripts/build_profiling.py --min-runtime 0.1s

# You can also store logs and process them at a later date
cargo re-poseidon > log; cat log | python3 .scripts/build_profiling.py 
```

# Memory-Profiling 
The [dhat](https://valgrind.org/docs/manual/dh-manual.html) utility and the [dhat-rs](https://github.com/nnethercote/dhat-rs) experimental crate are used

```bash
# Run dhat with default IVC (poseidon+trivial)
cargo cli-dhat

# Check available params of run
cargo cli-dhat --help
```

# Benchmark 

For benches, please check [benches](benches) folder.

```bash
cargo bench
```

## Criterion
You can also get a more detailed report. Please check for info [criterion.rs](https://github.com/bheisler/criterion.rs)

```bash
cargo criterion
```

# Getting Involved

We'd love for you to be a part of our community!

If you're as enthusiastic about `Sirius` as we are, we invite you to join our developer community at Telegram. It's a great place to stay updated, get involved, and contribute to the project. Whether you're looking to contribute code, provide feedback, or simply stay in the loop, our Telegram group is the place to be.

:point_right: [Join our developer community](https://t.me/+oQ04SUgs6KMyMzlh)

Thank you for your interest in contributing to `Sirius`! :sparkles:

