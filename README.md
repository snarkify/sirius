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

# Roadmap
- [x] 2023Q4 - [halo2](https://github.com/privacy-scaling-explorations/halo2) frontend support
- [x] 2023Q4 - folding scheme for plonkish custom gates
- [x] 2023Q4 - folding scheme for lookup arguments
- [x] 2024Q1 - IVC circuit
- [x] 2024Q1 - IVC Benchmarks
- [ ] [2024Q2](https://github.com/snarkify/sirius/milestone/2) - high-degree gates optimization from [Protogalaxy](https://eprint.iacr.org/2023/1106)
- [ ] [2024Q3](https://github.com/snarkify/sirius/milestone/3) - IVC with cyclefold
- [ ] 2024Q3 - [Snarkify Cloud](https://cloud.snarkify.io/) integration and GPU acceleration
- [ ] 2024Q4 - Agg circuit
- [ ] 2024Q4 - IOP + PCS SNARK support ([Spartan](https://eprint.iacr.org/2019/550) / [Hyperplonk](https://eprint.iacr.org/2022/1355))
- [ ] 2025Q1 - on-chain verifier support

_The estimated timeline is subject to change_.

# Getting Started

## Install Rust

Use [rustup](https://rustup.rs/)

## Add dependency

```bash
cargo add --git https://github.com/snarkify/sirius.git --tag v0.1.0 sirius
```

## Implement `StepCircuit` trait

```rust
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

An example of using the API of IVC:
```rust
fn main() {
    let primary = poseidon_step_circuit::TestPoseidonCircuit::default();
    let secondary = step_circuit::trivial::Circuit::<ARITY2, _>::default();

    // Specifications for random oracle used as part of the IVC algorithm
    let primary_spec = RandomOracleConstant::<C1Scalar>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<C2Scalar>::new(10, 10);

    let primary_commitment_key = get_or_create_commitment_key::<C1Affine>(COMMITMENT_KEY_SIZE, "bn256");
    let secondary_commitment_key = get_or_create_commitment_key::<C2Affine>(COMMITMENT_KEY_SIZE, "grumpkin");

    let pp = PublicParams::<
        '_,
        ARITY1,
        ARITY2,
        MAIN_GATE_SIZE,
        C1Affine,
        C2Affine,
        TestPoseidonCircuit<_>,
        step_circuit::trivial::Circuit<ARITY, _>,
        RandomOracle,
        RandomOracle,
    >::new(
        CircuitPublicParamsInput::new(
            PRIMARY_CIRCUIT_TABLE_SIZE as u32,
            &primary_commitment_key,
            primary_spec,
            &primary,
        ),
        CircuitPublicParamsInput::new(
            SECONDARY_CIRCUIT_TABLE_SIZE as u32,
            &secondary_commitment_key,
            secondary_spec,
            &secondary,
        ),
        LIMB_WIDTH,
        LIMBS_COUNT,
    )
    .expect("failed to create public params");

    let primary_input = array::from_fn(|i| C1Scalar::from_u128(i as u128));
    let secondary_input = array::from_fn(|i| C2Scalar::from_u128(i as u128));
    let fold_step_count = NonZeroUsize::new(10).unwrap();

    IVC::fold(
        &pp,
        primary,
        primary_input,
        secondary,
        secondary_input,
        fold_step_count,
    )
    .expect("failed to run IVC");
}
```

This code will run `fold_step_count` of folding steps, and also check the proof after execution.

# Run examples

For runnable examples, please check [examples](examples) folder.

```bash
# Alias to run IVC with parameterization via cli arguments
cargo cli-example --help

# Alias for run the IVC for trivial `StepCircuit` (just returns its input unchanged)
cargo trivial-example

# Alias for run the IVC for the poseidon-circuit
cargo poseidon-example
```

# Time-Profiling 

Span lifetime tracking implemented, which allows you to understand in detail
how long a particular step takes to complete.

```bash
# By default, it will output all spans with a lifetime greater than 1s
cargo poseidon-example | python3 .scripts/build_profiling.py

# It is possible to specify the bottom border of the output span
cargo poseidon-example | python3 .scripts/build_profiling.py --min-runtime 0.1s

# You can also store logs and process them at a later date
cargo poseidon-example > log; cat log | python3 .scripts/build_profiling.py 
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

