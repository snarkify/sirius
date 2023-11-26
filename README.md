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
<img width="800" alt="fig2" src="https://github.com/snarkify/sirius/assets/3767044/c258e9e4-2ca0-4c7a-b153-5e7a98e5292f">
</p>

- **Frontend Layer**: This layer serves as the interface of the constraint system. User-defined circuits and witness data are converted into an intermediate representation format defined by the folding scheme. Our current implementation follows the _special-sound interactive protocol_ (SPS) from [Protostar](https://eprint.iacr.org/2023/620). An alternative scheme would be the _Customizable Constraint Systems protocol_ ([CCS](https://eprint.iacr.org/2023/552)). 
- **Folding Scheme Layer**: At the heart of the framework are the folding schemes IVC that accumulate the computations of multiple steps. At each step, the prover first calculates the instance-witness pairs from the previous step and folds them into the accumulator, then computes the cross terms and error vector for the folded instance-witness pairs. An IVC circuit then takes the outputs from the prover and performs the following steps: apply the step function `F`, fold the previous step's instance into the accumulator instance, and verify the inputs of the IVC circuit.
- **Backend Layer**: The backend leverages Polynomial Interactive Oracle Proofs (PIOP) and Polynomial Commitment Schemes (PCS) to generate zkSNARKs for succinct and zero-knowledge verification. Polynomial relation checks of the IVC decider are converted to the _multivariate sum-check protocol_. The evaluation phase of the sum-check protocol depends on the polynomial commitment scheme (PCS) we choose, e.g. [Hyrax](https://eprint.iacr.org/2017/1132.pdf). It is worth noting that when the polynomials are sparse, we can use the Spark compiler from [Spartan](https://eprint.iacr.org/2019/550) to handle them efficiently. 

# Roadmap
- [x] 2023Q4 - [halo2](https://github.com/privacy-scaling-explorations/halo2) frontend support
- [x] 2023Q4 - folding scheme for plonkish custom gates
- [ ] 2023Q4 - folding scheme for lookup arguments
- [ ] 2023Q4 - IVC circuit
- [ ] 2024Q1 - high-degree gate optimization from [Protostar](https://eprint.iacr.org/2023/620)
- [ ] 2024Q1 - [Snarkify Cloud](https://cloud.snarkify.io/) integration and GPU acceleration
- [ ] 2024Q2 - IOP + PCS backend support ([Spartan](https://eprint.iacr.org/2019/550) / [Hyperplonk](https://eprint.iacr.org/2022/1355))
- [ ] 2024Q3 - on-chain verifier support
- [ ] 2024Q3 - non-uniform circuit folding

_The estimated timeline is subject to change_.

# Getting Started
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

# Getting Involved

We'd love for you to be a part of our community!

If you're as enthusiastic about `Sirius` as we are, we invite you to join our developer community at Telegram. It's a great place to stay updated, get involved, and contribute to the project. Whether you're looking to contribute code, provide feedback, or simply stay in the loop, our Telegram group is the place to be.

:point_right: [Join our developer community](https://t.me/+oQ04SUgs6KMyMzlh)

Thank you for your interest in contributing to `Sirius`! :sparkles:

