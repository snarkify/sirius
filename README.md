<h1 align="center">Sirius</h1>

>Sirius, renowned as the most luminous star in the night sky,
> deceives the naked eye by appearing as a solitary point of light when,
> in fact, it is a binary star system. Inspired by this duality,
> our project bears the name Sirius, capturing the essence of folded instances
> that give the illusion of being a singular entity.

Sirius is an open-source generic circuit folding framework. The goal is to achieve [Incrementally Verifiable Computation (IVC)](https://iacr.org/archive/tcc2008/49480001/49480001.pdf) for circuits written in various constrain systems: Plonk, R1CS and AIR. 

More precisely, $F$ is a function that accepts $z_{in}$ as input and $w$ as a private input. It produces an output $z_{out}$. Given the initial input $z_0$, the prover proves after applying step function $F$ $n$ times, the output is $z_n$.
<img width="855" alt="fig1" src="https://github.com/snarkify/sirius/assets/3767044/903002b6-e95e-4b7b-ac2c-525760995220">

This project is structured into three layers. The frontend layer accommodates constraint systems such as Plonk, R1CS, and AIR. The middle layer incorporates a folding scheme to accumulate the computation of n steps of $F$. Lastly, the backend layer utilizes polynomial IOP and polynomial commitment scheme to ensure the final verification is succinct and zero-knowledge.

The project is still in its early stage, and we use box color to indicate the current progress.
<img width="1017" alt="fig4" src="https://github.com/snarkify/sirius/assets/3767044/4aa58340-acda-48db-9170-3941645e7c26">



## Features
- [x] Supported frontend: [halo2](https://github.com/privacy-scaling-explorations/halo2) 
- [x] Folding scheme for plonk custom gates

## Features in progress
- [ ] IVC Circuit ![](https://geps.dev/progress/35)
- [ ] Folding scheme for lookup arguments ![](https://geps.dev/progress/50)
- [ ] [Protostar](https://eprint.iacr.org/2023/620) optimization for high degree gates

## Usage
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
