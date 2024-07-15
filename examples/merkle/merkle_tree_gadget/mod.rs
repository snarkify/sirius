pub const T: usize = 16;
pub const RATE: usize = T - 1;

pub use sirius::{
    main_gate,
    poseidon::{PoseidonRO, ROPair},
};

pub type HasherChip<F> = <PoseidonRO<T, RATE> as ROPair<F>>::OnCircuit;
pub type Spec<F> = sirius::poseidon::Spec<F, T, RATE>;
pub type MainGateConfig = main_gate::MainGateConfig<T>;

pub mod chip;
pub mod off_circuit;
