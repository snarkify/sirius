//! NIFS: Non Interactive Folding Scheme
//!
//! NIFS protocal allow us to fold two identical polynomial relations into one
//! e.g. the polynomial relation can be derived from different way, e.g.:
//! - Custom plonkish gate
//! - The permutation polynomial derived from plonk copy constraints
//!
//! For more details look at:
//! - Paragraph '3. Folding scheme' at [Nova whitepaper](https://eprint.iacr.org/2021/370)
//! - [nifs module](https://github.com/microsoft/Nova/blob/main/src/nova/nifs.rs) at [Nova codebase](https://github.com/microsoft/Nova)

pub mod protogalaxy;
pub mod sangria;

#[cfg(test)]
pub(crate) mod tests;
