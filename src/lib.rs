#![allow(clippy::type_complexity)]
#![allow(unstable_name_collisions)]
#![allow(dead_code)] // TODO: remove it later
#![allow(non_snake_case)] // UPPER_CASE is used for ease of compatibility with Nova documentation

pub mod commitment;
pub mod constants;
pub mod digest;
pub mod fft;
pub mod gadgets;
pub mod ivc;
pub mod main_gate;
pub mod nifs;
pub mod plonk;
pub mod polynomial;
pub mod poseidon;
pub mod sps;
pub mod table;
pub mod util;

pub mod error;

pub use halo2_proofs::{
    self, halo2curves,
    halo2curves::{ff, group},
};

pub mod sangria_prelude {
    use std::num::NonZeroUsize;

    use crate::ff::{FromUniformBytes, PrimeFieldBits};
    pub use crate::{
        commitment::CommitmentKey,
        ff::{Field, PrimeField},
        ivc::{StepCircuit, SangriaIVC},
    };

    /// Within the IVC framework, on-circuit & off-circuit random oracle will be used
    ///
    /// This type defines this pair
    ///
    /// Only poiseidon is currently available
    pub type RandomOracle<const T: usize, const RATE: usize> = super::poseidon::PoseidonRO<T, RATE>;

    /// Within the IVC framework, on-circuit & off-circuit random oracle will be used
    ///
    /// This type defines constant what needed for create random oracle
    ///
    /// Only poiseidon is currently available
    pub type RandomOracleConstant<F, const T: usize, const RATE: usize> =
        <RandomOracle<T, RATE> as super::poseidon::ROPair<F>>::Args;

    /// The IVC uses big uint math on-circuit and this parameter allows you to configure
    /// the limb width of limb
    ///
    /// Safety: because 32 != 0
    pub const DEFAULT_LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };

    /// The IVC uses big uint math on-circuit and this parameter allows you to configure
    /// the maximum number of limbs allowed
    ///
    /// Safety: because 10 != 0
    pub const DEFAULT_LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    pub const DEFAULT_STEP_FOLDING_CIRCUIT_SIZE: usize = 5;
    pub const DEFAULT_RANDOM_ORACLE_SIZE: usize = 5;
    pub const DEFAULT_RANDOM_ORACLE_RATE: usize = DEFAULT_RANDOM_ORACLE_SIZE - 1;

    /// Create constants for random oracle, with R_F & R_P as defaults
    pub fn default_random_oracle_constant<F>(
    ) -> RandomOracleConstant<F, DEFAULT_STEP_FOLDING_CIRCUIT_SIZE, DEFAULT_RANDOM_ORACLE_RATE>
    where
        F: serde::Serialize + FromUniformBytes<64> + PrimeFieldBits,
    {
        /// Number of complete rounds
        const POSEIDON_DEFUALT_R_F: usize = 10;

        /// Number of partial rounds
        const POSEIDON_DEFAULT_R_P: usize = 10;

        RandomOracleConstant::new(POSEIDON_DEFUALT_R_F, POSEIDON_DEFAULT_R_P)
    }

    /// All imports and alias related to what will use bn256 & grumpkin as the first and second
    /// curve respectively
    pub mod bn256 {
        pub use bn256::G1;
        pub use grumpkin::G1 as G2;

        use crate::{
            commitment::CommitmentKey,
            halo2curves::{
                bn256,
                group::{prime::PrimeCurve, Group},
                grumpkin,
            },
            ivc::step_circuit::StepCircuit,
        };

        pub type C1Affine = <G1 as PrimeCurve>::Affine;
        pub type C2Affine = <G2 as PrimeCurve>::Affine;

        pub type C1Scalar = <G1 as Group>::Scalar;
        pub type C2Scalar = <G2 as Group>::Scalar;

        pub type PublicParams<'l, const A1: usize, C1, const A2: usize, C2> =
            crate::ivc::sangria::PublicParams<
                'l,
                A1,
                A2,
                { super::DEFAULT_STEP_FOLDING_CIRCUIT_SIZE },
                C1Affine,
                C2Affine,
                C1,
                C2,
                super::RandomOracle<
                    { super::DEFAULT_RANDOM_ORACLE_SIZE },
                    { super::DEFAULT_RANDOM_ORACLE_RATE },
                >,
                super::RandomOracle<
                    { super::DEFAULT_RANDOM_ORACLE_SIZE },
                    { super::DEFAULT_RANDOM_ORACLE_RATE },
                >,
            >;

        /// This function creates public parameters for IVC
        ///
        /// All values except the input are selected by default
        pub fn new_default_pp<'k, const A1: usize, C1, const A2: usize, C2>(
            primary_k_table_size: u32,
            primary_commitment_key: &'k CommitmentKey<C1Affine>,
            sc1: &C1,
            secondary_k_table_size: u32,
            secondary_commitment_key: &'k CommitmentKey<C2Affine>,
            sc2: &C2,
        ) -> PublicParams<'k, A1, C1, A2, C2>
        where
            C1: StepCircuit<A1, C1Scalar>,
            C2: StepCircuit<A2, C2Scalar>,
        {
            PublicParams::new(
                crate::ivc::sangria::CircuitPublicParamsInput::new(
                    primary_k_table_size,
                    primary_commitment_key,
                    super::default_random_oracle_constant(),
                    sc1,
                ),
                crate::ivc::sangria::CircuitPublicParamsInput::new(
                    secondary_k_table_size,
                    secondary_commitment_key,
                    super::default_random_oracle_constant(),
                    sc2,
                ),
                super::DEFAULT_LIMB_WIDTH,
                super::DEFAULT_LIMBS_COUNT_LIMIT,
            )
            .unwrap()
        }
    }

    /// All imports and alias related to what will use grumpkin & bn256 as the first and second
    /// curve respectively
    pub mod grumpkin {
        pub use bn256::G1 as G2;
        pub use grumpkin::G1;

        use crate::{
            commitment::CommitmentKey,
            halo2curves::{
                bn256,
                group::{prime::PrimeCurve, Group},
                grumpkin,
            },
            ivc::step_circuit::StepCircuit,
        };

        pub type C1Affine = <G1 as PrimeCurve>::Affine;
        pub type C2Affine = <G2 as PrimeCurve>::Affine;

        pub type C1Scalar = <G1 as Group>::Scalar;
        pub type C2Scalar = <G2 as Group>::Scalar;

        pub type PublicParams<'l, const A1: usize, C1, const A2: usize, C2> =
            crate::ivc::sangria::PublicParams<
                'l,
                A1,
                A2,
                { super::DEFAULT_STEP_FOLDING_CIRCUIT_SIZE },
                C1Affine,
                C2Affine,
                C1,
                C2,
                super::RandomOracle<
                    { super::DEFAULT_RANDOM_ORACLE_SIZE },
                    { super::DEFAULT_RANDOM_ORACLE_RATE },
                >,
                super::RandomOracle<
                    { super::DEFAULT_RANDOM_ORACLE_SIZE },
                    { super::DEFAULT_RANDOM_ORACLE_RATE },
                >,
            >;

        /// This function creates public parameters for IVC
        ///
        /// All values except the input are selected by default
        pub fn new_default_pp<'k, const A1: usize, C1, const A2: usize, C2>(
            primary_k_table_size: u32,
            primary_commitment_key: &'k CommitmentKey<C1Affine>,
            sc1: &C1,
            secondary_k_table_size: u32,
            secondary_commitment_key: &'k CommitmentKey<C2Affine>,
            sc2: &C2,
        ) -> PublicParams<'k, A1, C1, A2, C2>
        where
            C1: StepCircuit<A1, C1Scalar>,
            C2: StepCircuit<A2, C2Scalar>,
        {
            PublicParams::new(
                crate::ivc::sangria::CircuitPublicParamsInput::new(
                    primary_k_table_size,
                    primary_commitment_key,
                    super::default_random_oracle_constant(),
                    sc1,
                ),
                crate::ivc::sangria::CircuitPublicParamsInput::new(
                    secondary_k_table_size,
                    secondary_commitment_key,
                    super::default_random_oracle_constant(),
                    sc2,
                ),
                super::DEFAULT_LIMB_WIDTH,
                super::DEFAULT_LIMBS_COUNT_LIMIT,
            )
            .unwrap()
        }
    }
}
