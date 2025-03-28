use std::{fmt, io, iter, marker::PhantomData, num::NonZeroUsize, ops::Deref};

use halo2_proofs::plonk;
use serde::Serialize;
use tracing::*;

use super::{
    super::{step_folding_circuit::StepParams, StepCircuit},
    consistency_markers_computation::ConsistencyMarkerComputation,
};
use crate::{
    commitment::CommitmentKey,
    constants::NUM_HASH_BITS,
    digest::{self, into_curve_from_bits, DigestToBits, DigestToCurve},
    ff::{Field, FromUniformBytes, PrimeFieldBits},
    group::prime::PrimeCurveAffine,
    halo2curves::CurveAffine,
    ivc::{
        self,
        step_folding_circuit::{StepFoldingCircuit, StepInputs},
    },
    main_gate::MainGateConfig,
    nifs::{
        self,
        sangria::{
            accumulator::FoldablePlonkTrace, GetConsistencyMarkers, VanillaFS,
            CONSISTENCY_MARKERS_COUNT,
        },
    },
    plonk::PlonkStructure,
    poseidon::{random_oracle::ROTrait, ROPair},
    table::CircuitRunner,
    util::ScalarToBase,
};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Plonk(#[from] plonk::Error),
    #[error("Error while calculate digest of pp")]
    WhileDigest(#[from] io::Error),
    #[error("While calculate intiail plonk relaxed trace of secondary circuit: {0:?}")]
    WhileGeneratePlonkTrace(#[from] nifs::sangria::Error),
    #[error("While calculate intiail plonk relaxed trace of secondary circuit, error was occured in `process_step`: {0:?}")]
    WhileProcessStep(#[from] ivc::step_circuit::SynthesisError),
}

#[derive(Serialize)]
pub struct CircuitPublicParams<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP>
where
    C: CurveAffine,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP: ROPair<C::Scalar>,
{
    S: PlonkStructure<C::Scalar>,
    #[serde(skip_serializing)]
    ck: &'key CommitmentKey<C>,
    params: StepParams<C::Scalar, RP::OnCircuit>,
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP>
    CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, RP>
where
    C: CurveAffine,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP: ROPair<C::Scalar>,
{
    pub fn k_table_size(&self) -> u32 {
        self.S.k as u32
    }
    pub fn ck(&self) -> &'key CommitmentKey<C> {
        self.ck
    }
    pub fn params(&self) -> &StepParams<C::Scalar, RP::OnCircuit> {
        &self.params
    }
    pub fn S(&self) -> &PlonkStructure<C::Scalar> {
        &self.S
    }
}

impl<const ARITY: usize, const MAIN_GATE_T: usize, C, RP> fmt::Debug
    for CircuitPublicParams<'_, ARITY, MAIN_GATE_T, C, RP>
where
    C: fmt::Debug + CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP: ROPair<C::Scalar>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CircuitPublicParams")
            .field("ck_len", &self.ck.len())
            .field("params", &self.params)
            .finish()
    }
}

impl<'key, const ARITY: usize, const MAIN_GATE_T: usize, C, RP>
    CircuitPublicParams<'key, ARITY, MAIN_GATE_T, C, RP>
where
    C: fmt::Debug + CurveAffine,
    C::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C::Scalar: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    RP: ROPair<C::Scalar, Config = MainGateConfig<MAIN_GATE_T>>,
{
    fn new(
        S: PlonkStructure<C::Scalar>,
        commitment_key: &'key CommitmentKey<C>,
        ro_constant: RP::Args,
        limb_width: NonZeroUsize,
        n_limbs: NonZeroUsize,
    ) -> Result<Self, Error> {
        let params = StepParams::new(limb_width, n_limbs, ro_constant);

        Ok(Self {
            S,
            ck: commitment_key,
            params,
        })
    }
}

#[derive(serde::Serialize)]
#[serde(bound(serialize = ""))]
pub struct PublicParams<
    'key,
    const A1: usize,
    const A2: usize,
    const MAIN_GATE_T: usize,
    C1,
    C2,
    SC1,
    SC2,
    RP1,
    RP2,
> where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    pub primary: CircuitPublicParams<'key, A1, MAIN_GATE_T, C1, RP1>,
    pub secondary: CircuitPublicParams<'key, A2, MAIN_GATE_T, C2, RP2>,
    _p: PhantomData<(SC1, SC2)>,

    #[serde(skip_serializing)]
    secondary_initial_plonk_trace: FoldablePlonkTrace<C2, { CONSISTENCY_MARKERS_COUNT }>,

    #[serde(skip_serializing)]
    digest_1: C1,
    #[serde(skip_serializing)]
    digest_2: C2,
}

impl<const A1: usize, const A2: usize, const MAIN_GATE_T: usize, C1, C2, SC1, SC2, RP1, RP2>
    fmt::Debug for PublicParams<'_, A1, A2, MAIN_GATE_T, C1, C2, SC1, SC2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
    C1: fmt::Debug,
    C2: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicParams")
            .field("primary", &self.primary)
            .field("secondary", &self.secondary)
            .finish()
    }
}

pub struct CircuitPublicParamsInput<
    'key,
    'circuit,
    const A: usize,
    C: CurveAffine,
    RPArgs,
    SC: StepCircuit<A, C::Scalar>,
> {
    step_circuit: &'circuit SC,
    commitment_key: &'key CommitmentKey<C>,
    k_table_size: u32,
    ro_constant: RPArgs,
}

impl<'key, 'circuit, const A: usize, C: CurveAffine, RPArgs, SC: StepCircuit<A, C::Scalar>>
    CircuitPublicParamsInput<'key, 'circuit, A, C, RPArgs, SC>
{
    pub fn new(
        k_table_size: u32,
        commitment_key: &'key CommitmentKey<C>,
        ro_constant: RPArgs,
        step_circuit: &'circuit SC,
    ) -> Self {
        Self {
            commitment_key,
            k_table_size,
            step_circuit,
            ro_constant,
        }
    }
}

impl<
        'key,
        const A1: usize,
        const A2: usize,
        const MAIN_GATE_T: usize,
        C1,
        C2,
        SC1,
        SC2,
        RP1,
        RP2,
    > PublicParams<'key, A1, A2, MAIN_GATE_T, C1, C2, SC1, SC2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,

    RP1: ROPair<C1::Scalar, Config = MainGateConfig<MAIN_GATE_T>>,
    RP2: ROPair<C2::Scalar, Config = MainGateConfig<MAIN_GATE_T>>,
{
    #[instrument(name = "pp_new", skip_all)]
    pub fn new(
        primary: CircuitPublicParamsInput<'key, '_, A1, C1, RP1::Args, SC1>,
        secondary: CircuitPublicParamsInput<'key, '_, A2, C2, RP2::Args, SC2>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        let primary_num_io = iter::once(CONSISTENCY_MARKERS_COUNT)
            .chain(primary.step_circuit.instances().iter().map(Vec::len))
            .collect::<Box<[_]>>();

        let secondary_num_io = iter::once(CONSISTENCY_MARKERS_COUNT)
            .chain(secondary.step_circuit.instances().iter().map(Vec::len))
            .collect::<Box<[_]>>();

        let primary_S = {
            let _primary_span = info_span!("primary").entered();

            let primary_step_params =
                StepParams::new(limb_width, limbs_count, primary.ro_constant.clone());

            let primary_sfc = StepFoldingCircuit::<'_, A1, C2, SC1, RP1::OnCircuit, MAIN_GATE_T> {
                step_circuit: primary.step_circuit,
                input: StepInputs::without_witness::<
                    StepFoldingCircuit<'_, A2, C1, SC2, RP2::OnCircuit, MAIN_GATE_T>,
                >(
                    primary.k_table_size,
                    &primary_num_io,
                    &secondary_num_io,
                    &primary_step_params,
                ),
            };
            let primary_instances =
                primary_sfc.instances([C1::Scalar::ZERO; CONSISTENCY_MARKERS_COUNT]);

            CircuitRunner::new(primary.k_table_size, primary_sfc, primary_instances)
                .try_collect_plonk_structure()
        }?;

        let (secondary_S, secondary_initial_plonk_trace) = {
            let _secondary_span = info_span!("secondary").entered();

            let secondary_initial_step_params =
                StepParams::new(limb_width, limbs_count, secondary.ro_constant.clone());

            let secondary_initial_step_input = StepInputs::without_witness::<
                StepFoldingCircuit<'_, A1, C2, SC1, RP1::OnCircuit, MAIN_GATE_T>,
            >(
                secondary.k_table_size,
                &secondary_num_io,
                &primary_num_io,
                &secondary_initial_step_params,
            );

            let secondary_consistenty_markers: [C2::Scalar; 2] = [
                C1::scalar_to_base(
                    &GetConsistencyMarkers::<CONSISTENCY_MARKERS_COUNT, _>::get_consistency_markers(
                        &secondary_initial_step_input.u,
                    )[1],
                )
                .unwrap(),
                ConsistencyMarkerComputation::<
                    '_,
                    A2,
                    C1,
                    RP2::OffCircuit,
                    { CONSISTENCY_MARKERS_COUNT },
                > {
                    random_oracle_constant: secondary.ro_constant.clone(),
                    public_params_hash: &secondary_initial_step_input.public_params_hash,
                    step: 1,
                    z_0: &secondary_initial_step_input.z_0,
                    z_i: &secondary
                        .step_circuit
                        .process_step(&secondary_initial_step_input.z_0, secondary.k_table_size)?,
                    relaxed: &secondary_initial_step_input.U.clone(),
                    limb_width,
                    limbs_count,
                }
                .generate_with_inspect(|buf| debug!("secondary X1 pp-new 0-step: {buf:?}")),
            ];

            let secondary_sfc = StepFoldingCircuit::<'_, A2, C1, SC2, RP2::OnCircuit, MAIN_GATE_T> {
                step_circuit: secondary.step_circuit,
                input: secondary_initial_step_input,
            };

            let secondary_instances = secondary_sfc.instances(secondary_consistenty_markers);
            let secondary_cr = CircuitRunner::new(
                secondary.k_table_size,
                secondary_sfc,
                secondary_instances.clone(),
            );

            let secondary_S = secondary_cr.try_collect_plonk_structure()?;
            let secondary_initial_plonk_trace =
                VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::generate_plonk_trace(
                    secondary.commitment_key,
                    &secondary_instances,
                    &secondary_cr.try_collect_witness()?,
                    &VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::setup_params(
                        C2::identity(),
                        secondary_S.clone(),
                    )?
                    .0,
                    &mut RP1::OffCircuit::new(primary.ro_constant.clone()),
                )?;

            Result::<_, Error>::Ok((secondary_S, secondary_initial_plonk_trace))
        }?;

        debug!("primary & secondary pp created");

        let mut self_ = Self {
            primary: CircuitPublicParams::new(
                primary_S,
                primary.commitment_key,
                primary.ro_constant,
                limb_width,
                limbs_count,
            )?,
            secondary: CircuitPublicParams::new(
                secondary_S,
                secondary.commitment_key,
                secondary.ro_constant,
                limb_width,
                limbs_count,
            )?,
            secondary_initial_plonk_trace,
            digest_1: C1::identity(),
            digest_2: C2::identity(),
            _p: PhantomData,
        };

        {
            let _primary_span = info_span!("digest").entered();
            let digest = digest::DefaultHasher::digest_to_bits(&self_)?;

            self_.digest_1 = into_curve_from_bits(digest.deref(), NUM_HASH_BITS);
            self_.digest_2 = into_curve_from_bits(digest.deref(), NUM_HASH_BITS);
        }

        Ok(self_)
    }

    pub fn secondary_initial_plonk_trace(
        &self,
    ) -> &FoldablePlonkTrace<C2, { CONSISTENCY_MARKERS_COUNT }> {
        &self.secondary_initial_plonk_trace
    }

    pub fn digest_1(&self) -> C1 {
        self.digest_1
    }

    pub fn digest_2(&self) -> C2 {
        self.digest_2
    }

    /// This method calculate digest of [`PublicParams`], but ignore [`CircuitPublicParams::ck`]
    /// from both step circuits params
    pub fn digest<C: CurveAffine>(&self) -> Result<C, io::Error> {
        digest::DefaultHasher::digest_to_curve(self)
    }
}

#[derive(Serialize)]
#[serde(bound(serialize = ""))]
pub(crate) struct PublicParamsDigestWrapper<'l, C1, C2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    primary_plonk_struct: PlonkStructure<C1::Scalar>,
    secondary_plonk_struct: PlonkStructure<C2::Scalar>,
    primary_params: &'l StepParams<C1::Scalar, RP1::OnCircuit>,
    secondary_params: &'l StepParams<C2::Scalar, RP2::OnCircuit>,
}

impl<C1, C2, RP1, RP2> PublicParamsDigestWrapper<'_, C1, C2, RP1, RP2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,

    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,

    RP1: ROPair<C1::Scalar>,
    RP2: ROPair<C2::Scalar>,
{
    pub fn digest<C: CurveAffine>(&self) -> Result<C, io::Error> {
        digest::DefaultHasher::digest_to_curve(self)
    }
}

#[cfg(test)]
mod pp_test {
    use std::{fs, path::Path};

    use bn256::G1 as C1;
    use grumpkin::G1 as C2;
    use tracing_test::traced_test;

    use super::*;
    use crate::{
        group::{prime::PrimeCurve, Group},
        halo2curves::{bn256, grumpkin},
        ivc::step_circuit::{self, trivial},
    };

    type C1Affine = <C1 as PrimeCurve>::Affine;
    type C2Affine = <C2 as PrimeCurve>::Affine;

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
    const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    type RandomOracle<const T: usize, const RATE: usize> = crate::poseidon::PoseidonRO<T, RATE>;

    type RandomOracleConstant<const T: usize, const RATE: usize, F> =
        <RandomOracle<T, RATE> as ROPair<F>>::Args;

    fn get_or_create_commitment_key<C: CurveAffine>(
        k: usize,
        label: &'static str,
    ) -> io::Result<CommitmentKey<C>> {
        const FOLDER: &str = ".cache/examples";

        let file_path = Path::new(FOLDER).join(label).join(format!("{k}.bin"));

        if file_path.exists() {
            debug!("{file_path:?} exists, load key");
            unsafe { CommitmentKey::load_from_file(&file_path, k) }
        } else {
            debug!("{file_path:?} not exists, start generate");
            let key = CommitmentKey::setup(k, label.as_bytes());
            fs::create_dir_all(file_path.parent().unwrap())?;
            unsafe {
                key.save_to_file(&file_path)?;
            }
            Ok(key)
        }
    }

    #[traced_test]
    #[test]
    fn digest() {
        type Scalar1 = <C1 as Group>::Scalar;
        type Scalar2 = <C2 as Group>::Scalar;

        let spec1 = RandomOracleConstant::<5, 4, Scalar1>::new(10, 10);
        let spec2 = RandomOracleConstant::<5, 4, Scalar2>::new(10, 10);

        const K: usize = 17;

        PublicParams::<
            '_,
            1,
            1,
            5,
            C1Affine,
            C2Affine,
            step_circuit::trivial::Circuit<1, Scalar1>,
            step_circuit::trivial::Circuit<1, Scalar2>,
            RandomOracle<5, 4>,
            RandomOracle<5, 4>,
        >::new(
            CircuitPublicParamsInput {
                step_circuit: &trivial::Circuit::default(),
                k_table_size: K as u32,
                commitment_key: &get_or_create_commitment_key(K + 3, "bn256").unwrap(),
                ro_constant: spec1,
            },
            CircuitPublicParamsInput {
                step_circuit: &trivial::Circuit::default(),
                k_table_size: K as u32,
                commitment_key: &get_or_create_commitment_key(K + 3, "grumpkin").unwrap(),
                ro_constant: spec2,
            },
            LIMB_WIDTH,
            LIMBS_COUNT_LIMIT,
        )
        .unwrap()
        .digest::<C1Affine>()
        .unwrap();
    }
}
