use std::{iter, num::NonZeroUsize};

use halo2_proofs::{arithmetic::CurveAffine, halo2curves::ff::PrimeFieldBits};
use poseidon::{self, SparseMDSMatrix};
use tracing::*;

use super::Spec;
use crate::{
    halo2curves::group::ff::{FromUniformBytes, PrimeField},
    poseidon::{ROConstantsTrait, ROTrait},
    util::{self, bits_to_fe_le, fe_to_bits_le},
};

// adapted from: https://github.com/privacy-scaling-explorations/snark-verifier

#[derive(Clone, Debug)]
struct State<F: PrimeField + FromUniformBytes<64>, const T: usize, const RATE: usize> {
    inner: [F; T],
}

impl<F: PrimeField + FromUniformBytes<64>, const T: usize, const RATE: usize> State<F, T, RATE> {
    fn new(inner: [F; T]) -> Self {
        Self { inner }
    }

    fn sbox_full(&mut self, constants: &[F; T]) {
        let pow5 = |v: &F| v.square() * v.square() * v;
        for (state, constant) in self.inner.iter_mut().zip(constants.iter()) {
            *state = pow5(state) + *constant;
        }
    }

    fn sbox_part(&mut self, constant: &F) {
        let pow5 = |v: &F| v.square() * v.square() * v;
        self.inner[0] = pow5(&self.inner[0]) + *constant;
    }

    fn pre_round(&mut self, inputs: &[F], pre_constants: &[F; T]) {
        assert!(RATE == T - 1);
        assert!(inputs.len() <= RATE);

        self.inner[0] += pre_constants[0];
        self.inner
            .iter_mut()
            .zip(pre_constants.iter())
            .skip(1)
            .zip(inputs)
            .for_each(|((state, constant), input)| {
                *state = *state + *input + *constant;
            });
        self.inner
            .iter_mut()
            .zip(pre_constants.iter())
            .skip(1 + inputs.len())
            .enumerate()
            .for_each(|(idx, (state, constant))| {
                *state = if idx == 0 {
                    *state + F::ONE + *constant
                } else {
                    *state + *constant
                };
            });
    }

    fn apply_mds(&mut self, mds: &[[F; T]; T]) {
        self.inner = mds
            .iter()
            .map(|row| {
                row.iter()
                    .clone()
                    .zip(self.inner.iter())
                    .fold(F::ZERO, |acc, (mij, sj)| acc + *sj * *mij)
            })
            .collect::<Vec<F>>()
            .try_into()
            .unwrap();
    }

    fn apply_sparse_mds(&mut self, mds: &SparseMDSMatrix<F, T, RATE>) {
        self.inner = iter::once(
            mds.row()
                .iter()
                .cloned()
                .zip(self.inner.iter())
                .fold(F::ZERO, |acc, (vi, si)| acc + vi * si),
        )
        .chain(
            mds.col_hat()
                .iter()
                .zip(self.inner.iter().skip(1))
                .map(|(coeff, state)| *coeff * self.inner[0] + *state),
        )
        .collect::<Vec<F>>()
        .try_into()
        .unwrap();
    }
}

impl<F, const T: usize, const RATE: usize> ROConstantsTrait for Spec<F, T, RATE>
where
    F: PrimeField + FromUniformBytes<64>,
{
    fn new(r_f: usize, r_p: usize) -> Self {
        Spec::new(r_f, r_p)
    }
}

impl<F: PrimeField, const T: usize, const RATE: usize> ROTrait<F> for PoseidonHash<F, T, RATE>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    type Constants = Spec<F, T, RATE>;

    fn new(constants: Self::Constants) -> Self {
        Self {
            spec: constants,
            state: State::new(poseidon::State::default().words()),
            buf: Vec::new(),
        }
    }

    fn absorb_field(&mut self, base: F) -> &mut Self {
        self.update(&[base]);
        self
    }

    fn absorb_point<C: CurveAffine>(&mut self, point: &C) -> &mut Self {
        let encoded = point.coordinates().map(|coordinates| {
            [coordinates.x(), coordinates.y()]
                .into_iter()
                .map(|v| util::fe_to_fe(v).unwrap())
                .collect::<Vec<_>>()
        });
        if bool::from(encoded.is_some()) {
            self.update(&encoded.unwrap())
        } else {
            self.update(&[F::ZERO, F::ZERO]) // C is infinity
        }

        self
    }

    fn inspect(&mut self, inspect: impl FnOnce(&[F])) -> &mut Self {
        inspect(&self.buf);
        self
    }

    #[instrument(skip_all)]
    fn squeeze<D: PrimeField>(&mut self, num_bits: NonZeroUsize) -> D {
        self.output::<D>(num_bits)
    }
}

#[derive(Clone, Debug)]
pub struct PoseidonHash<F: PrimeField, const T: usize, const RATE: usize>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    spec: Spec<F, T, RATE>,
    state: State<F, T, RATE>,
    buf: Vec<F>,
}

impl<F: PrimeField, const T: usize, const RATE: usize> PoseidonHash<F, T, RATE>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    fn update(&mut self, elements: &[F]) {
        self.buf.extend_from_slice(elements);
    }

    pub fn digest<F1: PrimeField>(
        spec: Spec<F, T, RATE>,
        elements: &[F],
        num_bits: NonZeroUsize,
    ) -> F1 {
        let mut s = Self::new(spec);
        s.update(elements);
        s.output(num_bits)
    }

    pub fn output<F1: PrimeField>(&mut self, num_bits: NonZeroUsize) -> F1 {
        let buf = self.buf.clone();

        debug!("Off circuit input of hash: {buf:?}");

        let exact = buf.len() % RATE == 0;

        for chunk in buf.chunks(RATE) {
            self.permutation(chunk);
        }
        if exact {
            self.permutation(&[]);
        }

        let output = self.state.inner[1];
        self.state = State::new(poseidon::State::default().words());

        let mut bits = fe_to_bits_le(&output);
        if bits.len() < num_bits.get() {
            bits.resize(num_bits.get(), false);
        }
        bits_to_fe_le(bits[..num_bits.get()].to_vec())
    }

    fn permutation(&mut self, inputs: &[F]) {
        let r_f = self.spec.r_f() / 2;
        let mds = self.spec.mds_matrices().mds().rows();
        let pre_sparse_mds = self.spec.mds_matrices().pre_sparse_mds().rows();
        let sparse_matrices = self.spec.mds_matrices().sparse_matrices();

        // First half of the full rounds
        let constants = self.spec.constants().start();
        self.state.pre_round(inputs, &constants[0]);
        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.state.sbox_full(constants);
            self.state.apply_mds(&mds);
        }
        self.state.sbox_full(constants.last().unwrap());
        self.state.apply_mds(&pre_sparse_mds);

        // Partial rounds
        let constants = self.spec.constants().partial();
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.state.sbox_part(constant);
            self.state.apply_sparse_mds(sparse_mds);
        }

        // Second half of the full rounds
        let constants = self.spec.constants().end();
        for constants in constants.iter() {
            self.state.sbox_full(constants);
            self.state.apply_mds(&mds);
        }
        self.state.sbox_full(&[F::ZERO; T]);
        self.state.apply_mds(&mds);
    }
}

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;
    use crate::halo2curves::pasta::{EpAffine, Fp, Fq};

    #[traced_test]
    #[test]
    fn test_poseidon_hash() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 4;
        const R_P: usize = 3;

        type PH = PoseidonHash<<EpAffine as CurveAffine>::Base, T, RATE>;

        let output = PH::new(Spec::<Fp, T, RATE>::new(R_F, R_P))
            .absorb_field_iter((0..5).map(|i| Fp::from(i as u64)))
            .squeeze::<<EpAffine as CurveAffine>::ScalarExt>(NonZeroUsize::new(128).unwrap());

        assert_eq!(
            output,
            Fq::from_str_vartime("277726250230731218669330566268314254439").unwrap()
        );
    }
}
