use halo2curves::group::ff::{FromUniformBytes, PrimeField};
use poseidon::{self, SparseMDSMatrix, Spec};
use std::{iter, mem};

// adapted from: https://github.com/privacy-scaling-explorations/snark-verifier

#[derive(Clone, Debug)]
struct State<F: PrimeField+FromUniformBytes<64>, const T: usize, const RATE: usize> {
    inner: [F; T],
}

impl<F: PrimeField+FromUniformBytes<64>, const T: usize, const RATE: usize> State<F, T, RATE> {
    fn new(inner: [F; T]) -> Self {
        Self {
            inner,
        }
    }

    fn sbox_full(&mut self, constants: &[F; T]) {
        let pow5 = |v: &F| { 
           v.square() * v.square() * v
        };
        for (state, constant) in self.inner.iter_mut().zip(constants.iter()) {
            *state = pow5(state) + *constant; 
        }
    }

    fn sbox_part(&mut self, constant: &F) {
        let pow5 = |v: &F| { v.square() * v.square() * v};
        self.inner[0] = pow5(&self.inner[0]) + *constant;
    }

    fn pre_round(&mut self, inputs: &[F], pre_constants: &[F; T]) {
        assert!(RATE == T - 1);
        assert!(inputs.len() <= RATE);

        self.inner[0] = self.inner[0] + pre_constants[0];
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
                *state = if idx == 0 { *state + F::ONE + *constant } else { *state + *constant };
            });
    }

    fn apply_mds(&mut self, mds: &[[F; T]; T]) {
        self.inner = mds
            .iter()
            .map(|row| {
                row.iter().clone().zip(self.inner.iter()).fold(F::ZERO, |acc, (mij, sj)| {
                    acc + *sj * *mij
                })
            })
            .collect::<Vec<F>>().try_into().unwrap();
    }

    fn apply_sparse_mds(&mut self, mds: &SparseMDSMatrix<F, T, RATE>) {
        self.inner = iter::once(
              mds.row()
              .iter()
              .cloned()
              .zip(self.inner.iter())
              .fold(F::ZERO, |acc, (vi, si)|{
                  acc + vi * si
              })
            )
        .chain(
            mds.col_hat()
            .iter()
            .zip(self.inner.iter().skip(1))
            .map(|(coeff, state)| {
                *coeff * self.inner[0] + *state
            }),
        )
       .collect::<Vec<F>>()
       .try_into()
       .unwrap();
    }
}


#[derive(Clone, Debug)]
pub struct PoseidonHash<F: PrimeField+FromUniformBytes<64>, const T: usize, const RATE: usize> {
    spec: Spec<F, T, RATE>,
    state: State<F, T, RATE>,
    buf: Vec<F>,
}

impl<F: PrimeField+FromUniformBytes<64>, const T: usize, const RATE: usize> PoseidonHash<F, T, RATE> {
    pub fn new(r_f: usize, r_p: usize) -> Self {
        Self {
            spec: Spec::new(r_f, r_p),
            state: State::new(
                poseidon::State::default()
                    .words()
            ),
            buf: Vec::new(),
        }
    }

    pub fn update(&mut self, elements: &[F]) {
        self.buf.extend_from_slice(elements);
    }

    pub fn squeeze(&mut self) -> F {
        let buf = mem::take(&mut self.buf);
        let exact = buf.len() % RATE == 0;

        for chunk in buf.chunks(RATE) {
            self.permutation(chunk);
        }
        if exact {
            self.permutation(&[]);
        }

        self.state.inner[1].clone()
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
    use super::*;
    use halo2curves::pasta::Fp;

    #[test]
    fn test_poseidon_hash() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 4;
        const R_P: usize = 3;
        type PH = PoseidonHash<Fp, T, RATE>;
        let mut poseidon = PH::new(R_F, R_P);
        let mut input = Vec::new();
        for i in 0..5 {
            input.push(Fp::from(i as u64));
        }
        poseidon.update(&input[..]);
        let output = poseidon.squeeze();
        // hex = 0x1cd3150d8e12454ff385da8a4d864af6d0f021529207b16dd6c3d8f2b52cfc67
        let out_hash = Fp::from_str_vartime("13037709793114148810823325920380362524528554380279235267325741570708489436263").unwrap();
        println!("output = {:?}", output);
        assert_eq!(output, out_hash);
    }
}
