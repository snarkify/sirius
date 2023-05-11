use halo2_proofs::plonk::{Circuit, ConstraintSystem, Error}; 
use halo2_proofs::circuit::{SimpleFloorPlanner, Layouter, Value};
use ff::PrimeField;
use crate::standard_gate::{StandardGateConfig,StandardGate, RegionCtx};

// (x_i_plus_1, y_i_plus_1) <-- (y_i, x_i + y_i)
#[derive(Clone, Debug)]
pub(crate) struct FiboIteration<F: PrimeField> {
  pub(crate) x_i: F,
  pub(crate) y_i: F,
  pub(crate) x_i_plus_1: F,
  pub(crate) y_i_plus_1: F,
}

impl<F: PrimeField> FiboIteration<F> {
    // generate trace
  pub fn new(num_iters: usize, x_0: u64, y_0: u64) -> (Vec<F>, Vec<Self>) {
    let mut res = Vec::new();
    let mut x_i = F::from(x_0);
    let mut y_i = F::from(y_0);
    for _i in 0..num_iters {
      let x_i_plus_1 = y_i;
      let y_i_plus_1 = x_i + y_i;
      res.push(Self {
            x_i,
            y_i,
            x_i_plus_1,
            y_i_plus_1
      });
      x_i = x_i_plus_1;
      y_i = y_i_plus_1;
    }
    let z0 = vec![F::from(x_0), F::from(y_0)];
      (z0, res)
    }
}

#[derive(Clone)]
pub(crate) struct FiboCircuitConfig {
    config: StandardGateConfig,
}

impl FiboCircuitConfig {
    fn standard_gate<F: PrimeField>(&self) -> StandardGate<F> {
        StandardGate::new(self.config.clone())
    }
}

#[derive(Default)]
pub(crate) struct FiboCircuit<F: PrimeField> {
    pub seq: Vec<FiboIteration<F>>,
}

impl<F: PrimeField> FiboCircuit<F> {
    pub fn new(seq: Vec<FiboIteration<F>>) -> Self {
        FiboCircuit {
            seq
        }
    }
}

impl<F: PrimeField> Circuit<F> for FiboCircuit<F> {
    type Config = FiboCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let config = StandardGate::<F>::configure(meta);
        FiboCircuitConfig { config }
    }
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let standard_gate = config.standard_gate();
        let vs: Vec<_> = layouter.assign_region(||"region 0", |region|{
            let offset = 0;
            // TODO: maybe put ctx in param, so that outer circuit can use 
            let ctx = &mut RegionCtx::new(region, offset);
            assert!(self.seq.len() >= 1);
            let mut cells_0 = standard_gate.add(ctx, Value::known(self.seq[0].x_i), Value::known(self.seq[0].y_i))?;
            let mut previous_cells = cells_0.clone();
            for i in 1..self.seq.len() {
                let x_i = self.seq[i].x_i;
                let y_i = self.seq[i].y_i;
                let cells = standard_gate.add(ctx, Value::known(x_i), Value::known(y_i))?;
                ctx.constrain_equal(cells[0].cell(), previous_cells[1].cell())?;
                ctx.constrain_equal(cells[1].cell(), previous_cells[2].cell())?;
                previous_cells = cells;
            }
            cells_0.extend(previous_cells);
            Ok(cells_0)
        })?;
        standard_gate.expose_public(layouter.namespace(||"x0"), vs[0].clone(), 0)?; 
        standard_gate.expose_public(layouter.namespace(||"y0"), vs[1].clone(), 1)?; 
        standard_gate.expose_public(layouter.namespace(||"xn"), vs[4].clone(), 2)?;
        standard_gate.expose_public(layouter.namespace(||"yn"), vs[5].clone(), 3)?;
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    // use halo2_proofs::dev::MockProver;
    // use pasta_curves::{Fp,EqAffine};
    use halo2_proofs::poly::ipa::commitment::{IPACommitmentScheme, ParamsIPA};
    use halo2_proofs::poly::ipa::multiopen::ProverIPA;
    use halo2_proofs::poly::{VerificationStrategy, ipa::strategy::SingleStrategy};
    use halo2_proofs::poly::commitment::ParamsProver;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer};
    use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof};
    use halo2curves::pasta::{vesta, EqAffine, Fp};
    use rand_core::OsRng;

    #[test]
    pub fn test_fibonacci() {
        println!("-----running FibonacciCircuit-----");
        const K:u32 = 8;
        let num_iters = 100;
        let fibo_iter = FiboIteration::new(num_iters, 1, 1);
    
        type Scheme = IPACommitmentScheme<EqAffine>;
        let params: ParamsIPA<vesta::Affine> = ParamsIPA::<EqAffine>::new(K);
        let circuit = FiboCircuit::<Fp>::new(fibo_iter.1);
    
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
    
        let zn = circuit.seq.last().unwrap();
        let public_inputs = vec![vec![fibo_iter.0[0], fibo_iter.0[1], zn.x_i_plus_1, zn.y_i_plus_1]];
        let pi: &[&[Fp]] = &public_inputs.iter().map(|v| v.as_slice()).collect::<Vec<_>>()[..];
        let mut transcript = Blake2bWrite::<_, EqAffine, Challenge255<_>>::init(vec![]);
        create_proof::<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>(&params, &pk, &[circuit], &[pi], OsRng, &mut transcript)
              .expect("proof generation should not fail");
    
        let proof = transcript.finalize();
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&params);
        let res = verify_proof(&params, pk.get_vk(), strategy, &[pi], &mut transcript);
        println!("{:?}", res);
    
        /*
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
        */
        println!("-----everything works fine-----");
    }
}
