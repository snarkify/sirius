use halo2_proofs::arithmetic::CurveAffine;
use std::io;

pub trait Transcript<C: CurveAffine> {
    fn squeeze_challenge(&mut self) -> C::Scalar;

    fn common_point(&mut self, point: C) -> io::Result<()>;

    fn common_scalar(&mut self, scalar: C::Scalar) -> io::Result<()>;
}

pub trait TranscriptRead<C: CurveAffine>: Transcript<C> {
    fn read_point(&mut self) -> io::Result<C>;

    fn read_scalar(&mut self) -> io::Result<C::Scalar>;
}

pub trait TranscriptWrite<C: CurveAffine>: Transcript<C> {
    fn write_point(&mut self, point: C) -> io::Result<()>;

    fn write_scalar(&mut self, scalar: C::Scalar) -> io::Result<()>;
}


/// A helper trait to obsorb different objects into transcript
pub trait AbsorbInTranscript<C: CurveAffine,T: Transcript<C>> {
  /// Absorbs the value in the provided transcript
  fn absorb_into(&self, transcript: &mut T) -> io::Result<()>;
}
