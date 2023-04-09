pub(crate) use rayon::current_num_threads;

pub fn parallelize_iter<I, T, F>(iter: I, f: F)
  where
      I: Send + Iterator<Item = T>,
      T: Send,
      F: Fn(T) + Send + Sync + Clone,
  {
      rayon::scope(|scope| {
          for item in iter {
              let f = f.clone();
              scope.spawn(move |_| f(item));
          }
      });
  }

/// This simple utility function will parallelize an operation that is to be
/// performed over a mutable slice.
pub fn parallelize<T, F>(v: &mut [T], f: F)
  where
      T: Send,
      F: Fn((&mut [T], usize)) + Send + Sync + Clone,
  {
      let num_threads = current_num_threads();
      let chunk_size = (v.len() as f64 / num_threads as f64).ceil() as usize;
      if v.len() < num_threads {
          f((v, 0));
      } else {
          parallelize_iter(v.chunks_mut(chunk_size).zip((0..).step_by(chunk_size)), f);
      }
 }
