use std::num::NonZeroUsize;

// SAFETY: Safe because value non zero
pub(crate) const MAX_BITS: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(255) };
// SAFETY: Safe because value non zero
pub(crate) const NUM_CHALLENGE_BITS: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(128) };
