use std::num::NonZeroUsize;

// SAFETY: Safe because value non zero
pub(crate) const MAX_BITS: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(255) };
// A hash outputs an arbitrary set of bytes, to interpret it within some field, we must
// limit the number of bits considered so that we don't get a small number as a hash.
//
// Check [`crate::digest`] for more details
// SAFETY: Safe because value non zero
pub(crate) const NUM_HASH_BITS: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(250) };
// SAFETY: Safe because value non zero
pub(crate) const NUM_CHALLENGE_BITS: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(128) };
