//! `cam_deref` — fetch, verify, decode.
//!
//! **Fetch** asks the store for the chunk a pointer names; **verify** is the
//! load itself, whose return type is a verified chunk; **decode** runs the
//! value's own codec from the pointer's offset, the reader splicing child
//! chunks through the same steps at each seam.
//!
//! # Store erasure
//!
//! [`cam_deref`] takes `&dyn ChunkStore` because the reader holds one, and a
//! value's codec must not learn where the value is stored.
//! [`crate::cam_commit`] stays generic over its store: nothing about the
//! value's encoding reaches the commit path's store, so there is nothing there
//! to erase.
//!
//! # Value validity
//!
//! Dereferencing authenticates the bytes named by the pointer. The codec and
//! consumer decide whether the decoded value is admissible.

use crate::chunk::ChunkStore;
use crate::error::ValueError;
use crate::ptr::ContentPtr;
use crate::reader::TokenReader;
use crate::tokens::CanonicalValue;

/// Fetches, verifies and decodes the value a pointer addresses.
///
/// # Specification
/// - requires: `pointer` addresses a constructor of a chunk `store` can answer
///   for, under the profile the value was committed with.
/// - ensures: on success the value the subtree at the pointer decodes to; for a
///   root pointer [`crate::cam_commit`] returned, a value equal to the one
///   committed, with every seam invisible in the result.
/// - provides: the value plane's read path, and the portability a content
///   pointer claims.
/// - fails: [`ValueError::UnknownChunk`] when the store cannot answer,
///   [`ValueError::DigestMismatch`] and [`ValueError::MalformedChunk`] when it
///   answers wrongly, [`ValueError::TruncatedStream`] when the offset passes
///   the chunk's records, [`ValueError::DecodeBudgetExceeded`], and the codec's
///   own refusals.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 agreement — every generated value derefs back equal under
///   every generated profile, and the dereffed value's flat bytes are the
///   original's, the flat encoder holding no store and no scanner — plus L3 for
///   the offset, separated by a hand-built non-zero offset that must address a
///   different subtree of the same chunk than offset zero, and for the
///   wrong-kind refusal, separated by a word whose leading byte is a tag.
/// - witness: `tests::laws::every_generated_value_commits_and_derefs_back_equal`
/// - witness: `tests::laws::chunking_is_invisible_to_the_flat_form`
/// - witness: `tests::values::a_committed_value_derefs_back_equal`
/// - witness: `tests::values::an_interior_pointer_derefs_to_its_own_subtree`
/// - witness: `tests::values::a_word_is_never_read_as_a_tag`
#[inline]
pub fn cam_deref<Value>(
    store: &dyn ChunkStore,
    pointer: ContentPtr,
) -> Result<Value, ValueError>
where
    Value: CanonicalValue,
{
    let chunk = store.load(pointer.digest())?;
    let mut reader = TokenReader::over_chunk(store, chunk)?;
    reader.skip(pointer.offset())?;

    Value::decode_tokens(&mut reader)
}
