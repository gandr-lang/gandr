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
/// - requires: the selected codec interprets the profile under which the value
///   was committed. Missing storage, malformed bytes and invalid offsets are
///   admitted for refusal.
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
/// - executable: none — the original value and the codec's equivalence relation
///   are not available here. Replaying emission or storage reads would add
///   codec execution and I/O, not observe the returned value alone.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 on generated trees of at most 4096 records observes exact
///   value equality and flat-byte equality under generated profiles. L3 at
///   offsets one and four in two literal chunks observes four exact leaves; a
///   word whose leading byte is a valid tag is still refused by kind. These
///   distinguish wrong digests or offsets, lost seams and kind coercion in the
///   witness codecs, not an arbitrary consumer codec's round-trip law.
/// - witness: `tests::laws::every_generated_value_commits_and_derefs_back_equal`
/// - witness: `tests::laws::chunking_is_invisible_to_the_flat_form`
/// - witness: `tests::values::a_committed_value_derefs_back_equal`
/// - witness: `tests::values::an_interior_pointer_derefs_to_its_own_subtree`
/// - witness: `tests::values::known_interior_addresses_select_distinct_values`
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
