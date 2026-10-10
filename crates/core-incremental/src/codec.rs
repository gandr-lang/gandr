//! The canonical byte form: one encoding for item identities, program
//! addresses and persisted checkpoint sets.
//!
//! # One writer, two sinks
//!
//! Every value is written by one set of functions into a [`Sink`]: a byte
//! buffer when the bytes are kept, a BLAKE3 hasher when only their digest is.
//! An item's identity digest is therefore the digest of exactly the bytes its
//! checkpoint would persist, and computing it allocates nothing.
//!
//! # Decoding refuses what encoding would not write
//!
//! The reader checks structure as it goes — tags, lengths, child indices and
//! their sorts — and a decoded value is written again and compared with its
//! input, so a payload that parses but is not the one canonical spelling of
//! its value is refused rather than accepted under a second address. A table
//! is also checked to be numbered by discovery from its roots, which writing
//! it again would not reveal. Counts read from the input never size an
//! allocation: a corrupted count fails at the end of the input instead.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_checker::ArgumentPosition;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::StaticArity;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::BinderDepth;
use gandr_core_term::Sort as TypeSort;
use gandr_core_term::SortParameter;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelOffset;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::boundary::NodeIndex;
use crate::boundary::Occurrence;
use crate::checkpoint::Answer;
use crate::checkpoint::Answered;
use crate::checkpoint::Checkpoints;
use crate::checkpoint::ItemCheckpoint;
use crate::content::ContentNode;
use crate::content::ItemContent;
use crate::content::Opacity;
use crate::content::Sort;
use crate::content::TypeContent;
use crate::footprint::Footprint;
use crate::footprint::HoleMark;
use crate::region::ItemKey;
use crate::region::Reference;
use crate::typing::Form;
use crate::typing::Refusal;
use crate::typing::Site;
use crate::typing::Typing;

/// The magic and version a persisted checkpoint set opens with.
const CHECKPOINTS_MAGIC: &[u8; 8] = b"GCKPT\0\0\x04";
/// The magic and version a program's address is computed over.
const PROGRAM_MAGIC: &[u8; 8] = b"GPROG\0\0\x02";
/// The decoder's cap on a level atom's offset.
///
/// A level holds `x + o` only as `o` successors of `x`, so decoding an offset
/// costs `o` steps; the cap bounds reconstruction work. Checkpoint encoding
/// rejects offsets at the same cap before a store can publish unreadable bytes.
pub const MAX_DECODED_LEVEL_OFFSET: u64 = 4096;

/// A form the persistent encoding has no spelling for.
///
/// # Specification
/// - executable: none — the enum names an encoding refusal; the rejecting
///   writers establish its cause.
///
/// # Adequacy
/// - hypothesis: L3 — unresolved nodes of all four sorts are rejected with the
///   corresponding sort. This is a finite semantic-form corpus, not evidence
///   about every possible arena.
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnsupportedPersistence
{
    /// An id of this sort that the item's arena resolves to nothing: a fact
    /// about another arena, meaningless outside this process.
    Dangling(Sort),
}

/// Why bytes are not a canonical encoding, or a value has none.
///
/// # Specification
/// - executable: none — error variants describe outcomes; the operations
///   returning them establish the classification.
///
/// # Adequacy
/// - hypothesis: L3 — truncated framing, noncanonical payloads, oversized
///   offsets and unresolved nodes exercise distinct refusals; a length wider
///   than 64 bits has no witness.
/// - witness: `codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CodecError
{
    /// The bytes are truncated, carry trailing bytes, or break the grammar.
    Corrupt,
    /// The bytes parse, but are not the one canonical spelling of their value.
    NonCanonical,
    /// A level atom's offset meets the decoder's cap.
    LevelOffsetTooLarge
    {
        /// The offset read.
        offset: LevelOffset,
    },
    /// The value holds a form the encoding has no spelling for.
    Unsupported(UnsupportedPersistence),
    /// A length does not fit the encoding's width.
    Unrepresentable,
}

impl fmt::Display for UnsupportedPersistence
{
    /// Writes the form's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Dangling(sort) => {
                let sort = match sort {
                    | Sort::Value => "value",
                    | Sort::Computation => "computation",
                    | Sort::ValueType => "value type",
                    | Sort::CompType => "computation type",
                };
                write!(f, "an unresolved {sort} id is process-local")
            },
        }
    }
}

/// A borrowed run of bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bytes<'data>(pub &'data [u8]);

/// Owned checkpoint bytes, canonical only after encoding or successful
/// decoding.
///
/// # Specification
/// - executable: none — the wrapper also accepts unchecked bytes from storage;
///   canonicality is a decoder result, not a type invariant.
///
/// # Adequacy
/// - hypothesis: L3 — malformed, truncated and trailing bytes can inhabit the
///   wrapper and are rejected by decoding; successful finite checkpoint corpora
///   have stable canonical encodings.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes`
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct CheckpointBytes(Vec<u8>);

impl From<Vec<u8>> for CheckpointBytes
{
    /// Wraps bytes read from elsewhere, to be decoded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl From<CheckpointBytes> for Vec<u8>
{
    /// Unwraps the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: CheckpointBytes) -> Self
    {
        bytes.0
    }
}

impl AsRef<[u8]> for CheckpointBytes
{
    /// Borrows the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// One byte naming a variant.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Tag(u8);

/// A little-endian 64-bit word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Word(u64);

/// A length or a count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Count(usize);

/// Where encoded bytes go.
///
/// # Specification
/// - executable: none — the trait exposes writes but no byte or length
///   observer; each implementation owns the append law.
///
/// # Adequacy
/// - hypothesis: L3 — the buffer and hash implementations consume the same
///   fixed framing bytes. This does not quantify over third-party
///   implementations.
/// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
pub trait Sink
{
    /// Append `bytes`.
    ///
    /// # Specification
    /// - executable: none — the required method has no body and the trait
    ///   exposes no sink-state observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete buffer and hash sinks preserve the fixed
    ///   framing byte sequence. The law remains an implementor obligation for
    ///   other sinks.
    /// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    );
}

impl Sink for CheckpointBytes
{
    /// Append to the buffer.
    ///
    /// # Specification
    /// - ensures: the length grows by the input length and the new suffix
    ///   equals the input.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nonempty prefix survives tag, word and
    ///   length-framed payload appends. The predicate observes length and
    ///   suffix; the byte golden also checks prefix preservation.
    /// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
    #[spec(
        captures: [before = self.0.len()],
        ensures: self.0.len().checked_sub(before) == Some(bytes.0.len())
            && self.0.get(before ..) == Some(bytes.0),
    )]
    #[inline]
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    )
    {
        self.0.extend_from_slice(bytes.0);
    }
}

impl Sink for blake3::Hasher
{
    /// Feed the hasher.
    ///
    /// # Specification
    /// - ensures: a representable byte-count increment equals the number of
    ///   supplied bytes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fixed frame has the independently hashed expected
    ///   bytes and the expected count. The predicate uses the public count
    ///   observer, not a cloned hash state; counter overflow and arbitrary
    ///   chunk histories are not witnessed.
    /// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
    #[spec(
        captures: [before = self.count()],
        ensures: u64::try_from(bytes.0.len())
            .ok()
            .and_then(|added| before.checked_add(added))
            .is_none_or(|after| self.count() == after),
    )]
    #[inline]
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    )
    {
        let _hasher = self.update(bytes.0);
    }
}

/// The primitive writes, over one sink.
///
/// # Specification
/// - executable: none — the writer holds an abstract sink without an output
///   observer; individual writes state framing and failure laws.
///
/// # Adequacy
/// - hypothesis: L3 — fixed tag, word and framed payload bytes are checked in
///   buffer and hash sinks.
/// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
#[repr(transparent)]
struct Writer<'sink, Out>
{
    /// The sink written to.
    sink: &'sink mut Out,
}

impl<Out> Writer<'_, Out>
where
    Out: Sink,
{
    /// Write one tag byte.
    ///
    /// # Specification
    /// - ensures: one tag byte is appended.
    /// - executable: none — `Sink` exposes no observation of the bytes written.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independent fixed bytes check tag width, word
    ///   endianness and prefix preservation. The hash sink is checked against
    ///   the digest of those fixed bytes.
    /// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
    fn tag(
        &mut self,
        tag: Tag,
    )
    {
        self.sink.put(Bytes(&[tag.0]));
    }

    /// Write one word.
    ///
    /// # Specification
    /// - ensures: exactly eight bytes are appended in little-endian order.
    /// - executable: none — `Sink` exposes no observation of the bytes written.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independent fixed bytes check tag width, word
    ///   endianness and prefix preservation. The hash sink is checked against
    ///   the digest of those fixed bytes.
    /// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
    fn word(
        &mut self,
        word: Word,
    )
    {
        self.sink.put(Bytes(&word.0.to_le_bytes()));
    }

    /// Write one count as a word.
    ///
    /// # Specification
    /// - fails: [`CodecError::Unrepresentable`] when the count passes 64 bits.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a framed payload contributes an eight-byte length
    ///   prefix. The predicate states the width refusal exactly; a count wider
    ///   than 64 bits is unwitnessed.
    /// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
    #[spec(
        ensures: |ret| {
            ret == u64::try_from(count.0)
                .map(|_| ())
                .map_err(|_overflow| CodecError::Unrepresentable)
        },
    )]
    fn count(
        &mut self,
        count: Count,
    ) -> Result<(), CodecError>
    {
        let word = u64::try_from(count.0).map_err(|_overflow| CodecError::Unrepresentable)?;
        self.word(Word(word));
        Ok(())
    }

    /// Write a length-prefixed run of bytes.
    ///
    /// # Specification
    /// - fails: as [`Self::count`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binary payload containing zero and non-ASCII bytes
    ///   follows its exact length prefix. Output bytes are witnessed because
    ///   the generic sink has no observer.
    /// - witness: `codec::tests::primitive_frames_have_known_bytes_and_digest`
    #[spec(
        ensures: |ret| {
            ret == u64::try_from(bytes.0.len())
                .map(|_| ())
                .map_err(|_overflow| CodecError::Unrepresentable)
        },
    )]
    fn bytes(
        &mut self,
        bytes: Bytes<'_>,
    ) -> Result<(), CodecError>
    {
        self.count(Count(bytes.0.len()))?;
        self.sink.put(bytes);
        Ok(())
    }
}

/// The primitive reads, over one input.
///
/// # Specification
/// - executable: none — the cursor is raw state and may lie outside the input;
///   checked operations, rather than construction, establish valid extents.
///
/// # Adequacy
/// - hypothesis: L3 — end-of-input, truncated fields, an overflowing cursor and
///   partially consumed frames exercise cursor transitions without assuming a
///   valid initial extent.
/// - witness: `codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
/// - witness: `codec::tests::framed_failures_retain_consumed_prefixes`
struct Reader<'data>
{
    /// The input.
    bytes: &'data [u8],
    /// The next unread byte.
    cursor: usize,
}

impl<'data> Reader<'data>
{
    /// Read the next `count` bytes.
    ///
    /// # Specification
    /// - fails: [`CodecError::Corrupt`] past the end of the input.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successful fixed-width reads and zero-length end
    ///   reads coexist with truncation and cursor-addition overflow; failures
    ///   leave the initial cursor unchanged.
    /// - witness: `codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| match before
            .checked_add(count.0)
            .and_then(|end| self.bytes.get(before .. end).map(|bytes| (end, bytes)))
        {
            | Some((end, bytes)) => self.cursor == end && ret == Ok(Bytes(bytes)),
            | None => self.cursor == before && ret == Err(CodecError::Corrupt),
        },
    )]
    fn take(
        &mut self,
        count: Count,
    ) -> Result<Bytes<'data>, CodecError>
    {
        let end = self
            .cursor
            .checked_add(count.0)
            .ok_or(CodecError::Corrupt)?;
        let taken = self
            .bytes
            .get(self.cursor .. end)
            .ok_or(CodecError::Corrupt)?;
        self.cursor = end;
        Ok(Bytes(taken))
    }

    /// Read one tag byte.
    ///
    /// # Specification
    /// - ensures: one available byte is returned and consumed; absence leaves
    ///   the cursor unchanged.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the byte following a known word is read exactly; a
    ///   read past the end is refused.
    /// - witness: `codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| match self.bytes.get(before) {
            | Some(&tag) => before.checked_add(1) == Some(self.cursor) && ret == Ok(Tag(tag)),
            | None => self.cursor == before && ret == Err(CodecError::Corrupt),
        },
    )]
    fn tag(&mut self) -> Result<Tag, CodecError>
    {
        let taken = self.take(Count(1))?;
        match *taken.0 {
            | [tag] => Ok(Tag(tag)),
            | _ => Err(CodecError::Corrupt),
        }
    }

    /// Read one word.
    ///
    /// # Specification
    /// - ensures: a complete eight-byte little-endian word is consumed; a short
    ///   field is not.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — eight distinct bytes have their independent
    ///   little-endian value; a seven-byte field and overflowing cursor are
    ///   rejected without advancing.
    /// - witness: `codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| match before
            .checked_add(8)
            .and_then(|end| self.bytes.get(before .. end).map(|bytes| (end, bytes)))
        {
            | Some((end, &[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7])) => {
                self.cursor == end
                    && ret
                        == Ok(Word(u64::from_le_bytes([
                            byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
                        ])))
            },
            | _ => self.cursor == before && ret == Err(CodecError::Corrupt),
        },
    )]
    fn word(&mut self) -> Result<Word, CodecError>
    {
        let taken = self.take(Count(8))?;
        let array: [u8; 8] = taken.0.try_into().map_err(|_short| CodecError::Corrupt)?;
        Ok(Word(u64::from_le_bytes(array)))
    }

    /// Read one count.
    ///
    /// # Specification
    /// - ensures: the complete word is consumed even if it cannot be narrowed
    ///   to the host count width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — framed lengths are decoded before payload extent
    ///   checks. Narrowing failure on targets with `usize` narrower than 64
    ///   bits is unwitnessed.
    /// - witness: `codec::tests::framed_failures_retain_consumed_prefixes`
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| match before
            .checked_add(8)
            .and_then(|end| self.bytes.get(before .. end).map(|bytes| (end, bytes)))
        {
            | Some((end, &[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7])) => {
                self.cursor == end
                    && ret
                        == usize::try_from(u64::from_le_bytes([
                            byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
                        ]))
                        .map(Count)
                        .map_err(|_overflow| CodecError::Corrupt)
            },
            | _ => self.cursor == before && ret == Err(CodecError::Corrupt),
        },
    )]
    fn count(&mut self) -> Result<Count, CodecError>
    {
        let word = self.word()?;
        let count = usize::try_from(word.0).map_err(|_overflow| CodecError::Corrupt)?;
        Ok(Count(count))
    }

    /// Read a length-prefixed run of bytes.
    ///
    /// # Specification
    /// - ensures: the length prefix is consumed before checking the payload
    ///   extent; a short payload remains unread.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a truncated payload retains its consumed prefix, and
    ///   its first byte remains readable. Zero-length frames and exact-end
    ///   payloads are exercised without a rollback assumption.
    /// - witness: `codec::tests::framed_failures_retain_consumed_prefixes`
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| match before
            .checked_add(8)
            .and_then(|end| self.bytes.get(before .. end).map(|bytes| (end, bytes)))
        {
            | Some((end, &[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7])) => {
                let payload = usize::try_from(u64::from_le_bytes([
                    byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
                ]))
                .ok()
                .and_then(|count| end.checked_add(count))
                .and_then(|after| self.bytes.get(end .. after).map(|bytes| (after, bytes)));
                match payload {
                    | Some((after, bytes)) => self.cursor == after && ret == Ok(Bytes(bytes)),
                    | None => self.cursor == end && ret == Err(CodecError::Corrupt),
                }
            },
            | _ => self.cursor == before && ret == Err(CodecError::Corrupt),
        },
    )]
    fn bytes(&mut self) -> Result<Bytes<'data>, CodecError>
    {
        let count = self.count()?;
        self.take(count)
    }

    /// Read a length-prefixed run of UTF-8 text.
    ///
    /// # Specification
    /// - ensures: valid UTF-8 is returned; invalid UTF-8 consumes its entire
    ///   frame before refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — multibyte UTF-8, an empty string and an invalid byte
    ///   followed by another tag distinguish framing failure from text failure.
    /// - witness: `codec::tests::framed_failures_retain_consumed_prefixes`
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| match before
            .checked_add(8)
            .and_then(|end| self.bytes.get(before .. end).map(|bytes| (end, bytes)))
        {
            | Some((end, &[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7])) => {
                let payload = usize::try_from(u64::from_le_bytes([
                    byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
                ]))
                .ok()
                .and_then(|count| end.checked_add(count))
                .and_then(|after| self.bytes.get(end .. after).map(|bytes| (after, bytes)));
                match payload {
                    | Some((after, bytes)) => {
                        self.cursor == after
                            && core::str::from_utf8(bytes).map_or_else(
                                |_invalid| ret == Err(CodecError::Corrupt),
                                |text| ret.as_deref() == Ok(text),
                            )
                    },
                    | None => self.cursor == end && ret == Err(CodecError::Corrupt),
                }
            },
            | _ => self.cursor == before && ret == Err(CodecError::Corrupt),
        },
    )]
    fn text(&mut self) -> Result<String, CodecError>
    {
        let bytes = self.bytes()?;
        String::from_utf8(bytes.0.to_vec()).map_err(|_invalid| CodecError::Corrupt)
    }

    /// Require that the whole input was read.
    ///
    /// # Specification
    /// - fails: [`CodecError::Corrupt`] when bytes remain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact exhaustion succeeds and trailing bytes are
    ///   refused without being consumed.
    /// - witness: `codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
    /// - witness: `codec::tests::framed_failures_retain_consumed_prefixes`
    #[spec(
        ensures: |ret| {
            ret == if self.cursor == self.bytes.len() {
                Ok(())
            }
            else {
                Err(CodecError::Corrupt)
            }
        },
    )]
    fn finish(&self) -> Result<(), CodecError>
    {
        if self.cursor == self.bytes.len() {
            Ok(())
        }
        else {
            Err(CodecError::Corrupt)
        }
    }
}

/// A count as a word, for fields the vocabulary types as `usize`.
///
/// # Specification
/// - ensures: the count is preserved when it fits a 64-bit word, otherwise it
///   is unrepresentable.
///
/// # Adequacy
/// - hypothesis: L3 — persisted checkpoint budgets round-trip through the word
///   field. A count wider than 64 bits has no witness.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
#[spec(
    ensures: |ret| {
        ret == u64::try_from(count.0)
            .map(Word)
            .map_err(|_overflow| CodecError::Unrepresentable)
    },
)]
fn word_of(count: Count) -> Result<Word, CodecError>
{
    let word = u64::try_from(count.0).map_err(|_overflow| CodecError::Unrepresentable)?;
    Ok(Word(word))
}

/// Write a reference.
///
/// # Specification
/// - ensures: unoccupied references always encode; item keys and occurrences
///   must fit word widths.
///
/// # Adequacy
/// - hypothesis: L3 — fixed frames distinguish the empty reference from an item
///   with binary key bytes and a nonzero occurrence. The predicate observes
///   representability, not the generic sink.
/// - witness: `codec::tests::reference_frames_preserve_binary_keys_and_occurrences`
#[spec(
    ensures: |ret| {
        ret == if match *reference {
            | Reference::Unoccupied => true,
            | Reference::Item {
                ref key,
                occurrence,
            } => {
                u64::try_from(key.as_ref().len()).is_ok()
                    && u64::try_from(usize::from(occurrence)).is_ok()
            },
        } {
            Ok(())
        }
        else {
            Err(CodecError::Unrepresentable)
        }
    },
)]
fn write_reference<Out>(
    writer: &mut Writer<'_, Out>,
    reference: &Reference,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *reference {
        | Reference::Unoccupied => writer.tag(Tag(0)),
        | Reference::Item {
            ref key,
            occurrence,
        } => {
            writer.tag(Tag(1));
            writer.bytes(Bytes(key.as_ref()))?;
            writer.count(Count(usize::from(occurrence)))?;
        },
    }
    Ok(())
}

/// The canonical bytes of one reference, for tests that rewrite a payload.
///
/// # Specification
/// - ensures: the returned bytes contain the exact tag, framed key and
///   occurrence of the reference.
///
/// # Adequacy
/// - hypothesis: L3 — a binary key containing zero and a non-UTF-8 byte has
///   independently specified bytes; the unoccupied reference has its distinct
///   one-byte frame.
/// - witness: `codec::tests::reference_frames_preserve_binary_keys_and_occurrences`
#[cfg(test)]
#[spec(
    ensures: |ret| {
        let bytes = ret.as_ref();
        match *reference {
            | Reference::Unoccupied => bytes == [0],
            | Reference::Item {
                ref key,
                occurrence,
            } => {
                bytes.first() == Some(&1)
                    && u64::try_from(key.as_ref().len()).is_ok_and(|count| {
                        bytes.get(1 .. 9) == Some(count.to_le_bytes().as_slice())
                    })
                    && bytes
                        .get(9 ..)
                        .and_then(|tail| tail.strip_prefix(key.as_ref()))
                        .is_some_and(|tail| {
                            u64::try_from(usize::from(occurrence))
                                .is_ok_and(|word| tail == word.to_le_bytes())
                        })
            },
        }
    },
)]
pub fn reference_bytes(reference: &Reference) -> CheckpointBytes
{
    let mut bytes = CheckpointBytes::default();
    let mut writer = Writer { sink: &mut bytes };
    assert_eq!(
        write_reference(&mut writer, reference),
        Ok(()),
        "a reference always encodes"
    );
    bytes
}

/// Read a reference.
///
/// # Specification
/// - ensures: a successful reference is exactly the consumed frame; only
///   corrupt input is refused.
///
/// # Adequacy
/// - hypothesis: L3 — binary keys and nonzero occurrences survive known frames,
///   while unknown tags are refused. The predicate checks successful payloads
///   without constructing a second owned key.
/// - witness: `codec::tests::reference_frames_preserve_binary_keys_and_occurrences`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref reference) => reader
            .bytes
            .get(before .. reader.cursor)
            .is_some_and(|bytes| match *reference {
                | Reference::Unoccupied => bytes == [0],
                | Reference::Item {
                    ref key,
                    occurrence,
                } => {
                    bytes.first() == Some(&1)
                        && u64::try_from(key.as_ref().len()).is_ok_and(|count| {
                            bytes.get(1 .. 9) == Some(count.to_le_bytes().as_slice())
                        })
                        && bytes
                            .get(9 ..)
                            .and_then(|tail| tail.strip_prefix(key.as_ref()))
                            .is_some_and(|tail| {
                                u64::try_from(usize::from(occurrence))
                                    .is_ok_and(|word| tail == word.to_le_bytes())
                            })
                },
            }),
        | Err(error) => error == CodecError::Corrupt && reader.cursor >= before,
    },
)]
fn read_reference(reader: &mut Reader<'_>) -> Result<Reference, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => Ok(Reference::Unoccupied),
        | 1 => {
            let key = reader.bytes()?;
            let occurrence = reader.count()?;
            Ok(Reference::Item {
                key: ItemKey::from(key.0),
                occurrence: Occurrence::from(occurrence.0),
            })
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write a level: its constant, then its atoms ascending.
///
/// # Specification
/// - ensures: encoding succeeds exactly when the atom count fits a word;
///   offsets are not capped here.
///
/// # Adequacy
/// - hypothesis: L3 — universe sorts and levels round-trip, including an offset
///   immediately below the decoder cap. Raw frames can represent a capped
///   offset for decoder fixtures; validated checkpoint encoding refuses it.
/// - witness: `persistence::tests::universe_sorts_and_levels_round_trip`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[spec(
    ensures: |ret| {
        ret == u64::try_from(level.atoms().count())
            .map(|_| ())
            .map_err(|_overflow| CodecError::Unrepresentable)
    },
)]
fn write_level<Out>(
    writer: &mut Writer<'_, Out>,
    level: &Level,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.word(Word(u64::from(level.constant_part())));
    writer.count(Count(level.atoms().count()))?;
    for (variable, offset) in level.atoms() {
        writer.word(Word(u64::from(u32::from(variable.index()))));
        writer.word(Word(u64::from(offset)));
    }
    Ok(())
}

/// Read a level, refusing an offset at or past the cap.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the level `max(c, x₁ + o₁, …)` the bytes spell.
/// - fails: [`CodecError::LevelOffsetTooLarge`] naming the first offset at or
///   past [`MAX_DECODED_LEVEL_OFFSET`]; [`CodecError::Corrupt`] for a malformed
///   level.
/// - panics: none.
/// - intension: an atom of offset `o` costs `o` successor steps, bounded by the
///   cap.
///
/// # Adequacy
/// - hypothesis: L3 — the cap boundary separates a round-tripping offset from
///   the exact refused offset. The predicate checks the successful offset bound
///   and the offending input word; it does not rebuild the level or
///   independently prove normalization of every atom sequence.
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
/// - witness: `persistence::tests::universe_sorts_and_levels_round_trip`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref level) => level
            .atoms()
            .all(|(_, offset)| u64::from(offset) < MAX_DECODED_LEVEL_OFFSET),
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
                && reader
                    .cursor
                    .checked_sub(8)
                    .and_then(|start| reader.bytes.get(start .. reader.cursor))
                    == Some(u64::from(offset).to_le_bytes().as_slice())
        },
        | Err(error) => error == CodecError::Corrupt,
    },
)]
fn read_level(reader: &mut Reader<'_>) -> Result<Level, CodecError>
{
    let constant = reader.word()?;
    let atoms = reader.count()?;
    let mut level = Level::constant(LevelConstant::from(constant.0));
    for _ in 0 .. atoms.0 {
        let variable = reader.word()?;
        let variable = u32::try_from(variable.0).map_err(|_overflow| CodecError::Corrupt)?;
        let offset = reader.word()?;
        if offset.0 >= MAX_DECODED_LEVEL_OFFSET {
            return Err(CodecError::LevelOffsetTooLarge {
                offset: LevelOffset::from(offset.0),
            });
        }
        let mut atom = Level::var(LevelVar::new(LevelVarIndex::from(variable)));
        for _ in 0 .. offset.0 {
            atom = atom.succ().map_err(|_overflow| CodecError::Corrupt)?;
        }
        level = level.max(&atom);
    }
    Ok(level)
}

/// The tag of a sign.
///
/// # Specification
/// - ensures: negative is tag zero and nonnegative is tag one.
///
/// # Adequacy
/// - hypothesis: L3 — the finite persisted semantic corpus exercises signed
///   literal encodings. The const predicate compares the primitive tag field
///   directly.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    ensures: |ret| {
        ret.0
            == match sign {
                | Sign::Negative => 0,
                | Sign::NonNegative => 1,
            }
    },
)]
const fn sign_tag(sign: Sign) -> Tag
{
    match sign {
        | Sign::Negative => Tag(0),
        | Sign::NonNegative => Tag(1),
    }
}

/// Read a sign.
///
/// # Specification
/// - ensures: only tags zero and one denote signs; an available tag is consumed
///   even when unknown.
///
/// # Adequacy
/// - hypothesis: L3 — signed integer and numeric literals cross the persistent
///   boundary. An unknown tag with available payload bytes is rejected before
///   that payload is consumed; the finite corpus does not enumerate magnitudes.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match reader.bytes.get(before) {
        | Some(&tag) => {
            before.checked_add(1) == Some(reader.cursor)
                && ret
                    == match tag {
                        | 0 => Ok(Sign::Negative),
                        | 1 => Ok(Sign::NonNegative),
                        | _ => Err(CodecError::Corrupt),
                    }
        },
        | None => reader.cursor == before && ret == Err(CodecError::Corrupt),
    },
)]
fn read_sign(reader: &mut Reader<'_>) -> Result<Sign, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => Ok(Sign::Negative),
        | 1 => Ok(Sign::NonNegative),
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write a literal.
///
/// # Specification
/// - ensures: encoding succeeds exactly when every decimal or text byte length
///   fits a word.
///
/// # Adequacy
/// - hypothesis: L3 — integer, text and numeric values in the finite semantic
///   corpus cross persistence. The predicate states field representability; the
///   corpus, rather than a generic sink observer, witnesses payload
///   preservation.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    ensures: |ret| {
        ret == if match *literal {
            | Literal::Integer(ref integer) => {
                u64::try_from(integer.magnitude().as_ref().len()).is_ok()
            },
            | Literal::Text(ref text) => u64::try_from(text.as_ref().len()).is_ok(),
            | Literal::Numeric(ref numeric) => {
                u64::try_from(numeric.integer_part().as_ref().len()).is_ok()
                    && u64::try_from(numeric.fraction().as_ref().len()).is_ok()
            },
        } {
            Ok(())
        }
        else {
            Err(CodecError::Unrepresentable)
        }
    },
)]
fn write_literal<Out>(
    writer: &mut Writer<'_, Out>,
    literal: &Literal,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *literal {
        | Literal::Integer(ref integer) => {
            writer.tag(Tag(0));
            writer.tag(sign_tag(integer.sign()));
            writer.bytes(Bytes(integer.magnitude().as_ref().as_bytes()))?;
        },
        | Literal::Text(ref string) => {
            writer.tag(Tag(1));
            writer.bytes(Bytes(string.as_ref().as_bytes()))?;
        },
        | Literal::Numeric(ref numeric) => {
            writer.tag(Tag(2));
            writer.tag(sign_tag(numeric.sign()));
            writer.bytes(Bytes(numeric.integer_part().as_ref().as_bytes()))?;
            writer.bytes(Bytes(numeric.fraction().as_ref().as_bytes()))?;
        },
    }
    Ok(())
}

/// Read a literal.
///
/// # Specification
/// - ensures: successful literals retain the input variant tag; decimal fields
///   may be normalized.
///
/// # Adequacy
/// - hypothesis: L3 — the finite semantic corpus preserves the three literal
///   classes through persistence. The predicate checks tag classification, not
///   a second construction of normalized decimal text. Unknown tags reject
///   before consuming available payload bytes.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref literal) => {
            reader.bytes.get(before)
                == Some(&match *literal {
                    | Literal::Integer(_) => 0,
                    | Literal::Text(_) => 1,
                    | Literal::Numeric(_) => 2,
                })
                && reader.cursor > before
        },
        | Err(error) => error == CodecError::Corrupt && reader.cursor >= before,
    },
)]
fn read_literal(reader: &mut Reader<'_>) -> Result<Literal, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => {
            let sign = read_sign(reader)?;
            let digits = reader.text()?;
            let magnitude = Magnitude::from_decimal_text(digits).ok_or(CodecError::Corrupt)?;
            Ok(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
        },
        | 1 => {
            let text = reader.text()?;
            Ok(Literal::Text(StringLiteral::new(text)))
        },
        | 2 => {
            let sign = read_sign(reader)?;
            let digits = reader.text()?;
            let integer_part = Magnitude::from_decimal_text(digits).ok_or(CodecError::Corrupt)?;
            let digits = reader.text()?;
            let fraction = FractionDigits::from_decimal_text(digits).ok_or(CodecError::Corrupt)?;
            Ok(Literal::Numeric(NumericLiteral::new(
                sign,
                integer_part,
                fraction,
            )))
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write a node index.
///
/// # Specification
/// trivial.
fn write_index<Out>(
    writer: &mut Writer<'_, Out>,
    index: NodeIndex,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(usize::from(index)))
}

/// Read a node index.
///
/// # Specification
/// trivial.
fn read_index(reader: &mut Reader<'_>) -> Result<NodeIndex, CodecError>
{
    let count = reader.count()?;
    Ok(NodeIndex::from(count.0))
}

/// Write one content node.
///
/// # Specification
/// - fails: [`CodecError::Unsupported`] for an unresolved node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite semantic corpus encodes supported nodes and
///   all four unresolved sorts are rejected with their exact sort. The
///   predicate classifies failures; a generic sink does not expose the emitted
///   fields.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[spec(
    ensures: |ret| match *node {
        | ContentNode::Unresolved(sort) => {
            ret == Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(
                sort,
            )))
        },
        | _ => matches!(ret, Ok(()) | Err(CodecError::Unrepresentable)),
    },
)]
fn write_node<Out>(
    writer: &mut Writer<'_, Out>,
    node: &ContentNode,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *node {
        | ContentNode::PrimitiveValue(primitive) => {
            writer.tag(Tag(0x0D));
            writer.bytes(Bytes(primitive.name().as_ref().as_bytes()))?;
        },
        | ContentNode::Primitive(primitive, arguments) => {
            writer.tag(Tag(0x16));
            writer.bytes(Bytes(primitive.name().as_ref().as_bytes()))?;
            writer.tag(match arguments {
                | gandr_core_term::primitive::Arguments::Unary(_) => Tag(1),
                | gandr_core_term::primitive::Arguments::Binary(_) => Tag(2),
            });
            for &argument in arguments.iter() {
                write_index(writer, argument)?;
            }
        },
        | ContentNode::PathUniverse(source, target) => {
            writer.tag(Tag(0x40));
            write_index(writer, source)?;
            write_index(writer, target)?;
        },
        | ContentNode::PathRefl(code) => {
            writer.tag(Tag(0x41));
            write_index(writer, code)?;
        },
        | ContentNode::PathEquiv {
            path_type,
            forward,
            backward,
            ref evidence,
        } => {
            writer.tag(Tag(0x42));
            write_index(writer, path_type)?;
            write_index(writer, forward)?;
            write_index(writer, backward)?;
            for word in evidence.words() {
                writer.word(Word(word.0));
            }
        },
        | ContentNode::PathProduct(first, second) => {
            writer.tag(Tag(0x43));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        | ContentNode::Transport(path, value) => {
            writer.tag(Tag(0x44));
            write_index(writer, path)?;
            write_index(writer, value)?;
        },
        | ContentNode::Variable { zone, index } => {
            writer.tag(Tag(0x01));
            writer.tag(match zone {
                | Zone::Intuitionistic => Tag(0),
                | Zone::Linear => Tag(1),
            });
            writer.word(Word(u64::from(u32::from(index))));
        },
        | ContentNode::Constant(ref reference) => {
            writer.tag(Tag(0x02));
            write_reference(writer, reference)?;
        },
        | ContentNode::Unit => writer.tag(Tag(0x03)),
        | ContentNode::Literal(ref literal) => {
            writer.tag(Tag(0x04));
            write_literal(writer, literal)?;
        },
        | ContentNode::Pair(first, second) => {
            writer.tag(Tag(0x05));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        | ContentNode::Injection(side, body) => {
            writer.tag(Tag(0x06));
            writer.tag(match side {
                | Side::Left => Tag(0),
                | Side::Right => Tag(1),
            });
            write_index(writer, body)?;
        },
        | ContentNode::Thunk(body) => {
            writer.tag(Tag(0x07));
            write_index(writer, body)?;
        },
        | ContentNode::ValueLift { ref target, body } => {
            writer.tag(Tag(0x08));
            write_level(writer, target)?;
            write_index(writer, body)?;
        },
        | ContentNode::Quote(quoted) => {
            writer.tag(Tag(0x09));
            write_index(writer, quoted)?;
        },
        | ContentNode::QuoteComputation(quoted) => {
            writer.tag(Tag(0x0A));
            write_index(writer, quoted)?;
        },
        | ContentNode::StaticLambda(body) => {
            writer.tag(Tag(0x0B));
            write_index(writer, body)?;
        },
        | ContentNode::StaticApplication(head, argument) => {
            writer.tag(Tag(0x0C));
            write_index(writer, head)?;
            write_index(writer, argument)?;
        },
        | ContentNode::Lambda(body) => {
            writer.tag(Tag(0x10));
            write_index(writer, body)?;
        },
        | ContentNode::Application(head, argument) => {
            writer.tag(Tag(0x11));
            write_index(writer, head)?;
            write_index(writer, argument)?;
        },
        | ContentNode::Return(value) => {
            writer.tag(Tag(0x12));
            write_index(writer, value)?;
        },
        | ContentNode::Bind(bound, rest) => {
            writer.tag(Tag(0x13));
            write_index(writer, bound)?;
            write_index(writer, rest)?;
        },
        | ContentNode::Force(value) => {
            writer.tag(Tag(0x14));
            write_index(writer, value)?;
        },
        | ContentNode::Case {
            scrutinee,
            on_left,
            on_right,
        } => {
            writer.tag(Tag(0x15));
            write_index(writer, scrutinee)?;
            write_index(writer, on_left)?;
            write_index(writer, on_right)?;
        },
        | ContentNode::Base(base) => {
            writer.tag(Tag(0x20));
            writer.tag(match base {
                | BaseType::Integer => Tag(0),
                | BaseType::String => Tag(1),
                | BaseType::Numeric => Tag(2),
            });
        },
        | ContentNode::UnitType => writer.tag(Tag(0x21)),
        | ContentNode::Product(first, second) => {
            writer.tag(Tag(0x22));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        | ContentNode::Sum(first, second) => {
            writer.tag(Tag(0x23));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        | ContentNode::ThunkType(body) => {
            writer.tag(Tag(0x24));
            write_index(writer, body)?;
        },
        // The value universe keeps the tag it had before the sorts were
        // spelled, and the other two sorts take fresh tags, so a table
        // written before the families reads the same after them.
        | ContentNode::Universe {
            sort: TypeSort::Ground(GroundSort::Value),
            ref level,
        } => {
            writer.tag(Tag(0x25));
            write_level(writer, level)?;
        },
        | ContentNode::Universe {
            sort: TypeSort::Ground(GroundSort::Computation),
            ref level,
        } => {
            writer.tag(Tag(0x29));
            write_level(writer, level)?;
        },
        | ContentNode::Universe {
            sort: TypeSort::Parameter(parameter),
            ref level,
        } => {
            writer.tag(Tag(0x2A));
            writer.word(Word(u64::from(u32::from(parameter))));
            write_level(writer, level)?;
        },
        | ContentNode::TypeLift { inner, ref target } => {
            writer.tag(Tag(0x26));
            write_index(writer, inner)?;
            write_level(writer, target)?;
        },
        | ContentNode::Element { code, ref target } => {
            writer.tag(Tag(0x27));
            write_index(writer, code)?;
            write_level(writer, target)?;
        },
        | ContentNode::Abstract(ref reference) => {
            writer.tag(Tag(0x28));
            write_reference(writer, reference)?;
        },
        | ContentNode::StaticPi { domain, codomain } => {
            writer.tag(Tag(0x2B));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        | ContentNode::Returner(result) => {
            writer.tag(Tag(0x30));
            write_index(writer, result)?;
        },
        | ContentNode::Arrow { domain, codomain } => {
            writer.tag(Tag(0x31));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        | ContentNode::Pi { domain, codomain } => {
            writer.tag(Tag(0x32));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        | ContentNode::ComputationElement { code, ref target } => {
            writer.tag(Tag(0x33));
            write_index(writer, code)?;
            write_level(writer, target)?;
        },
        | ContentNode::Unresolved(sort) => {
            return Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(
                sort,
            )));
        },
    }
    Ok(())
}

/// Read one content node.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for an unknown tag or a malformed field; no
///   tag spells an unresolved node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite semantic and universe corpora exercise tag
///   classes across all four sorts. The predicate relates the consumed tag to
///   the resulting class, not every payload field; unresolved nodes have no
///   accepted tag. Unknown node tags and invalid zone, side and base fields
///   stop at the tag.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::universe_sorts_and_levels_round_trip`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
/// - witness: `codec::tests::type_tables_validate_roots_child_extents_and_sorts`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref node) => {
            reader.cursor > before
                && reader.cursor <= reader.bytes.len()
                && reader.bytes.get(before).is_some_and(|&tag| match *node {
                    | ContentNode::PrimitiveValue(_) => tag == 0x0D,
                    | ContentNode::Primitive(..) => tag == 0x16,
                    | ContentNode::PathUniverse(..) => tag == 0x40,
                    | ContentNode::PathRefl(_) => tag == 0x41,
                    | ContentNode::PathEquiv { .. } => tag == 0x42,
                    | ContentNode::PathProduct(..) => tag == 0x43,
                    | ContentNode::Transport(..) => tag == 0x44,
                    | ContentNode::Variable { .. } => tag == 0x01,
                    | ContentNode::Constant(_) => tag == 0x02,
                    | ContentNode::Unit => tag == 0x03,
                    | ContentNode::Literal(_) => tag == 0x04,
                    | ContentNode::Pair(..) => tag == 0x05,
                    | ContentNode::Injection(..) => tag == 0x06,
                    | ContentNode::Thunk(_) => tag == 0x07,
                    | ContentNode::ValueLift { .. } => tag == 0x08,
                    | ContentNode::Quote(_) => tag == 0x09,
                    | ContentNode::QuoteComputation(_) => tag == 0x0A,
                    | ContentNode::StaticLambda(_) => tag == 0x0B,
                    | ContentNode::StaticApplication(..) => tag == 0x0C,
                    | ContentNode::Lambda(_) => tag == 0x10,
                    | ContentNode::Application(..) => tag == 0x11,
                    | ContentNode::Return(_) => tag == 0x12,
                    | ContentNode::Bind(..) => tag == 0x13,
                    | ContentNode::Force(_) => tag == 0x14,
                    | ContentNode::Case { .. } => tag == 0x15,
                    | ContentNode::Base(_) => tag == 0x20,
                    | ContentNode::UnitType => tag == 0x21,
                    | ContentNode::Product(..) => tag == 0x22,
                    | ContentNode::Sum(..) => tag == 0x23,
                    | ContentNode::ThunkType(_) => tag == 0x24,
                    | ContentNode::Universe {
                        sort: TypeSort::Ground(GroundSort::Value),
                        ..
                    } => tag == 0x25,
                    | ContentNode::TypeLift { .. } => tag == 0x26,
                    | ContentNode::Element { .. } => tag == 0x27,
                    | ContentNode::Abstract(_) => tag == 0x28,
                    | ContentNode::Universe {
                        sort: TypeSort::Ground(GroundSort::Computation),
                        ..
                    } => tag == 0x29,
                    | ContentNode::Universe {
                        sort: TypeSort::Parameter(_),
                        ..
                    } => tag == 0x2A,
                    | ContentNode::StaticPi { .. } => tag == 0x2B,
                    | ContentNode::Returner(_) => tag == 0x30,
                    | ContentNode::Arrow { .. } => tag == 0x31,
                    | ContentNode::Pi { .. } => tag == 0x32,
                    | ContentNode::ComputationElement { .. } => tag == 0x33,
                    | ContentNode::Unresolved(_) => false,
                })
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(error) => error == CodecError::Corrupt,
    },
)]
fn read_node(reader: &mut Reader<'_>) -> Result<ContentNode, CodecError>
{
    let tag = reader.tag()?;
    let node = match tag.0 {
        | 0x0D | 0x16 => {
            use gandr_core_term::primitive::Arguments;
            use gandr_core_term::primitive::PRELUDE;
            let name = reader.bytes()?;
            let primitive = PRELUDE
                .iter()
                .find(|primitive| primitive.name().as_ref().as_bytes() == name.0)
                .copied()
                .ok_or(CodecError::Corrupt)?;
            if tag.0 == 0x0D {
                ContentNode::PrimitiveValue(primitive)
            }
            else {
                let arguments = match reader.tag()?.0 {
                    | 1 => Arguments::Unary(read_index(reader)?),
                    | 2 => Arguments::Binary([read_index(reader)?, read_index(reader)?]),
                    | _ => return Err(CodecError::Corrupt),
                };
                ContentNode::Primitive(primitive, arguments)
            }
        },
        | 0x01 => {
            let zone = reader.tag()?;
            let zone = match zone.0 {
                | 0 => Zone::Intuitionistic,
                | 1 => Zone::Linear,
                | _ => return Err(CodecError::Corrupt),
            };
            let index = reader.word()?;
            let index = u32::try_from(index.0).map_err(|_overflow| CodecError::Corrupt)?;
            ContentNode::Variable {
                zone,
                index: DeBruijnIndex::from(index),
            }
        },
        | 0x02 => {
            let reference = read_reference(reader)?;
            ContentNode::Constant(reference)
        },
        | 0x03 => ContentNode::Unit,
        | 0x04 => {
            let literal = read_literal(reader)?;
            ContentNode::Literal(literal)
        },
        | 0x05 => {
            let first = read_index(reader)?;
            let second = read_index(reader)?;
            ContentNode::Pair(first, second)
        },
        | 0x06 => {
            let side = reader.tag()?;
            let side = match side.0 {
                | 0 => Side::Left,
                | 1 => Side::Right,
                | _ => return Err(CodecError::Corrupt),
            };
            let body = read_index(reader)?;
            ContentNode::Injection(side, body)
        },
        | 0x07 => {
            let body = read_index(reader)?;
            ContentNode::Thunk(body)
        },
        | 0x08 => {
            let target = read_level(reader)?;
            let body = read_index(reader)?;
            ContentNode::ValueLift { target, body }
        },
        | 0x09 => {
            let quoted = read_index(reader)?;
            ContentNode::Quote(quoted)
        },
        | 0x0A => {
            let quoted = read_index(reader)?;
            ContentNode::QuoteComputation(quoted)
        },
        | 0x0B => {
            let body = read_index(reader)?;
            ContentNode::StaticLambda(body)
        },
        | 0x0C => {
            let head = read_index(reader)?;
            let argument = read_index(reader)?;
            ContentNode::StaticApplication(head, argument)
        },
        | 0x10 => {
            let body = read_index(reader)?;
            ContentNode::Lambda(body)
        },
        | 0x11 => {
            let head = read_index(reader)?;
            let argument = read_index(reader)?;
            ContentNode::Application(head, argument)
        },
        | 0x12 => {
            let value = read_index(reader)?;
            ContentNode::Return(value)
        },
        | 0x13 => {
            let bound = read_index(reader)?;
            let rest = read_index(reader)?;
            ContentNode::Bind(bound, rest)
        },
        | 0x14 => {
            let value = read_index(reader)?;
            ContentNode::Force(value)
        },
        | 0x15 => {
            let scrutinee = read_index(reader)?;
            let on_left = read_index(reader)?;
            let on_right = read_index(reader)?;
            ContentNode::Case {
                scrutinee,
                on_left,
                on_right,
            }
        },
        | 0x20 => {
            let base = reader.tag()?;
            ContentNode::Base(match base.0 {
                | 0 => BaseType::Integer,
                | 1 => BaseType::String,
                | 2 => BaseType::Numeric,
                | _ => return Err(CodecError::Corrupt),
            })
        },
        | 0x21 => ContentNode::UnitType,
        | 0x22 => {
            let first = read_index(reader)?;
            let second = read_index(reader)?;
            ContentNode::Product(first, second)
        },
        | 0x23 => {
            let first = read_index(reader)?;
            let second = read_index(reader)?;
            ContentNode::Sum(first, second)
        },
        | 0x24 => {
            let body = read_index(reader)?;
            ContentNode::ThunkType(body)
        },
        | 0x25 => {
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Ground(GroundSort::Value),
                level,
            }
        },
        | 0x26 => {
            let inner = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::TypeLift { inner, target }
        },
        | 0x27 => {
            let code = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::Element { code, target }
        },
        | 0x28 => {
            let reference = read_reference(reader)?;
            ContentNode::Abstract(reference)
        },
        | 0x29 => {
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Ground(GroundSort::Computation),
                level,
            }
        },
        | 0x2A => {
            let parameter = reader.word()?;
            let parameter = u32::try_from(parameter.0).map_err(|_overflow| CodecError::Corrupt)?;
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Parameter(SortParameter::from(parameter)),
                level,
            }
        },
        | 0x2B => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::StaticPi { domain, codomain }
        },
        | 0x30 => {
            let result = read_index(reader)?;
            ContentNode::Returner(result)
        },
        | 0x31 => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::Arrow { domain, codomain }
        },
        | 0x32 => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::Pi { domain, codomain }
        },
        | 0x33 => {
            let code = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::ComputationElement { code, target }
        },
        | 0x40 => ContentNode::PathUniverse(read_index(reader)?, read_index(reader)?),
        | 0x41 => ContentNode::PathRefl(read_index(reader)?),
        | 0x42 => {
            let path_type = read_index(reader)?;
            let forward = read_index(reader)?;
            let backward = read_index(reader)?;
            let mut evidence = gandr_kernel_term::PathEvidence::default();
            for direction in [&mut evidence.source, &mut evidence.target] {
                let count = reader.word()?;
                for _ in 0 .. count.0 {
                    let count = reader.word()?;
                    let mut dialogue = Vec::new();
                    for _ in 0 .. count.0 {
                        let word = reader.word()?;
                        let decision = gandr_kernel_term::EvidenceWord(word.0)
                            .try_into()
                            .map_err(|_site| CodecError::Corrupt)?;
                        dialogue.push(decision);
                    }
                    direction.push(dialogue);
                }
            }
            ContentNode::PathEquiv {
                path_type,
                forward,
                backward,
                evidence: alloc::sync::Arc::new(evidence),
            }
        },
        | 0x43 => ContentNode::PathProduct(read_index(reader)?, read_index(reader)?),
        | 0x44 => ContentNode::Transport(read_index(reader)?, read_index(reader)?),
        | _ => return Err(CodecError::Corrupt),
    };
    Ok(node)
}

/// Write a table.
///
/// # Specification
/// - ensures: successful tables contain no unresolved node; an unsupported
///   refusal names the first one.
///
/// # Adequacy
/// - hypothesis: L3 — nested unresolved nodes in all four sorts retain the
///   precise refusal. Structural validation is a reader responsibility:
///   encoding a raw table does not certify its child extents, child sorts or
///   discovery order.
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
/// - witness: `codec::tests::type_tables_validate_roots_child_extents_and_sorts`
#[spec(
    ensures: |ret| match ret {
        | Ok(()) => nodes
            .iter()
            .all(|node| !matches!(*node, ContentNode::Unresolved(_))),
        | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
            nodes.iter().find_map(|node| match *node {
                | ContentNode::Unresolved(found) => Some(found),
                | _ => None,
            }) == Some(sort)
        },
        | Err(CodecError::Unrepresentable) => true,
        | _ => false,
    },
)]
fn write_nodes<Out>(
    writer: &mut Writer<'_, Out>,
    nodes: &[ContentNode],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(nodes.len()))?;
    for node in nodes {
        write_node(writer, node)?;
    }
    Ok(())
}

/// Read a table and check every child is in range and has its required sort.
///
/// # Specification
/// - requires: nothing.
/// - ensures: successful nodes are resolved and every child index names its
///   required sort. Discovery order and reachability are checked by the caller.
/// - fails: [`CodecError::Corrupt`] for malformed nodes or invalid children,
///   and [`CodecError::LevelOffsetTooLarge`] for an offset at the decoder cap.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — out-of-range and wrong-sort children are refused
///   independently of root validation; the predicate also checks table length.
/// - witness: `codec::tests::type_tables_validate_roots_child_extents_and_sorts`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref nodes) => {
            nodes.iter().all(|node| {
                !matches!(*node, ContentNode::Unresolved(_))
                    && node.children().iter().all(|(child, sort)| {
                        nodes
                            .get(usize::from(child))
                            .is_some_and(|found| found.sort() == sort)
                    })
            }) && u64::try_from(nodes.len()).is_ok_and(|count| {
                before
                    .checked_add(8)
                    .and_then(|end| reader.bytes.get(before .. end))
                    == Some(count.to_le_bytes().as_slice())
            })
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(error) => error == CodecError::Corrupt,
    },
)]
fn read_nodes(reader: &mut Reader<'_>) -> Result<Vec<ContentNode>, CodecError>
{
    let count = reader.count()?;
    let mut nodes = Vec::new();
    for _ in 0 .. count.0 {
        let node = read_node(reader)?;
        nodes.push(node);
    }
    for node in &nodes {
        for (child, sort) in node.children().iter() {
            match nodes.get(usize::from(child)) {
                | Some(found) if found.sort() == sort => {},
                | Some(_) | None => return Err(CodecError::Corrupt),
            }
        }
    }
    Ok(nodes)
}

/// Check that `nodes` is numbered by discovery from `roots`, in order.
///
/// # Specification
/// - requires: every child index of `nodes` is in range.
/// - ensures: `Ok` exactly when a breadth-first walk from the roots, children
///   left to right, discovers the indices `0, 1, …` in order and reaches them
///   all.
/// - fails: [`CodecError::NonCanonical`] otherwise; [`CodecError::Corrupt`] for
///   a root out of range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — swapped and unreachable entries are refused; empty
///   tables, repeated roots and a reachable cycle are accepted. The predicate
///   uses a scalar contiguous-frontier oracle, not a second allocated queue or
///   visited set.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `codec::tests::discovery_accepts_cycles_repeated_roots_and_empty_tables`
#[spec(
    requires: nodes.iter().all(|node| {
        node.children()
            .iter()
            .all(|(child, _)| usize::from(child) < nodes.len())
    }),
    ensures: |ret| {
        ret == 'discovery: {
            let mut next = 0_usize;
            for root in roots.iter().copied() {
                let index = usize::from(root);
                if index >= nodes.len() {
                    break 'discovery Err(CodecError::Corrupt);
                }
                if index > next {
                    break 'discovery Err(CodecError::NonCanonical);
                }
                if index == next {
                    next = next.saturating_add(1);
                }
            }
            for (index, node) in nodes.iter().enumerate() {
                if index >= next {
                    break 'discovery Err(CodecError::NonCanonical);
                }
                for (child, _) in node.children().iter() {
                    let child = usize::from(child);
                    if child > next {
                        break 'discovery Err(CodecError::NonCanonical);
                    }
                    if child == next {
                        next = next.saturating_add(1);
                    }
                }
            }
            Ok(())
        }
    },
)]
fn check_discovery(
    nodes: &[ContentNode],
    roots: &[NodeIndex],
) -> Result<(), CodecError>
{
    let mut seen = alloc::vec![false; nodes.len()];
    let mut next = 0_usize;
    let mut queue = alloc::collections::VecDeque::new();
    let mut discover = |index: NodeIndex,
                        queue: &mut alloc::collections::VecDeque<NodeIndex>|
     -> Result<(), CodecError> {
        let mark = seen
            .get_mut(usize::from(index))
            .ok_or(CodecError::Corrupt)?;
        if !*mark {
            if usize::from(index) != next {
                return Err(CodecError::NonCanonical);
            }
            *mark = true;
            next = next.saturating_add(1);
            queue.push_back(index);
        }
        Ok(())
    };
    for &root in roots {
        discover(root, &mut queue)?;
    }
    while let Some(index) = queue.pop_front() {
        let node = nodes.get(usize::from(index)).ok_or(CodecError::Corrupt)?;
        for (child, _) in node.children().iter() {
            discover(child, &mut queue)?;
        }
    }
    if next == nodes.len() {
        Ok(())
    }
    else {
        Err(CodecError::NonCanonical)
    }
}

/// Write an item's content.
///
/// # Specification
/// trivial.
pub fn write_item_content<Out>(
    sink: &mut Out,
    content: &ItemContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let mut writer = Writer { sink };
    write_item_content_with(&mut writer, content)
}

/// Write an item's content.
///
/// # Specification
/// - ensures: an unsupported refusal names the first unresolved table node;
///   metadata precedes the table.
///
/// # Adequacy
/// - hypothesis: L3 — independently built programs have identical content
///   encodings, while unresolved nodes are refused. The predicate classifies
///   table failures without duplicating serialization.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[spec(
    ensures: |ret| match ret {
        | Ok(()) => content
            .nodes()
            .iter()
            .all(|node| !matches!(*node, ContentNode::Unresolved(_))),
        | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
            content.nodes().iter().find_map(|node| match *node {
                | ContentNode::Unresolved(found) => Some(found),
                | _ => None,
            }) == Some(sort)
        },
        | Err(CodecError::Unrepresentable) => true,
        | _ => false,
    },
)]
fn write_item_content_with<Out>(
    writer: &mut Writer<'_, Out>,
    content: &ItemContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_reference(writer, content.reference())?;
    match content.signature() {
        | Maybe::Present(root) => {
            writer.tag(Tag(1));
            write_index(writer, root)?;
        },
        | Maybe::Absent(signature::Absent::Unsigned) => writer.tag(Tag(0)),
    }
    match content.body() {
        | Maybe::Present(root) => {
            writer.tag(Tag(1));
            write_index(writer, root)?;
        },
        | Maybe::Absent(body::Absent::Hole) => writer.tag(Tag(0)),
    }
    write_nodes(writer, content.nodes())
}

/// Read an item's content.
///
/// # Specification
/// - fails: as [`read_nodes`] and [`check_discovery`], and
///   [`CodecError::Corrupt`] for a signature root that is no value type or a
///   body root that is no value.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — ordinary and signed contents round-trip; swapped
///   discovery order and unreachable entries are refused. The predicate checks
///   root sorts and canonical reach without allocating a second graph. This is
///   structural validity, not a typing certificate.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::universe_sorts_and_levels_round_trip`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref content) => {
            let nodes = content.nodes();
            let roots = [
                match content.signature() {
                    | Maybe::Present(root) => Some((root, Sort::ValueType)),
                    | Maybe::Absent(_) => None,
                },
                match content.body() {
                    | Maybe::Present(root) => Some((root, Sort::Value)),
                    | Maybe::Absent(_) => None,
                },
            ];
            nodes.iter().all(|node| {
                !matches!(*node, ContentNode::Unresolved(_))
                    && node.children().iter().all(|(child, sort)| {
                        nodes
                            .get(usize::from(child))
                            .is_some_and(|found| found.sort() == sort)
                    })
            }) && roots.iter().flatten().all(|&(root, sort)| {
                nodes
                    .get(usize::from(root))
                    .is_some_and(|node| node.sort() == sort)
            }) && 'discovery: {
                let mut next = 0_usize;
                for root in roots.into_iter().flatten().map(|(root, _)| root) {
                    let index = usize::from(root);
                    if index >= nodes.len() {
                        break 'discovery Err(CodecError::Corrupt);
                    }
                    if index > next {
                        break 'discovery Err(CodecError::NonCanonical);
                    }
                    if index == next {
                        next = next.saturating_add(1);
                    }
                }
                for (index, node) in nodes.iter().enumerate() {
                    if index >= next {
                        break 'discovery Err(CodecError::NonCanonical);
                    }
                    for (child, _) in node.children().iter() {
                        let child = usize::from(child);
                        if child > next {
                            break 'discovery Err(CodecError::NonCanonical);
                        }
                        if child == next {
                            next = next.saturating_add(1);
                        }
                    }
                }
                Ok(())
            } == Ok(())
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Corrupt | CodecError::NonCanonical) => true,
        | Err(_) => false,
    },
)]
fn read_item_content(reader: &mut Reader<'_>) -> Result<ItemContent, CodecError>
{
    let reference = read_reference(reader)?;
    let signed = reader.tag()?;
    let signature = match signed.0 {
        | 0 => Maybe::Absent(signature::Absent::Unsigned),
        | 1 => {
            let root = read_index(reader)?;
            Maybe::Present(root)
        },
        | _ => return Err(CodecError::Corrupt),
    };
    let bodied = reader.tag()?;
    let body = match bodied.0 {
        | 0 => Maybe::Absent(body::Absent::Hole),
        | 1 => {
            let root = read_index(reader)?;
            Maybe::Present(root)
        },
        | _ => return Err(CodecError::Corrupt),
    };
    let nodes = read_nodes(reader)?;
    let mut roots = Vec::with_capacity(2);
    if let Maybe::Present(root) = signature {
        root_of_sort(&nodes, root, Sort::ValueType)?;
        roots.push(root);
    }
    if let Maybe::Present(root) = body {
        root_of_sort(&nodes, root, Sort::Value)?;
        roots.push(root);
    }
    check_discovery(&nodes, &roots)?;
    Ok(ItemContent::from_parts(reference, signature, body, nodes))
}

/// Require that the root `root` of `nodes` has sort `sort`.
///
/// # Specification
/// - ensures: success means the named root exists and has exactly the requested
///   sort.
///
/// # Adequacy
/// - hypothesis: L3 — a value-type root succeeds only for its own sort, and a
///   missing root is refused.
/// - witness: `codec::tests::type_tables_validate_roots_child_extents_and_sorts`
#[spec(
    ensures: |ret| {
        ret == if nodes
            .get(usize::from(root))
            .is_some_and(|node| node.sort() == sort)
        {
            Ok(())
        }
        else {
            Err(CodecError::Corrupt)
        }
    },
)]
fn root_of_sort(
    nodes: &[ContentNode],
    root: NodeIndex,
    sort: Sort,
) -> Result<(), CodecError>
{
    match nodes.get(usize::from(root)) {
        | Some(node) if node.sort() == sort => Ok(()),
        | Some(_) | None => Err(CodecError::Corrupt),
    }
}

/// Write a type's content.
///
/// # Specification
/// trivial.
fn write_type<Out>(
    writer: &mut Writer<'_, Out>,
    content: &TypeContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_nodes(writer, content.nodes())
}

/// Read a type's content.
///
/// # Specification
/// - fails: as [`read_nodes`] and [`check_discovery`], and
///   [`CodecError::Corrupt`] for an empty table or a root that is no type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, non-type, out-of-range and wrong-sort tables are
///   refused; a computation-type root is accepted. The predicate checks closed
///   children and canonical discovery from root zero, without re-encoding or
///   allocating another traversal state.
/// - witness: `codec::tests::type_tables_validate_roots_child_extents_and_sorts`
/// - witness: `persistence::tests::universe_sorts_and_levels_round_trip`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref content) => {
            let nodes = content.nodes();
            matches!(
                nodes.first().map(ContentNode::sort),
                Some(Sort::ValueType | Sort::CompType)
            ) && nodes.iter().all(|node| {
                !matches!(*node, ContentNode::Unresolved(_))
                    && node.children().iter().all(|(child, sort)| {
                        nodes
                            .get(usize::from(child))
                            .is_some_and(|found| found.sort() == sort)
                    })
            }) && 'discovery: {
                let mut next = 0_usize;
                for root in core::iter::once(NodeIndex::from(0_usize)) {
                    let index = usize::from(root);
                    if index >= nodes.len() {
                        break 'discovery Err(CodecError::Corrupt);
                    }
                    if index > next {
                        break 'discovery Err(CodecError::NonCanonical);
                    }
                    if index == next {
                        next = next.saturating_add(1);
                    }
                }
                for (index, node) in nodes.iter().enumerate() {
                    if index >= next {
                        break 'discovery Err(CodecError::NonCanonical);
                    }
                    for (child, _) in node.children().iter() {
                        let child = usize::from(child);
                        if child > next {
                            break 'discovery Err(CodecError::NonCanonical);
                        }
                        if child == next {
                            next = next.saturating_add(1);
                        }
                    }
                }
                Ok(())
            } == Ok(())
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Corrupt | CodecError::NonCanonical) => true,
        | Err(_) => false,
    },
)]
fn read_type(reader: &mut Reader<'_>) -> Result<TypeContent, CodecError>
{
    let nodes = read_nodes(reader)?;
    match nodes.first().map(ContentNode::sort) {
        | Some(Sort::ValueType | Sort::CompType) => {},
        | Some(Sort::Value | Sort::Computation) | None => return Err(CodecError::Corrupt),
    }
    check_discovery(&nodes, &[NodeIndex::from(0_usize)])?;
    Ok(TypeContent::from_nodes(nodes))
}

/// Write a set of references, ascending.
///
/// # Specification
/// - requires: the caller supplies ascending set iteration; this writer does
///   not sort it.
/// - ensures: an unrepresentable declared count is refused; later failures can
///   only be field-width refusals.
///
/// # Adequacy
/// - hypothesis: L3 — persisted footprint sets preserve their members and
///   canonical ordering. Only the declared count and error alphabet are
///   observed here: the owned iterator is not consumed a second time by the
///   predicate.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    captures: [count = references.len()],
    ensures: |ret| {
        matches!(ret, Ok(()) | Err(CodecError::Unrepresentable))
            && (u64::try_from(count).is_ok() || ret == Err(CodecError::Unrepresentable))
    },
)]
fn write_references<'set, Out, References>(
    writer: &mut Writer<'_, Out>,
    references: References,
) -> Result<(), CodecError>
where
    Out: Sink,
    References: ExactSizeIterator<Item = &'set Reference>,
{
    writer.count(Count(references.len()))?;
    for reference in references {
        write_reference(writer, reference)?;
    }
    Ok(())
}

/// Read a set of references.
///
/// # Specification
/// - ensures: duplicates collapse into a set no larger than the encoded count;
///   only a zero count yields an empty set.
///
/// # Adequacy
/// - hypothesis: L3 — reordered reference entries decode into a set and are
///   rejected by the outer canonical-byte check. The predicate bounds
///   cardinality rather than allocating a second decoded set.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref references) => match before
            .checked_add(8)
            .and_then(|end| reader.bytes.get(before .. end))
        {
            | Some(&[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7]) => {
                usize::try_from(u64::from_le_bytes([
                    byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
                ]))
                .is_ok_and(|count| {
                    references.len() <= count && references.is_empty() == (count == 0)
                })
            },
            | _ => false,
        },
        | Err(error) => error == CodecError::Corrupt,
    },
)]
fn read_references(reader: &mut Reader<'_>) -> Result<BTreeSet<Reference>, CodecError>
{
    let count = reader.count()?;
    let mut references = BTreeSet::new();
    for _ in 0 .. count.0 {
        let reference = read_reference(reader)?;
        let _fresh = references.insert(reference);
    }
    Ok(references)
}

/// Write a footprint.
///
/// # Specification
/// - ensures: encoding succeeds exactly when both set counts and every
///   reference field fit word widths.
///
/// # Adequacy
/// - hypothesis: L3 — stored footprints preserve finite reference sets and
///   their flags through persistence. The predicate checks representability,
///   not whether stored metadata describes the content.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
#[spec(
    ensures: |ret| {
        let fits = u64::try_from(footprint.reads().len()).is_ok()
            && u64::try_from(footprint.type_reads().len()).is_ok()
            && footprint.reads().all(|reference| match *reference {
                | Reference::Unoccupied => true,
                | Reference::Item {
                    ref key,
                    occurrence,
                } => {
                    u64::try_from(key.as_ref().len()).is_ok()
                        && u64::try_from(usize::from(occurrence)).is_ok()
                },
            })
            && footprint.type_reads().all(|reference| match *reference {
                | Reference::Unoccupied => true,
                | Reference::Item {
                    ref key,
                    occurrence,
                } => {
                    u64::try_from(key.as_ref().len()).is_ok()
                        && u64::try_from(usize::from(occurrence)).is_ok()
                },
            });
        ret == if fits {
            Ok(())
        }
        else {
            Err(CodecError::Unrepresentable)
        }
    },
)]
fn write_footprint<Out>(
    writer: &mut Writer<'_, Out>,
    footprint: &Footprint,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_references(writer, footprint.reads())?;
    write_references(writer, footprint.type_reads())?;
    writer.tag(match footprint.opacity() {
        | Opacity::Transparent => Tag(0),
        | Opacity::Opaque => Tag(1),
    });
    writer.tag(match footprint.hole() {
        | HoleMark::Filled => Tag(0),
        | HoleMark::Hole => Tag(1),
    });
    Ok(())
}

/// Read a footprint.
///
/// # Specification
/// - ensures: the trailing flag bytes determine opacity and hole status;
///   malformed flags are corrupt.
///
/// # Adequacy
/// - hypothesis: L3 — finite persisted footprints retain their metadata and
///   reordered sets fail outer canonicality. The flag predicate does not
///   certify read provenance or the type-read subset relation; all four flag
///   combinations are not separately witnessed. Out-of-domain opacity and hole
///   flags stop at their respective bytes.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref footprint) => {
            let flags = [
                match footprint.opacity() {
                    | Opacity::Transparent => 0,
                    | Opacity::Opaque => 1,
                },
                match footprint.hole() {
                    | HoleMark::Filled => 0,
                    | HoleMark::Hole => 1,
                },
            ];
            reader
                .cursor
                .checked_sub(2)
                .and_then(|start| reader.bytes.get(start .. reader.cursor))
                == Some(flags.as_slice())
        },
        | Err(error) => error == CodecError::Corrupt,
    },
)]
fn read_footprint(reader: &mut Reader<'_>) -> Result<Footprint, CodecError>
{
    let reads = read_references(reader)?;
    let type_reads = read_references(reader)?;
    let opacity = reader.tag()?;
    let opacity = match opacity.0 {
        | 0 => Opacity::Transparent,
        | 1 => Opacity::Opaque,
        | _ => return Err(CodecError::Corrupt),
    };
    let hole = reader.tag()?;
    let hole = match hole.0 {
        | 0 => HoleMark::Filled,
        | 1 => HoleMark::Hole,
        | _ => return Err(CodecError::Corrupt),
    };
    Ok(Footprint::from_parts(reads, type_reads, opacity, hole))
}

/// Write a site.
///
/// # Specification
/// - ensures: unreached sites always encode; a node site must fit the word
///   width.
///
/// # Adequacy
/// - hypothesis: L3 — the finite refusal corpus preserves projected sites; an
///   independent one-byte frame witnesses the unreached form. The generic sink
///   has no byte observer; the predicate states the width outcome.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    ensures: |ret| {
        ret == match site {
            | Site::Unreached => Ok(()),
            | Site::Node(index) => u64::try_from(usize::from(index))
                .map(|_| ())
                .map_err(|_overflow| CodecError::Unrepresentable),
        }
    },
)]
fn write_site<Out>(
    writer: &mut Writer<'_, Out>,
    site: Site,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match site {
        | Site::Node(index) => {
            writer.tag(Tag(0));
            write_index(writer, index)?;
        },
        | Site::Unreached => writer.tag(Tag(1)),
    }
    Ok(())
}

/// Read a site.
///
/// # Specification
/// - ensures: successful sites retain their tag and exact node-index word,
///   consuming only their own frame.
///
/// # Adequacy
/// - hypothesis: L3 — projected sites in the finite refusal corpus round-trip.
///   A fixed unreached frame consumes only its tag; an unknown tag rejects
///   before available payload bytes.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(Site::Unreached) => {
            reader.bytes.get(before) == Some(&1) && before.checked_add(1) == Some(reader.cursor)
        },
        | Ok(Site::Node(index)) => {
            reader.bytes.get(before) == Some(&0)
                && before.checked_add(9) == Some(reader.cursor)
                && u64::try_from(usize::from(index)).is_ok_and(|word| {
                    before
                        .checked_add(1)
                        .and_then(|start| reader.bytes.get(start .. reader.cursor))
                        == Some(word.to_le_bytes().as_slice())
                })
        },
        | Err(error) => error == CodecError::Corrupt && reader.cursor >= before,
    },
)]
fn read_site(reader: &mut Reader<'_>) -> Result<Site, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => {
            let index = read_index(reader)?;
            Ok(Site::Node(index))
        },
        | 1 => Ok(Site::Unreached),
        | _ => Err(CodecError::Corrupt),
    }
}

/// The tags of the unadmitted formers, in declaration order.
const FORMERS: [UnadmittedFormer; 8] = [
    UnadmittedFormer::ValueLift,
    UnadmittedFormer::NumericLiteral,
    UnadmittedFormer::NumericAtom,
    UnadmittedFormer::TypeLift,
    UnadmittedFormer::Abstract,
    UnadmittedFormer::SortParameter,
    UnadmittedFormer::TopUniverse,
    UnadmittedFormer::StaticLambda,
];

/// The shapes a rule can require, in stable wire order.
const SHAPES: [ExpectedShape; 7] = [
    ExpectedShape::Thunk,
    ExpectedShape::Returner,
    ExpectedShape::Arrow,
    ExpectedShape::Product,
    ExpectedShape::StaticPi,
    ExpectedShape::PathUniverse,
    ExpectedShape::Sum,
];

/// Write the position of `wanted` in `table` as a tag.
///
/// # Specification
/// - fails: [`CodecError::Unrepresentable`] when `wanted` is absent or its
///   first matching position does not fit in one byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — repeated values use the first position, index 255
///   encodes, index 256 is refused, and an absent value writes no tag. The
///   current callers use stable equality on enums.
/// - witness: `codec::tests::enumeration_tags_use_first_matches_and_enforce_byte_width`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    ensures: |ret| {
        ret == table
            .iter()
            .position(|entry| entry == wanted)
            .and_then(|position| u8::try_from(position).ok())
            .map(|_| ())
            .ok_or(CodecError::Unrepresentable)
    },
)]
fn write_listed<Out, Entry>(
    writer: &mut Writer<'_, Out>,
    table: &[Entry],
    wanted: &Entry,
) -> Result<(), CodecError>
where
    Out: Sink,
    Entry: PartialEq,
{
    let position = table
        .iter()
        .position(|entry| entry == wanted)
        .ok_or(CodecError::Unrepresentable)?;
    let tag = u8::try_from(position).map_err(|_overflow| CodecError::Unrepresentable)?;
    writer.tag(Tag(tag));
    Ok(())
}

/// Read a tag naming an entry of `table`.
///
/// # Specification
/// - ensures: an available tag is consumed; success is exactly membership of
///   its index in the table.
///
/// # Adequacy
/// - hypothesis: L3 — the byte-width boundary selects the expected entry, while
///   an out-of-range tag is refused. The generic entry bound has no equality
///   observer, so the predicate checks selection bounds and cursor movement;
///   concrete witnesses check the selected value.
/// - witness: `codec::tests::enumeration_tags_use_first_matches_and_enforce_byte_width`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match reader.bytes.get(before) {
        | Some(&tag) => {
            before.checked_add(1) == Some(reader.cursor)
                && ret.as_ref().map(|_| ()).map_err(|&error| error)
                    == table
                        .get(usize::from(tag))
                        .map(|_| ())
                        .ok_or(CodecError::Corrupt)
        },
        | None => reader.cursor == before && matches!(ret, Err(CodecError::Corrupt)),
    },
)]
fn read_listed<Entry>(
    reader: &mut Reader<'_>,
    table: &[Entry],
) -> Result<Entry, CodecError>
where
    Entry: Copy,
{
    let tag = reader.tag()?;
    table
        .get(usize::from(tag.0))
        .copied()
        .ok_or(CodecError::Corrupt)
}

/// Write a refusal.
///
/// # Specification
/// - ensures: an unsupported refusal names the first unresolved node in
///   serialized type-field order.
///
/// # Adequacy
/// - hypothesis: L3 — the finite corpus preserves selected refusal payloads;
///   independently malformed type fields distinguish the first and second
///   mismatch payloads. Not every refusal class is generated by the corpus. The
///   predicate does not re-serialize site or enum fields.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::checkpoint_encoding_reports_the_first_unresolved_plane`
#[spec(
    ensures: |ret| {
        let tables: [&[ContentNode]; 2] = match *refusal {
            | Refusal::TypeMismatch {
                ref synthesised,
                ref expected,
                ..
            }
            | Refusal::SortMismatch {
                ref synthesised,
                ref expected,
                ..
            }
            | Refusal::LevelMismatch {
                ref synthesised,
                ref expected,
                ..
            }
            | Refusal::FamilyArgumentClassifier {
                ref synthesised,
                ref expected,
                ..
            } => [synthesised.nodes(), expected.nodes()],
            | Refusal::ShapeMismatch { ref found, .. }
            | Refusal::StaticClassifierExpected { ref found, .. } => [found.nodes(), &[]],
            | Refusal::DependentBind {
                ref synthesised, ..
            } => [synthesised.nodes(), &[]],
            | _ => [&[], &[]],
        };
        match ret {
            | Ok(()) => tables
                .into_iter()
                .flatten()
                .all(|node| !matches!(*node, ContentNode::Unresolved(_))),
            | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
                tables.into_iter().flatten().find_map(|node| match *node {
                    | ContentNode::Unresolved(found) => Some(found),
                    | _ => None,
                }) == Some(sort)
            },
            | Err(CodecError::Unrepresentable) => true,
            | _ => false,
        }
    },
)]
fn write_refusal<Out>(
    writer: &mut Writer<'_, Out>,
    refusal: &Refusal,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *refusal {
        | Refusal::PathCode(site) => {
            writer.tag(Tag(18));
            write_site(writer, site)?;
        },
        | Refusal::TypeMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(0));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        | Refusal::ShapeMismatch {
            at,
            wanted,
            ref found,
        } => {
            writer.tag(Tag(1));
            write_site(writer, at)?;
            write_listed(writer, &SHAPES, &wanted)?;
            write_type(writer, found)?;
        },
        | Refusal::NotSynthesisable { form } => {
            writer.tag(Tag(2));
            match form {
                | Form::Injection(site) => {
                    writer.tag(Tag(5));
                    write_site(writer, site)?;
                },
                | Form::Case(site) => {
                    writer.tag(Tag(6));
                    write_site(writer, site)?;
                },
                | Form::Thunk(site) => {
                    writer.tag(Tag(0));
                    write_site(writer, site)?;
                },
                | Form::Lambda(site) => {
                    writer.tag(Tag(1));
                    write_site(writer, site)?;
                },
                | Form::Return(site) => {
                    writer.tag(Tag(2));
                    write_site(writer, site)?;
                },
                | Form::Hole => writer.tag(Tag(3)),
                | Form::StaticLambda(site) => {
                    writer.tag(Tag(4));
                    write_site(writer, site)?;
                },
            }
        },
        | Refusal::UnknownConstant { at, ref constant } => {
            writer.tag(Tag(3));
            write_site(writer, at)?;
            write_reference(writer, constant)?;
        },
        | Refusal::OutOfFragment { at, former } => {
            writer.tag(Tag(4));
            write_site(writer, at)?;
            write_listed(writer, &FORMERS, &former)?;
        },
        | Refusal::UnboundIndex {
            at,
            zone,
            index,
            depth,
        } => {
            writer.tag(Tag(5));
            write_site(writer, at)?;
            writer.tag(match zone {
                | Zone::Intuitionistic => Tag(0),
                | Zone::Linear => Tag(1),
            });
            writer.word(Word(u64::from(u32::from(index))));
            let depth = word_of(Count(usize::from(depth)))?;
            writer.word(depth);
        },
        | Refusal::BudgetExceeded { budget } => {
            writer.tag(Tag(6));
            let budget = word_of(Count(usize::from(budget)))?;
            writer.word(budget);
        },
        | Refusal::DanglingNode { at } => {
            writer.tag(Tag(7));
            write_site(writer, at)?;
        },
        | Refusal::AdmissionOrder => writer.tag(Tag(8)),
        | Refusal::MachineInvariant => writer.tag(Tag(9)),
        | Refusal::SortMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(10));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        | Refusal::LevelMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(11));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        | Refusal::DependentBind {
            at,
            ref synthesised,
        } => {
            writer.tag(Tag(12));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
        },
        | Refusal::Undecided { at } => {
            writer.tag(Tag(13));
            write_site(writer, at)?;
        },
        | Refusal::FamilyArity {
            at,
            expected,
            actual,
        } => {
            writer.tag(Tag(14));
            write_site(writer, at)?;
            writer.word(Word(u64::from(u32::from(expected))));
            writer.word(Word(u64::from(u32::from(actual))));
        },
        | Refusal::FamilyArgumentClassifier {
            at,
            position,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(15));
            write_site(writer, at)?;
            writer.word(Word(u64::from(u32::from(position))));
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        | Refusal::StaticLambdaArgument { at } => {
            writer.tag(Tag(16));
            write_site(writer, at)?;
        },
        | Refusal::StaticClassifierExpected { at, ref found } => {
            writer.tag(Tag(17));
            write_site(writer, at)?;
            write_type(writer, found)?;
        },
    }
    Ok(())
}

/// Read a count a refusal names in 32 bits: an arity or a position.
///
/// # Specification
/// - ensures: a complete word is consumed; it succeeds exactly when it fits in
///   32 bits. The generic `From<u32>` conversion supplies the returned
///   vocabulary value.
/// - fails: [`CodecError::Corrupt`] when the word exceeds `u32::MAX`, which no
///   write produces.
/// - panics: none.
///
/// # Errors
/// - [`CodecError`] — as above, or the reader's own refusal.
///
/// # Adequacy
/// - hypothesis: L3 — the largest 32-bit value succeeds and the next word is
///   refused after consumption. Persisted arities and positions witness
///   concrete vocabulary conversions; the generic output has no equality
///   observer, so the predicate checks width, errors and cursor movement.
/// - witness: `codec::tests::narrow_fields_refuse_out_of_range_words_after_consuming_them`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match before
        .checked_add(8)
        .and_then(|end| reader.bytes.get(before .. end))
    {
        | Some(&[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7]) => {
            before.checked_add(8) == Some(reader.cursor)
                && ret.as_ref().map(|_| ()).map_err(|&error| error)
                    == u32::try_from(u64::from_le_bytes([
                        byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
                    ]))
                    .map(|_| ())
                    .map_err(|_overflow| CodecError::Corrupt)
        },
        | _ => reader.cursor == before && matches!(ret, Err(CodecError::Corrupt)),
    },
)]
fn read_narrow<Count32>(reader: &mut Reader<'_>) -> Result<Count32, CodecError>
where
    Count32: From<u32>,
{
    let word = reader.word()?;
    let narrow = u32::try_from(word.0).map_err(|_overflow| CodecError::Corrupt)?;
    Ok(Count32::from(narrow))
}

/// Read a refusal.
///
/// # Specification
/// - ensures: a successful refusal retains its variant tag and only decoder
///   failures are returned.
///
/// # Adequacy
/// - hypothesis: L3 — selected refusal classes and their payloads survive the
///   finite semantic corpus. The predicate checks all tag classes without
///   reconstructing their owned type payloads; the corpus is not an exhaustive
///   refusal generator. Unknown outer tags, invalid non-synthesisable forms and
///   invalid unbound zones reject at their field before the following payload.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::narrow_fields_refuse_out_of_range_words_after_consuming_them`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref refusal) => {
            reader.bytes.get(before)
                == Some(&match *refusal {
                    | Refusal::TypeMismatch { .. } => 0,
                    | Refusal::ShapeMismatch { .. } => 1,
                    | Refusal::NotSynthesisable { .. } => 2,
                    | Refusal::UnknownConstant { .. } => 3,
                    | Refusal::OutOfFragment { .. } => 4,
                    | Refusal::UnboundIndex { .. } => 5,
                    | Refusal::BudgetExceeded { .. } => 6,
                    | Refusal::DanglingNode { .. } => 7,
                    | Refusal::AdmissionOrder => 8,
                    | Refusal::MachineInvariant => 9,
                    | Refusal::SortMismatch { .. } => 10,
                    | Refusal::LevelMismatch { .. } => 11,
                    | Refusal::DependentBind { .. } => 12,
                    | Refusal::Undecided { .. } => 13,
                    | Refusal::FamilyArity { .. } => 14,
                    | Refusal::FamilyArgumentClassifier { .. } => 15,
                    | Refusal::StaticLambdaArgument { .. } => 16,
                    | Refusal::StaticClassifierExpected { .. } => 17,
                    | Refusal::PathCode(_) => 18,
                })
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Corrupt | CodecError::NonCanonical) => true,
        | Err(_) => false,
    },
)]
fn read_refusal(reader: &mut Reader<'_>) -> Result<Refusal, CodecError>
{
    let tag = reader.tag()?;
    let refusal = match tag.0 {
        | 0 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::TypeMismatch {
                at,
                synthesised,
                expected,
            }
        },
        | 1 => {
            let at = read_site(reader)?;
            let wanted = read_listed(reader, &SHAPES)?;
            let found = read_type(reader)?;
            Refusal::ShapeMismatch { at, wanted, found }
        },
        | 2 => {
            let form = reader.tag()?;
            let form = match form.0 {
                | 0 => {
                    let site = read_site(reader)?;
                    Form::Thunk(site)
                },
                | 1 => {
                    let site = read_site(reader)?;
                    Form::Lambda(site)
                },
                | 2 => {
                    let site = read_site(reader)?;
                    Form::Return(site)
                },
                | 3 => Form::Hole,
                | 4 => {
                    let site = read_site(reader)?;
                    Form::StaticLambda(site)
                },
                | 5 => Form::Injection(read_site(reader)?),
                | 6 => Form::Case(read_site(reader)?),
                | _ => return Err(CodecError::Corrupt),
            };
            Refusal::NotSynthesisable { form }
        },
        | 3 => {
            let at = read_site(reader)?;
            let constant = read_reference(reader)?;
            Refusal::UnknownConstant { at, constant }
        },
        | 4 => {
            let at = read_site(reader)?;
            let former = read_listed(reader, &FORMERS)?;
            Refusal::OutOfFragment { at, former }
        },
        | 5 => {
            let at = read_site(reader)?;
            let zone = reader.tag()?;
            let zone = match zone.0 {
                | 0 => Zone::Intuitionistic,
                | 1 => Zone::Linear,
                | _ => return Err(CodecError::Corrupt),
            };
            let index = reader.word()?;
            let index = u32::try_from(index.0).map_err(|_overflow| CodecError::Corrupt)?;
            let depth = reader.count()?;
            Refusal::UnboundIndex {
                at,
                zone,
                index: DeBruijnIndex::from(index),
                depth: BinderDepth::from(depth.0),
            }
        },
        | 6 => {
            let budget = reader.count()?;
            Refusal::BudgetExceeded {
                budget: CheckBudget::from(budget.0),
            }
        },
        | 7 => {
            let at = read_site(reader)?;
            Refusal::DanglingNode { at }
        },
        | 8 => Refusal::AdmissionOrder,
        | 9 => Refusal::MachineInvariant,
        | 10 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::SortMismatch {
                at,
                synthesised,
                expected,
            }
        },
        | 11 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::LevelMismatch {
                at,
                synthesised,
                expected,
            }
        },
        | 12 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            Refusal::DependentBind { at, synthesised }
        },
        | 13 => {
            let at = read_site(reader)?;
            Refusal::Undecided { at }
        },
        | 14 => {
            let at = read_site(reader)?;
            let expected: StaticArity = read_narrow(reader)?;
            let actual: StaticArity = read_narrow(reader)?;
            Refusal::FamilyArity {
                at,
                expected,
                actual,
            }
        },
        | 15 => {
            let at = read_site(reader)?;
            let position: ArgumentPosition = read_narrow(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::FamilyArgumentClassifier {
                at,
                position,
                synthesised,
                expected,
            }
        },
        | 16 => {
            let at = read_site(reader)?;
            Refusal::StaticLambdaArgument { at }
        },
        | 17 => {
            let at = read_site(reader)?;
            let found = read_type(reader)?;
            Refusal::StaticClassifierExpected { at, found }
        },
        | 18 => Refusal::PathCode(read_site(reader)?),
        | _ => return Err(CodecError::Corrupt),
    };
    Ok(refusal)
}

/// Write a typing.
///
/// # Specification
/// - ensures: owed and checked verdicts have no unresolved type payload; other
///   verdicts refuse the first unresolved type node.
///
/// # Adequacy
/// - hypothesis: L3 — checked, synthesised, owed and selected refused verdicts
///   round-trip. Malformed synthesised and refused payloads distinguish their
///   failure paths; the predicate classifies type-plane failures rather than
///   reproducing the byte encoding.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::checkpoint_encoding_reports_the_first_unresolved_plane`
#[spec(
    ensures: |ret| match *typing {
        | Typing::Owed => ret == Ok(()),
        | Typing::Checked { conversions } => {
            ret == u64::try_from(usize::from(conversions))
                .map(|_| ())
                .map_err(|_overflow| CodecError::Unrepresentable)
        },
        | _ => {
            let tables: [&[ContentNode]; 2] = match *typing {
                | Typing::Synthesised { ref produced, .. } => [produced.nodes(), &[]],
                | Typing::Refused(ref refusal) => match *refusal {
                    | Refusal::TypeMismatch {
                        ref synthesised,
                        ref expected,
                        ..
                    }
                    | Refusal::SortMismatch {
                        ref synthesised,
                        ref expected,
                        ..
                    }
                    | Refusal::LevelMismatch {
                        ref synthesised,
                        ref expected,
                        ..
                    }
                    | Refusal::FamilyArgumentClassifier {
                        ref synthesised,
                        ref expected,
                        ..
                    } => [synthesised.nodes(), expected.nodes()],
                    | Refusal::ShapeMismatch { ref found, .. }
                    | Refusal::StaticClassifierExpected { ref found, .. } => {
                        [found.nodes(), &[]]
                    },
                    | Refusal::DependentBind {
                        ref synthesised, ..
                    } => [synthesised.nodes(), &[]],
                    | _ => [&[], &[]],
                },
                | Typing::Checked { .. } | Typing::Owed => [&[], &[]],
            };
            match ret {
                | Ok(()) => tables
                    .into_iter()
                    .flatten()
                    .all(|node| !matches!(*node, ContentNode::Unresolved(_))),
                | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
                    tables.into_iter().flatten().find_map(|node| match *node {
                        | ContentNode::Unresolved(found) => Some(found),
                        | _ => None,
                    }) == Some(sort)
                },
                | Err(CodecError::Unrepresentable) => true,
                | _ => false,
            }
        },
    },
)]
fn write_typing<Out>(
    writer: &mut Writer<'_, Out>,
    typing: &Typing,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *typing {
        | Typing::Checked { conversions } => {
            writer.tag(Tag(0));
            writer.count(Count(usize::from(conversions)))?;
        },
        | Typing::Synthesised {
            ref produced,
            conversions,
        } => {
            writer.tag(Tag(1));
            write_type(writer, produced)?;
            writer.count(Count(usize::from(conversions)))?;
        },
        | Typing::Owed => writer.tag(Tag(2)),
        | Typing::Refused(ref refusal) => {
            writer.tag(Tag(3));
            write_refusal(writer, refusal)?;
        },
    }
    Ok(())
}

/// Read a typing.
///
/// # Specification
/// - ensures: successful verdicts retain the input tag; failures belong to the
///   decoder error alphabet.
///
/// # Adequacy
/// - hypothesis: L3 — checked, synthesised, owed and selected refused verdicts
///   preserve their payloads. Tag classification is executable; this finite
///   corpus does not witness every malformed field. An unknown outer tag stops
///   before the available payload.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref typing) => {
            reader.bytes.get(before)
                == Some(&match *typing {
                    | Typing::Checked { .. } => 0,
                    | Typing::Synthesised { .. } => 1,
                    | Typing::Owed => 2,
                    | Typing::Refused(_) => 3,
                })
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Corrupt | CodecError::NonCanonical) => true,
        | Err(_) => false,
    },
)]
fn read_typing(reader: &mut Reader<'_>) -> Result<Typing, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => {
            let conversions = reader.count()?;
            Ok(Typing::Checked {
                conversions: ConversionCount::from(conversions.0),
            })
        },
        | 1 => {
            let produced = read_type(reader)?;
            let conversions = reader.count()?;
            Ok(Typing::Synthesised {
                produced,
                conversions: ConversionCount::from(conversions.0),
            })
        },
        | 2 => Ok(Typing::Owed),
        | 3 => {
            let refusal = read_refusal(reader)?;
            Ok(Typing::Refused(refusal))
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write an answer.
///
/// # Specification
/// - ensures: untyped answers always encode; typed answers refuse their first
///   unresolved node.
///
/// # Adequacy
/// - hypothesis: L3 — structured support answers survive persistence, and a
///   malformed support type is refused before a later malformed verdict.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::checkpoint_encoding_reports_the_first_unresolved_plane`
#[spec(
    ensures: |ret| match *answer {
        | Answer::Untyped => ret == Ok(()),
        | Answer::Typed(ref ty) => match ret {
            | Ok(()) => ty
                .nodes()
                .iter()
                .all(|node| !matches!(*node, ContentNode::Unresolved(_))),
            | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
                ty.nodes().iter().find_map(|node| match *node {
                    | ContentNode::Unresolved(found) => Some(found),
                    | _ => None,
                }) == Some(sort)
            },
            | Err(CodecError::Unrepresentable) => true,
            | _ => false,
        },
    },
)]
fn write_answer<Out>(
    writer: &mut Writer<'_, Out>,
    answer: &Answer,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *answer {
        | Answer::Untyped => writer.tag(Tag(0)),
        | Answer::Typed(ref ty) => {
            writer.tag(Tag(1));
            write_type(writer, ty)?;
        },
    }
    Ok(())
}

/// Read an answer.
///
/// # Specification
/// - ensures: tag zero yields an untyped answer; tag one yields a value- or
///   computation-type table.
///
/// # Adequacy
/// - hypothesis: L3 — persisted support contains structured typed answers and
///   preserves them on decoding. The predicate checks tag and root class, not
///   provenance from a checker. An unknown outer tag stops before the available
///   payload.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(Answer::Untyped) => reader.bytes.get(before) == Some(&0),
        | Ok(Answer::Typed(ref ty)) => {
            reader.bytes.get(before) == Some(&1)
                && matches!(
                    ty.nodes().first().map(ContentNode::sort),
                    Some(Sort::ValueType | Sort::CompType)
                )
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Corrupt | CodecError::NonCanonical) => true,
        | Err(_) => false,
    },
)]
fn read_answer(reader: &mut Reader<'_>) -> Result<Answer, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => Ok(Answer::Untyped),
        | 1 => {
            let ty = read_type(reader)?;
            Ok(Answer::Typed(ty))
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write one item's checkpoint.
///
/// # Specification
/// - ensures: the first unresolved node is sought in content, then support,
///   then verdict field order.
///
/// # Adequacy
/// - hypothesis: L3 — separate malformed content, support, synthesised and
///   two-field refused payloads identify the first failing plane. Successful
///   finite checkpoints preserve every stored field. The predicate scans
///   borrowed tables; it neither clones payloads nor serializes them again.
/// - witness: `codec::tests::checkpoint_encoding_reports_the_first_unresolved_plane`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    ensures: |ret| {
        let typing = checkpoint.typing();
        let tables: [&[ContentNode]; 2] = match *typing {
            | Typing::Synthesised { ref produced, .. } => [produced.nodes(), &[]],
            | Typing::Refused(ref refusal) => match *refusal {
                | Refusal::TypeMismatch {
                    ref synthesised,
                    ref expected,
                    ..
                }
                | Refusal::SortMismatch {
                    ref synthesised,
                    ref expected,
                    ..
                }
                | Refusal::LevelMismatch {
                    ref synthesised,
                    ref expected,
                    ..
                }
                | Refusal::FamilyArgumentClassifier {
                    ref synthesised,
                    ref expected,
                    ..
                } => [synthesised.nodes(), expected.nodes()],
                | Refusal::ShapeMismatch { ref found, .. }
                | Refusal::StaticClassifierExpected { ref found, .. } => [found.nodes(), &[]],
                | Refusal::DependentBind {
                    ref synthesised, ..
                } => [synthesised.nodes(), &[]],
                | _ => [&[], &[]],
            },
            | Typing::Checked { .. } | Typing::Owed => [&[], &[]],
        };
        let support =
            checkpoint
                .support()
                .iter()
                .flat_map(|answered| match *answered.answer() {
                    | Answer::Typed(ref ty) => ty.nodes(),
                    | Answer::Untyped => &[],
                });
        let mut nodes = checkpoint
            .content()
            .nodes()
            .iter()
            .chain(support)
            .chain(tables.into_iter().flatten());
        match ret {
            | Ok(()) => nodes.all(|node| !matches!(*node, ContentNode::Unresolved(_))),
            | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
                nodes.find_map(|node| match *node {
                    | ContentNode::Unresolved(found) => Some(found),
                    | _ => None,
                }) == Some(sort)
            },
            | Err(CodecError::Unrepresentable) => true,
            | _ => false,
        }
    },
)]
fn write_checkpoint<Out>(
    writer: &mut Writer<'_, Out>,
    checkpoint: &ItemCheckpoint,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_item_content_with(writer, checkpoint.content())?;
    write_footprint(writer, checkpoint.footprint())?;
    writer.count(Count(checkpoint.support().len()))?;
    for answered in checkpoint.support() {
        write_reference(writer, answered.reference())?;
        write_answer(writer, answered.answer())?;
    }
    write_typing(writer, checkpoint.typing())
}

/// Read one item's checkpoint.
///
/// # Specification
/// - ensures: the checkpoint retains its source reference and its support is
///   sorted with unique references.
///
/// # Adequacy
/// - hypothesis: L3 — persisted finite checkpoints preserve content, footprint,
///   support and verdict. The predicate checks the source identity and
///   canonical support order; it does not assert that stored metadata is a
///   checker certificate or decode a second copy.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref checkpoint) => {
            let reference = checkpoint.content().reference();
            let length = match *reference {
                | Reference::Unoccupied => Some(1),
                | Reference::Item { ref key, .. } => key.as_ref().len().checked_add(17),
            };
            let support = checkpoint.support();
            length
                .and_then(|length| before.checked_add(length))
                .and_then(|end| reader.bytes.get(before .. end))
                .is_some_and(|bytes| match *reference {
                    | Reference::Unoccupied => bytes == [0],
                    | Reference::Item {
                        ref key,
                        occurrence,
                    } => {
                        bytes.first() == Some(&1)
                            && u64::try_from(key.as_ref().len()).is_ok_and(|count| {
                                bytes.get(1 .. 9) == Some(count.to_le_bytes().as_slice())
                            })
                            && bytes
                                .get(9 ..)
                                .and_then(|tail| tail.strip_prefix(key.as_ref()))
                                .is_some_and(|tail| {
                                    u64::try_from(usize::from(occurrence))
                                        .is_ok_and(|word| tail == word.to_le_bytes())
                                })
                    },
                })
                && support
                    .iter()
                    .zip(support.iter().skip(1))
                    .all(|(first, second)| first.reference() < second.reference())
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Corrupt | CodecError::NonCanonical) => true,
        | Err(_) => false,
    },
)]
fn read_checkpoint(reader: &mut Reader<'_>) -> Result<ItemCheckpoint, CodecError>
{
    let content = read_item_content(reader)?;
    let footprint = read_footprint(reader)?;
    let count = reader.count()?;
    let mut support = Vec::new();
    for _ in 0 .. count.0 {
        let reference = read_reference(reader)?;
        let answer = read_answer(reader)?;
        support.push(Answered::new(reference, answer));
    }
    let typing = read_typing(reader)?;
    Ok(ItemCheckpoint::new(content, footprint, support, typing))
}

/// Check the decoder work bound in every checkpoint plane without copying it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when every level atom is below the decoder cap.
/// - fails: the first capped offset in content, support, then typing order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — checker-produced capped levels leave memory and file
///   records intact. Five node families and every auxiliary type slot are
///   exercised; the predicate bounds reported offsets and checks item levels on
///   success, without cloning the checkpoint.
/// - witness: `persistence::tests::stores_refuse_capped_levels_without_replacing_records`
/// - witness: `codec::tests::encoding_bounds_levels_in_every_node_family_and_plane`
/// - witness: `codec::tests::encoding_bounds_levels_in_every_auxiliary_type_table`
#[spec(
    ensures: |ret| match ret {
        | Ok(()) => checkpoint.content().nodes().iter().all(|node| match *node {
            | ContentNode::ValueLift { ref target, .. }
            | ContentNode::TypeLift { ref target, .. }
            | ContentNode::Element { ref target, .. }
            | ContentNode::ComputationElement { ref target, .. }
            | ContentNode::Universe {
                level: ref target, ..
            } => target
                .atoms()
                .all(|(_, offset)| u64::from(offset) < MAX_DECODED_LEVEL_OFFSET),
            | _ => true,
        }),
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(_) => false,
    },
)]
fn check_checkpoint_levels(checkpoint: &ItemCheckpoint) -> Result<(), CodecError>
{
    let types = match *checkpoint.typing() {
        | Typing::Synthesised { ref produced, .. } => [Some(produced), None],
        | Typing::Refused(ref refusal) => match *refusal {
            | Refusal::TypeMismatch {
                ref synthesised,
                ref expected,
                ..
            }
            | Refusal::SortMismatch {
                ref synthesised,
                ref expected,
                ..
            }
            | Refusal::LevelMismatch {
                ref synthesised,
                ref expected,
                ..
            }
            | Refusal::FamilyArgumentClassifier {
                ref synthesised,
                ref expected,
                ..
            } => [Some(synthesised), Some(expected)],
            | Refusal::ShapeMismatch { ref found, .. }
            | Refusal::StaticClassifierExpected { ref found, .. } => [Some(found), None],
            | Refusal::DependentBind {
                ref synthesised, ..
            } => [Some(synthesised), None],
            | _ => [None, None],
        },
        | Typing::Checked { .. } | Typing::Owed => [None, None],
    };
    let support = checkpoint
        .support()
        .iter()
        .filter_map(|answered| match *answered.answer() {
            | Answer::Typed(ref content) => Some(content.nodes()),
            | Answer::Untyped => None,
        });
    let nodes = core::iter::once(checkpoint.content().nodes())
        .chain(support)
        .chain(types.into_iter().flatten().map(TypeContent::nodes))
        .flatten();
    for node in nodes {
        let (ContentNode::ValueLift { ref target, .. }
        | ContentNode::TypeLift { ref target, .. }
        | ContentNode::Element { ref target, .. }
        | ContentNode::ComputationElement { ref target, .. }
        | ContentNode::Universe {
            level: ref target, ..
        }) = *node
        else {
            continue;
        };
        for (_, offset) in target.atoms() {
            if u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET {
                return Err(CodecError::LevelOffsetTooLarge { offset });
            }
        }
    }
    Ok(())
}

/// The canonical bytes of a checkpoint set.
///
/// # Specification
/// - requires: tables retain the canonical numbering and sorts established by
///   their producers or validated decoding; unresolved nodes remain admissible.
/// - ensures: the returned frame decodes to the supplied checkpoint set.
/// - fails: capped level offsets before framing, or an unsupported node or
///   unrepresentable count while framing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — fixed empty-envelope bytes preserve budget and version;
///   finite nonempty corpora preserve their fields. Capped levels are refused
///   before a store can replace a readable record. The predicate checks the
///   envelope and cap payload without decoding a copy.
/// - witness: `codec::tests::empty_envelopes_preserve_budget_and_separate_formats`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::checkpoint_encoding_reports_the_first_unresolved_plane`
/// - witness: `persistence::tests::stores_refuse_capped_levels_without_replacing_records`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref bytes) => {
            let bytes = bytes.as_ref();
            bytes.get(.. 8) == Some(CHECKPOINTS_MAGIC.as_slice())
                && u64::try_from(usize::from(checkpoints.budget())).is_ok_and(|budget| {
                    bytes.get(8 .. 16) == Some(budget.to_le_bytes().as_slice())
                })
                && u64::try_from(checkpoints.items().len()).is_ok_and(|count| {
                    bytes.get(16 .. 24) == Some(count.to_le_bytes().as_slice())
                })
                && (!checkpoints.items().is_empty() || bytes.len() == 24)
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Unsupported(_) | CodecError::Unrepresentable) => true,
        | Err(_) => false,
    },
)]
pub fn encode_checkpoints(checkpoints: &Checkpoints) -> Result<CheckpointBytes, CodecError>
{
    for checkpoint in checkpoints.items() {
        check_checkpoint_levels(checkpoint)?;
    }
    checkpoint_frame(checkpoints)
}

/// Frame checkpoint fields without checking graph canonicality or the decode
/// cap.
///
/// # Specification
/// - requires: nothing; invalid tables are admissible for wire-level fixtures.
/// - ensures: magic, budget and each checkpoint's fields are written in order.
/// - fails: the first unresolved plane or an unrepresentable count.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — fixed envelopes distinguish the format and preserve
///   budget; deliberately invalid tables and capped levels remain representable
///   as wire fixtures. This is also the decoder’s canonical comparison, after
///   validation.
/// - witness: `codec::tests::empty_envelopes_preserve_budget_and_separate_formats`
/// - witness: `codec::tests::checkpoint_encoding_reports_the_first_unresolved_plane`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref bytes) => {
            bytes.as_ref().get(.. 8) == Some(CHECKPOINTS_MAGIC.as_slice())
                && u64::try_from(usize::from(checkpoints.budget())).is_ok_and(|budget| {
                    bytes.as_ref().get(8 .. 16) == Some(budget.to_le_bytes().as_slice())
                })
        },
        | Err(CodecError::Unsupported(_) | CodecError::Unrepresentable) => true,
        | Err(_) => false,
    },
)]
pub fn checkpoint_frame(checkpoints: &Checkpoints) -> Result<CheckpointBytes, CodecError>
{
    let mut bytes = CheckpointBytes::default();
    let mut writer = Writer { sink: &mut bytes };
    writer.sink.put(Bytes(CHECKPOINTS_MAGIC));
    let budget = word_of(Count(usize::from(checkpoints.budget())))?;
    writer.word(budget);
    writer.count(Count(checkpoints.items().len()))?;
    for checkpoint in checkpoints.items() {
        write_checkpoint(&mut writer, checkpoint)?;
    }
    Ok(bytes)
}

/// The checkpoint set `bytes` spell.
///
/// # Specification
/// - requires: nothing — any bytes are admissible input.
/// - ensures: on success the one checkpoint set whose canonical bytes are
///   exactly `bytes`.
/// - fails: [`CodecError::Corrupt`] for truncated, malformed or trailing bytes;
///   [`CodecError::LevelOffsetTooLarge`] for an offset at the cap;
///   [`CodecError::NonCanonical`] for a payload that parses but is not the
///   canonical spelling of what it parses to.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — fixed empty-envelope bytes and finite semantic corpora
///   decode exactly, while every proper prefix of a populated checkpoint, wrong
///   magic, trailing bytes, noncanonical tables and the level cap are refused.
///   The predicate checks the envelope and failure classes; the decoder already
///   performs the full canonical re-encoding comparison.
/// - witness: `codec::tests::empty_envelopes_preserve_budget_and_separate_formats`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref checkpoints) => {
            let bytes = bytes.0;
            bytes.get(.. 8) == Some(CHECKPOINTS_MAGIC.as_slice())
                && u64::try_from(usize::from(checkpoints.budget())).is_ok_and(|budget| {
                    bytes.get(8 .. 16) == Some(budget.to_le_bytes().as_slice())
                })
                && u64::try_from(checkpoints.items().len()).is_ok_and(|count| {
                    bytes.get(16 .. 24) == Some(count.to_le_bytes().as_slice())
                })
                && (!checkpoints.items().is_empty() || bytes.len() == 24)
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(CodecError::Corrupt | CodecError::NonCanonical) => true,
        | Err(_) => false,
    },
)]
pub fn decode_checkpoints(bytes: Bytes<'_>) -> Result<Checkpoints, CodecError>
{
    let mut reader = Reader {
        bytes: bytes.0,
        cursor: 0,
    };
    let magic = reader.take(Count(CHECKPOINTS_MAGIC.len()))?;
    if magic.0 != CHECKPOINTS_MAGIC {
        return Err(CodecError::Corrupt);
    }
    let budget = reader.count()?;
    let count = reader.count()?;
    let mut items = Vec::new();
    for _ in 0 .. count.0 {
        let checkpoint = read_checkpoint(&mut reader)?;
        items.push(checkpoint);
    }
    reader.finish()?;
    let checkpoints = Checkpoints::new(CheckBudget::from(budget.0), items);
    let canonical = checkpoint_frame(&checkpoints)?;
    if canonical.0.as_slice() == bytes.0 {
        Ok(checkpoints)
    }
    else {
        Err(CodecError::NonCanonical)
    }
}

/// Write the canonical program bytes an address is computed over.
///
/// # Specification
/// - requires: `contents` are a program's items' contents, in order.
/// - ensures: the magic, the count, then each item's content.
/// - fails: [`CodecError::Unsupported`] naming the first unresolved node met.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — fixed empty program bytes have a distinct format prefix;
///   changed source order changes program identity, and unresolved content is
///   refused with its exact sort. The predicate checks the unresolved-node
///   order because the generic sink has no byte observer.
/// - witness: `codec::tests::empty_envelopes_preserve_budget_and_separate_formats`
/// - witness: `persistence::tests::meaningful_program_changes_and_source_order_change_identity`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[spec(
    ensures: |ret| match ret {
        | Ok(()) => contents
            .iter()
            .flat_map(ItemContent::nodes)
            .all(|node| !matches!(*node, ContentNode::Unresolved(_))),
        | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
            contents
                .iter()
                .flat_map(ItemContent::nodes)
                .find_map(|node| match *node {
                    | ContentNode::Unresolved(found) => Some(found),
                    | _ => None,
                })
                == Some(sort)
        },
        | Err(CodecError::Unrepresentable) => true,
        | _ => false,
    },
)]
pub fn write_program<Out>(
    sink: &mut Out,
    contents: &[ItemContent],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let mut writer = Writer { sink };
    writer.sink.put(Bytes(PROGRAM_MAGIC));
    writer.count(Count(contents.len()))?;
    for content in contents {
        write_item_content_with(&mut writer, content)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests
{

    #[test]
    fn native_names_and_operand_order_survive_persistence()
    {
        use gandr_core_term::primitive::Arguments;
        use gandr_core_term::primitive::PRELUDE;
        let sub = PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name().as_ref() == "sub")
            .unwrap();
        let neg = PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name().as_ref() == "neg")
            .unwrap();
        for node in [
            ContentNode::PrimitiveValue(sub),
            ContentNode::Primitive(
                sub,
                Arguments::Binary([NodeIndex::from(4_usize), NodeIndex::from(2_usize)]),
            ),
            ContentNode::Primitive(neg, Arguments::Unary(NodeIndex::from(3_usize))),
        ] {
            let mut bytes = CheckpointBytes::default();
            super::write_node(&mut Writer { sink: &mut bytes }, &node).unwrap();
            let mut reader = Reader {
                bytes: bytes.as_ref(),
                cursor: 0,
            };
            assert_eq!(super::read_node(&mut reader), Ok(node));
            assert_eq!(reader.finish(), Ok(()));
        }
        let mut bytes = CheckpointBytes::default();
        let mut writer = Writer { sink: &mut bytes };
        writer.tag(Tag(0x0d));
        writer.bytes(Bytes(b"not-a-native-row")).unwrap();
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_node(&mut reader), Err(CodecError::Corrupt));
    }

    use super::Answer;
    use super::Answered;
    use super::BTreeSet;
    use super::Bytes;
    use super::CheckBudget;
    use super::CheckpointBytes;
    use super::Checkpoints;
    use super::CodecError;
    use super::ContentNode;
    use super::ConversionCount;
    use super::Count;
    use super::Footprint;
    use super::HoleMark;
    use super::ItemCheckpoint;
    use super::ItemContent;
    use super::ItemKey;
    use super::Maybe;
    use super::NodeIndex;
    use super::Occurrence;
    use super::Opacity;
    use super::Reader;
    use super::Reference;
    use super::Refusal;
    use super::Sink;
    use super::Site;
    use super::Sort;
    use super::Tag;
    use super::TypeContent;
    use super::Typing;
    use super::UnsupportedPersistence;
    use super::Word;
    use super::Writer;
    use super::check_discovery;
    use super::decode_checkpoints;
    use super::encode_checkpoints;
    use super::read_listed;
    use super::read_narrow;
    use super::read_reference;
    use super::read_type;
    use super::reference_bytes;
    use super::root_of_sort;
    use super::signature;
    use super::write_listed;
    use super::write_nodes;
    use super::write_program;

    #[test]
    fn primitive_frames_have_known_bytes_and_digest()
    {
        let expected = [
            0xaa, 0x7f, 8, 7, 6, 5, 4, 3, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0x80,
        ];
        let mut bytes = CheckpointBytes::from(vec![0xaa]);
        let mut writer = Writer { sink: &mut bytes };
        writer.tag(Tag(0x7f));
        writer.word(Word(0x0102_0304_0506_0708));
        writer
            .bytes(Bytes(&[0, 0xff, 0x80]))
            .expect("representable payload");
        assert_eq!(bytes.as_ref(), expected);

        let mut hasher = blake3::Hasher::new();
        Sink::put(&mut hasher, Bytes(&[0xaa]));
        let mut writer = Writer { sink: &mut hasher };
        writer.tag(Tag(0x7f));
        writer.word(Word(0x0102_0304_0506_0708));
        writer
            .bytes(Bytes(&[0, 0xff, 0x80]))
            .expect("representable payload");
        assert_eq!(hasher.count(), 21);
        assert_eq!(hasher.finalize(), blake3::hash(&expected));
    }

    #[test]
    fn primitive_reads_preserve_cursor_on_extent_failure()
    {
        let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 0x7f];
        let mut reader = Reader {
            bytes: &bytes,
            cursor: 0,
        };
        assert_eq!(reader.finish(), Err(CodecError::Corrupt));
        assert_eq!(reader.cursor, 0);
        assert_eq!(reader.word(), Ok(Word(0x0807_0605_0403_0201)));
        assert_eq!(reader.cursor, 8);
        assert_eq!(reader.tag(), Ok(Tag(0x7f)));
        assert_eq!(reader.finish(), Ok(()));
        assert_eq!(reader.take(Count(0)), Ok(Bytes(&[])));
        assert_eq!(reader.cursor, 9);
        assert_eq!(reader.tag(), Err(CodecError::Corrupt));
        assert_eq!(reader.cursor, 9);

        let mut short = Reader {
            bytes: &[1, 2, 3, 4, 5, 6, 7],
            cursor: 0,
        };
        assert_eq!(short.word(), Err(CodecError::Corrupt));
        assert_eq!(short.cursor, 0);
        let mut overflow = Reader {
            bytes: &[],
            cursor: usize::MAX,
        };
        assert_eq!(overflow.take(Count(1)), Err(CodecError::Corrupt));
        assert_eq!(overflow.cursor, usize::MAX);
    }

    #[test]
    fn framed_failures_retain_consumed_prefixes()
    {
        let mut short = Reader {
            bytes: &[3, 0, 0, 0, 0, 0, 0, 0, 0xab, 0xcd],
            cursor: 0,
        };
        assert_eq!(short.bytes(), Err(CodecError::Corrupt));
        assert_eq!(short.cursor, 8);
        assert_eq!(short.tag(), Ok(Tag(0xab)));

        let mut invalid = Reader {
            bytes: &[1, 0, 0, 0, 0, 0, 0, 0, 0xff, 0x7f],
            cursor: 0,
        };
        assert_eq!(invalid.text(), Err(CodecError::Corrupt));
        assert_eq!(invalid.cursor, 9);
        assert_eq!(invalid.tag(), Ok(Tag(0x7f)));
        assert_eq!(invalid.finish(), Ok(()));

        let mut text = Reader {
            bytes: &[2, 0, 0, 0, 0, 0, 0, 0, 0xc3, 0xa9, 0, 0, 0, 0, 0, 0, 0, 0],
            cursor: 0,
        };
        assert_eq!(text.text().as_deref(), Ok("é"));
        assert_eq!(text.cursor, 10);
        assert_eq!(text.text().as_deref(), Ok(""));
        assert_eq!(text.finish(), Ok(()));
    }

    #[test]
    fn reference_frames_preserve_binary_keys_and_occurrences()
    {
        let occupied = Reference::Item {
            key: ItemKey::from([0, 0xff].as_slice()),
            occurrence: Occurrence::from(2_usize),
        };
        let expected = [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 2, 0, 0, 0, 0, 0, 0, 0];
        assert_eq!(reference_bytes(&occupied).as_ref(), expected);
        let mut reader = Reader {
            bytes: &expected,
            cursor: 0,
        };
        assert_eq!(read_reference(&mut reader), Ok(occupied));
        assert_eq!(reader.finish(), Ok(()));
        assert_eq!(reference_bytes(&Reference::Unoccupied).as_ref(), [0]);
        let mut empty = Reader {
            bytes: &[0],
            cursor: 0,
        };
        assert_eq!(read_reference(&mut empty), Ok(Reference::Unoccupied));
        assert_eq!(empty.finish(), Ok(()));
        let mut unknown = Reader {
            bytes: &[2],
            cursor: 0,
        };
        assert_eq!(read_reference(&mut unknown), Err(CodecError::Corrupt));
        assert_eq!(unknown.cursor, 1);
    }

    #[test]
    fn discovery_accepts_cycles_repeated_roots_and_empty_tables()
    {
        assert_eq!(check_discovery(&[], &[]), Ok(()));
        let nodes = [
            ContentNode::Product(NodeIndex::from(0_usize), NodeIndex::from(1_usize)),
            ContentNode::UnitType,
        ];
        assert_eq!(
            check_discovery(&nodes, &[
                NodeIndex::from(0_usize),
                NodeIndex::from(0_usize)
            ]),
            Ok(())
        );
        assert_eq!(
            check_discovery(&nodes, &[NodeIndex::from(usize::MAX)]),
            Err(CodecError::Corrupt)
        );
    }

    #[test]
    fn type_tables_validate_roots_child_extents_and_sorts()
    {
        let nodes = [ContentNode::UnitType];
        assert_eq!(
            root_of_sort(&nodes, NodeIndex::from(0_usize), Sort::ValueType),
            Ok(())
        );
        assert_eq!(
            root_of_sort(&nodes, NodeIndex::from(0_usize), Sort::Value),
            Err(CodecError::Corrupt)
        );
        assert_eq!(
            root_of_sort(&nodes, NodeIndex::from(usize::MAX), Sort::ValueType),
            Err(CodecError::Corrupt)
        );
        let decode = |nodes: Vec<ContentNode>| {
            let mut bytes = CheckpointBytes::default();
            write_nodes(&mut Writer { sink: &mut bytes }, &nodes).expect("raw table encodes");
            read_type(&mut Reader {
                bytes: bytes.as_ref(),
                cursor: 0,
            })
        };
        assert_eq!(decode(vec![]), Err(CodecError::Corrupt));
        assert_eq!(decode(vec![ContentNode::Unit]), Err(CodecError::Corrupt));
        assert_eq!(
            decode(vec![ContentNode::Product(
                NodeIndex::from(1_usize),
                NodeIndex::from(0_usize)
            ),]),
            Err(CodecError::Corrupt)
        );
        assert_eq!(
            decode(vec![
                ContentNode::Product(NodeIndex::from(1_usize), NodeIndex::from(1_usize)),
                ContentNode::Unit,
            ]),
            Err(CodecError::Corrupt)
        );
        let computation = decode(vec![
            ContentNode::Returner(NodeIndex::from(1_usize)),
            ContentNode::UnitType,
        ])
        .expect("closed computation type");
        assert_eq!(
            computation.nodes().first().map(ContentNode::sort),
            Some(Sort::CompType)
        );
    }

    #[test]
    fn enumeration_tags_use_first_matches_and_enforce_byte_width()
    {
        let mut bytes = CheckpointBytes::default();
        write_listed(&mut Writer { sink: &mut bytes }, &[3_u16, 8, 3], &3)
            .expect("first match fits");
        let table: Vec<u16> = (0 ..= 256).collect();
        write_listed(&mut Writer { sink: &mut bytes }, &table, &255).expect("last byte index");
        assert_eq!(
            write_listed(&mut Writer { sink: &mut bytes }, &table, &256),
            Err(CodecError::Unrepresentable)
        );
        assert_eq!(
            write_listed(&mut Writer { sink: &mut bytes }, &[3_u16, 8], &9),
            Err(CodecError::Unrepresentable)
        );
        assert_eq!(bytes.as_ref(), [0, 0xff]);
        let mut last = Reader {
            bytes: &[0xff],
            cursor: 0,
        };
        assert_eq!(read_listed(&mut last, &table), Ok(255));
        assert_eq!(last.cursor, 1);
        let mut invalid = Reader {
            bytes: &[2],
            cursor: 0,
        };
        assert_eq!(
            read_listed(&mut invalid, &[3_u16, 8]),
            Err(CodecError::Corrupt)
        );
        assert_eq!(invalid.cursor, 1);
    }

    #[test]
    fn narrow_fields_refuse_out_of_range_words_after_consuming_them()
    {
        let mut reader = Reader {
            bytes: &[0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
            cursor: 0,
        };
        assert_eq!(read_narrow::<u32>(&mut reader), Ok(u32::MAX));
        assert_eq!(reader.cursor, 8);
        assert_eq!(read_narrow::<u32>(&mut reader), Err(CodecError::Corrupt));
        assert_eq!(reader.cursor, 16);
        assert_eq!(reader.finish(), Ok(()));
    }

    #[test]
    fn empty_envelopes_preserve_budget_and_separate_formats()
    {
        let checkpoints = Checkpoints::new(CheckBudget::from(0x0102_0304_usize), vec![]);
        let expected = [
            b'G', b'C', b'K', b'P', b'T', 0, 0, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        assert_eq!(
            encode_checkpoints(&checkpoints)
                .expect("empty checkpoint")
                .as_ref(),
            expected
        );
        assert_eq!(decode_checkpoints(Bytes(&expected)), Ok(checkpoints));
        let mut wrong_version = expected;
        *wrong_version.get_mut(7).expect("version byte") = 3;
        assert_eq!(
            decode_checkpoints(Bytes(&wrong_version)),
            Err(CodecError::Corrupt)
        );
        let mut program = CheckpointBytes::default();
        write_program(&mut program, &[]).expect("empty program");
        assert_eq!(program.as_ref(), b"GPROG\0\0\x02\0\0\0\0\0\0\0\0");
        assert_eq!(
            decode_checkpoints(Bytes(program.as_ref())),
            Err(CodecError::Corrupt)
        );
    }

    #[test]
    fn checkpoint_encoding_reports_the_first_unresolved_plane()
    {
        let unresolved = |sort| TypeContent::from_nodes(vec![ContentNode::Unresolved(sort)]);
        let mismatch = |synthesised, expected| {
            Typing::Refused(Refusal::TypeMismatch {
                at: Site::Unreached,
                synthesised,
                expected,
            })
        };
        let encode = |nodes: Vec<ContentNode>, answer, typing| {
            let content = ItemContent::from_parts(
                Reference::Unoccupied,
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(NodeIndex::from(0_usize)),
                nodes,
            );
            let footprint = Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            );
            let item = ItemCheckpoint::new(
                content,
                footprint,
                vec![Answered::new(Reference::Unoccupied, answer)],
                typing,
            );
            let checkpoints = Checkpoints::new(CheckBudget::DEFAULT, vec![item]);
            let validated = encode_checkpoints(&checkpoints).map(|_bytes| ());
            let raw = super::checkpoint_frame(&checkpoints).map(|_bytes| ());
            assert_eq!(validated, raw);
            validated
        };
        let unsupported = |sort| {
            Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(
                sort,
            )))
        };
        assert_eq!(
            encode(
                vec![ContentNode::Unresolved(Sort::Value)],
                Answer::Typed(unresolved(Sort::ValueType)),
                Typing::Synthesised {
                    produced: unresolved(Sort::CompType),
                    conversions: ConversionCount::from(0_usize)
                },
            ),
            unsupported(Sort::Value),
        );
        assert_eq!(
            encode(
                vec![ContentNode::Unit],
                Answer::Typed(unresolved(Sort::ValueType)),
                Typing::Synthesised {
                    produced: unresolved(Sort::CompType),
                    conversions: ConversionCount::from(0_usize)
                },
            ),
            unsupported(Sort::ValueType),
        );
        assert_eq!(
            encode(
                vec![ContentNode::Unit],
                Answer::Untyped,
                Typing::Synthesised {
                    produced: unresolved(Sort::CompType),
                    conversions: ConversionCount::from(0_usize)
                },
            ),
            unsupported(Sort::CompType),
        );
        assert_eq!(
            encode(
                vec![ContentNode::Unit],
                Answer::Untyped,
                mismatch(unresolved(Sort::CompType), unresolved(Sort::Computation)),
            ),
            unsupported(Sort::CompType),
        );
        assert_eq!(
            encode(
                vec![ContentNode::Unit],
                Answer::Untyped,
                mismatch(
                    TypeContent::from_nodes(vec![ContentNode::UnitType]),
                    unresolved(Sort::Computation)
                ),
            ),
            unsupported(Sort::Computation),
        );
    }

    #[test]
    fn decoders_reject_unknown_tags_before_payloads()
    {
        type TagDecoder = for<'bytes> fn(&mut Reader<'bytes>) -> Result<(), CodecError>;
        let mut malformed = [0_u8; 65];
        *malformed.first_mut().expect("tag") = u8::MAX;
        let decoders: [TagDecoder; 7] = [
            |reader| super::read_sign(reader).map(|_value| ()),
            |reader| super::read_literal(reader).map(|_value| ()),
            |reader| super::read_node(reader).map(|_value| ()),
            |reader| super::read_site(reader).map(|_value| ()),
            |reader| super::read_refusal(reader).map(|_value| ()),
            |reader| super::read_typing(reader).map(|_value| ()),
            |reader| super::read_answer(reader).map(|_value| ()),
        ];
        for decode in decoders {
            let mut reader = Reader {
                bytes: &malformed,
                cursor: 0,
            };
            assert_eq!(decode(&mut reader), Err(CodecError::Corrupt));
            assert_eq!(reader.cursor, 1, "unknown tags stop before any payload");
        }

        for (tag, invalid_field) in [(0x01, 2), (0x06, 2), (0x20, 3)] {
            let mut bytes = [0_u8; 10];
            *bytes.first_mut().expect("node tag") = tag;
            *bytes.get_mut(1).expect("field tag") = invalid_field;
            let mut reader = Reader {
                bytes: &bytes,
                cursor: 0,
            };
            assert_eq!(super::read_node(&mut reader), Err(CodecError::Corrupt));
            assert_eq!(
                reader.cursor, 2,
                "zone, side and base tags reject at their field"
            );
        }

        for (prefix, consumed) in [(&[2, 7][..], 2), (&[5, 1, 2][..], 3)] {
            let mut bytes = prefix.to_vec();
            bytes.extend_from_slice(&[0; 16]);
            let mut reader = Reader {
                bytes: &bytes,
                cursor: 0,
            };
            assert_eq!(super::read_refusal(&mut reader), Err(CodecError::Corrupt));
            assert_eq!(
                reader.cursor, consumed,
                "form and zone tags stop at their field"
            );
        }

        for (opacity, hole, consumed) in [(2, 0, 17), (0, 2, 18)] {
            let mut bytes = [0_u8; 18];
            *bytes.get_mut(16).expect("opacity flag") = opacity;
            *bytes.get_mut(17).expect("hole flag") = hole;
            let mut reader = Reader {
                bytes: &bytes,
                cursor: 0,
            };
            assert_eq!(super::read_footprint(&mut reader), Err(CodecError::Corrupt));
            assert_eq!(
                reader.cursor, consumed,
                "each footprint flag has its own boundary"
            );
        }

        let mut bytes = CheckpointBytes::from(Vec::new());
        assert_eq!(
            super::write_site(&mut Writer { sink: &mut bytes }, Site::Unreached),
            Ok(())
        );
        assert_eq!(bytes.as_ref(), &[1]);
        let mut reader = Reader {
            bytes: &[1, 0xff],
            cursor: 0,
        };
        assert_eq!(super::read_site(&mut reader), Ok(Site::Unreached));
        assert_eq!(reader.cursor, 1);
    }

    #[test]
    fn encoding_bounds_levels_in_every_node_family_and_plane()
    {
        let mut level = super::Level::var(super::LevelVar::new(super::LevelVarIndex::from(0_u32)));
        for _ in 0 .. super::MAX_DECODED_LEVEL_OFFSET {
            level = level.succ().expect("representable offset");
        }
        let unit = || vec![ContentNode::Unit];
        let valid_type = || TypeContent::from_nodes(vec![ContentNode::UnitType]);
        let at = Site::Unreached;
        let cases = [
            (
                vec![
                    ContentNode::ValueLift {
                        target: level.clone(),
                        body: NodeIndex::from(1_usize),
                    },
                    ContentNode::Unit,
                ],
                Answer::Untyped,
                Typing::Owed,
            ),
            (
                unit(),
                Answer::Typed(TypeContent::from_nodes(vec![
                    ContentNode::TypeLift {
                        inner: NodeIndex::from(1_usize),
                        target: level.clone(),
                    },
                    ContentNode::UnitType,
                ])),
                Typing::Owed,
            ),
            (unit(), Answer::Untyped, Typing::Synthesised {
                produced: TypeContent::from_nodes(vec![
                    ContentNode::Element {
                        code: NodeIndex::from(1_usize),
                        target: level.clone(),
                    },
                    ContentNode::Unit,
                ]),
                conversions: ConversionCount::from(0_usize),
            }),
            (
                unit(),
                Answer::Untyped,
                Typing::Refused(Refusal::TypeMismatch {
                    at,
                    synthesised: TypeContent::from_nodes(vec![ContentNode::Universe {
                        sort: super::TypeSort::Ground(super::GroundSort::Value),
                        level: level.clone(),
                    }]),
                    expected: valid_type(),
                }),
            ),
            (
                unit(),
                Answer::Untyped,
                Typing::Refused(Refusal::TypeMismatch {
                    at,
                    synthesised: valid_type(),
                    expected: TypeContent::from_nodes(vec![
                        ContentNode::ComputationElement {
                            code: NodeIndex::from(1_usize),
                            target: level,
                        },
                        ContentNode::Unit,
                    ]),
                }),
            ),
        ];
        for (nodes, answer, typing) in cases {
            let content = ItemContent::from_parts(
                Reference::Unoccupied,
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(NodeIndex::from(0_usize)),
                nodes,
            );
            let item = ItemCheckpoint::new(
                content,
                Footprint::from_parts(
                    BTreeSet::new(),
                    BTreeSet::new(),
                    Opacity::Transparent,
                    HoleMark::Filled,
                ),
                vec![Answered::new(Reference::Unoccupied, answer)],
                typing,
            );
            let checkpoints = Checkpoints::new(CheckBudget::DEFAULT, vec![item]);
            assert_eq!(
                encode_checkpoints(&checkpoints),
                Err(CodecError::LevelOffsetTooLarge {
                    offset: super::LevelOffset::from(super::MAX_DECODED_LEVEL_OFFSET)
                })
            );
        }
    }

    #[test]
    fn encoding_bounds_levels_in_every_auxiliary_type_table()
    {
        type Mismatch = fn(TypeContent, TypeContent) -> Refusal;
        let mut level = super::Level::var(super::LevelVar::new(super::LevelVarIndex::from(0_u32)));
        for _ in 0 .. super::MAX_DECODED_LEVEL_OFFSET {
            level = level.succ().expect("representable offset");
        }
        let capped = || {
            TypeContent::from_nodes(vec![ContentNode::Universe {
                sort: super::TypeSort::Ground(super::GroundSort::Value),
                level: level.clone(),
            }])
        };
        let valid = || TypeContent::from_nodes(vec![ContentNode::UnitType]);
        let at = Site::Unreached;
        let mismatches: [Mismatch; 4] = [
            |synthesised, expected| Refusal::TypeMismatch {
                at: Site::Unreached,
                synthesised,
                expected,
            },
            |synthesised, expected| Refusal::SortMismatch {
                at: Site::Unreached,
                synthesised,
                expected,
            },
            |synthesised, expected| Refusal::LevelMismatch {
                at: Site::Unreached,
                synthesised,
                expected,
            },
            |synthesised, expected| Refusal::FamilyArgumentClassifier {
                at: Site::Unreached,
                position: super::ArgumentPosition::from(0_u32),
                synthesised,
                expected,
            },
        ];
        let mut cases = vec![
            (Answer::Typed(capped()), Typing::Owed),
            (Answer::Untyped, Typing::Synthesised {
                produced: capped(),
                conversions: ConversionCount::from(0_usize),
            }),
            (
                Answer::Untyped,
                Typing::Refused(Refusal::ShapeMismatch {
                    at,
                    wanted: super::ExpectedShape::Product,
                    found: capped(),
                }),
            ),
            (
                Answer::Untyped,
                Typing::Refused(Refusal::DependentBind {
                    at,
                    synthesised: capped(),
                }),
            ),
            (
                Answer::Untyped,
                Typing::Refused(Refusal::StaticClassifierExpected {
                    at,
                    found: capped(),
                }),
            ),
        ];
        for mismatch in mismatches {
            cases.push((
                Answer::Untyped,
                Typing::Refused(mismatch(capped(), valid())),
            ));
            cases.push((
                Answer::Untyped,
                Typing::Refused(mismatch(valid(), capped())),
            ));
        }
        for (answer, typing) in cases {
            let content = ItemContent::from_parts(
                Reference::Unoccupied,
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(NodeIndex::from(0_usize)),
                vec![ContentNode::Unit],
            );
            let item = ItemCheckpoint::new(
                content,
                Footprint::from_parts(
                    BTreeSet::new(),
                    BTreeSet::new(),
                    Opacity::Transparent,
                    HoleMark::Filled,
                ),
                vec![Answered::new(Reference::Unoccupied, answer)],
                typing,
            );
            let checkpoints = Checkpoints::new(CheckBudget::DEFAULT, vec![item]);
            assert_eq!(
                encode_checkpoints(&checkpoints),
                Err(CodecError::LevelOffsetTooLarge {
                    offset: super::LevelOffset::from(super::MAX_DECODED_LEVEL_OFFSET)
                })
            );
        }
    }
}
