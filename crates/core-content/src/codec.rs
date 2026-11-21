//! The byte form of a content node: the tags, words and counts that write a
//! table of supported nodes, and the reader that refuses each byte string
//! that no table writes.
//!
//! The checkpoint store and the image of a command write a content table in
//! this one form. The writer goes over a [`Sink`], so the same walk feeds a
//! buffer and a hasher. The reader takes a byte slice and gives the table or
//! a [`CodecError`].
//!
//! # Witnesses
//! - `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
//!
//! # Boundaries
//! - The byte form of a checkpoint record stays in the incremental crate.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Sort as TypeSort;
use gandr_core_term::SortParameter;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place as AccessPlace;
use gandr_core_term::session::DialogueMove;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::RecursionIndex;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::session::SessionType;
use gandr_core_term::session::WebPiece;
use gandr_core_term::support::Scope;
use gandr_core_term::support::Thinning;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelOffset;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CharacterLiteral;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::Float64Literal;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::IntegerWidth;
use gandr_kernel_term::JointPositions;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;

use crate::ContentNode;
use crate::ItemKey;
use crate::NodeIndex;
use crate::Occurrence;
use crate::Reference;
use crate::Sort;
use crate::SupportedNode;
use crate::TablePlace;
use crate::TypeContent;

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
/// - witness: `gandr-core-incremental::persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnsupportedPersistence
{
    /// An id of this sort that the item's arena resolves to nothing: a fact
    /// about another arena, meaningless outside this process.
    Dangling(Sort),
    /// A codata declaration: its signature has no content form.
    Codata,
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
/// - witness: `gandr-core-incremental::codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
/// - witness: `gandr-core-incremental::persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `gandr-core-incremental::persistence::tests::oversized_level_offset_is_refused_with_exact_error`
/// - witness: `gandr-core-incremental::persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
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
            Self::Dangling(sort) => {
                let sort = match sort {
                    Sort::Value => "value",
                    Sort::Computation => "computation",
                    Sort::ValueType => "value type",
                    Sort::CompType => "computation type",
                };
                write!(f, "an unresolved {sort} id is process-local")
            },
            Self::Codata => f.write_str("a codata signature has no content form"),
        }
    }
}

/// One byte naming a variant.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Tag(pub u8);

/// A little-endian 64-bit word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Word(pub u64);

/// A length or a count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Count(pub usize);

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
/// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    );

    /// Whether a codata application may be written to the sink. A codata
    /// application has content for its key alone, so only a sink that keys
    /// content and stores nothing writes one. A stored form that holds one
    /// needs a version of its own.
    const CODATA: CodataWrite = CodataWrite::Refused;
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
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
/// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
#[repr(transparent)]
pub struct Writer<'sink, Out>
{
    /// The sink written to.
    pub sink: &'sink mut Out,
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
    #[inline]
    pub fn tag(
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
    #[inline]
    pub fn word(
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
    ///
    /// # Errors
    /// A [`CodecError`] for a value that has no byte form, or a sink that
    /// refuses.
    #[spec(
        ensures: |ret| {
            ret == u64::try_from(count.0)
                .map(|_| ())
                .map_err(|_overflow| CodecError::Unrepresentable)
        },
    )]
    #[inline]
    pub fn count(
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_frames_have_known_bytes_and_digest`
    ///
    /// # Errors
    /// A [`CodecError`] for a value that has no byte form, or a sink that
    /// refuses.
    #[spec(
        ensures: |ret| {
            ret == u64::try_from(bytes.0.len())
                .map(|_| ())
                .map_err(|_overflow| CodecError::Unrepresentable)
        },
    )]
    #[inline]
    pub fn bytes(
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
/// - witness: `gandr-core-incremental::codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
/// - witness: `gandr-core-incremental::codec::tests::framed_failures_retain_consumed_prefixes`
pub struct Reader<'data>
{
    /// The input.
    pub bytes: &'data [u8],
    /// The next unread byte.
    pub cursor: usize,
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
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
    /// # Errors
    /// A [`CodecError`] for bytes that the writer does not give.
    #[inline]
    pub fn take(
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
    ///
    /// # Errors
    /// A [`CodecError`] for bytes that the writer does not give.
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| match self.bytes.get(before) {
            | Some(&tag) => before.checked_add(1) == Some(self.cursor) && ret == Ok(Tag(tag)),
            | None => self.cursor == before && ret == Err(CodecError::Corrupt),
        },
    )]
    #[inline]
    pub fn tag(&mut self) -> Result<Tag, CodecError>
    {
        let taken = self.take(Count(1))?;
        match *taken.0 {
            [tag] => Ok(Tag(tag)),
            _ => Err(CodecError::Corrupt),
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
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
    /// # Errors
    /// A [`CodecError`] for bytes that the writer does not give.
    #[inline]
    pub fn word(&mut self) -> Result<Word, CodecError>
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
    /// - witness: `gandr-core-incremental::codec::tests::framed_failures_retain_consumed_prefixes`
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
    /// # Errors
    /// A [`CodecError`] for bytes that the writer does not give.
    #[inline]
    pub fn count(&mut self) -> Result<Count, CodecError>
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
    /// - witness: `gandr-core-incremental::codec::tests::framed_failures_retain_consumed_prefixes`
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
    /// # Errors
    /// A [`CodecError`] for bytes that the writer does not give.
    #[inline]
    pub fn bytes(&mut self) -> Result<Bytes<'data>, CodecError>
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
    /// - witness: `gandr-core-incremental::codec::tests::framed_failures_retain_consumed_prefixes`
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
    /// # Errors
    /// A [`CodecError`] for bytes that the writer does not give.
    ///
    /// # Cost
    /// - allocation: the decoded text, growth within the bytes
    #[inline]
    pub fn text(&mut self) -> Result<String, CodecError>
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
    /// - witness: `gandr-core-incremental::codec::tests::primitive_reads_preserve_cursor_on_extent_failure`
    /// - witness: `gandr-core-incremental::codec::tests::framed_failures_retain_consumed_prefixes`
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
    /// # Errors
    /// A [`CodecError`] for bytes that the writer does not give.
    #[inline]
    pub fn finish(&self) -> Result<(), CodecError>
    {
        if self.cursor == self.bytes.len() {
            Ok(())
        }
        else {
            Err(CodecError::Corrupt)
        }
    }
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
/// - witness: `gandr-core-incremental::codec::tests::reference_frames_preserve_binary_keys_and_occurrences`
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
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_reference<Out>(
    writer: &mut Writer<'_, Out>,
    reference: &Reference,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *reference {
        Reference::Unoccupied => writer.tag(Tag(0)),
        Reference::Item {
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
/// - witness: `gandr-core-incremental::codec::tests::reference_frames_preserve_binary_keys_and_occurrences`
///
/// # Cost
/// - allocation: the key of the reference, growth within the bytes
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
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
#[inline]
pub fn read_reference(reader: &mut Reader<'_>) -> Result<Reference, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        0 => Ok(Reference::Unoccupied),
        1 => {
            let key = reader.bytes()?;
            let occurrence = reader.count()?;
            Ok(Reference::Item {
                key: ItemKey::from(key.0),
                occurrence: Occurrence::from(occurrence.0),
            })
        },
        _ => Err(CodecError::Corrupt),
    }
}

/// Write a world: tag zero for the host's, tag one then the reference of a
/// declared one.
///
/// # Specification
/// - fails: as [`write_reference`].
/// - panics: none.
/// - executable: none — the bytes are the writer's own output; the witness
///   reads them back.
///
/// # Adequacy
/// - hypothesis: L3 — a migration to a declared world and a handle at one round
///   trip, and the host's world reads back as itself.
/// - witness: `gandr-core-incremental::codec::tests::world_formers_round_trip_under_their_own_tags_3381`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_world<Out>(
    writer: &mut Writer<'_, Out>,
    world: &crate::WorldContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *world {
        crate::WorldContent::Host => writer.tag(Tag(0)),
        crate::WorldContent::Declared(ref reference) => {
            writer.tag(Tag(1));
            write_reference(writer, reference)?;
        },
    }
    Ok(())
}

/// Read a world.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for a tag past one or a malformed
///   reference.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_world`].
/// - witness: `gandr-core-incremental::codec::tests::world_formers_round_trip_under_their_own_tags_3381`
///
/// # Cost
/// - allocation: the reference of a declared world, growth within the bytes
#[spec(captures: [before = reader.cursor], ensures: |ret| ret.is_err() || reader.cursor > before)]
#[inline]
pub fn read_world(reader: &mut Reader<'_>) -> Result<crate::WorldContent, CodecError>
{
    match reader.tag()?.0 {
        0 => Ok(crate::WorldContent::Host),
        1 => read_reference(reader).map(crate::WorldContent::Declared),
        _ => Err(CodecError::Corrupt),
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
/// - witness: `gandr-core-incremental::persistence::tests::universe_sorts_and_levels_round_trip`
/// - witness: `gandr-core-incremental::persistence::tests::oversized_level_offset_is_refused_with_exact_error`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[spec(
    ensures: |ret| {
        ret == u64::try_from(level.atoms().count())
            .map(|_| ())
            .map_err(|_overflow| CodecError::Unrepresentable)
    },
)]
#[inline]
pub fn write_level<Out>(
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
/// - witness: `gandr-core-incremental::persistence::tests::oversized_level_offset_is_refused_with_exact_error`
/// - witness: `gandr-core-incremental::persistence::tests::universe_sorts_and_levels_round_trip`
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
///
/// # Cost
/// - allocation: the atoms of the level, growth within the bytes
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
#[inline]
pub fn read_level(reader: &mut Reader<'_>) -> Result<Level, CodecError>
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
/// - witness: `gandr-core-incremental::persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `gandr-core-incremental::codec::tests::decoders_reject_unknown_tags_before_payloads`
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
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[inline]
pub fn read_sign(reader: &mut Reader<'_>) -> Result<Sign, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        0 => Ok(Sign::Negative),
        1 => Ok(Sign::NonNegative),
        _ => Err(CodecError::Corrupt),
    }
}

/// Write a literal.
///
/// # Specification
/// - ensures: encoding succeeds exactly when every decimal or text byte length
///   fits a word; a floating-point literal writes its bit pattern as eight
///   bytes, little-endian.
///
/// # Adequacy
/// - hypothesis: L3 — integer, text, numeric and character values in the finite
///   semantic corpus cross persistence. The predicate states field
///   representability; the corpus, rather than a generic sink observer,
///   witnesses payload preservation.
/// - witness: `gandr-core-incremental::persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
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
            | Literal::Character(_) | Literal::Float64(_) | Literal::Fixed(_) => true,
        } {
            Ok(())
        }
        else {
            Err(CodecError::Unrepresentable)
        }
    },
)]
/// # Cost
/// - allocation: the text of a character literal, growth within the literal
fn write_literal<Out>(
    writer: &mut Writer<'_, Out>,
    literal: &Literal,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *literal {
        Literal::Integer(ref integer) => {
            writer.tag(Tag(0));
            writer.tag(sign_tag(integer.sign()));
            writer.bytes(Bytes(integer.magnitude().as_ref().as_bytes()))?;
        },
        Literal::Text(ref string) => {
            writer.tag(Tag(1));
            writer.bytes(Bytes(string.as_ref().as_bytes()))?;
        },
        Literal::Numeric(ref numeric) => {
            writer.tag(Tag(2));
            writer.tag(sign_tag(numeric.sign()));
            writer.bytes(Bytes(numeric.integer_part().as_ref().as_bytes()))?;
            writer.bytes(Bytes(numeric.fraction().as_ref().as_bytes()))?;
        },
        Literal::Character(character) => {
            writer.tag(Tag(3));
            writer.bytes(Bytes(character.to_text().as_bytes()))?;
        },
        Literal::Float64(float) => {
            writer.tag(Tag(8));
            writer.bytes(Bytes(u64::from(float).to_le_bytes().as_slice()))?;
        },
        Literal::Fixed(fixed) => {
            writer.tag(Tag(match fixed.width() {
                IntegerWidth::U32 => 4,
                IntegerWidth::U64 => 5,
                IntegerWidth::I32 => 6,
                IntegerWidth::I64 => 7,
                IntegerWidth::U8 => 9,
                IntegerWidth::U16 => 10,
                IntegerWidth::I8 => 11,
                IntegerWidth::I16 => 12,
                IntegerWidth::Usize => 13,
                IntegerWidth::Isize => 14,
            }));
            writer.word(Word(u64::from(fixed)));
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
/// - hypothesis: L3 — the finite semantic corpus preserves the literal classes
///   through persistence. The predicate checks tag classification, not a second
///   construction of normalized decimal text. Unknown tags reject before
///   consuming available payload bytes.
/// - witness: `gandr-core-incremental::persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `gandr-core-incremental::codec::tests::decoders_reject_unknown_tags_before_payloads`
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
///
/// # Cost
/// - allocation: the digits or the text of the literal, growth within the bytes
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref literal) => {
            reader.bytes.get(before)
                == Some(&match *literal {
                    | Literal::Integer(_) => 0,
                    | Literal::Text(_) => 1,
                    | Literal::Numeric(_) => 2,
                    | Literal::Character(_) => 3,
                    | Literal::Float64(_) => 8,
                    | Literal::Fixed(fixed) => match fixed.width() {
                        | IntegerWidth::U32 => 4,
                        | IntegerWidth::U64 => 5,
                        | IntegerWidth::I32 => 6,
                        | IntegerWidth::I64 => 7,
                        | IntegerWidth::U8 => 9,
                        | IntegerWidth::U16 => 10,
                        | IntegerWidth::I8 => 11,
                        | IntegerWidth::I16 => 12,
                        | IntegerWidth::Usize => 13,
                        | IntegerWidth::Isize => 14,
                    },
                })
                && reader.cursor > before
        },
        | Err(error) => error == CodecError::Corrupt && reader.cursor >= before,
    },
)]
#[inline]
pub fn read_literal(reader: &mut Reader<'_>) -> Result<Literal, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        0 => {
            let sign = read_sign(reader)?;
            let digits = reader.text()?;
            let magnitude = Magnitude::from_decimal_text(digits).ok_or(CodecError::Corrupt)?;
            Ok(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
        },
        1 => {
            let text = reader.text()?;
            Ok(Literal::Text(StringLiteral::new(text)))
        },
        2 => {
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
        3 => {
            let text = reader.text()?;
            let character =
                CharacterLiteral::try_from(text).map_err(|_not_one| CodecError::Corrupt)?;
            Ok(Literal::Character(character))
        },
        8 => {
            let bytes = reader.bytes()?;
            let bits: [u8; 8] = bytes.0.try_into().map_err(|_width| CodecError::Corrupt)?;
            Ok(Literal::Float64(Float64Literal::from(f64::from_bits(
                u64::from_le_bytes(bits),
            ))))
        },
        4 => read_fixed(reader, IntegerWidth::U32),
        5 => read_fixed(reader, IntegerWidth::U64),
        6 => read_fixed(reader, IntegerWidth::I32),
        7 => read_fixed(reader, IntegerWidth::I64),
        9 => read_fixed(reader, IntegerWidth::U8),
        10 => read_fixed(reader, IntegerWidth::U16),
        11 => read_fixed(reader, IntegerWidth::I8),
        12 => read_fixed(reader, IntegerWidth::I16),
        13 => read_fixed(reader, IntegerWidth::Usize),
        14 => read_fixed(reader, IntegerWidth::Isize),
        _ => Err(CodecError::Corrupt),
    }
}

/// Read a width literal's payload: its bit pattern as one word.
///
/// # Specification
/// - ensures: on `Ok`, the literal of `width` with the read pattern.
/// - fails: [`CodecError::Corrupt`] for a short word or a 32-bit width's
///   pattern that sets a bit above its 32nd.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the finite semantic corpus carries a width literal
///   through persistence.
/// - witness: `gandr-core-incremental::persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
///
/// # Cost
/// - allocation: the decoded literal, growth within the bytes
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|literal| literal.base_type() == BaseType::Fixed(width)))]
fn read_fixed(
    reader: &mut Reader<'_>,
    width: IntegerWidth,
) -> Result<Literal, CodecError>
{
    let bits = reader.word()?;
    FixedInteger::try_from((width, bits.0))
        .map(Literal::Fixed)
        .map_err(|_wider| CodecError::Corrupt)
}

/// Write a node index.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_index<Out>(
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
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[inline]
pub fn read_index(reader: &mut Reader<'_>) -> Result<NodeIndex, CodecError>
{
    let count = reader.count()?;
    Ok(NodeIndex::from(count.0))
}

/// Write one recorded move: its action's tag, then its payload or label.
///
/// # Specification
/// trivial.
fn write_move<Out>(
    writer: &mut Writer<'_, Out>,
    step: &RecordedMove<NodeIndex>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *step {
        RecordedMove::Sent(payload) => {
            writer.tag(Tag(0));
            write_index(writer, payload)?;
        },
        RecordedMove::Received(payload) => {
            writer.tag(Tag(1));
            write_index(writer, payload)?;
        },
        RecordedMove::Selected(ref label) => {
            writer.tag(Tag(2));
            writer.bytes(Bytes(label.as_ref().as_bytes()))?;
        },
        RecordedMove::Offered(ref label) => {
            writer.tag(Tag(3));
            writer.bytes(Bytes(label.as_ref().as_bytes()))?;
        },
        RecordedMove::Closed => writer.tag(Tag(4)),
    }
    Ok(())
}

/// Read one recorded move [`write_move`] wrote.
///
/// # Specification
/// trivial.
fn read_move(reader: &mut Reader<'_>) -> Result<RecordedMove<NodeIndex>, CodecError>
{
    Ok(match reader.tag()?.0 {
        0 => RecordedMove::Sent(read_index(reader)?),
        1 => RecordedMove::Received(read_index(reader)?),
        2 => RecordedMove::Selected(read_field_label(reader)?),
        3 => RecordedMove::Offered(read_field_label(reader)?),
        4 => RecordedMove::Closed,
        _ => return Err(CodecError::Corrupt),
    })
}

/// Write a dialogue move's endpoint: `0` for the left, `1` for the right.
///
/// # Specification
/// trivial.
fn write_side<Out>(
    writer: &mut Writer<'_, Out>,
    endpoint: Endpoint,
) where
    Out: Sink,
{
    writer.tag(Tag(match endpoint {
        Endpoint::Left => 0,
        Endpoint::Right => 1,
    }));
}

/// Read an endpoint [`write_side`] wrote.
///
/// # Specification
/// trivial.
fn read_side(reader: &mut Reader<'_>) -> Result<Endpoint, CodecError>
{
    match reader.tag()?.0 {
        0 => Ok(Endpoint::Left),
        1 => Ok(Endpoint::Right),
        _ => Err(CodecError::Corrupt),
    }
}

/// Write one piece of a web: its kind's tag, then an event's endpoint and
/// position or a node's factor count.
///
/// # Specification
/// trivial.
fn write_piece<Out>(
    writer: &mut Writer<'_, Out>,
    piece: WebPiece,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match piece {
        WebPiece::Event { endpoint, index } => {
            writer.tag(Tag(0));
            write_side(writer, endpoint);
            writer.count(Count(index))
        },
        WebPiece::Series(factors) => {
            writer.tag(Tag(1));
            writer.count(Count(factors))
        },
        WebPiece::Parallel(factors) => {
            writer.tag(Tag(2));
            writer.count(Count(factors))
        },
        WebPiece::Prime(factors) => {
            writer.tag(Tag(3));
            writer.count(Count(factors))
        },
    }
}

/// Read one web piece [`write_piece`] wrote.
///
/// # Specification
/// trivial.
fn read_piece(reader: &mut Reader<'_>) -> Result<WebPiece, CodecError>
{
    Ok(match reader.tag()?.0 {
        0 => {
            let endpoint = read_side(reader)?;
            WebPiece::Event {
                endpoint,
                index: reader.count()?.0,
            }
        },
        1 => WebPiece::Series(reader.count()?.0),
        2 => WebPiece::Parallel(reader.count()?.0),
        3 => WebPiece::Prime(reader.count()?.0),
        _ => return Err(CodecError::Corrupt),
    })
}

/// Write the region a capability or a kept type lives in: the held region, a
/// scope's at its depth, or a definition's region binder at its ordinal.
///
/// # Specification
/// trivial.
#[inline]
pub fn write_region<Out>(
    writer: &mut Writer<'_, Out>,
    region: gandr_core_term::effect::capability::Region,
) where
    Out: Sink,
{
    use gandr_core_term::effect::capability::Region;
    match region {
        Region::Held => writer.tag(Tag(0)),
        Region::Scoped(depth) => {
            writer.tag(Tag(1));
            writer.word(Word(u64::from(u32::from(depth))));
        },
        Region::Bound(binder) => {
            writer.tag(Tag(2));
            writer.word(Word(u64::from(u32::from(binder))));
        },
    }
}

/// Read a region [`write_region`] wrote.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`CodecError::Corrupt`] for a tag naming no region, or a depth or an
/// ordinal past 32 bits.
fn read_region(
    reader: &mut Reader<'_>
) -> Result<gandr_core_term::effect::capability::Region, CodecError>
{
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionBinder;
    use gandr_core_term::effect::capability::RegionDepth;
    let tag = reader.tag()?.0;
    if tag == 0 {
        return Ok(Region::Held);
    }
    let ordinal = u32::try_from(reader.word()?.0).map_err(|_overflow| CodecError::Corrupt)?;
    match tag {
        1 => Ok(Region::Scoped(RegionDepth::from(ordinal))),
        2 => Ok(Region::Bound(RegionBinder::from(ordinal))),
        _ => Err(CodecError::Corrupt),
    }
}

/// Write one content node.
///
/// # Specification
/// - fails: [`CodecError::Unsupported`] for an unresolved node, and for a
///   codata application unless the sink keys content and stores nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite semantic corpus encodes supported nodes and
///   all four unresolved sorts are rejected with their exact sort. The
///   predicate classifies failures; a generic sink does not expose the emitted
///   fields.
/// - witness: `gandr-core-incremental::persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `gandr-core-incremental::persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[spec(
    ensures: |ret| match *node {
        | ContentNode::Unresolved(sort) => {
            ret == Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(
                sort,
            )))
        },
        | ContentNode::Codata { .. } if Out::CODATA == CodataWrite::Refused => {
            ret == Err(CodecError::Unsupported(UnsupportedPersistence::Codata))
        },
        | _ => matches!(ret, Ok(()) | Err(CodecError::Unrepresentable)),
    },
)]
#[inline]
pub fn write_node<Out>(
    writer: &mut Writer<'_, Out>,
    node: &ContentNode,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *node {
        ContentNode::Data {
            ref declaration,
            ref arguments,
        } => {
            writer.tag(Tag(0x50));
            write_reference(writer, declaration)?;
            write_indices(writer, arguments)?;
        },
        ContentNode::Codata {
            ref declaration,
            ref arguments,
        } => {
            if Out::CODATA == CodataWrite::Refused {
                return Err(CodecError::Unsupported(UnsupportedPersistence::Codata));
            }
            writer.tag(Tag(0x99));
            write_reference(writer, declaration)?;
            write_indices(writer, arguments)?;
        },
        ContentNode::Hold(value) => {
            writer.tag(Tag(0x94));
            write_index(writer, value)?;
        },
        ContentNode::Leta {
            ref world,
            value,
            body,
        } => {
            writer.tag(Tag(0x95));
            write_world(writer, world)?;
            write_index(writer, value)?;
            write_index(writer, body)?;
        },
        ContentNode::Migrate { ref world, body } => {
            writer.tag(Tag(0x96));
            write_world(writer, world)?;
            write_index(writer, body)?;
        },
        ContentNode::HeldType { inner, ref world } => {
            writer.tag(Tag(0x97));
            write_index(writer, inner)?;
            write_world(writer, world)?;
        },
        ContentNode::CapabilityType(ref world) => {
            writer.tag(Tag(0x98));
            write_world(writer, world)?;
        },
        ContentNode::RecordType(ref fields) => {
            writer.tag(Tag(0x51));
            write_fields(writer, fields)?;
        },
        // A patch with no meets keeps the tag it had before systems of faces,
        // so its bytes and its content key do not change (#5106).
        ContentNode::Patched {
            base,
            ref fixed,
            ref meets,
        } => {
            writer.tag(Tag(if meets.is_empty() { 0x8F } else { 0x90 }));
            write_index(writer, base)?;
            write_fields(writer, fixed)?;
            if !meets.is_empty() {
                write_meets(writer, meets)?;
            }
        },
        ContentNode::Constructor {
            ref family,
            datatype,
            tag,
            ref fields,
        } => {
            writer.tag(Tag(0x52));
            write_reference(writer, family)?;
            write_index(writer, datatype)?;
            writer.count(Count(usize::from(tag)))?;
            write_indices(writer, fields)?;
        },
        ContentNode::Record(ref fields) => {
            writer.tag(Tag(0x53));
            write_fields(writer, fields)?;
        },
        ContentNode::DataCase {
            scrutinee,
            motive,
            ref branches,
            ref arities,
            equations,
        } => {
            // A case with no equation keeps its bytes; one over an indexed
            // family states how many its branches take.
            let owed = usize::from(equations);
            writer.tag(Tag(if owed == 0 { 0x54 } else { 0x5E }));
            write_index(writer, scrutinee)?;
            write_index(writer, motive)?;
            write_indices(writer, branches)?;
            writer.count(Count(arities.len()))?;
            for &arity in arities {
                writer.count(Count(usize::from(arity)))?;
            }
            if owed != 0 {
                writer.count(Count(owed))?;
            }
        },
        ContentNode::RecordProjection(record, ref label) => {
            writer.tag(Tag(0x55));
            write_index(writer, record)?;
            writer.bytes(Bytes(label.as_ref().as_bytes()))?;
        },
        ContentNode::TupleProjection(tuple, component) => {
            writer.tag(Tag(0x5A));
            write_index(writer, tuple)?;
            writer.count(Count(usize::from(component)))?;
        },
        ContentNode::Split(scrutinee, arity, body) => {
            writer.tag(Tag(0x5B));
            write_index(writer, scrutinee)?;
            writer.count(Count(usize::from(arity)))?;
            write_index(writer, body)?;
        },
        ContentNode::DependentSplit {
            scrutinee,
            arity,
            motive,
            body,
        } => {
            writer.tag(Tag(0x5C));
            write_index(writer, scrutinee)?;
            writer.count(Count(usize::from(arity)))?;
            write_index(writer, motive)?;
            write_index(writer, body)?;
        },
        ContentNode::Reify(ref frames) => {
            writer.tag(Tag(0x71));
            writer.count(Count(frames.len()))?;
            for frame in frames.iter() {
                match *frame {
                    gandr_core_term::control::StackFrame::Apply(value) => {
                        writer.tag(Tag(0));
                        write_index(writer, value)?;
                    },
                    gandr_core_term::control::StackFrame::Bind(body) => {
                        writer.tag(Tag(1));
                        write_index(writer, body)?;
                    },
                    gandr_core_term::control::StackFrame::Project(component) => {
                        writer.tag(Tag(2));
                        writer.count(Count(usize::from(component)))?;
                    },
                }
            }
        },
        ContentNode::Stack { input, output } => {
            writer.tag(Tag(0x72));
            write_index(writer, input)?;
            write_index(writer, output)?;
        },
        ContentNode::WithType(ref components) => {
            writer.tag(Tag(0x73));
            write_indices(writer, components)?;
        },
        ContentNode::SessionType(ref session) => {
            writer.tag(Tag(0x60));
            write_session_type(writer, session)?;
        },
        ContentNode::Session(ref action) => {
            writer.tag(Tag(0x61));
            write_session_action(writer, action)?;
        },
        ContentNode::Memory(ref form) => {
            writer.tag(Tag(0x7E));
            let slot = |writer: &mut Writer<'_, Out>, index: DeBruijnIndex| {
                writer.word(Word(u64::from(u32::from(index))));
            };
            match *form {
                MemoryForm::Hold { value, body, grade } => {
                    writer.tag(Tag(match grade {
                        HoldGrade::Many => 0,
                        HoldGrade::One => 7,
                    }));
                    write_index(writer, value)?;
                    write_index(writer, body)?;
                },
                MemoryForm::Access {
                    mode,
                    held,
                    place,
                    body,
                } => {
                    writer.tag(Tag(match (mode, place) {
                        (AccessMode::Exclusive { .. }, AccessPlace::Whole) => 1,
                        (AccessMode::Shared, AccessPlace::Whole) => 4,
                        (AccessMode::Exclusive { .. }, AccessPlace::At { .. }) => 5,
                        (AccessMode::Shared, AccessPlace::At { .. }) => 6,
                    }));
                    slot(writer, held);
                    if let AccessPlace::At { index } = place {
                        write_index(writer, index)?;
                    }
                    write_index(writer, body)?;
                    if let AccessMode::Exclusive { unwind } = mode {
                        write_index(writer, unwind)?;
                    }
                },
                MemoryForm::Resume { view, value } => {
                    writer.tag(Tag(2));
                    slot(writer, view);
                    write_index(writer, value)?;
                },
                MemoryForm::Abort { view } => {
                    writer.tag(Tag(3));
                    slot(writer, view);
                },
                MemoryForm::Consume { held } => {
                    writer.tag(Tag(8));
                    slot(writer, held);
                },
            }
        },
        ContentNode::SessionRelated {
            relation,
            source,
            target,
            payloads,
        } => {
            writer.tag(Tag(0x62));
            writer.tag(Tag(match relation {
                SessionRelation::Equivalence => 0,
                SessionRelation::Subtyping => 1,
            }));
            write_index(writer, source)?;
            write_index(writer, target)?;
            write_index(writer, payloads)?;
        },
        ContentNode::Stay(point) => {
            writer.tag(Tag(0x63));
            write_index(writer, point)?;
        },
        ContentNode::Then(first, second) => {
            writer.tag(Tag(0x64));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        ContentNode::Forward(translator) => {
            writer.tag(Tag(0x69));
            write_index(writer, translator)?;
        },
        ContentNode::FunctionFlow(domain, codomain) => {
            writer.tag(Tag(0x6A));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        ContentNode::FlowProduct(first, second) => {
            writer.tag(Tag(0x6B));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        ContentNode::Recorded(ref moves) => {
            writer.tag(Tag(0x65));
            writer.count(Count(moves.len()))?;
            for step in moves.iter() {
                write_move(writer, step)?;
            }
        },
        ContentNode::Dialogue(ref turns) => {
            writer.tag(Tag(0x6D));
            writer.count(Count(turns.len()))?;
            for turn in turns.iter() {
                write_side(writer, turn.endpoint);
                write_move(writer, &turn.movement)?;
            }
        },
        ContentNode::Web(ref pieces) => {
            writer.tag(Tag(0x6E));
            writer.count(Count(pieces.len()))?;
            for &piece in pieces.iter() {
                write_piece(writer, piece)?;
            }
        },
        ContentNode::Decompose(dialogue) => {
            writer.tag(Tag(0x83));
            write_index(writer, dialogue)?;
        },
        ContentNode::Ride {
            motive,
            flow,
            value,
        } => {
            writer.tag(Tag(0x66));
            write_index(writer, motive)?;
            write_index(writer, flow)?;
            write_index(writer, value)?;
        },
        ContentNode::FlowType {
            carrier,
            source,
            target,
        } => {
            writer.tag(Tag(0x67));
            write_index(writer, carrier)?;
            write_index(writer, source)?;
            write_index(writer, target)?;
        },
        ContentNode::RunType(code) => {
            writer.tag(Tag(0x68));
            write_index(writer, code)?;
        },
        ContentNode::PrefixType(code) => {
            writer.tag(Tag(0x6C));
            write_index(writer, code)?;
        },
        ContentNode::DialogueType(code) => {
            writer.tag(Tag(0x6F));
            write_index(writer, code)?;
        },
        ContentNode::WebType => writer.tag(Tag(0x82)),
        ContentNode::Perform {
            ref signature,
            ref operation,
            payload,
        } => {
            writer.tag(Tag(0x74));
            write_index(writer, payload)?;
            write_effect_signature(writer, signature)?;
            writer.bytes(Bytes(operation.as_ref().as_bytes()))?;
        },
        ContentNode::Handle {
            ref signature,
            subject,
            on_return,
            ref clauses,
        } => {
            writer.tag(Tag(0x75));
            write_index(writer, subject)?;
            write_index(writer, on_return)?;
            write_effect_signature(writer, signature)?;
            writer.count(Count(clauses.len()))?;
            for clause in clauses.iter() {
                writer.bytes(Bytes(clause.operation.as_ref().as_bytes()))?;
                write_index(writer, clause.body)?;
            }
        },
        ContentNode::Exercise {
            capability,
            ref signature,
            ref operation,
            payload,
        } => {
            writer.tag(Tag(0x7B));
            write_index(writer, capability)?;
            write_index(writer, payload)?;
            write_effect_signature(writer, signature)?;
            writer.bytes(Bytes(operation.as_ref().as_bytes()))?;
        },
        ContentNode::Scope {
            ref signature,
            subject,
            on_return,
            ref clauses,
        } => {
            writer.tag(Tag(0x7C));
            write_index(writer, subject)?;
            write_index(writer, on_return)?;
            write_effect_signature(writer, signature)?;
            writer.count(Count(clauses.len()))?;
            for clause in clauses.iter() {
                writer.bytes(Bytes(clause.operation.as_ref().as_bytes()))?;
                write_index(writer, clause.body)?;
            }
        },
        ContentNode::Capability {
            ref authority,
            grade,
            region,
        } => {
            writer.tag(Tag(0x7D));
            write_effect_row(writer, authority)?;
            writer.tag(match grade {
                gandr_core_term::effect::capability::CapabilityGrade::Durable => Tag(0),
                gandr_core_term::effect::capability::CapabilityGrade::Consumable => Tag(1),
            });
            write_region(writer, region);
        },
        ContentNode::KeptType { value, region } => {
            writer.tag(Tag(0x7F));
            write_index(writer, value)?;
            write_region(writer, region);
        },
        ContentNode::Resume(stack, body) => {
            writer.tag(Tag(0x76));
            write_index(writer, stack)?;
            write_index(writer, body)?;
        },
        ContentNode::Abandon(stack) => {
            writer.tag(Tag(0x81));
            write_index(writer, stack)?;
        },
        ContentNode::Reset(body) => {
            writer.tag(Tag(0x77));
            write_index(writer, body)?;
        },
        ContentNode::Shift(body) => {
            writer.tag(Tag(0x78));
            write_index(writer, body)?;
        },
        ContentNode::With(ref components) => {
            writer.tag(Tag(0x79));
            write_indices(writer, components)?;
        },
        ContentNode::Project(component, body) => {
            writer.tag(Tag(0x7A));
            writer.count(Count(usize::from(component)))?;
            write_index(writer, body)?;
        },
        ContentNode::PrimitiveValue(primitive) => {
            writer.tag(Tag(0x0D));
            writer.bytes(Bytes(primitive.name().as_ref().as_bytes()))?;
        },
        ContentNode::Primitive(primitive, arguments) => {
            writer.tag(Tag(0x16));
            writer.bytes(Bytes(primitive.name().as_ref().as_bytes()))?;
            writer.tag(match arguments {
                gandr_core_term::primitive::Arguments::Unary(_) => Tag(1),
                gandr_core_term::primitive::Arguments::Binary(_) => Tag(2),
            });
            for &argument in arguments.iter() {
                write_index(writer, argument)?;
            }
        },
        ContentNode::PathUniverse(source, target) => {
            writer.tag(Tag(0x40));
            write_index(writer, source)?;
            write_index(writer, target)?;
        },
        ContentNode::PathRefl(code) => {
            writer.tag(Tag(0x41));
            write_index(writer, code)?;
        },
        ContentNode::PathEquiv {
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
        ContentNode::PathProduct(first, second) => {
            writer.tag(Tag(0x43));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        ContentNode::Funext(left, right) => {
            writer.tag(Tag(0x49));
            write_index(writer, left)?;
            write_index(writer, right)?;
        },
        ContentNode::Equiv(forward, backward) => {
            writer.tag(Tag(0x4A));
            write_index(writer, forward)?;
            write_index(writer, backward)?;
        },
        ContentNode::Univalence(record, forward) => {
            writer.tag(Tag(0x4F));
            write_index(writer, record)?;
            write_index(writer, forward)?;
        },
        ContentNode::Ua {
            stratum,
            ref sides,
            forward,
            backward,
        } => {
            writer.tag(Tag(0x4C));
            writer.count(Count(usize::from(stratum.degree)))?;
            writer.count(Count(usize::from(stratum.bound)))?;
            write_description(writer, &sides.source)?;
            write_description(writer, &sides.target)?;
            write_index(writer, forward)?;
            write_index(writer, backward)?;
        },
        ContentNode::Compose {
            composite,
            ref cells,
            realised,
        } => {
            writer.tag(Tag(0x8A));
            writer.count(Count(usize::from(composite.stratum.degree)))?;
            writer.count(Count(usize::from(composite.stratum.bound)))?;
            write_pasting(writer, composite.pasting)?;
            write_index(writer, realised)?;
            write_indices(writer, cells)?;
        },
        ContentNode::Fill {
            composite,
            generator,
            ref cells,
        } => {
            writer.tag(Tag(0x8B));
            writer.count(Count(usize::from(composite.stratum.degree)))?;
            writer.count(Count(usize::from(composite.stratum.bound)))?;
            write_pasting(writer, composite.pasting)?;
            write_index(writer, generator)?;
            write_indices(writer, cells)?;
        },
        ContentNode::Transport(path, value) => {
            writer.tag(Tag(0x44));
            write_index(writer, path)?;
            write_index(writer, value)?;
        },
        ContentNode::PathType {
            carrier,
            left,
            right,
        } => {
            writer.tag(Tag(0x45));
            write_index(writer, carrier)?;
            write_index(writer, left)?;
            write_index(writer, right)?;
        },
        ContentNode::BridgeType {
            carrier,
            left,
            right,
        } => {
            writer.tag(Tag(0x89));
            write_index(writer, carrier)?;
            write_index(writer, left)?;
            write_index(writer, right)?;
        },
        ContentNode::Here(point) => {
            writer.tag(Tag(0x46));
            write_index(writer, point)?;
        },
        ContentNode::ElementTransport {
            motive,
            path,
            value,
        } => {
            writer.tag(Tag(0x47));
            write_index(writer, motive)?;
            write_index(writer, path)?;
            write_index(writer, value)?;
        },
        ContentNode::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value,
        } => {
            writer.tag(Tag(0x4B));
            for child in [motive, path, start, over, value] {
                write_index(writer, child)?;
            }
        },
        ContentNode::Returned(computation) => {
            writer.tag(Tag(0x48));
            write_index(writer, computation)?;
        },
        ContentNode::Nested(computation) => {
            writer.tag(Tag(0x4D));
            write_index(writer, computation)?;
        },
        ContentNode::Run(computation) => {
            writer.tag(Tag(0x4E));
            write_index(writer, computation)?;
        },
        ContentNode::RecordUpdate(base, overlay) => {
            writer.tag(Tag(0x84));
            write_index(writer, base)?;
            write_index(writer, overlay)?;
        },
        ContentNode::Variable { zone, index } => {
            writer.tag(Tag(0x01));
            writer.tag(match zone {
                Zone::Intuitionistic => Tag(0),
                Zone::Linear => Tag(1),
            });
            writer.word(Word(u64::from(u32::from(index))));
        },
        ContentNode::Constant(ref reference) => {
            writer.tag(Tag(0x02));
            write_reference(writer, reference)?;
        },
        ContentNode::Literal(ref literal) => {
            writer.tag(Tag(0x04));
            write_literal(writer, literal)?;
        },
        ContentNode::Tuple(ref components) => {
            writer.tag(Tag(0x05));
            write_indices(writer, components)?;
        },
        ContentNode::Injection(summand, body) => {
            writer.tag(Tag(0x06));
            writer.count(Count(usize::from(summand)))?;
            write_index(writer, body)?;
        },
        ContentNode::Thunk(body) => {
            writer.tag(Tag(0x07));
            write_index(writer, body)?;
        },
        ContentNode::ValueLift { ref target, body } => {
            writer.tag(Tag(0x08));
            write_level(writer, target)?;
            write_index(writer, body)?;
        },
        ContentNode::Quote(quoted) => {
            writer.tag(Tag(0x09));
            write_index(writer, quoted)?;
        },
        ContentNode::QuoteComputation(quoted) => {
            writer.tag(Tag(0x0A));
            write_index(writer, quoted)?;
        },
        ContentNode::StaticLambda(body) => {
            writer.tag(Tag(0x0B));
            write_index(writer, body)?;
        },
        ContentNode::StaticApplication(head, argument) => {
            writer.tag(Tag(0x0C));
            write_index(writer, head)?;
            write_index(writer, argument)?;
        },
        ContentNode::Hole(hole) => {
            writer.tag(Tag(0x0E));
            writer.word(Word(u64::from(u32::from(hole))));
        },
        ContentNode::ValueMark { mark, body } => {
            writer.tag(Tag(0x0F));
            writer.word(Word(u64::from(u32::from(mark))));
            write_index(writer, body)?;
        },
        ContentNode::Lambda(body) => {
            writer.tag(Tag(0x10));
            write_index(writer, body)?;
        },
        ContentNode::LinearLambda(body) => {
            writer.tag(Tag(0x91));
            write_index(writer, body)?;
        },
        ContentNode::Application(head, argument) => {
            writer.tag(Tag(0x11));
            write_index(writer, head)?;
            write_index(writer, argument)?;
        },
        ContentNode::Return(value) => {
            writer.tag(Tag(0x12));
            write_index(writer, value)?;
        },
        ContentNode::Bind(bound, rest) => {
            writer.tag(Tag(0x13));
            write_index(writer, bound)?;
            write_index(writer, rest)?;
        },
        ContentNode::ReturnAll(ref values) => {
            writer.tag(Tag(0x8D));
            write_indices(writer, values)?;
        },
        ContentNode::BindAll(bound, arity, rest) => {
            writer.tag(Tag(0x8E));
            write_index(writer, bound)?;
            writer.count(Count(usize::from(arity)))?;
            write_index(writer, rest)?;
        },
        ContentNode::Force(value) => {
            writer.tag(Tag(0x14));
            write_index(writer, value)?;
        },
        ContentNode::Case {
            scrutinee,
            ref branches,
        } => {
            writer.tag(Tag(0x15));
            write_index(writer, scrutinee)?;
            write_indices(writer, branches)?;
        },
        ContentNode::ComputationHole(hole) => {
            writer.tag(Tag(0x17));
            writer.word(Word(u64::from(u32::from(hole))));
        },
        ContentNode::ComputationMark { mark, body } => {
            writer.tag(Tag(0x18));
            writer.word(Word(u64::from(u32::from(mark))));
            write_index(writer, body)?;
        },
        ContentNode::Fixpoint { body, evidence } => {
            writer.tag(Tag(0x19));
            write_evidence(writer, evidence)?;
            write_index(writer, body)?;
        },
        ContentNode::Ascribe { body, ty } => {
            writer.tag(Tag(0x1A));
            write_index(writer, body)?;
            write_index(writer, ty)?;
        },
        ContentNode::ValueAscribe { value, ty } => {
            writer.tag(Tag(0x1B));
            write_index(writer, value)?;
            write_index(writer, ty)?;
        },
        ContentNode::Base(base) => {
            writer.tag(Tag(0x20));
            writer.tag(match base {
                BaseType::Integer => Tag(0),
                BaseType::String => Tag(1),
                BaseType::Numeric => Tag(2),
                BaseType::Character => Tag(3),
                BaseType::Float64 => Tag(8),
                BaseType::Fixed(IntegerWidth::U32) => Tag(4),
                BaseType::Fixed(IntegerWidth::U64) => Tag(5),
                BaseType::Fixed(IntegerWidth::I32) => Tag(6),
                BaseType::Fixed(IntegerWidth::I64) => Tag(7),
                BaseType::Fixed(IntegerWidth::U8) => Tag(9),
                BaseType::Fixed(IntegerWidth::U16) => Tag(10),
                BaseType::Fixed(IntegerWidth::I8) => Tag(11),
                BaseType::Fixed(IntegerWidth::I16) => Tag(12),
                BaseType::Fixed(IntegerWidth::Usize) => Tag(13),
                BaseType::Fixed(IntegerWidth::Isize) => Tag(14),
            });
        },
        ContentNode::Product(ref parts) => {
            writer.tag(Tag(0x22));
            write_indices(writer, parts)?;
        },
        ContentNode::Sum(ref parts) => {
            writer.tag(Tag(0x23));
            write_indices(writer, parts)?;
        },
        ContentNode::List(element) => {
            writer.tag(Tag(0x56));
            write_index(writer, element)?;
        },
        ContentNode::ListNil => writer.tag(Tag(0x57)),
        ContentNode::ListCons(head, tail) => {
            writer.tag(Tag(0x58));
            write_index(writer, head)?;
            write_index(writer, tail)?;
        },
        ContentNode::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        } => {
            writer.tag(Tag(0x59));
            for child in [element, result, list, on_nil, on_cons] {
                write_index(writer, child)?;
            }
        },
        ContentNode::ListCase {
            list,
            on_nil,
            on_cons,
        } => {
            writer.tag(Tag(0x5D));
            for child in [list, on_nil, on_cons] {
                write_index(writer, child)?;
            }
        },
        ContentNode::ThunkType(body) => {
            writer.tag(Tag(0x24));
            write_index(writer, body)?;
        },
        // The value universe keeps the tag it had before the sorts were
        // spelled, and the other two sorts take fresh tags, so a table
        // written before the families reads the same after them.
        ContentNode::Universe {
            sort: TypeSort::Ground(GroundSort::Value),
            ref level,
        } => {
            writer.tag(Tag(0x25));
            write_level(writer, level)?;
        },
        ContentNode::Universe {
            sort: TypeSort::Ground(GroundSort::Computation),
            ref level,
        } => {
            writer.tag(Tag(0x29));
            write_level(writer, level)?;
        },
        ContentNode::Universe {
            sort: TypeSort::Parameter(parameter),
            ref level,
        } => {
            writer.tag(Tag(0x2A));
            writer.word(Word(u64::from(u32::from(parameter))));
            write_level(writer, level)?;
        },
        ContentNode::TypeLift { inner, ref target } => {
            writer.tag(Tag(0x26));
            write_index(writer, inner)?;
            write_level(writer, target)?;
        },
        ContentNode::Element { code, ref target } => {
            writer.tag(Tag(0x27));
            write_index(writer, code)?;
            write_level(writer, target)?;
        },
        ContentNode::Abstract(ref reference) => {
            writer.tag(Tag(0x28));
            write_reference(writer, reference)?;
        },
        ContentNode::StaticPi { domain, codomain } => {
            writer.tag(Tag(0x2B));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        ContentNode::Sigma { first, second } => {
            writer.tag(Tag(0x2D));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        ContentNode::UnknownType => writer.tag(Tag(0x2C)),
        ContentNode::BufferType => writer.tag(Tag(0x80)),
        ContentNode::QubitType => writer.tag(Tag(0x93)),
        ContentNode::RowValue(ref row) => {
            writer.tag(Tag(0x85));
            write_effect_row(writer, row)?;
            match row.tail() {
                None => writer.tag(Tag(0)),
                Some(tail) => {
                    writer.tag(Tag(1));
                    write_index(writer, tail)?;
                },
            }
        },
        ContentNode::RowKind => writer.tag(Tag(0x86)),
        ContentNode::RowTail(code) => {
            writer.tag(Tag(0x87));
            write_index(writer, code)?;
        },
        ContentNode::Returner {
            result,
            ref effects,
        } => {
            if let Some(tail) = effects.tail() {
                writer.tag(Tag(0x88));
                write_index(writer, result)?;
                write_effect_row(writer, effects)?;
                write_index(writer, tail)?;
            }
            else if effects.purity() == gandr_core_term::effect::Purity::Pure {
                writer.tag(Tag(0x30));
                write_index(writer, result)?;
            }
            else {
                writer.tag(Tag(0x70));
                write_index(writer, result)?;
                write_effect_row(writer, effects)?;
            }
        },
        ContentNode::Returns {
            ref results,
            ref effects,
        } => {
            writer.tag(Tag(0x8C));
            write_indices(writer, results)?;
            write_effect_row(writer, effects)?;
            match effects.tail() {
                None => writer.tag(Tag(0)),
                Some(tail) => {
                    writer.tag(Tag(1));
                    write_index(writer, tail)?;
                },
            }
        },
        ContentNode::Arrow { domain, codomain } => {
            writer.tag(Tag(0x31));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        ContentNode::Pi { domain, codomain } => {
            writer.tag(Tag(0x32));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        ContentNode::LinearArrow {
            domain,
            multiplicity,
            codomain,
        } => {
            writer.tag(Tag(0x92));
            write_index(writer, domain)?;
            write_index(writer, multiplicity)?;
            write_index(writer, codomain)?;
        },
        ContentNode::ComputationElement { code, ref target } => {
            writer.tag(Tag(0x33));
            write_index(writer, code)?;
            write_level(writer, target)?;
        },
        ContentNode::UnknownComputationType => writer.tag(Tag(0x34)),
        ContentNode::Unresolved(sort) => {
            return Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(
                sort,
            )));
        },
    }
    Ok(())
}

/// Write a variadic sequence of child indices.
///
/// # Specification
/// - ensures: the sequence length precedes its indices in order.
/// - fails: an unrepresentable length or index.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — native round trips distinguish argument and branch order.
/// - witness: `gandr-core-incremental::tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_indices<Out>(
    writer: &mut Writer<'_, Out>,
    indices: &[NodeIndex],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(indices.len()))?;
    for &index in indices {
        write_index(writer, index)?;
    }
    Ok(())
}

/// Read child indices without allocating from an untrusted count.
///
/// # Specification
/// - ensures: a successful result consumes a count and exactly its indices.
/// - fails: malformed or truncated words.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — native round trips retain variadic order and reject
///   truncation.
/// - witness: `gandr-core-incremental::tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
///
/// # Cost
/// - allocation: the list of child indices, growth within the bytes
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.as_ref().map_or(true,|indices| reader.cursor == before.saturating_add(8).saturating_add(indices.len().saturating_mul(8))))]
#[inline]
pub fn read_indices(reader: &mut Reader<'_>) -> Result<Vec<NodeIndex>, CodecError>
{
    let count = reader.count()?;
    let mut indices = Vec::new();
    for _ in 0 .. count.0 {
        indices.push(read_index(reader)?);
    }
    Ok(indices)
}

/// Read one exact UTF-8 field label.
///
/// # Specification
/// - ensures: successful reads advance over one length-prefixed string.
/// - fails: invalid UTF-8 or a truncated frame.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — native records preserve exact labels across persistence.
/// - witness: `gandr-core-incremental::tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
///
/// # Cost
/// - allocation: the text of the label, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.as_ref().map_or(true,|label| reader.cursor == before.saturating_add(8).saturating_add(label.as_ref().len())))]
fn read_field_label(reader: &mut Reader<'_>) -> Result<gandr_core_term::FieldLabel, CodecError>
{
    let bytes = reader.bytes()?;
    let text = core::str::from_utf8(bytes.0).map_err(|_cause| CodecError::Corrupt)?;
    Ok(gandr_core_term::FieldLabel::from(String::from(text)))
}

/// Write record labels and children in lexical order.
///
/// # Specification
/// - ensures: every exact label and child follows the field count.
/// - fails: an unrepresentable count, string length or index.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — record persistence retains labels and field association.
/// - witness: `gandr-core-incremental::tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
fn write_fields<Out>(
    writer: &mut Writer<'_, Out>,
    fields: &alloc::collections::BTreeMap<gandr_core_term::FieldLabel, NodeIndex>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(fields.len()))?;
    for (label, &field) in fields {
        writer.bytes(Bytes(label.as_ref().as_bytes()))?;
        write_index(writer, field)?;
    }
    Ok(())
}

/// Read record fields, refusing duplicate or out-of-order labels.
///
/// # Specification
/// - ensures: a successful table has one child for each strictly ordered label.
/// - fails: malformed fields or noncanonical label order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — duplicate labels cannot silently overwrite a record
///   field.
/// - witness: `gandr-core-incremental::tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
///
/// # Cost
/// - allocation: the map of record fields, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor >= before.saturating_add(8))]
fn read_fields(
    reader: &mut Reader<'_>
) -> Result<alloc::collections::BTreeMap<gandr_core_term::FieldLabel, NodeIndex>, CodecError>
{
    let count = reader.count()?;
    let mut fields = alloc::collections::BTreeMap::new();
    for _ in 0 .. count.0 {
        let label = read_field_label(reader)?;
        if fields
            .last_key_value()
            .is_some_and(|(previous, _)| previous >= &label)
        {
            return Err(CodecError::NonCanonical);
        }
        let field = read_index(reader)?;
        let _previous = fields.insert(label, field);
    }
    Ok(fields)
}

/// Write a system's meets: the count, then each label and its value, in
/// written order.
///
/// # Specification
/// - ensures: every label and value follows the count, in written order.
/// - fails: an unrepresentable count, string length or index.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — a system of two faces keeps its meet across persistence.
/// - witness: `gandr-core-incremental::codec::tests::every_node_former_round_trips_under_its_own_frame`
fn write_meets<Out>(
    writer: &mut Writer<'_, Out>,
    meets: &[(gandr_core_term::FieldLabel, NodeIndex)],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(meets.len()))?;
    for &(ref label, value) in meets {
        writer.bytes(Bytes(label.as_ref().as_bytes()))?;
        write_index(writer, value)?;
    }
    Ok(())
}

/// Read a system's meets in written order.
///
/// # Specification
/// - ensures: one label and value for each counted meet, in written order.
/// - fails: a malformed label or index.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a system of two faces keeps its meet across persistence.
/// - witness: `gandr-core-incremental::codec::tests::every_node_former_round_trips_under_its_own_frame`
///
/// # Cost
/// - allocation: the list of meets, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor >= before.saturating_add(8))]
fn read_meets(
    reader: &mut Reader<'_>
) -> Result<Vec<(gandr_core_term::FieldLabel, NodeIndex)>, CodecError>
{
    let count = reader.count()?;
    let mut meets = Vec::new();
    for _ in 0 .. count.0 {
        let label = read_field_label(reader)?;
        meets.push((label, read_index(reader)?));
    }
    Ok(meets)
}

/// Write a protocol's labelled branches: the count, then each label and the
/// state it continues at, in label order.
///
/// # Specification
/// - ensures: the count, then each label's bytes and state follow in order.
/// - fails: an unrepresentable count or label length.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — a selection and an offer survive persistence with their
///   labels and continuations.
/// - witness: `gandr-core-incremental::codec::tests::session_nodes_persist_their_protocol_and_children`
fn write_branches<Out>(
    writer: &mut Writer<'_, Out>,
    branches: &alloc::collections::BTreeMap<gandr_core_term::FieldLabel, ProtocolState>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(branches.len()))?;
    for (label, &state) in branches {
        writer.bytes(Bytes(label.as_ref().as_bytes()))?;
        writer.count(Count(usize::from(state)))?;
    }
    Ok(())
}

/// Read a protocol's labelled branches, refusing duplicate or out-of-order
/// labels.
///
/// # Specification
/// - ensures: one continuation for each strictly ordered label.
/// - fails: malformed branches or noncanonical label order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a selection and an offer survive persistence with their
///   labels and continuations.
/// - witness: `gandr-core-incremental::codec::tests::session_nodes_persist_their_protocol_and_children`
///
/// # Cost
/// - allocation: the list of branches, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor >= before.saturating_add(8))]
fn read_branches(
    reader: &mut Reader<'_>
) -> Result<alloc::collections::BTreeMap<gandr_core_term::FieldLabel, ProtocolState>, CodecError>
{
    let count = reader.count()?;
    let mut branches = alloc::collections::BTreeMap::new();
    for _ in 0 .. count.0 {
        let label = read_field_label(reader)?;
        if branches
            .last_key_value()
            .is_some_and(|(previous, _)| previous >= &label)
        {
            return Err(CodecError::NonCanonical);
        }
        let state = ProtocolState::from(reader.count()?.0);
        let _previous = branches.insert(label, state);
    }
    Ok(branches)
}

/// Write a session type: its protocol in written form, the root, the state,
/// then the payload edges in slot order.
///
/// # Specification
/// - ensures: the node count, each written node, the root, the state and the
///   payload indices follow in order. The written form counts recursion
///   variables outward, so the bytes are a function of the protocol alone.
/// - fails: an unrepresentable count or label length.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive protocol with every former survives
///   persistence at a state past its root.
/// - witness: `gandr-core-incremental::codec::tests::session_nodes_persist_their_protocol_and_children`
///
/// # Cost
/// - allocation: the written form of the protocol, growth within the session
///   type
fn write_session_type<Out>(
    writer: &mut Writer<'_, Out>,
    session: &SessionType<NodeIndex>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let written = session.protocol().syntax();
    writer.count(Count(written.len()))?;
    for node in &written {
        match *node {
            ProtocolSyntax::Send { payload, next } => {
                writer.tag(Tag(0));
                writer.count(Count(usize::from(payload)))?;
                writer.count(Count(usize::from(next)))?;
            },
            ProtocolSyntax::Receive { payload, next } => {
                writer.tag(Tag(1));
                writer.count(Count(usize::from(payload)))?;
                writer.count(Count(usize::from(next)))?;
            },
            ProtocolSyntax::Select(ref branches) => {
                writer.tag(Tag(2));
                write_branches(writer, branches)?;
            },
            ProtocolSyntax::Offer(ref branches) => {
                writer.tag(Tag(3));
                write_branches(writer, branches)?;
            },
            ProtocolSyntax::End => writer.tag(Tag(4)),
            ProtocolSyntax::Mu(body) => {
                writer.tag(Tag(5));
                writer.count(Count(usize::from(body)))?;
            },
            ProtocolSyntax::Recur(outward) => {
                writer.tag(Tag(6));
                writer.count(Count(usize::from(outward)))?;
            },
        }
    }
    writer.count(Count(usize::from(session.protocol().root())))?;
    writer.count(Count(usize::from(session.state())))?;
    write_indices(writer, session.payloads())
}

/// Read a session type written by [`write_session_type`], validating the
/// protocol through the one constructor that admits protocols.
///
/// # Specification
/// - ensures: the session type of the written protocol, at the written state,
///   over the written payload edges.
/// - fails: [`CodecError::Corrupt`] for malformed bytes, an unknown node tag,
///   or a protocol or state the validation refuses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive protocol round-trips, and a protocol whose
///   recursion is not contractive is refused as corrupt.
/// - witness: `gandr-core-incremental::codec::tests::session_nodes_persist_their_protocol_and_children`
///
/// # Cost
/// - allocation: the session type and its payloads, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_session_type(reader: &mut Reader<'_>) -> Result<SessionType<NodeIndex>, CodecError>
{
    let count = reader.count()?;
    let mut written = Vec::new();
    for _ in 0 .. count.0 {
        written.push(match reader.tag()?.0 {
            0 => ProtocolSyntax::Send {
                payload: PayloadSlot::from(reader.count()?.0),
                next: ProtocolState::from(reader.count()?.0),
            },
            1 => ProtocolSyntax::Receive {
                payload: PayloadSlot::from(reader.count()?.0),
                next: ProtocolState::from(reader.count()?.0),
            },
            2 => ProtocolSyntax::Select(read_branches(reader)?),
            3 => ProtocolSyntax::Offer(read_branches(reader)?),
            4 => ProtocolSyntax::End,
            5 => ProtocolSyntax::Mu(ProtocolState::from(reader.count()?.0)),
            6 => ProtocolSyntax::Recur(RecursionIndex::from(reader.count()?.0)),
            _ => return Err(CodecError::Corrupt),
        });
    }
    let root = ProtocolState::from(reader.count()?.0);
    let state = ProtocolState::from(reader.count()?.0);
    let payloads = read_indices(reader)?;
    let protocol = Protocol::new(written, root, PayloadCount::from(payloads.len()))
        .map_err(|_refused| CodecError::Corrupt)?;
    SessionType::new(alloc::sync::Arc::new(protocol), payloads.into())
        .and_then(|session| session.at(state))
        .map_err(|_refused| CodecError::Corrupt)
}

/// Write a session action: its kind, its endpoint, then its label, payload,
/// arms or fork edges.
///
/// # Specification
/// - ensures: the kind's tag, then the endpoint for an action on one, then the
///   action's own fields in [`SessionAction`] order.
/// - fails: an unrepresentable count or label length.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — every action kind survives persistence with its endpoint,
///   label and children.
/// - witness: `gandr-core-incremental::codec::tests::session_nodes_persist_their_protocol_and_children`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_session_action<Out>(
    writer: &mut Writer<'_, Out>,
    action: &SessionAction<NodeIndex, NodeIndex, NodeIndex>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let endpoint = |writer: &mut Writer<'_, Out>, index: DeBruijnIndex| {
        writer.word(Word(u64::from(u32::from(index))));
    };
    match *action {
        SessionAction::Send {
            endpoint: subject,
            payload,
        } => {
            writer.tag(Tag(0));
            endpoint(writer, subject);
            write_index(writer, payload)?;
        },
        SessionAction::Receive {
            endpoint: subject,
            body,
        } => {
            writer.tag(Tag(1));
            endpoint(writer, subject);
            write_index(writer, body)?;
        },
        SessionAction::Select {
            endpoint: subject,
            ref label,
        } => {
            writer.tag(Tag(2));
            endpoint(writer, subject);
            writer.bytes(Bytes(label.as_ref().as_bytes()))?;
        },
        SessionAction::Offer {
            endpoint: subject,
            ref arms,
        } => {
            writer.tag(Tag(3));
            endpoint(writer, subject);
            write_fields(writer, arms)?;
        },
        SessionAction::Close { endpoint: subject } => {
            writer.tag(Tag(4));
            endpoint(writer, subject);
        },
        SessionAction::Fork {
            protocol,
            child,
            parent,
        } => {
            writer.tag(Tag(5));
            write_index(writer, protocol)?;
            write_index(writer, child)?;
            write_index(writer, parent)?;
        },
        SessionAction::Place { payload, body } => {
            writer.tag(Tag(6));
            write_index(writer, payload)?;
            write_index(writer, body)?;
        },
    }
    Ok(())
}

/// Read a session action written by [`write_session_action`].
///
/// # Specification
/// - ensures: the action of the written kind over the written endpoint, label,
///   payload, arms, receive body or fork edges.
/// - fails: [`CodecError::Corrupt`] for malformed bytes, an unknown kind or an
///   endpoint past the `u32` ceiling; [`CodecError::NonCanonical`] for arms out
///   of label order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every action kind round-trips.
/// - witness: `gandr-core-incremental::codec::tests::session_nodes_persist_their_protocol_and_children`
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
///
/// # Cost
/// - allocation: the label and the arms of the action, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
#[inline]
pub fn read_session_action(
    reader: &mut Reader<'_>
) -> Result<SessionAction<NodeIndex, NodeIndex, NodeIndex>, CodecError>
{
    let endpoint = |reader: &mut Reader<'_>| {
        let word = reader.word()?;
        u32::try_from(word.0)
            .map(DeBruijnIndex::from)
            .map_err(|_overflow| CodecError::Corrupt)
    };
    Ok(match reader.tag()?.0 {
        0 => SessionAction::Send {
            endpoint: endpoint(reader)?,
            payload: read_index(reader)?,
        },
        1 => SessionAction::Receive {
            endpoint: endpoint(reader)?,
            body: read_index(reader)?,
        },
        2 => SessionAction::Select {
            endpoint: endpoint(reader)?,
            label: read_field_label(reader)?,
        },
        3 => SessionAction::Offer {
            endpoint: endpoint(reader)?,
            arms: read_fields(reader)?,
        },
        4 => SessionAction::Close {
            endpoint: endpoint(reader)?,
        },
        5 => SessionAction::Fork {
            protocol: read_index(reader)?,
            child: read_index(reader)?,
            parent: read_index(reader)?,
        },
        6 => SessionAction::Place {
            payload: read_index(reader)?,
            body: read_index(reader)?,
        },
        _ => return Err(CodecError::Corrupt),
    })
}

/// Write a description as univalence at a stratum reads it: its name, then
/// each generator's label and port counts, in written order.
///
/// # Specification
/// - ensures: the name, the generator count and each generator follow in order.
/// - fails: an unrepresentable count or string length.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — a statement's descriptions survive persistence with their
///   generators' order and profiles.
/// - witness: `gandr-core-incremental::tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
fn write_description<Out>(
    writer: &mut Writer<'_, Out>,
    description: &gandr_core_term::ua::Description,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.bytes(Bytes(description.name.as_ref().as_bytes()))?;
    writer.count(Count(description.generators.len()))?;
    for generator in &description.generators {
        writer.bytes(Bytes(generator.label.as_ref().as_bytes()))?;
        writer.count(Count(usize::from(generator.profile.inputs)))?;
        writer.count(Count(usize::from(generator.profile.outputs)))?;
    }
    Ok(())
}

/// Read a description [`write_description`] wrote.
///
/// # Specification
/// - ensures: the name and the generators in the order written.
/// - fails: invalid UTF-8 or a truncated frame.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a statement's descriptions survive persistence with their
///   generators' order and profiles.
/// - witness: `gandr-core-incremental::tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
///
/// # Cost
/// - allocation: the decoded description, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor >= before.saturating_add(16))]
fn read_description(reader: &mut Reader<'_>)
-> Result<gandr_core_term::ua::Description, CodecError>
{
    let name = reader.text()?;
    let count = reader.count()?;
    let mut generators = Vec::new();
    for _ in 0 .. count.0 {
        let label = read_field_label(reader)?;
        let inputs = reader.count()?;
        let outputs = reader.count()?;
        generators.push(gandr_core_term::ua::Generator {
            label,
            profile: gandr_theory_sites::Profile {
                inputs: gandr_theory_sites::PortCount::from(inputs.0),
                outputs: gandr_theory_sites::PortCount::from(outputs.0),
            },
        });
    }
    Ok(gandr_core_term::ua::Description {
        name: gandr_theory_levitation::Name::from(name),
        generators: generators.into_boxed_slice(),
    })
}

/// Write the pasting a composite names: a tag naming its level, then the
/// tree.
///
/// Levels one and two keep the frames they had before the tree: a chain's
/// cell count, and a level-two shape's column count and column heights.
///
/// # Specification
/// - ensures: at level one, the chain's tag, then its cell count; at level two,
///   the level-two tag, then its column count and each column's height in
///   order; past level two, the tree's tag, then the level, the walk's step
///   count and each step, `0` down and `1` up.
/// - fails: an unrepresentable count.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — a composite and its refusal survive persistence with
///   their pasting, a chain's, a level-two shape's and a level-three tree's.
/// - witness: `gandr-core-incremental::codec::tests::every_refusal_round_trips_under_its_own_encoding`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_pasting<Out>(
    writer: &mut Writer<'_, Out>,
    pasting: gandr_core_term::compose::Pasting,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match pasting.form() {
        gandr_core_term::compose::Form::Chain(cells) => {
            writer.tag(Tag(0));
            writer.count(Count(usize::from(cells)))
        },
        gandr_core_term::compose::Form::Columns(tree) => {
            writer.tag(Tag(1));
            writer.count(Count(tree.columns().count()))?;
            for height in tree.columns() {
                writer.count(Count(usize::from(height)))?;
            }
            Ok(())
        },
        gandr_core_term::compose::Form::Tree { level, tree } => {
            writer.tag(Tag(2));
            writer.count(Count(usize::from(level)))?;
            writer.count(Count(tree.walk().count()))?;
            for step in tree.walk() {
                writer.tag(Tag(match step {
                    gandr_core_term::compose::Step::Down => 0,
                    gandr_core_term::compose::Step::Up => 1,
                }));
            }
            Ok(())
        },
    }
}

/// Read a pasting [`write_pasting`] wrote.
///
/// # Specification
/// - ensures: the pasting the tag names, at its level, with its tree.
/// - fails: an unknown tag, a truncated frame, a tree past one word, a walk
///   that goes around no tree, or a tree taller than its level.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a composite and its refusal survive persistence with
///   their pasting, a chain's, a level-two shape's and a level-three tree's.
/// - witness: `gandr-core-incremental::codec::tests::every_refusal_round_trips_under_its_own_encoding`
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
///
/// # Cost
/// - allocation: the pieces of the pasting, growth within the bytes
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
#[inline]
pub fn read_pasting(
    reader: &mut Reader<'_>
) -> Result<gandr_core_term::compose::Pasting, CodecError>
{
    let corrupt = |_unpacked: gandr_core_term::compose::PastingError| CodecError::Corrupt;
    match reader.tag()?.0 {
        0 => gandr_core_term::compose::Pasting::chain(gandr_core_term::compose::CellCount::from(
            reader.count()?.0,
        ))
        .map_err(corrupt),
        1 => {
            let columns = reader.count()?.0;
            let mut heights = Vec::new();
            for _column in 0 .. columns {
                heights.push(gandr_core_term::compose::CellCount::from(reader.count()?.0));
                if heights.len() > 31 {
                    return Err(CodecError::Corrupt);
                }
            }
            gandr_core_term::compose::Pasting::columns(&heights).map_err(corrupt)
        },
        2 => {
            let level = gandr_core_term::compose::Level::try_from(reader.count()?.0)
                .map_err(|_wide| CodecError::Corrupt)?;
            let steps = reader.count()?.0;
            let mut walk = Vec::new();
            for _step in 0 .. steps {
                walk.push(match reader.tag()?.0 {
                    0 => gandr_core_term::compose::Step::Down,
                    1 => gandr_core_term::compose::Step::Up,
                    _ => return Err(CodecError::Corrupt),
                });
                if walk.len() > 62 {
                    return Err(CodecError::Corrupt);
                }
            }
            let tree = gandr_core_term::compose::Tree::from_walk(walk).map_err(corrupt)?;
            gandr_core_term::compose::Pasting::new(level, tree).map_err(corrupt)
        },
        _ => Err(CodecError::Corrupt),
    }
}

/// Write an inline interface in canonical operation order.
///
/// # Specification
/// - ensures: names precede ordered payload and reply indices.
/// - fails: unrepresentable byte lengths or indices.
///
/// # Adequacy
/// - hypothesis: L3 — persistence distinguishes operation names and ordered
///   type edges.
/// - witness: `gandr-core-incremental::codec::tests::control_nodes_persist_names_frames_and_branch_order`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[spec(ensures: |ret| matches!(ret, Ok(()) | Err(CodecError::Unrepresentable)))]
#[inline]
pub fn write_effect_signature<Out>(
    writer: &mut Writer<'_, Out>,
    signature: &gandr_core_term::effect::EffectSig<NodeIndex>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.bytes(Bytes(signature.name().as_ref().as_bytes()))?;
    writer.count(Count(signature.operations().len()))?;
    for operation in signature.operations() {
        writer.bytes(Bytes(operation.name.as_ref().as_bytes()))?;
        write_index(writer, operation.payload)?;
        write_index(writer, operation.reply)?;
    }
    Ok(())
}

/// Read an interface without accepting duplicate or noncanonical operations.
///
/// # Specification
/// - ensures: a successful signature consumes its complete name and type edges.
/// - fails: corrupt fields or operation names not in strictly increasing order.
///
/// # Adequacy
/// - hypothesis: L3 — malformed signatures cannot acquire a second canonical
///   spelling.
/// - witness: `gandr-core-incremental::codec::tests::effect_rows_reject_duplicate_and_noncanonical_names`
/// - witness: `gandr-core-incremental::codec::tests::control_nodes_persist_names_frames_and_branch_order`
///
/// # Cost
/// - allocation: the operations of the interface, growth within the bytes
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[spec(captures: before = reader.cursor, ensures: |ret| match ret { Ok(_) => reader.cursor > before && reader.cursor <= reader.bytes.len(), Err(error) => error == CodecError::Corrupt })]
#[inline]
pub fn read_effect_signature(
    reader: &mut Reader<'_>
) -> Result<gandr_core_term::effect::EffectSig<NodeIndex>, CodecError>
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let name = EffectName::from(
        core::str::from_utf8(reader.bytes()?.0).map_err(|_invalid_utf8| CodecError::Corrupt)?,
    );
    let count = reader.count()?;
    let mut operations: Vec<EffectOp<NodeIndex>> = Vec::new();
    for _ in 0 .. count.0 {
        let name = OperationName::from(
            core::str::from_utf8(reader.bytes()?.0).map_err(|_invalid_utf8| CodecError::Corrupt)?,
        );
        if operations
            .last()
            .is_some_and(|previous| previous.name >= name)
        {
            return Err(CodecError::Corrupt);
        }
        operations.push(EffectOp {
            name,
            payload: read_index(reader)?,
            reply: read_index(reader)?,
        });
    }
    EffectSig::new(name, operations).map_err(|_duplicate_operation| CodecError::Corrupt)
}

/// Write a canonical instance map: each instance's region, the held region for
/// an interface's default, then its signature and every operation's type
/// indices.
///
/// # Specification
/// - ensures: a representable row's instances are written in label and
///   operation name order; its tail, when it has one, is the caller's to write.
/// - fails: `Unrepresentable` when a name length or node index cannot be
///   encoded.
///
/// # Adequacy
/// - hypothesis: L3 — relocation and persistence distinguish operation names
///   and types.
/// - witness: `gandr-core-incremental::codec::tests::effect_rows_persist_operation_types_and_canonical_identity`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[spec(ensures: |ret| matches!(ret, Ok(()) | Err(CodecError::Unrepresentable)))]
#[inline]
pub fn write_effect_row<Out>(
    writer: &mut Writer<'_, Out>,
    row: &gandr_core_term::effect::EffectRow<NodeIndex>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(row.instances().len()))?;
    for (label, signature) in row.instances() {
        write_region(writer, label.region());
        write_effect_signature(writer, signature)?;
    }
    Ok(())
}

/// Read an instance map without accepting duplicate or noncanonical labels.
///
/// # Specification
/// - ensures: successful rows consume input and preserve canonical labels and
///   type edges.
/// - fails: `Corrupt` for malformed input or labels not in strictly increasing
///   order.
///
/// # Adequacy
/// - hypothesis: L3 — round trips preserve nested operation types; malformed
///   rows are refused.
/// - witness: `gandr-core-incremental::codec::tests::effect_rows_reject_duplicate_and_noncanonical_names`
/// - witness: `gandr-core-incremental::codec::tests::effect_rows_persist_operation_types_and_canonical_identity`
///
/// # Cost
/// - allocation: the instance map of the row, growth within the bytes
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[spec(captures: [before = reader.cursor], ensures: |ret| match ret { Ok(_) => reader.cursor > before && reader.cursor <= reader.bytes.len(), Err(error) => error == CodecError::Corrupt })]
#[inline]
pub fn read_effect_row(
    reader: &mut Reader<'_>
) -> Result<gandr_core_term::effect::EffectRow<NodeIndex>, CodecError>
{
    use gandr_core_term::effect::EffectLabel;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::capability::Region;
    let count = reader.count()?;
    let mut placed: Vec<(EffectSig<NodeIndex>, Region)> = Vec::new();
    let mut previous: Option<EffectLabel> = None;
    for _ in 0 .. count.0 {
        let region = read_region(reader)?;
        let signature = read_effect_signature(reader)?;
        let label = EffectLabel::at(signature.name(), region);
        if previous.as_ref().is_some_and(|previous| *previous >= label) {
            return Err(CodecError::Corrupt);
        }
        previous = Some(label);
        placed.push((signature, region));
    }
    EffectRow::from_placed(placed).map_err(|_duplicate_label| CodecError::Corrupt)
}

/// Read a row literal's tail: absent, or the index of the row term it stands
/// for.
///
/// # Specification
/// - ensures: one tag byte, then an index when the tag is one.
/// - fails: `Corrupt` for a tag past one or a malformed index.
///
/// # Adequacy
/// - hypothesis: L3 — an open and a closed row literal each round trip.
/// - witness: `gandr-core-incremental::codec::tests::every_node_former_round_trips_under_its_own_frame`
///
/// # Cost
/// - allocation: the tail of the row literal, growth within the bytes
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[spec(captures: [before = reader.cursor], ensures: |ret| ret.is_err() || reader.cursor > before)]
#[inline]
pub fn read_row_tail(reader: &mut Reader<'_>) -> Result<Option<NodeIndex>, CodecError>
{
    match reader.tag()?.0 {
        0 => Ok(None),
        1 => read_index(reader).map(Some),
        _ => Err(CodecError::Corrupt),
    }
}

/// Read one content node.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for an unknown tag or a malformed field; no
///   tag spells an unresolved node. [`CodecError::NonCanonical`] for a patched
///   type that fixes no label.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite semantic and universe corpora exercise tag
///   classes across all four sorts. The predicate relates the consumed tag to
///   the resulting class, not every payload field; unresolved nodes have no
///   accepted tag. Unknown node tags and invalid zone, side and base fields
///   stop at the tag.
/// - witness: `gandr-core-incremental::persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `gandr-core-incremental::persistence::tests::universe_sorts_and_levels_round_trip`
/// - witness: `gandr-core-incremental::codec::tests::decoders_reject_unknown_tags_before_payloads`
/// - witness: `gandr-core-incremental::codec::tests::type_tables_validate_roots_child_extents_and_sorts`
/// - witness: `gandr-core-incremental::codec::tests::every_node_former_round_trips_under_its_own_frame`
/// - witness: `gandr-core-incremental::codec::tests::a_patched_frame_that_fixes_no_label_is_refused`
///
/// # Cost
/// - allocation: the node's own lists of children and fields, growth within the
///   stored table
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref node) => {
            reader.cursor > before
                && reader.cursor <= reader.bytes.len()
                && reader.bytes.get(before).is_some_and(|&tag| match *node {
                    ContentNode::Data { .. } => tag == 0x50,
                    ContentNode::Codata { .. } => tag == 0x99,
                    ContentNode::RecordType(_) => tag == 0x51,
                    ContentNode::Patched { ref meets, .. } => tag == if meets.is_empty() { 0x8F } else { 0x90 },
                    ContentNode::Constructor { .. } => tag == 0x52,
                    ContentNode::Record(_) => tag == 0x53,
                    ContentNode::DataCase { equations, .. } => tag == if usize::from(equations) == 0 { 0x54 } else { 0x5E },
                    ContentNode::RecordProjection(..) => tag == 0x55,
                    ContentNode::TupleProjection(..) => tag == 0x5A,
                    ContentNode::Split(..) => tag == 0x5B,
                    ContentNode::DependentSplit { .. } => tag == 0x5C,
                    | ContentNode::Reify(_) => tag == 0x71,
                    | ContentNode::Stack { .. } => tag == 0x72,
                    | ContentNode::WithType(..) => tag == 0x73,
                    | ContentNode::SessionType(_) => tag == 0x60,
                    | ContentNode::Session(_) => tag == 0x61,
                    | ContentNode::Memory(_) => tag == 0x7E,
                    | ContentNode::Hold(_) => tag == 0x94,
                    | ContentNode::Leta { .. } => tag == 0x95,
                    | ContentNode::Migrate { .. } => tag == 0x96,
                    | ContentNode::HeldType { .. } => tag == 0x97,
                    | ContentNode::CapabilityType(_) => tag == 0x98,
                    | ContentNode::SessionRelated { .. } => tag == 0x62,
                    | ContentNode::Stay(_) => tag == 0x63,
                    | ContentNode::Then(..) => tag == 0x64,
                    | ContentNode::Forward(_) => tag == 0x69,
                    | ContentNode::FunctionFlow(..) => tag == 0x6A,
                    | ContentNode::FlowProduct(..) => tag == 0x6B,
                    | ContentNode::Recorded(_) => tag == 0x65,
                    | ContentNode::Ride { .. } => tag == 0x66,
                    | ContentNode::FlowType { .. } => tag == 0x67,
                    | ContentNode::RunType(_) => tag == 0x68,
                    | ContentNode::PrefixType(_) => tag == 0x6C,
                    | ContentNode::Dialogue(_) => tag == 0x6D,
                    | ContentNode::Web(_) => tag == 0x6E,
                    | ContentNode::DialogueType(_) => tag == 0x6F,
                    | ContentNode::WebType => tag == 0x82,
                    | ContentNode::Decompose(_) => tag == 0x83,
                    | ContentNode::Perform { .. } => tag == 0x74,
                    | ContentNode::Handle { .. } => tag == 0x75,
                    | ContentNode::Exercise { .. } => tag == 0x7B,
                    | ContentNode::Scope { .. } => tag == 0x7C,
                    | ContentNode::Capability { .. } => tag == 0x7D,
                    | ContentNode::KeptType { .. } => tag == 0x7F,
                    | ContentNode::Resume(..) => tag == 0x76,
                    | ContentNode::Abandon(_) => tag == 0x81,
                    | ContentNode::Reset(_) => tag == 0x77,
                    | ContentNode::Shift(_) => tag == 0x78,
                    | ContentNode::With(..) => tag == 0x79,
                    | ContentNode::Ascribe { .. } => tag == 0x1A,
                    | ContentNode::ValueAscribe { .. } => tag == 0x1B,
                    | ContentNode::Project(..) => tag == 0x7A,
                    | ContentNode::PrimitiveValue(_) => tag == 0x0D,
                    | ContentNode::Primitive(..) => tag == 0x16,
                    | ContentNode::PathUniverse(..) => tag == 0x40,
                    | ContentNode::PathRefl(_) => tag == 0x41,
                    | ContentNode::PathEquiv { .. } => tag == 0x42,
                    | ContentNode::PathProduct(..) => tag == 0x43,
                    | ContentNode::Transport(..) => tag == 0x44,
                    | ContentNode::PathType { .. } => tag == 0x45,
                    | ContentNode::BridgeType { .. } => tag == 0x89,
                    | ContentNode::Here(_) => tag == 0x46,
                    | ContentNode::ElementTransport { .. } => tag == 0x47,
                    | ContentNode::Returned(_) => tag == 0x48,
                    | ContentNode::Nested(_) => tag == 0x4D,
                    | ContentNode::Run(_) => tag == 0x4E,
                    | ContentNode::RecordUpdate(..) => tag == 0x84,
                    | ContentNode::Funext(..) => tag == 0x49,
                    | ContentNode::Equiv(..) => tag == 0x4A,
                    | ContentNode::Univalence(..) => tag == 0x4F,
                    | ContentNode::TelescopeTransport { .. } => tag == 0x4B,
                    | ContentNode::Ua { .. } => tag == 0x4C,
                    | ContentNode::Compose { .. } => tag == 0x8A,
                    | ContentNode::Fill { .. } => tag == 0x8B,
                    | ContentNode::Variable { .. } => tag == 0x01,
                    | ContentNode::Constant(_) => tag == 0x02,
                    | ContentNode::Literal(_) => tag == 0x04,
                    | ContentNode::Tuple(_) => tag == 0x05,
                    | ContentNode::Injection(..) => tag == 0x06,
                    | ContentNode::Thunk(_) => tag == 0x07,
                    | ContentNode::ValueLift { .. } => tag == 0x08,
                    | ContentNode::Quote(_) => tag == 0x09,
                    | ContentNode::QuoteComputation(_) => tag == 0x0A,
                    | ContentNode::StaticLambda(_) => tag == 0x0B,
                    | ContentNode::StaticApplication(..) => tag == 0x0C,
                    | ContentNode::Hole(_) => tag == 0x0E,
                    | ContentNode::ValueMark { .. } => tag == 0x0F,
                    | ContentNode::Lambda(_) => tag == 0x10,
                    | ContentNode::LinearLambda(_) => tag == 0x91,
                    | ContentNode::Application(..) => tag == 0x11,
                    | ContentNode::Return(_) => tag == 0x12,
                    | ContentNode::Bind(..) => tag == 0x13,
                    | ContentNode::ReturnAll(_) => tag == 0x8D,
                    | ContentNode::BindAll(..) => tag == 0x8E,
                    | ContentNode::Returns { .. } => tag == 0x8C,
                    | ContentNode::Force(_) => tag == 0x14,
                    | ContentNode::Case { .. } => tag == 0x15,
                    | ContentNode::ComputationHole(_) => tag == 0x17,
                    | ContentNode::ComputationMark { .. } => tag == 0x18,
                    | ContentNode::Fixpoint { .. } => tag == 0x19,
                    | ContentNode::Base(_) => tag == 0x20,
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
                    | ContentNode::Sigma { .. } => tag == 0x2D,
                    | ContentNode::UnknownType => tag == 0x2C,
                    | ContentNode::BufferType => tag == 0x80,
                    | ContentNode::QubitType => tag == 0x93,
                    | ContentNode::RowValue(_) => tag == 0x85,
                    | ContentNode::RowKind => tag == 0x86,
                    | ContentNode::RowTail(_) => tag == 0x87,
                    | ContentNode::List(_) => tag == 0x56,
                    | ContentNode::ListNil => tag == 0x57,
                    | ContentNode::ListCons(..) => tag == 0x58,
                    | ContentNode::ListFold { .. } => tag == 0x59,
                    | ContentNode::ListCase { .. } => tag == 0x5D,
                    | ContentNode::Returner { ref effects, .. } => tag == if effects.tail().is_some() { 0x88 } else if effects.purity() == gandr_core_term::effect::Purity::Pure { 0x30 } else { 0x70 },
                    | ContentNode::Arrow { .. } => tag == 0x31,
                    | ContentNode::Pi { .. } => tag == 0x32,
                    | ContentNode::LinearArrow { .. } => tag == 0x92,
                    | ContentNode::ComputationElement { .. } => tag == 0x33,
                    | ContentNode::UnknownComputationType => tag == 0x34,
                    | ContentNode::Unresolved(_) => false,
                })
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(error) => matches!(error,CodecError::Corrupt | CodecError::NonCanonical),
    },
)]
#[inline]
pub fn read_node(reader: &mut Reader<'_>) -> Result<ContentNode, CodecError>
{
    let tag = reader.tag()?;
    let node = match tag.0 {
        0x50 => ContentNode::Data {
            declaration: read_reference(reader)?,
            arguments: read_indices(reader)?,
        },
        0x99 => ContentNode::Codata {
            declaration: read_reference(reader)?,
            arguments: read_indices(reader)?,
        },
        0x51 => ContentNode::RecordType(read_fields(reader)?),
        // A patch that fixes no label is its base, which the arena mints in
        // its place: no canonical frame holds one. A system of faces holds at
        // least one meet under its own tag.
        0x8F => {
            let base = read_index(reader)?;
            let fixed = read_fields(reader)?;
            if fixed.is_empty() {
                return Err(CodecError::NonCanonical);
            }
            ContentNode::Patched {
                base,
                fixed,
                meets: Vec::new(),
            }
        },
        0x90 => {
            let base = read_index(reader)?;
            let fixed = read_fields(reader)?;
            let meets = read_meets(reader)?;
            if fixed.is_empty() || meets.is_empty() {
                return Err(CodecError::NonCanonical);
            }
            ContentNode::Patched { base, fixed, meets }
        },
        0x52 => ContentNode::Constructor {
            family: read_reference(reader)?,
            datatype: read_index(reader)?,
            tag: gandr_core_term::ConstructorTag::from(reader.count()?.0),
            fields: read_indices(reader)?,
        },
        0x53 => ContentNode::Record(read_fields(reader)?),
        0x54 | 0x5E => {
            let scrutinee = read_index(reader)?;
            let motive = read_index(reader)?;
            let branches = read_indices(reader)?;
            let count = reader.count()?;
            let mut arities = Vec::new();
            for _ in 0 .. count.0 {
                arities.push(gandr_kernel_term::FieldCount::from(reader.count()?.0));
            }
            let equations = if tag.0 == 0x5E {
                match reader.count()?.0 {
                    0 => return Err(CodecError::Corrupt),
                    owed => gandr_kernel_term::EquationCount::from(owed),
                }
            }
            else {
                gandr_kernel_term::EquationCount::NONE
            };
            ContentNode::DataCase {
                scrutinee,
                motive,
                branches,
                arities,
                equations,
            }
        },
        0x55 => ContentNode::RecordProjection(read_index(reader)?, read_field_label(reader)?),
        0x5A => ContentNode::TupleProjection(
            read_index(reader)?,
            gandr_core_term::Component::from(reader.count()?.0),
        ),
        0x5B => {
            let scrutinee = read_index(reader)?;
            let arity = gandr_core_term::ComponentCount::from(reader.count()?.0);
            ContentNode::Split(scrutinee, arity, read_index(reader)?)
        },
        0x5C => {
            let scrutinee = read_index(reader)?;
            let arity = gandr_core_term::ComponentCount::from(reader.count()?.0);
            let motive = read_index(reader)?;
            ContentNode::DependentSplit {
                scrutinee,
                arity,
                motive,
                body: read_index(reader)?,
            }
        },
        0x71 => {
            let count = reader.count()?;
            let mut frames = Vec::new();
            for _ in 0 .. count.0 {
                frames.push(match reader.tag()?.0 {
                    0 => gandr_core_term::control::StackFrame::Apply(read_index(reader)?),
                    1 => gandr_core_term::control::StackFrame::Bind(read_index(reader)?),
                    2 => gandr_core_term::control::StackFrame::Project(
                        gandr_core_term::Component::from(reader.count()?.0),
                    ),
                    _ => return Err(CodecError::Corrupt),
                });
            }
            ContentNode::Reify(frames.into())
        },
        0x72 => ContentNode::Stack {
            input: read_index(reader)?,
            output: read_index(reader)?,
        },
        0x73 => ContentNode::WithType(read_indices(reader)?),
        0x60 => ContentNode::SessionType(read_session_type(reader)?),
        0x61 => ContentNode::Session(read_session_action(reader)?),
        0x94 => ContentNode::Hold(read_index(reader)?),
        0x95 => {
            let world = read_world(reader)?;
            let value = read_index(reader)?;
            ContentNode::Leta {
                world,
                value,
                body: read_index(reader)?,
            }
        },
        0x96 => {
            let world = read_world(reader)?;
            ContentNode::Migrate {
                world,
                body: read_index(reader)?,
            }
        },
        0x97 => {
            let inner = read_index(reader)?;
            ContentNode::HeldType {
                inner,
                world: read_world(reader)?,
            }
        },
        0x98 => ContentNode::CapabilityType(read_world(reader)?),
        0x7E => {
            let kind = reader.tag()?.0;
            let slot = |reader: &mut Reader<'_>| {
                let index = reader.word()?;
                u32::try_from(index.0)
                    .map(DeBruijnIndex::from)
                    .map_err(|_overflow| CodecError::Corrupt)
            };
            ContentNode::Memory(match kind {
                0 => MemoryForm::Hold {
                    value: read_index(reader)?,
                    body: read_index(reader)?,
                    grade: HoldGrade::Many,
                },
                7 => MemoryForm::Hold {
                    value: read_index(reader)?,
                    body: read_index(reader)?,
                    grade: HoldGrade::One,
                },
                1 | 4 | 5 | 6 => {
                    let held = slot(reader)?;
                    let place = if kind >= 5 {
                        AccessPlace::At {
                            index: read_index(reader)?,
                        }
                    }
                    else {
                        AccessPlace::Whole
                    };
                    let body = read_index(reader)?;
                    let mode = if kind == 1 || kind == 5 {
                        AccessMode::Exclusive {
                            unwind: read_index(reader)?,
                        }
                    }
                    else {
                        AccessMode::Shared
                    };
                    MemoryForm::Access {
                        mode,
                        held,
                        place,
                        body,
                    }
                },
                2 => MemoryForm::Resume {
                    view: slot(reader)?,
                    value: read_index(reader)?,
                },
                3 => MemoryForm::Abort {
                    view: slot(reader)?,
                },
                8 => MemoryForm::Consume {
                    held: slot(reader)?,
                },
                _ => return Err(CodecError::Corrupt),
            })
        },
        0x62 => ContentNode::SessionRelated {
            relation: match reader.tag()?.0 {
                0 => SessionRelation::Equivalence,
                1 => SessionRelation::Subtyping,
                _ => return Err(CodecError::Corrupt),
            },
            source: read_index(reader)?,
            target: read_index(reader)?,
            payloads: read_index(reader)?,
        },
        0x63 => ContentNode::Stay(read_index(reader)?),
        0x64 => ContentNode::Then(read_index(reader)?, read_index(reader)?),
        0x69 => ContentNode::Forward(read_index(reader)?),
        0x6A => ContentNode::FunctionFlow(read_index(reader)?, read_index(reader)?),
        0x6B => ContentNode::FlowProduct(read_index(reader)?, read_index(reader)?),
        0x65 => {
            let count = reader.count()?;
            let mut moves = Vec::new();
            for _ in 0 .. count.0 {
                moves.push(read_move(reader)?);
            }
            ContentNode::Recorded(moves.into())
        },
        0x6D => {
            let count = reader.count()?;
            let mut turns = Vec::new();
            for _ in 0 .. count.0 {
                let endpoint = read_side(reader)?;
                turns.push(DialogueMove {
                    endpoint,
                    movement: read_move(reader)?,
                });
            }
            ContentNode::Dialogue(turns.into())
        },
        0x6E => {
            let count = reader.count()?;
            let mut pieces = Vec::new();
            for _ in 0 .. count.0 {
                pieces.push(read_piece(reader)?);
            }
            ContentNode::Web(pieces.into())
        },
        0x83 => ContentNode::Decompose(read_index(reader)?),
        0x66 => ContentNode::Ride {
            motive: read_index(reader)?,
            flow: read_index(reader)?,
            value: read_index(reader)?,
        },
        0x67 => ContentNode::FlowType {
            carrier: read_index(reader)?,
            source: read_index(reader)?,
            target: read_index(reader)?,
        },
        0x68 => ContentNode::RunType(read_index(reader)?),
        0x6C => ContentNode::PrefixType(read_index(reader)?),
        0x6F => ContentNode::DialogueType(read_index(reader)?),
        0x82 => ContentNode::WebType,
        0x74 => {
            let payload = read_index(reader)?;
            let signature = read_effect_signature(reader)?;
            let operation = gandr_core_term::effect::OperationName::from(
                core::str::from_utf8(reader.bytes()?.0)
                    .map_err(|_invalid_utf8| CodecError::Corrupt)?,
            );
            ContentNode::Perform {
                signature,
                operation,
                payload,
            }
        },
        0x75 | 0x7C => {
            let subject = read_index(reader)?;
            let on_return = read_index(reader)?;
            let signature = read_effect_signature(reader)?;
            let count = reader.count()?;
            let mut clauses = Vec::new();
            for _ in 0 .. count.0 {
                let operation = gandr_core_term::effect::OperationName::from(
                    core::str::from_utf8(reader.bytes()?.0)
                        .map_err(|_invalid_utf8| CodecError::Corrupt)?,
                );
                clauses.push(gandr_core_term::control::EffectClause {
                    operation,
                    body: read_index(reader)?,
                });
            }
            if tag.0 == 0x7C {
                ContentNode::Scope {
                    signature,
                    subject,
                    on_return,
                    clauses: clauses.into(),
                }
            }
            else {
                ContentNode::Handle {
                    signature,
                    subject,
                    on_return,
                    clauses: clauses.into(),
                }
            }
        },
        0x7B => {
            let capability = read_index(reader)?;
            let payload = read_index(reader)?;
            let signature = read_effect_signature(reader)?;
            let operation = gandr_core_term::effect::OperationName::from(
                core::str::from_utf8(reader.bytes()?.0)
                    .map_err(|_invalid_utf8| CodecError::Corrupt)?,
            );
            ContentNode::Exercise {
                capability,
                signature,
                operation,
                payload,
            }
        },
        0x7D => {
            use gandr_core_term::effect::capability::CapabilityGrade;
            let authority = read_effect_row(reader)?;
            let grade = match reader.tag()?.0 {
                0 => CapabilityGrade::Durable,
                1 => CapabilityGrade::Consumable,
                _ => return Err(CodecError::Corrupt),
            };
            ContentNode::Capability {
                authority,
                grade,
                region: read_region(reader)?,
            }
        },
        0x7F => {
            let value = read_index(reader)?;
            ContentNode::KeptType {
                value,
                region: read_region(reader)?,
            }
        },
        0x76 => ContentNode::Resume(read_index(reader)?, read_index(reader)?),
        0x81 => ContentNode::Abandon(read_index(reader)?),
        0x77 => ContentNode::Reset(read_index(reader)?),
        0x78 => ContentNode::Shift(read_index(reader)?),
        0x79 => ContentNode::With(read_indices(reader)?),
        0x7A => {
            let component = gandr_core_term::Component::from(reader.count()?.0);
            ContentNode::Project(component, read_index(reader)?)
        },
        0x0D | 0x16 => {
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
                    1 => Arguments::Unary(read_index(reader)?),
                    2 => Arguments::Binary([read_index(reader)?, read_index(reader)?]),
                    _ => return Err(CodecError::Corrupt),
                };
                ContentNode::Primitive(primitive, arguments)
            }
        },
        0x01 => {
            let zone = reader.tag()?;
            let zone = match zone.0 {
                0 => Zone::Intuitionistic,
                1 => Zone::Linear,
                _ => return Err(CodecError::Corrupt),
            };
            let index = reader.word()?;
            let index = u32::try_from(index.0).map_err(|_overflow| CodecError::Corrupt)?;
            ContentNode::Variable {
                zone,
                index: DeBruijnIndex::from(index),
            }
        },
        0x02 => {
            let reference = read_reference(reader)?;
            ContentNode::Constant(reference)
        },
        0x04 => {
            let literal = read_literal(reader)?;
            ContentNode::Literal(literal)
        },
        0x05 => ContentNode::Tuple(read_indices(reader)?),
        0x06 => {
            let summand = Summand::from(reader.count()?.0);
            let body = read_index(reader)?;
            ContentNode::Injection(summand, body)
        },
        0x07 => {
            let body = read_index(reader)?;
            ContentNode::Thunk(body)
        },
        0x08 => {
            let target = read_level(reader)?;
            let body = read_index(reader)?;
            ContentNode::ValueLift { target, body }
        },
        0x09 => {
            let quoted = read_index(reader)?;
            ContentNode::Quote(quoted)
        },
        0x0A => {
            let quoted = read_index(reader)?;
            ContentNode::QuoteComputation(quoted)
        },
        0x0B => {
            let body = read_index(reader)?;
            ContentNode::StaticLambda(body)
        },
        0x0C => {
            let head = read_index(reader)?;
            let argument = read_index(reader)?;
            ContentNode::StaticApplication(head, argument)
        },
        0x0E => ContentNode::Hole(read_hole(reader)?),
        0x0F => {
            let mark = read_mark(reader)?;
            let body = read_index(reader)?;
            ContentNode::ValueMark { mark, body }
        },
        0x10 => {
            let body = read_index(reader)?;
            ContentNode::Lambda(body)
        },
        0x91 => {
            let body = read_index(reader)?;
            ContentNode::LinearLambda(body)
        },
        0x11 => {
            let head = read_index(reader)?;
            let argument = read_index(reader)?;
            ContentNode::Application(head, argument)
        },
        0x12 => {
            let value = read_index(reader)?;
            ContentNode::Return(value)
        },
        0x13 => {
            let bound = read_index(reader)?;
            let rest = read_index(reader)?;
            ContentNode::Bind(bound, rest)
        },
        // One value's return and bind have their own tags: an encoding of one
        // is not canonical.
        0x8D => {
            let values = read_indices(reader)?;
            if values.len() == 1 {
                return Err(CodecError::Corrupt);
            }
            ContentNode::ReturnAll(values)
        },
        0x8E => {
            let bound = read_index(reader)?;
            let arity = gandr_core_term::ComponentCount::from(reader.count()?.0);
            if usize::from(arity) == 1 {
                return Err(CodecError::Corrupt);
            }
            ContentNode::BindAll(bound, arity, read_index(reader)?)
        },
        0x14 => {
            let value = read_index(reader)?;
            ContentNode::Force(value)
        },
        0x15 => {
            let scrutinee = read_index(reader)?;
            ContentNode::Case {
                scrutinee,
                branches: read_indices(reader)?,
            }
        },
        0x17 => ContentNode::ComputationHole(read_hole(reader)?),
        0x18 => {
            let mark = read_mark(reader)?;
            let body = read_index(reader)?;
            ContentNode::ComputationMark { mark, body }
        },
        0x19 => {
            let evidence = read_evidence(reader)?;
            let body = read_index(reader)?;
            ContentNode::Fixpoint { body, evidence }
        },
        0x1A => {
            let body = read_index(reader)?;
            ContentNode::Ascribe {
                body,
                ty: read_index(reader)?,
            }
        },
        0x1B => {
            let value = read_index(reader)?;
            ContentNode::ValueAscribe {
                value,
                ty: read_index(reader)?,
            }
        },
        0x20 => {
            let base = reader.tag()?;
            ContentNode::Base(match base.0 {
                0 => BaseType::Integer,
                1 => BaseType::String,
                2 => BaseType::Numeric,
                3 => BaseType::Character,
                8 => BaseType::Float64,
                4 => BaseType::Fixed(IntegerWidth::U32),
                5 => BaseType::Fixed(IntegerWidth::U64),
                6 => BaseType::Fixed(IntegerWidth::I32),
                7 => BaseType::Fixed(IntegerWidth::I64),
                9 => BaseType::Fixed(IntegerWidth::U8),
                10 => BaseType::Fixed(IntegerWidth::U16),
                11 => BaseType::Fixed(IntegerWidth::I8),
                12 => BaseType::Fixed(IntegerWidth::I16),
                13 => BaseType::Fixed(IntegerWidth::Usize),
                14 => BaseType::Fixed(IntegerWidth::Isize),
                _ => return Err(CodecError::Corrupt),
            })
        },
        0x22 => ContentNode::Product(read_indices(reader)?),
        0x23 => ContentNode::Sum(read_indices(reader)?),
        0x24 => {
            let body = read_index(reader)?;
            ContentNode::ThunkType(body)
        },
        0x25 => {
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Ground(GroundSort::Value),
                level,
            }
        },
        0x26 => {
            let inner = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::TypeLift { inner, target }
        },
        0x27 => {
            let code = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::Element { code, target }
        },
        0x28 => {
            let reference = read_reference(reader)?;
            ContentNode::Abstract(reference)
        },
        0x29 => {
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Ground(GroundSort::Computation),
                level,
            }
        },
        0x2A => {
            let parameter = reader.word()?;
            let parameter = u32::try_from(parameter.0).map_err(|_overflow| CodecError::Corrupt)?;
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Parameter(SortParameter::from(parameter)),
                level,
            }
        },
        0x2B => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::StaticPi { domain, codomain }
        },
        0x2D => {
            let first = read_index(reader)?;
            let second = read_index(reader)?;
            ContentNode::Sigma { first, second }
        },
        0x2C => ContentNode::UnknownType,
        0x80 => ContentNode::BufferType,
        0x93 => ContentNode::QubitType,
        0x85 => {
            let row = read_effect_row(reader)?;
            ContentNode::RowValue(row.with_tail(read_row_tail(reader)?))
        },
        0x86 => ContentNode::RowKind,
        0x87 => ContentNode::RowTail(read_index(reader)?),
        0x56 => ContentNode::List(read_index(reader)?),
        0x57 => ContentNode::ListNil,
        0x58 => ContentNode::ListCons(read_index(reader)?, read_index(reader)?),
        0x59 => ContentNode::ListFold {
            element: read_index(reader)?,
            result: read_index(reader)?,
            list: read_index(reader)?,
            on_nil: read_index(reader)?,
            on_cons: read_index(reader)?,
        },
        0x5D => ContentNode::ListCase {
            list: read_index(reader)?,
            on_nil: read_index(reader)?,
            on_cons: read_index(reader)?,
        },
        0x30 => {
            let result = read_index(reader)?;
            ContentNode::Returner {
                result,
                effects: gandr_core_term::effect::EffectRow::EMPTY,
            }
        },
        0x70 => {
            let result = read_index(reader)?;
            let effects = read_effect_row(reader)?;
            if effects.purity() == gandr_core_term::effect::Purity::Pure {
                return Err(CodecError::Corrupt);
            }
            ContentNode::Returner { result, effects }
        },
        0x88 => {
            let result = read_index(reader)?;
            let effects = read_effect_row(reader)?;
            let tail = read_index(reader)?;
            ContentNode::Returner {
                result,
                effects: effects.with_tail(Some(tail)),
            }
        },
        0x8C => {
            let results = read_indices(reader)?;
            if results.len() == 1 {
                return Err(CodecError::Corrupt);
            }
            let effects = read_effect_row(reader)?;
            ContentNode::Returns {
                results,
                effects: effects.with_tail(read_row_tail(reader)?),
            }
        },
        0x31 => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::Arrow { domain, codomain }
        },
        0x32 => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::Pi { domain, codomain }
        },
        0x92 => {
            let domain = read_index(reader)?;
            let multiplicity = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::LinearArrow {
                domain,
                multiplicity,
                codomain,
            }
        },
        0x33 => {
            let code = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::ComputationElement { code, target }
        },
        0x34 => ContentNode::UnknownComputationType,
        0x40 => ContentNode::PathUniverse(read_index(reader)?, read_index(reader)?),
        0x41 => ContentNode::PathRefl(read_index(reader)?),
        0x42 => {
            let path_type = read_index(reader)?;
            let forward = read_index(reader)?;
            let backward = read_index(reader)?;
            let mut evidence = gandr_kernel_term::PathEvidence::default();
            for direction in [&mut evidence.source, &mut evidence.target] {
                let count = reader.word()?;
                for _ in 0 .. count.0 {
                    let count = reader.word()?;
                    let mut dialogue = gandr_kernel_data::SmallVec::new();
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
                evidence: gandr_kernel_data::Shared::new(evidence),
            }
        },
        0x43 => ContentNode::PathProduct(read_index(reader)?, read_index(reader)?),
        0x44 => ContentNode::Transport(read_index(reader)?, read_index(reader)?),
        0x45 => ContentNode::PathType {
            carrier: read_index(reader)?,
            left: read_index(reader)?,
            right: read_index(reader)?,
        },
        0x89 => ContentNode::BridgeType {
            carrier: read_index(reader)?,
            left: read_index(reader)?,
            right: read_index(reader)?,
        },
        0x46 => ContentNode::Here(read_index(reader)?),
        0x47 => ContentNode::ElementTransport {
            motive: read_index(reader)?,
            path: read_index(reader)?,
            value: read_index(reader)?,
        },
        0x48 => ContentNode::Returned(read_index(reader)?),
        0x4D => ContentNode::Nested(read_index(reader)?),
        0x4E => ContentNode::Run(read_index(reader)?),
        0x84 => ContentNode::RecordUpdate(read_index(reader)?, read_index(reader)?),
        0x49 => ContentNode::Funext(read_index(reader)?, read_index(reader)?),
        0x4A => ContentNode::Equiv(read_index(reader)?, read_index(reader)?),
        0x4F => ContentNode::Univalence(read_index(reader)?, read_index(reader)?),
        0x4B => ContentNode::TelescopeTransport {
            motive: read_index(reader)?,
            path: read_index(reader)?,
            start: read_index(reader)?,
            over: read_index(reader)?,
            value: read_index(reader)?,
        },
        0x4C => {
            let stratum = gandr_core_term::ua::Stratum {
                degree: gandr_theory_sites::Degree::from(reader.count()?.0),
                bound: gandr_theory_sites::ShapeSize::from(reader.count()?.0),
            };
            let source = read_description(reader)?;
            let target = read_description(reader)?;
            ContentNode::Ua {
                stratum,
                sides: alloc::sync::Arc::new(gandr_core_term::ua::Sides { source, target }),
                forward: read_index(reader)?,
                backward: read_index(reader)?,
            }
        },
        0x8A => {
            let stratum = gandr_core_term::ua::Stratum {
                degree: gandr_theory_sites::Degree::from(reader.count()?.0),
                bound: gandr_theory_sites::ShapeSize::from(reader.count()?.0),
            };
            let pasting = read_pasting(reader)?;
            ContentNode::Compose {
                composite: gandr_core_term::compose::Composite { stratum, pasting },
                realised: read_index(reader)?,
                cells: read_indices(reader)?,
            }
        },
        0x8B => {
            let stratum = gandr_core_term::ua::Stratum {
                degree: gandr_theory_sites::Degree::from(reader.count()?.0),
                bound: gandr_theory_sites::ShapeSize::from(reader.count()?.0),
            };
            ContentNode::Fill {
                composite: gandr_core_term::compose::Composite {
                    stratum,
                    pasting: read_pasting(reader)?,
                },
                generator: read_index(reader)?,
                cells: read_indices(reader)?,
            }
        },
        _ => return Err(CodecError::Corrupt),
    };
    Ok(node)
}

/// Read a hole's name, a word that must fit a `u32`.
///
/// # Specification
/// - ensures: the name the word carries.
/// - fails: [`CodecError::Corrupt`] for a word past the `u32` ceiling; the
///   reader's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CodecError`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a value hole and a computation hole round-trip through a
///   table.
/// - witness: `gandr-core-incremental::codec::tests::holes_marks_and_the_unknown_types_round_trip`
#[spec(ensures: |ret| match ret {
    | Ok(_) => true,
    | Err(error) => matches!(error, CodecError::Corrupt | CodecError::NonCanonical),
})]
fn read_hole(reader: &mut Reader<'_>) -> Result<HoleId, CodecError>
{
    let word = reader.word()?;
    u32::try_from(word.0)
        .map(HoleId::from)
        .map_err(|_overflow| CodecError::Corrupt)
}

/// Read a mark's index, a word that must fit a `u32`.
///
/// # Specification
/// - ensures: the index the word carries.
/// - fails: [`CodecError::Corrupt`] for a word past the `u32` ceiling; the
///   reader's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CodecError`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a value mark and a computation mark round-trip through a
///   table.
/// - witness: `gandr-core-incremental::codec::tests::holes_marks_and_the_unknown_types_round_trip`
#[spec(ensures: |ret| match ret {
    | Ok(_) => true,
    | Err(error) => matches!(error, CodecError::Corrupt | CodecError::NonCanonical),
})]
fn read_mark(reader: &mut Reader<'_>) -> Result<MarkIndex, CodecError>
{
    let word = reader.word()?;
    u32::try_from(word.0)
        .map(MarkIndex::from)
        .map_err(|_overflow| CodecError::Corrupt)
}

/// Write a supported table.
///
/// The table is its count, each node's former and scope, then every node's
/// edges in node and child order. A cover holds one edge per child of its
/// former, and an edge is as wide as its child's scope. So neither a cover's
/// arity nor an edge's widths is written.
///
/// # Specification
/// - ensures: successful tables contain no unresolved node; an unsupported
///   refusal names the first one. A sink that stores refuses a codata
///   application, which a table then holds. The references each node carries
///   are not written: a reader rebuilds them.
///
/// # Adequacy
/// - hypothesis: L3 — nested unresolved nodes in all four sorts retain the
///   precise refusal; a written table reads back equal. Structural validation
///   is a reader responsibility.
/// - witness: `gandr-core-incremental::persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
/// - witness: `gandr-core-incremental::codec::tests::supported_tables_round_trip_and_reject_forged_support`
/// - witness: `gandr-core-incremental::codec::tests::a_stored_form_refuses_a_codata_application_7403`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[spec(
    ensures: |ret| match ret {
        | Ok(()) => nodes
            .iter()
            .all(|node| !matches!(*node.former(), ContentNode::Unresolved(_))),
        | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
            nodes.iter().find_map(|node| match *node.former() {
                | ContentNode::Unresolved(found) => Some(found),
                | _ => None,
            }) == Some(sort)
        },
        | Err(CodecError::Unsupported(UnsupportedPersistence::Codata)) => {
            Out::CODATA == CodataWrite::Refused
                && nodes.iter().any(|node| matches!(*node.former(), ContentNode::Codata { .. }))
        },
        | Err(CodecError::Unrepresentable) => true,
        | _ => false,
    },
)]
#[inline]
pub fn write_nodes<Out>(
    writer: &mut Writer<'_, Out>,
    nodes: &[SupportedNode],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(nodes.len()))?;
    for node in nodes {
        write_node(writer, node.former())?;
        write_scope(writer, node.scope())?;
    }
    for node in nodes {
        for edge in node.cover() {
            write_selection(writer, edge);
        }
    }
    Ok(())
}

/// Write a selection's indices, the intuitionistic zone's and then the
/// linear zone's; its widths are the scope the reader already holds.
///
/// # Specification
/// - ensures: one word per selected index, intuitionistic first.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — a table with covers in both zones round-trips.
/// - witness: `gandr-core-incremental::codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[inline]
pub fn write_selection<Out>(
    writer: &mut Writer<'_, Out>,
    thinning: &Thinning,
) where
    Out: Sink,
{
    for zone in [Zone::Intuitionistic, Zone::Linear] {
        for index in thinning.indices(zone) {
            writer.word(Word(u64::from(u32::from(index))));
        }
    }
}

/// Read a selection of `scope`'s widths.
///
/// # Specification
/// - ensures: as many indices per zone as `scope` is wide there, as written.
/// - fails: [`CodecError::Corrupt`] for an index past `u32`, a zone whose
///   indices do not strictly ascend, or input that ends first.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a descending forged root support is refused.
/// - witness: `gandr-core-incremental::codec::tests::supported_tables_round_trip_and_reject_forged_support`
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
///
/// # Cost
/// - allocation: the selected indices, growth within the bytes
#[spec(ensures: |ret| match ret {
    Ok(ref selected) => selected.scope() == scope,
    Err(error) => error == CodecError::Corrupt,
})]
#[inline]
pub fn read_selection(
    reader: &mut Reader<'_>,
    scope: Scope,
) -> Result<Thinning, CodecError>
{
    let mut zones: [Vec<DeBruijnIndex>; 2] = [Vec::new(), Vec::new()];
    for (zone, selected) in [Zone::Intuitionistic, Zone::Linear]
        .into_iter()
        .zip(&mut zones)
    {
        for _ in 0 .. usize::from(scope.width(zone)) {
            let word = reader.word()?;
            let index = u32::try_from(word.0).map_err(|_overflow| CodecError::Corrupt)?;
            selected.push(DeBruijnIndex::from(index));
        }
    }
    let [ref intuitionistic, ref linear] = zones;
    Thinning::from_ascending(intuitionistic, linear).map_err(|_unordered| CodecError::Corrupt)
}

/// Write a scope's two widths as one word: the intuitionistic width in its
/// low half, the linear width in its high half.
///
/// # Specification
/// - ensures: one word.
/// - fails: [`CodecError::Unrepresentable`] for a width past `u32`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a table with scopes in both zones round-trips.
/// - witness: `gandr-core-incremental::codec::tests::supported_tables_round_trip_and_reject_forged_support`
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[spec(ensures: |ret| ret.is_ok() == [Zone::Intuitionistic, Zone::Linear].into_iter()
    .all(|zone| u32::try_from(usize::from(scope.width(zone))).is_ok()))]
#[inline]
pub fn write_scope<Out>(
    writer: &mut Writer<'_, Out>,
    scope: Scope,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let half = |zone: Zone| {
        u32::try_from(usize::from(scope.width(zone)))
            .map(u32::to_le_bytes)
            .map_err(|_overflow| CodecError::Unrepresentable)
    };
    let [i0, i1, i2, i3] = half(Zone::Intuitionistic)?;
    let [l0, l1, l2, l3] = half(Zone::Linear)?;
    writer.word(Word(u64::from_le_bytes([i0, i1, i2, i3, l0, l1, l2, l3])));
    Ok(())
}

/// Read a scope's two widths from one word.
///
/// # Specification
/// - ensures: the low half as the intuitionistic width, the high half as the
///   linear width.
/// - fails: [`CodecError::Corrupt`] for input that ends first.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a table with scopes in both zones round-trips.
/// - witness: `gandr-core-incremental::codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[spec(captures: [before = reader.cursor], ensures: |ret| ret.is_err() || reader.cursor == before.saturating_add(8))]
fn read_scope(reader: &mut Reader<'_>) -> Result<Scope, CodecError>
{
    let [i0, i1, i2, i3, l0, l1, l2, l3] = reader.word()?.0.to_le_bytes();
    let width = |half: [u8; 4]| {
        usize::try_from(u32::from_le_bytes(half))
            .map(BinderDepth::from)
            .map_err(|_overflow| CodecError::Corrupt)
    };
    Ok(Scope::new(
        width([i0, i1, i2, i3])?,
        width([l0, l1, l2, l3])?,
    ))
}

/// Read a supported table and rebuild it.
///
/// The reader takes every node's former and scope, then each edge as wide as
/// its child's scope. It checks every child in range and of its required
/// sort, the table acyclic, every cover the exact minimal cover of its node,
/// and no node twice. It recomputes every node's references.
///
/// # Specification
/// - requires: nothing.
/// - ensures: successful nodes are resolved, every child index names its
///   required sort, and each node carries the references beneath it. Discovery
///   order and reachability are checked by the caller.
/// - fails: [`CodecError::Corrupt`] for malformed nodes, invalid children, a
///   cycle or a forged cover; [`CodecError::NonCanonical`] for a node listed
///   twice; [`CodecError::LevelOffsetTooLarge`] for an offset at the decoder
///   cap.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — out-of-range and wrong-sort children are refused
///   independently of root validation; widened scopes, edges past their scope,
///   unused slots, duplicates and cycles are refused.
/// - witness: `gandr-core-incremental::codec::tests::type_tables_validate_roots_child_extents_and_sorts`
/// - witness: `gandr-core-incremental::codec::tests::supported_tables_round_trip_and_reject_forged_support`
/// - witness: `gandr-core-incremental::persistence::tests::oversized_level_offset_is_refused_with_exact_error`
///
/// # Cost
/// - allocation: the nodes and their lists of children, growth within the
///   stored table
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[spec(
    ensures: |ret| match ret {
        | Ok(ref nodes) => {
            nodes.iter().all(|node| {
                !matches!(*node.former(), ContentNode::Unresolved(_))
                    && node.former().children().iter().all(|(child, sort)| {
                        nodes
                            .get(usize::from(child))
                            .is_some_and(|found| found.sort() == sort)
                    })
            })
        },
        | Err(CodecError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= MAX_DECODED_LEVEL_OFFSET
        },
        | Err(error) => matches!(error,CodecError::Corrupt | CodecError::NonCanonical),
    },
)]
#[inline]
pub fn read_nodes(reader: &mut Reader<'_>) -> Result<Vec<SupportedNode>, CodecError>
{
    let count = reader.count()?;
    let mut formers = Vec::new();
    let mut scopes = Vec::new();
    for _ in 0 .. count.0 {
        formers.push(read_node(reader)?);
        scopes.push(read_scope(reader)?);
    }
    let mut parts = Vec::with_capacity(formers.len());
    for (former, &scope) in formers.into_iter().zip(&scopes) {
        let children = former.children();
        let mut cover = Vec::with_capacity(children.iter().count());
        for (child, _) in children.iter() {
            let width = *scopes.get(usize::from(child)).ok_or(CodecError::Corrupt)?;
            cover.push(read_selection(reader, width)?);
        }
        parts.push(crate::NodeParts {
            former,
            cover,
            scope,
        });
    }
    crate::assemble(parts).map_err(|fault| match fault {
        crate::TableFault::Duplicate => CodecError::NonCanonical,
        crate::TableFault::Child | crate::TableFault::Cycle | crate::TableFault::Cover(_) => {
            CodecError::Corrupt
        },
    })
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
/// - hypothesis: L3 — swapped and unreachable entries and a table numbered from
///   another root are refused; empty tables and repeated roots are accepted.
///   The predicate uses a scalar contiguous-frontier oracle, not a second
///   allocated queue or visited set.
/// - witness: `gandr-core-incremental::persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `gandr-core-incremental::codec::tests::discovery_accepts_repeated_roots_and_empty_tables`
///
/// # Cost
/// - allocation: the discovery numbers of the walk, growth within the table
#[spec(
    requires: nodes.iter().all(|node| {
        node.former().children()
            .iter()
            .all(|(child, _)| usize::from(child) < nodes.len())
    }),
    captures:[root_frontier=roots.clone().try_fold(0_usize, |next, root| {
        let index = usize::from(root);
        if index >= nodes.len() {
            Err(CodecError::Corrupt)
        }
        else if index > next {
            Err(CodecError::NonCanonical)
        }
        else if index == next {
            Ok(next.saturating_add(1))
        }
        else {
            Ok(next)
        }
    })],
    ensures: |ret| {
        ret == 'discovery: {
            let mut next = match root_frontier {
                Ok(next) => next,
                Err(error) => break 'discovery Err(error),
            };
            for (index, node) in nodes.iter().enumerate() {
                if index >= next {
                    break 'discovery Err(CodecError::NonCanonical);
                }
                for (child, _) in node.former().children().iter() {
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
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[inline]
pub fn check_discovery<Roots>(
    nodes: &[SupportedNode],
    roots: Roots,
) -> Result<(), CodecError>
where
    Roots: Iterator<Item = NodeIndex> + Clone,
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
    for root in roots {
        discover(root, &mut queue)?;
    }
    while let Some(index) = queue.pop_front() {
        let node = nodes.get(usize::from(index)).ok_or(CodecError::Corrupt)?;
        for (child, _) in node.former().children().iter() {
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

/// Write the content of one node: its table, then its root's support.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_node_content<Out>(
    sink: &mut Out,
    content: &TypeContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let mut writer = Writer { sink };
    write_type(&mut writer, content)
}

/// Write a type's content.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A [`CodecError`] for a value that has no byte form, or a sink that refuses.
#[inline]
pub fn write_type<Out>(
    writer: &mut Writer<'_, Out>,
    content: &TypeContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_nodes(writer, content.nodes())?;
    write_selection(writer, content.root());
    Ok(())
}

/// Read a type's content.
///
/// # Specification
/// - fails: as [`read_nodes`] and [`check_discovery`], and
///   [`CodecError::Corrupt`] for an empty table, a root that is no type or a
///   root support of other widths than the root's.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, non-type, out-of-range and wrong-sort tables are
///   refused; a computation-type root is accepted. The predicate checks closed
///   children and canonical discovery from root zero, without re-encoding or
///   allocating another traversal state.
/// - witness: `gandr-core-incremental::codec::tests::type_tables_validate_roots_child_extents_and_sorts`
/// - witness: `gandr-core-incremental::codec::tests::supported_tables_round_trip_and_reject_forged_support`
/// - witness: `gandr-core-incremental::persistence::tests::universe_sorts_and_levels_round_trip`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref content) => {
            let nodes = content.nodes();
            matches!(
                nodes.first().map(SupportedNode::sort),
                Some(Sort::ValueType | Sort::CompType)
            ) && nodes.iter().all(|node| {
                !matches!(*node.former(), ContentNode::Unresolved(_))
                    && node.former().children().iter().all(|(child, sort)| {
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
                    for (child, _) in node.former().children().iter() {
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
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
#[inline]
pub fn read_type(reader: &mut Reader<'_>) -> Result<TypeContent, CodecError>
{
    let nodes = read_nodes(reader)?;
    match nodes.first().map(SupportedNode::sort) {
        Some(Sort::ValueType | Sort::CompType) => {},
        Some(Sort::Value | Sort::Computation) | None => return Err(CodecError::Corrupt),
    }
    let root = NodeIndex::from(0_usize);
    check_discovery(&nodes, core::iter::once(root))?;
    let scope = nodes
        .first()
        .map(SupportedNode::scope)
        .ok_or(CodecError::Corrupt)?;
    let placement = read_selection(reader, scope)?;
    Ok(TypeContent::from_parts(nodes, placement))
}

/// Write a fixpoint's termination evidence: a tag in stable wire order, a
/// staged claim's position after it as a word, and a joint claim's count and
/// each component's position after it as words.
///
/// # Specification
/// - ensures: `Partial` writes tag 0, `StructuralDescent` tag 1, `Staged` tag 2
///   then its position, `Joint` tag 3 then its count and positions, and
///   `Guarded` tag 4.
/// - fails: [`CodecError::Unrepresentable`] for a position past 64 bits.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — each evidence round-trips, the staged one with its
///   position and the joint one with its positions in order.
/// - witness: `gandr-core-incremental::codec::tests::fixpoint_evidence_round_trips_with_its_staged_position`
#[spec(ensures: |ret| ret.is_ok() || ret == Err(CodecError::Unrepresentable))]
#[inline]
pub fn write_evidence<Out>(
    writer: &mut Writer<'_, Out>,
    evidence: FixpointEvidence,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match evidence {
        FixpointEvidence::Partial => writer.tag(Tag(0)),
        FixpointEvidence::StructuralDescent => writer.tag(Tag(1)),
        FixpointEvidence::Guarded => writer.tag(Tag(4)),
        FixpointEvidence::Staged { position } => {
            let position = u64::try_from(usize::from(position))
                .map_err(|_wide| CodecError::Unrepresentable)?;
            writer.tag(Tag(2));
            writer.word(Word(position));
        },
        FixpointEvidence::Joint { positions } => {
            writer.tag(Tag(3));
            writer.word(Word(
                u64::try_from(positions.iter().count())
                    .map_err(|_wide| CodecError::Unrepresentable)?,
            ));
            for position in positions.iter() {
                writer.word(Word(
                    u64::try_from(usize::from(position))
                        .map_err(|_wide| CodecError::Unrepresentable)?,
                ));
            }
        },
    }
    Ok(())
}

/// Read a fixpoint's termination evidence as [`write_evidence`] writes it.
///
/// # Specification
/// - ensures: tags 0 and 1 read the partial and structural evidence, tag 2 a
///   staged claim at the position after it, tag 3 a joint claim at the count
///   and positions after it, and tag 4 the guarded evidence.
/// - fails: [`CodecError::Corrupt`] for another tag, a short input, a position
///   past the platform's width, or a joint claim past its width.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_evidence`], and a tag past 4 is corrupt.
/// - witness: `gandr-core-incremental::codec::tests::fixpoint_evidence_round_trips_with_its_staged_position`
#[spec(captures: before = reader.cursor, ensures: |ret| ret.is_err() || reader.cursor > before)]
#[inline]
pub fn read_evidence(reader: &mut Reader<'_>) -> Result<FixpointEvidence, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        0 => Ok(FixpointEvidence::Partial),
        1 => Ok(FixpointEvidence::StructuralDescent),
        2 => {
            let word = reader.word()?;
            let position = usize::try_from(word.0).map_err(|_wide| CodecError::Corrupt)?;
            Ok(FixpointEvidence::Staged {
                position: StagedPosition::from(position),
            })
        },
        3 => {
            let count = usize::try_from(reader.word()?.0).map_err(|_wide| CodecError::Corrupt)?;
            if count > JointPositions::CAPACITY {
                return Err(CodecError::Corrupt);
            }
            let mut positions = [StagedPosition::default(); JointPositions::CAPACITY];
            for slot in positions.iter_mut().take(count) {
                let word = reader.word()?;
                *slot = StagedPosition::from(
                    usize::try_from(word.0).map_err(|_wide| CodecError::Corrupt)?,
                );
            }
            let positions = positions.get(.. count).ok_or(CodecError::Corrupt)?;
            JointPositions::new(positions)
                .map(|positions| FixpointEvidence::Joint { positions })
                .ok_or(CodecError::Corrupt)
        },
        4 => Ok(FixpointEvidence::Guarded),
        _ => Err(CodecError::Corrupt),
    }
}

/// A borrowed run of bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bytes<'data>(pub &'data [u8]);

/// Whether a sink takes a codata application.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodataWrite
{
    /// The sink stores what it takes, and refuses a codata application.
    Refused,
    /// The sink keys content and stores nothing.
    Keyed,
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
/// - witness: `gandr-core-incremental::persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
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
        Sign::Negative => Tag(0),
        Sign::NonNegative => Tag(1),
    }
}

/// Read a place in the table `nodes`: a node of it and its support, read
/// against the node's scope.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for a node past the table, and as
///   [`read_selection`].
/// - panics: none.
/// - executable: none — the witness reads the bytes back.
///
/// # Adequacy
/// - hypothesis: L3 — a report and a command image read back the places that
///   they wrote.
/// - witness: `gandr-core-incremental::report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
///
/// # Errors
/// A [`CodecError`] for bytes that the writer does not give.
///
/// # Cost
/// - allocation: the decoded table place, growth within the bytes
#[inline]
pub fn read_table_place(
    reader: &mut Reader<'_>,
    nodes: &[SupportedNode],
) -> Result<TablePlace, CodecError>
{
    let node = read_index(reader)?;
    let scope = nodes
        .get(usize::from(node))
        .map(SupportedNode::scope)
        .ok_or(CodecError::Corrupt)?;
    let support = read_selection(reader, scope)?;
    Ok(TablePlace { node, support })
}
