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
//! is also checked to be numbered by discovery from its roots, acyclic,
//! listing no node twice and every cover the exact minimal cover of its node,
//! none of which writing it again would reveal. A cover's arity is its
//! former's and an edge's widths, like a root support's, are the scope of the
//! node it selects for, so none of them is written: a table is its formers
//! and scopes, then every edge's indices. The references each node carries
//! are not written but rebuilt from the checked table. Counts read from the
//! input never size an allocation: a corrupted count fails at the end of the
//! input instead.
//!
//! # One canonical encoding
//!
//! A checkpoint set encodes to one byte string: magic, allowance, then each
//! item’s content, footprint, support and typing, with sets ascending and
//! tables in discovery order. Content producers establish the table invariants;
//! the decoder checks them. Before framing, a borrowed pass refuses any level
//! atom whose offset reaches 4,096, in the content, support or typing. The
//! decoder enforces the same bound because it reconstructs each offset with
//! that many successors. It also refuses truncated, malformed and trailing
//! bytes, and any payload that parses but is not the canonical spelling of its
//! value. After the level check, encoding names the sort of its first
//! unresolved id (`UnsupportedPersistence::Dangling`); opaque content has no
//! spelling.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::fmt;

use anodized::spec;
use gandr_core_checker::ArgumentPosition;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::RunFault;
use gandr_core_checker::RunStep;
use gandr_core_checker::StaticArity;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::body;
use gandr_core_checker::codata::CodataFault;
use gandr_core_checker::session::Capture;
use gandr_core_checker::session::ForkSide;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_checker::signature;
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
use gandr_core_term::session::ActionKind;
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
use gandr_core_term::support::Scope;
use gandr_core_term::support::Thinning;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelOffset;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::ParameterPosition;
use gandr_kernel_term::Sign;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageDepth;
use gandr_kernel_term::StageId;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::Standing;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
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
use crate::support::SupportedNode;
use crate::typing::EndpointSite;
use crate::typing::Form;
use crate::typing::Linearity;
use crate::typing::Located;
use crate::typing::Place;
use crate::typing::Refusal;
use crate::typing::Site;
use crate::typing::Typing;

/// The magic and version a persisted checkpoint set opens with.
const CHECKPOINTS_MAGIC: &[u8; 8] = b"GCKPT\0\0\x0d";

/// The magic and version a program's address is computed over.
const PROGRAM_MAGIC: &[u8; 8] = b"GPROG\0\0\x09";

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
    /// An item of a program that declares a world, or that states an entry:
    /// its judgement read homes no footprint records.
    Located,
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
            Self::Dangling(sort) => {
                let sort = match sort {
                    Sort::Value => "value",
                    Sort::Computation => "computation",
                    Sort::ValueType => "value type",
                    Sort::CompType => "computation type",
                };
                write!(f, "an unresolved {sort} id is process-local")
            },
            Self::Located => {
                f.write_str("a located program's judgements read homes no record keeps")
            },
            Self::Codata => f.write_str("a codata signature has no content form"),
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
        Sign::Negative => Tag(0),
        Sign::NonNegative => Tag(1),
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
        0 => Ok(Sign::Negative),
        1 => Ok(Sign::NonNegative),
        _ => Err(CodecError::Corrupt),
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
        _ => Err(CodecError::Corrupt),
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
        ContentNode::Data {
            ref declaration,
            ref arguments,
        } => {
            writer.tag(Tag(0x50));
            write_reference(writer, declaration)?;
            write_indices(writer, arguments)?;
        },
        ContentNode::RecordType(ref fields) => {
            writer.tag(Tag(0x51));
            write_fields(writer, fields)?;
        },
        ContentNode::Constructor {
            datatype,
            tag,
            ref fields,
        } => {
            writer.tag(Tag(0x52));
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
        } => {
            writer.tag(Tag(0x54));
            write_index(writer, scrutinee)?;
            write_index(writer, motive)?;
            write_indices(writer, branches)?;
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
            }
        },
        ContentNode::SessionRelated {
            relation,
            source,
            target,
        } => {
            writer.tag(Tag(0x62));
            writer.tag(Tag(match relation {
                SessionRelation::Equivalence => 0,
                SessionRelation::Subtyping => 1,
            }));
            write_index(writer, source)?;
            write_index(writer, target)?;
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
            }
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
            match region {
                gandr_core_term::effect::capability::Region::Held => writer.tag(Tag(0)),
                gandr_core_term::effect::capability::Region::Scoped(depth) => {
                    writer.tag(Tag(1));
                    writer.word(Word(u64::from(u32::from(depth))));
                },
            }
        },
        ContentNode::KeptType { value, region } => {
            writer.tag(Tag(0x7F));
            write_index(writer, value)?;
            writer.word(Word(u64::from(u32::from(region))));
        },
        ContentNode::Resume(stack, body) => {
            writer.tag(Tag(0x76));
            write_index(writer, stack)?;
            write_index(writer, body)?;
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
        ContentNode::Base(base) => {
            writer.tag(Tag(0x20));
            writer.tag(match base {
                BaseType::Integer => Tag(0),
                BaseType::String => Tag(1),
                BaseType::Numeric => Tag(2),
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
        ContentNode::Returner {
            result,
            ref effects,
        } => {
            if effects.purity() == gandr_core_term::effect::Purity::Pure {
                writer.tag(Tag(0x30));
                write_index(writer, result)?;
            }
            else {
                writer.tag(Tag(0x70));
                write_index(writer, result)?;
                write_effect_row(writer, effects)?;
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
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
fn write_indices<Out>(
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
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.as_ref().map_or(true,|indices| reader.cursor == before.saturating_add(8).saturating_add(indices.len().saturating_mul(8))))]
fn read_indices(reader: &mut Reader<'_>) -> Result<Vec<NodeIndex>, CodecError>
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
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
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
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
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
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
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
/// - witness: `codec::tests::session_nodes_persist_their_protocol_and_children`
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
/// - witness: `codec::tests::session_nodes_persist_their_protocol_and_children`
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
/// - witness: `codec::tests::session_nodes_persist_their_protocol_and_children`
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
/// - witness: `codec::tests::session_nodes_persist_their_protocol_and_children`
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
/// - witness: `codec::tests::session_nodes_persist_their_protocol_and_children`
fn write_session_action<Out>(
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
/// - witness: `codec::tests::session_nodes_persist_their_protocol_and_children`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_session_action(
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
/// - witness: `tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
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
/// - witness: `tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
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

/// Write why a univalence statement's stratum is not certified.
///
/// # Specification
/// - ensures: a tag naming the defect, then the degree or the bound it carries.
/// - fails: an unrepresentable count.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — each defect of the stratum survives persistence under its
///   own name.
/// - witness: `tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
fn write_stratum_defect<Out>(
    writer: &mut Writer<'_, Out>,
    defect: gandr_core_checker::ua::StratumDefect,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match defect {
        gandr_core_checker::ua::StratumDefect::Degree { degree } => {
            writer.tag(Tag(0));
            writer.count(Count(usize::from(degree)))
        },
        gandr_core_checker::ua::StratumDefect::Condition { degree } => {
            writer.tag(Tag(1));
            writer.count(Count(usize::from(degree)))
        },
        gandr_core_checker::ua::StratumDefect::Allowance { bound } => {
            writer.tag(Tag(2));
            writer.count(Count(usize::from(bound)))
        },
    }
}

/// Read a stratum defect [`write_stratum_defect`] wrote.
///
/// # Specification
/// - ensures: the defect the tag names, with its count.
/// - fails: an unknown tag or a truncated frame.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each defect of the stratum survives persistence under its
///   own name.
/// - witness: `tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
/// - witness: `codec::tests::every_refusal_round_trips_under_its_own_encoding`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_stratum_defect(
    reader: &mut Reader<'_>
) -> Result<gandr_core_checker::ua::StratumDefect, CodecError>
{
    match reader.tag()?.0 {
        0 => Ok(gandr_core_checker::ua::StratumDefect::Degree {
            degree: gandr_theory_sites::Degree::from(reader.count()?.0),
        }),
        1 => Ok(gandr_core_checker::ua::StratumDefect::Condition {
            degree: gandr_theory_sites::Degree::from(reader.count()?.0),
        }),
        2 => Ok(gandr_core_checker::ua::StratumDefect::Allowance {
            bound: gandr_theory_sites::ShapeSize::from(reader.count()?.0),
        }),
        _ => Err(CodecError::Corrupt),
    }
}

/// Write why a univalence statement's translators are no equivalence.
///
/// # Specification
/// - ensures: a tag naming the defect, then the way, profile, corolla and
///   element it carries.
/// - fails: an unrepresentable count.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — each defect of the translators survives persistence under
///   its own name.
/// - witness: `tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
fn write_ua_defect<Out>(
    writer: &mut Writer<'_, Out>,
    defect: gandr_core_checker::ua::UaDefect,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    use gandr_core_checker::ua::UaDefect;
    use gandr_core_checker::ua::Way;
    let (tag, counts): (u8, &[usize]) = match defect {
        UaDefect::UnknownGenerator { way: Way::Forward } => (0, &[0]),
        UaDefect::UnknownGenerator { way: Way::Backward } => (0, &[1]),
        UaDefect::PastTheBound { profile } => (1, &[
            usize::from(profile.inputs),
            usize::from(profile.outputs),
        ]),
        UaDefect::Cardinality { corolla } => (2, &[usize::from(corolla)]),
        UaDefect::Tables { corolla } => (3, &[usize::from(corolla)]),
        UaDefect::NotInverse { corolla, element } => {
            (4, &[usize::from(corolla), usize::from(element)])
        },
        UaDefect::NotNatural { corolla, element } => {
            (5, &[usize::from(corolla), usize::from(element)])
        },
        UaDefect::Stuck { corolla, element } => (6, &[usize::from(corolla), usize::from(element)]),
    };
    writer.tag(Tag(tag));
    for &count in counts {
        writer.count(Count(count))?;
    }
    Ok(())
}

/// Read a translator defect [`write_ua_defect`] wrote.
///
/// # Specification
/// - ensures: the defect the tag names, with its counts.
/// - fails: an unknown tag or way, or a truncated frame.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each defect of the translators survives persistence under
///   its own name.
/// - witness: `tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
/// - witness: `codec::tests::every_refusal_round_trips_under_its_own_encoding`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_ua_defect(reader: &mut Reader<'_>) -> Result<gandr_core_checker::ua::UaDefect, CodecError>
{
    use gandr_core_checker::ua::UaDefect;
    use gandr_core_checker::ua::Way;
    use gandr_theory_sites::ElementIndex;
    use gandr_theory_sites::ShapeIndex;
    let tag = reader.tag()?.0;
    let mut count = || reader.count().map(|count| count.0);
    Ok(match tag {
        0 => UaDefect::UnknownGenerator {
            way: match count()? {
                0 => Way::Forward,
                1 => Way::Backward,
                _ => return Err(CodecError::Corrupt),
            },
        },
        1 => UaDefect::PastTheBound {
            profile: gandr_theory_sites::Profile {
                inputs: gandr_theory_sites::PortCount::from(count()?),
                outputs: gandr_theory_sites::PortCount::from(count()?),
            },
        },
        2 => UaDefect::Cardinality {
            corolla: ShapeIndex::from(count()?),
        },
        3 => UaDefect::Tables {
            corolla: ShapeIndex::from(count()?),
        },
        4 => UaDefect::NotInverse {
            corolla: ShapeIndex::from(count()?),
            element: ElementIndex::from(count()?),
        },
        5 => UaDefect::NotNatural {
            corolla: ShapeIndex::from(count()?),
            element: ElementIndex::from(count()?),
        },
        6 => UaDefect::Stuck {
            corolla: ShapeIndex::from(count()?),
            element: ElementIndex::from(count()?),
        },
        _ => return Err(CodecError::Corrupt),
    })
}

/// Write an endpoint: its fork's site, then its side.
///
/// # Specification
/// - ensures: the site and the side's wire tag follow in order.
/// - fails: an unrepresentable site.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — a residue and an arm disagreement round-trip with their
///   endpoints.
/// - witness: `codec::tests::session_refusals_round_trip_with_their_endpoints`
fn write_endpoint<Out>(
    writer: &mut Writer<'_, Out>,
    endpoint: EndpointSite,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_site(writer, endpoint.fork)?;
    write_listed(writer, &SIDES, &endpoint.side)
}

/// Read an endpoint written by [`write_endpoint`].
///
/// # Specification
/// - ensures: the written fork site and side.
/// - fails: malformed bytes or an unknown side.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a residue and an arm disagreement round-trip with their
///   endpoints.
/// - witness: `codec::tests::session_refusals_round_trip_with_their_endpoints`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_endpoint(reader: &mut Reader<'_>) -> Result<EndpointSite, CodecError>
{
    Ok(EndpointSite {
        fork: read_site(reader)?,
        side: read_listed(reader, &SIDES)?,
    })
}

/// Write how an endpoint escaped its one linear use: the kind's tag, then its
/// endpoint, state, capture, arms or index.
///
/// # Specification
/// - ensures: the tag, then the defect's payloads in declaration order.
/// - fails: an unrepresentable site or type table.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — every defect kind round-trips with its payload.
/// - witness: `codec::tests::session_refusals_round_trip_with_their_endpoints`
fn write_linearity<Out>(
    writer: &mut Writer<'_, Out>,
    defect: &Linearity,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *defect {
        Linearity::Residue {
            endpoint,
            ref state,
        } => {
            writer.tag(Tag(0));
            write_endpoint(writer, endpoint)?;
            write_type(writer, state)?;
        },
        Linearity::Closed { endpoint } => {
            writer.tag(Tag(1));
            write_endpoint(writer, endpoint)?;
        },
        Linearity::UsedTwice { endpoint } => {
            writer.tag(Tag(2));
            write_endpoint(writer, endpoint)?;
        },
        Linearity::Captured { endpoint, by } => {
            writer.tag(Tag(3));
            write_endpoint(writer, endpoint)?;
            write_listed(writer, &CAPTURES, &by)?;
        },
        Linearity::AsValue { endpoint } => {
            writer.tag(Tag(5));
            write_endpoint(writer, endpoint)?;
        },
        Linearity::ArmsDisagree {
            endpoint,
            first,
            other,
        } => {
            writer.tag(Tag(6));
            write_endpoint(writer, endpoint)?;
            write_site(writer, first)?;
            write_site(writer, other)?;
        },
        Linearity::Unrestricted => writer.tag(Tag(7)),
        Linearity::Unbound { index } => {
            writer.tag(Tag(8));
            writer.word(Word(u64::from(u32::from(index))));
        },
        Linearity::BufferUnreturned { site } => {
            writer.tag(Tag(9));
            write_site(writer, site)?;
        },
        Linearity::BufferReturnedTwice { site } => {
            writer.tag(Tag(10));
            write_site(writer, site)?;
        },
        Linearity::BufferRead { site } => {
            writer.tag(Tag(11));
            write_site(writer, site)?;
        },
    }
    Ok(())
}

/// Read a linearity defect written by [`write_linearity`].
///
/// # Specification
/// - ensures: the defect of the written kind over the written payloads.
/// - fails: malformed bytes, an unknown kind, capture or side, or an index past
///   the `u32` ceiling.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every defect kind round-trips with its payload.
/// - witness: `codec::tests::session_refusals_round_trip_with_their_endpoints`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_linearity(reader: &mut Reader<'_>) -> Result<Linearity, CodecError>
{
    Ok(match reader.tag()?.0 {
        0 => Linearity::Residue {
            endpoint: read_endpoint(reader)?,
            state: read_type(reader)?,
        },
        1 => Linearity::Closed {
            endpoint: read_endpoint(reader)?,
        },
        2 => Linearity::UsedTwice {
            endpoint: read_endpoint(reader)?,
        },
        3 => Linearity::Captured {
            endpoint: read_endpoint(reader)?,
            by: read_listed(reader, &CAPTURES)?,
        },
        5 => Linearity::AsValue {
            endpoint: read_endpoint(reader)?,
        },
        6 => Linearity::ArmsDisagree {
            endpoint: read_endpoint(reader)?,
            first: read_site(reader)?,
            other: read_site(reader)?,
        },
        7 => Linearity::Unrestricted,
        8 => {
            let word = reader.word()?;
            Linearity::Unbound {
                index: u32::try_from(word.0)
                    .map(DeBruijnIndex::from)
                    .map_err(|_overflow| CodecError::Corrupt)?,
            }
        },
        9 => Linearity::BufferUnreturned {
            site: read_site(reader)?,
        },
        10 => Linearity::BufferReturnedTwice {
            site: read_site(reader)?,
        },
        11 => Linearity::BufferRead {
            site: read_site(reader)?,
        },
        _ => return Err(CodecError::Corrupt),
    })
}

/// Write a projected world: tag `0` for the host's, tag `1` and the
/// declaration's reference for a declared one.
///
/// # Specification
/// trivial.
fn write_place<Out>(
    writer: &mut Writer<'_, Out>,
    place: &Place,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *place {
        Place::Host => writer.tag(Tag(0)),
        Place::Declared(ref reference) => {
            writer.tag(Tag(1));
            write_reference(writer, reference)?;
        },
    }
    Ok(())
}

/// Read a projected world written by [`write_place`].
///
/// # Specification
/// trivial.
fn read_place(reader: &mut Reader<'_>) -> Result<Place, CodecError>
{
    Ok(match reader.tag()?.0 {
        0 => Place::Host,
        1 => Place::Declared(read_reference(reader)?),
        _ => return Err(CodecError::Corrupt),
    })
}

/// The crossing predicates, in stable wire order.
const PREDICATES: [gandr_core_checker::worlds::Predicate; 2] = [
    gandr_core_checker::worlds::Predicate::Mobile,
    gandr_core_checker::worlds::Predicate::Open,
];

/// What crosses at a refused crossing, in stable wire order.
const CROSSINGS: [gandr_core_checker::worlds::Crossed; 2] = [
    gandr_core_checker::worlds::Crossed::Result,
    gandr_core_checker::worlds::Crossed::Constant,
];

/// Write how a located judgement broke: the kind's tag, then its payloads in
/// declaration order.
///
/// # Specification
/// - ensures: the tag, then the defect's payloads in declaration order.
/// - fails: an unrepresentable reference or type table.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — every defect kind round-trips with its payload.
/// - witness: `codec::tests::located_refusals_round_trip_with_their_worlds`
fn write_located<Out>(
    writer: &mut Writer<'_, Out>,
    defect: &Located,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *defect {
        Located::Immobile {
            crossed,
            ref ty,
            ref former,
            predicate,
        } => {
            writer.tag(Tag(0));
            write_listed(writer, &CROSSINGS, &crossed)?;
            write_type(writer, ty)?;
            write_type(writer, former)?;
            write_listed(writer, &PREDICATES, &predicate)?;
        },
        Located::CapabilityMissing { ref world } => {
            writer.tag(Tag(1));
            write_place(writer, world)?;
        },
        Located::CapabilityCaptured { ref world, by } => {
            writer.tag(Tag(2));
            write_place(writer, world)?;
            write_listed(writer, &CAPTURES, &by)?;
        },
        Located::Elsewhere { ref bound } => {
            writer.tag(Tag(3));
            write_place(writer, bound)?;
        },
        Located::HoldElsewhere { ref wanted } => {
            writer.tag(Tag(4));
            write_place(writer, wanted)?;
        },
        Located::Unlocated => writer.tag(Tag(5)),
        Located::UndeclaredWorld { ref world } => {
            writer.tag(Tag(6));
            write_reference(writer, world)?;
        },
        Located::HostWorldUndeclared => writer.tag(Tag(7)),
        Located::MarkUnfounded {
            ref atom,
            ref former,
            predicate,
        } => {
            writer.tag(Tag(8));
            write_reference(writer, atom)?;
            write_type(writer, former)?;
            write_listed(writer, &PREDICATES, &predicate)?;
        },
        Located::EntryNamed { ref constant } => {
            writer.tag(Tag(9));
            write_reference(writer, constant)?;
        },
        Located::EntryUngranted { ref constant } => {
            writer.tag(Tag(10));
            write_reference(writer, constant)?;
        },
        Located::NotAHandle { ref found } => {
            writer.tag(Tag(11));
            write_type(writer, found)?;
        },
    }
    Ok(())
}

/// Read a located defect written by [`write_located`].
///
/// # Specification
/// - ensures: the defect of the written kind over the written payloads.
/// - fails: malformed bytes or an unknown kind, crossing, predicate or capture.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every defect kind round-trips with its payload.
/// - witness: `codec::tests::located_refusals_round_trip_with_their_worlds`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_located(reader: &mut Reader<'_>) -> Result<Located, CodecError>
{
    Ok(match reader.tag()?.0 {
        0 => Located::Immobile {
            crossed: read_listed(reader, &CROSSINGS)?,
            ty: read_type(reader)?,
            former: read_type(reader)?,
            predicate: read_listed(reader, &PREDICATES)?,
        },
        1 => Located::CapabilityMissing {
            world: read_place(reader)?,
        },
        2 => Located::CapabilityCaptured {
            world: read_place(reader)?,
            by: read_listed(reader, &CAPTURES)?,
        },
        3 => Located::Elsewhere {
            bound: read_place(reader)?,
        },
        4 => Located::HoldElsewhere {
            wanted: read_place(reader)?,
        },
        5 => Located::Unlocated,
        6 => Located::UndeclaredWorld {
            world: read_reference(reader)?,
        },
        7 => Located::HostWorldUndeclared,
        8 => Located::MarkUnfounded {
            atom: read_reference(reader)?,
            former: read_type(reader)?,
            predicate: read_listed(reader, &PREDICATES)?,
        },
        9 => Located::EntryNamed {
            constant: read_reference(reader)?,
        },
        10 => Located::EntryUngranted {
            constant: read_reference(reader)?,
        },
        11 => Located::NotAHandle {
            found: read_type(reader)?,
        },
        _ => return Err(CodecError::Corrupt),
    })
}

/// Write every root of a nominal signature, then the rules presenting it, then
/// the free cells of a type of words.
///
/// # Specification
/// - ensures: parameters, constructor rows, kind, rules and cells retain their
///   order; a rule side writes its node count, then per node a tag and either a
///   constructor ordinal or a variable word; the trailing tag is `0` when the
///   signature carries no cells and no index, `1` followed by the sort's
///   position, the cell count and each cell's two endpoints as rule sides when
///   it carries cells, and `2` followed by the index roots and one row of
///   stated-index roots per constructor when it is indexed.
/// - fails: an unrepresentable count or index.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — signatures with equal kinds but unequal constructors stay
///   distinct, a type of words round-trips its cells, and a vector its indices.
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
/// - witness: `codec::tests::a_type_of_words_round_trips_its_cells`
/// - witness: `codec::tests::an_indexed_family_round_trips_its_indices`
fn write_data_roots<Out>(
    writer: &mut Writer<'_, Out>,
    roots: &crate::content::DataRoots,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_indices(writer, &roots.parameters)?;
    writer.count(Count(roots.constructors.len()))?;
    for fields in &roots.constructors {
        write_indices(writer, fields)?;
    }
    write_index(writer, roots.kind)?;
    let rules = roots.presentation.rules();
    writer.count(Count(rules.len()))?;
    for rule in rules {
        write_rule_side(writer, rule.left())?;
        write_rule_side(writer, rule.right())?;
    }
    match (roots.presentation.cells(), roots.indices.is_empty()) {
        (None, true) => writer.tag(Tag(0)),
        (Some(cells), _) => {
            writer.tag(Tag(1));
            writer.count(Count(usize::from(cells.sort())))?;
            writer.count(Count(cells.cells().len()))?;
            for cell in cells.cells() {
                write_rule_side(writer, cell.source())?;
                write_rule_side(writer, cell.target())?;
            }
        },
        (None, false) => {
            writer.tag(Tag(2));
            write_indices(writer, &roots.indices)?;
            writer.count(Count(roots.results.len()))?;
            for stated in &roots.results {
                write_indices(writer, stated)?;
            }
        },
    }
    Ok(())
}

/// Write one rule side: its node count, then per node a tag and either a
/// constructor ordinal or a variable word.
///
/// # Specification
/// - ensures: the count and every node are written in order, as
///   [`read_rule_side`] reads them.
/// - fails: an unrepresentable count.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_data_roots`].
/// - witness: `codec::tests::a_type_of_words_round_trips_its_cells`
fn write_rule_side<Out>(
    writer: &mut Writer<'_, Out>,
    side: &[gandr_core_term::RuleNode],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(side.len()))?;
    for &node in side {
        match node {
            gandr_core_term::RuleNode::Constructor(tag) => {
                writer.tag(Tag(0));
                writer.count(Count(usize::from(tag)))?;
            },
            gandr_core_term::RuleNode::Variable(variable) => {
                writer.tag(Tag(1));
                writer.word(Word(u64::from(u32::from(variable))));
            },
        }
    }
    Ok(())
}

/// Read all nominal roots, rules, cells and indices without allocating from
/// untrusted counts.
///
/// # Specification
/// - ensures: successful reads consume parameters, constructor rows, kind,
///   rules and the trailing frame: the cells', or the indices'.
/// - fails: truncated or malformed root frames, an unknown rule-node tag, a
///   variable past `u32` and a trailing tag other than `0`, `1` or `2`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — nominal round trips retain the complete constructor
///   table, a type of words its cells, and a vector its indices.
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
/// - witness: `codec::tests::a_type_of_words_round_trips_its_cells`
/// - witness: `codec::tests::an_indexed_family_round_trips_its_indices`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor >= before.saturating_add(32))]
fn read_data_roots(reader: &mut Reader<'_>) -> Result<crate::content::DataRoots, CodecError>
{
    let parameters = read_indices(reader)?;
    let count = reader.count()?;
    let mut constructors = Vec::new();
    for _ in 0 .. count.0 {
        constructors.push(read_indices(reader)?);
    }
    let kind = read_index(reader)?;
    let count = reader.count()?;
    let mut rules = Vec::new();
    for _ in 0 .. count.0 {
        let left = read_rule_side(reader)?;
        let right = read_rule_side(reader)?;
        rules.push(gandr_core_term::PresentedRule::new(left, right));
    }
    let presentation = gandr_core_term::Presentation::new(rules);
    let (presentation, indices, results) = match reader.tag()?.0 {
        0 => (presentation, Vec::new(), Vec::new()),
        1 => {
            let sort = gandr_kernel_term::ConstantIndex::from(reader.count()?.0);
            let count = reader.count()?;
            let mut cells = Vec::new();
            for _ in 0 .. count.0 {
                let source = read_rule_side(reader)?;
                let target = read_rule_side(reader)?;
                cells.push(gandr_kernel_term::FreeCell::new(source, target));
            }
            (
                presentation.carrying(gandr_kernel_term::FreeCells::new(sort, cells)),
                Vec::new(),
                Vec::new(),
            )
        },
        2 => {
            let indices = read_indices(reader)?;
            let count = reader.count()?;
            let mut results = Vec::new();
            for _ in 0 .. count.0 {
                results.push(read_indices(reader)?);
            }
            (presentation, indices, results)
        },
        _ => return Err(CodecError::Corrupt),
    };
    Ok(crate::content::DataRoots {
        parameters,
        indices,
        constructors,
        results,
        kind,
        presentation,
    })
}

/// Read one rule side: a node count, then each node's tag and ordinal.
///
/// # Specification
/// - ensures: successful reads consume the count and every node in order.
/// - fails: truncation, a tag outside the constructor and variable alphabet,
///   and a variable past `u32`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`read_data_roots`].
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
#[spec(captures:[before=reader.cursor],ensures: |ret| ret.is_err() || reader.cursor >= before.saturating_add(8))]
fn read_rule_side(
    reader: &mut Reader<'_>
) -> Result<alloc::boxed::Box<[gandr_core_term::RuleNode]>, CodecError>
{
    let count = reader.count()?;
    let mut side = Vec::new();
    for _ in 0 .. count.0 {
        let node = match reader.tag()?.0 {
            0 => gandr_core_term::RuleNode::Constructor(gandr_core_term::ConstructorTag::from(
                reader.count()?.0,
            )),
            1 => {
                let word = reader.word()?;
                let ordinal = u32::try_from(word.0).map_err(|_overflow| CodecError::Corrupt)?;
                gandr_core_term::RuleNode::Variable(gandr_core_term::RuleVariable::from(ordinal))
            },
            _ => return Err(CodecError::Corrupt),
        };
        side.push(node);
    }
    Ok(side.into_boxed_slice())
}

/// Write a nominal signature's roots and shared node table.
///
/// # Specification
/// - ensures: successful writes retain every signature root and reachable node.
/// - fails: unrepresentable or process-local content.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — persisted support distinguishes equal-kind constructor
///   edits.
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
fn write_data_content<Out>(
    writer: &mut Writer<'_, Out>,
    content: &crate::content::DataContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_data_roots(writer, content.roots())?;
    write_nodes(writer, content.nodes())?;
    write_placements(writer, content.placements());
    Ok(())
}

/// Read and validate a complete nominal signature table.
///
/// # Specification
/// - ensures: every signature root has the sort [`DataRoots::sorted`] gives it
///   — a stated index a value, every other root a value type — in a
///   discovery-numbered supported table, with one support of its widths per
///   root.
/// - fails: malformed, ill-sorted or noncanonical content.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — native checkpoints preserve signatures and reject
///   malformed roots.
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
///
/// [`DataRoots::sorted`]: crate::content::DataRoots::sorted
#[spec(ensures: |ret| ret.as_ref().map_or(true,|content| content.roots().sorted().all(|(root, sort)| content.nodes().get(usize::from(root)).is_some_and(|node| node.sort() == sort))))]
fn read_data_content(reader: &mut Reader<'_>) -> Result<crate::content::DataContent, CodecError>
{
    let roots = read_data_roots(reader)?;
    let nodes = read_nodes(reader)?;
    for (root, sort) in roots.sorted() {
        root_of_sort(&nodes, root, sort)?;
    }
    check_discovery(&nodes, roots.iter())?;
    let placements = read_placements(reader, &nodes, roots.iter())?;
    Ok(crate::content::DataContent::from_parts(
        roots, nodes, placements,
    ))
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
/// - witness: `codec::tests::control_nodes_persist_names_frames_and_branch_order`
#[spec(ensures: |ret| matches!(ret, Ok(()) | Err(CodecError::Unrepresentable)))]
fn write_effect_signature<Out>(
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
/// - witness: `codec::tests::effect_rows_reject_duplicate_and_noncanonical_names`
/// - witness: `codec::tests::control_nodes_persist_names_frames_and_branch_order`
#[spec(captures: before = reader.cursor, ensures: |ret| match ret { Ok(_) => reader.cursor > before && reader.cursor <= reader.bytes.len(), Err(error) => error == CodecError::Corrupt })]
fn read_effect_signature(
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

/// Write a canonical interface map and every operation's type indices.
///
/// # Specification
/// - ensures: a representable row is written in interface and operation name
///   order.
/// - fails: `Unrepresentable` when a name length or node index cannot be
///   encoded.
///
/// # Adequacy
/// - hypothesis: L3 — relocation and persistence distinguish operation names
///   and types.
/// - witness: `codec::tests::effect_rows_persist_operation_types_and_canonical_identity`
#[spec(ensures: |ret| matches!(ret, Ok(()) | Err(CodecError::Unrepresentable)))]
fn write_effect_row<Out>(
    writer: &mut Writer<'_, Out>,
    row: &gandr_core_term::effect::EffectRow<NodeIndex>,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(row.signatures().len()))?;
    for signature in row.signatures() {
        write_effect_signature(writer, signature)?;
    }
    Ok(())
}

/// Read an interface map without accepting duplicate or noncanonical names.
///
/// # Specification
/// - ensures: successful rows consume input and preserve canonical names and
///   type edges.
/// - fails: `Corrupt` for malformed input or names not in strictly increasing
///   order.
///
/// # Adequacy
/// - hypothesis: L3 — round trips preserve nested operation types; malformed
///   rows are refused.
/// - witness: `codec::tests::effect_rows_reject_duplicate_and_noncanonical_names`
/// - witness: `codec::tests::effect_rows_persist_operation_types_and_canonical_identity`
#[spec(captures: [before = reader.cursor], ensures: |ret| match ret { Ok(_) => reader.cursor > before && reader.cursor <= reader.bytes.len(), Err(error) => error == CodecError::Corrupt })]
fn read_effect_row(
    reader: &mut Reader<'_>
) -> Result<gandr_core_term::effect::EffectRow<NodeIndex>, CodecError>
{
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    let count = reader.count()?;
    let mut signatures: Vec<EffectSig<NodeIndex>> = Vec::new();
    for _ in 0 .. count.0 {
        let signature = read_effect_signature(reader)?;
        if signatures
            .last()
            .is_some_and(|previous| previous.name() >= signature.name())
        {
            return Err(CodecError::Corrupt);
        }
        signatures.push(signature);
    }
    EffectRow::from_signatures(signatures).map_err(|_duplicate_interface| CodecError::Corrupt)
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
/// - witness: `codec::tests::every_node_former_round_trips_under_its_own_frame`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref node) => {
            reader.cursor > before
                && reader.cursor <= reader.bytes.len()
                && reader.bytes.get(before).is_some_and(|&tag| match *node {
                    ContentNode::Data { .. } => tag == 0x50,
                    ContentNode::RecordType(_) => tag == 0x51,
                    ContentNode::Constructor { .. } => tag == 0x52,
                    ContentNode::Record(_) => tag == 0x53,
                    ContentNode::DataCase { .. } => tag == 0x54,
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
                    | ContentNode::Perform { .. } => tag == 0x74,
                    | ContentNode::Handle { .. } => tag == 0x75,
                    | ContentNode::Exercise { .. } => tag == 0x7B,
                    | ContentNode::Scope { .. } => tag == 0x7C,
                    | ContentNode::Capability { .. } => tag == 0x7D,
                    | ContentNode::KeptType { .. } => tag == 0x7F,
                    | ContentNode::Resume(..) => tag == 0x76,
                    | ContentNode::Reset(_) => tag == 0x77,
                    | ContentNode::Shift(_) => tag == 0x78,
                    | ContentNode::With(..) => tag == 0x79,
                    | ContentNode::Ascribe { .. } => tag == 0x1A,
                    | ContentNode::Project(..) => tag == 0x7A,
                    | ContentNode::PrimitiveValue(_) => tag == 0x0D,
                    | ContentNode::Primitive(..) => tag == 0x16,
                    | ContentNode::PathUniverse(..) => tag == 0x40,
                    | ContentNode::PathRefl(_) => tag == 0x41,
                    | ContentNode::PathEquiv { .. } => tag == 0x42,
                    | ContentNode::PathProduct(..) => tag == 0x43,
                    | ContentNode::Transport(..) => tag == 0x44,
                    | ContentNode::PathType { .. } => tag == 0x45,
                    | ContentNode::Here(_) => tag == 0x46,
                    | ContentNode::ElementTransport { .. } => tag == 0x47,
                    | ContentNode::Returned(_) => tag == 0x48,
                    | ContentNode::Nested(_) => tag == 0x4D,
                    | ContentNode::Run(_) => tag == 0x4E,
                    | ContentNode::Funext(..) => tag == 0x49,
                    | ContentNode::Equiv(..) => tag == 0x4A,
                    | ContentNode::Univalence(..) => tag == 0x4F,
                    | ContentNode::TelescopeTransport { .. } => tag == 0x4B,
                    | ContentNode::Ua { .. } => tag == 0x4C,
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
                    | ContentNode::Application(..) => tag == 0x11,
                    | ContentNode::Return(_) => tag == 0x12,
                    | ContentNode::Bind(..) => tag == 0x13,
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
                    | ContentNode::List(_) => tag == 0x56,
                    | ContentNode::ListNil => tag == 0x57,
                    | ContentNode::ListCons(..) => tag == 0x58,
                    | ContentNode::ListFold { .. } => tag == 0x59,
                    | ContentNode::ListCase { .. } => tag == 0x5D,
                    | ContentNode::Returner { ref effects, .. } => tag == if effects.purity() == gandr_core_term::effect::Purity::Pure { 0x30 } else { 0x70 },
                    | ContentNode::Arrow { .. } => tag == 0x31,
                    | ContentNode::Pi { .. } => tag == 0x32,
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
fn read_node(reader: &mut Reader<'_>) -> Result<ContentNode, CodecError>
{
    let tag = reader.tag()?;
    let node = match tag.0 {
        0x50 => ContentNode::Data {
            declaration: read_reference(reader)?,
            arguments: read_indices(reader)?,
        },
        0x51 => ContentNode::RecordType(read_fields(reader)?),
        0x52 => ContentNode::Constructor {
            datatype: read_index(reader)?,
            tag: gandr_core_term::ConstructorTag::from(reader.count()?.0),
            fields: read_indices(reader)?,
        },
        0x53 => ContentNode::Record(read_fields(reader)?),
        0x54 => ContentNode::DataCase {
            scrutinee: read_index(reader)?,
            motive: read_index(reader)?,
            branches: read_indices(reader)?,
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
                moves.push(match reader.tag()?.0 {
                    0 => RecordedMove::Sent(read_index(reader)?),
                    1 => RecordedMove::Received(read_index(reader)?),
                    2 => RecordedMove::Selected(read_field_label(reader)?),
                    3 => RecordedMove::Offered(read_field_label(reader)?),
                    4 => RecordedMove::Closed,
                    _ => return Err(CodecError::Corrupt),
                });
            }
            ContentNode::Recorded(moves.into())
        },
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
            use gandr_core_term::effect::capability::Region;
            use gandr_core_term::effect::capability::RegionDepth;
            let authority = read_effect_row(reader)?;
            let grade = match reader.tag()?.0 {
                0 => CapabilityGrade::Durable,
                1 => CapabilityGrade::Consumable,
                _ => return Err(CodecError::Corrupt),
            };
            let region = match reader.tag()?.0 {
                0 => Region::Held,
                1 => {
                    let depth =
                        u32::try_from(reader.word()?.0).map_err(|_overflow| CodecError::Corrupt)?;
                    Region::Scoped(RegionDepth::from(depth))
                },
                _ => return Err(CodecError::Corrupt),
            };
            ContentNode::Capability {
                authority,
                grade,
                region,
            }
        },
        0x7F => {
            let value = read_index(reader)?;
            let depth = u32::try_from(reader.word()?.0).map_err(|_overflow| CodecError::Corrupt)?;
            ContentNode::KeptType {
                value,
                region: gandr_core_term::effect::capability::RegionDepth::from(depth),
            }
        },
        0x76 => ContentNode::Resume(read_index(reader)?, read_index(reader)?),
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
        0x20 => {
            let base = reader.tag()?;
            ContentNode::Base(match base.0 {
                0 => BaseType::Integer,
                1 => BaseType::String,
                2 => BaseType::Numeric,
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
        0x43 => ContentNode::PathProduct(read_index(reader)?, read_index(reader)?),
        0x44 => ContentNode::Transport(read_index(reader)?, read_index(reader)?),
        0x45 => ContentNode::PathType {
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
/// - witness: `codec::tests::holes_marks_and_the_unknown_types_round_trip`
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
/// - witness: `codec::tests::holes_marks_and_the_unknown_types_round_trip`
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

/// Write a supported table: its count, each node's former and scope, then
/// every node's edges in node and child order. A cover holds one edge per
/// child of its former and an edge is as wide as its child's scope, so
/// neither a cover's arity nor an edge's widths is written.
///
/// # Specification
/// - ensures: successful tables contain no unresolved node; an unsupported
///   refusal names the first one. The references each node carries are not
///   written: a reader rebuilds them.
///
/// # Adequacy
/// - hypothesis: L3 — nested unresolved nodes in all four sorts retain the
///   precise refusal; a written table reads back equal. Structural validation
///   is a reader responsibility.
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
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
        | Err(CodecError::Unrepresentable) => true,
        | _ => false,
    },
)]
fn write_nodes<Out>(
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
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
fn write_selection<Out>(
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
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[spec(ensures: |ret| match ret {
    Ok(ref selected) => selected.scope() == scope,
    Err(error) => error == CodecError::Corrupt,
})]
fn read_selection(
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
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[spec(ensures: |ret| ret.is_ok() == [Zone::Intuitionistic, Zone::Linear].into_iter()
    .all(|zone| u32::try_from(usize::from(scope.width(zone))).is_ok()))]
fn write_scope<Out>(
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
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
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

/// Write each root's support, in root order; each is as wide as its root's
/// scope, so neither the count nor the widths is written.
///
/// # Specification
/// - ensures: each support's indices, in root order.
/// - executable: none — a generic sink exposes no byte observer.
///
/// # Adequacy
/// - hypothesis: L3 — an item, a type and a data signature round-trip their
///   root supports.
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
fn write_placements<Out>(
    writer: &mut Writer<'_, Out>,
    placements: &[Thinning],
) where
    Out: Sink,
{
    for placement in placements {
        write_selection(writer, placement);
    }
}

/// Read one support per root of `nodes`, each as wide as its root's scope.
///
/// # Specification
/// - ensures: one support per root, in root order, each with its root's widths.
/// - fails: [`CodecError::Corrupt`] for a root out of range or a malformed
///   support.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an item, a type and a data signature round-trip their
///   root supports; a descending root support is refused.
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[spec(captures: [count = roots.clone().count()], ensures: |ret| ret.as_ref().map_or(true, |placements| placements.len() == count))]
fn read_placements<Roots>(
    reader: &mut Reader<'_>,
    nodes: &[SupportedNode],
    roots: Roots,
) -> Result<Vec<Thinning>, CodecError>
where
    Roots: Iterator<Item = NodeIndex> + Clone,
{
    roots
        .map(|root| {
            let node = nodes.get(usize::from(root)).ok_or(CodecError::Corrupt)?;
            read_selection(reader, node.scope())
        })
        .collect()
}

/// Read a supported table and rebuild it: every node's former and scope,
/// then each edge as wide as its child's scope; every child in range and of
/// its required sort, the table acyclic, every cover the exact minimal cover
/// of its node, no node twice, and every node's references recomputed.
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
/// - witness: `codec::tests::type_tables_validate_roots_child_extents_and_sorts`
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
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
fn read_nodes(reader: &mut Reader<'_>) -> Result<Vec<SupportedNode>, CodecError>
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
        parts.push(crate::support::NodeParts {
            former,
            cover,
            scope,
        });
    }
    crate::support::assemble(parts).map_err(|fault| match fault {
        crate::support::TableFault::Duplicate => CodecError::NonCanonical,
        crate::support::TableFault::Child
        | crate::support::TableFault::Cycle
        | crate::support::TableFault::Cover(_) => CodecError::Corrupt,
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
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `codec::tests::discovery_accepts_repeated_roots_and_empty_tables`
#[spec(
    requires: nodes.iter().all(|node| {
        node.former().children()
            .iter()
            .all(|(child, _)| usize::from(child) < nodes.len())
    }),
    captures:[expected_roots=roots.clone()],
    ensures: |ret| {
        ret == 'discovery: {
            let mut next = 0_usize;
            for root in expected_roots.clone() {
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
        }
    },
)]
fn check_discovery<Roots>(
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
/// - ensures: located content, which has no spelling, is refused before
///   anything is written; an unsupported refusal names the first unresolved
///   table node; metadata precedes the table.
///
/// # Adequacy
/// - hypothesis: L3 — independently built programs have identical content
///   encodings, while unresolved nodes are refused. The predicate classifies
///   table failures without duplicating serialization.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[spec(
    ensures: |ret| match ret {
        | Ok(()) => content.locus() == crate::content::Locus::Unlocated
            && content
                .nodes()
                .iter()
                .all(|node| !matches!(*node.former(), ContentNode::Unresolved(_))),
        | Err(CodecError::Unsupported(UnsupportedPersistence::Located)) => {
            content.locus() == crate::content::Locus::Located
                || matches!(*content.declaration(), crate::content::DeclarationRoots::World)
        },
        | Err(CodecError::Unsupported(UnsupportedPersistence::Codata)) => {
            matches!(*content.declaration(), crate::content::DeclarationRoots::Codata)
        },
        | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
            content.nodes().iter().find_map(|node| match *node.former() {
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
    if content.locus() == crate::content::Locus::Located {
        return Err(CodecError::Unsupported(UnsupportedPersistence::Located));
    }
    write_reference(writer, content.reference())?;
    match *(content.declaration()) {
        crate::content::DeclarationRoots::Value {
            ref signature,
            ref body,
            ref laws,
            ref rules,
            ref stages,
            ref supplies,
        } => {
            // A value naming no law keeps its original tag; a lawful one
            // takes its own, with the laws after the body; a ruled one takes
            // its own, with the laws, however many, then the rules; one
            // quantified over stages takes its own, with the laws and the
            // rules, however many, then each binder's bound; one whose calls
            // supply stages takes its own, with the laws, the rules and the
            // bounds, however many, then each supply.
            writer.tag(Tag(if !supplies.is_empty() {
                7
            }
            else if !stages.is_empty() {
                6
            }
            else if !rules.is_empty() {
                5
            }
            else if laws.is_empty() {
                0
            }
            else {
                3
            }));
            match *signature {
                Maybe::Present(root) => {
                    writer.tag(Tag(1));
                    write_index(writer, root)?;
                },
                Maybe::Absent(signature::Absent::Unsigned) => writer.tag(Tag(0)),
            }
            match *body {
                Maybe::Present(root) => {
                    writer.tag(Tag(1));
                    write_index(writer, root)?;
                },
                Maybe::Absent(body::Absent::Hole) => writer.tag(Tag(0)),
            }
            let staged = !stages.is_empty() || !supplies.is_empty();
            if !laws.is_empty() || !rules.is_empty() || staged {
                writer.count(Count(laws.len()))?;
                for law in laws {
                    write_reference(writer, law)?;
                }
            }
            if !rules.is_empty() || staged {
                writer.count(Count(rules.len()))?;
                for rule in rules {
                    write_operation_side(writer, &rule.left)?;
                    write_operation_side(writer, &rule.right)?;
                }
            }
            if staged {
                writer.count(Count(stages.len()))?;
                for &bound in stages {
                    writer.count(Count(match bound {
                        gandr_kernel_term::StageBound::Unbounded => 0,
                        gandr_kernel_term::StageBound::Below(binder) => {
                            usize::from(binder).saturating_add(1)
                        },
                    }))?;
                }
            }
            if !supplies.is_empty() {
                writer.count(Count(supplies.len()))?;
                for &(head, binder, stage) in supplies {
                    write_index(writer, head)?;
                    writer.count(Count(usize::from(binder)))?;
                    write_stage(writer, stage)?;
                }
            }
        },
        crate::content::DeclarationRoots::Data(ref roots) => {
            writer.tag(Tag(1));
            write_data_roots(writer, roots)?;
        },
        crate::content::DeclarationRoots::Abstract(roots) => {
            // An unmarked abstract type keeps its original tag; a mobile one
            // takes its own.
            writer.tag(Tag(match roots.mobility {
                gandr_core_checker::worlds::Mobility::Immobile => 2,
                gandr_core_checker::worlds::Mobility::Mobile => 4,
            }));
            write_index(writer, roots.kind)?;
            write_index(writer, roots.representation)?;
            writer.count(Count(usize::from(roots.extent)))?;
            writer.count(Count(usize::from(roots.site.sealing())))?;
            writer.count(Count(usize::from(roots.site.component())))?;
        },
        crate::content::DeclarationRoots::World => {
            return Err(CodecError::Unsupported(UnsupportedPersistence::Located));
        },
        crate::content::DeclarationRoots::Codata => {
            return Err(CodecError::Unsupported(UnsupportedPersistence::Codata));
        },
    }
    write_nodes(writer, content.nodes())?;
    write_placements(writer, content.placements());
    Ok(())
}

/// Write one side of an operation rule's content: its node count, then each
/// node's tag and payload.
///
/// # Specification
/// - fails: as [`write_reference`] and the writer's count.
/// - panics: none.
/// - executable: none — the bytes written are the body's own output; the
///   witness reads them back.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a ruled item's content round-trips.
/// - witness: `codec::tests::a_ruled_value_root_round_trips_and_its_rules_are_content`
fn write_operation_side<Out>(
    writer: &mut Writer<'_, Out>,
    side: &[crate::content::RuleRoot],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(side.len()))?;
    for node in side {
        match *node {
            crate::content::RuleRoot::Operation { ref callee, arity } => {
                writer.tag(Tag(0));
                write_reference(writer, callee)?;
                writer.count(Count(usize::from(arity)))?;
            },
            crate::content::RuleRoot::Constructor { ref family, tag } => {
                writer.tag(Tag(1));
                write_reference(writer, family)?;
                writer.count(Count(usize::from(tag)))?;
            },
            crate::content::RuleRoot::Results(count) => {
                writer.tag(Tag(2));
                writer.count(Count(usize::from(count)))?;
            },
            crate::content::RuleRoot::Variable(variable) => {
                writer.tag(Tag(3));
                writer.count(Count(
                    usize::try_from(u32::from(variable))
                        .map_err(|_overflow| CodecError::Unrepresentable)?,
                ))?;
            },
        }
    }
    Ok(())
}

/// Read one side of an operation rule's content.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for a node tag outside the four, or a
///   variable past `u32`; as [`read_reference`] and the reader's count.
/// - panics: none.
/// - executable: none — the read nodes are the body's own output; the witness
///   pins the round trip.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a ruled item's content round-trips.
/// - witness: `codec::tests::a_ruled_value_root_round_trips_and_its_rules_are_content`
fn read_operation_side(reader: &mut Reader<'_>)
-> Result<Vec<crate::content::RuleRoot>, CodecError>
{
    let count = reader.count()?.0;
    let mut side = Vec::new();
    for _node in 0 .. count {
        side.push(match reader.tag()?.0 {
            0 => crate::content::RuleRoot::Operation {
                callee: read_reference(reader)?,
                arity: gandr_kernel_term::FieldCount::from(reader.count()?.0),
            },
            1 => crate::content::RuleRoot::Constructor {
                family: read_reference(reader)?,
                tag: gandr_kernel_term::ConstructorTag::from(reader.count()?.0),
            },
            2 => crate::content::RuleRoot::Results(gandr_kernel_term::FieldCount::from(
                reader.count()?.0,
            )),
            3 => crate::content::RuleRoot::Variable(gandr_kernel_term::RuleVariable::from(
                u32::try_from(reader.count()?.0).map_err(|_overflow| CodecError::Corrupt)?,
            )),
            _ => return Err(CodecError::Corrupt),
        });
    }
    Ok(side)
}

/// Read an item's content.
///
/// # Specification
/// - fails: as [`read_nodes`] and [`check_discovery`], and
///   [`CodecError::Corrupt`] for a signature root that is no value type, a body
///   root that is no value, or root supports that are not one per root of the
///   root's widths.
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
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref content) => {
            let nodes = content.nodes();
            let roots = content.declaration().iter();
            nodes.iter().all(|node| {
                !matches!(*node.former(), ContentNode::Unresolved(_))
                    && node.former().children().iter().all(|(child, sort)| {
                        nodes
                            .get(usize::from(child))
                            .is_some_and(|found| found.sort() == sort)
                    })
            }) && roots.clone().all(|(root, sort)| {
                nodes
                    .get(usize::from(root))
                    .is_some_and(|node| node.sort() == sort)
            }) && 'discovery: {
                let mut next = 0_usize;
                for root in roots.map(|(root, _)| root) {
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
fn read_item_content(reader: &mut Reader<'_>) -> Result<ItemContent, CodecError>
{
    let reference = read_reference(reader)?;
    let declaration = match reader.tag()?.0 {
        tag @ (0 | 3 | 5 | 6 | 7) => {
            let signature = match reader.tag()?.0 {
                0 => Maybe::Absent(signature::Absent::Unsigned),
                1 => Maybe::Present(read_index(reader)?),
                _ => return Err(CodecError::Corrupt),
            };
            let body = match reader.tag()?.0 {
                0 => Maybe::Absent(body::Absent::Hole),
                1 => Maybe::Present(read_index(reader)?),
                _ => return Err(CodecError::Corrupt),
            };
            let mut laws = Vec::new();
            if tag != 0 {
                let count = reader.count()?.0;
                if count == 0 && tag == 3 {
                    return Err(CodecError::NonCanonical);
                }
                for _law in 0 .. count {
                    laws.push(read_reference(reader)?);
                }
            }
            let mut rules = Vec::new();
            if tag >= 5 {
                let count = reader.count()?.0;
                if count == 0 && tag == 5 {
                    return Err(CodecError::NonCanonical);
                }
                for _rule in 0 .. count {
                    let left = read_operation_side(reader)?;
                    let right = read_operation_side(reader)?;
                    rules.push(crate::content::RuleRoots { left, right });
                }
            }
            let mut stages = Vec::new();
            if tag >= 6 {
                let count = reader.count()?.0;
                if count == 0 && tag == 6 {
                    return Err(CodecError::NonCanonical);
                }
                for _binder in 0 .. count {
                    stages.push(reader.count()?.0.checked_sub(1).map_or(
                        gandr_kernel_term::StageBound::Unbounded,
                        |bound| {
                            gandr_kernel_term::StageBound::Below(
                                gandr_kernel_term::StageBinder::from(bound),
                            )
                        },
                    ));
                }
            }
            let mut supplies = Vec::new();
            if tag == 7 {
                let count = reader.count()?.0;
                if count == 0 {
                    return Err(CodecError::NonCanonical);
                }
                for _supply in 0 .. count {
                    let head = read_index(reader)?;
                    let binder = gandr_kernel_term::StageBinder::from(reader.count()?.0);
                    supplies.push((head, binder, read_stage(reader)?));
                }
            }
            crate::content::DeclarationRoots::Value {
                signature,
                body,
                laws,
                rules,
                stages,
                supplies,
            }
        },
        1 => crate::content::DeclarationRoots::Data(read_data_roots(reader)?),
        tag @ (2 | 4) => {
            let kind = read_index(reader)?;
            let representation = read_index(reader)?;
            let extent = gandr_kernel_term::SealExtent::from(reader.count()?.0);
            let sealing = gandr_core_checker::SealingSite::from(reader.count()?.0);
            let component = gandr_core_checker::ComponentOrdinal::from(reader.count()?.0);
            crate::content::DeclarationRoots::Abstract(crate::content::AbstractRoots {
                kind,
                representation,
                extent,
                site: gandr_core_checker::SealSite::new(sealing, component),
                mobility: if tag == 4 {
                    gandr_core_checker::worlds::Mobility::Mobile
                }
                else {
                    gandr_core_checker::worlds::Mobility::Immobile
                },
            })
        },
        _ => return Err(CodecError::Corrupt),
    };
    let nodes = read_nodes(reader)?;
    for (root, sort) in declaration.iter() {
        root_of_sort(&nodes, root, sort)?;
    }
    if let crate::content::DeclarationRoots::Value { ref supplies, .. } = declaration {
        for &(head, ..) in supplies {
            root_of_sort(&nodes, head, Sort::Value)?;
        }
    }
    check_discovery(&nodes, declaration.iter().map(|(root, _)| root))?;
    let placements = read_placements(reader, &nodes, declaration.iter().map(|(root, _)| root))?;
    Ok(ItemContent::from_parts(
        reference,
        declaration,
        nodes,
        placements,
    ))
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
    nodes: &[SupportedNode],
    root: NodeIndex,
    sort: Sort,
) -> Result<(), CodecError>
{
    match nodes.get(usize::from(root)) {
        Some(node) if node.sort() == sort => Ok(()),
        Some(_) | None => Err(CodecError::Corrupt),
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
/// - witness: `codec::tests::type_tables_validate_roots_child_extents_and_sorts`
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
/// - witness: `persistence::tests::universe_sorts_and_levels_round_trip`
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
fn read_type(reader: &mut Reader<'_>) -> Result<TypeContent, CodecError>
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
        Opacity::Transparent => Tag(0),
        Opacity::Opaque => Tag(1),
    });
    writer.tag(match footprint.hole() {
        HoleMark::Filled => Tag(0),
        HoleMark::Hole => Tag(1),
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
/// - witness: `codec::tests::every_footprint_stance_and_answer_round_trips`
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
        0 => Opacity::Transparent,
        1 => Opacity::Opaque,
        _ => return Err(CodecError::Corrupt),
    };
    let hole = reader.tag()?;
    let hole = match hole.0 {
        0 => HoleMark::Filled,
        1 => HoleMark::Hole,
        _ => return Err(CodecError::Corrupt),
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
        Site::Node(index) => {
            writer.tag(Tag(0));
            write_index(writer, index)?;
        },
        Site::Unreached => writer.tag(Tag(1)),
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
        0 => {
            let index = read_index(reader)?;
            Ok(Site::Node(index))
        },
        1 => Ok(Site::Unreached),
        _ => Err(CodecError::Corrupt),
    }
}

/// The tags of the unadmitted formers, in stable wire order.
const FORMERS: [UnadmittedFormer; 24] = [
    UnadmittedFormer::ValueLift,
    UnadmittedFormer::NumericLiteral,
    UnadmittedFormer::NumericAtom,
    UnadmittedFormer::TypeLift,
    UnadmittedFormer::Abstract,
    UnadmittedFormer::SortParameter,
    UnadmittedFormer::TopUniverse,
    UnadmittedFormer::StaticLambda,
    UnadmittedFormer::EffectRow,
    UnadmittedFormer::Reify,
    UnadmittedFormer::Stack,
    UnadmittedFormer::Perform,
    UnadmittedFormer::Handle,
    UnadmittedFormer::Resume,
    UnadmittedFormer::Reset,
    UnadmittedFormer::Shift,
    UnadmittedFormer::Capability,
    UnadmittedFormer::Exercise,
    UnadmittedFormer::Scope,
    UnadmittedFormer::Run,
    UnadmittedFormer::HigherFlow,
    UnadmittedFormer::Memory,
    UnadmittedFormer::Stage,
    UnadmittedFormer::Buffer,
];

/// The shapes a rule can require, in stable wire order.
const SHAPES: [ExpectedShape; 17] = [
    ExpectedShape::Thunk,
    ExpectedShape::Returner,
    ExpectedShape::Arrow,
    ExpectedShape::Product,
    ExpectedShape::StaticPi,
    ExpectedShape::PathUniverse,
    ExpectedShape::Sum,
    ExpectedShape::Data,
    ExpectedShape::Record,
    ExpectedShape::Stack,
    ExpectedShape::With,
    ExpectedShape::List,
    ExpectedShape::Session,
    ExpectedShape::Capability,
    ExpectedShape::Flow,
    ExpectedShape::Run,
    ExpectedShape::Sigma,
];

/// The actions a session state admits, in stable wire order.
const ACTIONS: [ActionKind; 5] = [
    ActionKind::Send,
    ActionKind::Receive,
    ActionKind::Select,
    ActionKind::Offer,
    ActionKind::Close,
];

/// The binders of an endpoint, in stable wire order.
const SIDES: [ForkSide; 3] = [ForkSide::Child, ForkSide::Parent, ForkSide::Received];

/// What may run an endpoint's use other than once, in stable wire order.
const CAPTURES: [Capture; 5] = [
    Capture::Thunk,
    Capture::Recursion,
    Capture::Branch,
    Capture::Stack,
    Capture::Continuation,
];

/// Write a fixpoint's termination evidence: a tag in stable wire order, a
/// staged claim's position after it as a word.
///
/// # Specification
/// - ensures: `Partial` writes tag 0, `StructuralDescent` tag 1, and `Staged`
///   tag 2 then its position.
/// - fails: [`CodecError::Unrepresentable`] for a position past 64 bits.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — each evidence round-trips, the staged one with its
///   position.
/// - witness: `codec::tests::fixpoint_evidence_round_trips_with_its_staged_position`
#[spec(ensures: |ret| ret.is_ok() || ret == Err(CodecError::Unrepresentable))]
fn write_evidence<Out>(
    writer: &mut Writer<'_, Out>,
    evidence: FixpointEvidence,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match evidence {
        FixpointEvidence::Partial => writer.tag(Tag(0)),
        FixpointEvidence::StructuralDescent => writer.tag(Tag(1)),
        FixpointEvidence::Staged { position } => {
            let position = u64::try_from(usize::from(position))
                .map_err(|_wide| CodecError::Unrepresentable)?;
            writer.tag(Tag(2));
            writer.word(Word(position));
        },
    }
    Ok(())
}

/// Read a fixpoint's termination evidence as [`write_evidence`] writes it.
///
/// # Specification
/// - ensures: tags 0 and 1 read the partial and structural evidence, tag 2 a
///   staged claim at the position after it.
/// - fails: [`CodecError::Corrupt`] for another tag, a short input, or a
///   position past the platform's width.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_evidence`], and a tag past 2 is corrupt.
/// - witness: `codec::tests::fixpoint_evidence_round_trips_with_its_staged_position`
#[spec(captures: before = reader.cursor, ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_evidence(reader: &mut Reader<'_>) -> Result<FixpointEvidence, CodecError>
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
        _ => Err(CodecError::Corrupt),
    }
}

/// Write a stage a recursion refusal names: tag 0 and the stage's ordinal
/// for a stage itself, tag 1, its anchor's ordinal and the steps below it
/// for a bound.
///
/// # Specification
/// - fails: [`CodecError::Unrepresentable`] for an ordinal past 64 bits.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a refusal at a stage and one at a bound round-trip.
/// - witness: `codec::tests::a_stage_refusal_round_trips_with_where_it_stood`
#[spec(ensures: |ret| ret.is_ok() || ret == Err(CodecError::Unrepresentable))]
fn write_stage<Out>(
    writer: &mut Writer<'_, Out>,
    stage: Stage,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let ordinal =
        |id: StageId| u64::try_from(usize::from(id)).map_err(|_wide| CodecError::Unrepresentable);
    match stage {
        Stage::At(id) => {
            let id = ordinal(id)?;
            writer.tag(Tag(0));
            writer.word(Word(id));
        },
        Stage::Below { anchor, depth } => {
            let anchor = ordinal(anchor)?;
            writer.tag(Tag(1));
            writer.word(Word(anchor));
            writer.word(Word(u64::from(u32::from(depth))));
        },
    }
    Ok(())
}

/// Read a stage as [`write_stage`] writes it.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for another tag, a short input, an ordinal
///   past the platform's width, or a bound zero or more than 32 bits of steps
///   below its anchor.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_stage`].
/// - witness: `codec::tests::a_stage_refusal_round_trips_with_where_it_stood`
#[spec(captures: before = reader.cursor, ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_stage(reader: &mut Reader<'_>) -> Result<Stage, CodecError>
{
    let tag = reader.tag()?;
    let word = reader.word()?;
    let id = usize::try_from(word.0).map_err(|_wide| CodecError::Corrupt)?;
    let id = StageId::from(id);
    match tag.0 {
        0 => Ok(Stage::At(id)),
        1 => {
            let steps = reader.word()?;
            let steps = u32::try_from(steps.0).map_err(|_wide| CodecError::Corrupt)?;
            let depth = core::num::NonZeroU32::new(steps).ok_or(CodecError::Corrupt)?;
            Ok(Stage::Below {
                anchor: id,
                depth: StageDepth::from(depth),
            })
        },
        _ => Err(CodecError::Corrupt),
    }
}

/// Write where a value stood in a stage order: tag 0 for the top, tag 1 and
/// the stage otherwise.
///
/// # Specification
/// - fails: as [`write_stage`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_stage`], and the top round-trips.
/// - witness: `codec::tests::a_stage_refusal_round_trips_with_where_it_stood`
#[spec(ensures: |ret| ret.is_ok() || ret == Err(CodecError::Unrepresentable))]
fn write_standing<Out>(
    writer: &mut Writer<'_, Out>,
    standing: Standing,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match standing {
        Standing::Top => {
            writer.tag(Tag(0));
            Ok(())
        },
        Standing::Staged(stage) => {
            writer.tag(Tag(1));
            write_stage(writer, stage)
        },
    }
}

/// Read where a value stood as [`write_standing`] writes it.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for another tag, and as [`read_stage`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_standing`].
/// - witness: `codec::tests::a_stage_refusal_round_trips_with_where_it_stood`
#[spec(captures: before = reader.cursor, ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_standing(reader: &mut Reader<'_>) -> Result<Standing, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        0 => Ok(Standing::Top),
        1 => {
            let stage = read_stage(reader)?;
            Ok(Standing::Staged(stage))
        },
        _ => Err(CodecError::Corrupt),
    }
}

/// The faults a presented type's rule is refused for, in stable wire order.
const RULE_FAULTS: [gandr_kernel_term::RuleFault; 10] = [
    gandr_kernel_term::RuleFault::VariableHeaded,
    gandr_kernel_term::RuleFault::UnknownConstructor,
    gandr_kernel_term::RuleFault::Arity,
    gandr_kernel_term::RuleFault::NotOwnPosition,
    gandr_kernel_term::RuleFault::NonLinear,
    gandr_kernel_term::RuleFault::Unbound,
    gandr_kernel_term::RuleFault::Duplicated,
    gandr_kernel_term::RuleFault::SlotMismatch,
    gandr_kernel_term::RuleFault::NotDecreasing,
    gandr_kernel_term::RuleFault::DependentSlot,
];

/// Write the parameter or field an occurrence refusal names.
///
/// # Specification
/// - ensures: a parameter writes tag 0 and its position; a field writes tag 1,
///   its constructor's tag and its position.
/// - fails: [`CodecError::Unrepresentable`] for a count no word holds.
/// - panics: none.
///
/// # Errors
/// - [`CodecError`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a field and a telescope site round-trip through a
///   persisted refused declaration.
/// - witness: `tests::recursive_data::recursive_data_checkpoints_round_trip_and_resume`
#[spec(ensures: |ret| ret.is_ok() || ret == Err(CodecError::Unrepresentable))]
fn write_occurrence_site<Out>(
    writer: &mut Writer<'_, Out>,
    site: OccurrenceSite,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match site {
        OccurrenceSite::Parameter(position) => {
            writer.tag(Tag(0));
            writer.count(Count(usize::from(position)))?;
        },
        OccurrenceSite::Field { tag, field } => {
            writer.tag(Tag(1));
            writer.count(Count(usize::from(tag)))?;
            writer.count(Count(usize::from(field)))?;
        },
    }
    Ok(())
}

/// Read the parameter or field an occurrence refusal names.
///
/// # Specification
/// - ensures: the inverse of [`write_occurrence_site`].
/// - fails: [`CodecError::Corrupt`] for an unknown site tag, or the reader's
///   own refusal.
/// - panics: none.
///
/// # Errors
/// - [`CodecError`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a field and a telescope site round-trip through a
///   persisted refused declaration.
/// - witness: `tests::recursive_data::recursive_data_checkpoints_round_trip_and_resume`
#[spec(captures: before = reader.cursor, ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_occurrence_site(reader: &mut Reader<'_>) -> Result<OccurrenceSite, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        0 => Ok(OccurrenceSite::Parameter(ParameterPosition::from(
            reader.count()?.0,
        ))),
        1 => {
            let constructor = ConstructorTag::from(reader.count()?.0);
            let field = FieldPosition::from(reader.count()?.0);
            Ok(OccurrenceSite::Field {
                tag: constructor,
                field,
            })
        },
        _ => Err(CodecError::Corrupt),
    }
}

/// Write why an absurd case's endpoints are not apart.
///
/// # Specification
/// - ensures: one tag per reason in declaration order, `Diverges` followed by
///   its two rule positions.
/// - fails: [`CodecError::Unrepresentable`] for a count no word holds.
/// - panics: none.
///
/// # Errors
/// - [`CodecError`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — each reason, and each order of a divergent pair, keeps
///   its own encoding and round-trips through a refusal.
/// - witness: `codec::tests::an_absurd_case_s_refusal_round_trips_with_its_reason`
#[spec(ensures: |ret| ret.is_ok() || ret == Err(CodecError::Unrepresentable))]
fn write_apartness<Out>(
    writer: &mut Writer<'_, Out>,
    reason: gandr_kernel_term::Apartness,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match reason {
        gandr_kernel_term::Apartness::Apart => writer.tag(Tag(0)),
        gandr_kernel_term::Apartness::Agree => writer.tag(Tag(1)),
        gandr_kernel_term::Apartness::Open => writer.tag(Tag(2)),
        gandr_kernel_term::Apartness::Leaf => writer.tag(Tag(3)),
        gandr_kernel_term::Apartness::Diverges { outer, inner } => {
            writer.tag(Tag(4));
            writer.count(Count(usize::from(outer)))?;
            writer.count(Count(usize::from(inner)))?;
        },
        gandr_kernel_term::Apartness::Undecided => writer.tag(Tag(5)),
    }
    Ok(())
}

/// Read why an absurd case's endpoints are not apart.
///
/// # Specification
/// - ensures: the inverse of [`write_apartness`].
/// - fails: [`CodecError::Corrupt`] for an unknown reason tag, or the reader's
///   own refusal.
/// - panics: none.
///
/// # Errors
/// - [`CodecError`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`write_apartness`].
/// - witness: `codec::tests::an_absurd_case_s_refusal_round_trips_with_its_reason`
#[spec(captures: before = reader.cursor, ensures: |ret| ret.is_err() || reader.cursor > before)]
fn read_apartness(reader: &mut Reader<'_>) -> Result<gandr_kernel_term::Apartness, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        0 => Ok(gandr_kernel_term::Apartness::Apart),
        1 => Ok(gandr_kernel_term::Apartness::Agree),
        2 => Ok(gandr_kernel_term::Apartness::Open),
        3 => Ok(gandr_kernel_term::Apartness::Leaf),
        4 => {
            let outer = gandr_kernel_term::RuleIndex::from(reader.count()?.0);
            let inner = gandr_kernel_term::RuleIndex::from(reader.count()?.0);
            Ok(gandr_kernel_term::Apartness::Diverges { outer, inner })
        },
        5 => Ok(gandr_kernel_term::Apartness::Undecided),
        _ => Err(CodecError::Corrupt),
    }
}

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
        let tables: [&[SupportedNode]; 2] = match *refusal {
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
            Refusal::DataFieldLevel {kind:ref found,..} | Refusal::RepresentationAboveKind {kind:ref found,..} | Refusal::MissingRecordField {expected:ref found,..} | Refusal::ShapeMismatch { ref found, .. }
            | Refusal::SessionMismatch { state: ref found, .. } | Refusal::Linearity { defect: Linearity::Residue { state: ref found, .. }, .. }
            | Refusal::StaticClassifierExpected { ref found, .. } => [found.nodes(), &[]],
            | Refusal::DependentBind {
                ref synthesised, ..
            } => [synthesised.nodes(), &[]],
            | Refusal::Located { defect: Located::Immobile { ref ty, ref former, .. }, .. } => [ty.nodes(), former.nodes()],
            | Refusal::Located { defect: Located::MarkUnfounded { ref former, .. } | Located::NotAHandle { found: ref former }, .. } => [former.nodes(), &[]],
            | _ => [&[], &[]],
        };
        match ret {
            | Ok(()) => tables
                .into_iter()
                .flatten()
                .all(|node| !matches!(*node.former(), ContentNode::Unresolved(_))),
            | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
                tables.into_iter().flatten().find_map(|node| match *node.former() {
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
        Refusal::NotADataType(ref reference) => {
            writer.tag(Tag(19));
            write_reference(writer, reference)?;
        },
        Refusal::DataKindNotUniverse(at) => {
            writer.tag(Tag(20));
            write_site(writer, at)?;
        },
        Refusal::DataFieldLevel { field, ref kind } => {
            writer.tag(Tag(21));
            write_site(writer, field)?;
            write_type(writer, kind)?;
        },
        Refusal::RuleNotPresentable { kind, refusal } => {
            writer.tag(Tag(72));
            write_site(writer, kind)?;
            writer.count(Count(usize::from(refusal.rule)))?;
            write_listed(writer, &RULE_FAULTS, &refusal.fault)?;
        },
        Refusal::RuleNotRespected { at, rule } => {
            writer.tag(Tag(73));
            write_site(writer, at)?;
            writer.count(Count(usize::from(rule)))?;
        },
        Refusal::NotApart { at, reason } => {
            writer.tag(Tag(74));
            write_site(writer, at)?;
            write_apartness(writer, reason)?;
        },
        Refusal::LoopNotRespected { at, cell, reason } => {
            writer.tag(Tag(75));
            write_site(writer, at)?;
            writer.count(Count(usize::from(cell)))?;
            writer.tag(Tag(match reason {
                gandr_core_checker::LoopRespect::Apart => 0,
                gandr_core_checker::LoopRespect::NotPresentedSet => 1,
            }));
        },
        Refusal::LoopUndecided { at, cell } => {
            writer.tag(Tag(78));
            write_site(writer, at)?;
            writer.count(Count(usize::from(cell)))?;
        },
        Refusal::AbstractKindNotUniverse(at) => {
            writer.tag(Tag(48));
            write_site(writer, at)?;
        },
        Refusal::RepresentationAboveKind {
            representation,
            ref kind,
        } => {
            writer.tag(Tag(49));
            write_site(writer, representation)?;
            write_type(writer, kind)?;
        },
        Refusal::NotAnAbstractType(ref reference) => {
            writer.tag(Tag(50));
            write_reference(writer, reference)?;
        },
        Refusal::SealSiteRepeated(site) => {
            writer.tag(Tag(51));
            writer.count(Count(usize::from(site.sealing())))?;
            writer.count(Count(usize::from(site.component())))?;
        },
        Refusal::DataArgumentArity(at) => {
            writer.tag(Tag(22));
            write_site(writer, at)?;
        },
        Refusal::UnknownConstructor { at, tag } => {
            writer.tag(Tag(23));
            write_site(writer, at)?;
            writer.count(Count(usize::from(tag)))?;
        },
        Refusal::ConstructorArity(at) => {
            writer.tag(Tag(24));
            write_site(writer, at)?;
        },
        Refusal::IndexedCase(at) => {
            writer.tag(Tag(81));
            write_site(writer, at)?;
        },
        Refusal::NonExhaustiveDataCase(at) => {
            writer.tag(Tag(25));
            write_site(writer, at)?;
        },
        Refusal::UndecidedCoverage(at) => {
            writer.tag(Tag(80));
            write_site(writer, at)?;
        },
        Refusal::AbsentRecordField(at) => {
            writer.tag(Tag(26));
            write_site(writer, at)?;
        },
        Refusal::AbsentTupleComponent(at) => {
            writer.tag(Tag(39));
            write_site(writer, at)?;
        },
        Refusal::MissingRecordField { at, ref expected } => {
            writer.tag(Tag(27));
            write_site(writer, at)?;
            write_type(writer, expected)?;
        },
        Refusal::EffectSignatureConflict {
            at,
            ref first,
            ref second,
        } => {
            writer.tag(Tag(34));
            write_site(writer, at)?;
            write_type(writer, first)?;
            write_type(writer, second)?;
        },
        Refusal::UnknownOperation { at } => {
            writer.tag(Tag(35));
            write_site(writer, at)?;
        },
        Refusal::HandlerCoverage { at } => {
            writer.tag(Tag(36));
            write_site(writer, at)?;
        },
        Refusal::ShiftWithoutReset { at } => {
            writer.tag(Tag(37));
            write_site(writer, at)?;
        },
        Refusal::DependentStack {
            at,
            ref synthesised,
        } => {
            writer.tag(Tag(38));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
        },
        Refusal::PathCode(site) => {
            writer.tag(Tag(18));
            write_site(writer, site)?;
        },
        Refusal::EndpointMismatch { at, left, right } => {
            writer.tag(Tag(40));
            write_site(writer, at)?;
            write_site(writer, left)?;
            write_site(writer, right)?;
        },
        Refusal::CompoundEndpoint {
            at,
            ref synthesised,
        } => {
            writer.tag(Tag(42));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
        },
        Refusal::FunextUnsupported { at, ref classifier } => {
            writer.tag(Tag(43));
            write_site(writer, at)?;
            write_type(writer, classifier)?;
        },
        Refusal::PointwiseDistinct(site) => {
            writer.tag(Tag(44));
            write_site(writer, site)?;
        },
        Refusal::EquivUnsupported { at, ref classifier } => {
            writer.tag(Tag(45));
            write_site(writer, at)?;
            write_type(writer, classifier)?;
        },
        Refusal::UncertifiedStratum { at, ref code } => {
            writer.tag(Tag(46));
            write_site(writer, at)?;
            write_type(writer, code)?;
        },
        Refusal::RoundTripDistinct(site) => {
            writer.tag(Tag(47));
            write_site(writer, site)?;
        },
        Refusal::NotOver {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(52));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        Refusal::UaUncertified { at, stratum } => {
            writer.tag(Tag(53));
            write_site(writer, at)?;
            write_stratum_defect(writer, stratum)?;
        },
        Refusal::UaInequivalent { at, defect } => {
            writer.tag(Tag(54));
            write_site(writer, at)?;
            write_ua_defect(writer, defect)?;
        },
        Refusal::UnenclosedRun { at } => {
            writer.tag(Tag(55));
            write_site(writer, at)?;
        },
        Refusal::TypeMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(0));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        Refusal::ShapeMismatch {
            at,
            wanted,
            ref found,
        } => {
            writer.tag(Tag(1));
            write_site(writer, at)?;
            write_listed(writer, &SHAPES, &wanted)?;
            write_type(writer, found)?;
        },
        Refusal::NotSynthesisable { form } => {
            writer.tag(Tag(2));
            match form {
                Form::Reify(site) => {
                    writer.tag(Tag(9));
                    write_site(writer, site)?;
                },
                Form::Handle(site) => {
                    writer.tag(Tag(10));
                    write_site(writer, site)?;
                },
                Form::Reset(site) => {
                    writer.tag(Tag(11));
                    write_site(writer, site)?;
                },
                Form::Shift(site) => {
                    writer.tag(Tag(12));
                    write_site(writer, site)?;
                },
                Form::With(site) => {
                    writer.tag(Tag(13));
                    write_site(writer, site)?;
                },
                Form::List(site) => {
                    writer.tag(Tag(8));
                    write_site(writer, site)?;
                },
                Form::Injection(site) => {
                    writer.tag(Tag(5));
                    write_site(writer, site)?;
                },
                Form::Case(site) => {
                    writer.tag(Tag(6));
                    write_site(writer, site)?;
                },
                Form::Split(site) => {
                    writer.tag(Tag(14));
                    write_site(writer, site)?;
                },
                Form::Nested(site) => {
                    writer.tag(Tag(15));
                    write_site(writer, site)?;
                },
                Form::Thunk(site) => {
                    writer.tag(Tag(0));
                    write_site(writer, site)?;
                },
                Form::Lambda(site) => {
                    writer.tag(Tag(1));
                    write_site(writer, site)?;
                },
                Form::Return(site) => {
                    writer.tag(Tag(2));
                    write_site(writer, site)?;
                },
                Form::Hole => writer.tag(Tag(3)),
                Form::StaticLambda(site) => {
                    writer.tag(Tag(4));
                    write_site(writer, site)?;
                },
                Form::Fixpoint(site) => {
                    writer.tag(Tag(7));
                    write_site(writer, site)?;
                },
                Form::Offer(site) => {
                    writer.tag(Tag(16));
                    write_site(writer, site)?;
                },
                Form::Scope(site) => {
                    writer.tag(Tag(17));
                    write_site(writer, site)?;
                },
                Form::Run(site) => {
                    writer.tag(Tag(18));
                    write_site(writer, site)?;
                },
            }
        },
        Refusal::UnknownConstant { at, ref constant } => {
            writer.tag(Tag(3));
            write_site(writer, at)?;
            write_reference(writer, constant)?;
        },
        Refusal::OutOfFragment { at, former } => {
            writer.tag(Tag(4));
            write_site(writer, at)?;
            write_listed(writer, &FORMERS, &former)?;
        },
        Refusal::UnboundIndex {
            at,
            zone,
            index,
            depth,
        } => {
            writer.tag(Tag(5));
            write_site(writer, at)?;
            writer.tag(match zone {
                Zone::Intuitionistic => Tag(0),
                Zone::Linear => Tag(1),
            });
            writer.word(Word(u64::from(u32::from(index))));
            let depth = word_of(Count(usize::from(depth)))?;
            writer.word(depth);
        },
        Refusal::BudgetExceeded { budget } => {
            writer.tag(Tag(6));
            let budget = word_of(Count(usize::from(budget)))?;
            writer.word(budget);
        },
        Refusal::DanglingNode { at } => {
            writer.tag(Tag(7));
            write_site(writer, at)?;
        },
        Refusal::AdmissionOrder => writer.tag(Tag(8)),
        Refusal::MachineInvariant => writer.tag(Tag(9)),
        Refusal::SortMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(10));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        Refusal::LevelMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(11));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        Refusal::DependentBind {
            at,
            ref synthesised,
        } => {
            writer.tag(Tag(12));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
        },
        Refusal::Undecided { at } => {
            writer.tag(Tag(13));
            write_site(writer, at)?;
        },
        Refusal::FamilyArity {
            at,
            expected,
            actual,
        } => {
            writer.tag(Tag(14));
            write_site(writer, at)?;
            writer.word(Word(u64::from(u32::from(expected))));
            writer.word(Word(u64::from(u32::from(actual))));
        },
        Refusal::FamilyArgumentClassifier {
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
        Refusal::StaticLambdaArgument { at } => {
            writer.tag(Tag(16));
            write_site(writer, at)?;
        },
        Refusal::StaticClassifierExpected { at, ref found } => {
            writer.tag(Tag(17));
            write_site(writer, at)?;
            write_type(writer, found)?;
        },
        Refusal::NegativeOccurrence(site) => {
            writer.tag(Tag(28));
            write_occurrence_site(writer, site)?;
        },
        Refusal::NestedOccurrence(site) => {
            writer.tag(Tag(29));
            write_occurrence_site(writer, site)?;
        },
        Refusal::IndexOccurrence(site) => {
            writer.tag(Tag(30));
            write_occurrence_site(writer, site)?;
        },
        Refusal::NonUniformOccurrence(site) => {
            writer.tag(Tag(31));
            write_occurrence_site(writer, site)?;
        },
        Refusal::CrossBlockReference { site, ref index } => {
            writer.tag(Tag(32));
            write_occurrence_site(writer, site)?;
            write_reference(writer, index)?;
        },
        Refusal::StageNotBelow { at, found, bound } => {
            writer.tag(Tag(77));
            write_site(writer, at)?;
            write_standing(writer, found)?;
            write_stage(writer, bound)?;
        },
        Refusal::StagesDisagree { at, binder } => {
            writer.tag(Tag(83));
            write_site(writer, at)?;
            writer.count(Count(usize::from(binder)))?;
        },
        Refusal::SessionMismatch {
            at,
            endpoint,
            ref state,
            defect,
        } => {
            writer.tag(Tag(56));
            write_site(writer, at)?;
            write_endpoint(writer, endpoint)?;
            write_type(writer, state)?;
            match defect {
                ProtocolDefect::Action { expected, observed } => {
                    writer.tag(Tag(0));
                    write_listed(writer, &ACTIONS, &expected)?;
                    write_listed(writer, &ACTIONS, &observed)?;
                },
                ProtocolDefect::Label => writer.tag(Tag(1)),
                ProtocolDefect::Arms => writer.tag(Tag(2)),
            }
        },
        Refusal::Linearity { at, ref defect } => {
            writer.tag(Tag(57));
            write_site(writer, at)?;
            write_linearity(writer, defect)?;
        },
        Refusal::CapabilityForged { at, ref expected } => {
            writer.tag(Tag(58));
            write_site(writer, at)?;
            write_type(writer, expected)?;
        },
        Refusal::CapabilityAmplified {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(59));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        Refusal::CapabilityOutsideAuthority { at, ref capability } => {
            writer.tag(Tag(60));
            write_site(writer, at)?;
            write_type(writer, capability)?;
        },
        Refusal::CapabilityEscaped { at, ref found } => {
            writer.tag(Tag(61));
            write_site(writer, at)?;
            write_type(writer, found)?;
        },
        Refusal::CapabilityConsumable(at) => {
            writer.tag(Tag(62));
            write_site(writer, at)?;
        },
        Refusal::CapabilityUngranted(declared) => {
            writer.tag(Tag(63));
            write_site(writer, declared)?;
        },
        Refusal::SessionNotEquivalent(at) => {
            writer.tag(Tag(64));
            write_site(writer, at)?;
        },
        Refusal::SessionNotSubtype(at) => {
            writer.tag(Tag(65));
            write_site(writer, at)?;
        },
        Refusal::SessionCodeExpected(at) => {
            writer.tag(Tag(66));
            write_site(writer, at)?;
        },
        Refusal::NonCovariantMotive(at) => {
            writer.tag(Tag(67));
            write_site(writer, at)?;
        },
        Refusal::RideUnsupported(at) => {
            writer.tag(Tag(68));
            write_site(writer, at)?;
        },
        Refusal::RunNotAdmitted { at, fault } => {
            writer.tag(Tag(69));
            write_site(writer, at)?;
            let (kind, step) = match fault {
                RunFault::WrongDirection(step) => (0, step),
                RunFault::WrongLabel(step) => (1, step),
                RunFault::ResumeAfterEnd(step) => (2, step),
                RunFault::Incomplete(step) => (3, step),
                RunFault::OfferNarrowed => (4, RunStep::from(0_u32)),
            };
            writer.tag(Tag(kind));
            writer.word(Word(u64::from(u32::from(step))));
        },
        Refusal::ForwardUnsupported(at) => {
            writer.tag(Tag(70));
            write_site(writer, at)?;
        },
        Refusal::Boundary(at) => {
            writer.tag(Tag(71));
            write_site(writer, at)?;
        },
        Refusal::Access { at, defect } => {
            writer.tag(Tag(76));
            write_site(writer, at)?;
            let (kind, by) = match defect {
                AccessDefect::NotHeld => (0, None),
                AccessDefect::Lent => (1, None),
                AccessDefect::HeldCaptured { by } => (2, Some(by)),
                AccessDefect::Escaped { by } => (3, Some(by)),
                AccessDefect::Unended => (4, None),
                AccessDefect::Spent => (5, None),
                AccessDefect::NotAView => (6, None),
                AccessDefect::UnwindEffect => (7, None),
                AccessDefect::ReadOnly => (8, None),
                AccessDefect::Unindexed => (9, None),
                AccessDefect::HeldShared => (10, None),
                AccessDefect::HeldCopied => (11, None),
                AccessDefect::Moved => (12, None),
                AccessDefect::Kept => (13, None),
                AccessDefect::KeptEscaped => (14, None),
            };
            writer.tag(Tag(kind));
            if let Some(by) = by {
                write_listed(writer, &CAPTURES, &by)?;
            }
        },
        Refusal::Codata { at, fault } => {
            writer.tag(Tag(82));
            write_site(writer, at)?;
            writer.tag(Tag(match fault {
                CodataFault::Undeclared => 0,
                CodataFault::KindNotUniverse => 1,
                CodataFault::WithoutObservations => 2,
                CodataFault::Occurrence => 3,
                CodataFault::ObservationLevel => 4,
                CodataFault::Arity => 5,
            }));
        },
        Refusal::Located { at, ref defect } => {
            writer.tag(Tag(79));
            write_site(writer, at)?;
            write_located(writer, defect)?;
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
/// - witness: `codec::tests::every_refusal_round_trips_under_its_own_encoding`
/// - witness: `codec::tests::an_offer_narrowed_fault_is_read_only_at_step_zero`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref refusal) => {
            reader.bytes.get(before)
                == Some(&match *refusal {
                    Refusal::NotADataType(_) => 19,
                    Refusal::DataKindNotUniverse(_) => 20,
                    Refusal::DataFieldLevel {..} => 21,
                    Refusal::RuleNotPresentable {..} => 72,
                    Refusal::RuleNotRespected {..} => 73,
                    Refusal::NotApart {..} => 74,
                    Refusal::LoopNotRespected {..} => 75,
                    Refusal::LoopUndecided {..} => 78,
                    Refusal::DataArgumentArity(_) => 22,
                    Refusal::UnknownConstructor {..} => 23,
                    Refusal::ConstructorArity(_) => 24,
                    Refusal::IndexedCase(_) => 81,
                    Refusal::NonExhaustiveDataCase(_) => 25,
                    Refusal::UndecidedCoverage(_) => 80,
                    Refusal::AbsentRecordField(_) => 26,
                    Refusal::MissingRecordField {..} => 27,
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
                    | Refusal::NegativeOccurrence(_) => 28,
                    | Refusal::NestedOccurrence(_) => 29,
                    | Refusal::IndexOccurrence(_) => 30,
                    | Refusal::NonUniformOccurrence(_) => 31,
                    | Refusal::CrossBlockReference { .. } => 32,
                    | Refusal::StageNotBelow { .. } => 77,
                    | Refusal::StagesDisagree { .. } => 83,
                    | Refusal::EffectSignatureConflict { .. } => 34,
                    | Refusal::UnknownOperation { .. } => 35,
                    | Refusal::HandlerCoverage { .. } => 36,
                    | Refusal::ShiftWithoutReset { .. } => 37,
                    | Refusal::DependentStack { .. } => 38,
                    | Refusal::AbsentTupleComponent(_) => 39,
                    | Refusal::EndpointMismatch { .. } => 40,
                    | Refusal::CompoundEndpoint { .. } => 42,
                    | Refusal::FunextUnsupported { .. } => 43,
                    | Refusal::PointwiseDistinct(_) => 44,
                    | Refusal::EquivUnsupported { .. } => 45,
                    | Refusal::UncertifiedStratum { .. } => 46,
                    | Refusal::RoundTripDistinct(_) => 47,
                    | Refusal::AbstractKindNotUniverse(_) => 48,
                    | Refusal::RepresentationAboveKind { .. } => 49,
                    | Refusal::NotAnAbstractType(_) => 50,
                    | Refusal::SealSiteRepeated(_) => 51,
                    | Refusal::NotOver { .. } => 52,
                    | Refusal::UaUncertified { .. } => 53,
                    | Refusal::UaInequivalent { .. } => 54,
                    | Refusal::UnenclosedRun { .. } => 55,
                    | Refusal::SessionMismatch { .. } => 56,
                    | Refusal::Linearity { .. } => 57,
                    | Refusal::CapabilityForged { .. } => 58,
                    | Refusal::CapabilityAmplified { .. } => 59,
                    | Refusal::CapabilityOutsideAuthority { .. } => 60,
                    | Refusal::CapabilityEscaped { .. } => 61,
                    | Refusal::CapabilityConsumable(_) => 62,
                    | Refusal::CapabilityUngranted(_) => 63,
                    | Refusal::SessionNotEquivalent(_) => 64,
                    | Refusal::SessionNotSubtype(_) => 65,
                    | Refusal::SessionCodeExpected(_) => 66,
                    | Refusal::NonCovariantMotive(_) => 67,
                    | Refusal::RideUnsupported(_) => 68,
                    | Refusal::RunNotAdmitted { .. } => 69,
                    | Refusal::ForwardUnsupported(_) => 70,
                    | Refusal::Boundary(_) => 71,
                    | Refusal::Access { .. } => 76,
                    | Refusal::Codata { .. } => 82,
                    | Refusal::Located { .. } => 79,
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
        19 => Refusal::NotADataType(read_reference(reader)?),
        20 => Refusal::DataKindNotUniverse(read_site(reader)?),
        21 => Refusal::DataFieldLevel {
            field: read_site(reader)?,
            kind: read_type(reader)?,
        },
        72 => {
            let kind = read_site(reader)?;
            let rule = gandr_kernel_term::RuleIndex::from(reader.count()?.0);
            let fault = read_listed(reader, &RULE_FAULTS)?;
            Refusal::RuleNotPresentable {
                kind,
                refusal: gandr_kernel_term::RuleRefusal { rule, fault },
            }
        },
        73 => Refusal::RuleNotRespected {
            at: read_site(reader)?,
            rule: gandr_kernel_term::RuleIndex::from(reader.count()?.0),
        },
        74 => Refusal::NotApart {
            at: read_site(reader)?,
            reason: read_apartness(reader)?,
        },
        75 => Refusal::LoopNotRespected {
            at: read_site(reader)?,
            cell: gandr_kernel_term::CellIndex::from(reader.count()?.0),
            reason: match reader.tag()?.0 {
                0 => gandr_core_checker::LoopRespect::Apart,
                1 => gandr_core_checker::LoopRespect::NotPresentedSet,
                _ => return Err(CodecError::Corrupt),
            },
        },
        78 => Refusal::LoopUndecided {
            at: read_site(reader)?,
            cell: gandr_kernel_term::CellIndex::from(reader.count()?.0),
        },
        22 => Refusal::DataArgumentArity(read_site(reader)?),
        23 => Refusal::UnknownConstructor {
            at: read_site(reader)?,
            tag: gandr_core_term::ConstructorTag::from(reader.count()?.0),
        },
        24 => Refusal::ConstructorArity(read_site(reader)?),
        81 => Refusal::IndexedCase(read_site(reader)?),
        25 => Refusal::NonExhaustiveDataCase(read_site(reader)?),
        80 => Refusal::UndecidedCoverage(read_site(reader)?),
        26 => Refusal::AbsentRecordField(read_site(reader)?),
        39 => Refusal::AbsentTupleComponent(read_site(reader)?),
        27 => Refusal::MissingRecordField {
            at: read_site(reader)?,
            expected: read_type(reader)?,
        },
        48 => Refusal::AbstractKindNotUniverse(read_site(reader)?),
        49 => Refusal::RepresentationAboveKind {
            representation: read_site(reader)?,
            kind: read_type(reader)?,
        },
        50 => Refusal::NotAnAbstractType(read_reference(reader)?),
        51 => {
            let sealing = gandr_core_checker::SealingSite::from(reader.count()?.0);
            let component = gandr_core_checker::ComponentOrdinal::from(reader.count()?.0);
            Refusal::SealSiteRepeated(gandr_core_checker::SealSite::new(sealing, component))
        },
        0 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::TypeMismatch {
                at,
                synthesised,
                expected,
            }
        },
        1 => {
            let at = read_site(reader)?;
            let wanted = read_listed(reader, &SHAPES)?;
            let found = read_type(reader)?;
            Refusal::ShapeMismatch { at, wanted, found }
        },
        2 => {
            let form = reader.tag()?;
            let form = match form.0 {
                0 => {
                    let site = read_site(reader)?;
                    Form::Thunk(site)
                },
                1 => {
                    let site = read_site(reader)?;
                    Form::Lambda(site)
                },
                2 => {
                    let site = read_site(reader)?;
                    Form::Return(site)
                },
                3 => Form::Hole,
                4 => {
                    let site = read_site(reader)?;
                    Form::StaticLambda(site)
                },
                5 => Form::Injection(read_site(reader)?),
                6 => Form::Case(read_site(reader)?),
                7 => Form::Fixpoint(read_site(reader)?),
                8 => Form::List(read_site(reader)?),
                9 => Form::Reify(read_site(reader)?),
                10 => Form::Handle(read_site(reader)?),
                11 => Form::Reset(read_site(reader)?),
                12 => Form::Shift(read_site(reader)?),
                13 => Form::With(read_site(reader)?),
                14 => Form::Split(read_site(reader)?),
                15 => Form::Nested(read_site(reader)?),
                16 => Form::Offer(read_site(reader)?),
                17 => Form::Scope(read_site(reader)?),
                18 => Form::Run(read_site(reader)?),
                _ => return Err(CodecError::Corrupt),
            };
            Refusal::NotSynthesisable { form }
        },
        3 => {
            let at = read_site(reader)?;
            let constant = read_reference(reader)?;
            Refusal::UnknownConstant { at, constant }
        },
        4 => {
            let at = read_site(reader)?;
            let former = read_listed(reader, &FORMERS)?;
            Refusal::OutOfFragment { at, former }
        },
        5 => {
            let at = read_site(reader)?;
            let zone = reader.tag()?;
            let zone = match zone.0 {
                0 => Zone::Intuitionistic,
                1 => Zone::Linear,
                _ => return Err(CodecError::Corrupt),
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
        6 => {
            let budget = reader.count()?;
            Refusal::BudgetExceeded {
                budget: CheckBudget::from(budget.0),
            }
        },
        7 => {
            let at = read_site(reader)?;
            Refusal::DanglingNode { at }
        },
        8 => Refusal::AdmissionOrder,
        9 => Refusal::MachineInvariant,
        10 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::SortMismatch {
                at,
                synthesised,
                expected,
            }
        },
        11 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::LevelMismatch {
                at,
                synthesised,
                expected,
            }
        },
        12 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            Refusal::DependentBind { at, synthesised }
        },
        13 => {
            let at = read_site(reader)?;
            Refusal::Undecided { at }
        },
        14 => {
            let at = read_site(reader)?;
            let expected: StaticArity = read_narrow(reader)?;
            let actual: StaticArity = read_narrow(reader)?;
            Refusal::FamilyArity {
                at,
                expected,
                actual,
            }
        },
        15 => {
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
        16 => {
            let at = read_site(reader)?;
            Refusal::StaticLambdaArgument { at }
        },
        17 => {
            let at = read_site(reader)?;
            let found = read_type(reader)?;
            Refusal::StaticClassifierExpected { at, found }
        },
        18 => Refusal::PathCode(read_site(reader)?),
        40 => Refusal::EndpointMismatch {
            at: read_site(reader)?,
            left: read_site(reader)?,
            right: read_site(reader)?,
        },
        42 => Refusal::CompoundEndpoint {
            at: read_site(reader)?,
            synthesised: read_type(reader)?,
        },
        43 => Refusal::FunextUnsupported {
            at: read_site(reader)?,
            classifier: read_type(reader)?,
        },
        44 => Refusal::PointwiseDistinct(read_site(reader)?),
        45 => Refusal::EquivUnsupported {
            at: read_site(reader)?,
            classifier: read_type(reader)?,
        },
        46 => Refusal::UncertifiedStratum {
            at: read_site(reader)?,
            code: read_type(reader)?,
        },
        47 => Refusal::RoundTripDistinct(read_site(reader)?),
        52 => Refusal::NotOver {
            at: read_site(reader)?,
            synthesised: read_type(reader)?,
            expected: read_type(reader)?,
        },
        53 => Refusal::UaUncertified {
            at: read_site(reader)?,
            stratum: read_stratum_defect(reader)?,
        },
        54 => Refusal::UaInequivalent {
            at: read_site(reader)?,
            defect: read_ua_defect(reader)?,
        },
        55 => Refusal::UnenclosedRun {
            at: read_site(reader)?,
        },
        56 => {
            let at = read_site(reader)?;
            let endpoint = read_endpoint(reader)?;
            let state = read_type(reader)?;
            let defect = match reader.tag()?.0 {
                0 => ProtocolDefect::Action {
                    expected: read_listed(reader, &ACTIONS)?,
                    observed: read_listed(reader, &ACTIONS)?,
                },
                1 => ProtocolDefect::Label,
                2 => ProtocolDefect::Arms,
                _ => return Err(CodecError::Corrupt),
            };
            Refusal::SessionMismatch {
                at,
                endpoint,
                state,
                defect,
            }
        },
        57 => Refusal::Linearity {
            at: read_site(reader)?,
            defect: read_linearity(reader)?,
        },
        58 => Refusal::CapabilityForged {
            at: read_site(reader)?,
            expected: read_type(reader)?,
        },
        59 => Refusal::CapabilityAmplified {
            at: read_site(reader)?,
            synthesised: read_type(reader)?,
            expected: read_type(reader)?,
        },
        60 => Refusal::CapabilityOutsideAuthority {
            at: read_site(reader)?,
            capability: read_type(reader)?,
        },
        61 => Refusal::CapabilityEscaped {
            at: read_site(reader)?,
            found: read_type(reader)?,
        },
        62 => Refusal::CapabilityConsumable(read_site(reader)?),
        63 => Refusal::CapabilityUngranted(read_site(reader)?),
        64 => Refusal::SessionNotEquivalent(read_site(reader)?),
        65 => Refusal::SessionNotSubtype(read_site(reader)?),
        66 => Refusal::SessionCodeExpected(read_site(reader)?),
        67 => Refusal::NonCovariantMotive(read_site(reader)?),
        68 => Refusal::RideUnsupported(read_site(reader)?),
        70 => Refusal::ForwardUnsupported(read_site(reader)?),
        71 => Refusal::Boundary(read_site(reader)?),
        76 => {
            let at = read_site(reader)?;
            let defect = match reader.tag()?.0 {
                0 => AccessDefect::NotHeld,
                1 => AccessDefect::Lent,
                2 => AccessDefect::HeldCaptured {
                    by: read_listed(reader, &CAPTURES)?,
                },
                3 => AccessDefect::Escaped {
                    by: read_listed(reader, &CAPTURES)?,
                },
                4 => AccessDefect::Unended,
                5 => AccessDefect::Spent,
                6 => AccessDefect::NotAView,
                7 => AccessDefect::UnwindEffect,
                8 => AccessDefect::ReadOnly,
                9 => AccessDefect::Unindexed,
                10 => AccessDefect::HeldShared,
                11 => AccessDefect::HeldCopied,
                12 => AccessDefect::Moved,
                13 => AccessDefect::Kept,
                14 => AccessDefect::KeptEscaped,
                _ => return Err(CodecError::NonCanonical),
            };
            Refusal::Access { at, defect }
        },
        82 => {
            let at = read_site(reader)?;
            let fault = match reader.tag()?.0 {
                0 => CodataFault::Undeclared,
                1 => CodataFault::KindNotUniverse,
                2 => CodataFault::WithoutObservations,
                3 => CodataFault::Occurrence,
                4 => CodataFault::ObservationLevel,
                5 => CodataFault::Arity,
                _ => return Err(CodecError::NonCanonical),
            };
            Refusal::Codata { at, fault }
        },
        79 => Refusal::Located {
            at: read_site(reader)?,
            defect: read_located(reader)?,
        },
        69 => {
            let at = read_site(reader)?;
            let kind = reader.tag()?.0;
            let step = RunStep::from(
                u32::try_from(reader.word()?.0).map_err(|_cause| CodecError::Corrupt)?,
            );
            let fault = match kind {
                0 => RunFault::WrongDirection(step),
                1 => RunFault::WrongLabel(step),
                2 => RunFault::ResumeAfterEnd(step),
                3 => RunFault::Incomplete(step),
                4 if u32::from(step) == 0 => RunFault::OfferNarrowed,
                _ => return Err(CodecError::NonCanonical),
            };
            Refusal::RunNotAdmitted { at, fault }
        },
        28 => Refusal::NegativeOccurrence(read_occurrence_site(reader)?),
        29 => Refusal::NestedOccurrence(read_occurrence_site(reader)?),
        30 => Refusal::IndexOccurrence(read_occurrence_site(reader)?),
        31 => Refusal::NonUniformOccurrence(read_occurrence_site(reader)?),
        32 => {
            let site = read_occurrence_site(reader)?;
            let index = read_reference(reader)?;
            Refusal::CrossBlockReference { site, index }
        },
        77 => {
            let at = read_site(reader)?;
            let found = read_standing(reader)?;
            let bound = read_stage(reader)?;
            Refusal::StageNotBelow { at, found, bound }
        },
        83 => Refusal::StagesDisagree {
            at: read_site(reader)?,
            binder: gandr_kernel_term::StageBinder::from(reader.count()?.0),
        },
        34 => Refusal::EffectSignatureConflict {
            at: read_site(reader)?,
            first: read_type(reader)?,
            second: read_type(reader)?,
        },
        35 => Refusal::UnknownOperation {
            at: read_site(reader)?,
        },
        36 => Refusal::HandlerCoverage {
            at: read_site(reader)?,
        },
        37 => Refusal::ShiftWithoutReset {
            at: read_site(reader)?,
        },
        38 => Refusal::DependentStack {
            at: read_site(reader)?,
            synthesised: read_type(reader)?,
        },
        _ => return Err(CodecError::Corrupt),
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
/// - hypothesis: L3 — checked, synthesised, owed, suspended and selected
///   refused verdicts round-trip. Malformed synthesised and refused payloads
///   distinguish their failure paths; the predicate classifies type-plane
///   failures rather than reproducing the byte encoding.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::a_suspended_typing_round_trips`
/// - witness: `codec::tests::checkpoint_encoding_reports_the_first_unresolved_plane`
#[spec(
    ensures: |ret| match *typing {
        | Typing::Data | Typing::Owed | Typing::Suspended => ret == Ok(()),
        | Typing::Checked { conversions } => {
            ret == u64::try_from(usize::from(conversions))
                .map(|_| ())
                .map_err(|_overflow| CodecError::Unrepresentable)
        },
        | _ => {
            let tables: [&[SupportedNode]; 2] = match *typing {
                | Typing::Synthesised { ref produced, .. } => [produced.nodes(), &[]],
                | Typing::Refused(ref refusal) => match *refusal {
            Refusal::DataFieldLevel {kind:ref found,..} | Refusal::RepresentationAboveKind {kind:ref found,..} | Refusal::MissingRecordField {expected:ref found,..} => [found.nodes(),&[]],
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
                    | Refusal::SessionMismatch {
                        state: ref found, ..
                    }
                    | Refusal::Linearity {
                        defect: Linearity::Residue {
                            state: ref found, ..
                        },
                        ..
                    }
                    | Refusal::StaticClassifierExpected { ref found, .. } => {
                        [found.nodes(), &[]]
                    },
                    | Refusal::DependentBind {
                        ref synthesised, ..
                    } => [synthesised.nodes(), &[]],
                    | Refusal::Located { defect: Located::Immobile { ref ty, ref former, .. }, .. } => [ty.nodes(), former.nodes()],
                    | Refusal::Located { defect: Located::MarkUnfounded { ref former, .. } | Located::NotAHandle { found: ref former }, .. } => [former.nodes(), &[]],
                    | _ => [&[], &[]],
                },
                | Typing::Data | Typing::Checked { .. } | Typing::Owed | Typing::Suspended => [&[], &[]],
            };
            match ret {
                | Ok(()) => tables
                    .into_iter()
                    .flatten()
                    .all(|node| !matches!(*node.former(), ContentNode::Unresolved(_))),
                | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
                    tables.into_iter().flatten().find_map(|node| match *node.former() {
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
        Typing::Data => writer.tag(Tag(4)),
        Typing::Checked { conversions } => {
            writer.tag(Tag(0));
            writer.count(Count(usize::from(conversions)))?;
        },
        Typing::Synthesised {
            ref produced,
            conversions,
        } => {
            writer.tag(Tag(1));
            write_type(writer, produced)?;
            writer.count(Count(usize::from(conversions)))?;
        },
        Typing::Owed => writer.tag(Tag(2)),
        Typing::Suspended => writer.tag(Tag(5)),
        Typing::Refused(ref refusal) => {
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
/// - hypothesis: L3 — checked, synthesised, owed, suspended and selected
///   refused verdicts preserve their payloads. Tag classification is
///   executable; this finite corpus does not witness every malformed field. An
///   unknown outer tag stops before the available payload.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::a_suspended_typing_round_trips`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        | Ok(ref typing) => {
            reader.bytes.get(before)
                == Some(&match *typing {
                    Typing::Data => 4,
                    | Typing::Checked { .. } => 0,
                    | Typing::Synthesised { .. } => 1,
                    | Typing::Owed => 2,
                    | Typing::Suspended => 5,
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
        4 => Ok(Typing::Data),
        0 => {
            let conversions = reader.count()?;
            Ok(Typing::Checked {
                conversions: ConversionCount::from(conversions.0),
            })
        },
        1 => {
            let produced = read_type(reader)?;
            let conversions = reader.count()?;
            Ok(Typing::Synthesised {
                produced,
                conversions: ConversionCount::from(conversions.0),
            })
        },
        2 => Ok(Typing::Owed),
        5 => Ok(Typing::Suspended),
        3 => {
            let refusal = read_refusal(reader)?;
            Ok(Typing::Refused(refusal))
        },
        _ => Err(CodecError::Corrupt),
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
    ensures: |ret| match ret {
        Ok(()) => answer.nodes().iter().all(|node| !matches!(*node.former(),ContentNode::Unresolved(_))),
        Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => answer.nodes().iter().find_map(|node| match *(node.former()) {
ContentNode::Unresolved(ref found) => Some(*found),
ContentNode::Univalence(..) | ContentNode::ListCase { .. } |
ContentNode::Data { .. } | ContentNode::RecordType(_) | ContentNode::Constructor { .. } | ContentNode::Record(_) | ContentNode::DataCase { .. } | ContentNode::RecordProjection(..) | ContentNode::TupleProjection(..) | ContentNode::Reify(_) | ContentNode::Stack { .. } | ContentNode::WithType(..) | ContentNode::Perform { .. } | ContentNode::Handle { .. } | ContentNode::Exercise { .. } | ContentNode::Scope { .. } | ContentNode::Capability { .. } | ContentNode::Resume(..) | ContentNode::Split(..) | ContentNode::DependentSplit { .. } | ContentNode::Reset(_) | ContentNode::Shift(_) | ContentNode::With(..) | ContentNode::Ascribe { .. } | ContentNode::Project(..) | ContentNode::PrimitiveValue(_) | ContentNode::Primitive(..) | ContentNode::PathUniverse(..) | ContentNode::PathRefl(_) | ContentNode::PathProduct(..) | ContentNode::Funext(..) | ContentNode::Equiv(..) | ContentNode::Ua { .. } | ContentNode::PathEquiv { .. } | ContentNode::Transport(..) | ContentNode::PathType { .. } | ContentNode::Here(_) | ContentNode::Returned(_) | ContentNode::Nested(_) | ContentNode::Run(_) | ContentNode::ElementTransport { .. } | ContentNode::TelescopeTransport { .. } | ContentNode::SessionRelated { .. } | ContentNode::Stay(_) | ContentNode::Then(..) | ContentNode::Forward(_) | ContentNode::FunctionFlow(..) | ContentNode::FlowProduct(..) | ContentNode::Recorded(_) | ContentNode::Ride { .. } | ContentNode::FlowType { .. } | ContentNode::RunType(_) | ContentNode::Variable { .. } | ContentNode::Constant(_) | ContentNode::Literal(_) | ContentNode::Tuple(_) | ContentNode::ListNil | ContentNode::ListCons(..) | ContentNode::Injection(..) | ContentNode::Thunk(_) | ContentNode::ValueLift { .. } | ContentNode::Quote(_) | ContentNode::QuoteComputation(_) | ContentNode::StaticLambda(_) | ContentNode::StaticApplication(..) | ContentNode::Hole(_) | ContentNode::ValueMark { .. } | ContentNode::Lambda(_) | ContentNode::Application(..) | ContentNode::Return(_) | ContentNode::Bind(..) | ContentNode::Force(_) | ContentNode::Case { .. } | ContentNode::ComputationHole(_) | ContentNode::ComputationMark { .. } | ContentNode::Fixpoint { .. } | ContentNode::ListFold { .. } | ContentNode::Session(_) | ContentNode::Memory(_) | ContentNode::Base(_) | ContentNode::Product(_) | ContentNode::Sum(_) | ContentNode::List(_) | ContentNode::KeptType { .. } | ContentNode::ThunkType(_) | ContentNode::Universe { .. } | ContentNode::TypeLift { .. } | ContentNode::Element { .. } | ContentNode::StaticPi { .. } | ContentNode::Sigma { .. } | ContentNode::SessionType(_) | ContentNode::Abstract(_) | ContentNode::UnknownType | ContentNode::BufferType | ContentNode::Returner { .. } | ContentNode::Arrow { .. } | ContentNode::Pi { .. } | ContentNode::ComputationElement { .. } | ContentNode::UnknownComputationType => None
}) == Some(sort),
        Err(CodecError::Unrepresentable) => true,
        _ => false,
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
        Answer::Data(None) => writer.tag(Tag(2)),
        Answer::Data(Some(ref signature)) => {
            writer.tag(Tag(3));
            write_data_content(writer, signature)?;
        },
        Answer::Untyped => writer.tag(Tag(0)),
        Answer::Codata => writer.tag(Tag(4)),
        Answer::Typed(ref ty) => {
            writer.tag(Tag(1));
            write_type(writer, ty)?;
        },
    }
    Ok(())
}

/// Read an answer.
///
/// # Specification
/// - ensures: tags zero and one retain absent and present value-signature
///   answers; tags two and three retain absent and complete data signatures;
///   tag four retains a codata answer.
///
/// # Adequacy
/// - hypothesis: L3 — persisted support contains structured typed answers and
///   preserves them on decoding. The predicate checks tag and root class, not
///   provenance from a checker. An unknown outer tag stops before the available
///   payload.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `codec::tests::decoders_reject_unknown_tags_before_payloads`
/// - witness: `codec::tests::every_footprint_stance_and_answer_round_trips`
#[spec(
    captures: [before = reader.cursor],
    ensures: |ret| match ret {
        Ok(Answer::Data(None)) => reader.bytes.get(before) == Some(&2),
        Ok(Answer::Data(Some(_))) => reader.bytes.get(before) == Some(&3),
        | Ok(Answer::Untyped) => reader.bytes.get(before) == Some(&0),
        | Ok(Answer::Codata) => reader.bytes.get(before) == Some(&4),
        | Ok(Answer::Typed(ref ty)) => {
            reader.bytes.get(before) == Some(&1)
                && matches!(
                    ty.nodes().first().map(SupportedNode::sort),
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
        2 => Ok(Answer::Data(None)),
        3 => Ok(Answer::Data(Some(read_data_content(reader)?))),
        0 => Ok(Answer::Untyped),
        4 => Ok(Answer::Codata),
        1 => {
            let ty = read_type(reader)?;
            Ok(Answer::Typed(ty))
        },
        _ => Err(CodecError::Corrupt),
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
        let tables: [&[SupportedNode]; 2] = match *typing {
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
                Refusal::DataFieldLevel {kind:ref found,..} | Refusal::RepresentationAboveKind {kind:ref found,..} | Refusal::MissingRecordField {expected:ref found,..} | Refusal::ShapeMismatch { ref found, .. }
                | Refusal::SessionMismatch { state: ref found, .. } | Refusal::Linearity { defect: Linearity::Residue { state: ref found, .. }, .. }
                | Refusal::StaticClassifierExpected { ref found, .. } => [found.nodes(), &[]],
                | Refusal::DependentBind {
                    ref synthesised, ..
                } => [synthesised.nodes(), &[]],
                | Refusal::Located { defect: Located::Immobile { ref ty, ref former, .. }, .. } => [ty.nodes(), former.nodes()],
                | Refusal::Located { defect: Located::MarkUnfounded { ref former, .. } | Located::NotAHandle { found: ref former }, .. } => [former.nodes(), &[]],
                | _ => [&[], &[]],
            },
            | Typing::Data | Typing::Checked { .. } | Typing::Owed | Typing::Suspended => [&[], &[]],
        };
        let support =
            checkpoint
                .support()
                .iter()
                .flat_map(|answered| answered.answer().nodes());
        let mut nodes = checkpoint
            .content()
            .nodes()
            .iter()
            .chain(support)
            .chain(tables.into_iter().flatten());
        match ret {
            | Ok(()) => checkpoint.content().locus() == crate::content::Locus::Unlocated
                && nodes.all(|node| !matches!(*node.former(), ContentNode::Unresolved(_))),
            | Err(CodecError::Unsupported(UnsupportedPersistence::Located)) => {
                checkpoint.content().locus() == crate::content::Locus::Located
            },
            | Err(CodecError::Unsupported(UnsupportedPersistence::Codata)) => {
                matches!(*checkpoint.content().declaration(), crate::content::DeclarationRoots::Codata)
            },
            | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
                nodes.find_map(|node| match *node.former() {
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
                    .all(|(first,second)| (first.reference(),first.answer().consultation()) < (second.reference(),second.answer().consultation()))
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
        | Ok(()) => checkpoint.content().nodes().iter().all(|node| match *node.former() {
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
        Typing::Synthesised { ref produced, .. } => [Some(produced), None],
        Typing::Refused(ref refusal) => match *refusal {
            Refusal::TypeMismatch {
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
            Refusal::DataFieldLevel {
                kind: ref found, ..
            }
            | Refusal::RepresentationAboveKind {
                kind: ref found, ..
            }
            | Refusal::MissingRecordField {
                expected: ref found,
                ..
            }
            | Refusal::ShapeMismatch { ref found, .. }
            | Refusal::SessionMismatch {
                state: ref found, ..
            }
            | Refusal::Linearity {
                defect:
                    Linearity::Residue {
                        state: ref found, ..
                    },
                ..
            }
            | Refusal::StaticClassifierExpected { ref found, .. } => [Some(found), None],
            Refusal::DependentBind {
                ref synthesised, ..
            } => [Some(synthesised), None],
            Refusal::Located {
                defect:
                    Located::Immobile {
                        ref ty, ref former, ..
                    },
                ..
            } => [Some(ty), Some(former)],
            Refusal::Located {
                defect:
                    Located::MarkUnfounded { ref former, .. }
                    | Located::NotAHandle { found: ref former },
                ..
            } => [Some(former), None],
            Refusal::NotADataType(_)
            | Refusal::DataKindNotUniverse(_)
            | Refusal::RuleNotPresentable { .. }
            | Refusal::RuleNotRespected { .. }
            | Refusal::NotApart { .. }
            | Refusal::LoopNotRespected { .. }
            | Refusal::LoopUndecided { .. }
            | Refusal::DataArgumentArity(_)
            | Refusal::UnknownConstructor { .. }
            | Refusal::ConstructorArity(_)
            | Refusal::IndexedCase(_)
            | Refusal::NonExhaustiveDataCase(_)
            | Refusal::UndecidedCoverage(_)
            | Refusal::AbsentRecordField(_)
            | Refusal::AbsentTupleComponent(_)
            | Refusal::UnknownOperation { .. }
            | Refusal::HandlerCoverage { .. }
            | Refusal::ShiftWithoutReset { .. }
            | Refusal::DependentStack { .. }
            | Refusal::PathCode(_)
            | Refusal::EndpointMismatch { .. }
            | Refusal::CompoundEndpoint { .. }
            | Refusal::FunextUnsupported { .. }
            | Refusal::PointwiseDistinct(_)
            | Refusal::EquivUnsupported { .. }
            | Refusal::UncertifiedStratum { .. }
            | Refusal::RoundTripDistinct(_)
            | Refusal::NotOver { .. }
            | Refusal::UaUncertified { .. }
            | Refusal::UaInequivalent { .. }
            | Refusal::NotSynthesisable { .. }
            | Refusal::UnknownConstant { .. }
            | Refusal::OutOfFragment { .. }
            | Refusal::UnboundIndex { .. }
            | Refusal::BudgetExceeded { .. }
            | Refusal::DanglingNode { .. }
            | Refusal::AdmissionOrder
            | Refusal::MachineInvariant
            | Refusal::Undecided { .. }
            | Refusal::FamilyArity { .. }
            | Refusal::StaticLambdaArgument { .. }
            | Refusal::NegativeOccurrence(_)
            | Refusal::NestedOccurrence(_)
            | Refusal::IndexOccurrence(_)
            | Refusal::NonUniformOccurrence(_)
            | Refusal::CrossBlockReference { .. }
            | Refusal::StageNotBelow { .. }
            | Refusal::StagesDisagree { .. }
            | Refusal::EffectSignatureConflict { .. }
            | Refusal::AbstractKindNotUniverse(_)
            | Refusal::NotAnAbstractType(_)
            | Refusal::SealSiteRepeated(_)
            | Refusal::UnenclosedRun { .. }
            | Refusal::Linearity { .. }
            | Refusal::CapabilityForged { .. }
            | Refusal::CapabilityAmplified { .. }
            | Refusal::CapabilityOutsideAuthority { .. }
            | Refusal::CapabilityEscaped { .. }
            | Refusal::CapabilityConsumable(_)
            | Refusal::CapabilityUngranted(_)
            | Refusal::SessionNotEquivalent(_)
            | Refusal::SessionNotSubtype(_)
            | Refusal::SessionCodeExpected(_)
            | Refusal::NonCovariantMotive(_)
            | Refusal::RideUnsupported(_)
            | Refusal::RunNotAdmitted { .. }
            | Refusal::ForwardUnsupported(_)
            | Refusal::Boundary(_)
            | Refusal::Access { .. }
            | Refusal::Codata { .. }
            | Refusal::Located { .. } => [None, None],
        },
        Typing::Data | Typing::Checked { .. } | Typing::Owed | Typing::Suspended => [None, None],
    };
    let support = checkpoint
        .support()
        .iter()
        .map(|answered| answered.answer().nodes());
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
        }) = *node.former()
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
/// - fails: [`CodecError::Unsupported`] naming a located item, a codata
///   declaration, or the first unresolved node met.
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
        | Ok(()) => contents.iter().map(Borrow::borrow).all(|content: &ItemContent| content.locus() == crate::content::Locus::Unlocated)
            && contents
                .iter()
                .map(Borrow::borrow)
                .flat_map(ItemContent::nodes)
                .all(|node| !matches!(*node.former(), ContentNode::Unresolved(_))),
        | Err(CodecError::Unsupported(UnsupportedPersistence::Located)) => {
            contents.iter().map(Borrow::borrow).any(|content: &ItemContent| content.locus() == crate::content::Locus::Located)
        },
        | Err(CodecError::Unsupported(UnsupportedPersistence::Codata)) => {
            contents.iter().map(Borrow::borrow).any(|content: &ItemContent| matches!(*content.declaration(), crate::content::DeclarationRoots::Codata))
        },
        | Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(sort))) => {
            contents
                .iter()
                .map(Borrow::borrow)
                .flat_map(ItemContent::nodes)
                .find_map(|node| match *node.former() {
                    | ContentNode::Unresolved(found) => Some(found),
                    | _ => None,
                })
                == Some(sort)
        },
        | Err(CodecError::Unrepresentable) => true,
        | _ => false,
    },
)]
pub fn write_program<Out, Content>(
    sink: &mut Out,
    contents: &[Content],
) -> Result<(), CodecError>
where
    Out: Sink,
    Content: Borrow<ItemContent>,
{
    let mut writer = Writer { sink };
    writer.sink.put(Bytes(PROGRAM_MAGIC));
    writer.count(Count(contents.len()))?;
    for content in contents {
        write_item_content_with(&mut writer, content.borrow())?;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
