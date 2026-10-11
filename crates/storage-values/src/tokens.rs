//! The canonical token stream: what a value emits, and what a body holds.
//!
//! A value walks its own structure in preorder and announces constructor entry
//! and exit to a [`TokenSink`]; the sink owns the framing and, when it
//! commits, the cut decision. Nothing about a value's Rust representation
//! reaches the bytes: only constructor tags, canonical words, canonical byte
//! payloads and already-committed child pointers do.
//!
//! # Why entry and exit rather than a flat token list
//!
//! A boundary event needs the residue of the subtree the boundary closes, so
//! something has to know where a subtree ends. Making the value announce exit
//! puts that knowledge where it already exists — in the walk — and lets the
//! sink keep one subtree start per open constructor without inspecting the
//! value.
//!
//! # The token body layout, which is a format rather than an implementation detail
//!
//! A body is a sequence of token records, each opening with a one-byte kind.
//! A [`crate::ContentPtr`]'s offset counts records from zero at the start of
//! the body.
//!
//! ```text
//! record := 0x01 open  || u8 tag
//!         | 0x02 word  || u64le value
//!         | 0x03 bytes || u64le length || length bytes
//!         | 0x04 child || 32-byte chunk digest || u32le token offset
//!         | 0x05 close
//! ```
//!
//! Every integer is little-endian at a fixed width. No kind byte outside
//! `0x01..=0x05` is admitted: an unknown kind in a content-addressed body is a
//! corrupted or foreign body, never a forward-compatible extension, because
//! the digest already committed to every byte.
//!
//! The kind byte is separate from the tag byte so a word whose leading byte
//! happens to be a valid tag cannot read as a constructor, and the close
//! record carries no tag because the nesting is balanced and the reader tracks
//! its own depth: a repeated tag would be a second copy of a fact, free to
//! disagree with the first.
//!
//! # The tag vocabulary is not this crate's
//!
//! Which tags exist, their arities and their meaning belong to the value's own
//! codec, committed as its [`crate::CodecIdentity`]. This module carries the
//! transport of tags and takes no position on what they mean.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::error::EmissionFault;
use crate::error::ValueError;
use crate::error::ValueQuantity;
use crate::ptr::CHUNK_DIGEST_LEN;
use crate::ptr::ChunkDigest;
use crate::ptr::ContentPtr;
use crate::ptr::TokenOffset;
use crate::reader::TokenReader;
use crate::units::CanonicalWord;
use crate::units::FlatBytes;
use crate::units::TokenBody;
use crate::units::TokenBytes;

/// Record kind byte: a constructor opens.
const KIND_OPEN: u8 = 0x01_u8;
/// Record kind byte: a canonical payload word.
const KIND_WORD: u8 = 0x02_u8;
/// Record kind byte: a length-prefixed inline byte payload.
const KIND_BYTES: u8 = 0x03_u8;
/// Record kind byte: a reference to an already-committed child chunk.
const KIND_CHILD: u8 = 0x04_u8;
/// Record kind byte: the innermost open constructor closes.
const KIND_CLOSE: u8 = 0x05_u8;

/// The kinds of token record a body holds.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TokenKind
{
    /// A constructor opens.
    Open,
    /// A canonical payload word.
    Word,
    /// A length-prefixed inline byte payload.
    Bytes,
    /// A reference to an already-committed child chunk.
    Child,
    /// The innermost open constructor closes.
    Close,
}

impl fmt::Display for TokenKind
{
    /// Writes the kind as a refusal names it.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the kinds an unexpected-token refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on all five kinds observes pairwise distinct names and
    ///   exact first-write refusal, distinguishing collapsed kinds and
    ///   swallowed errors without pinning diagnostic wording.
    /// - witness: `tokens::tests::token_renderings_preserve_kind_and_tag_information`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Open => "an open record",
            | Self::Word => "a word record",
            | Self::Bytes => "a bytes record",
            | Self::Child => "a child record",
            | Self::Close => "a close record",
        })
    }
}

/// One constructor tag in a canonical token stream.
///
/// The newtype exists so a tag cannot be confused with a canonical word or a
/// payload byte at the framing boundary, which is the one confusion the
/// encoder cannot otherwise catch.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstructorTag(u8);

impl From<u8> for ConstructorTag
{
    /// Reads a byte as a constructor tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: u8) -> Self
    {
        Self(tag)
    }
}

impl From<ConstructorTag> for u8
{
    /// Reads the tag back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: ConstructorTag) -> Self
    {
        tag.0
    }
}

impl fmt::Display for ConstructorTag
{
    /// Writes the tag as two hexadecimal digits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes `0x` and the tag as two lowercase hexadecimal digits.
    /// - provides: the tag an unexpected-constructor refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 over all 256 tag bytes compares the prefixed, padded
    ///   hexadecimal image with the primitive formatter; L3 observes exact
    ///   first-write refusal. Missing prefixes, zero nibbles or tag bits are
    ///   distinguished; alternate formatter modes are outside this domain.
    /// - witness: `tokens::tests::token_renderings_preserve_kind_and_tag_information`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{:#04x}", self.0)
    }
}

/// The receiver of one value's canonical token stream.
///
/// A sink never sees the value; it sees the walk. Every sink this crate
/// provides refuses an emission that is not exactly one balanced value with
/// [`ValueError::MalformedEmission`].
///
/// # Specification
/// - requires: implementations account for one balanced root and preserve the
///   typed payloads offered by the codec.
/// - ensures: successful emission records that root's preorder token stream;
///   malformed nesting is refused by the provided sinks.
/// - provides: the common emission boundary for flat and chunked values.
/// - fails: the concrete method's typed shape, accounting or store refusal.
/// - panics: none.
/// - executable: none — instrumenting required trait methods adds required
///   hooks and associated constants, changing the implementor contract;
///   executable checks belong to the concrete sinks.
///
/// # Adequacy
/// - hypothesis: L2 on generated seven-shape trees of at most 4096 records,
///   with byte payloads through 300 bytes, compares spliced chunks with flat
///   bytes. L3 malformed scripts distinguish missing balance checks. These
///   witnesses cover the provided sinks, not every external implementation.
/// - witness: `tests::laws::chunking_is_invisible_to_the_flat_form`
/// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
pub trait TokenSink
{
    /// Announces entry into a constructor.
    ///
    /// # Specification
    /// - requires: every open is matched by a later close at the same depth,
    ///   and the value's root is the only constructor opened at depth zero.
    /// - ensures: the sink records one open token for `tag`.
    /// - provides: the preorder skeleton the boundaries are taken over.
    /// - fails: [`ValueError`] when the emission breaks the balanced shape or
    ///   the sink's own accounting or store refuses.
    /// - panics: none.
    /// - executable: none — a required declaration has no body; trait-level
    ///   instrumentation adds required implementor hooks. Concrete sinks carry
    ///   the executable state relations.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 on seven-shape generated values through 4096 records
    ///   observes flat round trips; L3 empty, unmatched-close, second-root and
    ///   unclosed scripts observe exact faults. Missing opens, changed tags and
    ///   lost balance checks are distinguished for the provided sinks.
    /// - witness: `tests::laws::every_generated_value_round_trips_flat`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    fn open(
        &mut self,
        tag: ConstructorTag,
    ) -> Result<(), ValueError>;

    /// Contributes one canonical payload word.
    ///
    /// # Specification
    /// - requires: a constructor is open.
    /// - ensures: the sink records one word token.
    /// - provides: the only integer width the framing admits.
    /// - fails: [`ValueError`], as [`TokenSink::open`].
    /// - panics: none.
    /// - executable: none — a required declaration has no body; trait-level
    ///   instrumentation adds required implementor hooks. Concrete sinks carry
    ///   the executable state relations.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 on generated seven-shape values with full-width words
    ///   observes decoded equality; L3 payload-before-open and payload-after-
    ///   root scripts observe the exact fault. This distinguishes lost words
    ///   and missing shape checks, not arbitrary external sink behavior.
    /// - witness: `tests::laws::every_generated_value_round_trips_flat`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    fn word(
        &mut self,
        word: CanonicalWord,
    ) -> Result<(), ValueError>;

    /// Contributes an inline canonical byte payload.
    ///
    /// # Specification
    /// - requires: a constructor is open; `bytes` is already canonical.
    /// - ensures: the sink records one length-prefixed bytes token.
    /// - provides: the escape for payloads that are not word-shaped.
    /// - fails: [`ValueError`], as [`TokenSink::open`].
    /// - panics: none.
    /// - executable: none — a required declaration has no body; trait-level
    ///   instrumentation adds required implementor hooks. Concrete sinks carry
    ///   the executable state relations.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 on generated seven-shape values of at most 4096 records
    ///   includes byte payloads of length 0 through 300 and observes decoded
    ///   equality. Missing or reordered payload bytes are distinguished for the
    ///   flat sink; arbitrary external sinks are not quantified.
    /// - witness: `tests::laws::every_generated_value_round_trips_flat`
    fn bytes(
        &mut self,
        bytes: TokenBytes<'_>,
    ) -> Result<(), ValueError>;

    /// Contributes an already-committed value by reference.
    ///
    /// # Specification
    /// - requires: a constructor is open; `pointer` addresses a chunk the store
    ///   the value will be read from already holds.
    /// - ensures: the sink records one child token carrying the pointer, which
    ///   stands for the value it addresses.
    /// - provides: the sharing edge of the chunk DAG, for a value that embeds
    ///   another already-committed value.
    /// - fails: [`ValueError`], as [`TokenSink::open`]; a flat sink refuses
    ///   every child, since a flat form has no store to resolve one against.
    /// - panics: none.
    /// - executable: none — a required declaration has no body; trait-level
    ///   instrumentation adds required implementor hooks. Concrete sinks carry
    ///   the executable state relations.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 on a depth-five embedded fixture observes its complete
    ///   decoded value; L3 on a child offered to the flat sink observes the
    ///   exact seam position. Lost references and admitted flat seams are
    ///   distinguished; missing-store and arbitrary sink cases are separate.
    /// - witness: `tests::values::an_embedded_pointer_reads_as_the_value_it_names`
    /// - witness: `tests::flat::a_child_record_is_refused_in_a_flat_form`
    fn child_pointer(
        &mut self,
        pointer: ContentPtr,
    ) -> Result<(), ValueError>;

    /// Announces exit from the innermost open constructor.
    ///
    /// # Specification
    /// - requires: a constructor is open.
    /// - ensures: the sink records one close token; a committing sink raises a
    ///   boundary event here.
    /// - provides: the boundary positions locality is about.
    /// - fails: [`ValueError`], as [`TokenSink::open`].
    /// - panics: none.
    /// - executable: none — a required declaration has no body; trait-level
    ///   instrumentation adds required implementor hooks. Concrete sinks carry
    ///   the executable state relations.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 on seven-shape generated values through 4096 records
    ///   observes reconstructed values; L3 unmatched-close and unclosed scripts
    ///   observe exact faults. Omitted closes and missing balance checks are
    ///   distinguished for the provided sinks, not external implementations.
    /// - witness: `tests::laws::every_generated_value_round_trips_flat`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    fn close(&mut self) -> Result<(), ValueError>;
}

/// A value that can be written to, and read back from, the canonical token
/// stream.
///
/// Decoding what a value emits must return an equal value. This round-trip
/// law gives a [`ContentPtr`] its meaning across codec calls.
///
/// # Specification
/// - requires: an implementation emits deterministically and decodes the token
///   language it emits.
/// - ensures: decoding an emitted value reconstructs an equal value.
/// - provides: the codec law that makes a content pointer name a value.
/// - fails: concrete methods propagate typed sink or reader refusals.
/// - panics: none.
/// - executable: none — the law relates two effectful codec calls without an
///   equality bound on Self; trait instrumentation also adds required hooks.
///   Concrete codecs carry the checks their representation supports.
///
/// # Adequacy
/// - hypothesis: L2 on generated seven-shape trees through 4096 records, with
///   full-width words and byte payloads through 300 bytes, observes equality
///   after flat and chunked round trips. Lost payloads, reordered children and
///   seam leakage are distinguished for these codecs, not all implementors.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
/// - witness: `tests::laws::every_generated_value_commits_and_derefs_back_equal`
pub trait CanonicalValue: Sized
{
    /// Walks this value in preorder, announcing it to `sink`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the walk emitted exactly one balanced value: one
    ///   root constructor, every open closed.
    /// - provides: the producer half of the codec.
    /// - fails: [`ValueError`] propagated from the sink.
    /// - panics: none.
    /// - executable: none — a required declaration has no body; instrumenting
    ///   the trait changes its required hooks. The generic codec also has no
    ///   equality bound with which to replay the round-trip law.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 on generated seven-shape trees through 4096 records
    ///   observes equality after flat and chunked round trips, distinguishing
    ///   lost payloads, reordered children and leaked seams. This is bounded
    ///   evidence for the test codecs, not every external implementation.
    /// - witness: `tests::laws::every_generated_value_round_trips_flat`
    /// - witness: `tests::laws::every_generated_value_commits_and_derefs_back_equal`
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized;

    /// Reads one value from the canonical token stream.
    ///
    /// # Specification
    /// - requires: `reader` is positioned at this value's root constructor.
    /// - ensures: on success the reader is positioned immediately after the
    ///   value's closing record; chunk seams are crossed by the reader, so a
    ///   value read back is not told which chunks it spanned.
    /// - provides: the consumer half of the codec.
    /// - fails: [`ValueError`] on an unexpected record or constructor, a
    ///   truncated stream, a chunk the store cannot answer for, or a spent
    ///   decode budget.
    /// - panics: none.
    /// - executable: none — a required declaration has no body; instrumenting
    ///   the trait changes its required hooks. The generic codec also has no
    ///   equality bound with which to replay the round-trip law.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 on generated seven-shape trees through 4096 records
    ///   observes equality after flat and chunked round trips, distinguishing
    ///   lost payloads, reordered children and leaked seams. This is bounded
    ///   evidence for the test codecs, not every external implementation.
    /// - witness: `tests::laws::every_generated_value_round_trips_flat`
    /// - witness: `tests::laws::every_generated_value_commits_and_derefs_back_equal`
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>;
}

/// One token record, decoded or about to be written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Record<'body>
{
    /// A constructor opens.
    Open(ConstructorTag),
    /// A canonical payload word.
    Word(CanonicalWord),
    /// An inline byte payload.
    Bytes(TokenBytes<'body>),
    /// A reference to an already-committed child chunk.
    Child(ContentPtr),
    /// The innermost open constructor closes.
    Close,
}

impl Record<'_>
{
    /// Returns the record's kind.
    ///
    /// # Specification
    /// - requires: nothing; every record variant is admitted.
    /// - ensures: returns the kind corresponding to this record's variant.
    /// - provides: the discriminator used by readers to refuse a wrong kind.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on independent wire images for all five kinds observes
    ///   decoded records and their exact kind; empty and nonempty byte payloads
    ///   are separate cases. Swapped or collapsed kinds are distinguished, not
    ///   every possible payload.
    /// - witness: `tokens::tests::every_record_round_trips_through_the_grammar`
    #[spec(ensures: |ret| matches!((self, ret),
        (&Self::Open(_), TokenKind::Open)
        | (&Self::Word(_), TokenKind::Word)
        | (&Self::Bytes(_), TokenKind::Bytes)
        | (&Self::Child(_), TokenKind::Child)
        | (&Self::Close, TokenKind::Close)
    ))]
    pub(crate) const fn kind(&self) -> TokenKind
    {
        match *self {
            | Self::Open(_) => TokenKind::Open,
            | Self::Word(_) => TokenKind::Word,
            | Self::Bytes(_) => TokenKind::Bytes,
            | Self::Child(_) => TokenKind::Child,
            | Self::Close => TokenKind::Close,
        }
    }
}

/// Why the front of a body is not a well-formed record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecordFault
{
    /// The body ends inside the record.
    Truncated,
    /// The kind byte names no token kind.
    UnknownKind,
}

/// The front of a body: nothing left, or one record and the rest.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BodyFront<'body>
{
    /// The body is exhausted.
    Empty,
    /// One record, and the body after it.
    Record(Record<'body>, TokenBody<'body>),
}

/// Reads one record off the front of a body.
///
/// # Specification
/// - requires: nothing; every malformed front is a named fault.
/// - ensures: [`BodyFront::Empty`] for an empty body; otherwise the record the
///   layout in this module's documentation says the leading bytes encode, and
///   exactly the bytes after it.
/// - provides: the one grammar every reader of a body shares — the reader, the
///   frame verifier and the flat decoder cannot disagree on a record.
/// - fails: [`RecordFault::UnknownKind`] for a kind byte outside `0x01..=0x05`,
///   and [`RecordFault::Truncated`] when the body ends inside the record or a
///   declared payload length exceeds the bytes that remain.
/// - panics: none.
///
/// # Errors
/// [`RecordFault`] — the leading bytes are not one well-formed record.
///
/// # Adequacy
/// - hypothesis: L2 on independent wire images for every kind, including empty
///   and nonempty bytes, observes decoded payloads and a retained suffix. L3
///   covers every reserved kind byte, every proper nonempty prefix of the fixed
///   images, and an oversized byte length. Wrong kinds, endianness, consumed
///   lengths and fault classes are distinguished on that domain.
/// - witness: `tokens::tests::every_record_round_trips_through_the_grammar`
/// - witness: `tokens::tests::a_short_or_unknown_record_is_a_named_fault`
#[spec(ensures: |ret| match ret {
    Ok(BodyFront::Empty) => body.as_ref().is_empty(),
    Ok(BodyFront::Record(record, rest)) => {
        let consumed = match record {
            Record::Open(_) => Some(2),
            Record::Word(_) => Some(9),
            Record::Bytes(payload) => payload.as_ref().len().checked_add(9),
            Record::Child(_) => Some(37),
            Record::Close => Some(1),
        };
        consumed.is_some_and(|length| body.as_ref().get(length..).is_some_and(|suffix|
            rest.as_ref().len() == suffix.len()
                && core::ptr::eq(rest.as_ref().as_ptr(), suffix.as_ptr())))
            && matches!((body.as_ref().first(), record.kind()),
                (Some(&KIND_OPEN), TokenKind::Open)
                | (Some(&KIND_WORD), TokenKind::Word)
                | (Some(&KIND_BYTES), TokenKind::Bytes)
                | (Some(&KIND_CHILD), TokenKind::Child)
                | (Some(&KIND_CLOSE), TokenKind::Close))
    },
    Err(RecordFault::UnknownKind) => body.as_ref().first().is_some_and(|kind| !(KIND_OPEN..=KIND_CLOSE).contains(kind)),
    Err(RecordFault::Truncated) => matches!(body.as_ref().first(), Some(&(KIND_OPEN | KIND_WORD | KIND_BYTES | KIND_CHILD))),
})]
pub(crate) fn split_record(body: TokenBody<'_>) -> Result<BodyFront<'_>, RecordFault>
{
    let bytes: &[u8] = body.into();
    let Some((&kind, rest)) = bytes.split_first()
    else {
        return Ok(BodyFront::Empty);
    };

    let (record, rest) = match kind {
        | KIND_OPEN => {
            let Some((&tag, rest)) = rest.split_first()
            else {
                return Err(RecordFault::Truncated);
            };
            (Record::Open(ConstructorTag(tag)), rest)
        },
        | KIND_WORD => {
            let Some((word, rest)) = rest.split_first_chunk::<8>()
            else {
                return Err(RecordFault::Truncated);
            };
            (
                Record::Word(CanonicalWord::from(u64::from_le_bytes(*word))),
                rest,
            )
        },
        | KIND_BYTES => {
            let Some((length, rest)) = rest.split_first_chunk::<8>()
            else {
                return Err(RecordFault::Truncated);
            };
            let Ok(length) = usize::try_from(u64::from_le_bytes(*length))
            else {
                return Err(RecordFault::Truncated);
            };
            let Some((payload, rest)) = rest.split_at_checked(length)
            else {
                return Err(RecordFault::Truncated);
            };
            (Record::Bytes(TokenBytes::from(payload)), rest)
        },
        | KIND_CHILD => {
            let Some((digest, rest)) = rest.split_first_chunk::<CHUNK_DIGEST_LEN>()
            else {
                return Err(RecordFault::Truncated);
            };
            let Some((offset, rest)) = rest.split_first_chunk::<4>()
            else {
                return Err(RecordFault::Truncated);
            };
            let pointer = ContentPtr::new(
                ChunkDigest::from(*digest),
                TokenOffset::from(u32::from_le_bytes(*offset)),
            );
            (Record::Child(pointer), rest)
        },
        | KIND_CLOSE => (Record::Close, rest),
        | _ => return Err(RecordFault::UnknownKind),
    };

    Ok(BodyFront::Record(record, TokenBody::from(rest)))
}

/// A byte position in a body under construction.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct BodyMark(usize);

/// A token body under construction, shared by the committing traversal and
/// the flat encoder so both write one byte language.
///
/// # Specification
/// - requires: subtree marks originate at record boundaries in this writer.
/// - ensures: the current bytes form a sequence of well-formed records; pushes
///   append records and truncation preserves the preceding bytes.
/// - provides: the byte history from which subtree bodies are borrowed.
/// - fails: push names an unrepresentable payload length.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on independent images for each kind observes the full
///   appended sequence. L3 saved marks, nested suffixes and truncation observe
///   retained prefixes and borrowed views, distinguishing overwritten history,
///   wrong slice starts and over-truncation. Arbitrary histories are not
///   proved.
/// - witness: `tokens::tests::every_record_round_trips_through_the_grammar`
/// - witness: `tokens::tests::body_marks_preserve_prefixes_and_suffixes`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[spec(maintains: {
    let mut remaining = TokenBody::from(self.0.as_slice());
    loop {
        match split_record(remaining) {
            Ok(BodyFront::Empty) => break true,
            Ok(BodyFront::Record(_, rest)) => remaining = rest,
            Err(_) => break false,
        }
    }
})]
pub(crate) struct BodyWriter(Vec<u8>);

impl BodyWriter
{
    /// Appends one record in the layout this module documents.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the record's bytes are appended and nothing
    ///   already appended changes; [`split_record`] reads them back as the same
    ///   record.
    /// - provides: the one place a record becomes bytes.
    /// - fails: [`ValueError::ArithmeticOverflow`] when a payload's length does
    ///   not fit sixty-four bits.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::ArithmeticOverflow`] — a payload length exceeds `u64`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on independent images for all five kinds, including
    ///   empty bytes, observes the whole appended sequence and the decoded
    ///   payload. Wrong tags, byte order, lengths and overwritten prefixes are
    ///   distinguished. A slice longer than u64 is not allocatable on the
    ///   supported widths, so that conversion refusal is not executed.
    /// - witness: `tokens::tests::every_record_round_trips_through_the_grammar`
    #[spec(
        captures: entry = self.mark(),
        ensures: |ret| match ret {
            Ok(()) => matches!(split_record(self.since(entry)),
                Ok(BodyFront::Record(read, rest)) if read == record && rest.as_ref().is_empty()),
            Err(ValueError::ArithmeticOverflow { quantity: ValueQuantity::ByteLength }) =>
                self.mark() == entry && matches!(record, Record::Bytes(payload) if u64::try_from(payload.as_ref().len()).is_err()),
            Err(_) => false,
        },
    )]
    pub(crate) fn push(
        &mut self,
        record: Record<'_>,
    ) -> Result<(), ValueError>
    {
        match record {
            | Record::Open(tag) => {
                self.0.push(KIND_OPEN);
                self.0.push(tag.0);
            },
            | Record::Word(word) => {
                self.0.push(KIND_WORD);
                self.0
                    .extend_from_slice(u64::from(word).to_le_bytes().as_slice());
            },
            | Record::Bytes(payload) => {
                let Ok(length) = u64::try_from(payload.as_ref().len())
                else {
                    return Err(ValueError::ArithmeticOverflow {
                        quantity: ValueQuantity::ByteLength,
                    });
                };
                self.0.push(KIND_BYTES);
                self.0.extend_from_slice(length.to_le_bytes().as_slice());
                self.0.extend_from_slice(payload.as_ref());
            },
            | Record::Child(pointer) => {
                self.0.push(KIND_CHILD);
                self.0.extend_from_slice(pointer.digest().as_ref());
                self.0
                    .extend_from_slice(u32::from(pointer.offset()).to_le_bytes().as_slice());
            },
            | Record::Close => self.0.push(KIND_CLOSE),
        }

        Ok(())
    }

    /// Returns the position the next record will start at.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn mark(&self) -> BodyMark
    {
        BodyMark(self.0.len())
    }

    /// Borrows the bytes from `mark` to the end.
    ///
    /// # Specification
    /// - requires: `mark` came from [`BodyWriter::mark`] on this writer and no
    ///   truncation has passed it.
    /// - ensures: the bytes appended since `mark`, or an empty body when the
    ///   mark lies past the end.
    /// - provides: the subtree a cut frames and a residue hashes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on marks at the start, between records and at the end
    ///   observes exact suffix bytes and source-slice identity, distinguishing
    ///   wrong starts, truncated tails and copied views. The witness uses marks
    ///   admitted by the stated same-writer precondition.
    /// - witness: `tokens::tests::body_marks_preserve_prefixes_and_suffixes`
    #[spec(ensures: |ret| {
        let suffix = self.0.get(mark.0..).unwrap_or_default();
        ret.as_ref().len() == suffix.len()
            && core::ptr::eq(ret.as_ref().as_ptr(), suffix.as_ptr())
    })]
    pub(crate) fn since(
        &self,
        mark: BodyMark,
    ) -> TokenBody<'_>
    {
        TokenBody::from(self.0.get(mark.0 ..).unwrap_or_default())
    }

    /// Drops every byte from `mark` to the end.
    ///
    /// # Specification
    /// - requires: mark originated at a record boundary in this writer.
    /// - ensures: retains exactly the prefix before mark; a mark beyond the
    ///   current end leaves the body unchanged.
    /// - provides: replacement of a completed subtree by its child record.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on saved boundary marks, including a later mark after
    ///   an earlier truncation, observes complete retained bytes and exact
    ///   lengths. Wrong truncation points, cleared prefixes and growth are
    ///   distinguished on these finite histories.
    /// - witness: `tokens::tests::body_marks_preserve_prefixes_and_suffixes`
    #[spec(captures: before = self.0.len(),
        ensures: self.0.len() == before.min(mark.0))]
    pub(crate) fn truncate(
        &mut self,
        mark: BodyMark,
    )
    {
        self.0.truncate(mark.0);
    }

    /// Borrows the whole body.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn as_body(&self) -> TokenBody<'_>
    {
        TokenBody::from(self.0.as_slice())
    }

    /// Closes the writer into an owned flat form.
    ///
    /// # Specification
    /// - requires: nothing; balance is checked by the caller, not this move.
    /// - ensures: returns the accumulated bytes unchanged in an owned buffer.
    /// - provides: ownership transfer to the flat encoder's result.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the independent concatenated record images and L3 on
    ///   a truncated body observes every returned byte. The predicate checks
    ///   length and endpoints without copying the source buffer; the witnesses
    ///   distinguish changes to interior bytes on their bounded inputs.
    /// - witness: `tokens::tests::every_record_round_trips_through_the_grammar`
    /// - witness: `tokens::tests::body_marks_preserve_prefixes_and_suffixes`
    #[spec(
        requires: anodized::types::Spec::predicate(&self),
        captures: entry = (self.0.len(), self.0.first().copied(), self.0.last().copied()),
        ensures: |ret| ret.as_ref().len() == entry.0
            && ret.as_ref().first().copied() == entry.1
            && ret.as_ref().last().copied() == entry.2,
    )]
    pub(crate) fn into_flat(self) -> FlatBytes
    {
        FlatBytes::from(self.0.into_boxed_slice())
    }
}

/// Where an emission stands in the one-balanced-value shape.
///
/// # Specification
/// - requires: an inside state carries a positive open depth.
/// - ensures: admitted opens and closes preserve positive depth until the
///   outermost close makes the state complete; refusals preserve the state.
/// - provides: the balance state shared by every concrete sink.
/// - fails: the transition methods name the shape or arithmetic refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on empty, complete, depths one and two, and the width
///   boundary observes exact transitions, faults and preserved refusal states.
///   It distinguishes incorrect phase changes, depth steps and wraparound, not
///   every possible transition sequence.
/// - witness: `tokens::tests::emission_transitions_preserve_depth_and_refusal_state`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[spec(maintains: match *self {
    Self::Inside(ref depth) => anodized::types::Spec::predicate(depth),
    Self::Empty | Self::Complete => true,
})]
pub(crate) enum EmissionShape
{
    /// Nothing has been emitted.
    Empty,
    /// Inside the root, this many constructors deep.
    Inside(OpenDepth),
    /// The root has closed.
    Complete,
}

/// How many constructors are open, at least one.
///
/// # Specification
/// - requires: the constructor count is positive.
/// - ensures: the carried depth denotes at least one open constructor.
/// - provides: the positive-depth arm of the emission state.
/// - fails: never at this data declaration; open checks width overflow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on depths one, two and the width boundary observes exact
///   successor, predecessor and root closure states. Zero creation and wrapped
///   depth are distinguished on those transitions; arbitrary histories are
///   outside this finite boundary matrix.
/// - witness: `tokens::tests::emission_transitions_preserve_depth_and_refusal_state`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[spec(maintains: self.0 > 0)]
pub(crate) struct OpenDepth(usize);

/// Whether a close ended the root or an inner constructor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Closing
{
    /// An inner constructor closed; the root is still open.
    Inner,
    /// The root closed.
    Root,
}

impl EmissionShape
{
    /// Accounts an open, refusing a second root.
    ///
    /// # Specification
    /// - requires: an inside state carries a positive open depth.
    /// - ensures: on success one constructor deeper than before.
    /// - provides: the shape check every sink runs before writing an open.
    /// - fails: [`ValueError::MalformedEmission`] with
    ///   [`EmissionFault::SecondRoot`] after the root closed, or an overflow
    ///   refusal at the width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — the open breaks the shape.
    ///
    /// # Adequacy
    /// - hypothesis: L3 from empty, complete, depth one and the last two depths
    ///   observes exact resulting states and typed failures. Skipped
    ///   increments, wraparound, a second root and mutation on refusal are
    ///   distinguished; interior positive depths are not exhaustive.
    /// - witness: `tokens::tests::emission_transitions_preserve_depth_and_refusal_state`
    #[spec(
        maintains: anodized::types::Spec::predicate(self),
        captures: entry = *self,
        ensures: |ret| match entry {
            Self::Empty => ret == Ok(()) && *self == Self::Inside(OpenDepth(1)),
            Self::Complete => ret == Err(ValueError::MalformedEmission { fault: EmissionFault::SecondRoot }) && *self == entry,
            Self::Inside(OpenDepth(depth)) => depth.checked_add(1).map_or_else(
                || ret == Err(ValueError::ArithmeticOverflow { quantity: ValueQuantity::TokenCount }) && *self == entry,
                |deeper| ret == Ok(()) && *self == Self::Inside(OpenDepth(deeper)),
            ),
        },
    )]
    pub(crate) fn open(&mut self) -> Result<(), ValueError>
    {
        *self = match *self {
            | Self::Empty => Self::Inside(OpenDepth(1_usize)),
            | Self::Inside(OpenDepth(depth)) => {
                let Some(deeper) = depth.checked_add(1_usize)
                else {
                    return Err(ValueError::ArithmeticOverflow {
                        quantity: ValueQuantity::TokenCount,
                    });
                };
                Self::Inside(OpenDepth(deeper))
            },
            | Self::Complete => {
                return Err(ValueError::MalformedEmission {
                    fault: EmissionFault::SecondRoot,
                });
            },
        };

        Ok(())
    }

    /// Refuses a payload or child outside every constructor.
    ///
    /// # Specification
    /// - requires: an inside state carries a positive open depth.
    /// - ensures: success exactly when a constructor is open.
    /// - provides: the shape check before a word, bytes or child record.
    /// - fails: [`ValueError::MalformedEmission`] with
    ///   [`EmissionFault::PayloadOutsideConstructor`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — no constructor is open.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on empty, depth one and complete observes exact
    ///   admission or the payload-outside-constructor fault. It distinguishes
    ///   admission in either outer phase and a substituted fault; other depths
    ///   do not introduce another phase decision.
    /// - witness: `tokens::tests::emission_transitions_preserve_depth_and_refusal_state`
    #[spec(
        requires: anodized::types::Spec::predicate(&self),
        ensures: |ret| match self {
            Self::Inside(_) => ret == Ok(()),
            Self::Empty | Self::Complete => ret == Err(ValueError::MalformedEmission { fault: EmissionFault::PayloadOutsideConstructor }),
        },
    )]
    pub(crate) fn payload(self) -> Result<(), ValueError>
    {
        match self {
            | Self::Inside(_) => Ok(()),
            | Self::Empty | Self::Complete => Err(ValueError::MalformedEmission {
                fault: EmissionFault::PayloadOutsideConstructor,
            }),
        }
    }

    /// Accounts a close, reporting whether it ended the root.
    ///
    /// # Specification
    /// - requires: an inside state carries a positive open depth.
    /// - ensures: on success one constructor shallower, and [`Closing::Root`]
    ///   exactly when that leaves none open.
    /// - provides: the shape check before a close, and the signal that the
    ///   outermost close is not a cut candidate.
    /// - fails: [`ValueError::MalformedEmission`] with
    ///   [`EmissionFault::CloseWithoutOpen`] when none is open.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — no constructor is open.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on empty, complete and depths one, two and the ceiling
    ///   observes exact predecessor states, root/inner outcomes and refusal
    ///   preservation. It distinguishes premature root closure, narrowed
    ///   subtraction and state mutation on refusal, not every interior depth.
    /// - witness: `tokens::tests::emission_transitions_preserve_depth_and_refusal_state`
    #[spec(
        maintains: anodized::types::Spec::predicate(self),
        captures: entry = *self,
        ensures: |ret| match entry {
            Self::Empty | Self::Complete => ret == Err(ValueError::MalformedEmission { fault: EmissionFault::CloseWithoutOpen }) && *self == entry,
            Self::Inside(OpenDepth(depth)) => match depth.checked_sub(1) {
                Some(0) => ret == Ok(Closing::Root) && *self == Self::Complete,
                Some(shallower) => ret == Ok(Closing::Inner) && *self == Self::Inside(OpenDepth(shallower)),
                None => false,
            },
        },
    )]
    pub(crate) fn close(&mut self) -> Result<Closing, ValueError>
    {
        let Self::Inside(OpenDepth(depth)) = *self
        else {
            return Err(ValueError::MalformedEmission {
                fault: EmissionFault::CloseWithoutOpen,
            });
        };

        let (shape, closing) = match depth.checked_sub(1_usize) {
            | Some(0_usize) | None => (Self::Complete, Closing::Root),
            | Some(shallower) => (Self::Inside(OpenDepth(shallower)), Closing::Inner),
        };
        *self = shape;

        Ok(closing)
    }

    /// Refuses an emission that did not produce exactly one closed value.
    ///
    /// # Specification
    /// - requires: an inside state carries a positive open depth.
    /// - ensures: success exactly when the root has closed.
    /// - provides: the final shape check every sink runs.
    /// - fails: [`ValueError::MalformedEmission`] with
    ///   [`EmissionFault::EmptyValue`] or
    ///   [`EmissionFault::UnclosedConstructor`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — the emission is empty or unclosed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on empty, depth one and complete observes the exact
    ///   empty-value or unclosed-constructor fault and completed admission. It
    ///   distinguishes phase collapse and swapped faults; no payload data or
    ///   arbitrary external sink behavior is inferred.
    /// - witness: `tokens::tests::emission_transitions_preserve_depth_and_refusal_state`
    #[spec(
        requires: anodized::types::Spec::predicate(&self),
        ensures: |ret| match self {
            Self::Complete => ret == Ok(()),
            Self::Empty => ret == Err(ValueError::MalformedEmission { fault: EmissionFault::EmptyValue }),
            Self::Inside(_) => ret == Err(ValueError::MalformedEmission { fault: EmissionFault::UnclosedConstructor }),
        },
    )]
    pub(crate) fn finish(self) -> Result<(), ValueError>
    {
        match self {
            | Self::Complete => Ok(()),
            | Self::Empty => Err(ValueError::MalformedEmission {
                fault: EmissionFault::EmptyValue,
            }),
            | Self::Inside(_) => Err(ValueError::MalformedEmission {
                fault: EmissionFault::UnclosedConstructor,
            }),
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;
    use alloc::vec::Vec;

    use anodized::spec;

    use super::BodyFront;
    use super::BodyWriter;
    use super::Closing;
    use super::ConstructorTag;
    use super::EmissionShape;
    use super::OpenDepth;
    use super::Record;
    use super::RecordFault;
    use super::TokenKind;
    use super::split_record;
    use crate::EmissionFault;
    use crate::ValueError;
    use crate::ValueQuantity;
    use crate::ptr::ChunkDigest;
    use crate::ptr::ContentPtr;
    use crate::ptr::TokenOffset;
    use crate::units::CanonicalWord;
    use crate::units::TokenBody;
    use crate::units::TokenBytes;

    /// A sink that refuses the first formatted write.
    #[derive(Debug)]
    struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuses every offered write.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: returns the formatting error.
        /// - provides: the token formatter's refusal observer.
        /// - fails: always returns the formatting error.
        /// - panics: none.
        ///
        /// # Errors
        /// Always returns the formatting error.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on all token kinds and tag bytes observes exact
        ///   refusal, distinguishing acceptance of a formatted write.
        /// - witness: `tokens::tests::token_renderings_preserve_kind_and_tag_information`
        #[spec(ensures: |ret| ret == Err(core::fmt::Error))]
        fn write_str(
            &mut self,
            _s: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn token_renderings_preserve_kind_and_tag_information()
    {
        let kinds = [
            TokenKind::Open,
            TokenKind::Word,
            TokenKind::Bytes,
            TokenKind::Child,
            TokenKind::Close,
        ];
        let rendered = kinds.map(|kind| kind.to_string());
        for (index, kind) in kinds.into_iter().enumerate() {
            assert!(!rendered[.. index].contains(&rendered[index]));
            assert_eq!(
                core::fmt::write(&mut RefusingSink, format_args!("{kind}")),
                Err(core::fmt::Error)
            );
        }
        for byte in u8::MIN ..= u8::MAX {
            let tag = ConstructorTag::from(byte);
            assert_eq!(tag.to_string(), alloc::format!("{byte:#04x}"));
            assert_eq!(
                core::fmt::write(&mut RefusingSink, format_args!("{tag}")),
                Err(core::fmt::Error)
            );
        }
    }

    #[test]
    fn every_record_round_trips_through_the_grammar()
    {
        let payload = [0xaa, 0xbb, 0xcc];
        let cases: [(Record<'_>, TokenKind, &[u8]); 6] = [
            (
                Record::Open(ConstructorTag::from(0x2a_u8)),
                TokenKind::Open,
                &[0x01, 0x2a],
            ),
            (
                Record::Word(CanonicalWord::from(0x0102_0304_0506_0708_u64)),
                TokenKind::Word,
                &[0x02, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01],
            ),
            (
                Record::Bytes(TokenBytes::from(payload.as_slice())),
                TokenKind::Bytes,
                &[0x03, 3, 0, 0, 0, 0, 0, 0, 0, 0xaa, 0xbb, 0xcc],
            ),
            (
                Record::Bytes(TokenBytes::from([].as_slice())),
                TokenKind::Bytes,
                &[0x03, 0, 0, 0, 0, 0, 0, 0, 0],
            ),
            (
                Record::Child(ContentPtr::new(
                    ChunkDigest::from([0x5a; 32]),
                    TokenOffset::from(0x0a0b_0c0d_u32),
                )),
                TokenKind::Child,
                &[
                    0x04, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a,
                    0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a,
                    0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x0d, 0x0c, 0x0b, 0x0a,
                ],
            ),
            (Record::Close, TokenKind::Close, &[0x05]),
        ];
        let mut writer = BodyWriter::default();
        let mut expected = Vec::new();
        for (record, kind, image) in cases {
            let mark = writer.mark();
            writer.push(record).expect("the record appends");
            expected.extend_from_slice(image);
            assert_eq!(writer.as_body().as_ref(), expected.as_slice());
            assert_eq!(writer.since(mark).as_ref(), image);
            assert_eq!(record.kind(), kind);
            assert_eq!(
                split_record(TokenBody::from(image)),
                Ok(BodyFront::Record(record, TokenBody::from([].as_slice())))
            );
            for end in 1 .. image.len() {
                assert_eq!(
                    split_record(TokenBody::from(&image[.. end])),
                    Err(RecordFault::Truncated)
                );
            }
            let mut followed = image.to_vec();
            followed.extend_from_slice(&[0x01, 0xa7]);
            assert_eq!(
                split_record(TokenBody::from(followed.as_slice())),
                Ok(BodyFront::Record(
                    record,
                    TokenBody::from([0x01, 0xa7].as_slice())
                ))
            );
        }
        assert_eq!(writer.into_flat().as_ref(), expected.as_slice());
    }

    #[test]
    fn a_short_or_unknown_record_is_a_named_fault()
    {
        for kind in u8::MIN ..= u8::MAX {
            if (0x01 ..= 0x05).contains(&kind) {
                continue;
            }
            assert_eq!(
                split_record(TokenBody::from([kind].as_slice())),
                Err(RecordFault::UnknownKind)
            );
        }
        assert_eq!(
            split_record(TokenBody::from([].as_slice())),
            Ok(BodyFront::Empty)
        );
        assert_eq!(
            split_record(TokenBody::from(
                [0x03, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xaa].as_slice()
            )),
            Err(RecordFault::Truncated),
        );
    }

    #[test]
    fn body_marks_preserve_prefixes_and_suffixes()
    {
        let mut writer = BodyWriter::default();
        let start = writer.mark();
        writer
            .push(Record::Open(ConstructorTag::from(0x2a_u8)))
            .expect("open");
        let opened = writer.mark();
        writer
            .push(Record::Word(CanonicalWord::from(0x0102_0304_0506_0708_u64)))
            .expect("word");
        let word_end = writer.mark();
        writer
            .push(Record::Bytes(TokenBytes::from([0xaa, 0xbb].as_slice())))
            .expect("bytes");
        writer.push(Record::Close).expect("close");
        let end = writer.mark();
        let expected = [
            0x01, 0x2a, 0x02, 8, 7, 6, 5, 4, 3, 2, 1, 0x03, 2, 0, 0, 0, 0, 0, 0, 0, 0xaa, 0xbb,
            0x05,
        ];
        let full = writer.as_body();
        for (mark, offset) in [(start, 0), (opened, 2), (word_end, 11), (end, 23)] {
            let suffix = writer.since(mark);
            assert_eq!(suffix.as_ref(), &expected[offset ..]);
            assert!(core::ptr::eq(
                suffix.as_ref().as_ptr(),
                full.as_ref()[offset ..].as_ptr()
            ));
        }
        writer.truncate(word_end);
        assert_eq!(writer.as_body().as_ref(), &expected[.. 11]);
        writer.truncate(end);
        assert_eq!(writer.as_body().as_ref(), &expected[.. 11]);
        writer.push(Record::Close).expect("replacement closes");
        assert_eq!(writer.since(opened).as_ref(), [
            0x02, 8, 7, 6, 5, 4, 3, 2, 1, 0x05
        ]);
        assert_eq!(writer.into_flat().as_ref(), [
            0x01, 0x2a, 0x02, 8, 7, 6, 5, 4, 3, 2, 1, 0x05
        ]);
    }

    #[test]
    fn emission_transitions_preserve_depth_and_refusal_state()
    {
        let openings = [
            (
                EmissionShape::Empty,
                Ok(()),
                EmissionShape::Inside(OpenDepth(1)),
            ),
            (
                EmissionShape::Inside(OpenDepth(1)),
                Ok(()),
                EmissionShape::Inside(OpenDepth(2)),
            ),
            (
                EmissionShape::Inside(OpenDepth(usize::MAX - 1)),
                Ok(()),
                EmissionShape::Inside(OpenDepth(usize::MAX)),
            ),
            (
                EmissionShape::Inside(OpenDepth(usize::MAX)),
                Err(ValueError::ArithmeticOverflow {
                    quantity: ValueQuantity::TokenCount,
                }),
                EmissionShape::Inside(OpenDepth(usize::MAX)),
            ),
            (
                EmissionShape::Complete,
                Err(ValueError::MalformedEmission {
                    fault: EmissionFault::SecondRoot,
                }),
                EmissionShape::Complete,
            ),
        ];
        for (mut state, outcome, after) in openings {
            assert_eq!(state.open(), outcome);
            assert_eq!(state, after);
        }
        let closings = [
            (
                EmissionShape::Empty,
                Err(ValueError::MalformedEmission {
                    fault: EmissionFault::CloseWithoutOpen,
                }),
                EmissionShape::Empty,
            ),
            (
                EmissionShape::Complete,
                Err(ValueError::MalformedEmission {
                    fault: EmissionFault::CloseWithoutOpen,
                }),
                EmissionShape::Complete,
            ),
            (
                EmissionShape::Inside(OpenDepth(1)),
                Ok(Closing::Root),
                EmissionShape::Complete,
            ),
            (
                EmissionShape::Inside(OpenDepth(2)),
                Ok(Closing::Inner),
                EmissionShape::Inside(OpenDepth(1)),
            ),
            (
                EmissionShape::Inside(OpenDepth(usize::MAX)),
                Ok(Closing::Inner),
                EmissionShape::Inside(OpenDepth(usize::MAX - 1)),
            ),
        ];
        for (mut state, outcome, after) in closings {
            assert_eq!(state.close(), outcome);
            assert_eq!(state, after);
        }
        let phases = [
            (
                EmissionShape::Empty,
                Err(ValueError::MalformedEmission {
                    fault: EmissionFault::PayloadOutsideConstructor,
                }),
                Err(ValueError::MalformedEmission {
                    fault: EmissionFault::EmptyValue,
                }),
            ),
            (
                EmissionShape::Inside(OpenDepth(1)),
                Ok(()),
                Err(ValueError::MalformedEmission {
                    fault: EmissionFault::UnclosedConstructor,
                }),
            ),
            (
                EmissionShape::Complete,
                Err(ValueError::MalformedEmission {
                    fault: EmissionFault::PayloadOutsideConstructor,
                }),
                Ok(()),
            ),
        ];
        for (state, payload, finish) in phases {
            assert_eq!(state.payload(), payload);
            assert_eq!(state.finish(), finish);
        }
    }
}
