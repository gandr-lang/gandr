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
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0 types — a declaration with no body states the
    ///   obligation every implementation owes.
    /// - declaration-only: a required trait method has no body to witness; each
    ///   implementation is witnessed where it is defined.
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
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0 types — a declaration with no body states the
    ///   obligation every implementation owes.
    /// - declaration-only: a required trait method has no body to witness; each
    ///   implementation is witnessed where it is defined.
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
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0 types — a declaration with no body states the
    ///   obligation every implementation owes.
    /// - declaration-only: a required trait method has no body to witness; each
    ///   implementation is witnessed where it is defined.
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
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0 types — a declaration with no body states the
    ///   obligation every implementation owes.
    /// - declaration-only: a required trait method has no body to witness; each
    ///   implementation is witnessed where it is defined.
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
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0 types — a declaration with no body states the
    ///   obligation every implementation owes.
    /// - declaration-only: a required trait method has no body to witness; each
    ///   implementation is witnessed where it is defined.
    fn close(&mut self) -> Result<(), ValueError>;
}

/// A value that can be written to, and read back from, the canonical token
/// stream.
///
/// Decoding what a value emits must return an equal value. This round-trip
/// law gives a [`ContentPtr`] its meaning across codec calls.
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
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0 types — a declaration with no body states the
    ///   obligation every implementation owes.
    /// - declaration-only: a required trait method has no body to witness; each
    ///   codec is witnessed where it is defined.
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
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0 types — a declaration with no body states the
    ///   obligation every implementation owes.
    /// - declaration-only: a required trait method has no body to witness; each
    ///   codec is witnessed where it is defined.
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
    /// trivial.
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
/// - hypothesis: L2 agreement — every record the writer appends reads back as
///   itself with nothing left over — plus L3 for the two faults, separated by
///   an unassigned kind byte and by a record cut one byte short.
/// - witness: `tokens::tests::every_record_round_trips_through_the_grammar`
/// - witness: `tokens::tests::a_short_or_unknown_record_is_a_named_fault`
#[spec(ensures: |ret| (ret == Ok(BodyFront::Empty)) == body.as_ref().is_empty()
    && !matches!(ret, Ok(BodyFront::Record(_, rest)) if rest.as_ref().len() >= body.as_ref().len()))]
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

/// An append-only token body under construction, shared by the committing
/// traversal and the flat encoder so both write one byte language.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
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
    #[spec(captures: [entry = self.mark()],
        ensures: |ret| ret.is_err()
            || matches!(
                split_record(self.since(entry)),
                Ok(BodyFront::Record(read, rest)) if read == record && rest.as_ref().is_empty()
            ))]
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
    #[spec(ensures: |ret| ret.as_ref().len() == self.0.len().saturating_sub(mark.0))]
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
    /// trivial.
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
    /// trivial.
    pub(crate) fn into_flat(self) -> FlatBytes
    {
        FlatBytes::from(self.0.into_boxed_slice())
    }
}

/// Where an emission stands in the one-balanced-value shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    /// - requires: nothing.
    /// - ensures: on success one constructor deeper than before.
    /// - provides: the shape check every sink runs before writing an open.
    /// - fails: [`ValueError::MalformedEmission`] with
    ///   [`EmissionFault::SecondRoot`] after the root closed, or an overflow
    ///   refusal at the width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — the open breaks the shape.
    #[spec(captures: [entry = *self],
        ensures: |ret| (entry != Self::Empty || ret.is_ok())
            && (entry != Self::Complete || ret.is_err())
            && (ret.is_err() || matches!(*self, Self::Inside(_))))]
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
    /// - requires: nothing.
    /// - ensures: success exactly when a constructor is open.
    /// - provides: the shape check before a word, bytes or child record.
    /// - fails: [`ValueError::MalformedEmission`] with
    ///   [`EmissionFault::PayloadOutsideConstructor`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — no constructor is open.
    #[spec(ensures: |ret| ret.is_ok() == matches!(self, Self::Inside(_)))]
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
    /// - requires: nothing.
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
    #[spec(captures: [entry = *self],
        ensures: |ret| ret.is_ok() == matches!(entry, Self::Inside(_))
            && (ret == Ok(Closing::Root)) == (entry == Self::Inside(OpenDepth(1_usize))))]
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
    /// - requires: nothing.
    /// - ensures: success exactly when the root has closed.
    /// - provides: the final shape check every sink runs.
    /// - fails: [`ValueError::MalformedEmission`] with
    ///   [`EmissionFault::EmptyValue`] or
    ///   [`EmissionFault::UnclosedConstructor`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — the emission is empty or unclosed.
    #[spec(ensures: |ret| ret.is_ok() == (self == Self::Complete))]
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
    use super::BodyFront;
    use super::BodyWriter;
    use super::ConstructorTag;
    use super::Record;
    use super::RecordFault;
    use super::split_record;
    use crate::ptr::ChunkDigest;
    use crate::ptr::ContentPtr;
    use crate::ptr::TokenOffset;
    use crate::units::CanonicalWord;
    use crate::units::TokenBody;
    use crate::units::TokenBytes;

    #[test]
    fn every_record_round_trips_through_the_grammar()
    {
        let payload = [0xAA_u8, 0xBB, 0xCC];
        let records = [
            Record::Open(ConstructorTag::from(0x2A_u8)),
            Record::Word(CanonicalWord::from(0x0102_0304_0506_0708_u64)),
            Record::Bytes(TokenBytes::from(payload.as_slice())),
            Record::Bytes(TokenBytes::from([].as_slice())),
            Record::Child(ContentPtr::new(
                ChunkDigest::from([0x5A_u8; 32]),
                TokenOffset::from(0x0A0B_0C0D_u32),
            )),
            Record::Close,
        ];

        for record in records {
            let mut writer = BodyWriter::default();
            writer.push(record).expect("a record writes");
            let front = split_record(writer.as_body()).expect("a written record reads");

            let BodyFront::Record(read, rest) = front
            else {
                panic!("a written record is not an empty body");
            };
            assert_eq!(read, record);
            assert!(rest.as_ref().is_empty(), "nothing is left after one record");
        }

        // The integers are little-endian: the word's least significant byte
        // comes first.
        let mut writer = BodyWriter::default();
        writer
            .push(Record::Word(CanonicalWord::from(0x0102_0304_0506_0708_u64)))
            .expect("a word writes");
        assert_eq!(writer.as_body().as_ref(), [
            0x02, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01
        ]);
    }

    #[test]
    fn a_short_or_unknown_record_is_a_named_fault()
    {
        assert_eq!(
            split_record(TokenBody::from([0x06_u8].as_slice())),
            Err(RecordFault::UnknownKind)
        );
        assert_eq!(
            split_record(TokenBody::from([0x00_u8].as_slice())),
            Err(RecordFault::UnknownKind)
        );
        assert_eq!(
            split_record(TokenBody::from([0x02_u8, 1, 2, 3, 4, 5, 6, 7].as_slice())),
            Err(RecordFault::Truncated),
            "a word one byte short"
        );
        assert_eq!(
            split_record(TokenBody::from(
                [0x03_u8, 2, 0, 0, 0, 0, 0, 0, 0, 0xAA].as_slice()
            )),
            Err(RecordFault::Truncated),
            "a payload one byte short of its declared length"
        );
        assert_eq!(
            split_record(TokenBody::from([0x01_u8].as_slice())),
            Err(RecordFault::Truncated),
            "an open without its tag"
        );
        assert_eq!(
            split_record(TokenBody::from([].as_slice())),
            Ok(BodyFront::Empty)
        );
    }
}
