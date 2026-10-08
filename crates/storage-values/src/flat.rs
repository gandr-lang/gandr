//! The flat form: one value's canonical token body, with no store and no
//! seam.
//!
//! A consumer needing canonical bytes to hash, sign or keep in a record uses
//! the flat form. It uses the chunk body's byte language and writer, so for a
//! value that fits one chunk these bytes equal the body
//! [`crate::cam_commit`] frames. See the
//! [byte languages](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#byte-languages).
//!
//! A flat form carries no child record. It has no store to resolve one
//! against, so the encoder refuses a value that embeds a committed pointer and
//! the decoder refuses a body that carries one.

use anodized::spec;

use crate::chunk::frame_chunk;
use crate::error::ValueError;
use crate::ptr::ContentPtr;
use crate::ptr::TokenOffset;
use crate::reader::StreamEnd;
use crate::reader::TokenReader;
use crate::tokens::BodyWriter;
use crate::tokens::CanonicalValue;
use crate::tokens::ConstructorTag;
use crate::tokens::EmissionShape;
use crate::tokens::Record;
use crate::tokens::TokenSink;
use crate::units::CanonicalWord;
use crate::units::FlatBytes;
use crate::units::TokenBody;
use crate::units::TokenBytes;

/// The flat encoder's sink: a body writer and the emission's shape.
struct FlatSink
{
    /// The records written so far.
    body: BodyWriter,
    /// Where the emission stands in the one-balanced-value shape.
    shape: EmissionShape,
    /// The record position the next record takes.
    position: TokenOffset,
}

impl FlatSink
{
    /// Appends one record and advances the position.
    ///
    /// # Specification
    /// - requires: the record's shape check has passed.
    /// - ensures: on success the record is appended and the position is one
    ///   further.
    /// - provides: the one place the flat encoder writes.
    /// - fails: the body writer's overflow refusal, and an overflow refusal
    ///   past the record positions a reader can address.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::ArithmeticOverflow`] — a length or position passes its
    /// width.
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || self.position > entry)]
    fn emit(
        &mut self,
        record: Record<'_>,
    ) -> Result<(), ValueError>
    {
        self.body.push(record)?;
        self.position = self.position.next()?;

        Ok(())
    }
}

impl TokenSink for FlatSink
{
    /// Appends an open record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the open record is appended.
    /// - provides: the flat half of [`TokenSink::open`].
    /// - fails: the shape refusal for a second root, and [`FlatSink`]'s
    ///   overflow refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || self.position > entry)]
    fn open(
        &mut self,
        tag: ConstructorTag,
    ) -> Result<(), ValueError>
    {
        self.shape.open()?;

        self.emit(Record::Open(tag))
    }

    /// Appends a word record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the word record is appended.
    /// - provides: the flat half of [`TokenSink::word`].
    /// - fails: the shape refusal outside every constructor.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || self.position > entry)]
    fn word(
        &mut self,
        word: CanonicalWord,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;

        self.emit(Record::Word(word))
    }

    /// Appends a bytes record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the bytes record is appended.
    /// - provides: the flat half of [`TokenSink::bytes`].
    /// - fails: the shape refusal outside every constructor.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || self.position > entry)]
    fn bytes(
        &mut self,
        bytes: TokenBytes<'_>,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;

        self.emit(Record::Bytes(bytes))
    }

    /// Refuses a child record: a flat form has no store to resolve it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: never succeeds.
    /// - provides: the encoder's half of the no-seam rule.
    /// - fails: [`ValueError::SeamInFlatForm`] at the position the record would
    ///   have taken.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::SeamInFlatForm`] — always.
    #[inline]
    #[spec(ensures: |ret| ret == Err(ValueError::SeamInFlatForm { position: self.position }))]
    fn child_pointer(
        &mut self,
        _pointer: ContentPtr,
    ) -> Result<(), ValueError>
    {
        Err(ValueError::SeamInFlatForm {
            position: self.position,
        })
    }

    /// Appends a close record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the close record is appended.
    /// - provides: the flat half of [`TokenSink::close`].
    /// - fails: the shape refusal with nothing open.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || self.position > entry)]
    fn close(&mut self) -> Result<(), ValueError>
    {
        let _closing = self.shape.close()?;

        self.emit(Record::Close)
    }
}

/// Encodes one value as its flat form.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the canonical token body of the value: the records it
///   emitted, in order, in the layout a chunk body is written in;
///   [`decode_flat`] returns an equal value, and for a value that fits one
///   chunk the bytes equal that chunk's body.
/// - provides: the value's canonical bytes without a store.
/// - fails: [`ValueError::SeamInFlatForm`] for a value that embeds a committed
///   pointer, [`ValueError::MalformedEmission`] for an emission that is not one
///   balanced value, and an overflow refusal past the record positions a reader
///   can address.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 agreement — encode then decode is the identity, and the
///   bytes equal a single chunk's body.
/// - witness: `tests::flat::a_flat_form_round_trips`
/// - witness: `tests::flat::flat_bytes_equal_the_single_chunk_body`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|flat| frame_chunk(flat.as_body()).is_ok()))]
pub fn encode_flat<Value>(value: &Value) -> Result<FlatBytes, ValueError>
where
    Value: CanonicalValue,
{
    let mut sink = FlatSink {
        body: BodyWriter::default(),
        shape: EmissionShape::Empty,
        position: TokenOffset::ZERO,
    };
    value.emit_tokens(&mut sink)?;
    sink.shape.finish()?;

    Ok(sink.body.into_flat())
}

/// Decodes one value from its flat form, refusing anything after it.
///
/// # Specification
/// - requires: nothing; every malformed body is refused by name.
/// - ensures: on success the value the body encodes, and the body holds nothing
///   after it.
/// - provides: the read half of the flat form.
/// - fails: [`ValueError::TruncatedStream`] for a body that ends inside the
///   value, [`ValueError::TrailingTokens`] for one that continues past it,
///   [`ValueError::SeamInFlatForm`] for a child record, and the reader's and
///   the codec's other refusals.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L3 only — the end of the value is separated by a body one byte
///   short and one record long, and the seam by a hand-built child record.
/// - witness: `tests::flat::a_truncated_flat_form_is_refused`
/// - witness: `tests::flat::a_flat_form_with_trailing_tokens_is_refused`
/// - witness: `tests::flat::a_child_record_is_refused_in_a_flat_form`
#[inline]
#[spec(ensures: |ret| ret.is_err() || frame_chunk(body).is_ok())]
pub fn decode_flat<Value>(body: TokenBody<'_>) -> Result<Value, ValueError>
where
    Value: CanonicalValue,
{
    let mut reader = TokenReader::over_flat(body);
    let value = Value::decode_tokens(&mut reader)?;

    match reader.end() {
        | StreamEnd::Ended => Ok(value),
        | StreamEnd::Continues => Err(ValueError::TrailingTokens {
            position: reader.position(),
        }),
    }
}
