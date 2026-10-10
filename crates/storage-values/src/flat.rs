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
use crate::tokens::BodyFront;
use crate::tokens::BodyWriter;
use crate::tokens::CanonicalValue;
use crate::tokens::ConstructorTag;
use crate::tokens::EmissionShape;
use crate::tokens::Record;
use crate::tokens::TokenSink;
use crate::tokens::split_record;
use crate::units::CanonicalWord;
use crate::units::FlatBytes;
use crate::units::TokenBody;
use crate::units::TokenBytes;

/// The flat encoder's sink: a body writer and the emission's shape.
///
/// # Specification
/// - requires: construction by the flat encoder and updates through its sink.
/// - ensures: the record position never exceeds the bytes already written;
///   every addressed record occupies at least its kind byte. A failed position
///   advance may leave an unaddressed record in the discarded body.
/// - provides: the byte writer, emission state and address cursor together.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 the empty sink and a literal four-record, 23-byte emission
///   satisfy the refinement; a cursor past that image does not. Full wire bytes
///   and position four distinguish dropped records and cursor drift on this
///   corpus, not all failures at the address-width ceiling.
/// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
#[spec(maintains: usize::try_from(u32::from(self.position))
    .is_ok_and(|position| position <= self.body.as_body().as_ref().len()))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 a four-record open/word/binary-bytes/close emission has
    ///   a literal 23-byte image and final position four. A rejected seam at
    ///   position two leaves that image unchanged. These distinguish dropped or
    ///   altered records, wrong widths and skipped or doubled positions.
    ///   Address-width overflow is outside this short corpus.
    /// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
    #[spec(captures: [entry = self.position, mark = self.body.mark()],
        ensures: |ret| ret.is_err() || (entry.next() == Ok(self.position)
            && anodized::types::Spec::predicate(self)
            && matches!(split_record(self.body.since(mark)), Ok(BodyFront::Record(found, rest))
                if found == record && rest.as_ref().is_empty())))]
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
    /// - ensures: on success the open record is appended and the position
    ///   advances once.
    /// - provides: the flat half of [`TokenSink::open`].
    /// - fails: the shape refusal for a second root, and [`FlatSink`]'s
    ///   overflow refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a four-record open/word/binary-bytes/close emission has
    ///   a literal 23-byte image and final position four. A rejected seam at
    ///   position two leaves that image unchanged. These distinguish dropped or
    ///   altered records, wrong widths and skipped or doubled positions.
    ///   Address-width overflow is outside this short corpus.
    /// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || entry.next() == Ok(self.position))]
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
    /// - ensures: on success the word record is appended and the position
    ///   advances once.
    /// - provides: the flat half of [`TokenSink::word`].
    /// - fails: the shape refusal outside every constructor.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a four-record open/word/binary-bytes/close emission has
    ///   a literal 23-byte image and final position four. A rejected seam at
    ///   position two leaves that image unchanged. These distinguish dropped or
    ///   altered records, wrong widths and skipped or doubled positions.
    ///   Address-width overflow is outside this short corpus.
    /// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || entry.next() == Ok(self.position))]
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
    /// - ensures: on success the bytes record is appended and the position
    ///   advances once.
    /// - provides: the flat half of [`TokenSink::bytes`].
    /// - fails: the shape refusal outside every constructor.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a four-record open/word/binary-bytes/close emission has
    ///   a literal 23-byte image and final position four. A rejected seam at
    ///   position two leaves that image unchanged. These distinguish dropped or
    ///   altered records, wrong widths and skipped or doubled positions.
    ///   Address-width overflow is outside this short corpus.
    /// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || entry.next() == Ok(self.position))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 an offered pointer after two emitted records is refused
    ///   at position two, and the final literal body contains no seam. This
    ///   distinguishes acceptance, a wrong reported position or an appended
    ///   record despite refusal, without consulting any backing store.
    /// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
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
    /// - ensures: on success the close record is appended and the position
    ///   advances once.
    /// - provides: the flat half of [`TokenSink::close`].
    /// - fails: the shape refusal with nothing open.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a four-record open/word/binary-bytes/close emission has
    ///   a literal 23-byte image and final position four. A rejected seam at
    ///   position two leaves that image unchanged. These distinguish dropped or
    ///   altered records, wrong widths and skipped or doubled positions.
    ///   Address-width overflow is outside this short corpus.
    /// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    #[inline]
    #[spec(captures: [entry = self.position], ensures: |ret| ret.is_err() || entry.next() == Ok(self.position))]
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
/// - hypothesis: L2 round trips of generated trees drawn from seven shapes with
///   at most 4096 records compare complete decoded values; a fixed value also
///   compares flat bytes with its single chunk body. L3 literal wire bytes and
///   malformed emission scripts distinguish changed payloads, order, framing
///   and accepted imbalance. This is bounded evidence for these codecs.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
/// - witness: `tests::flat::a_flat_form_round_trips`
/// - witness: `tests::flat::flat_bytes_equal_the_single_chunk_body`
/// - witness: `flat::tests::flat_sink_preserves_wire_records_and_refusal_positions`
/// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
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
/// - hypothesis: L3 a fixed value's body, one byte short and one record long,
///   separates incomplete and trailing input; a hand-built child record is
///   refused at its named position. L2 generated trees from seven shapes with
///   at most 4096 records round-trip by complete value equality. These do not
///   establish arbitrary external codecs' laws or cover every malformed body.
/// - witness: `tests::flat::a_truncated_flat_form_is_refused`
/// - witness: `tests::flat::a_flat_form_with_trailing_tokens_is_refused`
/// - witness: `tests::flat::a_child_record_is_refused_in_a_flat_form`
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
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

#[cfg(test)]
mod tests
{
    use super::FlatSink;
    use crate::CanonicalWord;
    use crate::ChunkDigest;
    use crate::ConstructorTag;
    use crate::ContentPtr;
    use crate::EmissionFault;
    use crate::TokenBytes;
    use crate::TokenOffset;
    use crate::TokenSink as _;
    use crate::ValueError;
    use crate::tokens::BodyWriter;
    use crate::tokens::EmissionShape;

    #[test]
    fn flat_sink_preserves_wire_records_and_refusal_positions()
    {
        let mut sink = FlatSink {
            body: BodyWriter::default(),
            shape: EmissionShape::Empty,
            position: TokenOffset::ZERO,
        };
        assert!(anodized::types::Spec::predicate(&sink));
        assert_eq!(
            sink.bytes(TokenBytes::from(b"outside".as_slice())),
            Err(ValueError::MalformedEmission {
                fault: EmissionFault::PayloadOutsideConstructor,
            })
        );
        sink.open(ConstructorTag::from(0x2a_u8))
            .expect("the root opens");
        sink.word(CanonicalWord::from(7_u64))
            .expect("the word emits");
        let pointer = ContentPtr::new(ChunkDigest::from([7_u8; 32]), TokenOffset::ZERO);
        assert_eq!(
            sink.child_pointer(pointer),
            Err(ValueError::SeamInFlatForm {
                position: TokenOffset::from(2_u32),
            })
        );
        sink.bytes(TokenBytes::from([0_u8, 0xff_u8].as_slice()))
            .expect("the binary payload emits");
        sink.close().expect("the root closes");
        assert_eq!(
            sink.open(ConstructorTag::from(1_u8)),
            Err(ValueError::MalformedEmission {
                fault: EmissionFault::SecondRoot,
            })
        );
        let expected: [u8; 23] = [
            0x01, 0x2a, 0x02, 7, 0, 0, 0, 0, 0, 0, 0, 0x03, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0x05,
        ];
        assert_eq!(sink.body.as_body().as_ref(), expected.as_slice());
        assert_eq!(sink.position, TokenOffset::from(4_u32));
        assert!(anodized::types::Spec::predicate(&sink));
        sink.position = TokenOffset::from(24_u32);
        assert!(!anodized::types::Spec::predicate(&sink));
    }
}
