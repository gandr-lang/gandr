//! The token reader: one continuous stream over a body, splicing child chunks
//! in place and charging every step to one decode budget.
//!
//! # Store access
//!
//! A child record is a hole in the token stream, and filling it needs a fetch.
//! Handing a decoder a bare byte slice would make the seam visible in the
//! codec's signature — the decoder would have to report "I reached a pointer"
//! and be re-entered. So the reader holds the store, descends on a child
//! record, and returns to the parent when the child's subtree closes; a
//! decoder sees one stream and cannot tell where the seams were.
//!
//! The store is `&dyn` rather than a type parameter: a reader generic over its
//! store would push the store type into
//! [`crate::CanonicalValue::decode_tokens`] and so into every value's codec,
//! making a value's encoding depend on where it is stored.
//!
//! # Child subtrees
//!
//! A child record stands for one value. The reader therefore leaves a
//! descended chunk the moment the subtree it entered closes, and refuses a
//! chunk that ends before its subtree does — a chunk cannot splice records
//! into its parent's stream.
//!
//! # Seam stack
//!
//! A child record can appear at any depth in any chunk, and the decoder
//! driving the reader may keep its own stack already. Suspended chunks live in
//! a vector here, so the depth of a chunk DAG is bounded by the decode budget
//! rather than by the host stack.
//!
//! # Decode budget
//!
//! Per-record checks bound one record, and they do not bound a DAG that
//! references one chunk many times: each reference is read again, so the work
//! can grow with the number of paths rather than the number of chunks. Every
//! decode is therefore charged to one accumulator — a unit per record read, a
//! unit per payload byte, and a unit per chunk-image byte verified on a seam —
//! and refused once the total passes [`MAX_DECODE_WORK`].

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::chunk::ChunkStore;
use crate::chunk::VerifiedChunk;
use crate::error::ValueError;
use crate::error::ValueQuantity;
use crate::ptr::TokenOffset;
use crate::tokens::BodyFront;
use crate::tokens::ConstructorTag;
use crate::tokens::Record;
use crate::tokens::RecordFault;
use crate::tokens::TokenKind;
use crate::tokens::split_record;
use crate::units::CanonicalWord;
use crate::units::DecodeWork;
use crate::units::MAX_DECODE_WORK;
use crate::units::SeamDepth;
use crate::units::TokenBody;
use crate::units::TokenBytes;

/// Where a reader's records come from beyond the body it was opened over.
#[derive(Clone, Copy)]
enum Source<'stream>
{
    /// Child records are fetched from this store and verified.
    Store(&'stream dyn ChunkStore),
    /// There is no store: a child record is refused.
    Flat,
}

/// How many constructors a frame has opened and not yet closed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct OpenCount(u64);

/// One body being read: the unread records, the position of the first of
/// them, and how deep inside the frame's own subtree the reader is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Frame<'stream>
{
    /// The unread records.
    remaining: TokenBody<'stream>,
    /// The record position of the first unread record within its body.
    position: TokenOffset,
    /// Constructors this frame opened that have not closed.
    open: OpenCount,
}

impl<'stream> Frame<'stream>
{
    /// Opens a frame at the start of a body.
    ///
    /// # Specification
    /// trivial.
    const fn at_start(body: TokenBody<'stream>) -> Self
    {
        Self {
            remaining: body,
            position: TokenOffset::ZERO,
            open: OpenCount(0_u64),
        }
    }
}

/// Whether a reader has consumed its whole stream.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StreamEnd
{
    /// Nothing is left.
    Ended,
    /// Records remain.
    Continues,
}

/// A cursor over a value's token stream that splices child chunks in place.
pub struct TokenReader<'stream>
{
    /// Where child chunks are fetched from, if anywhere.
    source: Source<'stream>,
    /// The body being read.
    current: Frame<'stream>,
    /// Suspended parents, outermost first.
    suspended: Vec<Frame<'stream>>,
    /// The work spent so far.
    spent: DecodeWork,
    /// The most work this reader may spend.
    ceiling: DecodeWork,
}

impl fmt::Debug for TokenReader<'_>
{
    /// Writes the reader's position without the store.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the position, the seam depth and the work spent, and
    ///   never the store, which is not a value.
    /// - provides: where the reader is, for a failing test's message.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("TokenReader")
            .field("position", &self.current.position)
            .field("seam_depth", &self.suspended.len())
            .field("spent", &self.spent)
            .finish_non_exhaustive()
    }
}

impl<'stream> TokenReader<'stream>
{
    /// Opens a reader over a verified chunk whose children `store` holds,
    /// charging the chunk's verified image to the budget.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the reader is at the chunk body's first record,
    ///   having spent one unit per image byte.
    /// - provides: the entry point a deref opens.
    /// - fails: [`ValueError::DecodeBudgetExceeded`] for an image past the
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::DecodeBudgetExceeded`] — as listed above.
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|reader| reader.current.position == TokenOffset::ZERO && reader.suspended.is_empty()))]
    pub(crate) fn over_chunk(
        store: &'stream dyn ChunkStore,
        chunk: VerifiedChunk<'stream>,
    ) -> Result<Self, ValueError>
    {
        let mut reader = Self::new(Source::Store(store), chunk.body(), MAX_DECODE_WORK);
        let image_length = u64::try_from(chunk.image().as_ref().len()).unwrap_or(u64::MAX);
        reader.spent = charge(reader.spent, DecodeWork::from(image_length), reader.ceiling)?;

        Ok(reader)
    }

    /// Opens a reader over a flat form, which has no store.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn over_flat(body: TokenBody<'stream>) -> Self
    {
        Self::new(Source::Flat, body, MAX_DECODE_WORK)
    }

    /// Opens a reader with an explicit work ceiling.
    ///
    /// # Specification
    /// trivial.
    const fn new(
        source: Source<'stream>,
        body: TokenBody<'stream>,
        ceiling: DecodeWork,
    ) -> Self
    {
        Self {
            source,
            current: Frame::at_start(body),
            suspended: Vec::new(),
            spent: DecodeWork::ZERO,
            ceiling,
        }
    }

    /// Returns the record position the reader is at within its current body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn position(&self) -> TokenOffset
    {
        self.current.position
    }

    /// Returns how many chunk seams the reader is currently inside.
    ///
    /// Exposed so a test can assert that a value which should cross a seam
    /// does: a deref that read everything from one chunk passes a round trip
    /// and proves nothing about chunking.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn seam_depth(&self) -> SeamDepth
    {
        SeamDepth::from(self.suspended.len())
    }

    /// Returns the work the reader has spent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn spent(&self) -> DecodeWork
    {
        self.spent
    }

    /// Reads the next constructor tag, refusing any other record.
    ///
    /// # Specification
    /// - requires: nothing; a wrong record is the case this refuses.
    /// - ensures: on success the reader is past exactly one open record, having
    ///   crossed any seams on the way, and one constructor deeper.
    /// - provides: the decoder's structural step.
    /// - fails: [`ValueError::UnexpectedToken`] naming both kinds,
    ///   [`ValueError::TruncatedStream`], [`ValueError::UnknownTokenKind`],
    ///   [`ValueError::SeamInFlatForm`], [`ValueError::DecodeBudgetExceeded`],
    ///   or a store or frame refusal met while crossing a seam.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the wrong-kind surface is separated by a word
    ///   whose leading byte is a valid tag standing where a tag belongs, which
    ///   must be refused naming both kinds rather than coerced.
    /// - witness: `tests::values::a_word_is_never_read_as_a_tag`
    #[inline]
    #[spec(captures: [entry_spent = self.spent],
        ensures: |ret| ret.is_err() || (self.spent > entry_spent && self.current.open > OpenCount(0_u64)))]
    pub fn read_tag(&mut self) -> Result<ConstructorTag, ValueError>
    {
        let (record, rest) = self.next_record()?;

        let Record::Open(tag) = record
        else {
            return Err(self.unexpected(TokenKind::Open, &record));
        };
        let Some(deeper) = self.current.open.0.checked_add(1_u64)
        else {
            return Err(ValueError::ArithmeticOverflow {
                quantity: ValueQuantity::TokenCount,
            });
        };

        self.current.open = OpenCount(deeper);
        self.advance(rest, DecodeWork::ONE)?;

        Ok(tag)
    }

    /// Reads the next canonical word, refusing any other record.
    ///
    /// # Specification
    /// - requires: nothing; a wrong record is the case this refuses.
    /// - ensures: on success the reader is past exactly one word record.
    /// - provides: the decoder's scalar step.
    /// - fails: as [`TokenReader::read_tag`]; a word with no constructor open
    ///   in the current body is refused as standing where an open was required,
    ///   since a value and a child's subtree both open with one.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as [`TokenReader::read_tag`].
    #[inline]
    #[spec(captures: [entry_spent = self.spent],
        ensures: |ret| ret.is_err() || (self.spent > entry_spent && self.current.open > OpenCount(0_u64)))]
    pub fn read_word(&mut self) -> Result<CanonicalWord, ValueError>
    {
        let (record, rest) = self.next_record()?;

        let Record::Word(word) = record
        else {
            return Err(self.unexpected(TokenKind::Word, &record));
        };
        if self.current.open == OpenCount(0_u64) {
            return Err(self.unexpected(TokenKind::Open, &record));
        }
        self.advance(rest, DecodeWork::ONE)?;

        Ok(word)
    }

    /// Reads an inline byte payload, refusing any other record.
    ///
    /// # Specification
    /// - requires: nothing; a wrong record is the case this refuses.
    /// - ensures: on success the reader is past exactly one bytes record, and
    ///   the payload borrows out of the body that carries it.
    /// - provides: the decoder's payload step.
    /// - fails: as [`TokenReader::read_word`]; the payload's bytes are charged
    ///   to the budget.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as [`TokenReader::read_tag`].
    #[inline]
    #[spec(captures: [entry_spent = self.spent],
        ensures: |ret| ret.is_err() || (self.spent > entry_spent && self.current.open > OpenCount(0_u64)))]
    pub fn read_bytes(&mut self) -> Result<TokenBytes<'stream>, ValueError>
    {
        let (record, rest) = self.next_record()?;

        let Record::Bytes(payload) = record
        else {
            return Err(self.unexpected(TokenKind::Bytes, &record));
        };
        if self.current.open == OpenCount(0_u64) {
            return Err(self.unexpected(TokenKind::Open, &record));
        }
        let length = u64::try_from(payload.as_ref().len()).unwrap_or(u64::MAX);
        self.advance(rest, DecodeWork::from(length.saturating_add(1_u64)))?;

        Ok(payload)
    }

    /// Reads the close record of the innermost open constructor.
    ///
    /// # Specification
    /// - requires: nothing; a wrong record, or a close with nothing open, is
    ///   the case this refuses.
    /// - ensures: on success the reader is past exactly one close record and
    ///   one constructor shallower; when that closes the subtree a seam
    ///   entered, the reader is back in the parent's body, just past the child
    ///   record.
    /// - provides: the decoder's nesting step, and the point a seam is left.
    /// - fails: as [`TokenReader::read_tag`]; a close with no constructor open
    ///   in the current body is refused as a close standing where an open was
    ///   required.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as [`TokenReader::read_tag`].
    #[inline]
    #[spec(captures: [entry_spent = self.spent], ensures: |ret| ret.is_err() || self.spent > entry_spent)]
    pub fn read_close(&mut self) -> Result<(), ValueError>
    {
        let (record, rest) = self.next_record()?;

        let Record::Close = record
        else {
            return Err(self.unexpected(TokenKind::Close, &record));
        };
        let Some(shallower) = self.current.open.0.checked_sub(1_u64)
        else {
            return Err(self.unexpected(TokenKind::Open, &record));
        };

        self.current.open = OpenCount(shallower);
        self.advance(rest, DecodeWork::ONE)?;

        // A body whose subtree is one child record delivers that child's
        // subtree and nothing else, so leaving one seam can finish its parent
        // too.
        while self.current.open == OpenCount(0_u64)
            && let Some(parent) = self.suspended.pop()
        {
            self.current = parent;
        }

        Ok(())
    }

    /// Skips `count` records of the current body without descending.
    ///
    /// # Specification
    /// - requires: the reader is at the start of a body.
    /// - ensures: on success the reader is `count` records further into the
    ///   same body; no record is interpreted, so a child record is skipped
    ///   rather than entered.
    /// - provides: the entry step for a pointer that addresses the interior of
    ///   a chunk.
    /// - fails: [`ValueError::TruncatedStream`] when the body holds fewer
    ///   records, [`ValueError::UnknownTokenKind`] on an unassigned kind, and
    ///   [`ValueError::DecodeBudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[spec(captures: [entry = self.current.position],
        ensures: |ret| ret.is_err()
            || u32::from(self.current.position) == u32::from(entry).saturating_add(u32::from(count)))]
    pub(crate) fn skip(
        &mut self,
        count: TokenOffset,
    ) -> Result<(), ValueError>
    {
        for _record in 0_u32 .. u32::from(count) {
            let front = split_record(self.current.remaining).map_err(|fault| self.fault(fault));
            let BodyFront::Record(_skipped, rest) = front?
            else {
                return Err(ValueError::TruncatedStream {
                    position: self.current.position,
                });
            };
            self.advance(rest, DecodeWork::ONE)?;
        }

        Ok(())
    }

    /// Reports whether the whole stream has been read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`StreamEnd::Ended`] exactly when no seam is suspended and
    ///   the current body has no record left.
    /// - provides: the trailing-bytes check a flat decode ends with.
    /// - fails: never.
    /// - panics: none.
    #[spec(ensures: |ret| (ret == StreamEnd::Ended)
        == (self.suspended.is_empty() && self.current.remaining.as_ref().is_empty()))]
    pub(crate) fn end(&self) -> StreamEnd
    {
        if self.suspended.is_empty() && self.current.remaining.as_ref().is_empty() {
            StreamEnd::Ended
        }
        else {
            StreamEnd::Continues
        }
    }

    /// Positions the reader at the next record, crossing seams, and returns it
    /// without consuming it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the record under the cursor is not a child — a
    ///   child has been descended into, its chunk fetched and verified, and the
    ///   cursor moved to the record its offset names — and the returned rest is
    ///   the body after that record.
    /// - provides: the one place a seam is entered.
    /// - fails: [`ValueError::TruncatedStream`] at the end of the stream or
    ///   when a descended chunk ends inside its subtree;
    ///   [`ValueError::UnknownTokenKind`]; [`ValueError::SeamInFlatForm`] for a
    ///   child in a flat form; [`ValueError::DecodeBudgetExceeded`]; and the
    ///   store's or the frame's refusal of the child chunk.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|&(record, _rest)| record.kind() != TokenKind::Child))]
    fn next_record(&mut self) -> Result<(Record<'stream>, TokenBody<'stream>), ValueError>
    {
        loop {
            let front = split_record(self.current.remaining).map_err(|fault| self.fault(fault));
            let BodyFront::Record(record, rest) = front?
            else {
                return Err(ValueError::TruncatedStream {
                    position: self.current.position,
                });
            };
            let Record::Child(pointer) = record
            else {
                return Ok((record, rest));
            };
            let Source::Store(store) = self.source
            else {
                return Err(ValueError::SeamInFlatForm {
                    position: self.current.position,
                });
            };

            let chunk = store.load(pointer.digest())?;
            let image_length = u64::try_from(chunk.image().as_ref().len()).unwrap_or(u64::MAX);
            self.advance(rest, DecodeWork::from(image_length.saturating_add(1_u64)))?;
            let body = chunk.body();

            self.suspended.push(self.current);
            self.current = Frame::at_start(body);
            self.skip(pointer.offset())?;
        }
    }

    /// Consumes the record under the cursor and charges its work.
    ///
    /// # Specification
    /// - requires: `rest` is the body after the record under the cursor.
    /// - ensures: on success the cursor is at `rest`, one record further, and
    ///   `work` more has been spent.
    /// - provides: the one place the cursor moves and the budget is charged.
    /// - fails: [`ValueError::DecodeBudgetExceeded`] when the total would pass
    ///   the ceiling, and an overflow refusal at the position's width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — the budget or the position overflows.
    #[spec(captures: [entry = self.spent],
        ensures: |ret| ret.is_err()
            || (u64::from(self.spent) == u64::from(entry).saturating_add(u64::from(work))
                && self.current.remaining == rest))]
    fn advance(
        &mut self,
        rest: TokenBody<'stream>,
        work: DecodeWork,
    ) -> Result<(), ValueError>
    {
        self.spent = charge(self.spent, work, self.ceiling)?;
        self.current.position = self.current.position.next()?;
        self.current.remaining = rest;

        Ok(())
    }

    /// Builds the refusal for a record of the wrong kind at the cursor.
    ///
    /// # Specification
    /// trivial.
    const fn unexpected(
        &self,
        expected: TokenKind,
        found: &Record<'_>,
    ) -> ValueError
    {
        ValueError::UnexpectedToken {
            expected,
            found: found.kind(),
            position: self.current.position,
        }
    }

    /// Builds the refusal for a malformed record at the cursor.
    ///
    /// # Specification
    /// trivial.
    const fn fault(
        &self,
        fault: RecordFault,
    ) -> ValueError
    {
        let position = self.current.position;

        match fault {
            | RecordFault::Truncated => ValueError::TruncatedStream { position },
            | RecordFault::UnknownKind => ValueError::UnknownTokenKind { position },
        }
    }
}

/// Adds `work` to `spent`, refusing a total past `ceiling`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| ret.is_ok() ==
///   u64::from(spent).checked_add(u64::from(work)).is_some_and(|total| total <=
///   u64::from(ceiling))` — the new total exactly when it fits the width and
///   the ceiling.
/// - provides: the decode budget's one accumulator step.
/// - fails: [`ValueError::DecodeBudgetExceeded`] naming the would-be total,
///   saturated at the width, and the ceiling.
/// - panics: none.
///
/// # Errors
/// [`ValueError::DecodeBudgetExceeded`] — the total passes the ceiling.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surface is one comparison, separated by
///   a charge landing exactly on the ceiling (admitted) and one unit past it
///   (refused), plus a charge that would wrap the width.
/// - witness: `reader::tests::the_budget_admits_the_ceiling_and_refuses_one_past`
#[spec(ensures: |ret| ret.is_ok()
    == u64::from(spent)
        .checked_add(u64::from(work))
        .is_some_and(|total| total <= u64::from(ceiling)))]
fn charge(
    spent: DecodeWork,
    work: DecodeWork,
    ceiling: DecodeWork,
) -> Result<DecodeWork, ValueError>
{
    let sum = u64::from(spent).checked_add(u64::from(work));

    match sum {
        | Some(total) if total <= u64::from(ceiling) => Ok(DecodeWork::from(total)),
        | Some(_) | None => Err(ValueError::DecodeBudgetExceeded {
            spent: DecodeWork::from(u64::from(spent).saturating_add(u64::from(work))),
            ceiling,
        }),
    }
}

#[cfg(test)]
mod tests
{
    use super::Source;
    use super::TokenReader;
    use super::charge;
    use crate::error::ValueError;
    use crate::units::DecodeWork;
    use crate::units::TokenBody;

    #[test]
    fn the_budget_admits_the_ceiling_and_refuses_one_past()
    {
        let ceiling = DecodeWork::from(10_u64);

        assert_eq!(
            charge(DecodeWork::from(4_u64), DecodeWork::from(6_u64), ceiling),
            Ok(ceiling)
        );
        assert_eq!(
            charge(DecodeWork::from(4_u64), DecodeWork::from(7_u64), ceiling),
            Err(ValueError::DecodeBudgetExceeded {
                spent: DecodeWork::from(11_u64),
                ceiling,
            })
        );
        assert_eq!(
            charge(
                DecodeWork::from(u64::MAX),
                DecodeWork::ONE,
                DecodeWork::from(u64::MAX)
            ),
            Err(ValueError::DecodeBudgetExceeded {
                spent: DecodeWork::from(u64::MAX),
                ceiling: DecodeWork::from(u64::MAX),
            }),
            "a charge that would wrap the width is refused, not wrapped"
        );
    }

    #[test]
    fn a_reader_stops_at_its_ceiling()
    {
        // Open, word, close: three records, three units.
        let body = [0x01_u8, 0x2A, 0x02, 7, 0, 0, 0, 0, 0, 0, 0, 0x05];

        let mut enough = TokenReader::new(
            Source::Flat,
            TokenBody::from(body.as_slice()),
            DecodeWork::from(3_u64),
        );
        assert!(enough.read_tag().is_ok());
        assert!(enough.read_word().is_ok());
        assert!(enough.read_close().is_ok());
        assert_eq!(enough.spent(), DecodeWork::from(3_u64));

        let mut short = TokenReader::new(
            Source::Flat,
            TokenBody::from(body.as_slice()),
            DecodeWork::from(2_u64),
        );
        assert!(short.read_tag().is_ok());
        assert!(short.read_word().is_ok());
        assert_eq!(
            short.read_close(),
            Err(ValueError::DecodeBudgetExceeded {
                spent: DecodeWork::from(3_u64),
                ceiling: DecodeWork::from(2_u64),
            })
        );
    }
}
