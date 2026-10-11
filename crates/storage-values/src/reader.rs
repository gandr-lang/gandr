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
///
/// # Specification
/// - requires: nothing.
/// - ensures: carries the unread suffix and the cursor's position and nesting
///   bookkeeping; a refused read need not roll back the bookkeeping.
/// - provides: one suspended or current body, without retaining its prefix.
/// - fails: never.
/// - panics: none.
/// - executable: none — the consumed prefix and the history of refused reads
///   needed to relate the suffix, position and nesting are not retained.
///
/// # Adequacy
/// - hypothesis: L3 on one interior child at offset two observes the child's
///   exact tag and return to the parent's word and close, separating a restart,
///   lost parent and wrong resume position. This finite path does not prove all
///   possible seam histories.
/// - witness: `reader::tests::seams_charge_images_and_restore_the_parent`
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: spent work never exceeds the ceiling, and a flat reader has no
///   suspended chunk frames. Refused reads may change other bookkeeping.
/// - provides: a bounded cursor over flat bytes or authenticated chunks.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on a three-record body at budgets two and three observes
///   exact values, refusal and retained spent work. Forged over-budget and
///   flat-with-parent states are rejected, separating both refinements from an
///   unconditional predicate; this does not validate arbitrary codecs.
/// - witness: `reader::tests::a_reader_stops_at_its_ceiling`
#[spec(maintains: self.spent <= self.ceiling
    && (!matches!(self.source, Source::Flat) || self.suspended.is_empty()))]
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
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a body containing a distinctive private byte checks
    ///   that diagnostics omit its ordinary byte rendering, while a refused
    ///   output sink stops formatting. This targets accidental body disclosure
    ///   and swallowed write errors, not a fixed diagnostic spelling.
    /// - witness: `reader::tests::reader_diagnostics_omit_payload_data`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on one root and one interior child observes the exact
    ///   initial image-byte charge, position and later total work, separating
    ///   an uncharged root, body-only charging and a nonzero initial cursor.
    /// - witness: `reader::tests::seams_charge_images_and_restore_the_parent`
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|reader| reader.current.position == TokenOffset::ZERO
            && reader.suspended.is_empty()
            && reader.current.remaining == chunk.body()
            && u64::from(reader.spent) == u64::try_from(chunk.image().as_ref().len()).unwrap_or(u64::MAX)
            && anodized::types::Spec::predicate(reader)))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a literal four-record body observes the exact word,
    ///   record position and work; a word outside any constructor is refused
    ///   naming both kinds. These distinguish payload substitution, missed
    ///   advancement and missing structural admission.
    /// - witness: `reader::tests::typed_reads_charge_payloads_and_refuse_wrong_kinds`
    /// - witness: `reader::tests::payloads_and_closes_require_an_open_constructor`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a two-byte binary payload observes exact borrowed
    ///   bytes and three units of charged work; a payload outside a constructor
    ///   is refused. These separate copying, wrong slices, omitted byte work
    ///   and missing structural admission.
    /// - witness: `reader::tests::typed_reads_charge_payloads_and_refuse_wrong_kinds`
    /// - witness: `reader::tests::payloads_and_closes_require_an_open_constructor`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes the close at a literal root, a close with no
    ///   open constructor, and a child close that restores its parent. These
    ///   separate underflow, missed advancement and lost suspended state on
    ///   those paths.
    /// - witness: `reader::tests::typed_reads_charge_payloads_and_refuse_wrong_kinds`
    /// - witness: `reader::tests::payloads_and_closes_require_an_open_constructor`
    /// - witness: `reader::tests::seams_charge_images_and_restore_the_parent`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on an interior child at offset two observes its exact
    ///   tag rather than the earlier constructor. A flat body with a child
    ///   record is skipped without loading it. Exact-end and one-past-end skips
    ///   distinguish truncation from accepted positions.
    /// - witness: `reader::tests::seams_charge_images_and_restore_the_parent`
    /// - witness: `reader::tests::skipping_does_not_interpret_child_records`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes a literal body before and after its last
    ///   close, and the child-to-parent transition in a chunk stream,
    ///   separating remaining records and suspended parents from the actual
    ///   stream end.
    /// - witness: `reader::tests::typed_reads_charge_payloads_and_refuse_wrong_kinds`
    /// - witness: `reader::tests::seams_charge_images_and_restore_the_parent`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a literal flat body and one interior child observes
    ///   returned kinds, exact child tag and parent restoration. A flat seam is
    ///   refused at its position. These separate kind coercion, a seam exposed
    ///   as data and a wrong child offset.
    /// - witness: `reader::tests::typed_reads_charge_payloads_and_refuse_wrong_kinds`
    /// - witness: `reader::tests::seams_charge_images_and_restore_the_parent`
    /// - witness: `reader::tests::skipping_does_not_interpret_child_records`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes exact positions and work for word and binary
    ///   payload records, plus a three-record body stopped at a ceiling of two.
    ///   This separates omitted record work, omitted payload work, wrong suffix
    ///   advancement and a budget overrun on these paths.
    /// - witness: `reader::tests::typed_reads_charge_payloads_and_refuse_wrong_kinds`
    /// - witness: `reader::tests::a_reader_stops_at_its_ceiling`
    #[spec(captures: [entry = self.spent],
        ensures: |ret| ret.is_err()
            || (u64::from(self.spent) == u64::from(entry).saturating_add(u64::from(work))
                && self.current.remaining == rest
                && anodized::types::Spec::predicate(self)))]
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
/// - provides: the decode budget's one accumulator step, shared by the reader
///   and the closure walk.
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
    == u64::from(spent).checked_add(u64::from(work))
        .is_some_and(|total| total <= u64::from(ceiling))
    && ret.as_ref().ok().is_none_or(|total|
        u64::from(spent).checked_add(u64::from(work)) == Some(u64::from(*total))))]
pub(crate) fn charge(
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
    use core::fmt::Write as _;

    use anodized::spec;

    use super::Source;
    use super::StreamEnd;
    use super::TokenReader;
    use super::charge;
    use crate::CanonicalWord;
    use crate::ChunkStore as _;
    use crate::ConstructorTag;
    use crate::ContentPtr;
    use crate::InMemoryChunkStore;
    use crate::TokenKind;
    use crate::TokenOffset;
    use crate::error::ValueError;
    use crate::frame_chunk;
    use crate::tokens::BodyWriter;
    use crate::tokens::Record;
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
        assert_eq!(enough.read_tag(), Ok(ConstructorTag::from(0x2A_u8)));
        assert_eq!(enough.read_word(), Ok(CanonicalWord::from(7_u64)));
        assert_eq!(enough.read_close(), Ok(()));
        assert!(anodized::types::Spec::predicate(&enough));
        assert_eq!(enough.spent(), DecodeWork::from(3_u64));

        let mut short = TokenReader::new(
            Source::Flat,
            TokenBody::from(body.as_slice()),
            DecodeWork::from(2_u64),
        );
        assert_eq!(short.read_tag(), Ok(ConstructorTag::from(0x2A_u8)));
        assert_eq!(short.read_word(), Ok(CanonicalWord::from(7_u64)));
        assert_eq!(
            short.read_close(),
            Err(ValueError::DecodeBudgetExceeded {
                spent: DecodeWork::from(3_u64),
                ceiling: DecodeWork::from(2_u64),
            })
        );
        assert_eq!(short.spent(), DecodeWork::from(2_u64));
        assert!(anodized::types::Spec::predicate(&short));
        short.spent = DecodeWork::from(3_u64);
        assert!(!anodized::types::Spec::predicate(&short));
        short.spent = DecodeWork::from(2_u64);
        short
            .suspended
            .push(super::Frame::at_start(TokenBody::from(&[][..])));
        assert!(!anodized::types::Spec::predicate(&short));
    }

    #[test]
    fn typed_reads_charge_payloads_and_refuse_wrong_kinds()
    {
        let body = [
            1_u8, 42, 2, 7, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 255, 5,
        ];
        let mut reader = TokenReader::over_flat(TokenBody::from(body.as_slice()));
        assert_eq!(reader.end(), StreamEnd::Continues);
        assert_eq!(
            reader.read_word(),
            Err(ValueError::UnexpectedToken {
                expected: TokenKind::Word,
                found: TokenKind::Open,
                position: TokenOffset::ZERO,
            })
        );
        assert_eq!(reader.spent(), DecodeWork::ZERO);
        assert_eq!(reader.read_tag(), Ok(ConstructorTag::from(42_u8)));
        assert_eq!(
            reader.read_bytes(),
            Err(ValueError::UnexpectedToken {
                expected: TokenKind::Bytes,
                found: TokenKind::Word,
                position: TokenOffset::from(1_u32),
            })
        );
        assert_eq!(
            reader.read_close(),
            Err(ValueError::UnexpectedToken {
                expected: TokenKind::Close,
                found: TokenKind::Word,
                position: TokenOffset::from(1_u32),
            })
        );
        assert_eq!(reader.spent(), DecodeWork::ONE);
        assert_eq!(reader.read_word(), Ok(CanonicalWord::from(7_u64)));
        let payload = reader
            .read_bytes()
            .expect("the literal binary payload reads");
        assert_eq!(payload.as_ref(), &[0_u8, 255]);
        assert!(core::ptr::eq(
            core::ptr::from_ref(payload.as_ref()),
            core::ptr::from_ref(body.get(20 .. 22).expect("the literal payload range"))
        ));
        assert_eq!(reader.position(), TokenOffset::from(3_u32));
        assert_eq!(reader.spent(), DecodeWork::from(5_u64));
        assert_eq!(reader.read_close(), Ok(()));
        assert_eq!(reader.position(), TokenOffset::from(4_u32));
        assert_eq!(reader.spent(), DecodeWork::from(6_u64));
        assert_eq!(reader.end(), StreamEnd::Ended);
        assert_eq!(
            reader.read_tag(),
            Err(ValueError::TruncatedStream {
                position: TokenOffset::from(4_u32),
            })
        );
    }

    #[test]
    fn payloads_and_closes_require_an_open_constructor()
    {
        let word = [2_u8, 7, 0, 0, 0, 0, 0, 0, 0];
        let bytes = [3_u8, 0, 0, 0, 0, 0, 0, 0, 0];
        let close = [5_u8];
        let mut reader = TokenReader::over_flat(TokenBody::from(word.as_slice()));
        assert_eq!(
            reader.read_word(),
            Err(ValueError::UnexpectedToken {
                expected: TokenKind::Open,
                found: TokenKind::Word,
                position: TokenOffset::ZERO,
            })
        );
        let mut reader = TokenReader::over_flat(TokenBody::from(bytes.as_slice()));
        assert_eq!(
            reader.read_bytes(),
            Err(ValueError::UnexpectedToken {
                expected: TokenKind::Open,
                found: TokenKind::Bytes,
                position: TokenOffset::ZERO,
            })
        );
        let mut reader = TokenReader::over_flat(TokenBody::from(close.as_slice()));
        assert_eq!(
            reader.read_close(),
            Err(ValueError::UnexpectedToken {
                expected: TokenKind::Open,
                found: TokenKind::Close,
                position: TokenOffset::ZERO,
            })
        );
    }

    #[test]
    fn seams_charge_images_and_restore_the_parent()
    {
        let child_bytes = [1_u8, 1, 5, 1, 2, 5];
        let child = frame_chunk(TokenBody::from(child_bytes.as_slice())).expect("the child frames");
        let child_image_bytes =
            u64::try_from(child.image().as_ref().len()).expect("a fixture image");
        let mut parent = BodyWriter::default();
        parent
            .push(Record::Open(ConstructorTag::from(0_u8)))
            .expect("the root opens");
        parent
            .push(Record::Child(ContentPtr::new(
                child.digest(),
                TokenOffset::from(2_u32),
            )))
            .expect("the interior child is addressed");
        parent
            .push(Record::Word(CanonicalWord::from(9_u64)))
            .expect("the parent word emits");
        parent.push(Record::Close).expect("the parent closes");
        let parent = frame_chunk(parent.as_body()).expect("the parent frames");
        let parent_image_bytes =
            u64::try_from(parent.image().as_ref().len()).expect("a fixture image");
        let mut store = InMemoryChunkStore::new();
        store.insert(child.as_verified()).expect("the child stores");
        let mut reader =
            TokenReader::over_chunk(&store, parent.as_verified()).expect("the root opens");
        assert_eq!(reader.spent(), DecodeWork::from(parent_image_bytes));
        assert_eq!(reader.position(), TokenOffset::ZERO);
        assert_eq!(reader.read_tag(), Ok(ConstructorTag::from(0_u8)));
        assert_eq!(reader.read_tag(), Ok(ConstructorTag::from(2_u8)));
        assert_eq!(usize::from(reader.seam_depth()), 1_usize);
        assert_eq!(reader.position(), TokenOffset::from(3_u32));
        assert_eq!(reader.read_close(), Ok(()));
        assert_eq!(usize::from(reader.seam_depth()), 0_usize);
        assert_eq!(reader.position(), TokenOffset::from(2_u32));
        assert_eq!(reader.end(), StreamEnd::Continues);
        assert_eq!(reader.read_word(), Ok(CanonicalWord::from(9_u64)));
        assert_eq!(reader.read_close(), Ok(()));
        assert_eq!(
            reader.spent(),
            DecodeWork::from(parent_image_bytes + child_image_bytes + 8_u64)
        );
        assert_eq!(reader.end(), StreamEnd::Ended);
        assert!(anodized::types::Spec::predicate(&reader));
    }

    #[test]
    fn skipping_does_not_interpret_child_records()
    {
        let mut body = BodyWriter::default();
        body.push(Record::Child(ContentPtr::new(
            crate::ChunkDigest::from([7_u8; 32]),
            TokenOffset::ZERO,
        )))
        .expect("the child record emits");
        body.push(Record::Open(ConstructorTag::from(42_u8)))
            .expect("the constructor emits");
        body.push(Record::Close).expect("the close emits");
        let mut reader = TokenReader::over_flat(body.as_body());
        assert_eq!(
            reader.read_tag(),
            Err(ValueError::SeamInFlatForm {
                position: TokenOffset::ZERO
            })
        );
        assert_eq!(reader.skip(TokenOffset::from(1_u32)), Ok(()));
        assert_eq!(reader.read_tag(), Ok(ConstructorTag::from(42_u8)));
        assert_eq!(reader.read_close(), Ok(()));
        assert_eq!(reader.position(), TokenOffset::from(3_u32));
        assert_eq!(reader.end(), StreamEnd::Ended);
        let mut reader = TokenReader::over_flat(body.as_body());
        assert_eq!(reader.skip(TokenOffset::from(3_u32)), Ok(()));
        assert_eq!(reader.end(), StreamEnd::Ended);
        assert_eq!(
            reader.skip(TokenOffset::from(1_u32)),
            Err(ValueError::TruncatedStream {
                position: TokenOffset::from(3_u32),
            })
        );
    }

    /// An output boundary that admits no writes.
    #[derive(Debug)]
    struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuses the offered diagnostic output.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: returns the formatting error.
        /// - provides: an unavailable diagnostic sink.
        /// - fails: always returns the formatting error.
        /// - panics: none.
        ///
        /// # Errors
        /// Always returns the formatting error.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on a reader diagnostic observes the exact refusal,
        ///   distinguishing accidental acceptance of unavailable output.
        /// - witness: `reader::tests::reader_diagnostics_omit_payload_data`
        #[spec(ensures: |ret| ret == Err(core::fmt::Error))]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn reader_diagnostics_omit_payload_data()
    {
        let body = [253_u8; 32];
        let reader = TokenReader::over_flat(TokenBody::from(body.as_slice()));
        let rendered = alloc::format!("{reader:?}");
        assert!(
            !rendered.contains("253"),
            "the token body's byte rendering is private"
        );
        assert_eq!(write!(RefusingSink, "{reader:?}"), Err(core::fmt::Error));
    }
}
