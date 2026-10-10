//! Byte-addressed source positions: [`SourceText`], [`ByteOffset`],
//! [`ByteLength`] and [`ByteSpan`].
//!
//! A position is a byte offset rather than a line and column pair. Lines are a
//! rendering concern that costs a table to compute and invalidates on every
//! edit; a byte offset is what the lexer already has, what an edit is expressed
//! against, and what a diagnostic renderer converts once at the point of
//! display.
//!
//! Offsets are `usize`-backed, so no span in a tree is a width conversion away
//! from a failure that a test could never trigger: a span either lies inside
//! the source it is read against or it does not, and both answers are reachable
//! from a two-byte fixture.

use core::fmt;

use anodized::spec;

use crate::error::SyntaxError;

/// The complete source text one syntax tree was parsed from.
///
/// Every span in a tree is read against the text the tree was built over, so
/// the tree borrows it rather than copying the fragment each node covers.
///
/// This is the **offset frame**: a [`ByteSpan`] means what it means relative to
/// one of these and to nothing else. The bytes a span covers come back as a
/// [`SourceFragment`], a different type, so a fragment cannot stand in for the
/// source it was cut from — which would silently reinterpret every absolute
/// offset against a string that starts somewhere else.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceText<'source>(&'source str);

/// The bytes one span covers: a slice of some [`SourceText`], carrying no
/// offset frame of its own.
///
/// Deliberately not a [`SourceText`]. A fragment answers "what does this node
/// say", never "what do offsets mean", so it has no `end` and no `fragment` of
/// its own and cannot be handed to a [`TreeBuilder`] as a source. Each of those
/// three would be a frame confusion — a width read as a position, an absolute
/// offset re-read against a substring, every span in a tree validated against
/// the wrong text — and each is now a compile error rather than a wrong answer.
///
/// [`TreeBuilder`]: crate::TreeBuilder
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceFragment<'source>(&'source str);

impl<'source> From<&'source str> for SourceFragment<'source>
{
    /// Adopt borrowed text as the fragment it spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'source str) -> Self
    {
        Self(text)
    }
}

impl<'source> From<SourceFragment<'source>> for &'source str
{
    /// Read the fragment's borrowed text back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fragment: SourceFragment<'source>) -> Self
    {
        fragment.0
    }
}

impl AsRef<str> for SourceFragment<'_>
{
    /// Borrow the fragment's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for SourceFragment<'_>
{
    /// Write the fragment's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly the bytes the fragment covers, neither escaped
    ///   nor quoted, so the rendering of a lexeme is the lexeme.
    /// - provides: the quoted text a diagnostic renderer places in its message.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter's write-only sink exposes neither
    ///   emitted bytes nor its eventual failure to a return-value predicate;
    ///   repeating the writes would change that sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact output at empty, ordinary and boundary values
    ///   detects payload loss and altered rendering; a rejecting sink detects a
    ///   swallowed write failure.
    /// - witness: `span::tests::formatters_preserve_text_and_numeric_options`
    /// - witness: `span::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

impl<'source> From<&'source str> for SourceText<'source>
{
    /// Adopt borrowed text as the source one tree is read against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'source str) -> Self
    {
        Self(text)
    }
}

impl<'source> From<SourceText<'source>> for &'source str
{
    /// Read the source's borrowed text back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: SourceText<'source>) -> Self
    {
        text.0
    }
}

impl AsRef<str> for SourceText<'_>
{
    /// Borrow the source's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for SourceText<'_>
{
    /// Write the source text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the whole text, neither escaped nor truncated, so a
    ///   rendering carries every offset frame position it names.
    /// - provides: the source echo a diagnostic renderer prints around a span.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter's write-only sink exposes neither
    ///   emitted bytes nor its eventual failure to a return-value predicate;
    ///   repeating the writes would change that sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact output at empty, ordinary and boundary values
    ///   detects payload loss and altered rendering; a rejecting sink detects a
    ///   swallowed write failure.
    /// - witness: `span::tests::formatters_preserve_text_and_numeric_options`
    /// - witness: `span::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

impl<'source> SourceText<'source>
{
    /// Compare represented values during constant evaluation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn const_eq(
        self,
        other: Self,
    ) -> crate::ConstEquality
    {
        let mut left = self.0.as_bytes();
        let mut right = other.0.as_bytes();
        let mut same = left.len() == right.len();
        while let (Some((a, rest_a)), Some((b, rest_b))) = (left.split_first(), right.split_first())
        {
            same = same && *a == *b;
            left = rest_a;
            right = rest_b;
        }
        if same {
            crate::ConstEquality::Equal
        }
        else {
            crate::ConstEquality::Unequal
        }
    }

    /// The offset one byte past the last byte of this text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the offset one past this text's last byte, measured in the
    ///   frame this text is itself the origin of.
    /// - provides: the bound [`SourceText::fragment`] refuses a span above, and
    ///   the end an empty span at the text's tail carries.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, ASCII and multibyte UTF-8 sources expose
    ///   byte-count versus character-count and off-by-one mutations through
    ///   their exact end offsets.
    /// - witness: `span::tests::a_source_end_is_its_byte_length`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == self.0.len())]
    pub fn end(self) -> ByteOffset
    {
        ByteOffset(self.0.len())
    }

    /// The fragment `span` covers.
    ///
    /// # Specification
    /// - requires: nothing — every span is admissible input, and a span this
    ///   text cannot answer is refused rather than clamped.
    /// - ensures: the returned fragment is exactly the bytes of `self` from the
    ///   span's start up to, and not including, its end; it comes back as a
    ///   [`SourceFragment`], which carries no offset frame, so it cannot be
    ///   read back as the source these offsets were measured against.
    /// - provides: the lexeme a node contributes to its content digest, and the
    ///   text a diagnostic quotes for a node.
    /// - fails: [`SyntaxError::SpanOutsideSource`] when the span's end is above
    ///   this text's end; [`SyntaxError::SpanSplitsCharacter`] when an endpoint
    ///   falls inside a multi-byte character. The out-of-source fault is
    ///   decided first, and between the two endpoints the start is reported
    ///   first, so one span with two faults has one determined refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SyntaxError::SpanOutsideSource`] when `span.end()` exceeds
    /// [`SourceText::end`]; [`SyntaxError::SpanSplitsCharacter`] when either
    /// endpoint is not a character boundary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three decision surfaces (the end-past-source
    ///   comparison, the start boundary test, the end boundary test) separated
    ///   by the boundary pair `end == source_end` / `end == source_end + 1`, by
    ///   a start inside a two-byte character, and by an end inside one, each
    ///   asserted as an exact variant with its exact payload; the success arm
    ///   is asserted as an exact fragment on both an empty and a whole-source
    ///   span.
    /// - witness: `span::tests::a_span_inside_the_source_names_its_fragment`
    /// - witness: `span::tests::an_empty_span_names_the_empty_fragment`
    /// - witness: `span::tests::a_span_ending_at_the_source_end_is_admitted`
    /// - witness: `span::tests::a_span_one_byte_past_the_source_end_is_refused`
    /// - witness: `span::tests::a_start_inside_a_character_is_refused`
    /// - witness: `span::tests::an_end_inside_a_character_is_refused`
    /// - witness: `span::tests::fragment_faults_have_deterministic_precedence`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(fragment) => self.0.get(span.start.0 .. span.end.0) == Some(fragment.0),
        Err(SyntaxError::SpanOutsideSource { span: refused, source_end }) =>
            refused == span && source_end.0 == self.0.len() && span.end.0 > self.0.len(),
        Err(SyntaxError::SpanSplitsCharacter { offset }) =>
            span.end.0 <= self.0.len()
                && offset == if self.0.is_char_boundary(span.start.0) { span.end } else { span.start }
                && !self.0.is_char_boundary(offset.0),
        Err(_) => false,
    })]
    pub fn fragment(
        self,
        span: ByteSpan,
    ) -> Result<SourceFragment<'source>, SyntaxError>
    {
        let Some(fragment) = self.0.get(span.start.0 .. span.end.0)
        else {
            let source_end = self.end();
            if span.end > source_end {
                return Err(SyntaxError::SpanOutsideSource { span, source_end });
            }
            if !self.0.is_char_boundary(span.start.0) {
                return Err(SyntaxError::SpanSplitsCharacter { offset: span.start });
            }

            return Err(SyntaxError::SpanSplitsCharacter { offset: span.end });
        };

        Ok(SourceFragment(fragment))
    }
}

/// A zero-based byte offset into a source text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteOffset(usize);

impl From<usize> for ByteOffset
{
    /// Read a `usize` as an offset into some source text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: usize) -> Self
    {
        Self(offset)
    }
}

impl From<ByteOffset> for usize
{
    /// Read the offset back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: ByteOffset) -> Self
    {
        offset.0
    }
}

impl fmt::Display for ByteOffset
{
    /// Write the offset.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried count through the `usize` rendering, so
    ///   the width, fill, and sign options the caller set apply to it.
    /// - provides: the position a diagnostic quotes.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter's write-only sink exposes neither
    ///   emitted bytes nor its eventual failure to a return-value predicate;
    ///   repeating the writes would change that sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact output at empty, ordinary and boundary values
    ///   detects payload loss and altered rendering; a rejecting sink detects a
    ///   swallowed write failure.
    /// - witness: `span::tests::formatters_preserve_text_and_numeric_options`
    /// - witness: `span::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// A byte extent: the width of a span, never a position in a text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteLength(usize);

impl From<usize> for ByteLength
{
    /// Read a `usize` as a byte extent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: usize) -> Self
    {
        Self(length)
    }
}

impl From<ByteLength> for usize
{
    /// Read the extent back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: ByteLength) -> Self
    {
        length.0
    }
}

impl fmt::Display for ByteLength
{
    /// Write the extent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried count through the `usize` rendering, so
    ///   the width, fill, and sign options the caller set apply to it.
    /// - provides: the width a renderer reports for a node.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter's write-only sink exposes neither
    ///   emitted bytes nor its eventual failure to a return-value predicate;
    ///   repeating the writes would change that sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact output at empty, ordinary and boundary values
    ///   detects payload loss and altered rendering; a rejecting sink detects a
    ///   swallowed write failure.
    /// - witness: `span::tests::formatters_preserve_text_and_numeric_options`
    /// - witness: `span::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// The half-open byte range `[start, end)` one token or node covers.
///
/// The range is half-open so an empty span is expressible at every position and
/// two adjacent spans meet without overlapping, which is what lets a parent's
/// span be the join of its children's without arithmetic on widths.
///
/// # Specification
/// - ensures: the start never exceeds the end; equal endpoints name an empty
///   range, not an invalid span.
/// - executable: none — this type has no call boundary; its construction and
///   joining obligations belong to `ByteSpan::new` and `ByteSpan::join`.
///
/// # Adequacy
/// - hypothesis: L3 — ordered, equal and inverted endpoint pairs distinguish
///   retained endpoints, emptiness and refusal; exact endpoints and errors
///   detect swapping, clamping and an off-by-one ordering guard.
/// - witness: `span::tests::an_ordinary_span_keeps_its_endpoints`
/// - witness: `span::tests::an_empty_span_is_admitted`
/// - witness: `span::tests::an_inverted_span_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteSpan
{
    /// The offset of the first byte covered.
    start: ByteOffset,
    /// The offset one byte past the last byte covered.
    end: ByteOffset,
}

impl fmt::Display for ByteSpan
{
    /// Write the span as its two endpoints.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the start, the two-dot range operator, and the end, in
    ///   that order — the half-open reading the type carries, so an empty span
    ///   renders as a position repeated rather than as nothing.
    /// - provides: the span notation a diagnostic and a test failure message
    ///   both read.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter's write-only sink exposes neither
    ///   emitted bytes nor its eventual failure to a return-value predicate;
    ///   repeating the writes would change that sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact output at empty, ordinary and boundary values
    ///   detects payload loss and altered rendering; a rejecting sink detects a
    ///   swallowed write failure.
    /// - witness: `span::tests::formatters_preserve_text_and_numeric_options`
    /// - witness: `span::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl ByteSpan
{
    /// Compare represented values during constant evaluation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn const_eq(
        self,
        other: Self,
    ) -> crate::ConstEquality
    {
        if self.start.0 == other.start.0 && self.end.0 == other.end.0 {
            crate::ConstEquality::Equal
        }
        else {
            crate::ConstEquality::Unequal
        }
    }

    /// The span from `start` up to, and not including, `end`.
    ///
    /// # Specification
    /// - requires: nothing — an inverted pair is admissible input and is
    ///   refused rather than reordered, because silently swapping the endpoints
    ///   would turn a mis-measured lexeme into a plausible one.
    /// - ensures: on success the span's start and end are exactly the offered
    ///   offsets, and its start is at or below its end.
    /// - provides: the only way to mint a span, so the ordering invariant holds
    ///   of every span a tree carries.
    /// - fails: [`SyntaxError::InvertedSpan`], carrying both offered offsets,
    ///   when `end` is strictly below `start`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SyntaxError::InvertedSpan`] when `end < start`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one comparison, separated by the boundary triple
    ///   `start < end`, `start == end` and `start == end + 1`, the first two
    ///   asserted as exact spans and the third as the exact error variant with
    ///   both offsets.
    /// - witness: `span::tests::an_ordinary_span_keeps_its_endpoints`
    /// - witness: `span::tests::an_empty_span_is_admitted`
    /// - witness: `span::tests::an_inverted_span_is_refused`
    #[spec(ensures: |ref ret| match *ret {
        Ok(span) => start.0 <= end.0 && span.start.0 == start.0 && span.end.0 == end.0,
        Err(SyntaxError::InvertedSpan { start: actual_start, end: actual_end }) =>
            end.0 < start.0 && actual_start.0 == start.0 && actual_end.0 == end.0,
        Err(_) => false,
    })]
    #[inline]
    pub const fn new(
        start: ByteOffset,
        end: ByteOffset,
    ) -> Result<Self, SyntaxError>
    {
        if end.0 < start.0 {
            return Err(SyntaxError::InvertedSpan { start, end });
        }

        Ok(Self { start, end })
    }

    /// The offset of the first byte covered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(self) -> ByteOffset
    {
        self.start
    }

    /// The offset one byte past the last byte covered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(self) -> ByteOffset
    {
        self.end
    }

    /// The number of bytes covered.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the difference between the endpoints, which is exact because
    ///   [`ByteSpan::new`] admits no inverted span, so the saturating
    ///   subtraction never reaches its floor.
    /// - provides: the width a renderer allots to a node.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one subtraction, separated by an empty span and
    ///   a multi-byte span, each asserted as an exact length.
    /// - witness: `span::tests::a_span_length_is_its_byte_extent`
    #[spec(ensures: |ret| ret.0 == self.end.0.saturating_sub(self.start.0))]
    #[inline]
    #[must_use]
    pub const fn length(self) -> ByteLength
    {
        ByteLength(self.end.0.saturating_sub(self.start.0))
    }

    /// The smallest span covering both `self` and `other`.
    ///
    /// # Specification
    /// - requires: nothing — the two spans need not overlap or be ordered.
    /// - ensures: the result starts at the lower of the two starts and ends at
    ///   the higher of the two ends, so it covers every byte either covers.
    /// - provides: the span a parser gives a node built over already-spanned
    ///   children.
    /// - fails: never — the result is ordered by construction, so no minting
    ///   check is needed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — two independent selections, separated by a pair
    ///   in each order, a nested pair, and a disjoint pair, each asserted as an
    ///   exact span; the argument-order case is what a swapped minimum or
    ///   maximum fails.
    /// - witness: `span::tests::joining_two_spans_covers_both`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| {
        ret.start.0 == self.start.0.min(other.start.0)
            && ret.end.0 == self.end.0.max(other.end.0)
    })]
    pub fn join(
        self,
        other: Self,
    ) -> Self
    {
        let start = if self.start.0 < other.start.0 {
            self.start
        }
        else {
            other.start
        };
        let end = if self.end.0 > other.end.0 {
            self.end
        }
        else {
            other.end
        };

        Self { start, end }
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;

    use super::ByteLength;
    use super::ByteOffset;
    use super::ByteSpan;
    use super::SourceFragment;
    use super::SourceText;
    use crate::error::SyntaxError;

    /// A two-byte character followed by two one-byte characters: the boundary
    /// fixture every character-boundary case is separated by.
    const ACCENTED: &str = "\u{e9}ab";

    /// Mint a span from two offsets, for a test that is not about minting.
    ///
    /// # Specification
    /// - requires: `start` is at or below `end`; a test about minting offers an
    ///   inverted pair to [`ByteSpan::new`] itself.
    /// - ensures: the span carrying exactly those endpoints.
    /// - provides: the span every fixture that is not about minting is read
    ///   against.
    /// - panics: when the endpoints are inverted, so a fixture that violates
    ///   the precondition fails its own test rather than reading a span the
    ///   crate would have refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordered and equal endpoints are observed through
    ///   exact start, end and extent values; endpoint swaps or clamping differ.
    /// - witness: `span::tests::an_ordinary_span_keeps_its_endpoints`
    /// - witness: `span::tests::a_span_length_is_its_byte_extent`
    #[spec(
        requires: start <= end,
        ensures: |ret| ret.start() == start && ret.end() == end,
    )]
    fn span(
        start: ByteOffset,
        end: ByteOffset,
    ) -> ByteSpan
    {
        ByteSpan::new(start, end).unwrap()
    }

    #[test]
    fn an_ordinary_span_keeps_its_endpoints()
    {
        let subject = span(ByteOffset::from(2_usize), ByteOffset::from(5_usize));

        assert_eq!(
            subject.start(),
            ByteOffset::from(2_usize),
            "the start is the offered start"
        );
        assert_eq!(
            subject.end(),
            ByteOffset::from(5_usize),
            "the end is the offered end"
        );
    }

    #[test]
    fn an_empty_span_is_admitted()
    {
        let subject = ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(4_usize));

        assert_eq!(
            subject,
            Ok(span(ByteOffset::from(4_usize), ByteOffset::from(4_usize))),
            "coincident endpoints are the admitted boundary"
        );
    }

    #[test]
    fn an_inverted_span_is_refused()
    {
        let subject = ByteSpan::new(ByteOffset::from(5_usize), ByteOffset::from(4_usize));

        assert_eq!(
            subject,
            Err(SyntaxError::InvertedSpan {
                start: ByteOffset::from(5_usize),
                end: ByteOffset::from(4_usize),
            }),
            "one byte below the start is the refused boundary"
        );
    }

    #[test]
    fn a_span_length_is_its_byte_extent()
    {
        assert_eq!(
            span(ByteOffset::from(4_usize), ByteOffset::from(4_usize)).length(),
            ByteLength::from(0_usize),
            "an empty span is zero bytes wide"
        );
        assert_eq!(
            span(ByteOffset::from(2_usize), ByteOffset::from(7_usize)).length(),
            ByteLength::from(5_usize),
            "a span is exactly its endpoint difference wide"
        );
    }

    #[test]
    fn joining_two_spans_covers_both()
    {
        assert_eq!(
            span(ByteOffset::from(2_usize), ByteOffset::from(4_usize))
                .join(span(ByteOffset::from(6_usize), ByteOffset::from(9_usize))),
            span(ByteOffset::from(2_usize), ByteOffset::from(9_usize)),
            "disjoint spans join into the range spanning both"
        );
        assert_eq!(
            span(ByteOffset::from(6_usize), ByteOffset::from(9_usize))
                .join(span(ByteOffset::from(2_usize), ByteOffset::from(4_usize))),
            span(ByteOffset::from(2_usize), ByteOffset::from(9_usize)),
            "the join does not depend on argument order"
        );
        assert_eq!(
            span(ByteOffset::from(2_usize), ByteOffset::from(9_usize))
                .join(span(ByteOffset::from(4_usize), ByteOffset::from(6_usize))),
            span(ByteOffset::from(2_usize), ByteOffset::from(9_usize)),
            "a nested span leaves the enclosing one unchanged"
        );
    }

    #[test]
    fn a_span_inside_the_source_names_its_fragment()
    {
        let source = SourceText::from("def name");

        assert_eq!(
            source.fragment(span(ByteOffset::from(4_usize), ByteOffset::from(8_usize))),
            Ok(SourceFragment::from("name")),
            "the fragment is exactly the covered bytes"
        );
    }

    #[test]
    fn an_empty_span_names_the_empty_fragment()
    {
        let source = SourceText::from("def");

        assert_eq!(
            source.fragment(span(ByteOffset::from(1_usize), ByteOffset::from(1_usize))),
            Ok(SourceFragment::from("")),
            "an empty span names the empty fragment rather than failing"
        );
    }

    #[test]
    fn a_span_ending_at_the_source_end_is_admitted()
    {
        let source = SourceText::from("ab");

        assert_eq!(
            source.fragment(span(ByteOffset::from(0_usize), ByteOffset::from(2_usize))),
            Ok(SourceFragment::from("ab")),
            "a span reaching exactly the source end is admitted"
        );
    }

    #[test]
    fn a_span_one_byte_past_the_source_end_is_refused()
    {
        let source = SourceText::from("ab");

        assert_eq!(
            source.fragment(span(ByteOffset::from(0_usize), ByteOffset::from(3_usize))),
            Err(SyntaxError::SpanOutsideSource {
                span: span(ByteOffset::from(0_usize), ByteOffset::from(3_usize)),
                source_end: ByteOffset::from(2_usize),
            }),
            "one byte past the end is the refused boundary"
        );
    }

    #[test]
    fn a_start_inside_a_character_is_refused()
    {
        let source = SourceText::from(ACCENTED);

        assert_eq!(
            source.fragment(span(ByteOffset::from(1_usize), ByteOffset::from(3_usize))),
            Err(SyntaxError::SpanSplitsCharacter {
                offset: ByteOffset::from(1_usize),
            }),
            "a start inside the two-byte character names that start"
        );
    }

    #[test]
    fn an_end_inside_a_character_is_refused()
    {
        let source = SourceText::from(ACCENTED);

        assert_eq!(
            source.fragment(span(ByteOffset::from(0_usize), ByteOffset::from(1_usize))),
            Err(SyntaxError::SpanSplitsCharacter {
                offset: ByteOffset::from(1_usize),
            }),
            "an end inside the two-byte character names that end"
        );
    }

    #[test]
    fn fragment_faults_have_deterministic_precedence()
    {
        let source = SourceText::from("éé");
        let outside = span(ByteOffset::from(1_usize), ByteOffset::from(5_usize));
        assert_eq!(
            source.fragment(outside),
            Err(SyntaxError::SpanOutsideSource {
                span: outside,
                source_end: ByteOffset::from(4_usize),
            })
        );
        let both_split = span(ByteOffset::from(1_usize), ByteOffset::from(3_usize));
        assert_eq!(
            source.fragment(both_split),
            Err(SyntaxError::SpanSplitsCharacter {
                offset: ByteOffset::from(1_usize),
            })
        );
        let tail = span(ByteOffset::from(4_usize), ByteOffset::from(4_usize));
        assert_eq!(source.fragment(tail), Ok(SourceFragment::from("")));
    }

    #[test]
    fn formatters_preserve_text_and_numeric_options()
    {
        for text in ["", "é\n\"", "source"] {
            assert_eq!(alloc::format!("{}", SourceText::from(text)), text);
            assert_eq!(alloc::format!("{}", SourceFragment::from(text)), text);
        }
        for count in [0_usize, 12, usize::MAX] {
            assert_eq!(
                alloc::format!("{:*>+24}", ByteOffset::from(count)),
                alloc::format!("{count:*>+24}")
            );
            assert_eq!(
                alloc::format!("{:*>+24}", ByteLength::from(count)),
                alloc::format!("{count:*>+24}")
            );
        }
        assert_eq!(
            alloc::format!("{}", span(ByteOffset::from(0), ByteOffset::from(0))),
            "0..0"
        );
        assert_eq!(
            alloc::format!("{}", span(ByteOffset::from(2), ByteOffset::from(17))),
            "2..17"
        );
    }

    #[test]
    fn formatters_propagate_sink_failure()
    {
        use core::fmt::Write as _;
        let mut sink = crate::test_support::RefusingSink;
        assert!(
            sink.write_fmt(format_args!("{}", SourceText::from("x")))
                .is_err()
        );
        assert!(
            sink.write_fmt(format_args!("{}", SourceFragment::from("x")))
                .is_err()
        );
        assert!(
            sink.write_fmt(format_args!("{}", ByteOffset::from(0)))
                .is_err()
        );
        assert!(
            sink.write_fmt(format_args!("{}", ByteLength::from(0)))
                .is_err()
        );
        assert!(
            sink.write_fmt(format_args!(
                "{}",
                span(ByteOffset::from(0), ByteOffset::from(0))
            ))
            .is_err()
        );
    }

    #[test]
    fn a_source_end_is_its_byte_length()
    {
        for (text, length) in [("", 0_usize), ("ab", 2), (ACCENTED, 4)] {
            assert_eq!(SourceText::from(text).end(), ByteOffset::from(length));
        }
    }
}
