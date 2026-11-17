//! The sites of two reports, compared through the map of one rewrite.
//!
//! A rewrite moves text. So a parser obligation or a refusal that the
//! rewrite leaves alone can stand at another byte span in the candidate. The
//! map of the rewrite has two levels. Its pieces give each top-level form's
//! span in the text before the rewrite and in the candidate, in source
//! order. Its written leaves give, for each leaf of the candidate, the span
//! of the leaf it copies from the text before the rewrite. A leaf that the
//! rewrite writes itself copies none.
//!
//! A site compares as the piece that holds it and its offset inside that
//! piece. The offset counts the leaves of the text before the rewrite, and a
//! site of the candidate counts them through the leaves it copies. So the
//! layout can respace a piece, and a rewrite can respell the text around a
//! site, and the site stays. A site that no piece holds, or that starts or
//! ends at a leaf that the rewrite writes itself, compares equal to no site.

use alloc::vec::Vec;

use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::Piece;
use crate::leaf::Leaf;
use crate::material_leaves;

/// The map of one rewrite: its pieces, and the material leaves of the text
/// before it and of its candidate, each candidate leaf beside the span of the
/// leaf it copies.
///
/// # Specification
/// - requires: the pieces are in source order in both texts. The material
///   leaves of `written` and of the candidate pair one to one, as the formatter
///   checks before it compares reports.
/// - ensures: nothing.
/// - witness: `site::tests::a_respaced_piece_keeps_each_site_of_its_leaves`
#[derive(Clone, Debug)]
pub struct Sites<'map>
{
    /// Each top-level form's span before the rewrite and in the candidate.
    pieces: &'map [Piece],
    /// The span of each material leaf of the text before the rewrite.
    before: Vec<ByteSpan>,
    /// The span of each material leaf of the candidate, and the span of the
    /// leaf of the text before the rewrite that it copies.
    candidate: Vec<(ByteSpan, ByteSpan)>,
}

/// A site under the map.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Site
{
    /// The ordinal of the piece that holds it.
    piece: usize,
    /// The count of the piece's leaves, before the rewrite, that end at or
    /// before the site's start.
    start: usize,
    /// The count of the piece's leaves, before the rewrite, that start before
    /// the site's end.
    end: usize,
    /// The bytes from the start of the first leaf it reaches to its start,
    /// where it starts inside that leaf.
    inside_start: usize,
    /// The bytes from its end to the end of the last leaf it reaches, where it
    /// ends inside that leaf.
    inside_end: usize,
}

/// Why a span has no site.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unplaced
{
    /// No piece holds the span.
    Between,
    /// The span starts or ends at a leaf that the rewrite writes itself.
    Written,
}

/// Whether two sites are one site under the map.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Placement
{
    /// One site.
    Same,
    /// Two sites.
    Moved,
}

/// The ordinals of the leaves that a span reaches in a list of material
/// leaves: the first that does not end at or before its start, the count of
/// those that start before its end, and the bytes inside the leaves at its
/// two ends.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Reach
{
    /// The ordinal of the first leaf that does not end at or before the start.
    start: usize,
    /// The count of the leaves that start before the end.
    end: usize,
    /// The bytes from the first leaf's start to the span's start.
    inside_start: usize,
    /// The bytes from the span's end to the last leaf's end.
    inside_end: usize,
}

/// How `span` reaches the leaves whose spans `spans` reads from `leaves`.
///
/// # Specification
/// trivial.
fn reach<Item>(
    leaves: &[Item],
    spans: impl Fn(&Item) -> ByteSpan,
    span: ByteSpan,
) -> Reach
{
    let start = leaves.partition_point(|leaf| spans(leaf).end() <= span.start());
    let end = leaves.partition_point(|leaf| spans(leaf).start() < span.end());
    let inside_start = leaves
        .get(start)
        .map(&spans)
        .filter(|first| first.start() < span.start())
        .map_or(0, |first| {
            usize::from(span.start()).saturating_sub(usize::from(first.start()))
        });
    let inside_end = end
        .checked_sub(1)
        .and_then(|last| leaves.get(last))
        .map(&spans)
        .filter(|last| span.end() < last.end())
        .map_or(0, |last| {
            usize::from(last.end()).saturating_sub(usize::from(span.end()))
        });
    Reach {
        start,
        end,
        inside_start,
        inside_end,
    }
}

impl<'map> Sites<'map>
{
    /// The map of the rewrite whose pieces are `pieces`: `source` the leaves
    /// of the text before it, `written` the leaves the formatter wrote for its
    /// candidate, and `candidate` the leaves read back from the candidate.
    ///
    /// # Specification
    /// trivial.
    pub fn new(
        pieces: &'map [Piece],
        (source, written, candidate): (&[Leaf<'_>], &[Leaf<'_>], &[Leaf<'_>]),
    ) -> Self
    {
        Self {
            pieces,
            before: material_leaves(source).map(|leaf| leaf.span).collect(),
            candidate: material_leaves(candidate)
                .zip(material_leaves(written))
                .map(|(read, copied)| (read.span, copied.span))
                .collect(),
        }
    }

    /// The site of `span`, a span of the text before the rewrite in that
    /// text's own offsets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Present` exactly when one piece's source span holds `span`,
    ///   its ends included.
    /// - witness: `site::tests::a_site_between_pieces_has_no_place`
    pub fn before(
        &self,
        span: ByteSpan,
    ) -> Maybe<Site, Unplaced>
    {
        let Maybe::Present((piece, first)) = self.piece(span, |piece| piece.source)
        else {
            return Maybe::Absent(Unplaced::Between);
        };
        let reached = reach(&self.before, |&leaf| leaf, span);
        Maybe::Present(Site {
            piece,
            start: reached.start.saturating_sub(first),
            end: reached.end.saturating_sub(first),
            inside_start: reached.inside_start,
            inside_end: reached.inside_end,
        })
    }

    /// The site of `span`, a span of the candidate in its own offsets, read
    /// through the leaves each candidate leaf copies.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Present` exactly when one piece's formatted span holds
    ///   `span`, its ends included, and the leaves at its two ends copy leaves
    ///   of the text before the rewrite.
    /// - witness: `site::tests::a_respelled_piece_keeps_the_site_of_a_copied_leaf`
    pub fn candidate(
        &self,
        span: ByteSpan,
    ) -> Maybe<Site, Unplaced>
    {
        let Maybe::Present((piece, first)) = self.piece(span, |piece| piece.formatted)
        else {
            return Maybe::Absent(Unplaced::Between);
        };
        let reached = reach(&self.candidate, |&(read, _)| read, span);
        let copied = |ordinal: usize| match self.candidate.get(ordinal) {
            Some(&(_, copied)) => self
                .before
                .binary_search(&copied)
                .map_or(Maybe::Absent(Unplaced::Written), Maybe::Present),
            None => Maybe::Present(self.before.len()),
        };
        let start = match copied(reached.start) {
            Maybe::Present(start) => start,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let end = match reached.end.checked_sub(1) {
            Some(last) if reached.end > reached.start => match copied(last) {
                Maybe::Present(last) => last.saturating_add(1),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Some(_) | None => start,
        };
        Maybe::Present(Site {
            piece,
            start: start.saturating_sub(first),
            end: end.saturating_sub(first),
            inside_start: reached.inside_start,
            inside_end: reached.inside_end,
        })
    }

    /// The ordinal of the piece whose span, as `spanned` reads it, holds
    /// `span`, its ends included, and the ordinal of the first leaf before
    /// the rewrite that its source span holds.
    ///
    /// # Specification
    /// trivial.
    fn piece(
        &self,
        span: ByteSpan,
        spanned: impl Fn(&Piece) -> ByteSpan,
    ) -> Maybe<(usize, usize), Unplaced>
    {
        let after = self
            .pieces
            .partition_point(|piece| spanned(piece).start() <= span.start());
        let Some(ordinal) = after.checked_sub(1)
        else {
            return Maybe::Absent(Unplaced::Between);
        };
        let Some(piece) = self.pieces.get(ordinal)
        else {
            return Maybe::Absent(Unplaced::Between);
        };
        if span.end() > spanned(piece).end() {
            return Maybe::Absent(Unplaced::Between);
        }
        let first = self
            .before
            .partition_point(|leaf| leaf.start() < piece.source.start());
        Maybe::Present((ordinal, first))
    }

    /// Whether `before`, a span of a report on the text before the rewrite,
    /// and `candidate`, a span of the candidate's report, are one site. Both
    /// are spans of a unit's text in which each text starts at `base`, absent
    /// where the report names none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Same` where both are absent for equal reasons, where both
    ///   are present, either ends at or before `base` and the two are equal, or
    ///   where both are present, start at or after `base`, and
    ///   [`Sites::spanned`] places them as one in each text's own offsets.
    ///   `Moved` otherwise.
    /// - witness: `site::tests::a_site_between_pieces_has_no_place`
    pub fn placed<Reason>(
        &self,
        base: ByteOffset,
        (before, candidate): (Maybe<ByteSpan, Reason>, Maybe<ByteSpan, Reason>),
    ) -> Placement
    where
        Reason: PartialEq,
    {
        let own = |span: ByteSpan| {
            let shift = |offset: ByteOffset| {
                usize::from(offset)
                    .checked_sub(usize::from(base))
                    .map(ByteOffset::from)
            };
            ByteSpan::new(shift(span.start())?, shift(span.end())?).ok()
        };
        match (before, candidate) {
            (Maybe::Present(before), Maybe::Present(candidate))
                if before.end() <= base || candidate.end() <= base =>
            {
                if before == candidate {
                    Placement::Same
                }
                else {
                    Placement::Moved
                }
            },
            (Maybe::Present(before), Maybe::Present(candidate)) => {
                match (own(before), own(candidate)) {
                    (Some(before), Some(candidate)) => self.spanned(before, candidate),
                    (Some(_) | None, _) => Placement::Moved,
                }
            },
            (Maybe::Absent(before), Maybe::Absent(candidate)) if before == candidate => {
                Placement::Same
            },
            (Maybe::Absent(_), _) | (Maybe::Present(_), Maybe::Absent(_)) => Placement::Moved,
        }
    }

    /// Whether `before`, a span of the text before the rewrite, and
    /// `candidate`, a span of the candidate, each in its text's own offsets,
    /// are one site.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Same` exactly when both have a site and the sites are equal.
    /// - witness: `site::tests::a_respaced_piece_keeps_each_site_of_its_leaves`
    /// - witness: `site::tests::a_site_in_another_piece_is_moved`
    pub fn spanned(
        &self,
        before: ByteSpan,
        candidate: ByteSpan,
    ) -> Placement
    {
        match (self.before(before), self.candidate(candidate)) {
            (Maybe::Present(left), Maybe::Present(right)) if left == right => Placement::Same,
            (Maybe::Present(_) | Maybe::Absent(_), _) => Placement::Moved,
        }
    }
}

#[cfg(test)]
mod tests;
