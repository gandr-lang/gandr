//! The sites of two reports, compared through the map of one rewrite.
//!
//! A rewrite moves text. So a parser obligation or a refusal that the
//! rewrite leaves alone can stand at another byte span in the candidate.
//! Each pass of the formatter carries its own map at the leaves. The leaves
//! it wrote pair one to one with the leaves read back from the candidate,
//! because the formatter refuses two lists of unequal material. A leaf the
//! pass copies keeps the span it has in the text before the rewrite, and a
//! leaf a rewrite writes names the form it respells.
//!
//! A site maps by its two ends. An end at the start, the end or an offset of
//! a copied leaf maps to the same place of the paired leaf. An end at the
//! start or the end of a respelled form maps to the start of the first leaf
//! the pass wrote for the form, or to the end of the last one. An end inside
//! a tile the pass replaces, or inside layout, has no image, so its site
//! equals no site. The search reads the source span of each copied leaf and
//! assumes no order of the pairs, since a rewrite can change the order of
//! its operands.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::leaf::Leaf;
use crate::leaf::Origin;
use crate::paired;

/// The map of one pass: each leaf it copies, and each form it respells.
///
/// # Specification
/// - requires: the material leaves of the written leaves and of the candidate
///   pair one to one, as the formatter checks before it compares reports.
/// - ensures: nothing.
/// - witness: `site::tests::a_respaced_text_keeps_each_site_of_a_copied_leaf`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Sites
{
    /// Each copied leaf: its span in the text before the pass and its span in
    /// the candidate, ordered by the first.
    copied: Vec<(ByteSpan, ByteSpan)>,
    /// Each respelled form: its extent in the text before the pass and the
    /// span that its leaves cover in the candidate, ordered by the extent's
    /// start.
    starts: Vec<(ByteSpan, ByteSpan)>,
    /// The respelled forms again, ordered by the extent's end.
    ends: Vec<(ByteSpan, ByteSpan)>,
}

/// Whether two sites are one site under the map.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Placement
{
    /// One site.
    Same,
    /// Two sites, or a site with no image.
    Moved,
}

impl Sites
{
    /// The map of the pass whose written leaves are `written`, read back
    /// from its candidate as `candidate`.
    ///
    /// # Specification
    /// - requires: as [`Sites`].
    /// - ensures: each respelled form's leaves are the run of paired leaves
    ///   around the leaves its rewrite wrote, each copied from inside its
    ///   extent or written for a form inside it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the map is the pass's leaves, which a predicate
    ///   over the answer would pair again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a respelled form whose operands the pass copies maps
    ///   its ends to the ends of its leaves, and an end inside the tile it
    ///   replaces has no image.
    /// - witness: `site::tests::a_respelled_form_maps_its_ends_to_its_leaves`
    ///
    /// # Cost
    /// - allocation: the pairs, the copied leaves and the respelled forms,
    ///   growth within the candidate's leaves
    pub fn new(
        written: &[Leaf<'_>],
        candidate: &[Leaf<'_>],
    ) -> Self
    {
        let pairs: Vec<(Origin, ByteSpan, ByteSpan)> = paired(written, candidate)
            .unwrap_or_default()
            .into_iter()
            .map(|(wrote, read)| (wrote.origin, wrote.span, read.span))
            .collect();
        let mut copied: Vec<(ByteSpan, ByteSpan)> = pairs
            .iter()
            .filter(|&&(origin, ..)| origin == Origin::Source)
            .map(|&(_, source, read)| (source, read))
            .collect();
        copied.sort_unstable();
        // The first and the last pair that each rewrite wrote a leaf of.
        let mut anchors: BTreeMap<ByteSpan, (usize, usize)> = BTreeMap::new();
        for (ordinal, &(origin, ..)) in pairs.iter().enumerate() {
            if let Origin::Rewrite(form) = origin {
                anchors
                    .entry(form)
                    .and_modify(|anchor| anchor.1 = ordinal)
                    .or_insert((ordinal, ordinal));
            }
        }
        // Whether the pair at `ordinal` belongs to `form`: a leaf copied from
        // inside its extent, or a leaf written for a form inside it.
        let inside = |form: ByteSpan, ordinal: usize| {
            pairs.get(ordinal).is_some_and(|&(origin, source, _)| {
                let within = match origin {
                    Origin::Source => source,
                    Origin::Rewrite(within) => within,
                };
                form.start() <= within.start() && within.end() <= form.end()
            })
        };
        let mut starts: Vec<(ByteSpan, ByteSpan)> = anchors
            .into_iter()
            .filter_map(|(form, (mut first, mut last))| {
                while first
                    .checked_sub(1)
                    .is_some_and(|before| inside(form, before))
                {
                    first = first.saturating_sub(1);
                }
                while inside(form, last.saturating_add(1)) {
                    last = last.saturating_add(1);
                }
                let (&(_, _, opens), &(_, _, closes)) = (pairs.get(first)?, pairs.get(last)?);
                Some((form, ByteSpan::new(opens.start(), closes.end()).ok()?))
            })
            .collect();
        starts.sort_unstable();
        let mut ends = starts.clone();
        ends.sort_unstable_by_key(|&(form, _)| (form.end(), form.start()));
        Self {
            copied,
            starts,
            ends,
        }
    }

    /// Whether `image`, an offset of the candidate, is an image of `place`, an
    /// offset of the text before the pass.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Same` exactly when a copied leaf's source span holds `place`
    ///   and its candidate span holds `image` at the same offset, or a
    ///   respelled form starts at `place` and its leaves start at `image`, or
    ///   it ends at `place` and its leaves end at `image`. `Moved` otherwise.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a search of the map, which a
    ///   predicate over the answer would search again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an offset at the start, the end and inside a copied
    ///   leaf reaches its image, and an offset at another copy of its text or
    ///   in layout reaches none.
    /// - witness: `site::tests::a_respelled_form_maps_its_ends_to_its_leaves`
    /// - witness: `site::tests::a_site_at_another_copy_or_in_layout_is_moved`
    fn reaches(
        &self,
        place: ByteOffset,
        image: ByteOffset,
    ) -> Placement
    {
        let first = self
            .copied
            .partition_point(|&(source, _)| source.end() < place);
        let copied = self
            .copied
            .get(first ..)
            .unwrap_or_default()
            .iter()
            .take_while(|&&(source, _)| source.start() <= place)
            .any(|&(source, read)| {
                usize::from(place)
                    .checked_sub(usize::from(source.start()))
                    .and_then(|offset| usize::from(read.start()).checked_add(offset))
                    == Some(usize::from(image))
            });
        let opened = {
            let first = self
                .starts
                .partition_point(|&(form, _)| form.start() < place);
            self.starts
                .get(first ..)
                .unwrap_or_default()
                .iter()
                .take_while(|&&(form, _)| form.start() == place)
                .any(|&(_, leaves)| leaves.start() == image)
        };
        let closed = {
            let first = self.ends.partition_point(|&(form, _)| form.end() < place);
            self.ends
                .get(first ..)
                .unwrap_or_default()
                .iter()
                .take_while(|&&(form, _)| form.end() == place)
                .any(|&(_, leaves)| leaves.end() == image)
        };
        if copied || opened || closed {
            Placement::Same
        }
        else {
            Placement::Moved
        }
    }

    /// Whether `before`, a span of the text before the pass, and `candidate`,
    /// a span of the candidate, each in its text's own offsets, are one site.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Same` exactly when `candidate`'s start is an image of
    ///   `before`'s start and its end an image of `before`'s end.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is two searches of the map, which a
    ///   predicate over the answer would search again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a respaced text keeps each site of a copied leaf, and
    ///   a site at another copy or with an end in layout is moved.
    /// - witness: `site::tests::a_respaced_text_keeps_each_site_of_a_copied_leaf`
    /// - witness: `site::tests::a_site_at_another_copy_or_in_layout_is_moved`
    pub fn spanned(
        &self,
        before: ByteSpan,
        candidate: ByteSpan,
    ) -> Placement
    {
        if self.reaches(before.start(), candidate.start()) == Placement::Same
            && self.reaches(before.end(), candidate.end()) == Placement::Same
        {
            Placement::Same
        }
        else {
            Placement::Moved
        }
    }

    /// The extent, in the text before the pass, of each respelled form whose
    /// leaves in the candidate meet `candidate`, a span of the candidate.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each extent whose leaves start at or before `candidate`'s end
    ///   and end at or after its start, in the order of the extents' starts. An
    ///   empty span meets the leaves that it touches.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a filter of the map, which a
    ///   predicate over the answer would filter again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an obligation inside one respelled form names that
    ///   form alone, and a form elsewhere in the source is not named.
    /// - witness: `tests::rewrite::an_obligation_withdraws_only_the_form_that_holds_it_8085`
    pub fn respelled_at(
        &self,
        candidate: ByteSpan,
    ) -> impl Iterator<Item = ByteSpan> + '_
    {
        self.starts
            .iter()
            .filter(move |&&(_, leaves)| {
                leaves.start() <= candidate.end() && candidate.start() <= leaves.end()
            })
            .map(|&(form, _)| form)
    }

    /// Whether `before`, a span of a report on the text before the pass, and
    /// `candidate`, a span of the candidate's report, are one site. Both are
    /// spans of a unit's text in which each text starts at `base`, absent
    /// where the report names none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Same` where both are absent for equal reasons, where both
    ///   are present, either ends at or before `base` and the two are equal, or
    ///   where both are present, start at or after `base`, and
    ///   [`Sites::spanned`] places them as one in each text's own offsets.
    ///   `Moved` otherwise.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a search of the map, which a
    ///   predicate over the answer would search again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a span that ends before the base compares by its
    ///   bytes, and a span after it compares through the map.
    /// - witness: `site::tests::a_site_at_another_copy_or_in_layout_is_moved`
    /// - witness: `tests::rewrite::a_refusal_beside_or_at_a_respelled_form_keeps_its_site_6726`
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
}

#[cfg(test)]
mod tests;
