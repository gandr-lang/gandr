//! A cellular sheaf over a finite graded poset, and the gluing of sections
//! over a cover.
//!
//! A sheaf puts a stalk of some width on each cell, and an entry map on each
//! pair of a cell and a cell above it. The entry map from a lower cell to an
//! upper cell names, for each entry of the upper stalk, the entry of the lower
//! stalk that it reads. The maps compose: the map from a cell to a cell above
//! it equals the map through each cell between them.
//!
//! A cover is a list of cells, each with a section: one value for each entry
//! of its stalk. Two members of a cover overlap at the cells above both. The
//! sections glue when, at each overlap, the two restrictions agree. The maps
//! compose, so the crate compares them only at the least cells of each
//! overlap: in a site whose overlaps have a least cell, that cell alone. A
//! glued section holds a value at each entry of each cell above a member.
//!
//! A sheaf on the opens of a space runs each map the other way, from an open
//! to each smaller open: a face of a cover restricts to the meet of two faces.
//! Such a site is this poset with its order reversed. Its cells are ordered by
//! reverse inclusion, so the meet of two faces is the least cell above both,
//! and the maps keep the values at the smaller cell's points.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::Membership;

use crate::error::SheafError;
use crate::index::CoverIndex;
use crate::index::Entry;
use crate::index::Slot;
use crate::index::Width;

/// A cellular sheaf over a graded poset of at most 64 cells: a stalk width
/// for each cell and an entry map for each pair of a cell and a cell above
/// it.
///
/// # Specification
/// - ensures: one width and one star for each cell; the map from a cell to a
///   cell above it holds one entry for each entry of the upper stalk, each
///   inside the lower stalk; the maps compose.
/// - provides: the poset, the widths, the gluing of a cover and the cochains.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`Sheaf::new`]'s,
///   which makes it.
///
/// # Adequacy
/// - hypothesis: L2 — the face covers of every corpus shape and of every small
///   carrier glue as the union square decides; L3 — a map past its stalk, a map
///   of the wrong width and a map that does not compose are each refused by
///   name.
/// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
/// - witness: `tests::sheaf::a_map_past_its_stalk_is_refused`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sheaf<Cell>
{
    /// The cells and their order.
    poset: GradedPoset<Cell>,
    /// The width of each cell's stalk, in cell order.
    widths: Vec<Width>,
    /// For each pair of cells, the lower first, the start of the map from the
    /// lower to the upper in `entries`. Only a pair whose lower cell lies
    /// strictly below its upper cell is read.
    starts: Vec<usize>,
    /// The entry maps, one after the other.
    entries: Vec<Entry>,
    /// Each cell's star: the cell and every cell above it.
    stars: Vec<ElementSet>,
}

impl<Cell> Sheaf<Cell>
{
    /// The sheaf on `poset` whose stalk at each cell has the width `width`
    /// gives, and whose map from each cell to each cell above it is the one
    /// `restriction` gives.
    ///
    /// # Specification
    /// - ensures: each map holds one entry for each entry of its upper stalk,
    ///   each inside its lower stalk, and the maps compose.
    /// - fails: a map of another width, a map that reads past its lower stalk,
    ///   and a map that differs from the map through a cell between are each
    ///   refused by the cells they name.
    /// - panics: none.
    /// - intension: `width` is called once for each cell in cell order.
    ///   `restriction` is called once for each pair of a cell and a cell
    ///   strictly above it: for each upper cell in cell order, each lower cell
    ///   in cell order. The composition check reads each chain of three cells
    ///   once.
    ///
    /// # Errors
    /// - [`SheafError::RestrictionWidth`]: a map holds another number of
    ///   entries than its upper stalk.
    /// - [`SheafError::EntryOutside`]: a map reads an entry past its lower
    ///   stalk.
    /// - [`SheafError::NotFunctorial`]: a map differs from the map through a
    ///   cell between its two cells.
    /// - [`SheafError::CellOutside`]: unreachable for a poset that
    ///   [`GradedPoset::new`] makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the face covers of every corpus shape and of every
    ///   small carrier, each with its maps to the meets; L3 — a map past its
    ///   stalk, a map one entry short and a chain of three cells whose maps do
    ///   not compose separate the three refusals.
    /// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
    /// - witness: `tests::sheaf::a_map_past_its_stalk_is_refused`
    /// - witness: `tests::sheaf::a_map_of_another_width_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |sheaf| sheaf.widths.len() == sheaf.poset.cells().len()
        && sheaf.stars.len() == sheaf.poset.cells().len()))]
    #[inline]
    pub fn new<Widths, Restrict, Map>(
        poset: GradedPoset<Cell>,
        width: Widths,
        mut restriction: Restrict,
    ) -> Result<Self, SheafError>
    where
        Widths: FnMut(&Cell) -> Width,
        Restrict: FnMut(&Cell, &Cell) -> Map,
        Map: IntoIterator<Item = Entry>,
    {
        let count = poset.cells().len();
        let widths: Vec<Width> = poset.cells().iter().map(width).collect();
        let mut starts = vec![0_usize; count.saturating_mul(count)];
        let mut entries = Vec::new();
        let mut stars = vec![ElementSet::EMPTY; count];
        for (upper, upper_cell) in poset.cells().iter().enumerate() {
            let upper = Element::from(upper);
            let own = ElementSet::single(upper).map_err(SheafError::Poset)?;
            let closure = poset.closure(upper).map_err(SheafError::Poset)?;
            for lower in closure.elements() {
                let star = stars
                    .get_mut(usize::from(lower))
                    .ok_or(SheafError::CellOutside(lower))?;
                *star = star.union(own);
            }
            let upper_width = widths
                .get(usize::from(upper))
                .copied()
                .ok_or(SheafError::CellOutside(upper))?;
            for lower in closure.elements().filter(|&lower| lower != upper) {
                let lower_cell = poset
                    .cells()
                    .get(usize::from(lower))
                    .ok_or(SheafError::CellOutside(lower))?;
                let lower_width = widths
                    .get(usize::from(lower))
                    .copied()
                    .ok_or(SheafError::CellOutside(lower))?;
                let start = entries.len();
                for entry in restriction(lower_cell, upper_cell) {
                    if usize::from(entry) >= usize::from(lower_width) {
                        return Err(SheafError::EntryOutside {
                            lower,
                            upper,
                            entry,
                        });
                    }
                    entries.push(entry);
                }
                let held = Width::from(entries.len().saturating_sub(start));
                if held != upper_width {
                    return Err(SheafError::RestrictionWidth {
                        lower,
                        upper,
                        width: held,
                    });
                }
                let slot = starts
                    .get_mut(usize::from(pair(ElementCount::from(count), lower, upper)))
                    .ok_or(SheafError::CellOutside(lower))?;
                *slot = start;
            }
        }
        let sheaf = Self {
            poset,
            widths,
            starts,
            entries,
            stars,
        };
        sheaf.composes()?;
        Ok(sheaf)
    }

    /// Checks that each map equals the map through each cell between its two
    /// cells.
    ///
    /// # Specification
    /// - ensures: for each chain of three cells, the map from the lowest to the
    ///   highest reads, at each entry, what the two maps through the middle
    ///   read in turn.
    /// - fails: the first chain and entry where they differ is refused.
    /// - panics: none.
    /// - intension: the chains in order of their highest cell, then their
    ///   middle cell, then their lowest cell, each in cell order.
    ///
    /// # Errors
    /// - [`SheafError::NotFunctorial`]: two maps differ at an entry.
    /// - [`SheafError::CellOutside`], [`SheafError::EntryOutside`]:
    ///   unreachable, as the cells come from the poset and the maps were
    ///   checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three cells whose direct map swaps the two
    ///   entries its composite keeps separates the refusal.
    /// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::NotFunctorial { .. } | SheafError::CellOutside(_) | SheafError::EntryOutside { .. })))]
    fn composes(&self) -> Result<(), SheafError>
    {
        for upper in (0 .. self.widths.len()).map(Element::from) {
            let width = self.width(upper)?;
            let below_upper = self.poset.boundary(upper).map_err(SheafError::Poset)?;
            for middle in below_upper.elements() {
                let below_middle = self.poset.boundary(middle).map_err(SheafError::Poset)?;
                for lower in below_middle.elements() {
                    for entry in (0 .. usize::from(width)).map(Entry::from) {
                        let direct = self.read(lower, upper, entry)?;
                        let through = self.read(middle, upper, entry)?;
                        let composite = self.read(lower, middle, through)?;
                        if direct != composite {
                            return Err(SheafError::NotFunctorial {
                                lower,
                                middle,
                                upper,
                                entry,
                            });
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// The cells and their order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn poset(&self) -> &GradedPoset<Cell>
    {
        &self.poset
    }

    /// The width of a cell's stalk.
    ///
    /// # Specification
    /// - provides: the width `Sheaf::new` read for `cell`.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the face cover of the config shape gives each face
    ///   and its meet the width of its points, and a cell past the count is
    ///   refused.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(SheafError::CellOutside(cell)))]
    #[inline]
    pub fn width(
        &self,
        cell: Element,
    ) -> Result<Width, SheafError>
    {
        self.widths
            .get(usize::from(cell))
            .copied()
            .ok_or(SheafError::CellOutside(cell))
    }

    /// The entry of `lower`'s stalk that the map from `lower` to `upper`
    /// reads at `entry`: `entry` itself when the two cells are one.
    ///
    /// # Specification
    /// - requires: `lower` is `upper` or lies below it, and `entry` lies in
    ///   `upper`'s stalk.
    /// - ensures: the entry lies in `lower`'s stalk.
    /// - fails: a pair or an entry outside the maps is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`]: `entry` lies past the map, or the pair
    ///   is past the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every gluing and every coboundary reads its maps
    ///   through it, so a map read at the wrong pair changes a verdict.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. })))]
    pub(crate) fn read(
        &self,
        lower: Element,
        upper: Element,
        entry: Entry,
    ) -> Result<Entry, SheafError>
    {
        if lower == upper {
            return Ok(entry);
        }
        let outside = SheafError::EntryOutside {
            lower,
            upper,
            entry,
        };
        let place = pair(ElementCount::from(self.widths.len()), lower, upper);
        let start = self
            .starts
            .get(usize::from(place))
            .copied()
            .ok_or(outside)?;
        let at = start.checked_add(usize::from(entry)).ok_or(outside)?;
        self.entries.get(at).copied().ok_or(outside)
    }

    /// A cell's star: the cell and every cell above it.
    ///
    /// # Specification
    /// - provides: the star `Sheaf::new` computed for `cell`.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every overlap of every face cover is the meet of two
    ///   stars, so a lost cell drops a comparison.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.map_or(true, |star| star.contains(cell) == Membership::Inside))]
    fn star(
        &self,
        cell: Element,
    ) -> Result<ElementSet, SheafError>
    {
        self.stars
            .get(usize::from(cell))
            .copied()
            .ok_or(SheafError::CellOutside(cell))
    }

    /// The least cells of a set of cells: those with no other member of the
    /// set below them.
    ///
    /// # Specification
    /// - ensures: each returned cell lies in `set`, and no other member of
    ///   `set` lies below it.
    /// - fails: a member past the poset is refused by name.
    /// - panics: none.
    /// - intension: in cell order.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: a member lies past the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two edges between the same two points overlap at no
    ///   least cell, and each point is a least cell of the overlap; L2 — every
    ///   face cover overlaps at its meet alone.
    /// - witness: `tests::sheaf::an_overlap_with_two_least_cells_compares_at_each`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |least| least.iter().all(|&cell| set.contains(cell) == Membership::Inside)))]
    fn least(
        &self,
        set: ElementSet,
    ) -> Result<Vec<Element>, SheafError>
    {
        let mut least = Vec::new();
        for cell in set.elements() {
            let closure = self.poset.closure(cell).map_err(SheafError::Poset)?;
            let own = ElementSet::single(cell).map_err(SheafError::Poset)?;
            if closure.meet(set) == own {
                least.push(cell);
            }
        }
        Ok(least)
    }

    /// The first entry of `overlap`'s stalk at which the restrictions of two
    /// sections differ, or their agreement.
    ///
    /// # Specification
    /// - requires: `overlap` lies above both cells, and each section has the
    ///   width of its cell's stalk.
    /// - provides: the least entry where the two restrictions differ.
    /// - fails: a map read outside its stalk or a section too short is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`], [`SheafError::CellOutside`]: unreachable
    ///   for a sheaf `Sheaf::new` makes and a section `Sheaf::glue` checked.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every choice of values zero and one on every small
    ///   face cover, against the union square's first point of difference.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. } | SheafError::CellOutside(_))))]
    fn difference<Value>(
        &self,
        (left_cell, left): (Element, &[Value]),
        (right_cell, right): (Element, &[Value]),
        overlap: Element,
    ) -> Result<Difference, SheafError>
    where
        Value: Eq,
    {
        let width = self.width(overlap)?;
        for entry in (0 .. usize::from(width)).map(Entry::from) {
            let from_left = self.read(left_cell, overlap, entry)?;
            let from_right = self.read(right_cell, overlap, entry)?;
            let outside = SheafError::EntryOutside {
                lower: left_cell,
                upper: overlap,
                entry,
            };
            let left_value = left.get(usize::from(from_left)).ok_or(outside)?;
            let right_value = right.get(usize::from(from_right)).ok_or(outside)?;
            if left_value != right_value {
                return Ok(Difference::At(entry));
            }
        }
        Ok(Difference::Agree)
    }

    /// Checks that a section has one value for each entry of its cell's
    /// stalk.
    ///
    /// # Specification
    /// - ensures: the section's width is its cell's stalk width.
    /// - fails: a cell past the poset, or a section of another width, is
    ///   refused by its cell.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: the cell lies past the poset.
    /// - [`SheafError::SectionWidth`]: the section has another number of values
    ///   than the cell's stalk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a section one value short is refused through both the
    ///   gluing and the pair comparison.
    /// - witness: `tests::sheaf::a_section_of_another_width_is_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::CellOutside(_) | SheafError::SectionWidth { .. })))]
    fn fits<Value>(
        &self,
        (cell, section): (Element, &[Value]),
    ) -> Result<(), SheafError>
    {
        let width = self.width(cell)?;
        if section.len() != usize::from(width) {
            return Err(SheafError::SectionWidth {
                cell,
                width: Width::from(section.len()),
            });
        }
        Ok(())
    }

    /// Whether the sections of two cells agree at each cell above both.
    ///
    /// # Specification
    /// - requires: each section has one value for each entry of its cell's
    ///   stalk.
    /// - ensures: the two differ exactly when their restrictions differ at a
    ///   cell above both; then the answer names the least cell of the overlap
    ///   where they differ, and the first entry there.
    /// - fails: a cell past the poset, or a section of another width, is
    ///   refused by its cell.
    /// - panics: none.
    /// - intension: the least cells of the overlap in cell order, each read
    ///   once, so a caller that changes one member of a cover compares only the
    ///   pairs that hold it.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: a cell lies past the poset.
    /// - [`SheafError::SectionWidth`]: a section has another number of values
    ///   than its cell's stalk.
    /// - [`SheafError::EntryOutside`]: unreachable for a sheaf `Sheaf::new`
    ///   makes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the config shape's two faces agree and differ at
    ///   their meet; L2 — every gluing of every face cover compares its pairs
    ///   through it.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::sheaf::an_overlap_with_two_least_cells_compares_at_each`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::CellOutside(_) | SheafError::SectionWidth { .. } | SheafError::EntryOutside { .. })))]
    #[inline]
    pub fn compare<Value>(
        &self,
        left: (Element, &[Value]),
        right: (Element, &[Value]),
    ) -> Result<Agreement, SheafError>
    where
        Value: Eq,
    {
        self.fits(left)?;
        self.fits(right)?;
        let left_star = self.star(left.0)?;
        let right_star = self.star(right.0)?;
        for least in self.least(left_star.meet(right_star))? {
            if let Difference::At(entry) = self.difference(left, right, least)? {
                return Ok(Agreement::Differ {
                    overlap: least,
                    entry,
                });
            }
        }
        Ok(Agreement::Agree)
    }

    /// The gluing of the sections of `cover`: the glued section, or each pair
    /// of members whose restrictions differ.
    ///
    /// # Specification
    /// - requires: each member's section has one value for each entry of its
    ///   cell's stalk.
    /// - ensures: the gluing obstructs exactly when two members' restrictions
    ///   differ at a cell above both. Each obstruction names the pair, the
    ///   least cell of their overlap where the restrictions differ, and the
    ///   first entry there. A glued section holds, at each cell above a member,
    ///   the restriction of the first member below it.
    /// - fails: a member past the poset, or a section of another width, is
    ///   refused by its cell.
    /// - panics: none.
    /// - intension: the pairs in cover order, the earlier member first; the
    ///   least cells of each overlap in cell order, and one obstruction for
    ///   each pair at most.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: a member lies past the poset.
    /// - [`SheafError::SectionWidth`]: a section has another number of values
    ///   than its cell's stalk.
    /// - [`SheafError::EntryOutside`], [`SheafError::OutsideSupport`]:
    ///   unreachable for a sheaf `Sheaf::new` makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every choice of values zero and one on the face cover
    ///   of every corpus shape and every small carrier, against the union
    ///   square's mediator pair by pair, separates a lost overlap, a wrong
    ///   entry or a wrong pair; L3 — the config shape's two faces glue on their
    ///   meet and are obstructed there, and a section one value short is
    ///   refused.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::sheaf::a_section_of_another_width_is_refused`
    /// - witness: `tests::sheaf::an_overlap_with_two_least_cells_compares_at_each`
    #[spec(ensures: |ref ret| match *ret {
        Ok(Gluing::Obstructed(ref obstructions)) => !obstructions.is_empty(),
        Ok(Gluing::Glued(_)) => true,
        Err(error) => matches!(error, SheafError::CellOutside(_) | SheafError::SectionWidth { .. }
            | SheafError::EntryOutside { .. } | SheafError::OutsideSupport(_)),
    })]
    #[inline]
    pub fn glue<Value>(
        &self,
        cover: &[(Element, &[Value])],
    ) -> Result<Gluing<Value>, SheafError>
    where
        Value: Copy + Eq,
    {
        let mut support = ElementSet::EMPTY;
        for &member in cover {
            self.fits(member)?;
            let star = self.star(member.0)?;
            support = support.union(star);
        }
        let mut obstructions = Vec::new();
        for (first, &left) in cover.iter().enumerate() {
            for (second, &right) in cover.iter().enumerate().skip(first.saturating_add(1)) {
                match self.compare(left, right)? {
                    Agreement::Agree => {},
                    Agreement::Differ { overlap, entry } => obstructions.push(Obstruction {
                        members: (CoverIndex::from(first), CoverIndex::from(second)),
                        overlap,
                        entry,
                    }),
                }
            }
        }
        if !obstructions.is_empty() {
            return Ok(Gluing::Obstructed(obstructions));
        }
        let section = self.section(cover, support)?;
        Ok(Gluing::Glued(section))
    }

    /// The glued section of `cover` on `support`, the cells above its members.
    ///
    /// # Specification
    /// - requires: the sections of `cover` agree at each overlap, and `support`
    ///   is the union of the members' stars.
    /// - ensures: each cell of `support` holds the restriction of the first
    ///   member below it.
    /// - fails: a map read outside its stalk is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`], [`SheafError::OutsideSupport`],
    ///   [`SheafError::CellOutside`]: unreachable for a cover `Sheaf::glue`
    ///   checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the config shape's glued section holds each face's
    ///   values and the shared value at the meet.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |section| section.support == support))]
    fn section<Value>(
        &self,
        cover: &[(Element, &[Value])],
        support: ElementSet,
    ) -> Result<Section<Value>, SheafError>
    where
        Value: Copy,
    {
        let mut bounds = Vec::with_capacity(support.elements().count().saturating_add(1));
        let mut values = Vec::new();
        bounds.push(0);
        for cell in support.elements() {
            let mut below = None;
            for &(member, section) in cover {
                let star = self.star(member)?;
                if star.contains(cell) == Membership::Inside {
                    below = Some((member, section));
                    break;
                }
            }
            let (member, section) = below.ok_or(SheafError::OutsideSupport(cell))?;
            let width = self.width(cell)?;
            for entry in (0 .. usize::from(width)).map(Entry::from) {
                let from = self.read(member, cell, entry)?;
                let value =
                    section
                        .get(usize::from(from))
                        .copied()
                        .ok_or(SheafError::EntryOutside {
                            lower: member,
                            upper: cell,
                            entry,
                        })?;
                values.push(value);
            }
            bounds.push(values.len());
        }
        Ok(Section {
            support,
            bounds,
            values,
        })
    }
}

/// The place of the pair of `lower` and `upper` in a table of `count` cells
/// by `count`.
///
/// # Specification
/// trivial.
fn pair(
    count: ElementCount,
    lower: Element,
    upper: Element,
) -> Slot
{
    Slot::from(
        usize::from(lower)
            .saturating_mul(usize::from(count))
            .saturating_add(usize::from(upper)),
    )
}

/// Whether two restrictions agree at an overlap.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Difference
{
    /// They agree at every entry.
    Agree,
    /// They first differ at this entry.
    At(Entry),
}

/// Whether the sections of two cells agree where the cells overlap.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Agreement
{
    /// The restrictions agree at every cell above both.
    Agree,
    /// The restrictions differ.
    Differ
    {
        /// The least cell of the overlap where they differ.
        overlap: Element,
        /// The first entry of that cell's stalk where they differ.
        entry: Entry,
    },
}

/// Where two members of a cover differ.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Obstruction
{
    /// The two members, the earlier first.
    pub members: (CoverIndex, CoverIndex),
    /// The least cell of their overlap where their restrictions differ.
    pub overlap: Element,
    /// The first entry of that cell's stalk where they differ.
    pub entry: Entry,
}

/// The verdict on the sections of a cover.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Gluing<Value>
{
    /// The sections agree at each overlap, and glue to this section.
    Glued(Section<Value>),
    /// These pairs of members differ, in cover order; never empty.
    Obstructed(Vec<Obstruction>),
}

/// A section on the cells above the members of a cover: one value for each
/// entry of each such cell's stalk.
///
/// # Specification
/// - ensures: one bound more than the cells of the support, the first zero and
///   the last the number of values, rising by each cell's width.
/// - provides: the support and the values at each of its cells.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is `Sheaf::glue`'s,
///   which makes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Section<Value>
{
    /// The cells the section holds values at.
    support: ElementSet,
    /// Where each cell's values start in `values`, in cell order, and where
    /// the last ends.
    bounds: Vec<usize>,
    /// The values, cell after cell.
    values: Vec<Value>,
}

impl<Value> Section<Value>
{
    /// The cells the section holds values at: each cell above a member of
    /// its cover.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn support(&self) -> ElementSet
    {
        self.support
    }

    /// The values at a cell of the support, one for each entry of its stalk.
    ///
    /// # Specification
    /// - provides: the restriction to `cell` of the first member below it.
    /// - fails: a cell outside the support is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::OutsideSupport`]: `cell` lies above no member.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the config shape's glued section reads each face's
    ///   values and the meet's shared value, and refuses a cell outside.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.as_ref().map_or_else(|error| *error == SheafError::OutsideSupport(cell), |_| true))]
    #[inline]
    pub fn at(
        &self,
        cell: Element,
    ) -> Result<&[Value], SheafError>
    {
        if self.support.contains(cell) == Membership::Outside {
            return Err(SheafError::OutsideSupport(cell));
        }
        let place = self
            .support
            .elements()
            .take_while(|&member| member != cell)
            .count();
        let start = self.bounds.get(place).copied();
        let end = self.bounds.get(place.saturating_add(1)).copied();
        start
            .zip(end)
            .and_then(|(start, end)| self.values.get(start .. end))
            .ok_or(SheafError::OutsideSupport(cell))
    }
}
