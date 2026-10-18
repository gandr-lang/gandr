//! The co-de Bruijn carrier: a term's syntactic support kept on the term, as
//! a selection from its scope rather than an index into it.
//!
//! # Thinnings, covers and the bare leaf
//!
//! A [`Thinning`] is an order-preserving selection from a two-zone scope
//! `Γ; Σ`: for each zone, the de Bruijn indices it keeps, innermost first,
//! strictly ascending. Read as a map, it embeds a compact scope — one slot per
//! selected index — into the scope it was selected from. A node placed under
//! a thinning sees exactly the binders the thinning selects, so the thinning
//! is the node's support: what it mentions, and nothing else.
//!
//! A node's children each sit under some binders of each zone, a
//! [`Crossing`]: a lambda's body under one intuitionistic binder, a split's
//! body under one per component, a fork's halves under one linear binder.
//! [`Thinning::covering`] builds a node's support from the variables it names
//! itself and its children's supports — the union of what each child mentions
//! above the binders between them. [`Cover::of`] adds one edge per child: the
//! child's support read as a selection from the node's compact scope extended
//! by the child's local binders. The edges are the cover. An edge is a
//! function of the node's support, the child's support and the crossing, so a
//! consumer that keeps supports derives its edges rather than storing them.
//! Two nodes whose formers, covers and widths agree are the same compact node
//! wherever they stand, so one subterm placed under different unused binders
//! is one node. A variable's support is the one index it names, so a variable
//! is a bare leaf: its compact scope has one slot and its index carries
//! nothing.
//!
//! [`Thinning::place`] runs the other way: given a node's support in an
//! ambient scope and a child's edge, it composes the edge with the support
//! extended past the child's local binders, giving the child's support in the
//! ambient scope. Placing every node from a root's support recovers the de
//! Bruijn term: the projection consumers that print ambient binders read. A
//! placed index past the `u32` index space is refused as
//! [`PlacementError::IndexOverflow`], never saturated.
//!
//! [`check_cover`] is the converse of [`Cover::of`] for a reader that did not
//! build the cover: every edge selects exactly its child's scope, inside the
//! node's scope and its local binders, and every slot of the node's scope is
//! selected by an edge or named by the node itself, so the scope is minimal.
//!
//! **Choice.** One carrier for every vocabulary that adopts co-de Bruijn
//! scoping: the incremental content table, the command IL and the core arena's
//! nodes, so they share one algebra and one witness set.
//! **Alternatives.** The carrier inside the content table's crate, which the
//! next consumers would have to depend on or copy; a crate of its own, which
//! separates the carrier from the zones and binder depths it is stated over.
//! **Reversal.** A consumer outside the core vocabulary — one whose zones are
//! not `Γ; Σ` — moves the carrier into its own crate.
//!
//! # Bit selections
//!
//! A thinning is one machine word and one optional spill: the word holds one
//! bit per index for the innermost 48 intuitionistic and 16 linear binders,
//! and a selection naming an index past either width moves to two sorted
//! index lists behind one pointer. The form is canonical — the spill is
//! present exactly when some index passes its zone's inline width — so the
//! derived equality and hashing compare selections. A thinning is 16 bytes
//! and allocates nothing for a support inside the inline widths, which is
//! every support the corpus and the generators build; the union a cover
//! takes is word-wise shifts and disjunctions, and rank and select are
//! population counts.
//!
//! **Choice.** The inline bitset with a sparse spill, measured against the
//! sparse form alone — two index vectors, 48 bytes and an allocation per
//! non-empty zone — on the command IL's differential terms, where a node's
//! carried scope went from 144 bytes and an allocation per selection to 16
//! bytes per zone pair. The linear zone gets the narrower half: no former
//! binds more than one linear binder at a time, and the linear zone holds
//! session endpoints and memory slots, never a definition's parameters.
//! **Alternatives.** The sparse form alone; a run-length form, one
//! `(start, length)` pair per run of selected indices, which is as small for
//! a contiguous support and larger for a scattered one, and whose union is a
//! merge rather than a disjunction. **Reversal.** A measured workload whose
//! supports name binders past the inline widths often enough that the spill's
//! allocation dominates, which moves the split or widens the word.
//!
//! A [`Union`] builds a support from what a node names and its children's
//! supports past their crossings, in any order and with repeats: an uncrossed
//! child is one disjunction, a crossed one two shifts and a disjunction, while
//! every index fits the word. [`ThinningRef`] reads a stored thinning in place
//! — its word by value, its spill by reference — so a hot read neither clones
//! nor drops one. [`ThinningPair`] stores two thinnings in three words, both
//! words beside each other and one pointer shared by their spills: the row a
//! table keeps per node when a node carries a support in each of two spaces,
//! as the command IL's producer and covariable supports are.
//!
//! # The fence
//!
//! A carried support is syntactic: it over-approximates dependence. A
//! β-removable or singleton-typed use still occurs, so the support names it.
//! It keys, footprints, schedules and bounds capture, where an
//! over-approximation splits work and never merges two answers. It never
//! decides a strengthening: whether a type can be lowered out of a binder is
//! the judgement's question, answered by unification over the type, and the
//! bind rule's strengthening stays the refusal it is.
//!
//! # References
//!
//! - Conor `McBride`. "Everybody's Got To Be Somewhere." _Proceedings of the
//!   7th Workshop on Mathematically Structured Functional Programming (MSFP
//!   2018)_, EPTCS 275, pages 53–69. `doi:10.4204/EPTCS.275.6` — co-de Bruijn
//!   representation: thinnings, covers and relevant pairs, with every variable
//!   a bare leaf.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::BinderDepth;
use crate::syntax::Zone;

/// Why a selection holds no index at a position.
pub mod unselected
{
    /// The single reason a thinning names no rank for an index.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// The thinning does not select the index.
        Unselected,
    }
}

/// Why an index stands at no outer position.
mod bound
{
    /// The single reason an index has no image past a crossing.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub(super) enum Absent
    {
        /// The index names one of the binders crossed.
        Local,
    }
}

/// How many intuitionistic indices the inline word holds, from bit 0.
const INTUITIONISTIC_WIDTH: u32 = 48;

/// How many linear indices the inline word holds, above the intuitionistic
/// bits.
const LINEAR_WIDTH: u32 = 16;

/// The inline word's intuitionistic bits.
const INTUITIONISTIC_MASK: u64 = 0x0000_FFFF_FFFF_FFFF;

/// The inline word's width in bits: a lowering at least this far empties it.
const WORD_BITS: usize = 64;

/// One zone's inline selection: bit `i` selects index `i`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Bits(u64);

impl Bits
{
    /// The selection of `index` alone, when it is inside `zone`'s inline
    /// width.
    ///
    /// # Specification
    /// - ensures: one bit, at `index`, when the index is inside the width;
    ///   `unselected::Absent::Unselected` past it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last inline index and the first past it, in each
    ///   zone, separate the inline word from the spill.
    /// - witness: `support::tests::selections_past_the_inline_width_spill`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(Self(bits)) => bits.is_power_of_two() && bits.trailing_zeros() == u32::from(index),
        Maybe::Absent(unselected::Absent::Unselected) => index >= inline_width(zone),
    })]
    #[inline]
    fn single(
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Maybe<Self, unselected::Absent>
    {
        if index < inline_width(zone) {
            Maybe::Present(Self(1_u64.unbounded_shl(u32::from(index))))
        }
        else {
            Maybe::Absent(unselected::Absent::Unselected)
        }
    }

    /// The selection read past `crossed` binders: every index inside the
    /// crossing dropped, every other lowered by it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn lowered(
        self,
        crossed: BinderDepth,
    ) -> Self
    {
        let crossed = usize::from(crossed);
        if crossed >= WORD_BITS {
            return Self(0);
        }
        // reason: `crossed` is below the word's width, so it fits a `u32`
        // and the shift drops exactly the crossed bits.
        Self(
            self.0
                .wrapping_shr(u32::try_from(crossed).unwrap_or(u32::MAX)),
        )
    }

    /// The indices below `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn below(
        self,
        index: DeBruijnIndex,
    ) -> Self
    {
        Self(self.0 & 1_u64.unbounded_shl(u32::from(index)).wrapping_sub(1))
    }

    /// How many indices the selection holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn count(self) -> BinderDepth
    {
        // reason: a population count of a 64-bit word is at most 64.
        BinderDepth::from(usize::try_from(self.0.count_ones()).unwrap_or(usize::MAX))
    }
}

/// The inline width of `zone`: the first index the word cannot hold.
///
/// # Specification
/// trivial.
#[inline]
fn inline_width(zone: Zone) -> DeBruijnIndex
{
    DeBruijnIndex::from(match zone {
        Zone::Intuitionistic => INTUITIONISTIC_WIDTH,
        Zone::Linear => LINEAR_WIDTH,
    })
}

/// The selections a spilled thinning holds: every selected index of each
/// zone, strictly ascending.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Spill
{
    /// The intuitionistic indices.
    intuitionistic: Vec<DeBruijnIndex>,
    /// The linear indices.
    linear: Vec<DeBruijnIndex>,
}

impl Spill
{
    /// The indices of `zone`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zone(
        &self,
        zone: Zone,
    ) -> &[DeBruijnIndex]
    {
        match zone {
            Zone::Intuitionistic => &self.intuitionistic,
            Zone::Linear => &self.linear,
        }
    }

    /// The indices of `zone`, to extend.
    ///
    /// # Specification
    /// trivial.
    fn zone_mut(
        &mut self,
        zone: Zone,
    ) -> &mut Vec<DeBruijnIndex>
    {
        match zone {
            Zone::Intuitionistic => &mut self.intuitionistic,
            Zone::Linear => &mut self.linear,
        }
    }
}

/// An order-preserving selection from a two-zone scope.
///
/// # Specification
/// - executable: none — a data declaration. Every constructor keeps the form
///   canonical: the spill is present exactly when some selected index passes
///   its zone's inline width, and then the inline word is empty and each spill
///   list strictly ascends.
///
/// # Adequacy
/// - hypothesis: L3 — exhaustive small scopes and the unordered near-misses
///   separate dropped, repeated and misordered selections in either zone; the
///   indices on both sides of each inline width separate the word from the
///   spill and keep equality canonical across them.
/// - witness: `support::tests::selections_refuse_unordered_indices`
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
/// - witness: `support::tests::selections_past_the_inline_width_spill`
#[derive(Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Thinning
{
    /// The intuitionistic bits below [`INTUITIONISTIC_WIDTH`] and, above
    /// them, the linear bits below [`LINEAR_WIDTH`]; empty when spilled.
    inline: Bits,
    /// Both zones' indices, when one passes its inline width.
    spill: Option<Box<Spill>>,
}

/// A thinning read in place: its inline word by value and its spill, when
/// it has one, by reference.
///
/// It is `Copy`, so a hot read of a stored support neither clones nor drops
/// one, and a [`ThinningPair`] hands out its members without holding them
/// as whole thinnings.
///
/// # Specification
/// - executable: none — a data declaration; it is made only from a canonical
///   [`Thinning`] or pair, so its form is canonical too.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ThinningRef<'thinning>
{
    /// As the thinning's inline word.
    inline: Bits,
    /// The thinning's spill, by reference.
    spill: Option<&'thinning Spill>,
}

/// Two thinnings stored as one row: both inline words side by side and,
/// when either spills, both whole behind one pointer.
///
/// Three words where two [`Thinning`]s take four: the row a table keeps per
/// node when each node carries two supports.
///
/// # Specification
/// - executable: none — a data declaration. Every constructor keeps the form
///   canonical: the pointer is present exactly when either member spills, and
///   then both words are empty; equality is therefore the members'.
///
/// # Adequacy
/// - hypothesis: L3 — pairs inline in both members, spilled in one and spilled
///   in both read back their members and compare as those members.
/// - witness: `support::tests::a_pair_reads_back_its_members`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct ThinningPair
{
    /// The first member's inline word, while neither spills.
    first: Bits,
    /// The second member's inline word, while neither spills.
    second: Bits,
    /// Both members, once either spills.
    spilled: Option<Box<[Thinning; 2]>>,
}

impl<'thinning> ThinningRef<'thinning>
{
    /// The indices selected in `zone`, innermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn indices(
        self,
        zone: Zone,
    ) -> Indices<'thinning>
    {
        Indices(self.spill.map_or_else(
            || Walk::Bits(self.zone_bits(zone)),
            |spill| Walk::Listed(spill.zone(zone).iter()),
        ))
    }

    /// The indices selected in `zone` at or past `crossed`, as they stand:
    /// what a node selects beyond the binders its own former opens.
    ///
    /// # Specification
    /// - ensures: exactly the selected indices of `zone` not below `crossed`,
    ///   ascending.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — selections below, at and past a crossing of zero to
    ///   two binders, inline and spilled, separate the cut from its neighbours.
    /// - witness: `support::tests::outside_cuts_at_the_crossing`
    #[spec(ensures: |ret| ret.clone().eq(self.indices(zone).filter(|&index| {
        BinderDepth::from(usize::try_from(u32::from(index)).unwrap_or(usize::MAX)) >= crossed
    })))]
    #[inline]
    #[must_use]
    pub fn outside(
        self,
        zone: Zone,
        crossed: BinderDepth,
    ) -> Indices<'thinning>
    {
        let crossed = u32::try_from(usize::from(crossed)).unwrap_or(u32::MAX);
        Indices(self.spill.map_or_else(
            || {
                let bits = self.zone_bits(zone);
                Walk::Bits(Bits(bits.0 & !bits.below(DeBruijnIndex::from(crossed)).0))
            },
            |spill| {
                let listed = spill.zone(zone);
                let local = listed.partition_point(|&index| u32::from(index) < crossed);
                Walk::Listed(listed.get(local ..).unwrap_or_default().iter())
            },
        ))
    }

    /// The position `index` takes in the compact scope: how many selected
    /// indices of `zone` lie inside it.
    ///
    /// # Specification
    /// - ensures: the rank of `index` among the zone's selected indices when
    ///   selected; `unselected::Absent::Unselected` otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exhaustive small selections: every selected index
    ///   ranks to its position and every unselected one is absent; the same
    ///   held past an inline width ranks through the spill.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    /// - witness: `support::tests::selections_past_the_inline_width_spill`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(rank) => self.indices(zone).nth(usize::try_from(u32::from(rank)).unwrap_or(usize::MAX)) == Some(index),
        Maybe::Absent(unselected::Absent::Unselected) => self.indices(zone).all(|held| held != index),
    })]
    #[inline]
    pub fn rank(
        self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Maybe<DeBruijnIndex, unselected::Absent>
    {
        let rank = self.spill.map_or_else(
            || {
                let bits = self.zone_bits(zone);
                match Bits::single(zone, index) {
                    Maybe::Present(bit) if bits.0 & bit.0 != 0 => {
                        Some(usize::from(bits.below(index).count()))
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => None,
                }
            },
            |spill| spill.zone(zone).binary_search(&index).ok(),
        );
        rank.map_or(Maybe::Absent(unselected::Absent::Unselected), |rank| {
            // reason: a rank counts distinct `u32` indices below another `u32`
            // index, so it fits; the clamp keeps the conversion total.
            Maybe::Present(DeBruijnIndex::from(u32::try_from(rank).unwrap_or(u32::MAX)))
        })
    }

    /// The thinning read, owned.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_thinning(self) -> Thinning
    {
        Thinning {
            inline: self.inline,
            spill: self.spill.map(|spill| Box::new(spill.clone())),
        }
    }

    /// The inline bits of `zone`, with the zone's lowest index at bit 0.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn zone_bits(
        self,
        zone: Zone,
    ) -> Bits
    {
        match zone {
            Zone::Intuitionistic => Bits(self.inline.0 & INTUITIONISTIC_MASK),
            Zone::Linear => Bits(self.inline.0.unbounded_shr(INTUITIONISTIC_WIDTH)),
        }
    }
}

impl ThinningPair
{
    /// The pair of `first` and `second`.
    ///
    /// # Specification
    /// - ensures: [`Self::first`] reads `first` and [`Self::second`] reads
    ///   `second`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type's.
    /// - witness: `support::tests::a_pair_reads_back_its_members`
    #[spec(
        captures: [expected = (first.clone(), second.clone())],
        ensures: |ret| ret.first() == expected.0.view() && ret.second() == expected.1.view(),
    )]
    #[inline]
    #[must_use]
    pub fn new(
        first: Thinning,
        second: Thinning,
    ) -> Self
    {
        if first.spill.is_none() && second.spill.is_none() {
            return Self {
                first: first.inline,
                second: second.inline,
                spilled: None,
            };
        }
        Self {
            first: Bits(0),
            second: Bits(0),
            spilled: Some(Box::new([first, second])),
        }
    }

    /// The pair two unions finish to, without building either thinning
    /// while both are inline.
    ///
    /// # Specification
    /// - ensures: exactly `Self::new(first.finish(), second.finish())`.
    /// - panics: none.
    /// - executable: none — this runs once per node on the mint path; the
    ///   instrumented body is a closure the test profile does not inline, and
    ///   the witness reads both members back.
    /// - intension: two words moved while both unions are inline.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type's.
    /// - witness: `support::tests::a_pair_reads_back_its_members`
    #[inline]
    #[must_use]
    pub fn of(
        first: Union,
        second: Union,
    ) -> Self
    {
        match (first.listed, second.listed) {
            (None, None) => Self {
                first: first.inline,
                second: second.inline,
                spilled: None,
            },
            (first_listed, second_listed) => Self::new(
                Union {
                    inline: first.inline,
                    listed: first_listed,
                }
                .finish(),
                Union {
                    inline: second.inline,
                    listed: second_listed,
                }
                .finish(),
            ),
        }
    }

    /// The first member.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn first(&self) -> ThinningRef<'_>
    {
        self.spilled.as_ref().map_or(
            ThinningRef {
                inline: self.first,
                spill: None,
            },
            |both| {
                let [ref first, _] = **both;
                first.view()
            },
        )
    }

    /// The second member.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn second(&self) -> ThinningRef<'_>
    {
        self.spilled.as_ref().map_or(
            ThinningRef {
                inline: self.second,
                spill: None,
            },
            |both| {
                let [_, ref second] = **both;
                second.view()
            },
        )
    }
}

/// The indices a thinning selects in one zone, innermost first.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Indices<'thinning>(Walk<'thinning>);

/// Where a zone's indices are read from.
#[derive(Clone, Debug)]
enum Walk<'thinning>
{
    /// The bits not yet read, of an inline selection.
    Bits(Bits),
    /// The rest of a spilled selection.
    Listed(core::slice::Iter<'thinning, DeBruijnIndex>),
}

impl Iterator for Indices<'_>
{
    type Item = DeBruijnIndex;

    /// The next index, innermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<DeBruijnIndex>
    {
        match self.0 {
            Walk::Bits(ref mut bits) => {
                if bits.0 == 0 {
                    return None;
                }
                let at = bits.0.trailing_zeros();
                bits.0 &= bits.0.wrapping_sub(1);
                Some(DeBruijnIndex::from(at))
            },
            Walk::Listed(ref mut listed) => listed.next().copied(),
        }
    }

    /// The indices left, exactly.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let left = match self.0 {
            Walk::Bits(bits) => usize::from(bits.count()),
            Walk::Listed(ref listed) => listed.len(),
        };
        (left, Some(left))
    }
}

impl DoubleEndedIterator for Indices<'_>
{
    /// The next index from the outermost end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next_back(&mut self) -> Option<DeBruijnIndex>
    {
        match self.0 {
            Walk::Bits(ref mut bits) => {
                if bits.0 == 0 {
                    return None;
                }
                let at = u64::BITS
                    .wrapping_sub(1)
                    .wrapping_sub(bits.0.leading_zeros());
                bits.0 &= !1_u64.unbounded_shl(at);
                Some(DeBruijnIndex::from(at))
            },
            Walk::Listed(ref mut listed) => listed.next_back().copied(),
        }
    }
}

impl ExactSizeIterator for Indices<'_>
{
}

/// A thinning under construction, fed each zone's indices in ascending
/// order.
#[derive(Debug, Default)]
struct Builder
{
    /// The inline word while every index fits it.
    inline: Bits,
    /// The spill, once one index did not fit.
    spill: Option<Spill>,
}

impl Builder
{
    /// Add `index` to `zone`'s selection.
    ///
    /// # Specification
    /// - requires: `index` passes every index already added to `zone`.
    /// - ensures: the selection holds `index` in `zone`; an index past the
    ///   zone's inline width moves every earlier index to the spill.
    /// - panics: none.
    /// - executable: none — the builder is read only by finishing it, which
    ///   consumes it; the witness finishes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — selections on both sides of each inline width, added
    ///   in either zone order, separate the spill from the word.
    /// - witness: `support::tests::selections_past_the_inline_width_spill`
    fn push(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    )
    {
        if let Some(ref mut spill) = self.spill {
            spill.zone_mut(zone).push(index);
            return;
        }
        if let Maybe::Present(bit) = Bits::single(zone, index) {
            self.inline.0 |= match zone {
                Zone::Intuitionistic => bit.0,
                Zone::Linear => bit.0.unbounded_shl(INTUITIONISTIC_WIDTH),
            };
            return;
        }
        let held = Thinning {
            inline: core::mem::take(&mut self.inline),
            spill: None,
        };
        let mut spill = Spill {
            intuitionistic: held.indices(Zone::Intuitionistic).collect(),
            linear: held.indices(Zone::Linear).collect(),
        };
        spill.zone_mut(zone).push(index);
        self.spill = Some(spill);
    }

    /// The thinning built.
    ///
    /// # Specification
    /// trivial.
    fn finish(self) -> Thinning
    {
        Thinning {
            inline: self.inline,
            spill: self.spill.map(Box::new),
        }
    }
}

/// Whether a union, finished, is a given thinning.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Agreement
{
    /// The union finishes to exactly the thinning.
    Same,
    /// One of the two selects an index the other does not.
    Different,
}

/// A node's support under construction.
///
/// It takes the variables the node names itself and its children's supports
/// past their crossings, in any order and with repeats. [`Thinning::covering`]
/// is one pass of it; a consumer whose children come in several shapes feeds
/// it one at a time.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub struct Union
{
    /// The inline word while every index fits it.
    inline: Bits,
    /// Each zone's gathered indices, once one did not fit; boxed so the
    /// common, inline union is two words.
    listed: Option<Box<[Vec<DeBruijnIndex>; 2]>>,
}

impl Union
{
    /// The empty union.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            inline: Bits(0),
            listed: None,
        }
    }

    /// Add `index`, which the node names itself, to `zone`.
    ///
    /// # Specification
    /// - ensures: the union holds `index` in `zone`; an index past the zone's
    ///   inline width moves every earlier index to the gathered lists.
    /// - panics: none.
    /// - executable: none — the union is read only by finishing it, which
    ///   consumes it, and this runs once per name on the mint path; the witness
    ///   finishes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — occurrences on both sides of each inline width.
    /// - witness: `support::tests::selections_past_the_inline_width_spill`
    #[inline]
    pub fn name(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    )
    {
        if self.listed.is_none()
            && let Maybe::Present(bit) = Bits::single(zone, index)
        {
            self.inline.0 |= match zone {
                Zone::Intuitionistic => bit.0,
                Zone::Linear => bit.0.unbounded_shl(INTUITIONISTIC_WIDTH),
            };
            return;
        }
        self.name_listed(zone, index);
    }

    /// Add `index` to `zone`'s gathered list, gathering the inline word first.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn name_listed(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    )
    {
        let [ref mut intuitionistic, ref mut linear] = *self.lists();
        match zone {
            Zone::Intuitionistic => intuitionistic.push(index),
            Zone::Linear => linear.push(index),
        }
    }

    /// Add every index `child` selects past `crossing`, lowered by it: what a
    /// child standing under `crossing` more binders adds to its node.
    ///
    /// # Specification
    /// - ensures: the union holds each outer index of the child, read where the
    ///   node stands.
    /// - panics: none.
    /// - executable: none — the union is read only by finishing it, which
    ///   consumes it, and this runs once per child on the mint and check paths;
    ///   the witness finishes it.
    /// - intension: one disjunction for an uncrossed child, two shifts and a
    ///   disjunction for a crossed one, while both are inline.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Thinning::covering`].
    /// - witness: `support::tests::a_cover_unions_its_children`
    #[inline]
    pub fn child(
        &mut self,
        child: ThinningRef<'_>,
        crossing: Crossing,
    )
    {
        if self.listed.is_none() && child.spill.is_none() {
            self.inline.0 |= if crossing == Crossing::default() {
                child.inline.0
            }
            else {
                let intuitionistic = child
                    .zone_bits(Zone::Intuitionistic)
                    .lowered(crossing.depth(Zone::Intuitionistic));
                let linear = child
                    .zone_bits(Zone::Linear)
                    .lowered(crossing.depth(Zone::Linear));
                intuitionistic.0 | linear.0.unbounded_shl(INTUITIONISTIC_WIDTH)
            };
            return;
        }
        self.child_listed(child, crossing);
    }

    /// Add a child's outer indices one at a time, once either side has spilled.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn child_listed(
        &mut self,
        child: ThinningRef<'_>,
        crossing: Crossing,
    )
    {
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            let crossed = crossing.depth(zone);
            for index in child.outside(zone, crossed) {
                if let Maybe::Present(outer) = outer(index, crossed) {
                    self.name(zone, outer);
                }
            }
        }
    }

    /// The gathered lists, made from the inline word on first use.
    ///
    /// # Specification
    /// trivial.
    fn lists(&mut self) -> &mut [Vec<DeBruijnIndex>; 2]
    {
        let inline = &mut self.inline;
        self.listed.get_or_insert_with(|| {
            let held = Thinning {
                inline: core::mem::take(inline),
                spill: None,
            };
            Box::new([
                held.indices(Zone::Intuitionistic).collect(),
                held.indices(Zone::Linear).collect(),
            ])
        })
    }

    /// The union, as a canonical thinning.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn finish(self) -> Thinning
    {
        match self.listed {
            None => Thinning {
                inline: self.inline,
                spill: None,
            },
            Some(lists) => Self::finish_listed(*lists),
        }
    }

    /// Whether the union, finished, is `thinning`, without finishing it.
    ///
    /// # Specification
    /// - ensures: [`Agreement::Same`] exactly when `self.finish().view() ==
    ///   thinning`, the union unchanged.
    /// - panics: none.
    /// - executable: none — this runs once per node on the check path; the
    ///   instrumented body is a closure the test profile does not inline, and
    ///   the witness compares the answer with the finished union.
    /// - intension: one comparison of two words while the union is inline.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an inline union against its own thinning, one with an
    ///   index more, and a spilled union against its own thinning separate the
    ///   inline answer from the gathered one.
    /// - witness: `support::tests::a_union_equals_exactly_its_finished_thinning`
    #[inline]
    #[must_use]
    pub fn equals(
        &self,
        thinning: ThinningRef<'_>,
    ) -> Agreement
    {
        match self.listed {
            None if thinning.spill.is_none() && self.inline == thinning.inline => Agreement::Same,
            None => Agreement::Different,
            Some(ref lists) => Self::equals_listed(lists, thinning),
        }
    }

    /// Whether gathered lists, finished, are `thinning`: the comparison
    /// [`Self::equals`] keeps off its inline path.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn equals_listed(
        lists: &[Vec<DeBruijnIndex>; 2],
        thinning: ThinningRef<'_>,
    ) -> Agreement
    {
        if Self::finish_listed(lists.clone()).view() == thinning {
            Agreement::Same
        }
        else {
            Agreement::Different
        }
    }

    /// Empty the union for reuse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn clear(&mut self)
    {
        self.inline = Bits(0);
        if self.listed.is_some() {
            self.listed = None;
        }
    }

    /// The gathered lists, sorted and without repeats, as a canonical
    /// thinning.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn finish_listed(lists: [Vec<DeBruijnIndex>; 2]) -> Thinning
    {
        let [mut intuitionistic, mut linear] = lists;
        for list in [&mut intuitionistic, &mut linear] {
            list.sort_unstable();
            list.dedup();
        }
        Thinning::from_lists(intuitionistic, linear)
    }
}

/// The widths of a compact scope: how many slots each zone holds.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Scope
{
    /// The intuitionistic width.
    intuitionistic: BinderDepth,
    /// The linear width.
    linear: BinderDepth,
}

/// The binders of each zone a child stands under, counted from its parent.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Crossing
{
    /// Intuitionistic binders crossed.
    intuitionistic: BinderDepth,
    /// Linear binders crossed.
    linear: BinderDepth,
}

/// Why a pair of index lists is no thinning.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SelectionError
{
    /// The zone's indices repeat or descend.
    Unordered(Zone),
}

/// Why a cover is not the exact, minimal cover of its node.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CoverError
{
    /// The node holds a number of edges other than its children.
    Arity,
    /// An edge's width in the zone differs from its child's scope.
    Domain(Zone),
    /// An edge or an occurrence of the node selects past the node's scope.
    OutOfScope(Zone),
    /// A slot of the node's scope that no edge selects and the node does not
    /// name: the scope is not minimal.
    Unused(Zone),
}

/// Why a child or an occurrence has no ambient placement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PlacementError
{
    /// A placed index passes the `u32` index space.
    IndexOverflow,
    /// An edge or an occurrence selects past the parent's support.
    OutOfScope(Zone),
}

impl core::fmt::Display for SelectionError
{
    /// Name the zone whose selection is unordered.
    ///
    /// # Specification
    /// - ensures: writes the refused rule and its zone.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable sink.
    ///
    /// # Errors
    /// Returns the formatter's error when its sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant renders its own rule and zone.
    /// - witness: `support::tests::every_refusal_renders_its_rule`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Unordered(zone) => {
                write!(
                    f,
                    "the {} selection does not strictly ascend",
                    ZoneName(zone)
                )
            },
        }
    }
}

impl core::error::Error for SelectionError
{
}

impl core::fmt::Display for CoverError
{
    /// Name the cover rule that fails and its zone.
    ///
    /// # Specification
    /// - ensures: writes the refused rule and its zone.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable sink.
    ///
    /// # Errors
    /// Returns the formatter's error when its sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant renders its own rule and zone.
    /// - witness: `support::tests::every_refusal_renders_its_rule`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Arity => write!(f, "a cover holds one edge per child"),
            Self::Domain(zone) => write!(
                f,
                "a {} edge's width differs from its child's scope",
                ZoneName(zone)
            ),
            Self::OutOfScope(zone) => {
                write!(f, "a {} selection passes its node's scope", ZoneName(zone))
            },
            Self::Unused(zone) => write!(
                f,
                "a {} slot of the node's scope is selected by nothing",
                ZoneName(zone)
            ),
        }
    }
}

impl core::error::Error for CoverError
{
}

impl core::fmt::Display for PlacementError
{
    /// Name the placement rule that fails.
    ///
    /// # Specification
    /// - ensures: writes the refused rule, and its zone where it has one.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable sink.
    ///
    /// # Errors
    /// Returns the formatter's error when its sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant renders its own rule.
    /// - witness: `support::tests::every_refusal_renders_its_rule`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::IndexOverflow => write!(f, "a placed index passes the u32 index space"),
            Self::OutOfScope(zone) => write!(
                f,
                "a {} selection passes its parent's support",
                ZoneName(zone)
            ),
        }
    }
}

/// A zone as a message names it.
#[repr(transparent)]
struct ZoneName(Zone);

impl core::fmt::Display for ZoneName
{
    /// Writes the zone's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match self.0 {
            Zone::Intuitionistic => "intuitionistic",
            Zone::Linear => "linear",
        })
    }
}

impl core::error::Error for PlacementError
{
}

impl Scope
{
    /// The scope of `intuitionistic` and `linear` slots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        intuitionistic: BinderDepth,
        linear: BinderDepth,
    ) -> Self
    {
        Self {
            intuitionistic,
            linear,
        }
    }

    /// The width of `zone`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn width(
        self,
        zone: Zone,
    ) -> BinderDepth
    {
        match zone {
            Zone::Intuitionistic => self.intuitionistic,
            Zone::Linear => self.linear,
        }
    }
}

impl Crossing
{
    /// `intuitionistic` and `linear` binders crossed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        intuitionistic: BinderDepth,
        linear: BinderDepth,
    ) -> Self
    {
        Self {
            intuitionistic,
            linear,
        }
    }

    /// `count` binders of `zone` crossed, none of the other.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(
        zone: Zone,
        count: BinderDepth,
    ) -> Self
    {
        match zone {
            Zone::Intuitionistic => Self::new(count, BinderDepth::default()),
            Zone::Linear => Self::new(BinderDepth::default(), count),
        }
    }

    /// The binders of `zone` crossed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn depth(
        self,
        zone: Zone,
    ) -> BinderDepth
    {
        match zone {
            Zone::Intuitionistic => self.intuitionistic,
            Zone::Linear => self.linear,
        }
    }
}

/// `index` read past `crossed` binders: the index the same binder has one
/// crossing further out.
///
/// # Specification
/// - ensures: `index - crossed` when `index` reaches past every crossed binder;
///   `bound::Absent::Local` when it names one of them.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exhaustive indices below, at and above crossings of zero
///   to two binders separate a local binder from an outer one and the lowering
///   from identity.
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
#[spec(ensures: |ret| match ret {
    Maybe::Present(outer) => u64::from(u32::from(outer)).checked_add(u64::try_from(usize::from(crossed)).unwrap_or(u64::MAX)) == Some(u64::from(u32::from(index))),
    Maybe::Absent(bound::Absent::Local) => u64::from(u32::from(index)) < u64::try_from(usize::from(crossed)).unwrap_or(u64::MAX),
})]
fn outer(
    index: DeBruijnIndex,
    crossed: BinderDepth,
) -> Maybe<DeBruijnIndex, bound::Absent>
{
    let Ok(crossed) = u32::try_from(usize::from(crossed))
    else {
        return Maybe::Absent(bound::Absent::Local);
    };
    u32::from(index)
        .checked_sub(crossed)
        .map_or(Maybe::Absent(bound::Absent::Local), |outer| {
            Maybe::Present(DeBruijnIndex::from(outer))
        })
}

/// `index` read under `crossed` more binders.
///
/// # Specification
/// - ensures: `index + crossed`.
/// - fails: [`PlacementError::IndexOverflow`] when the sum passes `u32`.
/// - panics: none.
///
/// # Errors
/// - [`PlacementError::IndexOverflow`]: the raised index is unrepresentable.
///
/// # Adequacy
/// - hypothesis: L3 — the largest representable index under zero binders and
///   one below it under one binder are placed; the largest under one binder
///   overflows.
/// - witness: `support::tests::placement_reports_index_overflow`
#[spec(ensures: |ret| match ret {
    Ok(raised) => u64::from(u32::from(raised)) == u64::from(u32::from(index)).saturating_add(u64::try_from(usize::from(crossed)).unwrap_or(u64::MAX)),
    Err(error) => error == PlacementError::IndexOverflow,
})]
fn inner(
    index: DeBruijnIndex,
    crossed: BinderDepth,
) -> Result<DeBruijnIndex, PlacementError>
{
    let crossed =
        u32::try_from(usize::from(crossed)).map_err(|_overflow| PlacementError::IndexOverflow)?;
    let raised = u32::from(index)
        .checked_add(crossed)
        .ok_or(PlacementError::IndexOverflow)?;
    Ok(DeBruijnIndex::from(raised))
}

impl Thinning
{
    /// The empty selection: a closed node's support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn empty() -> Self
    {
        Self {
            inline: Bits(0),
            spill: None,
        }
    }

    /// The selection of `index` in `zone` alone: a variable's support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn leaf(
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Self
    {
        let mut leaf = Builder::default();
        leaf.push(zone, index);
        leaf.finish()
    }

    /// The thinning selecting `intuitionistic` and `linear`, as a reader that
    /// did not build them receives them.
    ///
    /// # Specification
    /// - ensures: the two selections, unchanged, when each strictly ascends.
    /// - fails: [`SelectionError::Unordered`] naming the first zone whose
    ///   indices repeat or descend.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SelectionError::Unordered`]: a zone's indices repeat or descend.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ascending, repeated and descending pairs in each zone
    ///   separate strict ascent from weak ascent and from either zone's check
    ///   alone.
    /// - witness: `support::tests::selections_refuse_unordered_indices`
    #[spec(
        captures: [given_intuitionistic = intuitionistic.clone(), given_linear = linear.clone()],
        ensures: |ret| match ret {
            | Ok(ref thinning) => thinning.indices(Zone::Intuitionistic).eq(given_intuitionistic.iter().copied())
                && thinning.indices(Zone::Linear).eq(given_linear.iter().copied()),
            | Err(SelectionError::Unordered(Zone::Intuitionistic)) => given_intuitionistic.windows(2).any(|pair| pair.first() >= pair.last()),
            | Err(SelectionError::Unordered(Zone::Linear)) => given_intuitionistic.windows(2).all(|pair| pair.first() < pair.last())
                && given_linear.windows(2).any(|pair| pair.first() >= pair.last()),
        },
    )]
    #[inline]
    pub fn from_ascending(
        intuitionistic: Vec<DeBruijnIndex>,
        linear: Vec<DeBruijnIndex>,
    ) -> Result<Self, SelectionError>
    {
        for (zone, indices) in [
            (Zone::Intuitionistic, &intuitionistic),
            (Zone::Linear, &linear),
        ] {
            if indices.windows(2).any(|pair| pair.first() >= pair.last()) {
                return Err(SelectionError::Unordered(zone));
            }
        }
        Ok(Self::from_lists(intuitionistic, linear))
    }

    /// The thinning selecting two strictly ascending lists, inline when both
    /// fit and as the lists themselves otherwise.
    ///
    /// # Specification
    /// - requires: each list strictly ascends.
    /// - ensures: the canonical thinning selecting the lists.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — lists ending on both sides of each inline width.
    /// - witness: `support::tests::selections_past_the_inline_width_spill`
    #[spec(
        requires: intuitionistic.windows(2).all(|pair| pair.first() < pair.last())
            && linear.windows(2).all(|pair| pair.first() < pair.last()),
        captures: [expected = (intuitionistic.clone(), linear.clone())],
        ensures: |ret| ret.indices(Zone::Intuitionistic).eq(expected.0.iter().copied())
            && ret.indices(Zone::Linear).eq(expected.1.iter().copied()),
    )]
    fn from_lists(
        intuitionistic: Vec<DeBruijnIndex>,
        linear: Vec<DeBruijnIndex>,
    ) -> Self
    {
        let fits = |list: &[DeBruijnIndex], zone: Zone| {
            list.last().is_none_or(|&last| last < inline_width(zone))
        };
        if fits(&intuitionistic, Zone::Intuitionistic) && fits(&linear, Zone::Linear) {
            let mut built = Builder::default();
            for (zone, list) in [
                (Zone::Intuitionistic, &intuitionistic),
                (Zone::Linear, &linear),
            ] {
                for &index in list {
                    built.push(zone, index);
                }
            }
            return built.finish();
        }
        Self {
            inline: Bits(0),
            spill: Some(Box::new(Spill {
                intuitionistic,
                linear,
            })),
        }
    }

    /// The thinning read in place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> ThinningRef<'_>
    {
        ThinningRef {
            inline: self.inline,
            spill: self.spill.as_deref(),
        }
    }

    /// The indices selected in `zone`, innermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn indices(
        &self,
        zone: Zone,
    ) -> Indices<'_>
    {
        self.view().indices(zone)
    }

    /// The indices selected in `zone` at or past `crossed`, as they stand:
    /// what a node selects beyond the binders its own former opens.
    ///
    /// # Specification
    /// - ensures: as [`ThinningRef::outside`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ThinningRef::outside`].
    /// - witness: `support::tests::outside_cuts_at_the_crossing`
    #[spec(ensures: |ret| ret.clone().eq(self.indices(zone).filter(|&index| {
        BinderDepth::from(usize::try_from(u32::from(index)).unwrap_or(usize::MAX)) >= crossed
    })))]
    #[inline]
    #[must_use]
    pub fn outside(
        &self,
        zone: Zone,
        crossed: BinderDepth,
    ) -> Indices<'_>
    {
        self.view().outside(zone, crossed)
    }

    /// The compact scope the selection embeds: one slot per selected index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn scope(&self) -> Scope
    {
        Scope {
            intuitionistic: BinderDepth::from(self.indices(Zone::Intuitionistic).len()),
            linear: BinderDepth::from(self.indices(Zone::Linear).len()),
        }
    }

    /// The position `index` takes in the compact scope: how many selected
    /// indices of `zone` lie inside it.
    ///
    /// # Specification
    /// - ensures: the rank of `index` among the zone's selected indices when
    ///   selected; `unselected::Absent::Unselected` otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exhaustive small selections: every selected index
    ///   ranks to its position and every unselected one is absent; the same
    ///   held past an inline width ranks through the spill.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    /// - witness: `support::tests::selections_past_the_inline_width_spill`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(rank) => self.indices(zone).nth(usize::try_from(u32::from(rank)).unwrap_or(usize::MAX)) == Some(index),
        Maybe::Absent(unselected::Absent::Unselected) => self.indices(zone).all(|held| held != index),
    })]
    #[inline]
    pub fn rank(
        &self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Maybe<DeBruijnIndex, unselected::Absent>
    {
        self.view().rank(zone, index)
    }

    /// The ambient index at position `rank` of the compact scope.
    ///
    /// # Specification
    /// - ensures: the zone's `rank`-th selected index.
    /// - fails: [`PlacementError::OutOfScope`] for a rank past the zone's
    ///   width.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlacementError::OutOfScope`]: the rank selects nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every rank of exhaustive small selections and the
    ///   first rank past each width.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    #[spec(ensures: |ret| match ret {
        Ok(index) => self.indices(zone).nth(usize::try_from(u32::from(rank)).unwrap_or(usize::MAX)) == Some(index),
        Err(error) => error == PlacementError::OutOfScope(zone)
            && self.indices(zone).nth(usize::try_from(u32::from(rank)).unwrap_or(usize::MAX)).is_none(),
    })]
    #[inline]
    pub fn select(
        &self,
        zone: Zone,
        rank: DeBruijnIndex,
    ) -> Result<DeBruijnIndex, PlacementError>
    {
        usize::try_from(u32::from(rank))
            .ok()
            .and_then(|rank| self.indices(zone).nth(rank))
            .ok_or(PlacementError::OutOfScope(zone))
    }

    /// The support of a node that names `own` itself and whose children have
    /// the supports and crossings `children` walks: what [`Cover::of`]
    /// carries, without the edges.
    ///
    /// # Specification
    /// - requires: `own` and every child's support are in the node's ambient
    ///   scope extended by that child's crossing.
    /// - ensures: exactly `own` together with every child index past its
    ///   crossing, lowered by it, per zone.
    /// - panics: none.
    /// - executable: none — `children` is consumed by the call, so a predicate
    ///   has no second walk of it; the witnesses compare the union with an
    ///   independent reference union.
    /// - intension: a shift and a disjunction per child while every selection
    ///   is inline; one sort per zone otherwise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exhaustive one-child and two-child unions over small
    ///   scopes and crossings of up to two binders per zone separate a lost
    ///   union member, a crossing applied to the wrong zone and an unlowered
    ///   index; a child and an occurrence past the inline widths take the
    ///   spilled path to the same union.
    /// - witness: `support::tests::placing_each_edge_recovers_its_child`
    /// - witness: `support::tests::a_cover_unions_its_children`
    /// - witness: `support::tests::selections_past_the_inline_width_spill`
    #[inline]
    pub fn covering<'child, Own, Children>(
        own: Own,
        children: Children,
    ) -> Self
    where
        Own: IntoIterator<Item = (Zone, DeBruijnIndex)>,
        Children: IntoIterator<Item = (&'child Self, Crossing)>,
    {
        let mut union = Union::new();
        for (zone, index) in own {
            union.name(zone, index);
        }
        for (child, crossing) in children {
            union.child(child.view(), crossing);
        }
        union.finish()
    }

    /// The support of a child whose edge is `edge` and which stands under
    /// `crossing` more binders than this node, whose support this is.
    ///
    /// Composition: the edge selects from this node's compact scope extended
    /// by the child's local binders, and this support extended past them
    /// selects from the ambient scope.
    ///
    /// # Specification
    /// - requires: `edge` selects from this node's compact scope extended by
    ///   `crossing`, as [`Cover::of`] built it or [`check_cover`] admitted it.
    /// - ensures: each local binder the edge selects stays its own index; each
    ///   outer slot becomes the ambient index this support selects there,
    ///   raised past the crossing. The result strictly ascends.
    /// - fails: [`PlacementError::IndexOverflow`] when a raised index passes
    ///   `u32`; [`PlacementError::OutOfScope`] when the edge selects past this
    ///   support.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlacementError::IndexOverflow`]: an ambient index is unrepresentable
    ///   under the child's binders.
    /// - [`PlacementError::OutOfScope`]: the edge selects a slot this support
    ///   does not hold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exhaustive one-child covers over small scopes and
    ///   crossings of up to two binders per zone: placing each edge recovers
    ///   the child's support exactly, separating local binders from outer
    ///   slots, the zones from each other and the raise from identity; the
    ///   index ceiling separates overflow from saturation.
    /// - witness: `support::tests::placing_each_edge_recovers_its_child`
    /// - witness: `support::tests::placement_reports_index_overflow`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |placed| placed.scope() == edge.scope()))]
    #[inline]
    pub fn place(
        &self,
        edge: &Self,
        crossing: Crossing,
    ) -> Result<Self, PlacementError>
    {
        let mut placed = Builder::default();
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            let crossed = crossing.depth(zone);
            for slot in edge.indices(zone) {
                let ambient = match outer(slot, crossed) {
                    Maybe::Absent(bound::Absent::Local) => slot,
                    Maybe::Present(rank) => {
                        let selected = self.select(zone, rank)?;
                        inner(selected, crossed)?
                    },
                };
                placed.push(zone, ambient);
            }
        }
        Ok(placed.finish())
    }
}

impl core::fmt::Debug for Thinning
{
    /// Writes each zone's selected indices.
    ///
    /// # Specification
    /// - ensures: writes the intuitionistic and the linear indices, ascending.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable sink.
    ///
    /// # Errors
    /// Returns the formatter's error when its sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an inline selection and a spilled one print the same
    ///   listing of their indices, so the form never shows.
    /// - witness: `support::tests::a_thinning_prints_its_indices_in_either_form`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("Thinning")
            .field(
                "intuitionistic",
                &Listing(self.indices(Zone::Intuitionistic)),
            )
            .field("linear", &Listing(self.indices(Zone::Linear)))
            .finish()
    }
}

/// A zone's indices as a debug list.
#[repr(transparent)]
struct Listing<'thinning>(Indices<'thinning>);

impl core::fmt::Debug for Listing<'_>
{
    /// Writes the indices as a list.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_list().entries(self.0.clone()).finish()
    }
}

/// A node's support and the edge embedding each child's support in it.
///
/// # Specification
/// - executable: none — a data declaration; [`Cover::of`] establishes that the
///   support is the exact union and that each edge selects its child's whole
///   support.
///
/// # Adequacy
/// - hypothesis: L3 — exhaustive one-child covers recover each child by
///   placement and pass [`check_cover`]; two-child covers union their outer
///   selections.
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
/// - witness: `support::tests::a_cover_unions_its_children`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Cover
{
    /// The node's support in its ambient scope.
    support: Thinning,
    /// One edge per child, in child order.
    edges: Vec<Thinning>,
}

impl Cover
{
    /// Cover a node that names `own` itself and whose children have the
    /// supports and crossings `children` walks, in child order; the walk is
    /// cloned for each pass over the children.
    ///
    /// # Specification
    /// - requires: `own` and every child's support are in the node's ambient
    ///   scope extended by that child's crossing; every clone of `children`
    ///   yields the same sequence.
    /// - ensures: the support is [`Thinning::covering`] of `own` and the
    ///   children; each edge has its child's widths, keeps each local binder
    ///   the child selects as its own index, and reads each outer index as its
    ///   crossing plus its rank in the support. Placing each edge from the
    ///   support gives back its child's support.
    /// - panics: none.
    /// - intension: one union, and one rank per selected child index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exhaustive one-child covers over small scopes,
    ///   crossings of up to two binders per zone and every own occurrence set;
    ///   two-child covers with overlapping, disjoint and nested selections
    ///   separate a lost union member, a duplicated slot, a mis-ranked edge and
    ///   a crossing applied to the wrong zone.
    /// - witness: `support::tests::placing_each_edge_recovers_its_child`
    /// - witness: `support::tests::a_cover_unions_its_children`
    #[spec(ensures: |ret| ret.edges.len() == children.clone().count()
        && ret.edges.iter().zip(children.clone()).all(|(edge, (child, crossing))|
            edge.scope() == child.scope() && ret.support.place(edge, crossing).as_ref() == Ok(child)))]
    #[inline]
    pub fn of<'child, Own, Children>(
        own: Own,
        children: &Children,
    ) -> Self
    where
        Own: IntoIterator<Item = (Zone, DeBruijnIndex)>,
        Children: Iterator<Item = (&'child Thinning, Crossing)> + Clone,
    {
        let support = Thinning::covering(own, children.clone());
        let edges = children
            .clone()
            .map(|(child, crossing)| {
                let mut edge = Builder::default();
                for zone in [Zone::Intuitionistic, Zone::Linear] {
                    let crossed = crossing.depth(zone);
                    for index in child.indices(zone) {
                        let slot = match outer(index, crossed) {
                            Maybe::Absent(bound::Absent::Local) => index,
                            Maybe::Present(outer) => match support.rank(zone, outer) {
                                // reason: the support is the union of what the
                                // children select past their crossings, so
                                // `outer` is selected; its rank plus the
                                // crossing is at most the child's own index,
                                // which fits.
                                Maybe::Present(rank) => inner(rank, crossed).unwrap_or(index),
                                Maybe::Absent(unselected::Absent::Unselected) => index,
                            },
                        };
                        edge.push(zone, slot);
                    }
                }
                edge.finish()
            })
            .collect();
        Self { support, edges }
    }

    /// The node's support in its ambient scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn support(&self) -> &Thinning
    {
        &self.support
    }

    /// The edges, in child order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn edges(&self) -> &[Thinning]
    {
        &self.edges
    }

    /// The support and the edges, by value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (Thinning, Vec<Thinning>)
    {
        (self.support, self.edges)
    }
}

/// Check that `edges` are the exact, minimal cover of a node of `scope` that
/// names the compact positions `own` itself and whose children have the
/// scopes and crossings `children`.
///
/// # Specification
/// - requires: nothing — this is the reader's check of a cover it did not
///   build.
/// - ensures: success exactly when there is one edge per child, each edge has
///   its child's widths, every outer slot an edge selects and every position
///   the node names is inside `scope`, and every slot of `scope` is selected by
///   some edge or named by the node.
/// - fails: [`CoverError::Arity`] for an edge count other than the child count;
///   [`CoverError::Domain`] for an edge whose widths differ from its child's;
///   [`CoverError::OutOfScope`] for a selection past the scope;
///   [`CoverError::Unused`] for a slot nothing selects. Arity is checked first,
///   then each edge's domain in child order, then the selections' range in zone
///   order, then coverage in zone order.
/// - panics: none.
/// - intension: allocates for the selected slots, never for the scope's width,
///   so a reader's forged width costs nothing before it is refused.
///
/// # Errors
/// - [`CoverError::Arity`], [`CoverError::Domain`], [`CoverError::OutOfScope`],
///   [`CoverError::Unused`]: as above.
///
/// # Adequacy
/// - hypothesis: L3 — every cover [`Cover::of`] builds over exhaustive small
///   scopes passes; one forged cover per refusal, in each zone, fails with
///   exactly its own error: a missing edge, a widened edge, an edge past the
///   scope, an own position past the scope and a widened scope.
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
/// - witness: `support::tests::a_cover_refuses_every_forged_edge`
#[spec(captures: [count = children.clone().count()], ensures: |ret| ret.is_err() || edges.len() == count)]
#[inline]
pub fn check_cover<Own, Children>(
    scope: Scope,
    own: Own,
    edges: &[Thinning],
    children: Children,
) -> Result<(), CoverError>
where
    Own: IntoIterator<Item = (Zone, DeBruijnIndex)>,
    Children: Iterator<Item = (Scope, Crossing)> + Clone,
{
    if children.clone().count() != edges.len() {
        return Err(CoverError::Arity);
    }
    let mut selected: [Vec<DeBruijnIndex>; 2] = [Vec::new(), Vec::new()];
    let mut select = |zone: Zone, slot: DeBruijnIndex| {
        let [ref mut intuitionistic, ref mut linear] = selected;
        match zone {
            Zone::Intuitionistic => intuitionistic.push(slot),
            Zone::Linear => linear.push(slot),
        }
    };
    for (edge, (child, crossing)) in edges.iter().zip(children) {
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            if edge.scope().width(zone) != child.width(zone) {
                return Err(CoverError::Domain(zone));
            }
            for slot in edge.indices(zone) {
                if let Maybe::Present(outer) = outer(slot, crossing.depth(zone)) {
                    select(zone, outer);
                }
            }
        }
    }
    for (zone, slot) in own {
        select(zone, slot);
    }
    for slots in &mut selected {
        slots.sort_unstable();
        slots.dedup();
    }
    let zones = [Zone::Intuitionistic, Zone::Linear];
    for (zone, slots) in zones.into_iter().zip(&selected) {
        let width = scope.width(zone);
        let past = slots.last().is_some_and(|&last| {
            usize::try_from(u32::from(last)).map_or(true, |last| last >= usize::from(width))
        });
        if past {
            return Err(CoverError::OutOfScope(zone));
        }
    }
    for (zone, slots) in zones.into_iter().zip(&selected) {
        if slots.len() != usize::from(scope.width(zone)) {
            return Err(CoverError::Unused(zone));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
