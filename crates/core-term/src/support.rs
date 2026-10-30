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
//! # The tiered code
//!
//! A thinning is written in one self-describing code per zone it selects
//! from, each a whole number of 64-bit words whose first word opens with an
//! eight-bit header naming the form, the zone and the length. Three forms
//! carry a selection — a dense bitset, an Elias–Fano sequence for a sparse
//! one and a run for a contiguous one — and the encoder writes the shortest,
//! dense on a tie, so each selection has exactly one code and the derived
//! equality and hashing compare selections. A one-word dense code holds the
//! 56 innermost binders; the empty selection is the zero word; a variable's
//! support is one word wherever its binder stands, dense inside the word and
//! a run of one past it. A [`Thinning`] is three words: its code's first word
//! inline and the rest behind one pointer, present exactly when the code
//! spans more than one word, so a one-word support allocates nothing. Rank
//! and select are population counts over the dense form and over the sparse
//! form's unary upper bits, and arithmetic over a run. The code is defined in
//! the `code` module.
//!
//! **Choice.** The tiered code with a header word, as designed for the
//! carrier: forms chosen by size, so a deep, sparse support costs bits per
//! index rather than bits per binder of depth, and a contiguous one costs a
//! word. Three refinements, each where that design assumed one zone or left
//! the order open: the header names the zone, so a thinning writes up to two
//! codes and reads either without decoding the other; the length field is
//! five bits with a long form past 31 words, so the header stays one byte and
//! the one-word dense code keeps 56 binders; and a run wins a tie with a
//! sparse code, since a run decodes in constant time.
//! **Alternatives.** The fixed form it replaced — 48 intuitionistic and 16
//! linear bits in one word, sorted index lists behind a pointer past either —
//! which allocates for any support naming a binder past 48 and costs a word
//! per 64 binders of depth; a dense bitset alone, whose size is the scope's
//! depth; Roaring containers, whose per-container headers outweigh supports
//! of a few indices. **Reversal.** A measured workload whose supports span
//! more than one word often enough that decoding dominates their reads, which
//! adds a dense accumulator to the union or widens the inline word.
//!
//! A [`Union`] builds a support from what a node names and its children's
//! supports past their crossings, in any order and with repeats: while every
//! index lands in the intuitionistic zone's one-word dense code, an uncrossed
//! child is one disjunction and a crossed one a shift, a mask and a
//! disjunction. Past that word it gathers each zone's indices and writes the
//! code once when finished. The design states the union as a word-wise
//! disjunction in the dense tier; a dense accumulator for a deep, sparse
//! support takes the scope's width, which is the cost the sparse form
//! removes, so past the word the union gathers indices instead.
//! [`ThinningRef`] reads a code in place — its first word by value, the rest
//! by reference — so a hot read neither clones nor drops a thinning.
//!
//! # Where supports are kept
//!
//! A table keeps a support as a [`Slot`] in the node's row: one word, the
//! code itself when the code is one word and otherwise a handle to its words
//! in a [`WordArena`], so the row grows by one word and the wide case stays
//! off it.
//!
//! # The fence
//!
//! A carried support is syntactic: it over-approximates dependence. A
//! β-removable or singleton-typed use still occurs, so the support names it.
//! It keys, footprints, schedules and bounds capture, where an
//! over-approximation splits work and never merges two answers. It decides
//! the syntactic strengthening — a type whose support selects a binder
//! mentions it, exactly where an occurrence walk would find it — and never a
//! semantic one: whether a type that mentions a binder can still be lowered
//! out of it is the judgement's question, answered by unification over the
//! type, and the bind rule's strengthening stays the refusal it is.
//!
//! # References
//!
//! - Conor `McBride`. "Everybody's Got To Be Somewhere." _Proceedings of the
//!   7th Workshop on Mathematically Structured Functional Programming (MSFP
//!   2018)_, EPTCS 275, pages 53–69. `doi:10.4204/EPTCS.275.6` — co-de Bruijn
//!   representation: thinnings, covers and relevant pairs, with every variable
//!   a bare leaf.
//! - Peter Elias. "Efficient Storage and Retrieval by Content and Address of
//!   Static Files." _Journal of the ACM_ 21(2), 1974, pages 246–260.
//!   `doi:10.1145/321812.321820` — the monotone sequence split into lower bits
//!   and unary upper bits that the sparse form writes.
//! - Robert M. Fano. "On the Number of Bits Required to Implement an
//!   Associative Memory." Memorandum 61, Computer Structures Group, Project
//!   MAC, MIT, 1971 — the same split, found independently.
//! - Sebastiano Vigna. "Quasi-Succinct Indices." _Proceedings of the Sixth ACM
//!   International Conference on Web Search and Data Mining (WSDM 2013)_, pages
//!   83–92. `doi:10.1145/2433396.2433409` — Elias–Fano sequences read by rank
//!   and select over the upper bits, and the lower width `⌊log₂(u / n)⌋`.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use self::code::Buffer;
pub use self::code::Coding;
use self::code::Raw;
use self::code::Seq;
use self::code::Walk;
use self::code::Word;
pub use self::code::WordCount;
use self::code::omitted;
use self::code::walked;
pub use self::store::Slot;
pub use self::store::WordArena;
pub use self::store::WordMark;
pub use self::store::unstored;
use crate::context::BinderDepth;
use crate::syntax::Zone;

mod code;
mod store;

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
pub(crate) mod bound
{
    /// The single reason an index has no image past a crossing.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// The index names one of the binders crossed.
        Local,
    }
}

/// An order-preserving selection from a two-zone scope.
///
/// # Specification
/// - executable: none — a data declaration. Every constructor writes the
///   encoder's one code for the selection: `head` is the code's first word, and
///   `tail` holds the rest, present exactly when the code spans more than one
///   word.
///
/// # Adequacy
/// - hypothesis: L3 — exhaustive small scopes and the unordered near-misses
///   separate dropped, repeated and misordered selections in either zone;
///   selections on both sides of each form's boundary keep equality canonical
///   across the forms.
/// - witness: `support::tests::selections_refuse_unordered_indices`
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
/// - witness: `support::tests::one_encoding_per_selection`
#[derive(Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Thinning
{
    /// The code's first word.
    head: Word,
    /// The code's other words, when it spans more than one.
    tail: Option<Box<[u64]>>,
}

/// A thinning read in place: its code's first word by value and the rest by
/// reference.
///
/// It is `Copy`, so a hot read of a stored support neither clones nor drops
/// one; equality compares the words, which the encoder makes one per
/// selection.
///
/// # Specification
/// - executable: none — a data declaration; it is made only from a
///   [`Thinning`], a stored [`Slot`] or a one-word code, so its words are the
///   encoder's code.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct ThinningRef<'thinning>
{
    /// The code's words.
    seq: Seq<'thinning>,
}

impl<'thinning> ThinningRef<'thinning>
{
    /// The empty selection, read in place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn empty() -> Self
    {
        Self {
            seq: Seq {
                head: Word(0),
                tail: &[],
            },
        }
    }

    /// The selection of `index` in `zone` alone, read in place: a variable's
    /// support, one word wherever its binder stands.
    ///
    /// # Specification
    /// - ensures: the view of [`Thinning::leaf`] of the same index.
    /// - panics: none.
    /// - executable: none — the witness compares it with the encoder's code.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last index the one-word dense code holds and the
    ///   first past it, in either zone.
    /// - witness: `support::tests::the_mode_switches_at_its_boundaries`
    #[inline]
    #[must_use]
    pub fn leaf(
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Self
    {
        Self {
            seq: Seq {
                head: code::single(zone, index),
                tail: &[],
            },
        }
    }

    /// The code `seq` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn of_seq(seq: Seq<'thinning>) -> Self
    {
        Self { seq }
    }

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
        Indices(self.seq.walk(zone, Raw(0)))
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
    /// - hypothesis: L3 — selections of every form below, at and past a
    ///   crossing of zero to two binders, and past the one-word code, separate
    ///   the cut from its neighbours.
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
        let from = u64::try_from(usize::from(crossed)).unwrap_or(u64::MAX);
        Indices(self.seq.walk(zone, Raw(from)))
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
    ///   held in every form ranks through that form.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    /// - witness: `support::tests::one_encoding_per_selection`
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
        match self.seq.rank(zone, index) {
            // reason: a rank counts distinct `u32` indices below another `u32`
            // index, so it fits; the clamp keeps the conversion total.
            Maybe::Present(rank) => Maybe::Present(DeBruijnIndex::from(
                u32::try_from(rank.0).unwrap_or(u32::MAX),
            )),
            Maybe::Absent(omitted::Absent::Omitted) => {
                Maybe::Absent(unselected::Absent::Unselected)
            },
        }
    }

    /// The form the code of `zone` takes.
    ///
    /// # Specification
    /// - ensures: [`Coding::Omitted`] exactly when the selection writes no code
    ///   for `zone` — a zone that selects nothing, save the intuitionistic zone
    ///   of the empty selection, which is the empty dense code — and the code's
    ///   form otherwise.
    /// - panics: none.
    /// - executable: none — the form is read off the header the predicate would
    ///   read; the witnesses hold it to an independent sizing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — selections at either side of each form's boundary, in
    ///   either zone.
    /// - witness: `support::tests::the_mode_switches_at_its_boundaries`
    #[inline]
    #[must_use]
    pub fn coding(
        self,
        zone: Zone,
    ) -> Coding
    {
        match self.seq.zone(zone) {
            Maybe::Present(code) => code.coding(),
            Maybe::Absent(omitted::Absent::Omitted) => Coding::Omitted,
        }
    }

    /// How many words the selection's codes span together.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn words(self) -> WordCount
    {
        self.seq.len()
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
            head: self.seq.head,
            tail: if self.seq.tail.is_empty() {
                None
            }
            else {
                Some(Box::from(self.seq.tail))
            },
        }
    }
}

impl core::fmt::Debug for ThinningRef<'_>
{
    /// Writes each zone's selected indices, as [`Thinning`]'s does.
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
    /// - hypothesis: L3 — as [`Thinning`]'s.
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

/// The indices a thinning selects in one zone, innermost first.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Indices<'thinning>(Walk<'thinning>);

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
        match self.0.front() {
            Maybe::Present(index) => Some(index),
            Maybe::Absent(walked::Absent::Exhausted) => None,
        }
    }

    /// The indices left, exactly.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let left = usize::try_from(self.0.left().0).unwrap_or(usize::MAX);
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
        match self.0.back() {
            Maybe::Present(index) => Some(index),
            Maybe::Absent(walked::Absent::Exhausted) => None,
        }
    }
}

impl ExactSizeIterator for Indices<'_>
{
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
    /// The intuitionistic zone's one-word dense code, while every index fits
    /// it.
    inline: Word,
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
            inline: Word(0),
            listed: None,
        }
    }

    /// Add `index`, which the node names itself, to `zone`.
    ///
    /// # Specification
    /// - ensures: the union holds `index` in `zone`; a linear index, or an
    ///   intuitionistic index past the one-word code, moves every earlier index
    ///   to the gathered lists.
    /// - panics: none.
    /// - executable: none — the union is read only by finishing it, which
    ///   consumes it, and this runs once per name on the mint path; the witness
    ///   finishes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — occurrences on both sides of the one-word code's
    ///   width, in either zone.
    /// - witness: `support::tests::union_is_canonical`
    #[inline]
    pub fn name(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    )
    {
        if self.listed.is_none()
            && zone == Zone::Intuitionistic
            && let Maybe::Present(bit) = Word::inline_bit(index)
        {
            self.inline.0 |= bit.0;
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
    /// - intension: one disjunction for an uncrossed child, a shift, a mask and
    ///   a disjunction for a crossed one, while both are one-word dense
    ///   intuitionistic codes.
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
        if self.listed.is_none()
            && child.seq.tail.is_empty()
            && let Maybe::Present(word) = child.seq.head.inline_dense()
        {
            self.inline.0 |= word.lowered(crossing.depth(Zone::Intuitionistic)).0;
            return;
        }
        self.child_listed(child, crossing);
    }

    /// Add a child's outer indices one at a time, once either side is past
    /// the one-word code.
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
        let inline = core::mem::take(&mut self.inline);
        self.listed.get_or_insert_with(|| {
            let held = ThinningRef::of_seq(Seq {
                head: inline,
                tail: &[],
            });
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
                head: self.inline,
                tail: None,
            },
            Some(lists) => Self::finish_listed(*lists),
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
        Thinning::from_lists(&intuitionistic, &linear)
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
pub(crate) fn outer(
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
            head: Word(0),
            tail: None,
        }
    }

    /// The selection of `index` in `zone` alone: a variable's support, one word
    /// wherever its binder stands.
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
        ThinningRef::leaf(zone, index).to_thinning()
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
        ensures: |ret| match ret {
            | Ok(ref thinning) => thinning.indices(Zone::Intuitionistic).eq(intuitionistic.iter().copied())
                && thinning.indices(Zone::Linear).eq(linear.iter().copied()),
            | Err(SelectionError::Unordered(Zone::Intuitionistic)) => intuitionistic.windows(2).any(|pair| pair.first() >= pair.last()),
            | Err(SelectionError::Unordered(Zone::Linear)) => intuitionistic.windows(2).all(|pair| pair.first() < pair.last())
                && linear.windows(2).any(|pair| pair.first() >= pair.last()),
        },
    )]
    #[inline]
    pub fn from_ascending(
        intuitionistic: &[DeBruijnIndex],
        linear: &[DeBruijnIndex],
    ) -> Result<Self, SelectionError>
    {
        for (zone, indices) in [
            (Zone::Intuitionistic, intuitionistic),
            (Zone::Linear, linear),
        ] {
            if indices.windows(2).any(|pair| pair.first() >= pair.last()) {
                return Err(SelectionError::Unordered(zone));
            }
        }
        Ok(Self::from_lists(intuitionistic, linear))
    }

    /// The thinning selecting two strictly ascending lists: the encoder's code
    /// of each zone that selects something.
    ///
    /// # Specification
    /// - requires: each list strictly ascends.
    /// - ensures: the canonical thinning selecting the lists.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — lists on both sides of each form's boundary, in
    ///   either zone and in both.
    /// - witness: `support::tests::one_encoding_per_selection`
    #[spec(
        requires: intuitionistic.windows(2).all(|pair| pair.first() < pair.last())
            && linear.windows(2).all(|pair| pair.first() < pair.last()),
        ensures: |ret| ret.indices(Zone::Intuitionistic).eq(intuitionistic.iter().copied())
            && ret.indices(Zone::Linear).eq(linear.iter().copied()),
    )]
    fn from_lists(
        intuitionistic: &[DeBruijnIndex],
        linear: &[DeBruijnIndex],
    ) -> Self
    {
        match (intuitionistic.last(), linear.last()) {
            (None, None) => return Self::empty(),
            (Some(_), None) | (None, Some(_)) => {
                let (zone, list) = if linear.is_empty() {
                    (Zone::Intuitionistic, intuitionistic)
                }
                else {
                    (Zone::Linear, linear)
                };
                let mut word = 0_u64;
                let mut inline = true;
                for &index in list {
                    match Word::inline_bit(index) {
                        Maybe::Present(bit) => word |= bit.0,
                        Maybe::Absent(omitted::Absent::Omitted) => {
                            inline = false;
                            break;
                        },
                    }
                }
                if inline {
                    return Self {
                        head: Word(word).in_zone(zone),
                        tail: None,
                    };
                }
            },
            (Some(_), Some(_)) => {},
        }
        let mut words = Buffer(Vec::new());
        if !intuitionistic.is_empty() {
            code::encode(Zone::Intuitionistic, intuitionistic, &mut words);
        }
        if !linear.is_empty() {
            code::encode(Zone::Linear, linear, &mut words);
        }
        Self::from_buffer(words)
    }

    /// The thinning whose code is `words`.
    ///
    /// # Specification
    /// trivial.
    fn from_buffer(words: Buffer) -> Self
    {
        let Buffer(mut words) = words;
        if words.len() <= 1 {
            return Self {
                head: Word(words.first().copied().unwrap_or(0)),
                tail: None,
            };
        }
        let head = Word(words.remove(0));
        Self {
            head,
            tail: Some(words.into_boxed_slice()),
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
        ThinningRef::of_seq(Seq {
            head: self.head,
            tail: self.tail.as_deref().unwrap_or_default(),
        })
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
    ///   held in every form ranks through that form.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    /// - witness: `support::tests::one_encoding_per_selection`
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
    /// - intension: a shift, a mask and a disjunction per child while every
    ///   selection is a one-word dense code; one sort per zone otherwise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exhaustive one-child and two-child unions over small
    ///   scopes and crossings of up to two binders per zone separate a lost
    ///   union member, a crossing applied to the wrong zone and an unlowered
    ///   index; a child and an occurrence past the one-word code take the
    ///   gathered path to the same union.
    /// - witness: `support::tests::placing_each_edge_recovers_its_child`
    /// - witness: `support::tests::a_cover_unions_its_children`
    /// - witness: `support::tests::union_is_canonical`
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
        let mut placed = Union::new();
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
                placed.name(zone, ambient);
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
    /// - hypothesis: L3 — selections in every form print the same listing of
    ///   their indices, so the form never shows.
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
                let mut edge = Union::new();
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
                        edge.name(zone, slot);
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
