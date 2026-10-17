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
//! [`Cover::of`] builds a node's support from the variables it names itself
//! and its children's supports — the union of what each child mentions above
//! the binders between them — and one edge per child: the child's support
//! read as a selection from the node's compact scope extended by the child's
//! local binders. The edges are the cover. Two nodes whose formers, covers
//! and widths agree are the same compact node wherever they stand, so one
//! subterm placed under different unused binders is one node. A variable's
//! support is the one index it names, so a variable is a bare leaf: its
//! compact scope has one slot and its index carries nothing.
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
//! scoping: the incremental content table today, the command IL and the core
//! nodes after it, so they share one algebra and one witness set.
//! **Alternatives.** The carrier inside the content table's crate, which the
//! next consumers would have to depend on or copy; a crate of its own, which
//! separates the carrier from the zones and binder depths it is stated over.
//! **Reversal.** A consumer outside the core vocabulary — one whose zones are
//! not `Γ; Σ` — moves the carrier into its own crate.
//!
//! # Sparse selections
//!
//! A thinning stores the selected indices, not one bit per scope entry. A
//! small support can name a large index — a reference to a binder thousands
//! of levels out — and a bitset pays for the whole scope width at every node
//! and every edge; a sparse selection pays for what is selected. Composition
//! is a merge or a binary search per selected index rather than word-wise
//! logic. **Reversal.** A measured workload whose supports are dense in their
//! scopes, where a bitset's word operations outrun the per-index walk and its
//! width is no larger than the selection.
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

/// An order-preserving selection from a two-zone scope.
///
/// # Specification
/// - executable: none — a data declaration; [`Thinning::from_ascending`] and
///   [`Cover::of`] establish the invariant that each zone's indices strictly
///   ascend.
///
/// # Adequacy
/// - hypothesis: L3 — exhaustive small scopes and the unordered near-misses
///   separate dropped, repeated and misordered selections in either zone.
/// - witness: `support::tests::selections_refuse_unordered_indices`
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Thinning
{
    /// Selected intuitionistic indices, strictly ascending.
    intuitionistic: Vec<DeBruijnIndex>,
    /// Selected linear indices, strictly ascending.
    linear: Vec<DeBruijnIndex>,
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
            intuitionistic: Vec::new(),
            linear: Vec::new(),
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
        let mut leaf = Self::empty();
        leaf.zone_mut(zone).push(index);
        leaf
    }

    /// The selection of `indices` in `zone` alone, gathered in any order and
    /// with repeats.
    ///
    /// # Specification
    /// - ensures: the zone selects each index of `indices` once, ascending; the
    ///   other zone selects nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a gathered list out of order and with a repeat
    ///   separates sorting and deduplication from either alone.
    /// - witness: `rewrite::tests::a_value_type_support_names_exactly_its_free_indices`
    #[spec(ensures: |ret| ret.indices(zone).windows(2).all(|pair| pair.first() < pair.last())
        && ret.indices(match zone {
            | Zone::Intuitionistic => Zone::Linear,
            | Zone::Linear => Zone::Intuitionistic,
        }).is_empty())]
    pub(crate) fn gathered(
        zone: Zone,
        mut indices: Vec<DeBruijnIndex>,
    ) -> Self
    {
        indices.sort_unstable();
        indices.dedup();
        let mut gathered = Self::empty();
        *gathered.zone_mut(zone) = indices;
        gathered
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
            | Ok(ref thinning) => thinning.intuitionistic == given_intuitionistic && thinning.linear == given_linear,
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
        Ok(Self {
            intuitionistic,
            linear,
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
    ) -> &[DeBruijnIndex]
    {
        match zone {
            Zone::Intuitionistic => &self.intuitionistic,
            Zone::Linear => &self.linear,
        }
    }

    /// The selection of `zone`, to extend.
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

    /// The compact scope the selection embeds: one slot per selected index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn scope(&self) -> Scope
    {
        Scope {
            intuitionistic: BinderDepth::from(self.intuitionistic.len()),
            linear: BinderDepth::from(self.linear.len()),
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
    ///   ranks to its position and every unselected one is absent.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(rank) => self.indices(zone).get(usize::try_from(u32::from(rank)).unwrap_or(usize::MAX)) == Some(&index),
        Maybe::Absent(unselected::Absent::Unselected) => self.indices(zone).binary_search(&index).is_err(),
    })]
    #[inline]
    pub fn rank(
        &self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Maybe<DeBruijnIndex, unselected::Absent>
    {
        self.indices(zone).binary_search(&index).map_or(
            Maybe::Absent(unselected::Absent::Unselected),
            |rank| {
                // reason: a rank counts distinct `u32` indices below another
                // `u32` index, so it fits; the clamp keeps the conversion total.
                Maybe::Present(DeBruijnIndex::from(u32::try_from(rank).unwrap_or(u32::MAX)))
            },
        )
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
        Ok(index) => self.indices(zone).get(usize::try_from(u32::from(rank)).unwrap_or(usize::MAX)) == Some(&index),
        Err(error) => error == PlacementError::OutOfScope(zone)
            && self.indices(zone).get(usize::try_from(u32::from(rank)).unwrap_or(usize::MAX)).is_none(),
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
            .and_then(|rank| self.indices(zone).get(rank))
            .copied()
            .ok_or(PlacementError::OutOfScope(zone))
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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |placed| placed.scope() == edge.scope()
        && [Zone::Intuitionistic, Zone::Linear].into_iter().all(|zone|
            placed.indices(zone).windows(2).all(|pair| pair.first() < pair.last()))))]
    #[inline]
    pub fn place(
        &self,
        edge: &Self,
        crossing: Crossing,
    ) -> Result<Self, PlacementError>
    {
        let mut placed = Self::empty();
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            let crossed = crossing.depth(zone);
            let target = placed.zone_mut(zone);
            target.reserve_exact(edge.indices(zone).len());
            for &slot in edge.indices(zone) {
                let ambient = match outer(slot, crossed) {
                    Maybe::Absent(bound::Absent::Local) => slot,
                    Maybe::Present(rank) => {
                        let selected = self.select(zone, rank)?;
                        inner(selected, crossed)?
                    },
                };
                target.push(ambient);
            }
        }
        Ok(placed)
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
    /// - ensures: the support is exactly `own` together with every child index
    ///   past its crossing, lowered by the crossing, per zone; each edge has
    ///   its child's widths, keeps each local binder the child selects as its
    ///   own index, and reads each outer index as its crossing plus its rank in
    ///   the support. Placing each edge from the support gives back its child's
    ///   support.
    /// - panics: none.
    /// - intension: one sort per zone over the gathered indices, and one binary
    ///   search per selected child index.
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
        let mut support = Thinning::empty();
        for (zone, index) in own {
            support.zone_mut(zone).push(index);
        }
        for (child, crossing) in children.clone() {
            for zone in [Zone::Intuitionistic, Zone::Linear] {
                let crossed = crossing.depth(zone);
                support
                    .zone_mut(zone)
                    .extend(child.indices(zone).iter().filter_map(|&index| {
                        match outer(index, crossed) {
                            Maybe::Present(outer) => Some(outer),
                            Maybe::Absent(bound::Absent::Local) => None,
                        }
                    }));
            }
        }
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            let selected = support.zone_mut(zone);
            selected.sort_unstable();
            selected.dedup();
        }
        let edges = children
            .clone()
            .map(|(child, crossing)| {
                let mut edge = Thinning::empty();
                for zone in [Zone::Intuitionistic, Zone::Linear] {
                    let crossed = crossing.depth(zone);
                    let target = edge.zone_mut(zone);
                    target.reserve_exact(child.indices(zone).len());
                    for &index in child.indices(zone) {
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
                        target.push(slot);
                    }
                }
                edge
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
            for &slot in edge.indices(zone) {
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
