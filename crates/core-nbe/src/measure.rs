//! He's sharing measure over one validated overlay root.
//!
//! # Five quantities, one walk
//!
//! [`SharingMeasure::of`] validates a root, then walks it once in post-order
//! over a heap task stack and reports five quantities: the shares the root
//! holds, the occurrences they stand for — their arities summed — the longest
//! chain of nested shares, the overlay nodes the root reaches, and the size of
//! the unshared term it stands for. A chain of shares counts through legs and
//! bodies alike: a share inside another's leg lies beneath it in the overlay as
//! surely as one inside its body.
//!
//! # The expansion is counted, never walked
//!
//! The expansion size is the node count of the term with every share's leg
//! inlined at each of its occurrences: the part of the unshared machines' walk
//! that sharing changes. A graft is one node over its children, an opaque node
//! counts once as the leaf it is to the overlay, and a share and an occurrence
//! stand for nothing of their own. The walk measures each leg once, keeps its
//! size on a stack of the legs in scope, and reads it at every occurrence.
//! Validation refuses a node reached twice, so the walk enters each node once
//! and costs the reachable overlay's size, never its expansion.
//!
//! # Overflow is a refusal
//!
//! Every quantity is a 64-bit counter and every addition is checked. A chain
//! that doubles its expansion per link passes the counter at its sixty-fourth
//! link, and the measure answers [`MeasureFault::Overflow`] naming the quantity
//! and the node where the sum passed it. A wrapped size would be wrong, and a
//! saturated one would report a cost the unshared pipeline cannot pay as if it
//! could.
//!
//! # Sharing measure
//!
//! `SharingMeasure::of` validates an overlay root, then walks it once in
//! post-order on a heap task stack and reports five quantities, each its own
//! counter type: `ShareCount`, the share nodes the root reaches;
//! `OccurrenceCount`, their arities summed; `ShareDepth`, the most shares on
//! one path down from the root, through legs and bodies alike; `NodeCount`, the
//! nodes the root reaches; and `ExpansionSize`, the node count of the term the
//! root stands for with every share's leg inlined at each of its occurrences,
//! where a graft is one node over its children, an opaque node is one node, and
//! a share and an occurrence are nothing of their own. The expansion is the
//! part of the unshared machines' walk that sharing changes: what evaluation
//! walks when it takes each occurrence of an erased leg's id as a copy. The
//! quantities are He's strong-normalisation measure for sharing reductions,
//! read over the overlay. The duplication walk prices the copying stance by
//! them before it mints, since that stance's output is the root's whole
//! expansion.
//!
//! The walk measures each leg once, keeps its measure on a stack of the legs in
//! scope, and reads it at every occurrence, so it enters each node once and
//! costs the reachable overlay, never its expansion: validation's refusal of a
//! node reached twice is what makes one visit per node enough. A chain of
//! sixty-three shares whose expansion doubles per link holds 253 nodes and
//! measures exactly `u64::MAX`. Every addition is checked, and a sum past its
//! 64-bit counter is refused as `MeasureFault::Overflow`, naming the
//! `MeasuredQuantity` and the node where the sum passed it, so the same chain
//! one link longer is refused at that link's pair. A validation refusal arrives
//! unchanged as `MeasureFault::Refused`, before anything is counted. The
//! measure is a function of the structure its root reaches: no id, other root
//! or later parent changes it.
//!
//! Alternatives: index arithmetic over one arena minted child before parent,
//! which the overlay's four family vectors, with no order across them, cannot
//! support; a walk over the expansion, which costs what it measures on a
//! doubling chain; a saturating counter, which reports a cost the unshared
//! pipeline cannot pay as if it could; and a weakening count beside the shares,
//! which has nothing to count, since validation refuses a share of arity zero
//! and a weakening is therefore an absent share. Reversal: the overlay admits
//! shares of arity zero, and the weakening count returns beside the five.

use alloc::vec::Vec;

use anodized::spec;

use crate::overlay::Overlay;
use crate::overlay::OverlayId;
use crate::overlay::OverlayRefusal;
use crate::overlay::Shape;
use crate::overlay::ShareArity;

/// How many shares a measured root holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ShareCount(u64);

impl From<ShareCount> for u64
{
    /// How many shares `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ShareCount) -> Self
    {
        count.0
    }
}

/// How many occurrences a measured root's shares stand for: their arities
/// summed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OccurrenceCount(u64);

impl From<OccurrenceCount> for u64
{
    /// How many occurrences `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: OccurrenceCount) -> Self
    {
        count.0
    }
}

/// The longest chain of nested shares: the most shares on any one path down
/// from a measured root, through legs and bodies alike.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ShareDepth(u64);

impl From<ShareDepth> for u64
{
    /// How many shares the chain holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: ShareDepth) -> Self
    {
        depth.0
    }
}

/// How many overlay nodes a measured root reaches, of every kind and family.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeCount(u64);

impl From<NodeCount> for u64
{
    /// How many nodes `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: NodeCount) -> Self
    {
        count.0
    }
}

/// The size of the unshared term a measured root stands for: its node count
/// with every share's leg inlined at each of its occurrences, an opaque node
/// counting once.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExpansionSize(u64);

impl From<ExpansionSize> for u64
{
    /// How many nodes the unshared term holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(size: ExpansionSize) -> Self
    {
        size.0
    }
}

/// The quantity whose counter an addition passed.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MeasuredQuantity
{
    /// The [`ShareCount`].
    Shares,
    /// The [`OccurrenceCount`].
    Occurrences,
    /// The [`ShareDepth`].
    Depth,
    /// The [`NodeCount`].
    Nodes,
    /// The [`ExpansionSize`].
    Expansion,
}

/// Why a root could not be measured.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MeasureFault
{
    /// Validation refused the overlay, in its own vocabulary, before anything
    /// was counted. Carried rather than translated, so the refusal arrives
    /// under the name of the condition.
    Refused(OverlayRefusal),
    /// An addition passed a quantity's 64-bit counter.
    Overflow
    {
        /// The quantity whose counter the sum passed.
        quantity: MeasuredQuantity,
        /// The node at which the sum passed it.
        node: OverlayId,
    },
    /// The walk's own stacks disagreed with the validated overlay. Unreachable
    /// while every leg is in scope beneath the body that reads it and every
    /// graft is summed over the results its own children left; kept so the
    /// measure fails closed rather than answering.
    MachineInvariant,
}

/// He's measure of one validated overlay root.
///
/// # Specification
/// - provides: the five quantities [`SharingMeasure::of`] computes, read
///   through one accessor each; the fields are private, so a measure exists
///   only as the measure of some root.
/// - executable: none — a data `maintains` predicate needs anodized's `logic`
///   feature, which the workspace does not enable. [`Self::of`] enforces the
///   four laws; the root and overlay needed for provenance are not retained in
///   this value.
///
/// # Adequacy
/// - hypothesis: L1/L3 — values returned for validated roots are observed by
///   their five counters. Swapping fields or counting a shared leg twice
///   changes exact tuples or the independently counted erased tree.
/// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
/// - witness: `measure::measure::the_expansion_size_is_what_the_unshared_walk_visits`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SharingMeasure
{
    /// The share nodes the root reaches.
    shares: ShareCount,
    /// Their arities summed.
    occurrences: OccurrenceCount,
    /// The most shares on one path down from the root.
    depth: ShareDepth,
    /// The nodes the root reaches.
    nodes: NodeCount,
    /// The node count of the unshared term the root stands for.
    expansion: ExpansionSize,
}

impl SharingMeasure
{
    /// Measure the overlay reachable from `root`.
    ///
    /// # Specification
    /// - requires: nothing — a root from another overlay, and a root the
    ///   overlay does not validate from, are admissible input.
    /// - ensures: on success, over the nodes reachable from `root`: the share
    ///   count is the number of share nodes; the occurrence count is their
    ///   arities summed; the share depth is the most share nodes on any one
    ///   path down from `root`, through legs and bodies alike; the node count
    ///   is the number of nodes; and the expansion size is the node count of
    ///   the term `root` stands for with every share's leg inlined at each of
    ///   its occurrences, where a graft is one node over its children, an
    ///   opaque node is one node, and a share and an occurrence are nothing of
    ///   their own. The result is a function of that reachable structure alone:
    ///   neither the ids it is minted under nor any other node of the overlay
    ///   changes it. The quantities obey four laws: occurrences at least
    ///   shares, depth at most shares, nodes above shares and occurrences
    ///   together, and an expansion of at least one.
    /// - provides: the sharing reductions' termination evidence and the
    ///   allocation a duplication stance is priced by.
    /// - fails: [`MeasureFault::Refused`] with the validation refusal before
    ///   anything is counted; [`MeasureFault::Overflow`] naming the quantity
    ///   and the node at the first checked addition, in post-order, whose sum
    ///   passes its 64-bit counter; [`MeasureFault::MachineInvariant`] when the
    ///   walk's own stacks break.
    /// - panics: none.
    /// - intension: validation, then one post-order walk with one task per node
    ///   and two more per share, all on the heap. Each node is entered once and
    ///   each leg's size is read from a stack at every occurrence, so the walk
    ///   costs the reachable overlay's size, never its expansion.
    ///
    /// # Errors
    /// - [`MeasureFault::Refused`] — the overlay does not validate from `root`.
    /// - [`MeasureFault::Overflow`] — a sum passed a quantity's counter.
    /// - [`MeasureFault::MachineInvariant`] — the walk's own stacks broke.
    ///
    /// # Adequacy
    /// - hypothesis: L1 for the expansion — over every closed overlay of a
    ///   generated class, the erasure and a test-local walk of the erased term
    ///   as a tree decide it independently of the measure, as they do over the
    ///   crate's deep cases. L3 for the other quantities and the guards — a
    ///   share whose leg is inlined at many occurrences, nested shares to a
    ///   known depth through bodies and through legs with two sibling chains in
    ///   both orders, an occurrence-free root of a three-child former, a leg
    ///   reading the shares outside its own, occurrences at two distances whose
    ///   legs differ in size, a doubling chain at the counter's last fitting
    ///   link and one link past it asserted by quantity and node, one refusal
    ///   per validation rule asserted unchanged with one that precedes an
    ///   overflow, and one root measured equal across overlays, ids and
    ///   parents. The walk's depth is separated from the host stack by chains
    ///   measured inside a small stack. The counters other than the expansion
    ///   need more nodes than four families of 32-bit ids hold to overflow, so
    ///   their ceilings stay prose. Swapping counters, counting a shared leg
    ///   twice or translating a validation refusal changes an observation.
    /// - witness: `measure::tests::a_share_with_many_occurrences_inlines_its_leg_at_each`
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
    /// - witness: `measure::tests::an_occurrence_free_root_measures_its_own_size`
    /// - witness: `measure::tests::a_leg_reads_the_shares_outside_its_own`
    /// - witness: `measure::tests::an_occurrence_reads_the_leg_its_distance_names`
    /// - witness: `measure::tests::a_doubling_chain_measures_in_its_own_size`
    /// - witness: `measure::tests::an_expansion_past_the_counter_is_refused_at_its_node`
    /// - witness: `measure::tests::an_invalid_overlay_is_refused_by_name_before_measuring`
    /// - witness: `measure::tests::the_measure_is_a_function_of_what_the_root_reaches`
    /// - witness: `measure::measure::the_expansion_size_is_what_the_unshared_walk_visits`
    /// - witness: `measure::measure::a_deep_overlay_is_measured_inside_a_small_stack`
    /// - witness:
    ///   `deep_evaluation::deep_evaluation::the_deep_evaluation_cases_measure_as_their_erasure_inside_a_small_stack`
    /// - witness:
    ///   `deep_readback::deep_readback::the_deep_readback_cases_measure_as_their_erasure_inside_a_small_stack`
    /// - witness:
    ///   `teardown::teardown::the_teardown_overlays_are_measured_inside_a_small_stack`
    #[inline]
    #[spec(
        ensures: |ret| match ret {
            Ok(measured) => measured.occurrences.0 >= measured.shares.0
            && measured.depth.0 <= measured.shares.0
            && measured.nodes.0.checked_sub(measured.shares.0)
                .and_then(|rest| rest.checked_sub(measured.occurrences.0))
                .is_some_and(|rest| rest > 0_u64)
            && measured.expansion.0 >= 1_u64,
            Err(MeasureFault::Refused(refusal)) => overlay.validate(root) == Err(refusal),
            Err(MeasureFault::Overflow { node, .. }) => overlay.shape(node).is_ok(),
            Err(MeasureFault::MachineInvariant) => true,
        }
    )]
    pub fn of(
        overlay: &Overlay,
        root: OverlayId,
    ) -> Result<Self, MeasureFault>
    {
        overlay.validate(root).map_err(MeasureFault::Refused)?;
        let mut measuring = Measuring {
            overlay,
            visits: Vec::from([Visit::Enter(root)]),
            legs: Vec::new(),
            results: Vec::new(),
            shares: ShareCount::default(),
            occurrences: OccurrenceCount::default(),
            nodes: NodeCount::default(),
        };
        let measured = measuring.run()?;
        Ok(Self {
            shares: measuring.shares,
            occurrences: measuring.occurrences,
            depth: measured.depth,
            nodes: measuring.nodes,
            expansion: measured.expansion,
        })
    }

    /// The share count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shares(&self) -> ShareCount
    {
        self.shares
    }

    /// The occurrence count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn occurrences(&self) -> OccurrenceCount
    {
        self.occurrences
    }

    /// The share depth.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn depth(&self) -> ShareDepth
    {
        self.depth
    }

    /// The node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn nodes(&self) -> NodeCount
    {
        self.nodes
    }

    /// The expansion size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn expansion(&self) -> ExpansionSize
    {
        self.expansion
    }
}

impl ShareCount
{
    /// The count with `share` added.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count one higher, when it fits.
    /// - provides: the checked step the walk counts every share node with.
    /// - fails: [`MeasureFault::Overflow`] of [`MeasuredQuantity::Shares`] at
    ///   `share` when the count is already at the counter's ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — the count would pass its counter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the step is separated by every measured share count
    ///   asserted exactly; the ceiling needs more share nodes than an overlay
    ///   holds and stays prose. Changing the increment or the returned counter
    ///   field changes the exact public totals; the predicate states the
    ///   checked arithmetic.
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
    #[spec(
        ensures: |ret| ret == self.0.checked_add(1_u64).map(Self).ok_or(MeasureFault::Overflow { quantity: MeasuredQuantity::Shares, node: share })
    )]
    fn with(
        self,
        share: OverlayId,
    ) -> Result<Self, MeasureFault>
    {
        self.0
            .checked_add(1_u64)
            .map(Self)
            .ok_or(MeasureFault::Overflow {
                quantity: MeasuredQuantity::Shares,
                node: share,
            })
    }
}

impl OccurrenceCount
{
    /// The count with the occurrences of `share`, of `arity`, added.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count raised by `arity`, when it fits.
    /// - provides: the checked sum the walk totals the arities with.
    /// - fails: [`MeasureFault::Overflow`] of [`MeasuredQuantity::Occurrences`]
    ///   at `share` when the sum passes the counter.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — the sum would pass its counter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sum is separated from a count of shares by a
    ///   share of arity one thousand and from a count of occurrence nodes by
    ///   the generated class; the ceiling needs more occurrence nodes than an
    ///   overlay holds and stays prose. Changing the increment or the returned
    ///   counter field changes the exact public totals; the predicate states
    ///   the checked arithmetic.
    /// - witness: `measure::tests::a_share_with_many_occurrences_inlines_its_leg_at_each`
    /// - witness: `measure::measure::the_expansion_size_is_what_the_unshared_walk_visits`
    #[spec(
        ensures: |ret| ret == self.0.checked_add(u64::from(u32::from(arity))).map(Self).ok_or(MeasureFault::Overflow { quantity: MeasuredQuantity::Occurrences, node: share })
    )]
    fn with(
        self,
        arity: ShareArity,
        share: OverlayId,
    ) -> Result<Self, MeasureFault>
    {
        self.0
            .checked_add(u64::from(u32::from(arity)))
            .map(Self)
            .ok_or(MeasureFault::Overflow {
                quantity: MeasuredQuantity::Occurrences,
                node: share,
            })
    }
}

impl ShareDepth
{
    /// The depth of `share` over the deeper of its leg and its body.
    ///
    /// # Specification
    /// - requires: `self` is the larger of the depths of the leg and the body
    ///   of `share`.
    /// - ensures: that depth one higher, when it fits.
    /// - provides: the checked step that makes a share one link of every chain
    ///   through it.
    /// - fails: [`MeasureFault::Overflow`] of [`MeasuredQuantity::Depth`] at
    ///   `share` when the depth is already at the counter's ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — the depth would pass its counter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the step is separated by chains nested through bodies
    ///   and through legs and by sibling chains in both orders, each asserted
    ///   exactly; the ceiling needs more share nodes than an overlay holds and
    ///   stays prose. Changing the increment or the returned counter field
    ///   changes the exact public totals; the predicate states the checked
    ///   arithmetic.
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
    #[spec(
        ensures: |ret| ret == self.0.checked_add(1_u64).map(Self).ok_or(MeasureFault::Overflow { quantity: MeasuredQuantity::Depth, node: share })
    )]
    fn above(
        self,
        share: OverlayId,
    ) -> Result<Self, MeasureFault>
    {
        self.0
            .checked_add(1_u64)
            .map(Self)
            .ok_or(MeasureFault::Overflow {
                quantity: MeasuredQuantity::Depth,
                node: share,
            })
    }
}

impl NodeCount
{
    /// The count with `node` added.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count one higher, when it fits.
    /// - provides: the checked step the walk counts every node it enters with.
    /// - fails: [`MeasureFault::Overflow`] of [`MeasuredQuantity::Nodes`] at
    ///   `node` when the count is already at the counter's ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — the count would pass its counter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the step is separated by every measured node count
    ///   asserted exactly, among them roots whose expansion lies below and
    ///   above their node count; the ceiling needs more nodes than an overlay
    ///   holds and stays prose. Changing the increment or the returned counter
    ///   field changes the exact public totals; the predicate states the
    ///   checked arithmetic.
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
    #[spec(
        ensures: |ret| ret == self.0.checked_add(1_u64).map(Self).ok_or(MeasureFault::Overflow { quantity: MeasuredQuantity::Nodes, node })
    )]
    fn with(
        self,
        node: OverlayId,
    ) -> Result<Self, MeasureFault>
    {
        self.0
            .checked_add(1_u64)
            .map(Self)
            .ok_or(MeasureFault::Overflow {
                quantity: MeasuredQuantity::Nodes,
                node,
            })
    }
}

impl ExpansionSize
{
    /// What one graft or one opaque node contributes on its own.
    const ONE: Self = Self(1_u64);

    /// The size with `child`'s added, at the graft `graft`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the two sizes summed, when the sum fits.
    /// - provides: the one addition expansion sizes grow by, so an expansion
    ///   past the counter is refused at the graft whose sum passes it.
    /// - fails: [`MeasureFault::Overflow`] of [`MeasuredQuantity::Expansion`]
    ///   at `graft` when the sum passes the counter.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — the sum would pass its counter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the guard is separated by the boundary pair of a
    ///   doubling chain whose expansion reaches exactly the counter's ceiling
    ///   and the same chain one link longer, refused at that link's graft; the
    ///   ordinary sum is separated by every measured expansion asserted
    ///   exactly. Changing the increment or the returned counter field changes
    ///   the exact public totals; the predicate states the checked arithmetic.
    /// - witness: `measure::tests::a_doubling_chain_measures_in_its_own_size`
    /// - witness: `measure::tests::an_expansion_past_the_counter_is_refused_at_its_node`
    #[spec(
        ensures: |ret| ret == self.0.checked_add(child.0).map(Self).ok_or(MeasureFault::Overflow { quantity: MeasuredQuantity::Expansion, node: graft })
    )]
    fn with(
        self,
        child: Self,
        graft: OverlayId,
    ) -> Result<Self, MeasureFault>
    {
        self.0
            .checked_add(child.0)
            .map(Self)
            .ok_or(MeasureFault::Overflow {
                quantity: MeasuredQuantity::Expansion,
                node: graft,
            })
    }
}

/// What the walk knows of one node once everything beneath it is measured.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Measured
{
    /// The size of the unshared term the node stands for.
    expansion: ExpansionSize,
    /// The most shares on one path down from the node.
    depth: ShareDepth,
}

impl Measured
{
    /// A graft over no children, or an opaque node.
    const LEAF: Self = Self {
        expansion: ExpansionSize::ONE,
        depth: ShareDepth(0_u64),
    };
}

/// The height of the result stack when a graft was entered: its children's
/// results lie above it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Height(usize);

/// One pending step of the measuring walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Count one node, and measure it or queue what measuring it takes.
    Enter(OverlayId),
    /// Move a share's measured leg from the results into scope, before the
    /// share's body.
    Bind,
    /// Measure a share from its leg in scope and its measured body.
    Unbind
    {
        /// The share.
        share: OverlayId,
    },
    /// Measure a graft from the results its children left above `base`.
    Assemble
    {
        /// The graft.
        graft: OverlayId,
        /// The result stack's height when the graft was entered.
        base: Height,
    },
}

/// The measuring walk: its task stack, the measured legs of the shares around
/// the current node innermost last, the measured nodes awaiting their parent,
/// and the three counts that need no parent.
struct Measuring<'run>
{
    /// The overlay measured.
    overlay: &'run Overlay,
    /// The pending steps.
    visits: Vec<Visit>,
    /// The measured legs of the shares whose bodies enclose the current node.
    legs: Vec<Measured>,
    /// The measured nodes awaiting their parent.
    results: Vec<Measured>,
    /// The share nodes entered so far.
    shares: ShareCount,
    /// Their arities summed.
    occurrences: OccurrenceCount,
    /// The nodes entered so far.
    nodes: NodeCount,
}

impl Measuring<'_>
{
    /// Drive the walk until its steps run out.
    ///
    /// # Specification
    /// - requires: the overlay validates from the root the steps hold.
    /// - ensures: the measured root, with no leg left in scope and no other
    ///   result left over.
    /// - provides: the heap-only drive; depth costs steps, never host frames.
    /// - fails: [`MeasureFault::Overflow`] from the first addition that passes
    ///   its counter, and [`MeasureFault::MachineInvariant`] when a stack
    ///   breaks.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — a sum passed a quantity's counter.
    /// - [`MeasureFault::MachineInvariant`] — a stack broke.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the drive's depth is separated from the host stack by
    ///   chains nested through bodies, whose task, leg and result stacks all
    ///   grow with the chain, measured inside a small stack; its result is
    ///   separated by every measure the suites assert. Leaving a result or leg
    ///   behind violates the completion predicate; dropping a visit changes the
    ///   independently observed root measure.
    /// - witness: `measure::measure::a_deep_overlay_is_measured_inside_a_small_stack`
    /// - witness: `measure::tests::a_measure_that_ends_with_a_leg_still_in_scope_is_refused`
    #[spec(
        ensures: |ret| ret.map_or(true, |measured| self.visits.is_empty() && self.legs.is_empty() && self.results.is_empty() && measured.expansion.0 >= 1_u64 && measured.depth.0 <= self.shares.0)
    )]
    fn run(&mut self) -> Result<Measured, MeasureFault>
    {
        while let Some(visit) = self.visits.pop() {
            match visit {
                Visit::Enter(node) => {
                    self.enter(node)?;
                },
                Visit::Bind => {
                    let Some(leg) = self.results.pop()
                    else {
                        return Err(MeasureFault::MachineInvariant);
                    };
                    self.legs.push(leg);
                },
                Visit::Unbind { share } => {
                    self.unbind(share)?;
                },
                Visit::Assemble { graft, base } => {
                    self.assemble(graft, base)?;
                },
            }
        }
        let Some(measured) = self.results.pop()
        else {
            return Err(MeasureFault::MachineInvariant);
        };
        if self.results.is_empty() && self.legs.is_empty() {
            Ok(measured)
        }
        else {
            Err(MeasureFault::MachineInvariant)
        }
    }

    /// Count one node, and measure it or queue what measuring it takes.
    ///
    /// # Specification
    /// - requires: `node` is reachable from a validated root, and the legs in
    ///   scope are those of the shares whose bodies enclose it.
    /// - ensures: the node is counted; an opaque node pushes one node of
    ///   expansion and an occurrence the expansion of the leg its distance
    ///   names, both at depth zero; a share is counted with its arity and
    ///   queues its leg, the bind, its body and its close, in that order; a
    ///   graft queues its children left to right and then its own assembly over
    ///   the result stack's present height.
    /// - provides: the post-order every quantity is computed in.
    /// - fails: [`MeasureFault::Refused`] for a node that does not resolve,
    ///   [`MeasureFault::Overflow`] from a count, and
    ///   [`MeasureFault::MachineInvariant`] for an occurrence no leg in scope
    ///   answers.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Refused`] — `node` does not resolve.
    /// - [`MeasureFault::Overflow`] — a count passed its counter.
    /// - [`MeasureFault::MachineInvariant`] — no leg in scope answers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four node kinds are separated by an
    ///   occurrence-free root and by shares whose occurrences read legs of
    ///   different sizes at two distances, including from inside another
    ///   share's leg; the queue order is separated by the same cases, since a
    ///   leg bound after its body would be read by the wrong occurrences.
    ///   Counting a node twice, entering a body before binding its leg or
    ///   reversing the children changes a predicate or an exact result.
    /// - witness: `measure::tests::an_occurrence_free_root_measures_its_own_size`
    /// - witness: `measure::tests::a_leg_reads_the_shares_outside_its_own`
    /// - witness: `measure::tests::an_occurrence_reads_the_leg_its_distance_names`
    #[spec(
        captures: [nodes = self.nodes, shares = self.shares, occurrences = self.occurrences, results = self.results.len(), visits = self.visits.len()],
        ensures: |ret| ret.is_err() || (nodes.0.checked_add(1_u64) == Some(self.nodes.0) && self.overlay.shape(node).is_ok_and(|shape| match shape {
            Shape::Opaque(_) => self.shares == shares && self.occurrences == occurrences && self.visits.len() == visits && self.results.len() == results.saturating_add(1) && self.results.last() == Some(&Measured::LEAF),
            Shape::Bound(bound) => self.shares == shares && self.occurrences == occurrences && self.visits.len() == visits && self.results.len() == results.saturating_add(1) && usize::try_from(u32::from(bound.distance)).ok().and_then(|distance| self.legs.len().checked_sub(distance.saturating_add(1))).and_then(|offset| self.legs.get(offset)).is_some_and(|leg| self.results.last() == Some(&Measured { expansion: leg.expansion, depth: ShareDepth::default() })),
            Shape::Shared(sharing) => shares.0.checked_add(1_u64) == Some(self.shares.0) && occurrences.0.checked_add(u64::from(u32::from(sharing.arity))) == Some(self.occurrences.0) && self.results.len() == results && self.visits.get(visits..) == Some(&[Visit::Unbind { share: node }, Visit::Enter(sharing.body), Visit::Bind, Visit::Enter(sharing.leg)]),
            Shape::Grafted(children) => {
                self.shares == shares && self.occurrences == occurrences && self.results.len() == results && self.visits.get(visits) == Some(&Visit::Assemble { graft: node, base: Height(results) }) && bool::from(crate::spec::queued_since(&self.visits, gandr_theory_spec_combinators::Mark::from(visits.saturating_add(1)), children, Visit::Enter))
            },
        }))
    )]
    fn enter(
        &mut self,
        node: OverlayId,
    ) -> Result<(), MeasureFault>
    {
        let shape = self.overlay.shape(node).map_err(MeasureFault::Refused)?;
        self.nodes = self.nodes.with(node)?;
        match shape {
            Shape::Opaque(_) => {
                self.results.push(Measured::LEAF);
            },
            Shape::Bound(bound) => {
                let distance = usize::try_from(u32::from(bound.distance)).unwrap_or(usize::MAX);
                let Some(&leg) = self
                    .legs
                    .len()
                    .checked_sub(1)
                    .and_then(|innermost| innermost.checked_sub(distance))
                    .and_then(|named| self.legs.get(named))
                else {
                    return Err(MeasureFault::MachineInvariant);
                };
                self.results.push(Measured {
                    expansion: leg.expansion,
                    depth: ShareDepth::default(),
                });
            },
            Shape::Shared(sharing) => {
                self.shares = self.shares.with(node)?;
                self.occurrences = self.occurrences.with(sharing.arity, node)?;
                self.visits.push(Visit::Unbind { share: node });
                self.visits.push(Visit::Enter(sharing.body));
                self.visits.push(Visit::Bind);
                self.visits.push(Visit::Enter(sharing.leg));
            },
            Shape::Grafted(children) => {
                self.visits.push(Visit::Assemble {
                    graft: node,
                    base: Height(self.results.len()),
                });
                children.push_reversed(&mut self.visits, Visit::Enter);
            },
        }
        Ok(())
    }

    /// Measure a share from its leg in scope and its measured body.
    ///
    /// # Specification
    /// - requires: the share's leg is the innermost in scope and its body's
    ///   measure is the topmost result.
    /// - ensures: both are popped, and the share's measure pushed: its body's
    ///   expansion, since the share and its occurrences stand for nothing of
    ///   their own and every occurrence already read the leg, and a depth one
    ///   above the deeper of the leg and the body.
    /// - provides: the one place a share closes, so a leg leaves scope exactly
    ///   when its body is measured.
    /// - fails: [`MeasureFault::Overflow`] from the depth, and
    ///   [`MeasureFault::MachineInvariant`] when the leg or the body is
    ///   missing.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — the depth passed its counter.
    /// - [`MeasureFault::MachineInvariant`] — the leg or the body is missing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the expansion is separated from one that counted the
    ///   share or its leg again by every share measured exactly, and the depth
    ///   from one that read only the leg or only the body by chains nested
    ///   through each. Adding the leg again, summing depths or retaining a
    ///   scope frame changes the measured result or the stack predicate.
    /// - witness: `measure::tests::a_share_with_many_occurrences_inlines_its_leg_at_each`
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
    #[spec(
        captures: [results = self.results.len(), legs = self.legs.len(), body = self.results.last().copied(), leg = self.legs.last().copied()],
        ensures: |ret| body.zip(leg).map_or_else(
            || ret == Err(MeasureFault::MachineInvariant) && self.results.len() == results.saturating_sub(1) && self.legs.len() == legs.saturating_sub(1),
            |(body, leg)| {
                let depth = body.depth.0.max(leg.depth.0).checked_add(1_u64);
                self.legs.len() == legs.saturating_sub(1) && depth.map_or_else(
                    || ret == Err(MeasureFault::Overflow { quantity: MeasuredQuantity::Depth, node: share }) && self.results.len() == results.saturating_sub(1),
                    |depth| ret == Ok(()) && self.results.len() == results && self.results.last() == Some(&Measured { expansion: body.expansion, depth: ShareDepth(depth) }))
            })
    )]
    fn unbind(
        &mut self,
        share: OverlayId,
    ) -> Result<(), MeasureFault>
    {
        let (Some(body), Some(leg)) = (self.results.pop(), self.legs.pop())
        else {
            return Err(MeasureFault::MachineInvariant);
        };
        let depth = body.depth.max(leg.depth).above(share)?;
        self.results.push(Measured {
            expansion: body.expansion,
            depth,
        });
        Ok(())
    }

    /// Measure a graft from the results its children left above `base`.
    ///
    /// # Specification
    /// - requires: the results above `base` are the graft's children's, and
    ///   nothing else.
    /// - ensures: those results are popped, and the graft's measure pushed: one
    ///   node of expansion more than its children's together, at the deepest of
    ///   their depths.
    /// - provides: the one place a graft is summed, over any number of
    ///   children.
    /// - fails: [`MeasureFault::Overflow`] of the expansion at `graft`, and
    ///   [`MeasureFault::MachineInvariant`] when the result stack sits below
    ///   `base`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeasureFault::Overflow`] — the expansion passed its counter.
    /// - [`MeasureFault::MachineInvariant`] — the stack sits below `base`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sum and the depth are separated by grafts of
    ///   none, one, two and three children measured exactly and by sibling
    ///   chains of different depths in both orders; the overflow by the
    ///   doubling chain's boundary pair. Omitting the graft node, summing child
    ///   depths or dropping a child changes an exact result and the
    ///   reconstruction predicate.
    /// - witness: `measure::tests::an_occurrence_free_root_measures_its_own_size`
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
    /// - witness: `measure::tests::an_expansion_past_the_counter_is_refused_at_its_node`
    #[spec(
        captures: [count = self.results.len(), children = [self.results.get(base.0).copied(), self.results.get(base.0.saturating_add(1)).copied(), self.results.get(base.0.saturating_add(2)).copied()]],
        ensures: |ret| {
            if count < base.0 {
                ret == Err(MeasureFault::MachineInvariant) && self.results.len() == count
            } else {
                let expected = children.into_iter().flatten().try_fold(Measured::LEAF, |sum, child| sum.expansion.0.checked_add(child.expansion.0).map(|expansion| Measured { expansion: ExpansionSize(expansion), depth: sum.depth.max(child.depth) }));
                expected.map_or_else(
                    || ret == Err(MeasureFault::Overflow { quantity: MeasuredQuantity::Expansion, node: graft }) && self.results.len() == base.0,
                    |expected| ret == Ok(()) && self.results.len() == base.0.saturating_add(1) && self.results.last() == Some(&expected))
            }
        }
    )]
    fn assemble(
        &mut self,
        graft: OverlayId,
        base: Height,
    ) -> Result<(), MeasureFault>
    {
        if self.results.len() < base.0 {
            return Err(MeasureFault::MachineInvariant);
        }
        let mut measured = Measured::LEAF;
        for child in self.results.drain(base.0 ..) {
            measured.expansion = measured.expansion.with(child.expansion, graft)?;
            measured.depth = measured.depth.max(child.depth);
        }
        self.results.push(measured);
        Ok(())
    }
}

#[cfg(test)]
mod tests;
