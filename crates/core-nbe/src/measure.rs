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
    ///   their ceilings stay prose.
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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |measured| {
        measured.occurrences.0 >= measured.shares.0
            && measured.depth.0 <= measured.shares.0
            && measured.nodes.0.checked_sub(measured.shares.0)
                .and_then(|rest| rest.checked_sub(measured.occurrences.0))
                .is_some_and(|rest| rest > 0_u64)
            && measured.expansion.0 >= 1_u64
    }))]
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
    ///   holds and stays prose.
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
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
    ///   overlay holds and stays prose.
    /// - witness: `measure::tests::a_share_with_many_occurrences_inlines_its_leg_at_each`
    /// - witness: `measure::measure::the_expansion_size_is_what_the_unshared_walk_visits`
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
    ///   stays prose.
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
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
    ///   holds and stays prose.
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
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
    ///   exactly.
    /// - witness: `measure::tests::a_doubling_chain_measures_in_its_own_size`
    /// - witness: `measure::tests::an_expansion_past_the_counter_is_refused_at_its_node`
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
    ///   separated by every measure the suites assert.
    /// - witness: `measure::measure::a_deep_overlay_is_measured_inside_a_small_stack`
    fn run(&mut self) -> Result<Measured, MeasureFault>
    {
        while let Some(visit) = self.visits.pop() {
            match visit {
                | Visit::Enter(node) => {
                    self.enter(node)?;
                },
                | Visit::Bind => {
                    let Some(leg) = self.results.pop()
                    else {
                        return Err(MeasureFault::MachineInvariant);
                    };
                    self.legs.push(leg);
                },
                | Visit::Unbind { share } => {
                    self.unbind(share)?;
                },
                | Visit::Assemble { graft, base } => {
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
    /// - witness: `measure::tests::an_occurrence_free_root_measures_its_own_size`
    /// - witness: `measure::tests::a_leg_reads_the_shares_outside_its_own`
    /// - witness: `measure::tests::an_occurrence_reads_the_leg_its_distance_names`
    fn enter(
        &mut self,
        node: OverlayId,
    ) -> Result<(), MeasureFault>
    {
        let shape = self.overlay.shape(node).map_err(MeasureFault::Refused)?;
        self.nodes = self.nodes.with(node)?;
        match shape {
            | Shape::Opaque(_) => {
                self.results.push(Measured::LEAF);
            },
            | Shape::Bound(bound) => {
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
            | Shape::Shared(sharing) => {
                self.shares = self.shares.with(node)?;
                self.occurrences = self.occurrences.with(sharing.arity, node)?;
                self.visits.push(Visit::Unbind { share: node });
                self.visits.push(Visit::Enter(sharing.body));
                self.visits.push(Visit::Bind);
                self.visits.push(Visit::Enter(sharing.leg));
            },
            | Shape::Grafted(children) => {
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
    ///   through each.
    /// - witness: `measure::tests::a_share_with_many_occurrences_inlines_its_leg_at_each`
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
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
    ///   doubling chain's boundary pair.
    /// - witness: `measure::tests::an_occurrence_free_root_measures_its_own_size`
    /// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
    /// - witness: `measure::tests::an_expansion_past_the_counter_is_refused_at_its_node`
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
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_kernel_term::Side;

    use super::ExpansionSize;
    use super::MeasureFault;
    use super::MeasuredQuantity;
    use super::NodeCount;
    use super::OccurrenceCount;
    use super::ShareCount;
    use super::ShareDepth;
    use super::SharingMeasure;
    use crate::overlay::Bound;
    use crate::overlay::CompGraft;
    use crate::overlay::CompNode;
    use crate::overlay::Overlay;
    use crate::overlay::OverlayId;
    use crate::overlay::OverlayRefusal;
    use crate::overlay::OverlayValueId;
    use crate::overlay::ShareArity;
    use crate::overlay::ShareDistance;
    use crate::overlay::SharePosition;
    use crate::overlay::Sharing;
    use crate::overlay::ValueGraft;
    use crate::overlay::ValueNode;

    /// How many links a test chain holds.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Links(u32);

    /// The occurrences the many-occurrence share stands for.
    const OCCURRENCES: u32 = 1_000;

    /// The longest doubling chain whose expansion fits a 64-bit counter:
    /// link `k` stands for `2^(k + 1) - 1` nodes.
    const FITTING_LINKS: Links = Links(63);

    /// A grafted unit value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh value leaf.
    /// - provides: the legs and leaves the cases share.
    /// - panics: when the mint is refused, which only the id ceiling causes.
    fn unit(overlay: &mut Overlay) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("a leaf names no child")
    }

    /// A value occurrence `distance` shares out, at `position`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh value occurrence.
    /// - provides: the occurrences the cases place in preorder.
    /// - panics: when the mint is refused, which only the id ceiling causes.
    fn occurrence(
        overlay: &mut Overlay,
        distance: ShareDistance,
        position: SharePosition,
    ) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Bound(Bound { distance, position }))
            .expect("an occurrence names no child")
    }

    /// A value pair of two nodes.
    ///
    /// # Specification
    /// - requires: both nodes resolve in `overlay`.
    /// - ensures: a fresh grafted pair.
    /// - provides: the two-child graft the cases build with.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn pair(
        overlay: &mut Overlay,
        first: OverlayValueId,
        second: OverlayValueId,
    ) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Pair(first, second)))
            .expect("both components resolve")
    }

    /// A value share of the value `leg` among `arity` occurrences in `body`.
    ///
    /// # Specification
    /// - requires: `leg` and `body` resolve in `overlay`.
    /// - ensures: a fresh value share.
    /// - provides: the shares the cases build.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn share(
        overlay: &mut Overlay,
        arity: ShareArity,
        leg: OverlayValueId,
        body: OverlayValueId,
    ) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Shared(Sharing {
                arity,
                leg: OverlayId::Value(leg),
                body,
            }))
            .expect("the leg and the body resolve")
    }

    /// The occurrence at distance zero and position zero: the only occurrence
    /// of a share of arity one directly around it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh value occurrence.
    /// - provides: the one occurrence each chain link holds.
    /// - panics: when the mint is refused, which only the id ceiling causes.
    fn only_occurrence(overlay: &mut Overlay) -> OverlayValueId
    {
        occurrence(
            overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        )
    }

    /// `⟨x₀, link⟩[x₀ ← ⟨⟩]` per link over a unit: shares nested through
    /// their bodies.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the outermost of `links` links, each a share of arity one
    ///   whose body pairs its occurrence with the link below.
    /// - provides: a chain whose share depth is its length, whose node count is
    ///   four per link and one, and whose expansion is two per link and one.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn body_chain(
        overlay: &mut Overlay,
        links: Links,
    ) -> OverlayValueId
    {
        let mut nested = unit(overlay);
        for _link in 0 .. links.0 {
            let leg = unit(overlay);
            let read = only_occurrence(overlay);
            let body = pair(overlay, read, nested);
            nested = share(overlay, ShareArity::from(1_u32), leg, body);
        }
        nested
    }

    /// `x₀[x₀ ← link]` per link over a unit: shares nested through their
    /// legs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the outermost of `links` links, each a share of arity one
    ///   whose leg is the link below and whose body is its occurrence.
    /// - provides: a chain whose share depth is its length, whose node count is
    ///   two per link and one, and whose expansion is the unit's alone.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn leg_chain(
        overlay: &mut Overlay,
        links: Links,
    ) -> OverlayValueId
    {
        let mut nested = unit(overlay);
        for _link in 0 .. links.0 {
            let read = only_occurrence(overlay);
            nested = share(overlay, ShareArity::from(1_u32), nested, read);
        }
        nested
    }

    /// `⟨x₀, x₁⟩[x₀ x₁ ← link]` per link over a unit: the chain whose
    /// expansion doubles per link.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the outermost of `links` links, each a share of arity two
    ///   whose leg is the link below and whose body pairs its two occurrences,
    ///   together with the outermost link's body.
    /// - provides: a chain of four nodes per link and one whose link `k` stands
    ///   for `2^(k + 1) - 1` nodes.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn doubling_chain(
        overlay: &mut Overlay,
        links: Links,
    ) -> (OverlayValueId, OverlayValueId)
    {
        let mut nested = unit(overlay);
        let mut body = nested;
        for _link in 0 .. links.0 {
            let left = occurrence(
                overlay,
                ShareDistance::from(0_u32),
                SharePosition::from(0_u32),
            );
            let right = occurrence(
                overlay,
                ShareDistance::from(0_u32),
                SharePosition::from(1_u32),
            );
            body = pair(overlay, left, right);
            nested = share(overlay, ShareArity::from(2_u32), nested, body);
        }
        (nested, body)
    }

    /// `⟨x₀, y₀[y₀ ← x₁]⟩[x₀ x₁ ← ⟨⟨⟩, ⟨⟩⟩]`: an inner share whose leg is an
    /// occurrence of the outer one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the outer share, whose second occurrence stands as the inner
    ///   share's leg and so counts from outside the inner share.
    /// - provides: the root the scope and purity cases measure: nine nodes, two
    ///   shares of three occurrences nested two deep, standing for seven nodes.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn leg_scope_case(overlay: &mut Overlay) -> OverlayValueId
    {
        let first = unit(overlay);
        let second = unit(overlay);
        let leg = pair(overlay, first, second);
        let read_outer = only_occurrence(overlay);
        let inner_leg = occurrence(
            overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(1_u32),
        );
        let read_inner = only_occurrence(overlay);
        let inner = share(overlay, ShareArity::from(1_u32), inner_leg, read_inner);
        let body = pair(overlay, read_outer, inner);
        share(overlay, ShareArity::from(2_u32), leg, body)
    }

    /// Measure a value root, refusal included.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`SharingMeasure::of`] at the value root `root`.
    /// - provides: the one call every case below measures through.
    /// - panics: none.
    fn measured(
        overlay: &Overlay,
        root: OverlayValueId,
    ) -> Result<SharingMeasure, MeasureFault>
    {
        SharingMeasure::of(overlay, OverlayId::Value(root))
    }

    #[test]
    fn a_share_with_many_occurrences_inlines_its_leg_at_each()
    {
        let mut overlay = Overlay::new();
        let first = unit(&mut overlay);
        let second = unit(&mut overlay);
        let leg = pair(&mut overlay, first, second);
        let mut body = only_occurrence(&mut overlay);
        for position in 1 .. OCCURRENCES {
            let read = occurrence(
                &mut overlay,
                ShareDistance::from(0_u32),
                SharePosition::from(position),
            );
            body = pair(&mut overlay, body, read);
        }
        let root = share(&mut overlay, ShareArity::from(OCCURRENCES), leg, body);
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(1),
                occurrences: OccurrenceCount(1_000),
                depth: ShareDepth(1),
                nodes: NodeCount(2_003),
                expansion: ExpansionSize(3_999),
            }),
            measured(&overlay, root),
            "the three-node leg counts once among the nodes and three times per occurrence in \
             the expansion, beside the 999 pairs that hold the occurrences"
        );
    }

    #[test]
    fn the_share_depth_is_the_longest_chain_of_nested_shares()
    {
        let mut overlay = Overlay::new();
        let short_bodies = body_chain(&mut overlay, Links(3));
        let long_legs = leg_chain(&mut overlay, Links(5));
        let long_bodies = body_chain(&mut overlay, Links(5));
        let short_legs = leg_chain(&mut overlay, Links(3));
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(3),
                occurrences: OccurrenceCount(3),
                depth: ShareDepth(3),
                nodes: NodeCount(13),
                expansion: ExpansionSize(7),
            }),
            measured(&overlay, short_bodies),
            "a chain of three shares nested through their bodies is three deep"
        );
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(5),
                occurrences: OccurrenceCount(5),
                depth: ShareDepth(5),
                nodes: NodeCount(11),
                expansion: ExpansionSize(1),
            }),
            measured(&overlay, long_legs),
            "a chain of five shares nested through their legs is five deep, and stands for the \
             one unit at its bottom"
        );
        let legs_longer = pair(&mut overlay, short_bodies, long_legs);
        let bodies_longer = pair(&mut overlay, long_bodies, short_legs);
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(8),
                occurrences: OccurrenceCount(8),
                depth: ShareDepth(5),
                nodes: NodeCount(25),
                expansion: ExpansionSize(9),
            }),
            measured(&overlay, legs_longer),
            "two sibling chains measure the longer, here the right one"
        );
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(8),
                occurrences: OccurrenceCount(8),
                depth: ShareDepth(5),
                nodes: NodeCount(29),
                expansion: ExpansionSize(13),
            }),
            measured(&overlay, bodies_longer),
            "and here the left one"
        );
    }

    #[test]
    fn an_occurrence_free_root_measures_its_own_size()
    {
        let mut core = CoreArena::new();
        let held_unit = core.value_unit();
        let held = core.value_pair(held_unit, held_unit);

        let mut overlay = Overlay::new();
        let left = unit(&mut overlay);
        let opaque = overlay
            .mint_value(ValueNode::Opaque(held))
            .expect("an opaque node names no overlay child");
        let injected = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Injection(
                Side::Left,
                opaque,
            )))
            .expect("the injected value resolves");
        let root = pair(&mut overlay, left, injected);
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(0),
                occurrences: OccurrenceCount(0),
                depth: ShareDepth(0),
                nodes: NodeCount(4),
                expansion: ExpansionSize(4),
            }),
            measured(&overlay, root),
            "with no share the expansion is the node count, the opaque pair counting once"
        );

        let scrutinee = overlay
            .mint_value(ValueNode::Opaque(held))
            .expect("an opaque node names no overlay child");
        let returned_left = unit(&mut overlay);
        let on_left = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(returned_left)))
            .expect("the returned value resolves");
        let returned_right = unit(&mut overlay);
        let on_right = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(returned_right)))
            .expect("the returned value resolves");
        let case = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Case {
                scrutinee,
                on_left,
                on_right,
            }))
            .expect("the scrutinee and both branches resolve");
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(0),
                occurrences: OccurrenceCount(0),
                depth: ShareDepth(0),
                nodes: NodeCount(6),
                expansion: ExpansionSize(6),
            }),
            SharingMeasure::of(&overlay, OverlayId::Computation(case)),
            "a computation root of three children measures the same way"
        );
    }

    #[test]
    fn a_leg_reads_the_shares_outside_its_own()
    {
        let mut overlay = Overlay::new();
        let root = leg_scope_case(&mut overlay);
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(2),
                occurrences: OccurrenceCount(3),
                depth: ShareDepth(2),
                nodes: NodeCount(9),
                expansion: ExpansionSize(7),
            }),
            measured(&overlay, root),
            "the inner leg is an occurrence of the outer share, so the inner body stands for the \
             outer leg's three nodes: one pair, then three nodes at each of two places"
        );
    }

    #[test]
    fn an_occurrence_reads_the_leg_its_distance_names()
    {
        let mut overlay = Overlay::new();
        let first = unit(&mut overlay);
        let second = unit(&mut overlay);
        let outer_leg = pair(&mut overlay, first, second);
        let read_outer_first = only_occurrence(&mut overlay);
        let inner_leg = unit(&mut overlay);
        let read_outer_second = occurrence(
            &mut overlay,
            ShareDistance::from(1_u32),
            SharePosition::from(1_u32),
        );
        let read_inner_first = only_occurrence(&mut overlay);
        let read_inner_second = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(1_u32),
        );
        let inner_reads = pair(&mut overlay, read_inner_first, read_inner_second);
        let inner_body = pair(&mut overlay, read_outer_second, inner_reads);
        let inner = share(&mut overlay, ShareArity::from(2_u32), inner_leg, inner_body);
        let outer_body = pair(&mut overlay, read_outer_first, inner);
        let root = share(&mut overlay, ShareArity::from(2_u32), outer_leg, outer_body);
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(2),
                occurrences: OccurrenceCount(4),
                depth: ShareDepth(2),
                nodes: NodeCount(13),
                expansion: ExpansionSize(11),
            }),
            measured(&overlay, root),
            "the occurrence at distance one reads the outer three-node leg and the two at \
             distance zero the inner unit; read from the other end of the scope, the same \
             occurrences would stand for thirteen nodes"
        );
    }

    #[test]
    fn a_doubling_chain_measures_in_its_own_size()
    {
        let mut overlay = Overlay::new();
        let (root, _body) = doubling_chain(&mut overlay, FITTING_LINKS);
        assert_eq!(
            Ok(SharingMeasure {
                shares: ShareCount(63),
                occurrences: OccurrenceCount(126),
                depth: ShareDepth(63),
                nodes: NodeCount(253),
                expansion: ExpansionSize(u64::MAX),
            }),
            measured(&overlay, root),
            "253 nodes stand for 2^64 - 1, a size no walk over the expansion could reach, \
             measured exactly at the counter's ceiling"
        );
    }

    #[test]
    fn an_expansion_past_the_counter_is_refused_at_its_node()
    {
        let mut overlay = Overlay::new();
        let (root, body) = doubling_chain(&mut overlay, Links(64));
        let Some(&ValueNode::Shared(sharing)) = overlay.value(root)
        else {
            panic!("the chain's root is its outermost share");
        };
        let OverlayId::Value(below) = sharing.leg
        else {
            panic!("each link's leg is the value link below it");
        };
        assert_eq!(
            Ok(ExpansionSize(u64::MAX)),
            measured(&overlay, below).map(|fitting| fitting.expansion()),
            "the link below still fits the counter exactly"
        );
        assert_eq!(
            Err(MeasureFault::Overflow {
                quantity: MeasuredQuantity::Expansion,
                node: OverlayId::Value(body),
            }),
            measured(&overlay, root),
            "one link more and the outermost body's pair passes the counter, refused there \
             rather than wrapped or saturated"
        );
    }

    #[test]
    fn an_invalid_overlay_is_refused_by_name_before_measuring()
    {
        let mut elsewhere = Overlay::new();
        let _first = unit(&mut elsewhere);
        let _second = unit(&mut elsewhere);
        let foreign = unit(&mut elsewhere);

        let mut overlay = Overlay::new();
        let leaf = unit(&mut overlay);
        assert_eq!(
            Err(MeasureFault::Refused(OverlayRefusal::Unresolved {
                node: OverlayId::Value(foreign)
            })),
            measured(&overlay, foreign),
            "a root the overlay does not hold"
        );

        let open = only_occurrence(&mut overlay);
        assert_eq!(
            Err(MeasureFault::Refused(OverlayRefusal::OpenReference {
                node: OverlayId::Value(open)
            })),
            measured(&overlay, open),
            "an occurrence with no share around it"
        );

        let twice = pair(&mut overlay, leaf, leaf);
        assert_eq!(
            Err(MeasureFault::Refused(OverlayRefusal::ReachedTwice {
                node: OverlayId::Value(leaf)
            })),
            measured(&overlay, twice),
            "sharing no share names"
        );

        let short_leg = unit(&mut overlay);
        let short_read = only_occurrence(&mut overlay);
        let short = share(&mut overlay, ShareArity::from(2_u32), short_leg, short_read);
        assert_eq!(
            Err(MeasureFault::Refused(OverlayRefusal::MissingOccurrences {
                share: OverlayId::Value(short),
                arity: ShareArity::from(2_u32),
                next: SharePosition::from(1_u32),
            })),
            measured(&overlay, short),
            "a share its body under-fills"
        );

        let (overflowing, _body) = doubling_chain(&mut overlay, Links(64));
        let empty_body = unit(&mut overlay);
        let empty = share(
            &mut overlay,
            ShareArity::from(0_u32),
            overflowing,
            empty_body,
        );
        assert_eq!(
            Err(MeasureFault::Refused(OverlayRefusal::ZeroArity {
                share: OverlayId::Value(empty)
            })),
            measured(&overlay, empty),
            "a share standing for nothing is refused by validation before its leg, whose \
             expansion passes the counter, is measured"
        );
    }

    #[test]
    fn the_measure_is_a_function_of_what_the_root_reaches()
    {
        let mut overlay = Overlay::new();
        let root = leg_scope_case(&mut overlay);
        let first = measured(&overlay, root);
        assert_eq!(
            first,
            measured(&overlay, root),
            "measuring again answers the same"
        );

        let beside = unit(&mut overlay);
        let _parent = pair(&mut overlay, root, beside);
        assert_eq!(
            first,
            measured(&overlay, root),
            "a parent minted over the root changes nothing it reaches"
        );

        let mut padded = Overlay::new();
        let padding = body_chain(&mut padded, Links(4));
        let moved = leg_scope_case(&mut padded);
        assert_ne!(
            OverlayId::Value(root),
            OverlayId::Value(moved),
            "the same structure sits at other ids"
        );
        assert_eq!(
            first,
            measured(&padded, moved),
            "and measures the same in another overlay, beside nodes it does not reach"
        );
        assert!(
            measured(&padded, padding).is_ok_and(|other| Ok(other) != first),
            "while the padding measures as itself"
        );
    }
}
