//! Reference-counted render plans retained by resolved summaries.
//!
//! Resolution allocates, retains, and releases plans while it prunes its
//! frontier, and the render machine walks the winning one. A plan identity is
//! generational, so a recycled slot is never mistaken for the node it held
//! before, and every release walks its children on an explicit stack.

use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::arena::TextId;
use crate::arena::VerbatimId;
use crate::error::RenderAllocationSite;
use crate::error::RenderArithmetic;
use crate::error::RenderError;
use crate::error::RenderInvariant;
use crate::limits::RenderMeter;
use crate::measure::PhysicalLineEnding;
use crate::units::Indentation;

quenchant_shape::reason_enum! {
    /// Why a plan identity names no live node.
    pub(crate) mod lookup {
        /// The reason the identity names nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// The slot lies outside the arena.
            OutOfRange,
            /// The slot was released, or recycled under a later generation.
            Released,
        }
    }
}

/// A generational identity in the plan arena.
///
/// # Specification
/// - requires: the identity was minted by one [`PlanArena`].
/// - ensures: a recycled slot cannot be mistaken for its previous node.
/// - provides: the winning-plan handle returned by resolution.
/// - panics: none.
/// - executable: none — the identity is a data declaration; allocation,
///   retention, checked lookup and release carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
///   identities expose exact node, reference count and typed absence. Aliased
///   children, failed second retention and a refused parent allocation expose
///   rollback counts; u32 reference/generation ceilings distinguish overflow
///   from reuse. Allocation failure is not deterministically injected.
/// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
/// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
/// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PlanId
{
    /// The dense arena slot.
    slot: u32,
    /// The slot generation.
    generation: u32,
}

/// One first-order plan node.
///
/// # Specification
/// - requires: child identities belong to the same plan arena.
/// - ensures: the node contains no closure or recursive continuation.
/// - provides: the data the render machine walks to emit bytes.
/// - panics: none.
/// - executable: none — the plan node is a data declaration; allocation,
///   retention, checked lookup and release carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
///   identities expose exact node, reference count and typed absence. Aliased
///   children, failed second retention and a refused parent allocation expose
///   rollback counts; u32 reference/generation ceilings distinguish overflow
///   from reuse. Allocation failure is not deterministically injected.
/// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
/// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
/// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PlanNode
{
    /// Emits no bytes.
    Empty,
    /// Emits one stored text identity.
    Text(TextId),
    /// Emits one stored verbatim identity.
    Verbatim(VerbatimId),
    /// Emits a configured layout ending and indentation.
    Newline
    {
        /// Number of spaces after the ending.
        indentation: Indentation,
        /// Physical ending bytes.
        ending: PhysicalLineEnding,
    },
    /// Executes left before right.
    Seq
    {
        /// First child.
        left: PlanId,
        /// Second child.
        right: PlanId,
    },
}

/// What releasing one reference to a plan left behind.
///
/// # Specification
/// - requires: the value came from [`PlanArena::release_one`].
/// - ensures: `Freed` and `FreedSequence` mean the slot was recycled; `Shared`
///   means another reference keeps the node live.
/// - provides: the children a releasing caller must release in turn.
/// - panics: none.
/// - executable: none — the release result is a data declaration; allocation,
///   retention, checked lookup and release carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
///   identities expose exact node, reference count and typed absence. Aliased
///   children, failed second retention and a refused parent allocation expose
///   rollback counts; u32 reference/generation ceilings distinguish overflow
///   from reuse. Allocation failure is not deterministically injected.
/// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
/// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
/// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Released
{
    /// Another reference keeps the node live.
    Shared,
    /// The node was freed and had no children.
    Freed,
    /// The node was a sequence, freed; each child lost one reference.
    FreedSequence
    {
        /// The first child.
        left: PlanId,
        /// The second child.
        right: PlanId,
    },
}

/// One slot in the generational plan arena.
///
/// # Specification
/// - requires: the slot is owned by one plan arena.
/// - ensures: live references retain the current generation; released nodes
///   have no references.
/// - provides: one reusable plan identity with checked retention.
/// - panics: none.
/// - executable: none — this ownership record has no executable invocation;
///   plan-arena transitions carry its predicates.
///
/// # Adequacy
/// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
///   identities expose exact node, reference count and typed absence. Aliased
///   children, failed second retention and a refused parent allocation expose
///   rollback counts; u32 reference/generation ceilings distinguish overflow
///   from reuse. Allocation failure is not deterministically injected.
/// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
/// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
/// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlanSlot
{
    /// Generation guarding this slot's identity.
    generation: u32,
    /// Number of live references to the node.
    references: u32,
    /// The plan node, absent after release.
    node: Maybe<PlanNode, lookup::Absent>,
}

/// The private plan store held by one [`Resolved`] result.
///
/// [`Resolved`]: crate::resolve::Resolved
///
/// # Specification
/// - requires: operations use the owning resolution meter.
/// - ensures: live identities match their slot generation and released slots
///   may be reused only at a later generation.
/// - provides: bounded first-order plan ownership for a resolved result.
/// - panics: none.
/// - executable: none — this ownership record has no executable invocation;
///   plan-arena transitions carry its predicates.
///
/// # Adequacy
/// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
///   identities expose exact node, reference count and typed absence. Aliased
///   children, failed second retention and a refused parent allocation expose
///   rollback counts; u32 reference/generation ceilings distinguish overflow
///   from reuse. Allocation failure is not deterministically injected.
/// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
/// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
/// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
#[derive(Debug)]
pub(crate) struct PlanArena
{
    /// Generational slots, including recycled entries.
    slots: Vec<PlanSlot>,
    /// Released identities whose slots are available for reuse.
    free: Vec<PlanId>,
}

impl PlanArena
{
    /// Creates an empty plan arena.
    ///
    /// # Specification
    /// - requires: no prior plan identities are live.
    /// - ensures: the first allocation starts at slot zero.
    /// - provides: the retention store for one resolution.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
    ///   identities expose exact node, reference count and typed absence.
    ///   Aliased children, failed second retention and a refused parent
    ///   allocation expose rollback counts; u32 reference/generation ceilings
    ///   distinguish overflow from reuse. Allocation failure is not
    ///   deterministically injected.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    #[spec(
        ensures: |ret| ret.slots.is_empty()
                && ret.free.is_empty()
    )]
    #[inline]
    pub(crate) const fn new() -> Self
    {
        Self {
            slots: Vec::new(),
            free: Vec::new(),
        }
    }

    /// Allocates one plan node with one owning reference.
    ///
    /// # Specification
    /// - requires: `meter` is the operation's shared render meter.
    /// - ensures: the returned identity resolves until its final release.
    /// - provides: generational plan allocation, reusing a released slot first.
    /// - fails: reports a plan limit, allocation failure, or generation
    ///   overflow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::LimitExceeded`] at a plan ceiling,
    /// [`RenderError::AllocationFailed`] when the slot store cannot grow, and
    /// [`RenderError::ArithmeticOverflow`] when a slot or generation cannot
    /// advance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
    ///   identities expose exact node, reference count and typed absence.
    ///   Aliased children, failed second retention and a refused parent
    ///   allocation expose rollback counts; u32 reference/generation ceilings
    ///   distinguish overflow from reuse. Allocation failure is not
    ///   deterministically injected.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    #[spec(
        captures: before = (self.slots.len(), self.free.len(), self.free.last().copied(), self.free.last().and_then(|id| usize::try_from(id.slot).ok()).and_then(|index| self.slots.get(index)).map(|entry| entry.generation)),
        ensures: |ret| ret.as_ref().map_or(true,
            |id| usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)) == Some(&PlanSlot { generation: id.generation, references: 1, node: Maybe::Present(node) })
                && before.2.map_or_else(|| usize::try_from(id.slot) == Ok(before.0)
                && id.generation == 0
                && self.slots.len() == before.0.saturating_add(1)
                && self.free.len() == before.1,
            |released| id.slot == released.slot
                && before.3.and_then(|generation| generation.checked_add(1)) == Some(id.generation)
                && self.slots.len() == before.0
                && self.free.len().checked_add(1) == Some(before.1)))
    )]
    pub(crate) fn alloc(
        &mut self,
        node: PlanNode,
        meter: &mut RenderMeter,
    ) -> Result<PlanId, RenderError>
    {
        meter.charge_plan_node()?;
        if let Some(released) = self.free.pop() {
            let entry = self.entry_mut(released)?;
            entry.generation =
                entry
                    .generation
                    .checked_add(1u32)
                    .ok_or(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::PlanGeneration,
                    })?;
            entry.references = 1u32;
            entry.node = Maybe::Present(node);
            return Ok(PlanId {
                slot: released.slot,
                generation: entry.generation,
            });
        }
        self.slots
            .try_reserve(1usize)
            .map_err(|_error| RenderError::AllocationFailed {
                site: RenderAllocationSite::PlanArena,
            })?;
        let slot =
            u32::try_from(self.slots.len()).map_err(|_error| RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::PlanSlot,
            })?;
        self.slots.push(PlanSlot {
            generation: 0u32,
            references: 1u32,
            node: Maybe::Present(node),
        });
        Ok(PlanId {
            slot,
            generation: 0u32,
        })
    }

    /// Allocates a sequence and retains its two child identities.
    ///
    /// # Specification
    /// - requires: children are candidate identities; stale and out-of-range
    ///   identities remain in the domain.
    /// - ensures: the sequence owns one reference to each child; on failure
    ///   both children keep exactly the references they had.
    /// - provides: the plan operation used by concatenation.
    /// - fails: returns stale-identity, allocation, or render-budget errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::Invariant`] for a child that is not live, and
    /// every error [`Self::alloc`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
    ///   identities expose exact node, reference count and typed absence.
    ///   Aliased children, failed second retention and a refused parent
    ///   allocation expose rollback counts; u32 reference/generation ceilings
    ///   distinguish overflow from reuse. Allocation failure is not
    ///   deterministically injected.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    #[spec(
        captures: before = (usize::try_from(left.slot).ok().and_then(|index| self.slots.get(index)).copied(), usize::try_from(right.slot).ok().and_then(|index| self.slots.get(index)).copied()),
        ensures: |ret| ret.as_ref().map_or_else(|_error| usize::try_from(left.slot).ok().and_then(|index| self.slots.get(index)).copied() == before.0
                && usize::try_from(right.slot).ok().and_then(|index| self.slots.get(index)).copied() == before.1,
            |id| self.get(*id) == Maybe::Present(PlanNode::Seq { left, right })
                && before.0.is_some_and(|old| old.references.checked_add(if left == right { 2 }
            else { 1 }).is_some_and(|references| usize::try_from(left.slot).ok().and_then(|index| self.slots.get(index)) == Some(&PlanSlot { references, ..old })))
                && before.1.is_some_and(|old| old.references.checked_add(if left == right { 2 }
            else { 1 }).is_some_and(|references| usize::try_from(right.slot).ok().and_then(|index| self.slots.get(index)) == Some(&PlanSlot { references, ..old }))))
    )]
    pub(crate) fn alloc_seq(
        &mut self,
        left: PlanId,
        right: PlanId,
        meter: &mut RenderMeter,
    ) -> Result<PlanId, RenderError>
    {
        self.retain(left)?;
        if let Err(error) = self.retain(right) {
            let _released = self.release_one(left, meter)?;
            return Err(error);
        }
        match self.alloc(PlanNode::Seq { left, right }, meter) {
            | Ok(plan) => Ok(plan),
            | Err(error) => {
                let _left = self.release_one(left, meter)?;
                let _right = self.release_one(right, meter)?;
                Err(error)
            },
        }
    }

    /// Returns a plan node when `id` has the current slot generation.
    ///
    /// # Specification
    /// - requires: `id` may be stale or foreign.
    /// - ensures: stale generations never expose a recycled node.
    /// - provides: checked machine lookup; [`lookup::Absent::OutOfRange`] for a
    ///   slot outside the arena and [`lookup::Absent::Released`] for one
    ///   released or recycled since `id` was minted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
    ///   identities expose exact node, reference count and typed absence.
    ///   Aliased children, failed second retention and a refused parent
    ///   allocation expose rollback counts; u32 reference/generation ceilings
    ///   distinguish overflow from reuse. Allocation failure is not
    ///   deterministically injected.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    #[spec(
        ensures: |ret| ret == usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)).map_or(Maybe::Absent(lookup::Absent::OutOfRange),
            |entry| if entry.generation == id.generation { entry.node }
            else { Maybe::Absent(lookup::Absent::Released) })
    )]
    #[inline]
    pub(crate) fn get(
        &self,
        id: PlanId,
    ) -> Maybe<PlanNode, lookup::Absent>
    {
        let Some(entry) = usize::try_from(id.slot)
            .ok()
            .and_then(|slot| self.slots.get(slot))
        else {
            return Maybe::Absent(lookup::Absent::OutOfRange);
        };
        if entry.generation != id.generation {
            return Maybe::Absent(lookup::Absent::Released);
        }
        entry.node
    }

    /// Retains one live reference to a plan.
    ///
    /// # Specification
    /// - requires: `id` is any candidate plan identity.
    /// - ensures: the reference count increases exactly once.
    /// - provides: memo and sequence retention.
    /// - fails: rejects stale identities or reference overflow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::Invariant`] for an identity that is not live,
    /// and [`RenderError::ArithmeticOverflow`] when the count cannot advance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
    ///   identities expose exact node, reference count and typed absence.
    ///   Aliased children, failed second retention and a refused parent
    ///   allocation expose rollback counts; u32 reference/generation ceilings
    ///   distinguish overflow from reuse. Allocation failure is not
    ///   deterministically injected.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    #[spec(
        captures: before = (usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)).copied(), self.slots.len(), self.free.len()),
        ensures: |ret| self.slots.len() == before.1
                && self.free.len() == before.2
                && match before.0 { Some(old) if old.generation == id.generation
                && matches!(old.node, Maybe::Present(_)) => old.references.checked_add(1).map_or_else(|| ret == Err(RenderError::ArithmeticOverflow { operation: RenderArithmetic::PlanRefcount })
                && usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)) == Some(&old),
            |references| ret.is_ok()
                && usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)) == Some(&PlanSlot { references, ..old })), old => ret == Err(RenderError::Invariant { invariant: RenderInvariant::PlanIdentity })
                && usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)).copied() == old }
    )]
    pub(crate) fn retain(
        &mut self,
        id: PlanId,
    ) -> Result<(), RenderError>
    {
        let entry = self.live_mut(id)?;
        entry.references =
            entry
                .references
                .checked_add(1u32)
                .ok_or(RenderError::ArithmeticOverflow {
                    operation: RenderArithmetic::PlanRefcount,
                })?;
        Ok(())
    }

    /// Releases one reference and reports the children it left to release.
    ///
    /// The resolver supplies the shared work-vector accounting around the
    /// returned children, so release records never need a second stack.
    ///
    /// # Specification
    /// - requires: `id` is any candidate plan identity.
    /// - ensures: the count drops by one; at zero the slot is freed for reuse
    ///   and the live-plan gauge drops by one.
    /// - provides: one release step, its children returned rather than walked.
    /// - fails: rejects an identity that is not live, or a free list that
    ///   cannot grow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::Invariant`] for an identity that is not live and
    /// [`RenderError::AllocationFailed`] when the free list cannot grow.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared and final releases expose reference counts,
    ///   returned child identities, stale lookup and reuse. An aliased sequence
    ///   returns its child twice because it owns two references. Premature
    ///   freeing, wrong child order, peak-counter decrement and recursive
    ///   release change these observations; a hundred-thousand-sequence witness
    ///   runs on a bounded native stack.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    /// - witness: `plan::tests::plan_release_recycles_a_deep_sequence_iteratively`
    #[spec(
        captures: before = (usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)).copied(), self.slots.len(), self.free.len(), meter.usage()),
        ensures: |ret| self.slots.len() == before.1
                && meter.usage() == before.3
                && ret.as_ref().map_or_else(|_error| self.free.len() == before.2
                && usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)).copied() == before.0,
            |released| before.0.is_some_and(|old| old.generation == id.generation
                && matches!(old.node, Maybe::Present(_))
                && if old.references > 1 { *released == Released::Shared
                && self.free.len() == before.2
                && usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)) == Some(&PlanSlot { references: old.references.saturating_sub(1), ..old }) }
            else { self.free.len() == before.2.saturating_add(1)
                && self.free.last() == Some(&id)
                && usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)) == Some(&PlanSlot { generation: old.generation, references: 0, node: Maybe::Absent(lookup::Absent::Released) })
                && *released == match old.node { Maybe::Present(PlanNode::Seq { left, right }) => Released::FreedSequence { left, right }, _ => Released::Freed } }))
    )]
    pub(crate) fn release_one(
        &mut self,
        id: PlanId,
        meter: &mut RenderMeter,
    ) -> Result<Released, RenderError>
    {
        self.free
            .try_reserve(1usize)
            .map_err(|_error| RenderError::AllocationFailed {
                site: RenderAllocationSite::PlanArena,
            })?;
        let entry = self.live_mut(id)?;
        if entry.references > 1u32 {
            entry.references = entry.references.saturating_sub(1u32);
            return Ok(Released::Shared);
        }
        let node = core::mem::replace(&mut entry.node, Maybe::Absent(lookup::Absent::Released));
        entry.references = 0u32;
        self.free.push(id);
        meter.release_plan_node();
        Ok(match node {
            | Maybe::Present(PlanNode::Seq { left, right }) => {
                Released::FreedSequence { left, right }
            },
            | Maybe::Present(
                PlanNode::Empty
                | PlanNode::Text(_)
                | PlanNode::Verbatim(_)
                | PlanNode::Newline { .. },
            )
            | Maybe::Absent(_) => Released::Freed,
        })
    }

    /// The slot `id` names, whatever generation it holds now.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: success borrows the slot's entry, live or released.
    /// - provides: the shared slot lookup of allocation and the liveness check.
    /// - fails: rejects a slot outside the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::Invariant`] for a slot outside the arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
    ///   identities expose exact node, reference count and typed absence.
    ///   Aliased children, failed second retention and a refused parent
    ///   allocation expose rollback counts; u32 reference/generation ceilings
    ///   distinguish overflow from reuse. Allocation failure is not
    ///   deterministically injected.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    #[spec(
        captures: before = usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)).map(|entry| &raw const *entry),
        ensures: |ret| ret.as_ref().map_or_else(|error| before.is_none()
                && *error == RenderError::Invariant { invariant: RenderInvariant::PlanIdentity },
            |entry| before.is_some_and(|expected| core::ptr::eq(&raw const **entry, expected)))
    )]
    fn entry_mut(
        &mut self,
        id: PlanId,
    ) -> Result<&mut PlanSlot, RenderError>
    {
        usize::try_from(id.slot)
            .ok()
            .and_then(|slot| self.slots.get_mut(slot))
            .ok_or(RenderError::Invariant {
                invariant: RenderInvariant::PlanIdentity,
            })
    }

    /// The slot `id` names, when it still holds the node `id` was minted for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: success borrows a slot at `id`'s generation holding a node.
    /// - provides: the shared liveness check of retention and release.
    /// - fails: rejects a slot outside the arena, a recycled generation, or a
    ///   released node.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::Invariant`] for an identity that is not live.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, shared, released, recycled and out-of-range
    ///   identities expose exact node, reference count and typed absence.
    ///   Aliased children, failed second retention and a refused parent
    ///   allocation expose rollback counts; u32 reference/generation ceilings
    ///   distinguish overflow from reuse. Allocation failure is not
    ///   deterministically injected.
    /// - witness: `plan::tests::plan_generation_rejects_recycled_identity`
    /// - witness: `plan::tests::sequence_retention_preserves_aliases_and_rolls_back_refusals`
    /// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
    #[spec(
        captures: before = usize::try_from(id.slot).ok().and_then(|index| self.slots.get(index)).filter(|entry| entry.generation == id.generation
                && matches!(entry.node, Maybe::Present(_))).map(|entry| &raw const *entry),
        ensures: |ret| ret.as_ref().map_or_else(|error| before.is_none()
                && *error == RenderError::Invariant { invariant: RenderInvariant::PlanIdentity },
            |entry| before.is_some_and(|expected| core::ptr::eq(&raw const **entry, expected)))
    )]
    fn live_mut(
        &mut self,
        id: PlanId,
    ) -> Result<&mut PlanSlot, RenderError>
    {
        let entry = self.entry_mut(id)?;
        if entry.generation != id.generation || matches!(entry.node, Maybe::Absent(_)) {
            return Err(RenderError::Invariant {
                invariant: RenderInvariant::PlanIdentity,
            });
        }
        Ok(entry)
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::limits::RenderLimits;
    use crate::limits::RenderMeter;

    /// A meter under the default render limits.
    ///
    /// # Specification
    /// trivial.
    fn meter() -> RenderMeter
    {
        RenderMeter::new(RenderLimits::default())
    }

    /// Recycled slots reject the identity from the prior generation.
    #[test]
    fn plan_generation_rejects_recycled_identity()
    {
        let mut arena = PlanArena::new();
        let mut meter = meter();
        let stale = arena.alloc(PlanNode::Empty, &mut meter).unwrap();
        assert_eq!(arena.release_one(stale, &mut meter), Ok(Released::Freed));
        let current = arena
            .alloc(PlanNode::Text(TextId::from(7u32)), &mut meter)
            .unwrap();
        assert_eq!(current.slot, stale.slot, "the released slot is reused");
        assert_ne!(stale, current);
        assert_eq!(arena.get(stale), Maybe::Absent(lookup::Absent::Released));
        assert_eq!(
            arena.get(current),
            Maybe::Present(PlanNode::Text(TextId::from(7u32)))
        );
        assert_eq!(
            arena.retain(stale),
            Err(RenderError::Invariant {
                invariant: RenderInvariant::PlanIdentity
            })
        );
    }

    /// Deep sequence release walks children without using the native stack.
    #[test]
    fn plan_release_recycles_a_deep_sequence_iteratively()
    {
        let released = std::thread::Builder::new()
            .stack_size(0x0001_0000_usize)
            .spawn(|| {
                let mut arena = PlanArena::new();
                let mut meter = meter();
                let mut root = arena.alloc(PlanNode::Empty, &mut meter).unwrap();
                for _ in 0u32 .. 100_000u32 {
                    let child = arena.alloc(PlanNode::Empty, &mut meter).unwrap();
                    let parent = arena.alloc_seq(root, child, &mut meter).unwrap();
                    assert_eq!(arena.release_one(root, &mut meter), Ok(Released::Shared));
                    assert_eq!(arena.release_one(child, &mut meter), Ok(Released::Shared));
                    root = parent;
                }
                let mut pending = alloc::vec![root];
                while let Some(plan) = pending.pop() {
                    if let Released::FreedSequence { left, right } =
                        arena.release_one(plan, &mut meter).unwrap()
                    {
                        pending.push(right);
                        pending.push(left);
                    }
                }
                (arena.slots.len(), arena.free.len(), arena.get(root))
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(released.0, 200_001_usize, "every node took its own slot");
        assert_eq!(released.1, released.0, "every slot was freed");
        assert_eq!(released.2, Maybe::Absent(lookup::Absent::Released));
    }

    /// A sequence owns two references even when both edges alias, and failed
    /// construction restores them.
    #[test]
    fn sequence_retention_preserves_aliases_and_rolls_back_refusals()
    {
        let mut arena = PlanArena::new();
        let mut budget = meter();
        let child = arena.alloc(PlanNode::Empty, &mut budget).expect("child");
        let parent = arena
            .alloc_seq(child, child, &mut budget)
            .expect("aliased sequence");
        assert_eq!(arena.slots.first().expect("child slot").references, 3);
        assert_eq!(
            arena.release_one(parent, &mut budget),
            Ok(Released::FreedSequence {
                left: child,
                right: child
            })
        );
        assert_eq!(arena.release_one(child, &mut budget), Ok(Released::Shared));
        assert_eq!(arena.release_one(child, &mut budget), Ok(Released::Shared));
        assert_eq!(arena.get(child), Maybe::Present(PlanNode::Empty));
        assert_eq!(arena.release_one(child, &mut budget), Ok(Released::Freed));
        assert_eq!(arena.get(child), Maybe::Absent(lookup::Absent::Released));

        let mut arena = PlanArena::new();
        let mut budget = meter();
        let left = arena
            .alloc(PlanNode::Empty, &mut budget)
            .expect("left child");
        let stale = arena
            .alloc(PlanNode::Text(TextId::from(1_u32)), &mut budget)
            .expect("second child");
        assert_eq!(arena.release_one(stale, &mut budget), Ok(Released::Freed));
        let before = *arena.slots.first().expect("left slot");
        for right in [stale, PlanId {
            slot: u32::MAX,
            generation: 0,
        }] {
            assert_eq!(
                arena.alloc_seq(left, right, &mut budget),
                Err(RenderError::Invariant {
                    invariant: RenderInvariant::PlanIdentity
                })
            );
            assert_eq!(arena.slots.first(), Some(&before));
            assert_eq!(arena.get(left), Maybe::Present(PlanNode::Empty));
        }

        let mut arena = PlanArena::new();
        let mut budget = RenderMeter::new(RenderLimits {
            max_plan_nodes_created: crate::units::MaxPlanNodesCreated::from(2_u64),
            ..RenderLimits::default()
        });
        let left = arena
            .alloc(PlanNode::Empty, &mut budget)
            .expect("left child");
        let right = arena
            .alloc(PlanNode::Text(TextId::from(7_u32)), &mut budget)
            .expect("right child");
        let before = budget.usage();
        assert_eq!(
            arena.alloc_seq(left, right, &mut budget),
            Err(RenderError::LimitExceeded {
                kind: crate::error::RenderLimitKind::PlanNodesCreated,
                limit: crate::units::LimitBound::from(2_u64)
            })
        );
        assert_eq!(budget.usage(), before);
        assert_eq!(
            arena.slots.as_slice(),
            [
                PlanSlot {
                    generation: left.generation,
                    references: 1,
                    node: Maybe::Present(PlanNode::Empty)
                },
                PlanSlot {
                    generation: right.generation,
                    references: 1,
                    node: Maybe::Present(PlanNode::Text(TextId::from(7_u32)))
                }
            ]
            .as_slice()
        );
    }

    /// Reference overflow and generation exhaustion refuse without wrapping or
    /// exposing stale nodes.
    #[test]
    fn reference_and_generation_ceilings_preserve_identity_boundaries()
    {
        let mut arena = PlanArena::new();
        let mut budget = RenderMeter::new(RenderLimits {
            max_live_plan_nodes: crate::units::MaxLivePlanNodes::from(1_u64),
            ..RenderLimits::default()
        });
        let id = arena
            .alloc(PlanNode::Empty, &mut budget)
            .expect("first node");
        let outside = PlanId {
            slot: 1,
            generation: 0,
        };
        assert_eq!(
            arena.get(outside),
            Maybe::Absent(lookup::Absent::OutOfRange)
        );
        assert_eq!(
            arena.entry_mut(outside).map(|entry| entry.node),
            Err(RenderError::Invariant {
                invariant: RenderInvariant::PlanIdentity
            })
        );
        assert_eq!(
            arena.live_mut(outside).map(|entry| entry.node),
            Err(RenderError::Invariant {
                invariant: RenderInvariant::PlanIdentity
            })
        );
        arena.slots.first_mut().expect("live slot").references = u32::MAX;
        let before = *arena.slots.first().expect("live slot");
        assert_eq!(
            arena.retain(id),
            Err(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::PlanRefcount
            })
        );
        assert_eq!(arena.slots.first(), Some(&before));
        arena.slots.first_mut().expect("live slot").references = u32::MAX.saturating_sub(1);
        let before = *arena.slots.first().expect("live slot");
        assert_eq!(
            arena.alloc_seq(id, id, &mut budget),
            Err(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::PlanRefcount
            })
        );
        assert_eq!(arena.slots.first(), Some(&before));
        arena.slots.first_mut().expect("live slot").references = 1;
        assert_eq!(arena.release_one(id, &mut budget), Ok(Released::Freed));
        let current = arena
            .alloc(PlanNode::Text(TextId::from(3_u32)), &mut budget)
            .expect("release returns live quota");
        assert_eq!(arena.get(id), Maybe::Absent(lookup::Absent::Released));
        assert_eq!(
            arena.entry_mut(id).map(|entry| entry.node),
            Ok(Maybe::Present(PlanNode::Text(TextId::from(3_u32))))
        );
        assert_eq!(
            arena.live_mut(id).map(|entry| entry.node),
            Err(RenderError::Invariant {
                invariant: RenderInvariant::PlanIdentity
            })
        );
        assert_eq!(arena.release_one(current, &mut budget), Ok(Released::Freed));
        let exhausted = PlanId {
            slot: current.slot,
            generation: u32::MAX,
        };
        arena.slots.first_mut().expect("released slot").generation = u32::MAX;
        *arena.free.last_mut().expect("released identity") = exhausted;
        assert_eq!(
            arena.alloc(PlanNode::Empty, &mut budget),
            Err(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::PlanGeneration
            })
        );
        assert_eq!(
            arena.slots.first().expect("exhausted slot").generation,
            u32::MAX
        );
        assert_eq!(
            arena.get(exhausted),
            Maybe::Absent(lookup::Absent::Released)
        );
    }
}
