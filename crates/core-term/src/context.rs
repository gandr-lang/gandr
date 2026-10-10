//! The one unified context: two flat, de Bruijn, id-addressed, name-free zones
//! `Γ; Σ`, with the linear zone's one-shot discipline enforced by the lookup
//! that reads it.
//!
//! # One representation
//!
//! There is one spelling of "the context", and it is the flat one: no name
//! keys a binder, so a lookup is an index into a stack rather than a scan, and
//! no binder costs a heap string. Names live in the surface syntax and in
//! diagnostics, above this crate.
//!
//! # Two zones, two index spaces
//!
//! `Γ` admits weakening and contraction: an occurrence reads a slot and changes
//! nothing, so an index may be read any number of times. `Σ` is linear: an
//! occurrence *consumes* its slot, a second occurrence of the same index is
//! refused, and closing a linear binder's scope with its slot unconsumed is
//! refused too.
//!
//! Each zone has its own binder stack and its own de Bruijn index space, which
//! is why [`Value::Variable`] carries the zone beside the index.
//!
//! The linear zone is the type-level form of "a control capture cannot be
//! naively duplicated": it is the half a duplication policy asks rather than
//! re-decides. No former in the core vocabulary binds into it, so its laws are
//! unit-tested here against a context opened with [`Zone::Linear`] directly.
//!
//! # The error path is single-valued
//!
//! A failing operation leaves the context **at the failure point**, unchanged
//! by the failure itself and un-unwound. The context has one implementation,
//! iterative, so no second face can unwind it differently, and the failure
//! state *is* the specification: it is asserted rather than described.
//!
//! [`Value::Variable`]: crate::Value::Variable

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;

use crate::arena::ValueTypeId;
use crate::syntax::Zone;

/// The number of binders one zone of a context holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderDepth(usize);

impl From<usize> for BinderDepth
{
    /// Wraps a raw count as a zone's binder depth.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: usize) -> Self
    {
        Self(depth)
    }
}

impl From<BinderDepth> for usize
{
    /// Unwraps a binder depth to its raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: BinderDepth) -> Self
    {
        depth.0
    }
}

/// Whether a linear slot still carries its single use.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LinearUse
{
    /// The slot has not been consumed; exactly one occurrence may still read
    /// it.
    Available,
    /// The slot has been consumed; a further occurrence is refused.
    Consumed,
}

/// One binder of the linear zone: its declared type and its remaining use.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct LinearSlot
{
    /// The type the binder was introduced at.
    declared: ValueTypeId,
    /// Whether the slot's single use is still available.
    use_state: LinearUse,
}

/// Why a context operation was refused.
///
/// Every variant names the zone or the slot it is about, because the context is
/// name-free: a diagnostic above this crate re-attaches the surface name, and a
/// refusal that named neither the zone nor the index would be unattachable.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ContextError
{
    /// The index counts past every binder the zone holds.
    UnboundIndex
    {
        /// The zone the index was read in.
        zone: Zone,
        /// The index that failed to resolve.
        index: DeBruijnIndex,
        /// The binders the zone held when it failed.
        depth: BinderDepth,
    },
    /// A linear slot was read a second time. Contraction is not admissible in
    /// the linear zone, and this is where the refusal happens.
    LinearSlotConsumed
    {
        /// The index whose slot was already consumed.
        index: DeBruijnIndex,
    },
    /// A linear binder's scope closed with its single use unspent. Weakening is
    /// not admissible in the linear zone either, and this is that half.
    LinearSlotUnconsumed
    {
        /// The depth the zone stood at when the scope closed.
        depth: BinderDepth,
    },
    /// A scope was closed in a zone that holds no binder.
    NoBinderToClose
    {
        /// The zone that was empty.
        zone: Zone,
    },
}

/// The offset of one binder within its zone's flat stack.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SlotOffset(usize);

/// Resolve a de Bruijn index against a zone of `depth` binders.
///
/// The index counts binders outward from the use site, so index zero names the
/// innermost binder, which is the *last* element of the flat stack.
///
/// # Specification
/// - requires: nothing — every index and every depth is admissible input.
/// - ensures: `|ret| usize::try_from(u32::from(index)).map_or_else(|_|
///   ret.is_none(), |index| match ret { Some(offset) =>
///   offset.0.checked_add(index).and_then(|below| below.checked_add(1_usize))
///   == Some(depth.0), None => index >= depth.0 })` — the stack offset of the
///   named binder, which is `depth - index - 1`, exactly when the index counts
///   within `depth`.
/// - provides: the one arithmetic both zones' lookups share, so the two cannot
///   disagree about what an index names. The clause states the offset by the
///   sum that recovers the depth, so it is not the body's own subtraction chain
///   read back.
/// - fails: returns `None` when the index counts past the zone's binders,
///   including for an empty zone.
/// - panics: none — both subtractions are checked.
///
/// # Adequacy
/// - hypothesis: L3 — the two decision surfaces are the two checked
///   subtractions, separated by the innermost index of a two-deep zone, an
///   outer index, the first index past the depth, and an index read against an
///   empty zone, each observed through the lookups that report on it.
/// - witness: `context::tests::opening_a_binder_shifts_the_zones_indices`
/// - witness: `context::tests::an_index_past_the_depth_is_unbound`
#[inline]
#[spec(ensures: |ret| usize::try_from(u32::from(index)).map_or_else(|_| ret.is_none(), |index| {
    match ret {
        | Some(offset) => {
            offset.0.checked_add(index).and_then(|below| below.checked_add(1_usize))
                == Some(depth.0)
        },
        | None => index >= depth.0,
    }
}))]
fn slot_offset(
    depth: BinderDepth,
    index: DeBruijnIndex,
) -> Option<SlotOffset>
{
    let index = usize::try_from(u32::from(index)).ok()?;
    let remaining = depth.0.checked_sub(index)?;
    let offset = remaining.checked_sub(1_usize)?;
    Some(SlotOffset(offset))
}

/// The unified typing context: the intuitionistic zone `Γ` and the linear zone
/// `Σ`, both flat, both id-addressed, both name-free.
///
/// Cloning a context is a flat two-vector clone, which is what lets a
/// conversion or a normalizer take one by value without an owning-pointer
/// graph coming with it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Context
{
    /// `Γ`, innermost binder last.
    intuitionistic: Vec<ValueTypeId>,
    /// `Σ`, innermost binder last, each slot carrying its remaining use.
    linear: Vec<LinearSlot>,
}

impl Context
{
    /// The empty context.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The number of binders a zone holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn depth(
        &self,
        zone: Zone,
    ) -> BinderDepth
    {
        BinderDepth(match zone {
            | Zone::Intuitionistic => self.intuitionistic.len(),
            | Zone::Linear => self.linear.len(),
        })
    }

    /// Open a binder in `zone` at `declared`.
    ///
    /// A linear binder opens with its single use available; the intuitionistic
    /// zone records the type alone, because a structural slot has no use to
    /// spend.
    ///
    /// # Specification
    /// - requires: `declared` resolves in the arena the caller reads this
    ///   context against; the context stores the id and never dereferences it.
    /// - ensures: the zone's depth is one greater, every previously bound index
    ///   is reachable at one more than it was, and index zero of the zone names
    ///   `declared`.
    /// - provides: the binder-opening half of every rule that goes under a
    ///   binder. The predicate observes depth, the new slot and the untouched
    ///   zone's depth; the shift of older slots is witnessed by lookup.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two decision surfaces are which zone is pushed
    ///   and what a linear slot's opening use is, separated by opening one
    ///   binder in each zone with the other zone's depth asserted unmoved, and
    ///   by reading the fresh linear slot's use, which must open available.
    /// - witness: `context::tests::opening_a_binder_shifts_the_zones_indices`
    /// - witness: `context::tests::a_fresh_linear_slot_opens_available`
    #[spec(
        captures: [structural = self.intuitionistic.len(), linear = self.linear.len()],
        ensures: match zone {
            | Zone::Intuitionistic => structural.checked_add(1) == Some(self.intuitionistic.len())
                && self.linear.len() == linear && self.intuitionistic.last() == Some(&declared),
            | Zone::Linear => linear.checked_add(1) == Some(self.linear.len())
                && self.intuitionistic.len() == structural
                && self.linear.last() == Some(&LinearSlot { declared, use_state: LinearUse::Available }),
        },
    )]
    #[inline]
    pub fn open(
        &mut self,
        zone: Zone,
        declared: ValueTypeId,
    )
    {
        match zone {
            | Zone::Intuitionistic => self.intuitionistic.push(declared),
            | Zone::Linear => self.linear.push(LinearSlot {
                declared,
                use_state: LinearUse::Available,
            }),
        }
    }

    /// Close the innermost binder of `zone` and return the type it was opened
    /// at.
    ///
    /// # Specification
    /// - requires: nothing — an empty zone is admissible input and is refused.
    /// - ensures: `|ret| ret.is_err() ||
    ///   (usize::from(entry_depth).checked_sub(1_usize) ==
    ///   Some(usize::from(self.depth(zone))) && ret.ok() == entry_innermost)` —
    ///   on success the zone's depth is one smaller and the returned id is the
    ///   one the closed binder was opened at.
    /// - provides: the binder-closing half of every rule that goes under a
    ///   binder.
    /// - fails: [`ContextError::NoBinderToClose`] when the zone is empty;
    ///   [`ContextError::LinearSlotUnconsumed`] when the linear zone's
    ///   innermost slot still carries its use, which is the refusal of
    ///   weakening in `Σ`. Both leave the context exactly as it was — the
    ///   unconsumed slot is taken and put back — so the failure state is the
    ///   state the caller inspects, and the depth the refusal reports is the
    ///   depth it left behind.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ContextError::NoBinderToClose`] — the named zone holds no binder.
    /// - [`ContextError::LinearSlotUnconsumed`] — the linear binder's single
    ///   use was never spent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the empty-zone guard and
    ///   the linear zone's use check, separated by closing an empty zone,
    ///   closing a consumed linear slot, and closing an unconsumed one, each
    ///   with the post-failure depth asserted exactly.
    /// - witness: `context::tests::closing_an_empty_zone_is_refused`
    /// - witness: `context::tests::a_linear_binder_must_be_consumed_before_it_closes`
    #[inline]
    #[spec(
        captures: [
            entry_depth = self.depth(zone),
            entry_innermost = match zone {
                | Zone::Intuitionistic => self.intuitionistic.last().copied(),
                | Zone::Linear => self.linear.last().map(|slot| slot.declared),
            },
        ],
        ensures: |ret| ret.is_err()
            || (usize::from(entry_depth).checked_sub(1_usize)
                == Some(usize::from(self.depth(zone)))
                && ret.ok() == entry_innermost),
    )]
    pub fn close(
        &mut self,
        zone: Zone,
    ) -> Result<ValueTypeId, ContextError>
    {
        match zone {
            | Zone::Intuitionistic => self
                .intuitionistic
                .pop()
                .ok_or(ContextError::NoBinderToClose { zone }),
            | Zone::Linear => {
                // Pop first and restore on refusal, rather than reading the top
                // and shortening the vector by a computed length. The slot is
                // `Copy`, so the restore puts back exactly what was taken and
                // the refusal leaves the zone where it was — while there is no
                // length arithmetic left that could be off by one.
                let Some(slot) = self.linear.pop()
                else {
                    return Err(ContextError::NoBinderToClose { zone });
                };
                if slot.use_state == LinearUse::Available {
                    self.linear.push(slot);
                    return Err(ContextError::LinearSlotUnconsumed {
                        depth: BinderDepth(self.linear.len()),
                    });
                }
                Ok(slot.declared)
            },
        }
    }

    /// The type a bound index was opened at, with no use spent.
    ///
    /// This is the *reading* of a slot rather than the *occurrence* of a
    /// variable: it reports a consumed linear slot's type as readily as an
    /// available one, because a diagnostic and a well-formedness walk both need
    /// the declared type of a slot whose use is already gone.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range index is admissible input.
    /// - ensures: `|ret| ret.ok() ==
    ///   usize::try_from(u32::from(index)).ok().and_then(|index| match zone {
    ///   Zone::Intuitionistic => self.intuitionistic.iter().rev().nth(index)
    ///   .copied(), Zone::Linear => self.linear.iter().rev().nth(index)
    ///   .map(|slot| slot.declared) })` — the id the named binder was opened
    ///   at, counted inward from the innermost slot rather than through the
    ///   shared offset arithmetic.
    /// - provides: the non-consuming lookup, which is what separates reading a
    ///   context from typing an occurrence in it. The unchanged-context half of
    ///   the postcondition is `&self`'s own guarantee rather than a checkable
    ///   observation.
    /// - fails: [`ContextError::UnboundIndex`] when the index counts past the
    ///   zone's binders.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ContextError::UnboundIndex`] — the index names no binder of the
    ///   zone.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the zone selection and the
    ///   index arithmetic, separated by the innermost index, an outer index and
    ///   the first index past the depth, each asserted exactly, plus a linear
    ///   slot read after it was consumed, which must still report its type.
    /// - witness: `context::tests::a_declared_lookup_spends_no_use`
    /// - witness: `context::tests::an_index_past_the_depth_is_unbound`
    /// - witness: `context::tests::opening_a_binder_shifts_the_zones_indices`
    /// - witness: `context::tests::the_linear_zone_refuses_contraction`
    #[inline]
    #[spec(ensures: |ret| ret.ok() == usize::try_from(u32::from(index)).ok().and_then(|index| {
        match zone {
            | Zone::Intuitionistic => self.intuitionistic.iter().rev().nth(index).copied(),
            | Zone::Linear => self.linear.iter().rev().nth(index).map(|slot| slot.declared),
        }
    }))]
    pub fn declared(
        &self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Result<ValueTypeId, ContextError>
    {
        let depth = self.depth(zone);
        let unbound = ContextError::UnboundIndex { zone, index, depth };
        let Some(offset) = slot_offset(depth, index)
        else {
            return Err(unbound);
        };
        match zone {
            | Zone::Intuitionistic => self.intuitionistic.get(offset.0).copied().ok_or(unbound),
            | Zone::Linear => self
                .linear
                .get(offset.0)
                .map(|slot| slot.declared)
                .ok_or(unbound),
        }
    }

    /// Type one variable occurrence, spending whatever use the zone's
    /// discipline says an occurrence spends.
    ///
    /// In `Γ` an occurrence spends nothing, so contraction is admissible and
    /// the same index types any number of occurrences. In `Σ` an occurrence
    /// consumes the slot, so a second occurrence of the same index is
    /// refused — the linear zone's whole content, at the one place a term
    /// reads it.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range index and an already-consumed slot
    ///   are both admissible input and both refused.
    /// - ensures: the type of the named binder; in `Σ`, and only there, the
    ///   named slot is left [`LinearUse::Consumed`]. No other slot is touched
    ///   in either zone.
    /// - provides: the typing rule for [`Value::Variable`], which is the only
    ///   place the two zones' disciplines differ. The predicate observes the
    ///   selected slot, exact refusal and both depths; neighbouring slots are
    ///   distinguished by the finite transition witness.
    /// - fails: [`ContextError::UnboundIndex`] when the index names no binder;
    ///   [`ContextError::LinearSlotConsumed`] when the linear slot's single use
    ///   is already spent. A refusal spends nothing, so the context after a
    ///   failure is the context before it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ContextError::UnboundIndex`] — the index names no binder of the
    ///   zone.
    /// - [`ContextError::LinearSlotConsumed`] — the linear slot was already
    ///   used.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the zone's discipline and
    ///   the consumed guard, separated by two occurrences of one intuitionistic
    ///   index (both admitted), two occurrences of one linear index (the second
    ///   refused by variant), and an out-of-range index in each zone.
    /// - witness: `context::tests::the_intuitionistic_zone_admits_contraction`
    /// - witness: `context::tests::the_linear_zone_refuses_contraction`
    /// - witness: `context::tests::an_index_past_the_depth_is_unbound`
    /// - witness: `context::tests::occurrences_preserve_other_slots_and_refusal_state`
    ///
    /// [`Value::Variable`]: crate::Value::Variable
    #[spec(
        captures: [declared = self.declared(zone, index), use_state = self.linear_use(index),
            structural = self.intuitionistic.len(), linear = self.linear.len()],
        ensures: |ret| self.intuitionistic.len() == structural && self.linear.len() == linear
            && match declared {
                | Err(error) => ret == Err(error) && self.linear_use(index) == use_state,
                | Ok(declared) => match zone {
                    | Zone::Intuitionistic => ret == Ok(declared) && self.linear_use(index) == use_state,
                    | Zone::Linear => match use_state {
                        | Ok(LinearUse::Available) => ret == Ok(declared)
                            && self.linear_use(index) == Ok(LinearUse::Consumed),
                        | Ok(LinearUse::Consumed) => ret == Err(ContextError::LinearSlotConsumed { index })
                            && self.linear_use(index) == use_state,
                        | Err(error) => ret == Err(error) && self.linear_use(index) == use_state,
                    },
                },
            },
    )]
    #[inline]
    pub fn occurrence(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Result<ValueTypeId, ContextError>
    {
        let depth = self.depth(zone);
        let unbound = ContextError::UnboundIndex { zone, index, depth };
        let Some(offset) = slot_offset(depth, index)
        else {
            return Err(unbound);
        };
        match zone {
            | Zone::Intuitionistic => self.intuitionistic.get(offset.0).copied().ok_or(unbound),
            | Zone::Linear => {
                let Some(slot) = self.linear.get_mut(offset.0)
                else {
                    return Err(unbound);
                };
                if slot.use_state == LinearUse::Consumed {
                    return Err(ContextError::LinearSlotConsumed { index });
                }
                slot.use_state = LinearUse::Consumed;
                Ok(slot.declared)
            },
        }
    }

    /// Whether a linear slot still carries its single use.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range index is admissible input.
    /// - ensures: `|ret| ret.ok() ==
    ///   usize::try_from(u32::from(index)).ok().and_then(|index|
    ///   self.linear.iter().rev().nth(index).map(|slot| slot.use_state))` — the
    ///   slot's remaining use, counted inward from the innermost slot.
    /// - provides: the observation a caller needs to decide whether closing a
    ///   linear scope will be refused, without provoking the refusal. The
    ///   unchanged-context half of the postcondition is `&self`'s own guarantee
    ///   rather than a checkable observation.
    /// - fails: [`ContextError::UnboundIndex`] when the index names no linear
    ///   binder.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ContextError::UnboundIndex`] — the index names no linear binder.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the single decision surface is the index arithmetic,
    ///   separated by a slot before and after its use and by an index past the
    ///   depth, each asserted by variant.
    /// - witness: `context::tests::the_linear_zone_refuses_contraction`
    /// - witness: `context::tests::a_fresh_linear_slot_opens_available`
    #[inline]
    #[spec(ensures: |ret| ret.ok() == usize::try_from(u32::from(index)).ok().and_then(|index| {
        self.linear.iter().rev().nth(index).map(|slot| slot.use_state)
    }))]
    pub fn linear_use(
        &self,
        index: DeBruijnIndex,
    ) -> Result<LinearUse, ContextError>
    {
        let zone = Zone::Linear;
        let depth = self.depth(zone);
        let unbound = ContextError::UnboundIndex { zone, index, depth };
        let Some(offset) = slot_offset(depth, index)
        else {
            return Err(unbound);
        };
        self.linear
            .get(offset.0)
            .map(|slot| slot.use_state)
            .ok_or(unbound)
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_kernel_term::DeBruijnIndex;

    use super::BinderDepth;
    use super::Context;
    use super::ContextError;
    use super::LinearUse;
    use crate::arena::CoreArena;
    use crate::arena::ValueTypeId;
    use crate::syntax::Zone;

    /// Two distinct value-type ids to open binders at, so a lookup returning
    /// the wrong slot is visible rather than accidentally right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns an arena holding the unit value type and the product
    ///   of it with itself, together with both ids, which are distinct.
    /// - provides: the shared fixture the context rows open binders at.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal declared types distinguish the innermost
    ///   binder from the outer one as opening shifts de Bruijn indices.
    /// - witness: `context::tests::opening_a_binder_shifts_the_zones_indices`
    #[spec(ensures: |ret| ret.1 != ret.2
        && ret.0.value_type(ret.1) == Some(&crate::ValueType::Unit)
        && ret.0.value_type(ret.2) == Some(&crate::ValueType::Product(ret.1, ret.1)))]
    fn two_types() -> (CoreArena, ValueTypeId, ValueTypeId)
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let pair = arena.value_type_product(unit, unit);
        (arena, unit, pair)
    }

    #[test]
    fn occurrences_preserve_other_slots_and_refusal_state()
    {
        let (_arena, outer, inner) = two_types();
        let mut context = Context::new();
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            context.open(zone, outer);
            context.open(zone, inner);
        }
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            for raw in [2_u32, u32::MAX] {
                let index = DeBruijnIndex::from(raw);
                let before = context.clone();
                assert_eq!(
                    Err(ContextError::UnboundIndex {
                        zone,
                        index,
                        depth: BinderDepth::from(2_usize)
                    }),
                    context.occurrence(zone, index)
                );
                assert_eq!(before, context);
            }
        }
        let zero = DeBruijnIndex::from(0_u32);
        let one = DeBruijnIndex::from(1_u32);
        assert_eq!(Ok(outer), context.occurrence(Zone::Linear, one));
        assert_eq!(Ok(LinearUse::Available), context.linear_use(zero));
        assert_eq!(Ok(LinearUse::Consumed), context.linear_use(one));
        let before = context.clone();
        assert_eq!(
            Err(ContextError::LinearSlotUnconsumed {
                depth: BinderDepth::from(2_usize)
            }),
            context.close(Zone::Linear)
        );
        assert_eq!(before, context);
        assert_eq!(Ok(inner), context.occurrence(Zone::Intuitionistic, zero));
        assert_eq!(before, context);
        assert_eq!(Ok(inner), context.occurrence(Zone::Linear, zero));
        assert_eq!(Ok(inner), context.close(Zone::Linear));
        assert_eq!(Ok(outer), context.declared(Zone::Linear, zero));
        assert_eq!(
            Err(ContextError::LinearSlotConsumed { index: zero }),
            context.occurrence(Zone::Linear, zero)
        );
        assert_eq!(Ok(inner), context.declared(Zone::Intuitionistic, zero));
        assert_eq!(Ok(outer), context.declared(Zone::Intuitionistic, one));
        assert_eq!(Ok(outer), context.close(Zone::Linear));
        assert_eq!(BinderDepth::from(0_usize), context.depth(Zone::Linear));
    }

    #[test]
    fn opening_a_binder_shifts_the_zones_indices()
    {
        let (_arena, outer, inner) = two_types();
        let mut context = Context::new();
        context.open(Zone::Intuitionistic, outer);
        assert_eq!(
            Ok(outer),
            context.declared(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            "the only binder is index zero"
        );
        context.open(Zone::Intuitionistic, inner);
        assert_eq!(
            Ok(inner),
            context.declared(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            "the new binder takes index zero"
        );
        assert_eq!(
            Ok(outer),
            context.declared(Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
            "the old binder moved out by exactly one — weakening in the structural zone"
        );
        assert_eq!(
            BinderDepth::from(0_usize),
            context.depth(Zone::Linear),
            "the zones have separate binder stacks"
        );
    }

    #[test]
    fn the_intuitionistic_zone_admits_contraction()
    {
        let (_arena, declared, _other) = two_types();
        let mut context = Context::new();
        context.open(Zone::Intuitionistic, declared);
        let index = DeBruijnIndex::from(0_u32);
        assert_eq!(
            Ok(declared),
            context.occurrence(Zone::Intuitionistic, index),
            "the first occurrence types"
        );
        assert_eq!(
            Ok(declared),
            context.occurrence(Zone::Intuitionistic, index),
            "and so does the second — a structural slot spends nothing"
        );
    }

    #[test]
    fn the_linear_zone_refuses_contraction()
    {
        let (_arena, declared, _other) = two_types();
        let mut context = Context::new();
        context.open(Zone::Linear, declared);
        let index = DeBruijnIndex::from(0_u32);
        assert_eq!(
            Ok(declared),
            context.occurrence(Zone::Linear, index),
            "the single use types the first occurrence"
        );
        assert_eq!(
            Err(ContextError::LinearSlotConsumed { index }),
            context.occurrence(Zone::Linear, index),
            "the second occurrence is refused by name"
        );
        assert_eq!(
            Ok(LinearUse::Consumed),
            context.linear_use(index),
            "the refusal left the slot consumed rather than reopening it"
        );
        assert_eq!(
            Ok(declared),
            context.declared(Zone::Linear, index),
            "a consumed slot still reports the type it was opened at"
        );
    }

    #[test]
    fn a_fresh_linear_slot_opens_available()
    {
        let (_arena, declared, _other) = two_types();
        let mut context = Context::new();
        context.open(Zone::Linear, declared);
        let index = DeBruijnIndex::from(0_u32);
        assert_eq!(
            Ok(LinearUse::Available),
            context.linear_use(index),
            "a linear binder opens carrying its use"
        );
        assert_eq!(
            Err(ContextError::UnboundIndex {
                zone: Zone::Linear,
                index: DeBruijnIndex::from(1_u32),
                depth: BinderDepth::from(1_usize),
            }),
            context.linear_use(DeBruijnIndex::from(1_u32)),
            "an index past the linear depth has no use to report"
        );
    }

    #[test]
    fn a_declared_lookup_spends_no_use()
    {
        let (_arena, declared, _other) = two_types();
        let mut context = Context::new();
        context.open(Zone::Linear, declared);
        let index = DeBruijnIndex::from(0_u32);
        assert_eq!(Ok(declared), context.declared(Zone::Linear, index));
        assert_eq!(
            Ok(LinearUse::Available),
            context.linear_use(index),
            "reading a slot is not occurring in it"
        );
    }

    #[test]
    fn an_index_past_the_depth_is_unbound()
    {
        let (_arena, declared, _other) = two_types();
        let mut context = Context::new();
        let empty = DeBruijnIndex::from(0_u32);
        assert_eq!(
            Err(ContextError::UnboundIndex {
                zone: Zone::Intuitionistic,
                index: empty,
                depth: BinderDepth::from(0_usize),
            }),
            context.occurrence(Zone::Intuitionistic, empty),
            "an empty zone binds no index"
        );
        context.open(Zone::Intuitionistic, declared);
        let past = DeBruijnIndex::from(1_u32);
        assert_eq!(
            Err(ContextError::UnboundIndex {
                zone: Zone::Intuitionistic,
                index: past,
                depth: BinderDepth::from(1_usize),
            }),
            context.declared(Zone::Intuitionistic, past),
            "the first index past the depth is refused, and the refusal names the depth"
        );
    }

    #[test]
    fn closing_an_empty_zone_is_refused()
    {
        let mut context = Context::new();
        for zone in [Zone::Intuitionistic, Zone::Linear] {
            assert_eq!(
                Err(ContextError::NoBinderToClose { zone }),
                context.close(zone),
                "an empty zone has no scope to close"
            );
            assert_eq!(
                BinderDepth::from(0_usize),
                context.depth(zone),
                "the refusal left the zone where it was"
            );
        }
    }

    #[test]
    fn a_linear_binder_must_be_consumed_before_it_closes()
    {
        let (_arena, declared, _other) = two_types();
        let mut context = Context::new();
        context.open(Zone::Linear, declared);
        assert_eq!(
            Err(ContextError::LinearSlotUnconsumed {
                depth: BinderDepth::from(1_usize),
            }),
            context.close(Zone::Linear),
            "an unspent linear use is a refusal, not a silent discard"
        );
        assert_eq!(
            BinderDepth::from(1_usize),
            context.depth(Zone::Linear),
            "the failure left the context at the failure point, un-unwound"
        );
        let consumed = context.occurrence(Zone::Linear, DeBruijnIndex::from(0_u32));
        assert_eq!(
            Ok(declared),
            consumed,
            "the slot was still there to be used"
        );
        assert_eq!(
            Ok(declared),
            context.close(Zone::Linear),
            "a consumed slot closes and reports the type it was opened at"
        );
    }

    #[test]
    fn an_intuitionistic_scope_closes_without_a_use()
    {
        let (_arena, declared, _other) = two_types();
        let mut context = Context::new();
        context.open(Zone::Intuitionistic, declared);
        assert_eq!(
            Ok(declared),
            context.close(Zone::Intuitionistic),
            "a structural binder closes unread — weakening is admissible in the structural zone"
        );
    }
}
