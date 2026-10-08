//! The order-maintenance structure ([`OrderMaintenance`]) and its handle
//! ([`Pos`]) — see the crate-root documentation for the problem statement, the
//! labeling algorithm, and the complexity claims.
//!
//! The structure is a flat arena of [`Slot`]s addressed by [`SlotIndex`]; list
//! order is carried by index links, never by owning pointers, and every walk
//! over those links is an explicit loop.

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering as AtomicOrdering;

use anodized::spec;

/// A process-wide counter minting a distinct identity for each
/// [`OrderMaintenance`], so a [`Pos`] from one structure is detected as foreign
/// to another rather than silently resolving against an unrelated element.
static NEXT_STRUCTURE_ID: StructureIdCounter = StructureIdCounter(AtomicUsize::new(0));

/// A structure's process-unique identity, stamped into every [`Pos`] it mints;
/// a handle used against a different structure is rejected.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct StructureId(usize);

/// A counter minting distinct [`StructureId`]s; exhaustion fails rather than
/// wrapping, so a reissued id can never alias an extant [`Pos`].
///
/// The counter is pointer-width rather than 64-bit so the crate builds on every
/// target that has an atomic compare-exchange at all, not only on targets with
/// 64-bit atomics. Pointer width is the floor a process-wide unique-id counter
/// cannot go below: the identity has to be at least as wide as the number of
/// structures a process can distinguish, and narrowing it would move exhaustion
/// from unreachable to merely unlikely. The crate root states the target
/// requirement and enforces it.
#[repr(transparent)]
struct StructureIdCounter(AtomicUsize);

impl StructureIdCounter
{
    /// A counter with exactly one distinct identity left to issue.
    #[cfg(test)]
    #[inline]
    fn nearly_exhausted() -> Self
    {
        Self(AtomicUsize::new(usize::MAX.wrapping_sub(1)))
    }

    /// Mints the next distinct [`StructureId`] from this counter.
    ///
    /// # Specification
    /// - requires: nothing; the counter is safe to share across threads.
    /// - ensures: on `Ok`, the returned id was never issued by this counter
    ///   before and never will be again.
    /// - provides: the identity stamped into every handle a structure mints.
    ///   The postcondition stays prose: uniqueness is a law over the ids
    ///   earlier and later calls issue, which no predicate at this call can
    ///   observe.
    /// - fails: returns [`OrderError::StructureIdExhausted`] once the counter
    ///   would wrap, leaving the final id permanently unissued.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when no distinct id
    /// remains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the sole decision surface is the `checked_add`
    ///   guard, separated by driving a counter seeded one below the ceiling
    ///   through its last successful issue and then its first refusal, with the
    ///   exact error variant asserted.
    /// - witness: `order::tests::structure_id_exhaustion_is_typed`
    #[inline]
    fn allocate(&self) -> Result<StructureId, OrderError>
    {
        self.0
            .try_update(AtomicOrdering::Relaxed, AtomicOrdering::Relaxed, |next| {
                next.checked_add(1)
            })
            .map(StructureId)
            .map_err(|_current| OrderError::StructureIdExhausted)
    }
}

/// The number of bits in a label universe: labels live in `[0, 2^bits)`.
///
/// [`Self::MAX`] sits below 64 with headroom so that the relabel arithmetic (an
/// aligned window of size `2^h` for `h <= MAX`, and label offsets bounded by
/// that window) never approaches `u64::MAX`, and so the resulting density cap
/// `2^61` dwarfs the `u32` slot-index ceiling that binds first in practice.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct LabelBits(u32);

impl LabelBits
{
    /// The narrowest supported label-universe width.
    const MIN: Self = Self(1);
    /// The widest supported label-universe width: labels live in `[0, 2^62)`.
    const MAX: Self = Self(62);

    /// This width clamped into `[MIN, MAX]`.
    #[inline]
    fn clamped(self) -> Self
    {
        Self(self.0.clamp(Self::MIN.0, Self::MAX.0))
    }

    /// The next wider width, or `None` at the representable ceiling.
    #[inline]
    fn wider(self) -> Option<Self>
    {
        self.0.checked_add(1).map(Self)
    }
}

/// An element's order label; strictly increasing in list order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Label(u64);

impl Label
{
    /// The smallest representable label.
    const ZERO: Self = Self(0);
}

/// The label-universe size `2^label_bits`, cached from a structure's
/// [`LabelBits`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct LabelCapacity(u64);

/// The size of a relabel window: a power-of-two count of consecutive label
/// values, redistributed evenly when the window is relabeled.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct LabelRangeSize(u64);

/// An element's slot index in the arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SlotIndex(u32);

impl TryFrom<usize> for SlotIndex
{
    type Error = <u32 as TryFrom<usize>>::Error;

    #[inline]
    fn try_from(value: usize) -> Result<Self, Self::Error>
    {
        u32::try_from(value).map(Self)
    }
}

impl TryFrom<SlotIndex> for usize
{
    type Error = <Self as TryFrom<u32>>::Error;

    #[inline]
    fn try_from(value: SlotIndex) -> Result<Self, Self::Error>
    {
        Self::try_from(value.0)
    }
}

/// A slot's reuse counter, bumped each time the slot is freed so a handle
/// minted before the reuse no longer resolves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SlotGeneration(u32);

impl SlotGeneration
{
    /// The generation a never-reused slot carries.
    const FIRST: Self = Self(0);
    /// The last generation a slot can carry before it must be retired.
    #[cfg(test)]
    const LAST: Self = Self(u32::MAX);

    /// The generation the slot's next occupant carries, or `None` once the
    /// slot's generation space is exhausted and the slot must be retired
    /// rather than reused.
    #[inline]
    fn successor(self) -> Option<Self>
    {
        self.0.checked_add(1).map(Self)
    }
}

/// The number of elements a relabel window must hold, counting the element
/// being inserted.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct OccupantCount(usize);

/// An element's position within the sequence spread evenly across a relabel
/// window.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SequencePosition(usize);

/// A test-only ceiling on the number of arena slots a structure may create.
#[cfg(test)]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SlotLimit(usize);

/// The number of live elements in an [`OrderMaintenance`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LiveLen(usize);

impl LiveLen
{
    /// The length of an empty structure.
    const ZERO: Self = Self(0);

    /// This length with one more element, or `None` past the representable
    /// ceiling.
    #[inline]
    fn incremented(self) -> Option<Self>
    {
        self.0.checked_add(1).map(Self)
    }

    /// This length with one fewer element, or `None` when already empty.
    #[inline]
    fn decremented(self) -> Option<Self>
    {
        self.0.checked_sub(1).map(Self)
    }
}

impl From<LiveLen> for usize
{
    #[inline]
    fn from(value: LiveLen) -> Self
    {
        value.0
    }
}

/// Whether an [`OrderMaintenance`] currently has no live elements.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct OrderIsEmpty(bool);

impl From<OrderIsEmpty> for bool
{
    #[inline]
    fn from(value: OrderIsEmpty) -> Self
    {
        value.0
    }
}

/// Whether a handle refers to a live element of an [`OrderMaintenance`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HandleMembership(bool);

impl From<HandleMembership> for bool
{
    #[inline]
    fn from(value: HandleMembership) -> Self
    {
        value.0
    }
}

/// Whether one interval contains another in the maintained order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct IntervalContainment(bool);

impl From<IntervalContainment> for bool
{
    #[inline]
    fn from(value: IntervalContainment) -> Self
    {
        value.0
    }
}

/// An opaque, stable handle to an element of an [`OrderMaintenance`].
///
/// A `Pos` stays valid while *other* elements are inserted, relabeled, and
/// removed; it is invalidated only by removing *its own* element. Handles are
/// generation-checked, so a handle to a removed element does not silently alias
/// a later element that reuses the freed slot — operations on a stale handle
/// report failure (`None` / [`OrderError::UnknownPosition`]) instead.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Pos
{
    /// The identity of the [`OrderMaintenance`] this handle belongs to; a
    /// handle used against a different structure is rejected.
    structure_id: StructureId,
    /// The element's slot index in the arena.
    index: SlotIndex,
    /// The slot generation at the time this handle was minted; a later reuse of
    /// the slot bumps the slot's generation past this value.
    generation: SlotGeneration,
}

/// A failure of an [`OrderMaintenance`] operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OrderError
{
    /// An operation was requested relative to a handle that does not refer to a
    /// live element (it was removed, or it came from a different structure).
    UnknownPosition,
    /// No distinct structure identifier remains. Construction fails rather than
    /// reusing an identifier that could alias an extant [`Pos`].
    StructureIdExhausted,
    /// The structure has reached the maximum number of live, free, or retired
    /// slots representable by [`Pos`], or the label-universe density cap, so no
    /// fresh element can be admitted.
    CapacityExhausted,
    /// An internal invariant of the arena was violated: a live element's link
    /// or label did not resolve. No sequence of public operations produces
    /// this; the variant exists so a corrupted arena surfaces as a typed error
    /// instead of a panic or a silently skipped write.
    Inconsistent,
}

impl core::fmt::Display for OrderError
{
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let message = match *self {
            | Self::UnknownPosition => "order-maintenance operation on an unknown or stale handle",
            | Self::StructureIdExhausted => "order-maintenance structure identifiers are exhausted",
            | Self::CapacityExhausted => "order-maintenance structure is at capacity",
            | Self::Inconsistent => "order-maintenance arena is internally inconsistent",
        };
        f.write_str(message)
    }
}

impl core::error::Error for OrderError
{
}

/// One arena slot: either live, reusable, or permanently retired.
enum Slot<T>
{
    /// A live element.
    Occupied(Occupied<T>),
    /// A freed slot, threaded onto the free list.
    Free(Free),
    /// A slot whose generation space is exhausted and must never be reused.
    Retired,
}

/// A live element's slot payload.
struct Occupied<T>
{
    /// The slot's current generation (matched against a [`Pos`]).
    generation: SlotGeneration,
    /// The element's order label; strictly increasing in list order.
    label: Label,
    /// The previous element in list order, if any.
    prev: Option<SlotIndex>,
    /// The next element in list order, if any.
    next: Option<SlotIndex>,
    /// The caller's payload.
    value: T,
}

/// A freed slot's payload.
struct Free
{
    /// The generation that the next occupant of this slot will carry.
    generation: SlotGeneration,
    /// The next free slot on the free list, if any.
    next_free: Option<SlotIndex>,
}

/// A total order over payload-carrying elements with O(1) comparison.
///
/// See the crate-root documentation for the algorithm and complexity. The
/// structure owns its elements; iteration ([`Self::iter`]) and navigation
/// ([`Self::next`] / [`Self::prev`]) visit them in order.
pub struct OrderMaintenance<T>
{
    /// The element arena, addressed by [`SlotIndex`].
    slots: Vec<Slot<T>>,
    /// The head of the free list (slots available for reuse), if any.
    free_head: Option<SlotIndex>,
    /// Test-only ceiling for representable slots, used to exercise exhaustion
    /// without allocating a `u32::MAX`-sized arena.
    #[cfg(test)]
    slot_limit: Option<SlotLimit>,
    /// The first element in list order, if any.
    head: Option<SlotIndex>,
    /// The last element in list order, if any.
    tail: Option<SlotIndex>,
    /// The number of live elements.
    len: LiveLen,
    /// The label-universe width: labels live in `[0, 2^label_bits)`.
    label_bits: LabelBits,
    /// The label-universe size `2^label_bits`, cached from `label_bits`.
    capacity: LabelCapacity,
    /// This structure's process-unique identity, stamped into every [`Pos`] it
    /// mints (see [`NEXT_STRUCTURE_ID`]).
    structure_id: StructureId,
}

impl<T> OrderMaintenance<T>
{
    /// Creates an empty structure over the default `[0, 2^62)` label universe.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, the structure is empty and its identity is distinct
    ///   from every other structure this process built.
    /// - provides: a total order whose comparison is O(1).
    /// - fails: returns [`OrderError::StructureIdExhausted`] once every
    ///   distinct structure identifier has been issued.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when no distinct structure
    /// id remains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the emptiness postcondition is pinned by exact
    ///   assertions on every observation a fresh structure exposes (length,
    ///   emptiness, both ends, iteration), and the identity postcondition by
    ///   two structures rejecting each other's handles.
    /// - witness: `order::tests::new_is_empty`
    /// - witness: `order::tests::foreign_handle_is_rejected`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|order| order.len() == LiveLen::ZERO))]
    pub fn new() -> Result<Self, OrderError>
    {
        Self::with_label_bits(LabelBits::MAX)
    }

    /// Creates an empty structure over the `[0, 2^label_bits)` label universe,
    /// clamping the requested width into the supported range.
    ///
    /// The narrow-universe form exists for tests that provoke relabeling and
    /// capacity exhaustion without inserting `2^61` elements; in production
    /// [`Self::new`] selects the full universe.
    ///
    /// # Specification
    /// - requires: nothing; the requested width is clamped into the supported
    ///   range before the universe size is computed.
    /// - ensures: on `Ok`, the structure is empty over the clamped universe and
    ///   carries an identity distinct from every other structure this process
    ///   built.
    /// - provides: the narrow-universe constructor the relabel and capacity
    ///   tests drive. The clause checks emptiness and the clamped width;
    ///   identity distinctness stays prose, because it is a law over every
    ///   structure this process built before this call.
    /// - fails: [`OrderError::StructureIdExhausted`] when no distinct structure
    ///   id remains.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when no distinct structure
    /// id remains.
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret
            .as_ref()
            .is_ok_and(|order| order.len() == LiveLen::ZERO
                && order.label_bits == label_bits.clamped()))]
    fn with_label_bits(label_bits: LabelBits) -> Result<Self, OrderError>
    {
        Self::with_label_bits_from_counter(label_bits, &NEXT_STRUCTURE_ID)
    }

    /// Creates an empty structure over the clamped `[0, 2^label_bits)` label
    /// universe, drawing its identity from `counter` instead of the
    /// process-wide [`NEXT_STRUCTURE_ID`].
    ///
    /// The injectable counter exists for tests that exercise structure-id
    /// exhaustion without minting `u64::MAX` structures.
    ///
    /// # Specification
    /// - requires: nothing; the width is clamped into the supported range
    ///   before the universe size is computed.
    /// - ensures: on `Ok`, the structure is empty over the clamped universe and
    ///   its identity is minted from `counter`.
    /// - provides: the constructor the exhaustion tests drive against a bounded
    ///   counter. The clause checks emptiness and the clamped width; the
    ///   identity's provenance stays prose, because `counter` is shared across
    ///   threads and has already advanced when the postcondition runs.
    /// - fails: [`OrderError::StructureIdExhausted`] when `counter` has no
    ///   fresh id; [`OrderError::CapacityExhausted`] on a clamped universe size
    ///   that is not representable, which the clamp range precludes.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when `counter` has no fresh
    /// id to issue, or [`OrderError::CapacityExhausted`] when the clamped
    /// universe size is not representable.
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret
            .as_ref()
            .is_ok_and(|order| order.len() == LiveLen::ZERO
                && order.label_bits == label_bits.clamped()))]
    fn with_label_bits_from_counter(
        label_bits: LabelBits,
        counter: &StructureIdCounter,
    ) -> Result<Self, OrderError>
    {
        let structure_id = counter.allocate()?;
        let bits = label_bits.clamped();
        let capacity = 1u64
            .checked_shl(bits.0)
            .map(LabelCapacity)
            .ok_or(OrderError::CapacityExhausted)?;
        Ok(Self {
            slots: Vec::new(),
            free_head: None,
            #[cfg(test)]
            slot_limit: None,
            head: None,
            tail: None,
            len: LiveLen::ZERO,
            label_bits: bits,
            capacity,
            structure_id,
        })
    }

    /// Creates a structure whose arena may never exceed `slot_limit` slots.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, the structure is empty and its arena may never
    ///   exceed `slot_limit` slots.
    /// - provides: the bounded-arena constructor the retirement tests drive.
    ///   The clause checks emptiness and the installed ceiling; never exceeding
    ///   it stays prose, because that is a law over every later allocation.
    /// - fails: [`OrderError::StructureIdExhausted`] when no distinct structure
    ///   id remains.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when no distinct structure
    /// id remains.
    #[cfg(test)]
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret
            .as_ref()
            .is_ok_and(|order| order.len() == LiveLen::ZERO
                && order.slot_limit == Some(slot_limit)))]
    fn with_label_bits_and_slot_limit(
        label_bits: LabelBits,
        slot_limit: SlotLimit,
    ) -> Result<Self, OrderError>
    {
        let mut order = Self::with_label_bits(label_bits)?;
        order.slot_limit = Some(slot_limit);
        Ok(order)
    }

    /// The number of live elements.
    #[inline]
    #[must_use]
    pub fn len(&self) -> LiveLen
    {
        self.len
    }

    /// Whether the structure has no live elements.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> OrderIsEmpty
    {
        OrderIsEmpty(self.len == LiveLen::ZERO)
    }

    /// The first element in order, if any.
    #[inline]
    #[must_use]
    pub fn first(&self) -> Option<Pos>
    {
        let index = self.head?;
        self.pos_at(index)
    }

    /// The last element in order, if any.
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<Pos>
    {
        let index = self.tail?;
        self.pos_at(index)
    }

    /// Whether `pos` refers to a live element of this structure.
    #[inline]
    #[must_use]
    pub fn contains(
        &self,
        pos: Pos,
    ) -> HandleMembership
    {
        HandleMembership(self.resolve(pos).is_some())
    }

    /// The payload of `pos`, or `None` if the handle is stale or foreign.
    ///
    /// # Specification
    /// - requires: nothing; any handle may be offered.
    /// - ensures: returns `Some(&value)` exactly when `pos` refers to a live
    ///   element of this structure.
    /// - provides: borrowed access to the caller's payload. The clause checks
    ///   that a payload is returned exactly when the handle is live.
    /// - fails: returns `None` for a removed, generation-stale, or foreign
    ///   handle.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the two guards inside [`Self::resolve`]
    ///   (structure identity, generation match) are separated by a removed
    ///   handle, a handle whose slot was reused at a bumped generation, and a
    ///   handle from a second structure, each paired with the exact payload or
    ///   `None`.
    /// - witness: `order::tests::remove_middle_unlinks_and_invalidates`
    /// - witness: `order::tests::slot_reuse_distinguishes_generation`
    /// - witness: `order::tests::foreign_handle_is_rejected`
    // The caller may supply any handle; rejection is a returned absence.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == bool::from(self.contains(pos)))]
    pub fn get(
        &self,
        pos: Pos,
    ) -> Option<&T>
    {
        let occupied = self.resolve(pos)?;
        Some(&occupied.value)
    }

    /// Compares two elements in the order, in O(1).
    ///
    /// # Specification
    /// - requires: `left` and `right` are handles to this structure.
    /// - ensures: returns `Some(ordering)` giving the relative list order of
    ///   the two elements; `Some(Equal)` exactly when both handles refer to the
    ///   same live element, so distinct live elements never compare `Equal`.
    /// - provides: the total order the structure exists to maintain. The clause
    ///   checks the label comparison of the two resolved elements and the
    ///   reflexive arm; the precondition stays prose, because liveness is
    ///   answered here rather than assumed — a stale or foreign handle returns
    ///   `None` instead of tripping a check.
    /// - fails: returns `None` if either handle is stale or foreign.
    /// - panics: none.
    /// - intension: one integer comparison of the two labels, independent of
    ///   the number of elements between them.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for the ordering itself — every pair of handles is
    ///   compared against the rank pair in a naive `Vec` model after every
    ///   generated edit, so any mutant that perturbs a label or the comparison
    ///   direction diverges; L3 residue for the reflexive and failure arms,
    ///   pinned by exact `Ordering` variants and a foreign handle.
    /// - witness: `oracle::oracle::matches_reference_model`
    /// - witness: `order::tests::comparison_is_reflexive_and_total`
    /// - witness: `order::tests::foreign_handle_is_rejected`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret
        == self
            .resolve(left)
            .zip(self.resolve(right))
            .map(|(first, second)| first.label.cmp(&second.label))
        && (ret == Some(Ordering::Equal))
            == (left == right && bool::from(self.contains(left))))]
    pub fn cmp(
        &self,
        left: Pos,
        right: Pos,
    ) -> Option<Ordering>
    {
        let left_occupied = self.resolve(left)?;
        let right_occupied = self.resolve(right)?;
        Some(left_occupied.label.cmp(&right_occupied.label))
    }

    /// The element immediately after `pos` in order, or `None` at the end (or
    /// if the handle is stale or foreign).
    #[inline]
    #[must_use]
    pub fn next(
        &self,
        pos: Pos,
    ) -> Option<Pos>
    {
        let occupied = self.resolve(pos)?;
        let next_index = occupied.next?;
        self.pos_at(next_index)
    }

    /// The element immediately before `pos` in order, or `None` at the start
    /// (or if the handle is stale or foreign).
    #[inline]
    #[must_use]
    pub fn prev(
        &self,
        pos: Pos,
    ) -> Option<Pos>
    {
        let occupied = self.resolve(pos)?;
        let prev_index = occupied.prev?;
        self.pos_at(prev_index)
    }

    /// Iterates `(handle, &payload)` over every element in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields exactly the live elements, each once, in list order,
    ///   and each handle resolves to the payload it is paired with.
    /// - provides: the in-order view every structural oracle reads. The
    ///   postcondition stays prose: it quantifies over the walk the returned
    ///   iterator has yet to perform, which no predicate at this exit can
    ///   observe.
    /// - fails: the walk stops early rather than looping if a link does not
    ///   resolve, which no sequence of public operations produces.
    /// - panics: none.
    /// - intension: a single forward pass over the `next` links, holding one
    ///   slot index of state.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the yielded payload sequence and the yielded handle
    ///   sequence are both compared against a naive `Vec` model after every
    ///   generated edit, so any mutant that drops, repeats, or reorders an
    ///   element diverges; L3 residue for the empty structure.
    /// - witness: `oracle::oracle::matches_reference_model`
    /// - witness: `order::tests::new_is_empty`
    #[inline]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T>
    {
        Iter {
            order: self,
            cursor: self.head,
        }
    }

    /// Inserts `value` as the first element in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, `value` is the new first element, everything already
    ///   present keeps its relative order, and the returned handle refers to
    ///   the new element.
    /// - provides: the handle for the inserted element.
    /// - fails: [`OrderError::CapacityExhausted`] when no element can be
    ///   admitted; [`OrderError::Inconsistent`] on a corrupted arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when the structure is full.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the reference model inserts at index 0 and the whole
    ///   handle and payload sequence is compared after every generated edit; L3
    ///   residue for the front relabel arm, where the predecessor is absent, on
    ///   a narrow universe whose front gap is exhausted.
    /// - witness: `oracle::oracle::matches_reference_model`
    /// - witness: `order::tests::push_front_reverses`
    /// - witness: `order::tests::relabel_at_front_preserves_order`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || self.first() == ret.ok())]
    pub fn push_front(
        &mut self,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        self.insert_between(None, self.head, value)
    }

    /// Inserts `value` as the last element in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, `value` is the new last element, everything already
    ///   present keeps its relative order, and the returned handle refers to
    ///   the new element.
    /// - provides: the handle for the inserted element.
    /// - fails: [`OrderError::CapacityExhausted`] when no element can be
    ///   admitted; [`OrderError::Inconsistent`] on a corrupted arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when the structure is full.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the reference model appends and the whole handle and
    ///   payload sequence is compared after every generated edit; L3 residue
    ///   for the capacity boundary, where a two-bit universe admits exactly two
    ///   elements and refuses the third with the exact error variant.
    /// - witness: `oracle::oracle::matches_reference_model`
    /// - witness: `order::tests::push_back_preserves_order`
    /// - witness: `order::tests::capacity_exhausts_in_a_tiny_universe`
    /// - witness: `order::tests::retired_slot_capacity_exhaustion_is_typed`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || self.last() == ret.ok())]
    pub fn push_back(
        &mut self,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        self.insert_between(self.tail, None, value)
    }

    /// Inserts `value` immediately after `pos` in order.
    ///
    /// # Specification
    /// - requires: `pos` is a live handle to this structure.
    /// - ensures: on `Ok`, `value` sits immediately after `pos` and before
    ///   whatever previously followed `pos`; the returned handle refers to it
    ///   and every pre-existing handle keeps resolving.
    /// - provides: the handle for the inserted element. The clause checks the
    ///   placement, the element that previously followed `pos`, and the
    ///   returned handle's liveness; the precondition stays prose, because
    ///   liveness is reported as [`OrderError::UnknownPosition`] rather than
    ///   assumed, and the surviving-handle claim stays prose, because it
    ///   quantifies over every handle this structure ever minted.
    /// - fails: [`OrderError::UnknownPosition`] if `pos` is stale or foreign;
    ///   [`OrderError::CapacityExhausted`] if no element can be admitted;
    ///   [`OrderError::Inconsistent`] on a corrupted arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::UnknownPosition`] for a stale handle and
    /// [`OrderError::CapacityExhausted`] when the structure is full.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for placement — the reference model inserts at `index +
    ///   1` and the whole sequence is compared after every generated edit; L3
    ///   residue for the stale-handle and foreign-handle arms, pinned by the
    ///   exact error variant, and for the relabel arm, driven by repeated
    ///   insertion behind one fixed anchor.
    /// - witness: `oracle::oracle::matches_reference_model`
    /// - witness: `order::tests::insert_after_and_before_place_correctly`
    /// - witness: `order::tests::relabel_after_anchor_preserves_order`
    /// - witness: `order::tests::stale_handle_insert_errors`
    /// - witness: `order::tests::foreign_handle_is_rejected`
    /// - witness: `order::tests::corrupt_link_insert_is_typed`
    #[inline]
    #[spec(
        captures: followed = self.next(pos),
        ensures: |ret| ret.as_ref().ok().is_none_or(|inserted| self.next(pos) == Some(*inserted)
            && self.next(*inserted) == followed
            && bool::from(self.contains(*inserted))),
    )]
    pub fn insert_after(
        &mut self,
        pos: Pos,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        let occupied = self.resolve(pos).ok_or(OrderError::UnknownPosition)?;
        let next_index = occupied.next;
        self.insert_between(Some(pos.index), next_index, value)
    }

    /// Inserts `value` immediately before `pos` in order.
    ///
    /// # Specification
    /// - requires: `pos` is a live handle to this structure.
    /// - ensures: on `Ok`, `value` sits immediately before `pos` and after
    ///   whatever previously preceded `pos`; the returned handle refers to it
    ///   and every pre-existing handle keeps resolving.
    /// - provides: the handle for the inserted element. The clause checks the
    ///   placement, the element that previously preceded `pos`, and the
    ///   returned handle's liveness; the precondition and the surviving-handle
    ///   claim stay prose for the same two reasons as [`Self::insert_after`].
    /// - fails: [`OrderError::UnknownPosition`] if `pos` is stale or foreign;
    ///   [`OrderError::CapacityExhausted`] if no element can be admitted;
    ///   [`OrderError::Inconsistent`] on a corrupted arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::UnknownPosition`] for a stale handle and
    /// [`OrderError::CapacityExhausted`] when the structure is full.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for placement — the reference model inserts at `index`
    ///   and the whole sequence is compared after every generated edit; L3
    ///   residue for the stale-handle arm, pinned by the exact error variant.
    /// - witness: `oracle::oracle::matches_reference_model`
    /// - witness: `order::tests::insert_after_and_before_place_correctly`
    /// - witness: `order::tests::stale_handle_insert_errors`
    #[inline]
    #[spec(
        captures: preceded = self.prev(pos),
        ensures: |ret| ret.as_ref().ok().is_none_or(|inserted| self.prev(pos) == Some(*inserted)
            && self.prev(*inserted) == preceded
            && bool::from(self.contains(*inserted))),
    )]
    pub fn insert_before(
        &mut self,
        pos: Pos,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        let occupied = self.resolve(pos).ok_or(OrderError::UnknownPosition)?;
        let prev_index = occupied.prev;
        self.insert_between(prev_index, Some(pos.index), value)
    }

    /// Removes the element `pos` refers to, returning its payload.
    ///
    /// # Specification
    /// - requires: nothing; any handle may be offered.
    /// - ensures: on `Ok(Some(value))` the element is unlinked, its slot is
    ///   freed for reuse (or retired when its generation space is spent), and
    ///   `pos` together with every copy of it is thereafter stale; the
    ///   remaining elements keep their relative order and their handles.
    /// - provides: the removed payload by value. The clause checks, on
    ///   `Ok(Some(_))`, that `pos` is stale, that its slot is on the free list
    ///   or retired, that its former neighbours are now adjacent, and that an
    ///   absent neighbour moved the corresponding end; the relative order of
    ///   the remaining elements stays prose, because it quantifies over every
    ///   surviving handle.
    /// - fails: returns `Ok(None)` if `pos` is stale or foreign, and
    ///   [`OrderError::Inconsistent`] on a corrupted arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when a neighbour link of the
    /// removed element does not resolve to a live slot.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for the unlinking — the reference model removes at the
    ///   same index and the whole handle and payload sequence is compared after
    ///   every generated edit; L3 residue for the three link arms (interior,
    ///   head, tail), the sole-element arm, the repeat-removal arm, and the
    ///   generation-exhaustion arm that retires a slot instead of freeing it.
    /// - witness: `oracle::oracle::matches_reference_model`
    /// - witness: `order::tests::remove_middle_unlinks_and_invalidates`
    /// - witness: `order::tests::remove_head_and_tail`
    /// - witness: `order::tests::remove_only_element_empties`
    /// - witness: `order::tests::exhausted_generation_retires_slot_and_allocates_another`
    /// - witness: `order::tests::corrupt_link_removal_is_typed`
    #[inline]
    #[spec(
        captures: [preceded = self.prev(pos), followed = self.next(pos)],
        ensures: |ret| !ret.as_ref().is_ok_and(Option::is_some)
            || (!bool::from(self.contains(pos))
                && (self.free_head == Some(pos.index)
                    || matches!(self.slot(pos.index), Some(&Slot::Retired)))
                && preceded.is_none_or(|earlier| self.next(earlier) == followed)
                && followed.is_none_or(|later| self.prev(later) == preceded)
                && (preceded.is_some() || self.first() == followed)
                && (followed.is_some() || self.last() == preceded)),
    )]
    pub fn remove(
        &mut self,
        pos: Pos,
    ) -> Result<Option<T>, OrderError>
    {
        let Some(occupied) = self.resolve(pos)
        else {
            return Ok(None);
        };
        let prev_index = occupied.prev;
        let next_index = occupied.next;
        let generation = occupied.generation;
        let len = self.len.decremented().ok_or(OrderError::Inconsistent)?;
        // Unlink from the neighbours and the head/tail before freeing the slot.
        match prev_index {
            | Some(prev) => self.set_next(prev, next_index)?,
            | None => self.head = next_index,
        }
        match next_index {
            | Some(next) => self.set_prev(next, prev_index)?,
            | None => self.tail = prev_index,
        }
        let slot_position =
            usize::try_from(pos.index).map_err(|_ignored| OrderError::Inconsistent)?;
        let slot = self
            .slots
            .get_mut(slot_position)
            .ok_or(OrderError::Inconsistent)?;
        // A slot whose generation space is spent is retired rather than reused,
        // so a handle carrying the final generation can never be re-minted.
        let successor = generation.successor();
        let replacement = match successor {
            | Some(free_generation) => Slot::Free(Free {
                generation: free_generation,
                next_free: self.free_head,
            }),
            | None => Slot::Retired,
        };
        let freed = core::mem::replace(slot, replacement);
        if successor.is_some() {
            self.free_head = Some(pos.index);
        }
        self.len = len;
        match freed {
            | Slot::Occupied(occupied_slot) => Ok(Some(occupied_slot.value)),
            | Slot::Free(_) | Slot::Retired => Err(OrderError::Inconsistent),
        }
    }

    /// Tests whether `outer` contains `inner` as pre/post-order intervals: a
    /// tree node whose interval is `[lo, hi]` contains another exactly when its
    /// `lo` is no later and its `hi` no earlier.
    ///
    /// # Specification
    /// - requires: all four endpoints are live handles to this structure, and
    ///   each interval's `lo` is no later than its `hi`.
    /// - ensures: returns `Some` wrapping containment exactly when `outer.lo <=
    ///   inner.lo` and `inner.hi <= outer.hi` in the order, so an interval
    ///   contains itself.
    /// - provides: the constant-time subtree-enclosure test the incremental
    ///   consumer schedules from. The clause checks both bounds and their
    ///   inclusivity; the precondition stays prose, because a stale endpoint is
    ///   answered with `None` here, and an interval's own well-formedness is
    ///   established where its endpoints are minted.
    /// - fails: returns `None` if any endpoint is stale or foreign.
    /// - panics: none.
    /// - intension: two label comparisons, independent of interval width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the two conjoined bounds and their inclusivity
    ///   form a finite decision class, enumerated over nested, reversed,
    ///   disjoint, and identical interval pairs with the exact boolean
    ///   asserted, plus a stale endpoint pinning the failure arm.
    /// - witness: `order::tests::interval_containment`
    /// - witness: `order::tests::interval_with_stale_endpoint_is_none`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret
        == self
            .cmp(outer.lo, inner.lo)
            .zip(self.cmp(inner.hi, outer.hi))
            .map(|(lo_ordering, hi_ordering)| IntervalContainment(
                lo_ordering.is_le() && hi_ordering.is_le(),
            )))]
    pub fn interval_contains(
        &self,
        outer: crate::interval::Interval,
        inner: crate::interval::Interval,
    ) -> Option<IntervalContainment>
    {
        let lo_ordering = self.cmp(outer.lo, inner.lo)?;
        let hi_ordering = self.cmp(inner.hi, outer.hi)?;
        Some(IntervalContainment(
            lo_ordering.is_le() && hi_ordering.is_le(),
        ))
    }

    // ----- internal helpers ------------------------------------------------

    /// The handle for slot `index`, if the slot is occupied.
    #[inline]
    fn pos_at(
        &self,
        index: SlotIndex,
    ) -> Option<Pos>
    {
        let occupied = self.occupied(index)?;
        Some(Pos {
            structure_id: self.structure_id,
            index,
            generation: occupied.generation,
        })
    }

    /// The slot at `index`, if the arena has one.
    #[inline]
    fn slot(
        &self,
        index: SlotIndex,
    ) -> Option<&Slot<T>>
    {
        let position = usize::try_from(index).ok()?;
        self.slots.get(position)
    }

    /// The occupied payload at `index`, if the slot exists and is occupied.
    #[inline]
    fn occupied(
        &self,
        index: SlotIndex,
    ) -> Option<&Occupied<T>>
    {
        match *self.slot(index)? {
            | Slot::Occupied(ref occupied) => Some(occupied),
            | Slot::Free(_) | Slot::Retired => None,
        }
    }

    /// The mutable occupied payload at `index`, if the slot exists and is
    /// occupied.
    #[inline]
    fn occupied_mut(
        &mut self,
        index: SlotIndex,
    ) -> Option<&mut Occupied<T>>
    {
        let position = usize::try_from(index).ok()?;
        let slot = self.slots.get_mut(position)?;
        match *slot {
            | Slot::Occupied(ref mut occupied) => Some(occupied),
            | Slot::Free(_) | Slot::Retired => None,
        }
    }

    /// The occupied payload `pos` refers to, if the handle is live: same
    /// structure, occupied slot, matching generation.
    #[inline]
    fn resolve(
        &self,
        pos: Pos,
    ) -> Option<&Occupied<T>>
    {
        if pos.structure_id != self.structure_id {
            return None;
        }
        let occupied = self.occupied(pos.index)?;
        (occupied.generation == pos.generation).then_some(occupied)
    }

    /// The label of the occupied slot at `index`, if any.
    #[inline]
    fn label_of(
        &self,
        index: SlotIndex,
    ) -> Option<Label>
    {
        let occupied = self.occupied(index)?;
        Some(occupied.label)
    }

    /// Sets the `prev` link of the occupied slot at `index`.
    ///
    /// # Specification
    /// - requires: `index` names a live slot.
    /// - ensures: the `prev` link is written when it can resolve, and an
    ///   unresolvable write is reported rather than dropped.
    /// - provides: the checked `prev` write every unlink and relink routes
    ///   through. The precondition stays prose, because a dead index is
    ///   answered as [`OrderError::Inconsistent`] rather than assumed.
    /// - fails: [`OrderError::Inconsistent`] when `index` does not name a live
    ///   slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when `index` does not name a live
    /// slot, rather than dropping the write.
    #[inline]
    #[spec(ensures: |ret| ret.is_ok()
        == self
            .occupied(index)
            .is_some_and(|occupied| occupied.prev == prev))]
    fn set_prev(
        &mut self,
        index: SlotIndex,
        prev: Option<SlotIndex>,
    ) -> Result<(), OrderError>
    {
        let occupied = self.occupied_mut(index).ok_or(OrderError::Inconsistent)?;
        occupied.prev = prev;
        Ok(())
    }

    /// Sets the `next` link of the occupied slot at `index`.
    ///
    /// # Specification
    /// - requires: `index` names a live slot.
    /// - ensures: the `next` link is written when it can resolve, and an
    ///   unresolvable write is reported rather than dropped.
    /// - provides: the checked `next` write every unlink and relink routes
    ///   through. The precondition stays prose, because a dead index is
    ///   answered as [`OrderError::Inconsistent`] rather than assumed.
    /// - fails: [`OrderError::Inconsistent`] when `index` does not name a live
    ///   slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when `index` does not name a live
    /// slot, rather than dropping the write.
    #[inline]
    #[spec(ensures: |ret| ret.is_ok()
        == self
            .occupied(index)
            .is_some_and(|occupied| occupied.next == next))]
    fn set_next(
        &mut self,
        index: SlotIndex,
        next: Option<SlotIndex>,
    ) -> Result<(), OrderError>
    {
        let occupied = self.occupied_mut(index).ok_or(OrderError::Inconsistent)?;
        occupied.next = next;
        Ok(())
    }

    /// Sets the `label` of the occupied slot at `index`.
    ///
    /// # Specification
    /// - requires: `index` names a live slot.
    /// - ensures: the `label` is written when it can resolve, and an
    ///   unresolvable write is reported rather than dropped, so the
    ///   strictly-increasing label invariant cannot be violated silently.
    /// - provides: the checked label write the relabel routes through. The
    ///   precondition stays prose, because a dead index is answered as
    ///   [`OrderError::Inconsistent`] rather than assumed.
    /// - fails: [`OrderError::Inconsistent`] when `index` does not name a live
    ///   slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when `index` does not name a live
    /// slot, rather than dropping the write and leaving a label that violates
    /// the strictly-increasing invariant.
    #[inline]
    #[spec(ensures: |ret| ret.is_ok()
        == self
            .occupied(index)
            .is_some_and(|occupied| occupied.label == label))]
    fn set_label(
        &mut self,
        index: SlotIndex,
        label: Label,
    ) -> Result<(), OrderError>
    {
        let occupied = self.occupied_mut(index).ok_or(OrderError::Inconsistent)?;
        occupied.label = label;
        Ok(())
    }

    /// Allocates a slot holding `value` with the given label and links, reusing
    /// a freed slot when one is available and appending otherwise.
    ///
    /// The neighbours' links and the structure's head/tail are *not* patched
    /// here — the caller wires them — but `len` is incremented for the new
    /// element.
    ///
    /// # Specification
    /// - requires: `prev` and `next` are the insertion point's live neighbours,
    ///   either `None` at a list end.
    /// - ensures: on `Ok`, a slot holding `value` with `label` is threaded
    ///   between the two, `len` is incremented, and the returned handle
    ///   resolves to the new element.
    /// - provides: the fresh handle every insertion returns. Both lines stay
    ///   prose: the relabel path allocates with both links absent and wires
    ///   them afterwards, so the neighbour precondition is not a fact at every
    ///   call site, and the postcondition speaks of `value`, which is moved
    ///   into the slot.
    /// - fails: [`OrderError::CapacityExhausted`] when no `u32` slot index is
    ///   available; [`OrderError::Inconsistent`] when the free list threads a
    ///   slot that is not free.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no `u32` slot index is
    /// available, and [`OrderError::Inconsistent`] when the free list threads a
    /// slot that is not free.
    #[inline]
    fn alloc(
        &mut self,
        label: Label,
        prev: Option<SlotIndex>,
        next: Option<SlotIndex>,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        let len = self
            .len
            .incremented()
            .ok_or(OrderError::CapacityExhausted)?;
        if let Some(free_index) = self.free_head {
            let free_position =
                usize::try_from(free_index).map_err(|_ignored| OrderError::Inconsistent)?;
            let slot = self
                .slots
                .get_mut(free_position)
                .ok_or(OrderError::Inconsistent)?;
            let free = match *slot {
                | Slot::Free(ref free) => Free {
                    generation: free.generation,
                    next_free: free.next_free,
                },
                | Slot::Occupied(_) | Slot::Retired => return Err(OrderError::Inconsistent),
            };
            *slot = Slot::Occupied(Occupied {
                generation: free.generation,
                label,
                prev,
                next,
                value,
            });
            self.free_head = free.next_free;
            self.len = len;
            return Ok(Pos {
                structure_id: self.structure_id,
                index: free_index,
                generation: free.generation,
            });
        }
        #[cfg(test)]
        if self
            .slot_limit
            .is_some_and(|limit| self.slots.len() >= limit.0)
        {
            return Err(OrderError::CapacityExhausted);
        }
        let index = SlotIndex::try_from(self.slots.len())
            .map_err(|_ignored| OrderError::CapacityExhausted)?;
        self.slots.push(Slot::Occupied(Occupied {
            generation: SlotGeneration::FIRST,
            label,
            prev,
            next,
            value,
        }));
        self.len = len;
        Ok(Pos {
            structure_id: self.structure_id,
            index,
            generation: SlotGeneration::FIRST,
        })
    }

    /// Inserts `value` between the adjacent elements `prev_index` and
    /// `next_index` (either may be `None` at a list end; both `None` only for
    /// an empty structure).
    ///
    /// Takes the midpoint of the neighbours' label gap when one exists,
    /// otherwise relabels a minimal aligned window to open room (see
    /// [`Self::relabel_insert`]).
    ///
    /// # Specification
    /// - requires: `prev_index` and `next_index` are adjacent in list order,
    ///   either `None` at a list end; both `None` only for an empty structure.
    /// - ensures: on `Ok`, `value` sits between the two, labels remain strictly
    ///   increasing in list order, and the returned handle resolves to the new
    ///   element.
    /// - provides: the insertion every public insert routes through. The clause
    ///   checks the adjacency each call site reads — the predecessor's own
    ///   `next` link, or the end the structure records — while the
    ///   postcondition stays prose, because strict label increase is a property
    ///   of the whole list and `value` is moved into the slot.
    /// - fails: [`OrderError::CapacityExhausted`] when no element can be
    ///   admitted; [`OrderError::Inconsistent`] when a neighbour index does not
    ///   name a live slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no element can be
    /// admitted, and [`OrderError::Inconsistent`] when a neighbour index does
    /// not name a live slot.
    #[inline]
    #[spec(requires: match (prev_index, next_index) {
        (Some(prev), Some(next)) => self
            .occupied(prev)
            .is_some_and(|occupied| occupied.next == Some(next)),
        (Some(prev), None) => self.tail == Some(prev),
        (None, Some(next)) => self.head == Some(next),
        (None, None) => self.len == LiveLen::ZERO,
    })]
    fn insert_between(
        &mut self,
        prev_index: Option<SlotIndex>,
        next_index: Option<SlotIndex>,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        // The lowest admissible label sits just above the predecessor (or at
        // zero); the exclusive upper bound is the successor's label (or the
        // universe size).
        let mut lower = Label::ZERO;
        if let Some(prev) = prev_index {
            let prev_label = self.label_of(prev).ok_or(OrderError::Inconsistent)?;
            let above = prev_label
                .0
                .checked_add(1)
                .ok_or(OrderError::CapacityExhausted)?;
            lower = Label(above);
        }
        let mut upper = Label(self.capacity.0);
        if let Some(next) = next_index {
            upper = self.label_of(next).ok_or(OrderError::Inconsistent)?;
        }
        if lower < upper {
            let label = Label(u64::midpoint(lower.0, upper.0));
            return self.link_new(prev_index, next_index, label, value);
        }
        self.relabel_insert(prev_index, next_index, value)
    }

    /// Allocates `value` with `label` and wires it between `prev_index` and
    /// `next_index`, updating the neighbours' links and the head/tail.
    ///
    /// # Specification
    /// - requires: `prev_index` and `next_index` are adjacent in list order,
    ///   either `None` at a list end.
    /// - ensures: on `Ok`, `value` with `label` is wired between the two, the
    ///   neighbours' links and the head/tail are updated, and the returned
    ///   handle resolves to the new element.
    /// - provides: the linked element's handle. The clauses check the caller's
    ///   adjacency and the whole wiring — the new element's label and links,
    ///   both neighbours' back-links, and the head or tail an absent neighbour
    ///   moves — while the payload identity stays prose, because `value` is
    ///   moved into the slot.
    /// - fails: [`OrderError::CapacityExhausted`] when no slot is available;
    ///   [`OrderError::Inconsistent`] when a neighbour index does not name a
    ///   live slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no slot is available, and
    /// [`OrderError::Inconsistent`] when a neighbour index does not name a live
    /// slot.
    #[inline]
    #[spec(
        requires: match (prev_index, next_index) {
            (Some(prev), Some(next)) => self
                .occupied(prev)
                .is_some_and(|occupied| occupied.next == Some(next)),
            (Some(prev), None) => self.tail == Some(prev),
            (None, Some(next)) => self.head == Some(next),
            (None, None) => self.head.is_none() && self.tail.is_none(),
        },
        ensures: |ret| ret.as_ref().ok().is_none_or(|pos| self
            .resolve(*pos)
            .is_some_and(|occupied| occupied.label == label
                && occupied.prev == prev_index
                && occupied.next == next_index)
            && prev_index.is_none_or(|prev| self
                .occupied(prev)
                .is_some_and(|occupied| occupied.next == Some(pos.index)))
            && next_index.is_none_or(|next| self
                .occupied(next)
                .is_some_and(|occupied| occupied.prev == Some(pos.index)))
            && (prev_index.is_some() || self.head == Some(pos.index))
            && (next_index.is_some() || self.tail == Some(pos.index))),
    )]
    fn link_new(
        &mut self,
        prev_index: Option<SlotIndex>,
        next_index: Option<SlotIndex>,
        label: Label,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        let pos = self.alloc(label, prev_index, next_index, value)?;
        match prev_index {
            | Some(prev) => self.set_next(prev, Some(pos.index))?,
            | None => self.head = Some(pos.index),
        }
        match next_index {
            | Some(next) => self.set_prev(next, Some(pos.index))?,
            | None => self.tail = Some(pos.index),
        }
        Ok(pos)
    }

    /// Opens room for a new element between `prev_index` and `next_index` by
    /// relabeling the smallest power-of-two-aligned label window around the
    /// insertion point that is at most half full, then inserting `value` into
    /// the evenly-redistributed window.
    ///
    /// At least one neighbour is `Some` here — the empty and gap-available
    /// cases are handled by [`Self::insert_between`]. The widening loop is
    /// bounded by the universe width, and the density cap guarantees the
    /// whole-universe window is sparse enough whenever the structure is below
    /// that cap.
    ///
    /// One `Vec` is allocated for the window and reused across the widening
    /// steps, so a relabel allocates once regardless of how far it widens.
    ///
    /// # Specification
    /// - requires: at least one of `prev_index` and `next_index` is `Some`, and
    ///   the walked segment's links and labels all resolve.
    /// - ensures: on `Ok`, `value` sits between the two and the relabeled
    ///   window's labels are distinct, strictly increasing, and strictly inside
    ///   the window.
    /// - provides: the handle of the inserted element. Both lines stay prose:
    ///   the precondition's walk-integrity half is answered as
    ///   [`OrderError::Inconsistent`] rather than assumed, so a clause carrying
    ///   only its anchor half would be weaker than the line; and the relabeled
    ///   window is a local buffer by the time the postcondition runs.
    /// - fails: [`OrderError::CapacityExhausted`] when even the whole-universe
    ///   window cannot hold the new element at density one half, or when no
    ///   slot is available; [`OrderError::Inconsistent`] when a link or label
    ///   in the walked segment does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when even the whole-universe
    /// window cannot accommodate the new element at density one half, or when
    /// no slot is available; [`OrderError::Inconsistent`] when a link or label
    /// in the walked segment does not resolve.
    #[inline]
    fn relabel_insert(
        &mut self,
        prev_index: Option<SlotIndex>,
        next_index: Option<SlotIndex>,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        let anchor = prev_index.or(next_index).ok_or(OrderError::Inconsistent)?;
        let anchor_label = self.label_of(anchor).ok_or(OrderError::Inconsistent)?;
        let mut window: Vec<SlotIndex> = Vec::new();
        let mut height = LabelBits::MIN;
        while height <= self.label_bits {
            let range_size = 1u64
                .checked_shl(height.0)
                .map(LabelRangeSize)
                .ok_or(OrderError::CapacityExhausted)?;
            // The aligned window `[start, start + range_size)` containing the
            // anchor: clear the low `height` bits of the anchor's label.
            let start = anchor_label
                .0
                .checked_shr(height.0)
                .and_then(|shifted| shifted.checked_shl(height.0))
                .map(Label)
                .ok_or(OrderError::CapacityExhausted)?;
            let end = start
                .0
                .checked_add(range_size.0)
                .map(Label)
                .ok_or(OrderError::CapacityExhausted)?;
            self.collect_window(&mut window, anchor, start, end)?;
            // The new element plus the window's existing elements must fit at
            // density at most one half, so the even redistribution leaves gaps:
            // `2 * occupants <= range_size`.
            let occupants = window
                .len()
                .checked_add(1)
                .map(OccupantCount)
                .ok_or(OrderError::CapacityExhausted)?;
            let doubled = u64::try_from(occupants.0)
                .ok()
                .and_then(|count| count.checked_mul(2));
            if doubled.is_some_and(|value| value <= range_size.0) {
                return self.redistribute(&window, prev_index, start, range_size, occupants, value);
            }
            height = height.wider().ok_or(OrderError::CapacityExhausted)?;
        }
        Err(OrderError::CapacityExhausted)
    }

    /// Fills `window` with, in list order, every element whose label lies in
    /// `[start, end)` around `anchor` (whose own label is in the range).
    ///
    /// The result is a contiguous list segment because labels increase in list
    /// order. `window` is cleared first, so one buffer serves every widening
    /// step of a relabel.
    ///
    /// # Specification
    /// - requires: `anchor`'s label lies in `[start, end)`, and the walked
    ///   segment's links resolve.
    /// - ensures: `window` holds, in list order, exactly the elements whose
    ///   labels lie in `[start, end)`.
    /// - provides: the contiguous segment one redistribution consumes. Both
    ///   lines stay prose: the walk's integrity is answered as
    ///   [`OrderError::Inconsistent`] rather than assumed, and the window's
    ///   exactness is a claim about every element of the list, which a
    ///   predicate could only recheck by walking it again.
    /// - fails: [`OrderError::Inconsistent`] when a link in the walked segment
    ///   points at a slot that is not live.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when a link in the walked segment
    /// points at a slot that is not live.
    #[inline]
    fn collect_window(
        &self,
        window: &mut Vec<SlotIndex>,
        anchor: SlotIndex,
        start: Label,
        end: Label,
    ) -> Result<(), OrderError>
    {
        window.clear();
        // Walk left to the first in-range element.
        let mut leftmost = anchor;
        loop {
            let occupied = self.occupied(leftmost).ok_or(OrderError::Inconsistent)?;
            let Some(prev) = occupied.prev
            else {
                break;
            };
            let prev_label = self.label_of(prev).ok_or(OrderError::Inconsistent)?;
            if prev_label < start {
                break;
            }
            leftmost = prev;
        }
        // Walk right from the leftmost, collecting while in range.
        let mut cursor = Some(leftmost);
        while let Some(index) = cursor {
            let occupied = self.occupied(index).ok_or(OrderError::Inconsistent)?;
            if occupied.label >= end {
                break;
            }
            window.push(index);
            cursor = occupied.next;
        }
        Ok(())
    }

    /// Redistributes the `window` elements plus the new `value` evenly across
    /// the aligned label range `[start, start + range_size)` and wires the
    /// resulting contiguous segment back into the list.
    ///
    /// `occupants == window.len() + 1` and `2 * occupants <= range_size` (the
    /// caller's density check), so the assigned labels are distinct, strictly
    /// increasing, and strictly inside the range — which preserves the global
    /// order against the un-relabeled neighbours just outside it.
    ///
    /// # Specification
    /// - requires: `occupants == window.len() + 1` and `2 * occupants <=
    ///   range_size` (the caller's density check).
    /// - ensures: on `Ok`, the `window` elements plus `value` occupy
    ///   `occupants` evenly spaced labels inside the range, wired back as one
    ///   contiguous segment.
    /// - provides: the handle of the new element. The clause checks the
    ///   caller's density arithmetic; the postcondition stays prose here,
    ///   because [`Self::assign_labels`] and [`Self::relink_segment`] carry the
    ///   spread and the wiring as their own clauses, and `value` is moved into
    ///   the slot.
    /// - fails: [`OrderError::CapacityExhausted`] when no slot is available for
    ///   the new element; [`OrderError::Inconsistent`] when the window does not
    ///   contain the predecessor or does not cover `occupants` positions.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no slot is available for
    /// the new element, and [`OrderError::Inconsistent`] when the window does
    /// not contain the predecessor or does not cover `occupants` positions.
    #[inline]
    #[spec(requires: window.len().checked_add(1) == Some(occupants.0)
        && u64::try_from(occupants.0)
            .is_ok_and(|count| count.saturating_mul(2) <= range_size.0))]
    fn redistribute(
        &mut self,
        window: &[SlotIndex],
        prev_index: Option<SlotIndex>,
        start: Label,
        range_size: LabelRangeSize,
        occupants: OccupantCount,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        // The new element's position within the rebuilt sequence: immediately
        // after its predecessor, which is the anchor and therefore always in
        // the window, or at the front when there is no predecessor.
        let insert_at = match prev_index {
            | Some(prev) => {
                let found = window
                    .iter()
                    .position(|&index| index == prev)
                    .ok_or(OrderError::Inconsistent)?;
                found.checked_add(1).ok_or(OrderError::Inconsistent)?
            },
            | None => 0,
        };
        // The elements just outside the window keep their labels and bound the
        // rebuilt segment.
        let left_outer = window
            .first()
            .and_then(|&first| self.occupied(first))
            .and_then(|occupied| occupied.prev);
        let right_outer = window
            .last()
            .and_then(|&last| self.occupied(last))
            .and_then(|occupied| occupied.next);
        // Allocate the new element; its label and links are set below.
        let new_pos = self.alloc(start, None, None, value)?;
        // Build the rebuilt ordered sequence: the window with the new element
        // spliced in at `insert_at`.
        let mut sequence: Vec<SlotIndex> = Vec::with_capacity(occupants.0);
        for slot_position in 0 .. occupants.0 {
            if slot_position == insert_at {
                sequence.push(new_pos.index);
                continue;
            }
            // Window positions before `insert_at` map directly; positions after
            // it shift down by one to skip the inserted slot.
            let window_position = if slot_position < insert_at {
                slot_position
            }
            else {
                slot_position
                    .checked_sub(1)
                    .ok_or(OrderError::Inconsistent)?
            };
            let index = window
                .get(window_position)
                .copied()
                .ok_or(OrderError::Inconsistent)?;
            sequence.push(index);
        }
        self.assign_labels(&sequence, start, range_size, occupants)?;
        self.relink_segment(&sequence, left_outer, right_outer)?;
        Ok(new_pos)
    }

    /// Assigns evenly-spaced labels in `(start, start + range_size)` to the
    /// `sequence`, in order.
    ///
    /// # Specification
    /// - requires: `2 * occupants <= range_size` and every sequence index names
    ///   a live slot.
    /// - ensures: on `Ok`, each element of `sequence` carries the evenly spaced
    ///   label of its position, strictly increasing in order.
    /// - provides: the relabeled segment the link rewrite consumes. The clauses
    ///   check the caller's density and every index's liveness, then that each
    ///   element carries the spread label of its position and that the labels
    ///   strictly increase.
    /// - fails: [`OrderError::Inconsistent`] when a spread label is not
    ///   representable or a sequence index does not name a live slot; the
    ///   caller's density check precludes both.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when a spread label is not
    /// representable or a sequence index does not name a live slot; the
    /// caller's density check precludes both.
    #[inline]
    #[spec(
        requires: u64::try_from(occupants.0)
            .is_ok_and(|count| count.saturating_mul(2) <= range_size.0)
            && sequence.iter().all(|&index| self.occupied(index).is_some()),
        ensures: |ret| ret.is_err()
            || (sequence.iter().enumerate().all(|(position, &index)| self.label_of(index)
                == Self::spread_label(start, range_size, occupants, SequencePosition(position)))
                && sequence
                    .iter()
                    .zip(sequence.iter().skip(1))
                    .all(|(&before, &after)| self
                        .label_of(before)
                        .zip(self.label_of(after))
                        .is_some_and(|(earlier, later)| earlier < later))),
    )]
    fn assign_labels(
        &mut self,
        sequence: &[SlotIndex],
        start: Label,
        range_size: LabelRangeSize,
        occupants: OccupantCount,
    ) -> Result<(), OrderError>
    {
        for (position, &index) in sequence.iter().enumerate() {
            let label =
                Self::spread_label(start, range_size, occupants, SequencePosition(position))
                    .ok_or(OrderError::Inconsistent)?;
            self.set_label(index, label)?;
        }
        Ok(())
    }

    /// The evenly-spaced label for sequence position `position` of `occupants`
    /// within `[start, start + range_size)`.
    ///
    /// # Specification
    /// - requires: `position < occupants` and `2 * occupants <= range_size`.
    /// - ensures: returns `start + ((position + 1) * range_size) / (occupants +
    ///   1)`, which lies strictly inside the range and strictly above the label
    ///   of every smaller position.
    /// - provides: the label written into the relabeled slot.
    /// - fails: returns `None` only on an arithmetic conversion the
    ///   precondition precludes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 through the structural invariant — the strict-increase
    ///   and in-range properties are asserted over the whole list after every
    ///   relabeling insertion, so any mutant to the numerator, divisor, or
    ///   offset either collides two labels or escapes the window and breaks a
    ///   comparison against the un-relabeled neighbours; the full-universe
    ///   stress test supplies the wide-range boundary.
    /// - witness: `order::tests::relabel_after_anchor_preserves_order`
    /// - witness: `order::tests::relabel_at_front_preserves_order`
    /// - witness: `oracle::oracle::relabel_stress_at_full_universe`
    #[inline]
    #[spec(requires: position.0 < occupants.0
        && u64::try_from(occupants.0).is_ok_and(|count| count.saturating_mul(2) <= range_size.0))]
    fn spread_label(
        start: Label,
        range_size: LabelRangeSize,
        occupants: OccupantCount,
        position: SequencePosition,
    ) -> Option<Label>
    {
        let numerator_position = position.0.checked_add(1)?;
        let numerator = u128::try_from(numerator_position).ok()?;
        let divisor_occupants = occupants.0.checked_add(1)?;
        let divisor = u128::try_from(divisor_occupants).ok()?;
        let scaled = numerator.checked_mul(u128::from(range_size.0))?;
        let offset_wide = scaled.checked_div(divisor)?;
        let offset = u64::try_from(offset_wide).ok()?;
        let label = start.0.checked_add(offset)?;
        Some(Label(label))
    }

    /// Re-links the `sequence` into a contiguous list segment bounded by
    /// `left_outer` before it and `right_outer` after it, updating the
    /// structure's head/tail when a bound is absent.
    ///
    /// # Specification
    /// - requires: every sequence index and bound names a live slot.
    /// - ensures: on `Ok`, `sequence` is one contiguous list segment bounded by
    ///   `left_outer` and `right_outer`, and the structure's head/tail move
    ///   with an absent bound.
    /// - provides: the re-wired segment the relabel relies on. The clauses
    ///   check every index's liveness, then the segment's internal links, its
    ///   two boundary links, and the head or tail an absent bound moves.
    /// - fails: [`OrderError::Inconsistent`] when a sequence or bound index
    ///   does not name a live slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when a sequence or bound index does
    /// not name a live slot.
    #[inline]
    #[spec(
        requires: sequence.iter().all(|&index| self.occupied(index).is_some())
            && left_outer.is_none_or(|index| self.occupied(index).is_some())
            && right_outer.is_none_or(|index| self.occupied(index).is_some()),
        ensures: |ret| ret.is_err()
            || (sequence.iter().enumerate().all(|(position, &index)| self
                .occupied(index)
                .is_some_and(|occupied| occupied.prev
                    == position
                        .checked_sub(1)
                        .map_or(left_outer, |before| sequence.get(before).copied())
                    && occupied.next
                        == position
                            .checked_add(1)
                            .and_then(|after| sequence.get(after).copied())
                            .or(right_outer)))
                && sequence.first().copied().is_none_or(|first| match left_outer {
                    Some(outer) => self
                        .occupied(outer)
                        .is_some_and(|occupied| occupied.next == Some(first)),
                    None => self.head == Some(first),
                })
                && sequence.last().copied().is_none_or(|last| match right_outer {
                    Some(outer) => self
                        .occupied(outer)
                        .is_some_and(|occupied| occupied.prev == Some(last)),
                    None => self.tail == Some(last),
                })),
    )]
    fn relink_segment(
        &mut self,
        sequence: &[SlotIndex],
        left_outer: Option<SlotIndex>,
        right_outer: Option<SlotIndex>,
    ) -> Result<(), OrderError>
    {
        for (position, &index) in sequence.iter().enumerate() {
            let prev_link = position
                .checked_sub(1)
                .map_or(left_outer, |before| sequence.get(before).copied());
            let successor = position
                .checked_add(1)
                .and_then(|after| sequence.get(after))
                .copied();
            let next_link = successor.map_or(right_outer, Some);
            self.set_prev(index, prev_link)?;
            self.set_next(index, next_link)?;
        }
        match (left_outer, sequence.first()) {
            | (Some(outer), Some(&first)) => self.set_next(outer, Some(first))?,
            | (None, Some(&first)) => self.head = Some(first),
            | (_, None) => {},
        }
        match (right_outer, sequence.last()) {
            | (Some(outer), Some(&last)) => self.set_prev(outer, Some(last))?,
            | (None, Some(&last)) => self.tail = Some(last),
            | (_, None) => {},
        }
        Ok(())
    }
}

/// An in-order iterator over an [`OrderMaintenance`], yielding each element's
/// handle beside a borrow of its payload.
///
/// The cursor is a slot index rather than a borrowed node, so the iterator is a
/// plain state machine over the arena.
pub struct Iter<'order, T>
{
    /// The structure being walked.
    order: &'order OrderMaintenance<T>,
    /// The slot to yield next, or `None` once the walk is finished.
    cursor: Option<SlotIndex>,
}

impl<'order, T> IntoIterator for &'order OrderMaintenance<T>
{
    type IntoIter = Iter<'order, T>;
    type Item = (Pos, &'order T);

    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.iter()
    }
}

impl<'order, T> Iterator for Iter<'order, T>
{
    type Item = (Pos, &'order T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        let index = self.cursor?;
        let order = self.order;
        let occupied = order.occupied(index)?;
        self.cursor = occupied.next;
        let pos = Pos {
            structure_id: order.structure_id,
            index,
            generation: occupied.generation,
        };
        Some((pos, &occupied.value))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;
    use core::cmp::Ordering;

    use super::Label;
    use super::LabelBits;
    use super::OrderError;
    use super::OrderMaintenance;
    use super::Pos;
    use super::Slot;
    use super::SlotGeneration;
    use super::SlotIndex;
    use super::SlotLimit;
    use super::StructureIdCounter;
    use crate::interval::Interval;

    /// Fixtures and structural oracles shared by the unit tests.
    mod support
    {
        use super::*;

        /// A structure over the production label universe.
        pub(super) fn new_order<T>() -> OrderMaintenance<T>
        {
            OrderMaintenance::new().expect("structure id allocation succeeds in focused tests")
        }

        /// A structure over a deliberately narrow label universe, so relabeling
        /// and capacity exhaustion are reachable in a handful of insertions.
        pub(super) fn narrow_order<T>(label_bits: LabelBits) -> OrderMaintenance<T>
        {
            OrderMaintenance::with_label_bits(label_bits)
                .expect("structure id allocation succeeds in focused tests")
        }

        /// Asserts the structural invariant: labels strictly increase along the
        /// list and stay inside the universe, the forward and backward link
        /// chains agree on length, and head/tail bound the chain.
        pub(super) fn assert_invariant<T>(order: &OrderMaintenance<T>)
        {
            let universe = Label(order.capacity.0);
            let mut count: usize = 0;
            let mut previous_label = None;
            let mut cursor = order.head;
            let mut last_seen = None;
            while let Some(index) = cursor {
                let occupied = order.occupied(index).expect("listed slot is occupied");
                if let Some(label) = previous_label {
                    assert!(
                        occupied.label > label,
                        "labels strictly increase in list order"
                    );
                }
                assert!(
                    occupied.label < universe,
                    "labels stay inside the label universe"
                );
                previous_label = Some(occupied.label);
                last_seen = Some(index);
                count = count.saturating_add(1);
                cursor = occupied.next;
            }
            assert_eq!(count, usize::from(order.len), "forward length matches len");
            assert_eq!(last_seen, order.tail, "tail is the last listed element");

            let mut back_count: usize = 0;
            let mut back_cursor = order.tail;
            let mut first_seen = None;
            while let Some(index) = back_cursor {
                let occupied = order.occupied(index).expect("listed slot is occupied");
                first_seen = Some(index);
                back_count = back_count.saturating_add(1);
                back_cursor = occupied.prev;
            }
            assert_eq!(
                back_count,
                usize::from(order.len),
                "backward length matches len"
            );
            assert_eq!(first_seen, order.head, "head is the first listed element");
        }

        /// Asserts O(1) comparison agrees with list order for every pair, and
        /// that each element compares equal only to itself.
        pub(super) fn assert_cmp_consistent<T>(order: &OrderMaintenance<T>)
        {
            let handles = positions(order);
            for (left_rank, &left) in handles.iter().enumerate() {
                for (right_rank, &right) in handles.iter().enumerate() {
                    assert_eq!(
                        Some(left_rank.cmp(&right_rank)),
                        order.cmp(left, right),
                        "cmp matches list order for every pair"
                    );
                }
            }
        }

        /// The handles in list order.
        pub(super) fn positions<T>(order: &OrderMaintenance<T>) -> Vec<Pos>
        {
            order.iter().map(|(pos, _value)| pos).collect()
        }

        /// The payloads in list order.
        pub(super) fn ordered<T>(order: &OrderMaintenance<T>) -> Vec<T>
        where
            T: Copy,
        {
            order.iter().map(|(_pos, &value)| value).collect()
        }

        /// Points the `next` link of the element at `index` at a slot the arena
        /// does not have, so the next walk over that link must report
        /// [`OrderError::Inconsistent`].
        pub(super) fn corrupt_next_link<T>(
            order: &mut OrderMaintenance<T>,
            index: SlotIndex,
        )
        {
            let dangling = SlotIndex(u32::MAX);
            let occupied = order.occupied_mut(index).expect("slot is occupied");
            occupied.next = Some(dangling);
        }
    }

    use support::assert_cmp_consistent;
    use support::assert_invariant;
    use support::corrupt_next_link;
    use support::narrow_order;
    use support::new_order;
    use support::ordered;
    use support::positions;

    #[test]
    fn new_is_empty()
    {
        let order: OrderMaintenance<u64> = new_order();
        assert!(bool::from(order.is_empty()), "a fresh structure is empty");
        assert_eq!(
            0,
            usize::from(order.len()),
            "a fresh structure has no elements"
        );
        assert_eq!(None, order.first(), "no first element");
        assert_eq!(None, order.last(), "no last element");
        assert_eq!(Vec::<u64>::new(), ordered(&order), "iteration is empty");
    }

    #[test]
    fn push_back_preserves_order()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        for value in 0 .. 6 {
            order.push_back(value).expect("push_back succeeds");
        }
        assert_eq!(
            vec![0, 1, 2, 3, 4, 5],
            ordered(&order),
            "push_back appends in order"
        );
        assert_eq!(6, usize::from(order.len()), "length tracks insertions");
        let handles = positions(&order);
        assert_eq!(order.first(), handles.first().copied(), "first is the head");
        assert_eq!(order.last(), handles.last().copied(), "last is the tail");
        assert_invariant(&order);
        assert_cmp_consistent(&order);
    }

    #[test]
    fn push_front_reverses()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        for value in 0 .. 6 {
            order.push_front(value).expect("push_front succeeds");
        }
        assert_eq!(
            vec![5, 4, 3, 2, 1, 0],
            ordered(&order),
            "push_front prepends"
        );
        assert_invariant(&order);
        assert_cmp_consistent(&order);
    }

    #[test]
    fn insert_after_and_before_place_correctly()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let first = order.push_back(0).expect("push_back succeeds");
        let last = order.push_back(9).expect("push_back succeeds");
        let middle = order.insert_after(first, 5).expect("insert_after succeeds");
        order
            .insert_before(middle, 3)
            .expect("insert_before succeeds");
        order
            .insert_before(last, 7)
            .expect("insert_before succeeds");
        assert_eq!(
            vec![0, 3, 5, 7, 9],
            ordered(&order),
            "inserts land at the right spots"
        );
        assert_invariant(&order);
        assert_cmp_consistent(&order);
    }

    #[test]
    fn remove_middle_unlinks_and_invalidates()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        order.push_back(0).expect("push_back succeeds");
        let middle = order.push_back(1).expect("push_back succeeds");
        order.push_back(2).expect("push_back succeeds");
        assert_eq!(
            Ok(Some(1)),
            order.remove(middle),
            "remove returns the payload"
        );
        assert_eq!(vec![0, 2], ordered(&order), "the element is unlinked");
        assert!(
            !bool::from(order.contains(middle)),
            "the removed handle is stale"
        );
        assert_eq!(None, order.get(middle), "get on a stale handle is None");
        assert_eq!(Ok(None), order.remove(middle), "double remove is Ok(None)");
        assert_invariant(&order);
        assert_cmp_consistent(&order);
    }

    #[test]
    fn remove_head_and_tail()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let head = order.push_back(0).expect("push_back succeeds");
        order.push_back(1).expect("push_back succeeds");
        let tail = order.push_back(2).expect("push_back succeeds");
        assert_eq!(Ok(Some(0)), order.remove(head), "remove head");
        assert_eq!(Ok(Some(2)), order.remove(tail), "remove tail");
        assert_eq!(vec![1], ordered(&order), "only the middle survives");
        assert_invariant(&order);
    }

    #[test]
    fn remove_only_element_empties()
    {
        const SOLE_ELEMENT_VALUE: u64 = 42;

        let mut order: OrderMaintenance<u64> = new_order();
        let only = order
            .push_back(SOLE_ELEMENT_VALUE)
            .expect("push_back succeeds");
        assert_eq!(
            Ok(Some(SOLE_ELEMENT_VALUE)),
            order.remove(only),
            "remove the sole element"
        );
        assert!(bool::from(order.is_empty()), "structure is empty again");
        order.push_back(7).expect("reuse after emptying");
        assert_eq!(vec![7], ordered(&order), "can insert after emptying");
    }

    #[test]
    fn relabel_after_anchor_preserves_order()
    {
        const RELABEL_SENTINEL_VALUE: u64 = 100;

        // A narrow universe forces relabeling after only a few insertions; the
        // repeated insert-after-the-same-anchor stacks elements in reverse.
        let mut order: OrderMaintenance<u64> = narrow_order(LabelBits(4));
        let anchor = order.push_back(0).expect("push_back succeeds");

        order
            .push_back(RELABEL_SENTINEL_VALUE)
            .expect("push_back succeeds");
        for value in 1 ..= 6 {
            order
                .insert_after(anchor, value)
                .expect("insert_after succeeds under relabel");
            assert_invariant(&order);
            assert_cmp_consistent(&order);
        }
        assert_eq!(
            vec![0, 6, 5, 4, 3, 2, 1, 100],
            ordered(&order),
            "relabeling preserves the list order"
        );
    }

    #[test]
    fn relabel_at_front_preserves_order()
    {
        // Exhaust the front gap so a push_front must relabel with no
        // predecessor (the absent-predecessor relabel branch).
        let mut order: OrderMaintenance<u64> = narrow_order(LabelBits(4));
        for value in 0 .. 7 {
            order
                .push_front(value)
                .expect("push_front succeeds under relabel");
            assert_invariant(&order);
            assert_cmp_consistent(&order);
        }
        assert_eq!(
            vec![6, 5, 4, 3, 2, 1, 0],
            ordered(&order),
            "front relabeling preserves order"
        );
    }

    #[test]
    fn capacity_exhausts_in_a_tiny_universe()
    {
        // With two label bits the universe is `{0, 1, 2, 3}`; a third append
        // has no gap, and the whole-universe window cannot fit three elements
        // at density one half, so the relabel reports exhaustion.
        let mut order: OrderMaintenance<u64> = narrow_order(LabelBits(2));
        order.push_back(0).expect("first append fits");
        order.push_back(1).expect("second append fits");
        assert_eq!(
            Err(OrderError::CapacityExhausted),
            order.push_back(2),
            "a relabel that cannot reach density one half reports exhaustion"
        );
        // The structure is still well-formed and usable after the rejection.
        assert_eq!(
            vec![0, 1],
            ordered(&order),
            "the rejected element left no trace"
        );
        assert_eq!(2, usize::from(order.len()), "the rejection did not count");
        assert_invariant(&order);
    }

    #[test]
    fn structure_id_exhaustion_is_typed()
    {
        let counter = StructureIdCounter::nearly_exhausted();
        let mut first: OrderMaintenance<u64> =
            OrderMaintenance::with_label_bits_from_counter(LabelBits(4), &counter)
                .expect("the last distinct structure id is available");
        let old = first.push_back(1).expect("insertion succeeds");

        let exhausted =
            OrderMaintenance::<u64>::with_label_bits_from_counter(LabelBits(4), &counter);

        assert_eq!(
            Err(OrderError::StructureIdExhausted),
            exhausted.map(|_ignored: OrderMaintenance<u64>| ()),
            "structure id exhaustion is typed"
        );
        assert_eq!(
            Some(&1),
            first.get(old),
            "an extant position is not aliased by a wrapped structure id"
        );
    }

    #[test]
    fn exhausted_generation_retires_slot_and_allocates_another()
    {
        let mut order: OrderMaintenance<u64> = narrow_order(LabelBits(4));
        let first = order.push_back(0).expect("initial insert succeeds");
        let exhausted = Pos {
            generation: SlotGeneration::LAST,
            ..first
        };
        let occupied = order.occupied_mut(first.index).expect("slot is occupied");
        occupied.generation = SlotGeneration::LAST;

        assert_eq!(
            Ok(Some(0)),
            order.remove(exhausted),
            "remove the exhausted slot"
        );
        assert!(
            matches!(order.slot(exhausted.index), Some(&Slot::Retired)),
            "the exhausted slot is retired permanently"
        );
        let replacement = order.push_back(1).expect("a fresh slot is allocated");
        assert_ne!(
            exhausted.index, replacement.index,
            "the retired slot index is not reused"
        );
        assert_eq!(
            None,
            order.get(exhausted),
            "the stale exhausted-generation handle does not alias the replacement"
        );
        assert_eq!(Some(&1), order.get(replacement), "the replacement resolves");
    }

    #[test]
    fn retired_slot_capacity_exhaustion_is_typed()
    {
        let mut order: OrderMaintenance<u64> =
            OrderMaintenance::with_label_bits_and_slot_limit(LabelBits(4), SlotLimit(1))
                .expect("bounded test structure can be constructed");
        let first = order
            .push_back(0)
            .expect("initial insert consumes the slot");
        let exhausted = Pos {
            generation: SlotGeneration::LAST,
            ..first
        };
        let occupied = order.occupied_mut(first.index).expect("slot is occupied");
        occupied.generation = SlotGeneration::LAST;

        assert_eq!(Ok(Some(0)), order.remove(exhausted), "retire the only slot");
        assert_eq!(
            Err(OrderError::CapacityExhausted),
            order.push_back(1),
            "when every representable slot is retired, insertion reports typed exhaustion"
        );
        assert_eq!(
            None,
            order.get(exhausted),
            "the retired slot remains unavailable to stale handles"
        );
    }

    #[test]
    fn corrupt_link_removal_is_typed()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let head = order.push_back(0).expect("push_back succeeds");
        order.push_back(1).expect("push_back succeeds");
        corrupt_next_link(&mut order, head.index);
        assert_eq!(
            Err(OrderError::Inconsistent),
            order.remove(head),
            "a dangling successor link surfaces as a typed inconsistency"
        );
    }

    #[test]
    fn corrupt_link_insert_is_typed()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let head = order.push_back(0).expect("push_back succeeds");
        order.push_back(1).expect("push_back succeeds");
        corrupt_next_link(&mut order, head.index);
        assert_eq!(
            Err(OrderError::Inconsistent),
            order.insert_after(head, 2),
            "an insertion beside a dangling successor link is a typed inconsistency"
        );
    }

    #[test]
    fn navigation_walks_both_ways()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let first = order.push_back(0).expect("push_back succeeds");
        let second = order.push_back(1).expect("push_back succeeds");
        let third = order.push_back(2).expect("push_back succeeds");
        assert_eq!(Some(second), order.next(first), "next walks forward");
        assert_eq!(None, order.next(third), "next at the tail is None");
        assert_eq!(Some(second), order.prev(third), "prev walks backward");
        assert_eq!(None, order.prev(first), "prev at the head is None");
        assert_eq!(Some(&1), order.get(second), "get returns the payload");
    }

    #[test]
    fn slot_reuse_distinguishes_generation()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let first = order.push_back(0).expect("push_back succeeds");
        order.push_back(1).expect("push_back succeeds");
        assert_eq!(Ok(Some(0)), order.remove(first), "free the first slot");
        // The next allocation reuses the freed slot with a bumped generation.
        let reused = order.push_back(2).expect("push_back reuses the slot");
        assert_eq!(reused.index, first.index, "the freed slot index is reused");
        assert_ne!(
            first.generation, reused.generation,
            "the generation is bumped"
        );
        assert_eq!(
            None,
            order.get(first),
            "the stale handle does not alias the reuse"
        );
        assert_eq!(Some(&2), order.get(reused), "the fresh handle resolves");
    }

    #[test]
    fn stale_handle_insert_errors()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let only = order.push_back(0).expect("push_back succeeds");
        order.remove(only).expect("remove succeeds");
        assert_eq!(
            Err(OrderError::UnknownPosition),
            order.insert_after(only, 1),
            "insert_after a stale handle errors"
        );
        assert_eq!(
            Err(OrderError::UnknownPosition),
            order.insert_before(only, 1),
            "insert_before a stale handle errors"
        );
    }

    #[test]
    fn foreign_handle_is_rejected()
    {
        let mut one: OrderMaintenance<u64> = new_order();
        let mut two: OrderMaintenance<u64> = new_order();
        let foreign = one.push_back(0).expect("push_back succeeds");
        let native = two.push_back(1).expect("push_back succeeds");
        assert_eq!(None, two.get(foreign), "a foreign handle does not resolve");
        assert_eq!(
            None,
            two.cmp(foreign, native),
            "comparing across structures is None"
        );
        assert_eq!(
            None,
            two.cmp(native, foreign),
            "comparing across structures is None in either argument"
        );
        assert_eq!(
            Err(OrderError::UnknownPosition),
            two.insert_after(foreign, 2),
            "inserting at a foreign handle errors"
        );
        assert_eq!(
            Ok(None),
            two.remove(foreign),
            "removing a foreign handle is Ok(None)"
        );
        assert!(
            !bool::from(two.contains(foreign)),
            "a foreign handle is not contained"
        );
    }

    #[test]
    fn interval_containment()
    {
        // Pre/post-order points for a tree: outer `[a_lo, a_hi]` wraps inner
        // `[b_lo, b_hi]`; a third point `c` sits after both.
        let mut order: OrderMaintenance<&'static str> = new_order();
        let a_lo = order.push_back("a_lo").expect("push_back succeeds");
        let b_lo = order.push_back("b_lo").expect("push_back succeeds");
        let b_hi = order.push_back("b_hi").expect("push_back succeeds");
        let a_hi = order.push_back("a_hi").expect("push_back succeeds");
        let c = order.push_back("c").expect("push_back succeeds");
        let outer = Interval::new(a_lo, a_hi);
        let inner = Interval::new(b_lo, b_hi);
        let disjoint = Interval::new(c, c);
        assert_eq!(
            Some(true),
            order.interval_contains(outer, inner).map(bool::from),
            "outer contains inner"
        );
        assert_eq!(
            Some(false),
            order.interval_contains(inner, outer).map(bool::from),
            "inner does not contain outer"
        );
        assert_eq!(
            Some(false),
            order.interval_contains(outer, disjoint).map(bool::from),
            "outer does not contain a later point"
        );
        assert_eq!(
            Some(false),
            order.interval_contains(disjoint, outer).map(bool::from),
            "a later point does not contain outer"
        );
        assert_eq!(
            Some(true),
            order.interval_contains(outer, outer).map(bool::from),
            "an interval contains itself"
        );
        assert_eq!(
            Some(true),
            order
                .interval_contains(outer, Interval::new(a_lo, b_hi))
                .map(bool::from),
            "a shared lower endpoint still counts as containment"
        );
        assert_eq!(
            Some(true),
            order
                .interval_contains(outer, Interval::new(b_lo, a_hi))
                .map(bool::from),
            "a shared upper endpoint still counts as containment"
        );
    }

    #[test]
    fn interval_with_stale_endpoint_is_none()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let lo = order.push_back(0).expect("push_back succeeds");
        let hi = order.push_back(1).expect("push_back succeeds");
        let gone = order.push_back(2).expect("push_back succeeds");
        order.remove(gone).expect("remove succeeds");
        let live = Interval::new(lo, hi);
        let stale = Interval::new(gone, gone);
        assert_eq!(
            None,
            order.interval_contains(live, stale),
            "a stale inner endpoint yields None"
        );
        assert_eq!(
            None,
            order.interval_contains(stale, live),
            "a stale outer endpoint yields None"
        );
    }

    #[test]
    fn comparison_is_reflexive_and_total()
    {
        let mut order: OrderMaintenance<u64> = new_order();
        let first = order.push_back(0).expect("push_back succeeds");
        let second = order.push_back(1).expect("push_back succeeds");
        assert_eq!(
            Some(Ordering::Equal),
            order.cmp(first, first),
            "an element equals itself"
        );
        assert_eq!(
            Some(Ordering::Less),
            order.cmp(first, second),
            "earlier is Less"
        );
        assert_eq!(
            Some(Ordering::Greater),
            order.cmp(second, first),
            "later is Greater"
        );
    }

    #[test]
    fn error_display_is_distinct_per_variant()
    {
        use alloc::string::String;

        let messages: [String; 4] = [
            alloc::string::ToString::to_string(&OrderError::UnknownPosition),
            alloc::string::ToString::to_string(&OrderError::StructureIdExhausted),
            alloc::string::ToString::to_string(&OrderError::CapacityExhausted),
            alloc::string::ToString::to_string(&OrderError::Inconsistent),
        ];
        for (left_rank, left) in messages.iter().enumerate() {
            assert!(!left.is_empty(), "every variant renders a message");
            for (right_rank, right) in messages.iter().enumerate() {
                assert_eq!(
                    left_rank == right_rank,
                    left == right,
                    "distinct variants render distinct messages"
                );
            }
        }
    }
}
