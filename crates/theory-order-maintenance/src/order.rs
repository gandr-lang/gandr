//! The order-maintenance structure ([`OrderMaintenance`]) and its handle
//! ([`Pos`]).
//!
//! The structure is two flat arenas: the elements, in [`Slot`]s addressed by
//! [`SlotIndex`], and the groups that label them, in [`GroupSlot`]s addressed
//! by [`GroupIndex`]. List order is carried by index links, never by owning
//! pointers, and every walk over those links is an explicit loop.
//!
//! An element's key is its group's label, a point on a circle of `2^64` labels
//! measured from the first group's, then its own label in `[0, 2^w)` for the
//! group width `w` ([`GroupWidth`]). An insertion takes the midpoint of its
//! neighbours' labels in their group. A group with no label left there splits
//! from its back into groups of `w/2` elements, each placed at the midpoint of
//! the room after it and spread over its own labels. When that room is spent,
//! the groups after the full one are spread over the first room the walk finds
//! holding more than the square of their number, the walk continuing past the
//! last group to the first.

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
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a counter whose next [`Self::allocate`] issues the
    ///   final identity and whose following call refuses.
    /// - provides: the seeded counter the exhaustion test drives, so the
    ///   refusal is reachable without minting `usize::MAX` structures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter starts exactly one issue below refusal;
    ///   the final identity and permanent exhaustion are observed on successive
    ///   calls.
    /// - witness: `order::tests::structure_id_exhaustion_is_typed`
    #[cfg(test)]
    #[inline]
    #[spec(ensures: |ret| ret.0.load(AtomicOrdering::Relaxed) == usize::MAX.wrapping_sub(1))]
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
    ///   The predicate bounds the issued id between monotone observations of
    ///   this shared counter; uniqueness across calls is witnessed separately.
    /// - fails: returns [`OrderError::StructureIdExhausted`] once the counter
    ///   would wrap, leaving the final id permanently unissued.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when no distinct id
    /// remains.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for a bounded concurrent batch against the exact
    ///   sequence of issued identities; L3 for the final issue and permanent
    ///   refusal. The predicate does not retain a history of prior issues.
    /// - witness: `order::tests::concurrent_identity_allocation_is_disjoint`
    /// - witness: `order::tests::structure_id_exhaustion_is_typed`
    #[inline]
    #[spec(
        captures: issued_from = self.0.load(AtomicOrdering::Relaxed),
        ensures: |ret| ret.map_or_else(
            |error| error == OrderError::StructureIdExhausted
                && self.0.load(AtomicOrdering::Relaxed) == usize::MAX,
            |identity| identity.0 >= issued_from
                && identity.0 < self.0.load(AtomicOrdering::Relaxed)),
    )]
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

/// The width of a group's label universe, the `log N` of the two-level
/// scheme.
///
/// An element carries a bottom label in `[0, 2^width)` within its group, and
/// a group left with no label between two neighbours splits into groups of
/// `width / 2` elements. A wider group absorbs more insertions before it
/// splits and relabels more elements when it does. [`Self::DEFAULT`] is the
/// width [`OrderMaintenance::new`] selects.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GroupWidth(u32);

impl GroupWidth
{
    /// The narrowest width: sixteen bottom labels, and two elements in each
    /// group a split makes.
    pub const MIN: Self = Self(4);
    /// The widest width: bottom labels fill a `u32` below its top bit.
    pub const MAX: Self = Self(31);
    /// The width [`OrderMaintenance::new`] selects: the widest, which the
    /// crate's bench measures fastest, or within a few nanoseconds of the
    /// fastest, in every workload from a thousand elements to a million.
    pub const DEFAULT: Self = Self::MAX;

    /// The size of a group's label universe, `2^width`.
    ///
    /// # Specification
    /// - requires: nothing; every width lies in `[MIN, MAX]` by construction.
    /// - ensures: returns `2^width`.
    /// - provides: the exclusive upper bound of a group's bottom labels.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact spread labels of the narrowest group and
    ///   the largest label the widest group holds pin the power.
    /// - witness: `order::tests::a_group_spreads_its_elements_evenly`
    #[inline]
    #[spec(ensures: |ret| Some(ret.0) == 1_u64.checked_shl(self.0))]
    fn universe(self) -> BottomUniverse
    {
        BottomUniverse(1_u64.checked_shl(self.0).unwrap_or(u64::MAX))
    }

    /// How many elements each group a split makes holds: `width / 2`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns `width / 2`, at least two for every width.
    /// - provides: the size a full group is cut into, from its back.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a split group of the width eight leaves groups of
    ///   four elements behind a remainder of three.
    /// - witness: `order::tests::a_full_group_splits_from_its_back`
    #[inline]
    #[spec(ensures: |ret| ret.0 == self.0.div_euclid(2))]
    fn split_len(self) -> GroupLen
    {
        GroupLen(self.0.div_euclid(2))
    }
}

impl From<GroupWidth> for u32
{
    /// The width as a plain count of bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: GroupWidth) -> Self
    {
        value.0
    }
}

impl From<u32> for GroupWidth
{
    /// The width `bits`, clamped into `[MIN, MAX]`.
    ///
    /// # Specification
    /// - requires: nothing; any width may be offered.
    /// - ensures: returns `bits` unchanged when it lies in `[MIN, MAX]`, and
    ///   the nearer endpoint otherwise.
    /// - provides: the only way to name a width, so a group's universe is
    ///   always representable and a split always leaves two elements a group or
    ///   more.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — widths below, at and above both endpoints separate
    ///   clamping from passing a width through.
    /// - witness: `order::tests::group_widths_clamp_into_their_range`
    #[inline]
    #[spec(ensures: |ret| ret.0 == bits.clamp(Self::MIN.0, Self::MAX.0))]
    fn from(bits: u32) -> Self
    {
        Self(bits.clamp(Self::MIN.0, Self::MAX.0))
    }
}

/// The width of the top-label universe: group labels are points on a circle
/// of `2^width` labels, and a group's place in the order is its label's
/// distance from the base group's label, measured forward around the circle.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TopWidth(u32);

impl TopWidth
{
    /// The full circle, `2^64` labels: the square of the `u32` slot ceiling,
    /// so the rebalance walk finds room for every group a structure can hold.
    const FULL: Self = Self(64);

    /// The circle's last label, `2^width - 1`: the mask that reduces a label
    /// difference onto the circle.
    ///
    /// # Specification
    /// - requires: the width lies in `[1, 64]`.
    /// - ensures: returns `2^width - 1`.
    /// - provides: the reduction every label sum and difference takes, so
    ///   arithmetic on the circle never leaves it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a circle of eight labels measures a wrapped distance
    ///   exactly, and the full circle wraps at `2^64`.
    /// - witness: `order::tests::top_labels_are_measured_around_the_circle`
    #[inline]
    #[spec(
        requires: (1 ..= 64).contains(&self.0),
        ensures: |ret| 1_u128.checked_shl(self.0).and_then(|span| span.checked_sub(1)) == Some(u128::from(ret.0)),
    )]
    fn last(self) -> TopLabel
    {
        TopLabel(
            64_u32
                .checked_sub(self.0)
                .and_then(|shift| u64::MAX.checked_shr(shift))
                .unwrap_or(u64::MAX),
        )
    }

    /// The number of labels on the circle, `2^width`.
    ///
    /// # Specification
    /// - requires: the width lies in `[1, 64]`.
    /// - ensures: returns `2^width`.
    /// - provides: the room a group has when it is the only one: the whole
    ///   circle.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the room from a group to itself is the whole circle
    ///   of eight labels; a circle of two labels holds two groups and refuses a
    ///   third.
    /// - witness: `order::tests::top_labels_are_measured_around_the_circle`
    /// - witness: `order::tests::capacity_exhausts_on_a_circle_of_two_labels`
    #[inline]
    #[spec(
        requires: (1 ..= 64).contains(&self.0),
        ensures: |ret| Some(ret.0) == 1_u128.checked_shl(self.0),
    )]
    fn universe(self) -> TopGap
    {
        TopGap(1_u128.checked_shl(self.0).unwrap_or(u128::MAX))
    }
}

/// A group's label: a point on the top circle.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TopLabel(u64);

/// The room between two group labels, measured forward around the top circle:
/// in `(0, 2^width]`, the whole circle from a group to itself.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TopGap(u128);

/// An element's label within its group: strictly increasing along the group.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BottomLabel(u32);

/// The size of a group's label universe, `2^width`: every bottom label lies
/// below it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BottomUniverse(u64);

/// An element's place among the elements a group spreads, counting from one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SpreadPosition(u64);

/// A group's slot index in the group arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct GroupIndex(u32);

/// The number of elements a group holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct GroupLen(u32);

/// An element's place in the order: its group's label measured from the base
/// group's, then its own label. Keys compare as the elements they belong to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct OrderKey
{
    /// The group's label's distance from the base group's label.
    top: TopLabel,
    /// The element's label within its group.
    bottom: BottomLabel,
}

/// An element's slot index in the arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SlotIndex(u32);

impl TryFrom<usize> for SlotIndex
{
    type Error = <u32 as TryFrom<usize>>::Error;

    /// The slot index for an arena position, if the position is
    /// representable.
    ///
    /// # Specification
    /// - requires: nothing; any position may be offered.
    /// - ensures: returns the index carrying `value` unchanged when it fits the
    ///   underlying `u32`.
    /// - provides: the one narrowing step from an arena position to a handle
    ///   field, so an arena wider than a handle can address is refused rather
    ///   than truncated.
    /// - fails: returns the `u32` conversion's own error once `value` exceeds
    ///   `u32::MAX`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and the largest slot index round-trip; on a
    ///   wider host the first unrepresentable arena position refuses.
    /// - witness: `order::tests::slot_indices_preserve_numeric_bounds`
    #[spec(ensures: |ret| ret.map(|index| index.0) == u32::try_from(value))]
    #[inline]
    fn try_from(value: usize) -> Result<Self, Self::Error>
    {
        u32::try_from(value).map(Self)
    }
}

impl TryFrom<SlotIndex> for usize
{
    type Error = <Self as TryFrom<u32>>::Error;

    /// The arena position a slot index names, if the position is
    /// representable.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the index's own value widened to `usize`.
    /// - provides: the indexing step every arena lookup takes.
    /// - fails: returns the `usize` conversion's own error on a target too
    ///   narrow to hold a `u32`, which no supported target is.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two representable endpoints preserve their
    ///   numeric identity without sign extension or truncation.
    /// - witness: `order::tests::slot_indices_preserve_numeric_bounds`
    #[spec(ensures: |ret| ret == Self::try_from(value.0))]
    #[inline]
    fn try_from(value: SlotIndex) -> Result<Self, Self::Error>
    {
        Self::try_from(value.0)
    }
}

/// A slot's reuse counter, bumped each time the slot is freed so a handle
/// minted before the reuse does not resolve.
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
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the generation one above this one, or `None` at the
    ///   representable ceiling.
    /// - provides: the exhaustion signal the free path reads; the absence is
    ///   what retires a slot instead of reusing it under a generation some live
    ///   handle already carries.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first reuse, the final reusable generation and
    ///   exhausted retirement distinguish increment from wraparound.
    /// - witness: `order::tests::generation_and_length_refuse_wraparound`
    /// - witness: `order::tests::exhausted_generation_retires_slot_and_allocates_another`
    #[spec(ensures: |ret| ret.map(|generation| generation.0) == self.0.checked_add(1))]
    #[inline]
    fn successor(self) -> Option<Self>
    {
        self.0.checked_add(1).map(Self)
    }
}

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
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns this length plus one, or `None` at the representable
    ///   ceiling.
    /// - provides: the checked bump the insert path takes, so a length that
    ///   could not be represented refuses the insertion rather than wrapping.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty growth, the final representable increment and
    ///   refusal beyond the ceiling are distinguished.
    /// - witness: `order::tests::generation_and_length_refuse_wraparound`
    #[spec(ensures: |ret| ret.map(|length| length.0) == self.0.checked_add(1))]
    #[inline]
    fn incremented(self) -> Option<Self>
    {
        self.0.checked_add(1).map(Self)
    }

    /// This length with one fewer element, or `None` when already empty.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns this length minus one, or `None` when already zero.
    /// - provides: the checked decrement the remove path takes, so a removal
    ///   unmatched by an insertion cannot wrap the length.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — decrement to zero, decrement from the ceiling and
    ///   empty refusal separate subtraction from saturation or wraparound.
    /// - witness: `order::tests::generation_and_length_refuse_wraparound`
    #[spec(ensures: |ret| ret.map(|length| length.0) == self.0.checked_sub(1))]
    #[inline]
    fn decremented(self) -> Option<Self>
    {
        self.0.checked_sub(1).map(Self)
    }
}

impl From<LiveLen> for usize
{
    /// The length as a plain count.
    ///
    /// # Specification
    /// trivial.
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
    /// The answer as a plain boolean.
    ///
    /// # Specification
    /// trivial.
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
    /// The answer as a plain boolean.
    ///
    /// # Specification
    /// trivial.
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
    /// The answer as a plain boolean.
    ///
    /// # Specification
    /// trivial.
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
    /// slots representable by [`Pos`], or no room is left on the circle of
    /// group labels, so no fresh element can be admitted.
    CapacityExhausted,
    /// An internal invariant of the arena was violated: a live element's link
    /// or label did not resolve. No sequence of public operations produces
    /// this; the variant exists so a corrupted arena surfaces as a typed error
    /// instead of a panic or a silently skipped write.
    Inconsistent,
}

impl core::fmt::Display for OrderError
{
    /// Writes the failure's message.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one fixed message per variant, naming the operation
    ///   and the condition that refused it.
    /// - provides: the rendering [`core::error::Error`] reporting reads.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes a write-only sink, not its
    ///   emitted text or the sink outcome independently of this call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four failure classes render distinctly without
    ///   pinning wording, and a refusing sink propagates its error.
    /// - witness: `order::tests::error_display_is_distinct_per_variant`
    /// - witness: `order::tests::formatter_refusal_is_propagated`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let message = match *self {
            Self::UnknownPosition => "order-maintenance operation on an unknown or stale handle",
            Self::StructureIdExhausted => "order-maintenance structure identifiers are exhausted",
            Self::CapacityExhausted => "order-maintenance structure is at capacity",
            Self::Inconsistent => "order-maintenance arena is internally inconsistent",
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
    /// The group the element is labelled in.
    group: GroupIndex,
    /// The element's label within its group; strictly increasing along it.
    label: BottomLabel,
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

/// A group: a run of consecutive elements sharing one top label.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Group
{
    /// The group's point on the top circle.
    label: TopLabel,
    /// The group before this one in list order, if any.
    prev: Option<GroupIndex>,
    /// The group after this one in list order, if any.
    next: Option<GroupIndex>,
    /// The group's first element.
    first: SlotIndex,
    /// The group's last element.
    last: SlotIndex,
    /// How many elements the group holds; never zero for a live group.
    len: GroupLen,
}

/// One group-arena slot: a live group, or a freed one threaded onto the free
/// list.
enum GroupSlot
{
    /// A live group.
    Live(Group),
    /// A freed group slot, and the next free one, if any.
    Free(Option<GroupIndex>),
}

/// Where an insertion between two adjacent elements lands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Room
{
    /// The group the new element joins, and the label between its neighbours
    /// that it takes.
    Free
    {
        /// The group the new element joins.
        group: GroupIndex,
        /// The new element's label.
        label: BottomLabel,
    },
    /// The group the new element joins has no label between its neighbours.
    Full(GroupIndex),
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
    /// Test-only ceiling for representable slots, so a test can exercise
    /// exhaustion without allocating a `u32::MAX`-sized arena.
    #[cfg(test)]
    slot_limit: Option<SlotLimit>,
    /// The first element in list order, if any.
    head: Option<SlotIndex>,
    /// The last element in list order, if any.
    tail: Option<SlotIndex>,
    /// The number of live elements.
    len: LiveLen,
    /// The group arena, addressed by [`GroupIndex`].
    groups: Vec<GroupSlot>,
    /// The head of the group free list, if any.
    free_group: Option<GroupIndex>,
    /// The base group: the first element's group, from whose label every
    /// group's place is measured; `None` exactly when the structure is empty.
    base: Option<GroupIndex>,
    /// The width of every group's label universe.
    width: GroupWidth,
    /// The width of the top circle.
    top: TopWidth,
    /// This structure's process-unique identity, stamped into every [`Pos`] it
    /// mints (see [`NEXT_STRUCTURE_ID`]).
    structure_id: StructureId,
}

impl<T> OrderMaintenance<T>
{
    /// Creates an empty structure whose groups have [`GroupWidth::DEFAULT`].
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
        Self::with_group_width(GroupWidth::DEFAULT)
    }

    /// Creates an empty structure whose groups have `width`.
    ///
    /// # Specification
    /// - requires: nothing; every width lies in range by construction.
    /// - ensures: on `Ok`, the structure is empty, its groups have `width`, and
    ///   its identity is distinct from every other structure this process
    ///   built.
    /// - provides: the group width as a parameter, for a consumer or a bench
    ///   that measures it. The clause checks emptiness and the installed width;
    ///   identity distinctness stays prose, because it is a law over every
    ///   structure this process built before this call.
    /// - fails: [`OrderError::StructureIdExhausted`] when no distinct structure
    ///   id remains.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when no distinct structure
    /// id remains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a structure built at a clamped width carries that
    ///   width, and the narrowest width's splits are observed group by group.
    /// - witness: `order::tests::group_widths_clamp_into_their_range`
    /// - witness: `order::tests::a_full_group_splits_from_its_back`
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret
            .as_ref()
            .is_ok_and(|order| order.len() == LiveLen::ZERO && order.width == width))]
    pub fn with_group_width(width: GroupWidth) -> Result<Self, OrderError>
    {
        Self::with_widths_from_counter(TopWidth::FULL, width, &NEXT_STRUCTURE_ID)
    }

    /// Creates an empty structure over a top circle of `2^top` labels whose
    /// groups have `width`.
    ///
    /// The narrow circle exists for tests that provoke the rebalance and
    /// capacity exhaustion without inserting `2^32` groups; in production the
    /// circle is [`TopWidth::FULL`].
    ///
    /// # Specification
    /// - requires: `top` lies in `[1, 64]`.
    /// - ensures: on `Ok`, the structure is empty over the two widths.
    /// - provides: the narrow-circle constructor the rebalance and capacity
    ///   tests drive.
    /// - fails: [`OrderError::StructureIdExhausted`] when no distinct structure
    ///   id remains.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when no distinct structure
    /// id remains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a circle of two labels refuses its third group, and a
    ///   circle of sixteen relabels the groups after a full one.
    /// - witness: `order::tests::capacity_exhausts_on_a_circle_of_two_labels`
    /// - witness: `order::tests::a_crowded_circle_spreads_the_groups_after_the_full_one`
    #[cfg(test)]
    #[inline]
    #[spec(
        requires: (1 ..= 64).contains(&top.0),
        ensures: |ret| ret.is_err()
            || ret
                .as_ref()
                .is_ok_and(|order| order.len() == LiveLen::ZERO && order.top == top && order.width == width),
    )]
    fn with_widths(
        top: TopWidth,
        width: GroupWidth,
    ) -> Result<Self, OrderError>
    {
        Self::with_widths_from_counter(top, width, &NEXT_STRUCTURE_ID)
    }

    /// Creates an empty structure over the two widths, drawing its identity
    /// from `counter` instead of the process-wide [`NEXT_STRUCTURE_ID`].
    ///
    /// The injectable counter exists for tests that exercise structure-id
    /// exhaustion without minting `usize::MAX` structures.
    ///
    /// # Specification
    /// - requires: `top` lies in `[1, 64]`.
    /// - ensures: on `Ok`, the structure is empty over the two widths and its
    ///   identity is minted from `counter`.
    /// - provides: the constructor every other one routes through. The clause
    ///   checks emptiness and the widths; the identity's provenance stays
    ///   prose, because `counter` is shared across threads and has already
    ///   advanced when the postcondition runs.
    /// - fails: [`OrderError::StructureIdExhausted`] when `counter` has no
    ///   fresh id.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::StructureIdExhausted`] when `counter` has no fresh
    /// id to issue.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bounded counter admits exactly its final structure
    ///   and then returns the typed exhaustion error; fresh structures expose
    ///   the installed widths.
    /// - witness: `order::tests::structure_id_exhaustion_is_typed`
    /// - witness: `order::tests::new_is_empty`
    #[inline]
    #[spec(
        requires: (1 ..= 64).contains(&top.0),
        ensures: |ret| ret.is_err()
            || ret
                .as_ref()
                .is_ok_and(|order| order.len() == LiveLen::ZERO && order.top == top && order.width == width),
    )]
    fn with_widths_from_counter(
        top: TopWidth,
        width: GroupWidth,
        counter: &StructureIdCounter,
    ) -> Result<Self, OrderError>
    {
        let structure_id = counter.allocate()?;
        Ok(Self {
            slots: Vec::new(),
            free_head: None,
            #[cfg(test)]
            slot_limit: None,
            head: None,
            tail: None,
            len: LiveLen::ZERO,
            groups: Vec::new(),
            free_group: None,
            base: None,
            width,
            top,
            structure_id,
        })
    }

    /// Creates a structure whose arena may never exceed `slot_limit` slots.
    ///
    /// # Specification
    /// - requires: `top` lies in `[1, 64]`.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a spent generation retires its slot, and a bounded
    ///   arena refuses another allocation rather than reusing that retired
    ///   identity.
    /// - witness: `order::tests::retired_slot_capacity_exhaustion_is_typed`
    #[cfg(test)]
    #[inline]
    #[spec(
        requires: (1 ..= 64).contains(&top.0),
        ensures: |ret| ret.is_err()
            || ret
                .as_ref()
                .is_ok_and(|order| order.len() == LiveLen::ZERO
                    && order.slot_limit == Some(slot_limit)),
    )]
    fn with_widths_and_slot_limit(
        top: TopWidth,
        width: GroupWidth,
        slot_limit: SlotLimit,
    ) -> Result<Self, OrderError>
    {
        let mut order = Self::with_widths(top, width)?;
        order.slot_limit = Some(slot_limit);
        Ok(order)
    }

    /// The number of live elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> LiveLen
    {
        self.len
    }

    /// Whether the structure has no live elements.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers affirmatively exactly when [`Self::len`] is zero.
    /// - provides: the emptiness question in the crate's own answer type,
    ///   agreeing with the length by construction.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, populated and emptied structures separate zero
    ///   length from both ends of a mutation sequence.
    /// - witness: `order::tests::new_is_empty`
    /// - witness: `order::tests::remove_only_element_empties`
    /// - witness: `order::tests::navigation_rejects_stale_and_foreign_handles`
    #[spec(ensures: |ret| ret.0 == (self.len.0 == 0))]
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> OrderIsEmpty
    {
        OrderIsEmpty(self.len == LiveLen::ZERO)
    }

    /// The first element in order, if any.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a handle to the earliest live element, and `None`
    ///   exactly when the structure is empty.
    /// - provides: the entry point of a forward walk; the handle carries this
    ///   structure's identity and the element's current generation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and populated ends, prepending and head removal
    ///   distinguish the first live handle from a missing or stale arena slot.
    /// - witness: `order::tests::new_is_empty`
    /// - witness: `order::tests::push_back_preserves_order`
    /// - witness: `order::tests::push_front_reverses`
    /// - witness: `order::tests::remove_head_and_tail`
    #[spec(ensures: |ret| ret == self.head.and_then(|index| self.pos_at(index)))]
    #[inline]
    #[must_use]
    pub fn first(&self) -> Option<Pos>
    {
        let index = self.head?;
        self.pos_at(index)
    }

    /// The last element in order, if any.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a handle to the latest live element, and `None`
    ///   exactly when the structure is empty.
    /// - provides: the entry point of a backward walk; the handle carries this
    ///   structure's identity and the element's current generation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and populated ends, appending and tail removal
    ///   distinguish the last live handle from a missing or stale arena slot.
    /// - witness: `order::tests::new_is_empty`
    /// - witness: `order::tests::push_back_preserves_order`
    /// - witness: `order::tests::remove_head_and_tail`
    #[spec(ensures: |ret| ret == self.tail.and_then(|index| self.pos_at(index)))]
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<Pos>
    {
        let index = self.tail?;
        self.pos_at(index)
    }

    /// Whether `pos` refers to a live element of this structure.
    ///
    /// # Specification
    /// - requires: nothing; any handle may be offered.
    /// - ensures: answers affirmatively exactly when `pos` names a live element
    ///   of this structure — this identity, an occupied slot, and the slot's
    ///   current generation.
    /// - provides: the liveness question a caller holding a possibly stale
    ///   handle asks before acting on it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — removed, reused-generation and foreign handles are
    ///   rejected while the current native handle still resolves.
    /// - witness: `order::tests::remove_middle_unlinks_and_invalidates`
    /// - witness: `order::tests::slot_reuse_distinguishes_generation`
    /// - witness: `order::tests::foreign_handle_is_rejected`
    #[spec(ensures: |ret| ret.0 == (pos.structure_id == self.structure_id
        && self.occupied(pos.index).is_some_and(|occupied| occupied.generation == pos.generation)))]
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
    /// - requires: nothing; either handle may be stale or foreign.
    /// - ensures: returns `Some(ordering)` giving the relative list order of
    ///   the two elements; `Some(Equal)` exactly when both handles refer to the
    ///   same live element, so distinct live elements never compare `Equal`.
    /// - provides: the total order the structure exists to maintain. The clause
    ///   splits on the group as the body does. Two elements of one group are
    ///   checked against their labels, which order their keys, since both keys
    ///   carry the group's top. Two of different groups are checked against
    ///   their keys, read by [`Self::key_at`], so the check enters no clause of
    ///   the key. The clause also checks the answer's presence against both
    ///   handles resolving, and reflexivity against the handles once both
    ///   resolve, which reads no handle a third time. Stale or foreign handles
    ///   are answered with `None`, never assumed live.
    /// - fails: returns `None` if either handle is stale or foreign.
    /// - panics: none.
    /// - intension: two label comparisons at most — the groups' labels measured
    ///   from the base group's, read once, then the elements' own — independent
    ///   of the number of elements between them.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for the ordering itself — every pair of handles is
    ///   compared against the rank pair in a naive `Vec` model at the end of
    ///   every generated edit sequence, on the default widths and on a narrow
    ///   circle whose groups split, rebalance and wrap past the base, so label
    ///   or comparison perturbations diverge; L3 residue for the reflexive and
    ///   failure arms, pinned by exact `Ordering` variants and a foreign
    ///   handle.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    /// - witness: `order::tests::comparison_is_reflexive_and_total`
    /// - witness: `order::tests::foreign_handle_is_rejected`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match self.resolve(left).zip(self.resolve(right)) {
        None => ret.is_none(),
        Some((first, second)) => (ret == Some(Ordering::Equal)) == (left == right)
            && if first.group == second.group {
                ret == Some(first.label.cmp(&second.label))
            }
            else {
                ret.is_some()
                    && ret == self
                        .base_label()
                        .and_then(|base| self.key_at(base, first).zip(self.key_at(base, second)))
                        .map(|(first_key, second_key)| first_key.cmp(&second_key))
            },
    })]
    pub fn cmp(
        &self,
        left: Pos,
        right: Pos,
    ) -> Option<Ordering>
    {
        let left_occupied = self.resolve(left)?;
        let right_occupied = self.resolve(right)?;
        if left_occupied.group == right_occupied.group {
            return Some(left_occupied.label.cmp(&right_occupied.label));
        }
        let base = self.base_label()?;
        let left_key = self.key(base, left_occupied)?;
        let right_key = self.key(base, right_occupied)?;
        Some(left_key.cmp(&right_key))
    }

    /// The element immediately after `pos` in order, or `None` at the end (or
    /// if the handle is stale or foreign).
    ///
    /// # Specification
    /// - requires: nothing; any handle may be offered.
    /// - ensures: returns a handle to the element immediately later in the
    ///   order, and `None` both at the last element and for a stale or foreign
    ///   handle.
    /// - provides: the forward step of a walk. The two absences are not told
    ///   apart here; a caller needing them apart asks [`Self::contains`] first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forward adjacency and the tail boundary are paired
    ///   with rejection of removed and foreign handles, including after slot
    ///   reuse.
    /// - witness: `order::tests::navigation_walks_both_ways`
    /// - witness: `order::tests::navigation_rejects_stale_and_foreign_handles`
    #[spec(ensures: |ret| ret == self.resolve(pos)
        .and_then(|occupied| occupied.next)
        .and_then(|index| self.pos_at(index)))]
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
    ///
    /// # Specification
    /// - requires: nothing; any handle may be offered.
    /// - ensures: returns a handle to the element immediately earlier in the
    ///   order, and `None` both at the first element and for a stale or foreign
    ///   handle.
    /// - provides: the backward step of a walk. The two absences are not told
    ///   apart here; a caller needing them apart asks [`Self::contains`] first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — backward adjacency and the head boundary are paired
    ///   with rejection of removed and foreign handles, including after slot
    ///   reuse.
    /// - witness: `order::tests::navigation_walks_both_ways`
    /// - witness: `order::tests::navigation_rejects_stale_and_foreign_handles`
    #[spec(ensures: |ret| ret == self.resolve(pos)
        .and_then(|occupied| occupied.prev)
        .and_then(|index| self.pos_at(index)))]
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
    ///   predicate binds the iterator to this owner and its current head; the
    ///   complete future walk is witnessed independently against the model.
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
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::new_is_empty`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.cursor == self.head
        && core::ptr::eq(core::ptr::from_ref(ret.order), core::ptr::from_ref(self)))]
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
    ///   residue for the front split, where the predecessor is absent, on a
    ///   narrow group whose front labels are exhausted.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::push_front_reverses`
    /// - witness: `order::tests::a_full_front_group_splits_before_its_head`
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
    ///   for the capacity boundary, where a circle of two labels admits exactly
    ///   six elements of the narrowest width and refuses the seventh with the
    ///   exact error variant, and for appends whose rebalance wraps past the
    ///   last group to the base.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::push_back_preserves_order`
    /// - witness: `order::tests::capacity_exhausts_on_a_circle_of_two_labels`
    /// - witness: `order::tests::appends_wrap_the_rebalance_past_the_last_group`
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
    /// - requires: nothing; a stale or foreign handle is refused.
    /// - ensures: on `Ok`, `value` sits immediately after `pos` and before what
    ///   followed `pos` before; the returned handle refers to it and every
    ///   pre-existing handle keeps resolving.
    /// - provides: the handle for the inserted element. The clause checks the
    ///   new adjacency and liveness. Stale or foreign handles return the typed
    ///   refusal; survival of every older handle is witnessed by the model.
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
    ///   exact error variant, and for the split arm, driven by repeated
    ///   insertion behind one fixed anchor.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::insert_after_and_before_place_correctly`
    /// - witness: `order::tests::a_full_group_splits_behind_its_anchor`
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
    /// - requires: nothing; a stale or foreign handle is refused.
    /// - ensures: on `Ok`, `value` sits immediately before `pos` and after what
    ///   preceded `pos` before; the returned handle refers to it and every
    ///   pre-existing handle keeps resolving.
    /// - provides: the handle for the inserted element. The clause checks the
    ///   new adjacency and liveness; the model witnesses surviving handles.
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
    /// - witness: `tests::oracle::matches_reference_model`
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
    ///   freed for reuse (or retired when its generation space is spent), its
    ///   group is freed when it held nothing else, and `pos` together with
    ///   every copy of it is thereafter stale; the remaining elements keep
    ///   their relative order, their labels and their handles.
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
    /// removed element, or its group, does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for the unlinking — the reference model removes at the
    ///   same index and the whole handle and payload sequence is compared after
    ///   every generated edit; L3 residue for the three link arms (interior,
    ///   head, tail), the sole-element arm, the repeat-removal arm, the arm
    ///   that frees a group and moves the base, and the generation-exhaustion
    ///   arm that retires a slot instead of freeing it.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::remove_middle_unlinks_and_invalidates`
    /// - witness: `order::tests::remove_head_and_tail`
    /// - witness: `order::tests::remove_only_element_empties`
    /// - witness: `order::tests::emptying_the_base_group_frees_it_and_moves_the_base`
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
        let group = occupied.group;
        let len = self.len.decremented().ok_or(OrderError::Inconsistent)?;
        // Unlink from the neighbours and the head/tail before freeing the slot.
        match prev_index {
            Some(prev) => self.set_next(prev, next_index)?,
            None => self.head = next_index,
        }
        match next_index {
            Some(next) => self.set_prev(next, prev_index)?,
            None => self.tail = prev_index,
        }
        self.leave_group(group, pos.index, prev_index, next_index)?;
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
            Some(free_generation) => Slot::Free(Free {
                generation: free_generation,
                next_free: self.free_head,
            }),
            None => Slot::Retired,
        };
        let freed = core::mem::replace(slot, replacement);
        if successor.is_some() {
            self.free_head = Some(pos.index);
        }
        self.len = len;
        match freed {
            Slot::Occupied(occupied_slot) => Ok(Some(occupied_slot.value)),
            Slot::Free(_) | Slot::Retired => Err(OrderError::Inconsistent),
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
    /// - intension: two comparisons, independent of interval width.
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
    ///
    /// # Specification
    /// - requires: nothing; an absent slot is answered with `None`.
    /// - ensures: returns a handle stamped with this structure's identity and
    ///   the slot's current generation, and `None` when the slot is absent,
    ///   free, or retired.
    /// - provides: the one site a handle is minted, so every handle in
    ///   circulation carries a generation that was live when it was taken.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh and reused handles preserve owner, index and
    ///   current generation; absent and retired slots yield no handle.
    /// - witness: `order::tests::slot_reuse_distinguishes_generation`
    /// - witness: `order::tests::exhausted_generation_retires_slot_and_allocates_another`
    /// - witness: `order::tests::arena_observers_distinguish_slot_states`
    #[spec(ensures: |ret| ret == self.occupied(index).map(|occupied| Pos {
        structure_id: self.structure_id, index, generation: occupied.generation,
    }))]
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
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the arena's slot at `index`, and `None` when the
    ///   index is past the arena's end or not representable as a position.
    /// - provides: the bounds-checked arena read every lookup routes through,
    ///   so an out-of-range index is an absence rather than a panic.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — occupied, free, retired and out-of-arena positions
    ///   distinguish address preservation from absence.
    /// - witness: `order::tests::arena_observers_distinguish_slot_states`
    #[spec(ensures: |ret| ret.map(core::ptr::from_ref) == usize::try_from(index)
        .ok().and_then(|position| self.slots.get(position)).map(core::ptr::from_ref))]
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
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the live payload at `index`, and `None` when the slot
    ///   is absent, free, or retired.
    /// - provides: the liveness filter over [`Self::slot`], so a freed or
    ///   retired slot never reads as an element.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — only the occupied variant yields its own payload
    ///   address; free, retired and absent slots refuse.
    /// - witness: `order::tests::arena_observers_distinguish_slot_states`
    #[spec(ensures: |ret| ret.map(core::ptr::from_ref) == self.slot(index).and_then(|slot| match *slot {
        Slot::Occupied(ref occupied) => Some(core::ptr::from_ref(occupied)),
        Slot::Free(_) | Slot::Retired => None,
    }))]
    #[inline]
    fn occupied(
        &self,
        index: SlotIndex,
    ) -> Option<&Occupied<T>>
    {
        match *self.slot(index)? {
            Slot::Occupied(ref occupied) => Some(occupied),
            Slot::Free(_) | Slot::Retired => None,
        }
    }

    /// The mutable occupied payload at `index`, if the slot exists and is
    /// occupied.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a unique borrow of the live payload at `index`, and
    ///   `None` when the slot is absent, free, or retired.
    /// - provides: the mutable counterpart of [`Self::occupied`], answering the
    ///   same question under a unique borrow.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mutable access changes the actual occupied payload,
    ///   while free, retired and absent slots return no borrow. The captured
    ///   address avoids retaining an overlapping shared borrow.
    /// - witness: `order::tests::arena_observers_distinguish_slot_states`
    #[spec(
        captures: expected = self.occupied(index).map(core::ptr::from_ref),
        ensures: |ret| ret.as_deref().map(core::ptr::from_ref) == expected,
    )]
    #[inline]
    fn occupied_mut(
        &mut self,
        index: SlotIndex,
    ) -> Option<&mut Occupied<T>>
    {
        let position = usize::try_from(index).ok()?;
        let slot = self.slots.get_mut(position)?;
        match *slot {
            Slot::Occupied(ref mut occupied) => Some(occupied),
            Slot::Free(_) | Slot::Retired => None,
        }
    }

    /// The occupied payload `pos` refers to, if the handle is live: same
    /// structure, occupied slot, matching generation.
    ///
    /// # Specification
    /// - requires: nothing; any handle may be offered.
    /// - ensures: returns the payload `pos` names exactly when all three of the
    ///   handle's claims hold — this structure's identity, an occupied slot,
    ///   and the slot's current generation — and `None` otherwise.
    /// - provides: the single handle-validation site every operation on a
    ///   handle routes through, so a stale handle cannot alias the element that
    ///   reused its slot.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — identity, occupancy and generation are separated by
    ///   foreign, removed, reused and out-of-arena handles; a valid handle
    ///   resolves to its own payload.
    /// - witness: `order::tests::foreign_handle_is_rejected`
    /// - witness: `order::tests::slot_reuse_distinguishes_generation`
    /// - witness: `order::tests::arena_observers_distinguish_slot_states`
    #[spec(ensures: |ret| ret.map(core::ptr::from_ref) == self.occupied(pos.index)
        .filter(|occupied| pos.structure_id == self.structure_id && occupied.generation == pos.generation)
        .map(core::ptr::from_ref))]
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

    /// Sets the `prev` link of the occupied slot at `index`.
    ///
    /// # Specification
    /// - requires: nothing; a dead slot is a typed refusal.
    /// - ensures: the `prev` link is written when it can resolve, and an
    ///   unresolvable write is reported rather than dropped.
    /// - provides: the checked `prev` write every unlink and relink uses.
    /// - fails: [`OrderError::Inconsistent`] when `index` does not name a live
    ///   slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when `index` does not name a live
    /// slot, rather than dropping the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — interior and endpoint unlinking check the written
    ///   predecessor; free and absent indices return the exact inconsistency
    ///   error.
    /// - witness: `order::tests::remove_middle_unlinks_and_invalidates`
    /// - witness: `order::tests::remove_head_and_tail`
    /// - witness: `order::tests::slot_writes_refuse_dead_indices`
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
    /// - requires: nothing; a dead slot is a typed refusal.
    /// - ensures: the `next` link is written when it can resolve, and an
    ///   unresolvable write is reported rather than dropped.
    /// - provides: the checked `next` write every unlink and relink uses.
    /// - fails: [`OrderError::Inconsistent`] when `index` does not name a live
    ///   slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when `index` does not name a live
    /// slot, rather than dropping the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — insertion and unlinking check the written successor;
    ///   free and absent indices return the exact inconsistency error.
    /// - witness: `order::tests::insert_after_and_before_place_correctly`
    /// - witness: `order::tests::remove_middle_unlinks_and_invalidates`
    /// - witness: `order::tests::slot_writes_refuse_dead_indices`
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

    /// The live group at `index`, if the group arena has one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the live group at `index`, and `None` when the index
    ///   is past the arena's end or names a freed group slot.
    /// - provides: the bounds- and liveness-checked group read every label
    ///   lookup routes through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a live group reads as itself, a freed group slot and
    ///   an index past the arena read as absent.
    /// - witness: `order::tests::emptying_the_base_group_frees_it_and_moves_the_base`
    #[spec(ensures: |ret| ret.map(core::ptr::from_ref) == usize::try_from(index.0)
        .ok()
        .and_then(|position| self.groups.get(position))
        .and_then(|slot| match *slot {
            GroupSlot::Live(ref group) => Some(core::ptr::from_ref(group)),
            GroupSlot::Free(_) => None,
        }))]
    #[inline]
    fn group(
        &self,
        index: GroupIndex,
    ) -> Option<&Group>
    {
        let position = usize::try_from(index.0).ok()?;
        match *self.groups.get(position)? {
            GroupSlot::Live(ref group) => Some(group),
            GroupSlot::Free(_) => None,
        }
    }

    /// The mutable live group at `index`, if the group arena has one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a unique borrow of the live group at `index`, and
    ///   `None` when the index is past the arena's end or names a freed group
    ///   slot.
    /// - provides: the mutable counterpart of [`Self::group`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the split and the rebalance write group links and
    ///   labels only through this borrow; the sequence models observe every
    ///   write.
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    #[spec(
        captures: expected = self.group(index).map(core::ptr::from_ref),
        ensures: |ret| ret.as_deref().map(core::ptr::from_ref) == expected,
    )]
    #[inline]
    fn group_mut(
        &mut self,
        index: GroupIndex,
    ) -> Option<&mut Group>
    {
        let position = usize::try_from(index.0).ok()?;
        match *self.groups.get_mut(position)? {
            GroupSlot::Live(ref mut group) => Some(group),
            GroupSlot::Free(_) => None,
        }
    }

    /// The base group's label, which every group's place is measured from.
    ///
    /// # Specification
    /// - requires: nothing; a structure without a base is an absence.
    /// - ensures: returns the label of the group the structure's base names,
    ///   and `None` when the structure has no base or it does not resolve.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sequence models compare every pair of elements by
    ///   their keys, measured from this label, after generated edits that move
    ///   the base.
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    #[spec(ensures: |ret| ret == self.base.and_then(|base| self.group(base)).map(|group| group.label))]
    #[inline]
    fn base_label(&self) -> Option<TopLabel>
    {
        Some(self.group(self.base?)?.label)
    }

    /// The place of a live element in the order: its group's label measured
    /// forward from the base group's label `base`, then its own label.
    ///
    /// # Specification
    /// - requires: nothing; an unresolvable group is an absence.
    /// - ensures: returns the element's group's distance from `base` around the
    ///   circle, beside the element's own label, and `None` when the group does
    ///   not resolve.
    /// - provides: at [`Self::base_label`], the key two elements of different
    ///   groups compare by.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sequence models compare every pair of elements by
    ///   their keys after generated edits that move the base; L3 for a wrapped
    ///   group label, whose distance from the base is exact.
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    /// - witness: `order::tests::top_labels_are_measured_around_the_circle`
    #[spec(ensures: |ret| ret.is_none_or(|key| key.bottom == occupied.label && key.top <= self.top.last()))]
    #[inline]
    fn key(
        &self,
        base: TopLabel,
        occupied: &Occupied<T>,
    ) -> Option<OrderKey>
    {
        self.key_at(base, occupied)
    }

    /// [`Self::key`] without its clause: the reader the clauses that state an
    /// ordering against keys call, so checking one comparison enters no
    /// further clause of the key.
    ///
    /// # Specification
    /// - requires: as [`Self::key`].
    /// - ensures: as [`Self::key`].
    /// - panics: none.
    /// - executable: none — it is the clauses' own reader; [`Self::key`] states
    ///   its clause over this body.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Self::key`].
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    #[inline]
    fn key_at(
        &self,
        base: TopLabel,
        occupied: &Occupied<T>,
    ) -> Option<OrderKey>
    {
        let group = self.group(occupied.group)?;
        Some(OrderKey {
            top: TopLabel(group.label.0.wrapping_sub(base.0) & self.top.last().0),
            bottom: occupied.label,
        })
    }

    /// The group after `index` around the circle: its successor in list
    /// order, or the base group after the last one.
    ///
    /// # Specification
    /// - requires: nothing; a dead group is a typed refusal.
    /// - ensures: returns the group's successor, or the base when it has none.
    /// - provides: the step the rebalance walk and the split's gap take, so a
    ///   walk past the last group continues from the base.
    /// - fails: [`OrderError::Inconsistent`] when `index` does not name a live
    ///   group or the structure has no base.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when `index` does not name a live
    /// group or the structure has no base.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rebalance from the last group but one walks past
    ///   the last group to the base and relabels it.
    /// - witness: `order::tests::a_crowded_circle_spreads_the_groups_after_the_full_one`
    #[spec(ensures: |ret| ret.ok() == self.group(index).and_then(|group| group.next.or(self.base)))]
    #[inline]
    fn successor(
        &self,
        index: GroupIndex,
    ) -> Result<GroupIndex, OrderError>
    {
        let group = self.group(index).ok_or(OrderError::Inconsistent)?;
        group.next.or(self.base).ok_or(OrderError::Inconsistent)
    }

    /// The room from group `from` forward to group `to` around the circle:
    /// the difference of their labels, and the whole circle when they are one
    /// group.
    ///
    /// # Specification
    /// - requires: nothing; a dead group is a typed refusal.
    /// - ensures: on `Ok`, returns `(L(to) - L(from)) mod 2^width` for two
    ///   groups, and `2^width` for one.
    /// - provides: the measure the split's placement and the rebalance's
    ///   density test read.
    /// - fails: [`OrderError::Inconsistent`] when either index does not name a
    ///   live group.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when either index does not name a
    /// live group.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — on a circle of eight labels, a wrapped room and the
    ///   room from a group to itself are exact.
    /// - witness: `order::tests::top_labels_are_measured_around_the_circle`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|room| room.0 > 0 && room.0 <= self.top.universe().0))]
    #[inline]
    fn distance(
        &self,
        from: GroupIndex,
        to: GroupIndex,
    ) -> Result<TopGap, OrderError>
    {
        if from == to {
            return Ok(self.top.universe());
        }
        let start = self.group(from).ok_or(OrderError::Inconsistent)?.label;
        let end = self.group(to).ok_or(OrderError::Inconsistent)?.label;
        Ok(TopGap(u128::from(
            end.0.wrapping_sub(start.0) & self.top.last().0,
        )))
    }

    /// Takes a group slot for `group`, reusing a freed one when there is one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, the returned index names a live group equal to
    ///   `group`.
    /// - provides: the group every split and first insertion creates. Linking
    ///   it among the other groups is the caller's.
    /// - fails: [`OrderError::CapacityExhausted`] when no `u32` group index is
    ///   available; [`OrderError::Inconsistent`] when the free list threads a
    ///   live group.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no `u32` group index is
    /// available, and [`OrderError::Inconsistent`] when the free list threads
    /// a live group.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a freed group slot is taken by the next split before
    ///   the arena grows.
    /// - witness: `order::tests::emptying_the_base_group_frees_it_and_moves_the_base`
    #[spec(
        captures: wanted = group,
        ensures: |ret| ret.as_ref().is_err()
            || ret.as_ref().is_ok_and(|&index| self.group(index) == Some(&wanted)),
    )]
    #[inline]
    fn alloc_group(
        &mut self,
        group: Group,
    ) -> Result<GroupIndex, OrderError>
    {
        if let Some(free) = self.free_group {
            let position = usize::try_from(free.0).map_err(|_ignored| OrderError::Inconsistent)?;
            let slot = self
                .groups
                .get_mut(position)
                .ok_or(OrderError::Inconsistent)?;
            let GroupSlot::Free(next_free) = *slot
            else {
                return Err(OrderError::Inconsistent);
            };
            *slot = GroupSlot::Live(group);
            self.free_group = next_free;
            return Ok(free);
        }
        let index = u32::try_from(self.groups.len())
            .map(GroupIndex)
            .map_err(|_ignored| OrderError::CapacityExhausted)?;
        self.groups.push(GroupSlot::Live(group));
        Ok(index)
    }

    /// Frees the group slot at `index` onto the group free list.
    ///
    /// # Specification
    /// - requires: no element and no group link names the group any more.
    /// - ensures: on `Ok`, the slot is free and heads the group free list.
    /// - provides: the release a group that has emptied, or a first group whose
    ///   element was refused, takes.
    /// - fails: [`OrderError::Inconsistent`] when the index is past the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when the index is past the arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an emptied group's slot is freed and taken again by
    ///   the next split.
    /// - witness: `order::tests::emptying_the_base_group_frees_it_and_moves_the_base`
    /// - witness: `order::tests::retired_slot_capacity_exhaustion_is_typed`
    #[spec(ensures: |ret| ret.is_err() || (self.free_group == Some(index) && self.group(index).is_none()))]
    #[inline]
    fn release_group(
        &mut self,
        index: GroupIndex,
    ) -> Result<(), OrderError>
    {
        let position = usize::try_from(index.0).map_err(|_ignored| OrderError::Inconsistent)?;
        let slot = self
            .groups
            .get_mut(position)
            .ok_or(OrderError::Inconsistent)?;
        *slot = GroupSlot::Free(self.free_group);
        self.free_group = Some(index);
        Ok(())
    }

    /// Records that the element at `element` joined group `index` between
    /// `prev` and `next`: the group counts it, and it opens or closes the
    /// group's run when its neighbour on that side lies outside the group.
    ///
    /// # Specification
    /// - requires: the element is linked between `prev` and `next` and labelled
    ///   in the group.
    /// - ensures: on `Ok`, the group counts one more element, and names it
    ///   first or last where a neighbour is absent or in another group.
    /// - provides: the group bookkeeping every insertion beside an existing
    ///   element ends with.
    /// - fails: [`OrderError::Inconsistent`] when a neighbour or the group does
    ///   not resolve, or the count would overflow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when a neighbour or the group does
    /// not resolve, or the count would overflow.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sequence models check every group's first, last
    ///   and count after every generated edit through the structural invariant.
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    #[spec(
        captures: before = self.group(index).map(|group| group.len),
        ensures: |ret| ret.is_err()
            || self.group(index).is_some_and(|group| before.and_then(|len| len.0.checked_add(1)) == Some(group.len.0)
                && (prev.is_some() || group.first == element)
                && (next.is_some() || group.last == element)),
    )]
    #[inline]
    fn join_group(
        &mut self,
        index: GroupIndex,
        element: SlotIndex,
        prev: Option<SlotIndex>,
        next: Option<SlotIndex>,
    ) -> Result<(), OrderError>
    {
        let opens = match prev {
            Some(before) => self.occupied(before).ok_or(OrderError::Inconsistent)?.group != index,
            None => true,
        };
        let closes = match next {
            Some(after) => self.occupied(after).ok_or(OrderError::Inconsistent)?.group != index,
            None => true,
        };
        let group = self.group_mut(index).ok_or(OrderError::Inconsistent)?;
        group.len = GroupLen(group.len.0.checked_add(1).ok_or(OrderError::Inconsistent)?);
        if opens {
            group.first = element;
        }
        if closes {
            group.last = element;
        }
        Ok(())
    }

    /// Records that the element at `element`, linked between `prev` and
    /// `next` until now, left group `index`: the group stops counting it, a
    /// group left empty is unlinked and freed, and otherwise the group's run
    /// starts or ends at the neighbour when the element opened or closed it.
    ///
    /// # Specification
    /// - requires: the element has just been unlinked from between `prev` and
    ///   `next`, and was labelled in the group.
    /// - ensures: on `Ok`, the group counts one element fewer, or is freed and
    ///   unlinked among the groups when it held only this one, the base moving
    ///   to the next group when the base emptied.
    /// - provides: the group bookkeeping every removal ends with; no other
    ///   label changes.
    /// - fails: [`OrderError::Inconsistent`] when the group does not resolve,
    ///   counts nothing, or names an end whose neighbour is absent.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when the group does not resolve,
    /// counts nothing, or names an end whose neighbour is absent.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sequence models remove at every rank and check
    ///   every group through the structural invariant; L3 for the base group
    ///   emptying, freeing its slot and moving the base.
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    /// - witness: `order::tests::emptying_the_base_group_frees_it_and_moves_the_base`
    #[spec(
        captures: before = self.group(index).map(|group| group.len),
        ensures: |ret| ret.is_err()
            || before.is_some_and(|len| match self.group(index) {
                Some(group) => len.0.checked_sub(1) == Some(group.len.0),
                None => len.0 == 1 && self.free_group == Some(index),
            }),
    )]
    #[inline]
    fn leave_group(
        &mut self,
        index: GroupIndex,
        element: SlotIndex,
        prev: Option<SlotIndex>,
        next: Option<SlotIndex>,
    ) -> Result<(), OrderError>
    {
        let group = self.group_mut(index).ok_or(OrderError::Inconsistent)?;
        let len = group.len.0.checked_sub(1).ok_or(OrderError::Inconsistent)?;
        if len == 0 {
            let emptied = *group;
            match emptied.prev {
                Some(before) => {
                    self.group_mut(before).ok_or(OrderError::Inconsistent)?.next = emptied.next;
                },
                None => self.base = emptied.next,
            }
            if let Some(after) = emptied.next {
                self.group_mut(after).ok_or(OrderError::Inconsistent)?.prev = emptied.prev;
            }
            return self.release_group(index);
        }
        group.len = GroupLen(len);
        if group.first == element {
            group.first = next.ok_or(OrderError::Inconsistent)?;
        }
        if group.last == element {
            group.last = prev.ok_or(OrderError::Inconsistent)?;
        }
        Ok(())
    }

    /// The label of the `position`th of `len` elements spread evenly over a
    /// group's universe, counting from one: `position * universe / (len + 1)`.
    ///
    /// # Specification
    /// - requires: `1 <= position <= len`.
    /// - ensures: on `Some`, returns `position * universe / (len + 1)`, which
    ///   increases strictly with `position` and stays below `universe`.
    /// - provides: the label a split or a first insertion writes.
    /// - fails: returns `None` when an intermediate or the label is not
    ///   representable, which the widths preclude.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact vectors over the narrowest universe pin the
    ///   numerator, the divisor and the rounding down; the widest universe's
    ///   largest group pins the wide product.
    /// - witness: `order::tests::a_group_spreads_its_elements_evenly`
    #[spec(
        requires: position.0 >= 1 && position.0 <= u64::from(len.0),
        ensures: |ret| ret.map(|label| u64::from(label.0))
            == position
                .0
                .checked_mul(universe.0)
                .zip(u64::from(len.0).checked_add(1))
                .and_then(|(scaled, divisor)| scaled.checked_div(divisor))
                .filter(|&label| u32::try_from(label).is_ok()),
    )]
    #[inline]
    fn spread_label(
        universe: BottomUniverse,
        len: GroupLen,
        position: SpreadPosition,
    ) -> Option<BottomLabel>
    {
        let scaled = position.0.checked_mul(universe.0)?;
        let divisor = u64::from(len.0).checked_add(1)?;
        let label = scaled.checked_div(divisor)?;
        u32::try_from(label).ok().map(BottomLabel)
    }

    /// Spreads group `index`'s elements evenly over its universe, labelling
    /// each in the group: the paper's `AssignLabel` over a group.
    ///
    /// # Specification
    /// - requires: the group's run of `len` elements starts at its `first`.
    /// - ensures: on `Ok`, the `k`th element of the run is in the group and
    ///   carries the `k`th of `len` spread labels.
    /// - provides: the relabel that closes a split, for each group it makes and
    ///   the group it cut. The clause checks the run's first element; the whole
    ///   run is checked by the structural invariant the split witnesses assert
    ///   after every insertion.
    /// - fails: [`OrderError::Inconsistent`] when the group or an element of
    ///   its run does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when the group or an element of
    /// its run does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a split of a group of seven at the width eight leaves
    ///   exact spread labels in both groups, observed through the structural
    ///   invariant and the comparison oracle.
    /// - witness: `order::tests::a_full_group_splits_from_its_back`
    #[spec(ensures: |ret| ret.is_err()
        || self.group(index).is_some_and(|group| self.occupied(group.first).is_some_and(|first|
            first.group == index
                && Some(first.label) == Self::spread_label(self.width.universe(), group.len, SpreadPosition(1)))))]
    #[inline]
    fn spread(
        &mut self,
        index: GroupIndex,
    ) -> Result<(), OrderError>
    {
        let group = self.group(index).ok_or(OrderError::Inconsistent)?;
        let (first, len) = (group.first, group.len);
        let universe = self.width.universe();
        let mut cursor = Some(first);
        let mut position = SpreadPosition(1);
        while position.0 <= u64::from(len.0) {
            let at = cursor.ok_or(OrderError::Inconsistent)?;
            let label =
                Self::spread_label(universe, len, position).ok_or(OrderError::Inconsistent)?;
            let occupied = self.occupied_mut(at).ok_or(OrderError::Inconsistent)?;
            occupied.group = index;
            occupied.label = label;
            cursor = occupied.next;
            position = SpreadPosition(position.0.checked_add(1).ok_or(OrderError::Inconsistent)?);
        }
        Ok(())
    }

    /// Makes room on the circle after group `index` by relabelling the groups
    /// that follow it: the paper's Rebalance, after Dietz and Sleator. The
    /// walk takes successors around the circle until the `j`th one lies more
    /// than `j²` labels on, then spreads the `j - 1` groups before it evenly
    /// over that room. Past the last group the walk continues from the base,
    /// so the base and the groups after it may be relabelled; every group's
    /// distance from the base keeps its order.
    ///
    /// # Specification
    /// - requires: nothing; a dead group is a typed refusal.
    /// - ensures: on `Ok`, the group's successor lies two labels on or more,
    ///   and the groups' order around the circle is unchanged.
    /// - provides: the room a split's new group takes.
    /// - fails: [`OrderError::CapacityExhausted`] when the walk returns to the
    ///   group itself with no room `j²` admits: the circle holds too many
    ///   groups; [`OrderError::Inconsistent`] when a group does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when the circle holds too
    /// many groups, and [`OrderError::Inconsistent`] when a group does not
    /// resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact labels after a rebalance that stops short of
    ///   the base and after one that wraps past it and relabels the base; a
    ///   circle of two labels refuses a third group; L2 through the sequence
    ///   model on a narrow circle.
    /// - witness: `order::tests::a_crowded_circle_spreads_the_groups_after_the_full_one`
    /// - witness: `order::tests::capacity_exhausts_on_a_circle_of_two_labels`
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    #[spec(ensures: |ret| ret.is_err()
        || self
            .successor(index)
            .and_then(|after| self.distance(index, after))
            .is_ok_and(|room| room.0 >= 2))]
    #[inline]
    fn rebalance(
        &mut self,
        index: GroupIndex,
    ) -> Result<(), OrderError>
    {
        // How many groups share the room, counting the one that ends it.
        let mut count: u128 = 1;
        let mut cursor = self.successor(index)?;
        let mut room = self.distance(index, cursor)?;
        while room.0 <= count.checked_mul(count).ok_or(OrderError::Inconsistent)? {
            if cursor == index {
                return Err(OrderError::CapacityExhausted);
            }
            cursor = self.successor(cursor)?;
            count = count.checked_add(1).ok_or(OrderError::Inconsistent)?;
            room = self.distance(index, cursor)?;
        }
        let origin = self.group(index).ok_or(OrderError::Inconsistent)?.label;
        let mask = self.top.last().0;
        let mut walked = self.successor(index)?;
        let mut position: u128 = 1;
        while position < count {
            let offset = room
                .0
                .checked_mul(position)
                .and_then(|scaled| scaled.checked_div(count))
                .and_then(|offset| u64::try_from(offset).ok())
                .ok_or(OrderError::Inconsistent)?;
            let after = self.successor(walked)?;
            self.group_mut(walked)
                .ok_or(OrderError::Inconsistent)?
                .label = TopLabel(origin.0.wrapping_add(offset) & mask);
            walked = after;
            position = position.checked_add(1).ok_or(OrderError::Inconsistent)?;
        }
        Ok(())
    }

    /// Cuts the last `keep` elements of group `index` into a new group placed
    /// halfway to the group's successor on the circle, and returns it. The
    /// cut elements keep their labels until the caller spreads the new group.
    ///
    /// # Specification
    /// - requires: the group holds more than `keep` elements, and its successor
    ///   lies two labels on or more.
    /// - ensures: on `Ok`, the returned group follows `index`, holds its last
    ///   `keep` elements, and sits strictly between it and its old successor.
    /// - provides: one step of the paper's Relabel.
    /// - fails: [`OrderError::Inconsistent`] when a group or an element does
    ///   not resolve or the group holds no more than `keep`;
    ///   [`OrderError::CapacityExhausted`] when no group index is available.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when a group or an element does
    /// not resolve, and [`OrderError::CapacityExhausted`] when no group index
    /// is available.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a group of seven at the width eight is cut into three
    ///   and four, the four following.
    /// - witness: `order::tests::a_full_group_splits_from_its_back`
    #[spec(ensures: |ret| ret.as_ref().is_err()
        || ret.as_ref().is_ok_and(|&peeled| self.group(index).is_some_and(|group| group.next == Some(peeled))
            && self.group(peeled).is_some_and(|group| group.prev == Some(index) && group.len == keep)))]
    #[inline]
    fn peel(
        &mut self,
        index: GroupIndex,
        keep: GroupLen,
    ) -> Result<GroupIndex, OrderError>
    {
        let room = self.distance(index, self.successor(index)?)?;
        let group = *self.group(index).ok_or(OrderError::Inconsistent)?;
        let remaining = group
            .len
            .0
            .checked_sub(keep.0)
            .filter(|&left| left > 0)
            .ok_or(OrderError::Inconsistent)?;
        let offset = room
            .0
            .checked_div(2)
            .and_then(|half| u64::try_from(half).ok())
            .ok_or(OrderError::Inconsistent)?;
        let mut first = group.last;
        let mut walked = 1_u32;
        while walked < keep.0 {
            first = self
                .occupied(first)
                .and_then(|occupied| occupied.prev)
                .ok_or(OrderError::Inconsistent)?;
            walked = walked.checked_add(1).ok_or(OrderError::Inconsistent)?;
        }
        let kept_last = self
            .occupied(first)
            .and_then(|occupied| occupied.prev)
            .ok_or(OrderError::Inconsistent)?;
        let peeled = self.alloc_group(Group {
            label: TopLabel(group.label.0.wrapping_add(offset) & self.top.last().0),
            prev: Some(index),
            next: group.next,
            first,
            last: group.last,
            len: keep,
        })?;
        if let Some(after) = group.next {
            self.group_mut(after).ok_or(OrderError::Inconsistent)?.prev = Some(peeled);
        }
        let cut = self.group_mut(index).ok_or(OrderError::Inconsistent)?;
        cut.next = Some(peeled);
        cut.last = kept_last;
        cut.len = GroupLen(remaining);
        Ok(peeled)
    }

    /// Splits the full group `index`: the paper's Relabel. While the group
    /// holds more than half its width, its last half-width elements are cut
    /// into a new group after it, the circle rebalanced first when the group's
    /// successor lies fewer than two labels on, and each new group spread;
    /// then the group itself is spread.
    ///
    /// # Specification
    /// - requires: nothing; a dead group is a typed refusal.
    /// - ensures: on `Ok`, the group holds at most half its width, every group
    ///   the split made holds exactly half, and the order of every element is
    ///   unchanged.
    /// - provides: the room an insertion into a full group takes: every group
    ///   the split leaves has a label between any two of its elements.
    /// - fails: [`OrderError::CapacityExhausted`] when the circle has no room
    ///   for another group or no group index is available;
    ///   [`OrderError::Inconsistent`] when a group or an element does not
    ///   resolve. A refusal leaves the groups already cut in place, each one a
    ///   valid group of the order.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when the circle has no room
    /// for another group, and [`OrderError::Inconsistent`] when a group or an
    /// element does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a group of seven at the width eight splits into three
    ///   and four; repeated insertion behind one anchor and before the head
    ///   splits again and again; L2 through the sequence models.
    /// - witness: `order::tests::a_full_group_splits_from_its_back`
    /// - witness: `order::tests::a_full_group_splits_behind_its_anchor`
    /// - witness: `order::tests::a_full_front_group_splits_before_its_head`
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    #[spec(ensures: |ret| ret.is_err()
        || self.group(index).is_some_and(|group| group.len <= self.width.split_len()))]
    #[inline]
    fn split(
        &mut self,
        index: GroupIndex,
    ) -> Result<(), OrderError>
    {
        let keep = self.width.split_len();
        while self.group(index).ok_or(OrderError::Inconsistent)?.len > keep {
            if self.distance(index, self.successor(index)?)?.0 < 2 {
                self.rebalance(index)?;
            }
            let peeled = self.peel(index, keep)?;
            self.spread(peeled)?;
        }
        self.spread(index)
    }

    /// Where an element inserted between the adjacent `prev_index` and
    /// `next_index` lands: in the predecessor's group, or the successor's at
    /// the front, at the midpoint of the labels between its neighbours in
    /// that group — or nowhere, when the group has no label there.
    ///
    /// # Specification
    /// - requires: at least one of the two is `Some`, and they are adjacent.
    /// - ensures: on `Ok`, returns the group and a label strictly between the
    ///   predecessor's and the successor's labels in that group (`0` and the
    ///   universe standing for an absent one), or `Full` with the group when
    ///   none lies between.
    /// - provides: the placement every insertion beside an existing element
    ///   starts from.
    /// - fails: [`OrderError::Inconsistent`] when a neighbour does not resolve
    ///   or both are absent.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::Inconsistent`] when a neighbour does not resolve
    /// or both are absent.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every generated insertion lands where the sequence
    ///   model puts it; L3 for the full arms behind an anchor and before the
    ///   head.
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    /// - witness: `order::tests::a_full_group_splits_behind_its_anchor`
    /// - witness: `order::tests::a_full_front_group_splits_before_its_head`
    #[spec(ensures: |ret| !matches!(
        ret,
        Ok(Room::Free { label, .. }) if u64::from(label.0) >= self.width.universe().0
    ))]
    #[inline]
    fn room(
        &self,
        prev_index: Option<SlotIndex>,
        next_index: Option<SlotIndex>,
    ) -> Result<Room, OrderError>
    {
        let universe = self.width.universe();
        let (group, lower) = if let Some(prev) = prev_index {
            let occupied = self.occupied(prev).ok_or(OrderError::Inconsistent)?;
            let above = u64::from(occupied.label.0)
                .checked_add(1)
                .ok_or(OrderError::Inconsistent)?;
            (occupied.group, above)
        }
        else {
            let next = next_index.ok_or(OrderError::Inconsistent)?;
            let occupied = self.occupied(next).ok_or(OrderError::Inconsistent)?;
            (occupied.group, 0)
        };
        let upper = match next_index {
            Some(next) => {
                let occupied = self.occupied(next).ok_or(OrderError::Inconsistent)?;
                if occupied.group == group {
                    u64::from(occupied.label.0)
                }
                else {
                    universe.0
                }
            },
            None => universe.0,
        };
        if lower < upper {
            let label = u32::try_from(u64::midpoint(lower, upper))
                .map_err(|_ignored| OrderError::Inconsistent)?;
            return Ok(Room::Free {
                group,
                label: BottomLabel(label),
            });
        }
        Ok(Room::Full(group))
    }

    /// Allocates a slot holding `value` in `group` with the given label and
    /// links, reusing a freed slot when one is available and appending
    /// otherwise.
    ///
    /// The neighbours' links, the structure's head/tail and the group's
    /// bookkeeping are *not* patched here — the caller wires them — but `len`
    /// is incremented for the new element.
    ///
    /// # Specification
    /// - requires: nothing; links may be absent while an insertion is wired.
    /// - ensures: on `Ok`, a slot holding `value` with `group` and `label` is
    ///   threaded between the two, `len` is incremented, and the returned
    ///   handle resolves to the new element.
    /// - provides: the fresh handle every insertion returns. The predicate
    ///   checks the new length, handle, group, label and links without copying
    ///   the moved payload; payload identity is checked by the sequence oracle.
    /// - fails: [`OrderError::CapacityExhausted`] when no `u32` slot index is
    ///   available; [`OrderError::Inconsistent`] when the free list threads a
    ///   slot that is not free.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no `u32` slot index is
    /// available, and [`OrderError::Inconsistent`] when the free list threads a
    /// slot that is not free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh allocation, reuse with a new generation,
    ///   retired-slot refusal and a corrupt free list separate allocation
    ///   routes. Moved payloads are observed through the returned handle and
    ///   the sequence model.
    /// - witness: `order::tests::slot_reuse_distinguishes_generation`
    /// - witness: `order::tests::retired_slot_capacity_exhaustion_is_typed`
    /// - witness: `order::tests::allocation_refuses_a_broken_free_list`
    #[spec(
        captures: length = self.len.0,
        ensures: |ret| ret.as_ref().map_or_else(
            |error| matches!(error, OrderError::CapacityExhausted | OrderError::Inconsistent),
            |pos| Some(self.len.0) == length.checked_add(1)
                && self.resolve(*pos).is_some_and(|occupied| occupied.group == group
                    && occupied.label == label
                    && occupied.prev == prev && occupied.next == next)),
    )]
    #[inline]
    fn alloc(
        &mut self,
        group: GroupIndex,
        label: BottomLabel,
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
                Slot::Free(ref free) => Free {
                    generation: free.generation,
                    next_free: free.next_free,
                },
                Slot::Occupied(_) | Slot::Retired => return Err(OrderError::Inconsistent),
            };
            *slot = Slot::Occupied(Occupied {
                generation: free.generation,
                group,
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
            group,
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

    /// Inserts `value` into the empty structure: one group, the base, at the
    /// circle's zero, holding the element at the middle of its universe.
    ///
    /// # Specification
    /// - requires: the structure is empty.
    /// - ensures: on `Ok`, the structure holds the one element, in the base
    ///   group, and the returned handle resolves to it; on a refused element
    ///   the group slot taken for it is freed again.
    /// - provides: the insertion every operation on an empty structure routes
    ///   through.
    /// - fails: [`OrderError::CapacityExhausted`] when no slot or group index
    ///   is available; [`OrderError::Inconsistent`] on a corrupted arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no slot or group index
    /// is available, and [`OrderError::Inconsistent`] on a corrupted arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first insertion and one into a bounded arena whose
    ///   only slot is retired, which frees the group it took.
    /// - witness: `order::tests::push_back_preserves_order`
    /// - witness: `order::tests::retired_slot_capacity_exhaustion_is_typed`
    #[spec(
        requires: self.len == LiveLen::ZERO && self.base.is_none(),
        ensures: |ret| ret.as_ref().map_or_else(|_| self.base.is_none(), |pos| self.first() == Some(*pos)
            && self.last() == Some(*pos)
            && self.resolve(*pos).is_some_and(|occupied| Some(occupied.group) == self.base)),
    )]
    #[inline]
    fn insert_first(
        &mut self,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        let label = Self::spread_label(self.width.universe(), GroupLen(1), SpreadPosition(1))
            .ok_or(OrderError::Inconsistent)?;
        // The group's run is named once the element has its slot.
        let group = self.alloc_group(Group {
            label: TopLabel(0),
            prev: None,
            next: None,
            first: SlotIndex(0),
            last: SlotIndex(0),
            len: GroupLen(1),
        })?;
        match self.alloc(group, label, None, None, value) {
            Ok(pos) => {
                let created = self.group_mut(group).ok_or(OrderError::Inconsistent)?;
                created.first = pos.index;
                created.last = pos.index;
                self.base = Some(group);
                self.head = Some(pos.index);
                self.tail = Some(pos.index);
                Ok(pos)
            },
            Err(error) => {
                self.release_group(group)?;
                Err(error)
            },
        }
    }

    /// Inserts `value` between the adjacent elements `prev_index` and
    /// `next_index` (either may be `None` at a list end; both `None` only for
    /// an empty structure).
    ///
    /// Takes the midpoint of the neighbours' labels in the group the element
    /// joins when one lies between, otherwise splits that group first (see
    /// [`Self::split`]).
    ///
    /// # Specification
    /// - requires: `prev_index` and `next_index` are adjacent in list order,
    ///   either `None` at a list end; both `None` only for an empty structure.
    /// - ensures: on `Ok`, `value` sits between the two, keys remain strictly
    ///   increasing in list order, and the returned handle resolves to the new
    ///   element.
    /// - provides: the insertion every public insert routes through. The clause
    ///   checks the adjacency each call site reads — the predecessor's own
    ///   `next` link, or the end the structure records — while the
    ///   postcondition stays prose, because strict key increase is a property
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sequence models check placement and surviving
    ///   values; L3 separates a direct gap, a front or anchored split, capacity
    ///   refusal and a dangling neighbour.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    /// - witness: `order::tests::a_full_front_group_splits_before_its_head`
    /// - witness: `order::tests::a_full_group_splits_behind_its_anchor`
    /// - witness: `order::tests::capacity_exhausts_on_a_circle_of_two_labels`
    /// - witness: `order::tests::corrupt_link_insert_is_typed`
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
        if prev_index.is_none() && next_index.is_none() {
            return self.insert_first(value);
        }
        let (group, label) = match self.room(prev_index, next_index)? {
            Room::Free { group, label } => (group, label),
            Room::Full(full) => {
                self.split(full)?;
                match self.room(prev_index, next_index)? {
                    Room::Free { group, label } => (group, label),
                    Room::Full(_) => return Err(OrderError::Inconsistent),
                }
            },
        };
        self.link_new(prev_index, next_index, group, label, value)
    }

    /// Allocates `value` in `group` with `label` and wires it between
    /// `prev_index` and `next_index`, updating the neighbours' links, the
    /// head/tail and the group's bookkeeping.
    ///
    /// # Specification
    /// - requires: `prev_index` and `next_index` are adjacent in list order,
    ///   either `None` at a list end, and `label` lies between their labels in
    ///   `group`.
    /// - ensures: on `Ok`, `value` with `group` and `label` is wired between
    ///   the two, the neighbours' links and the head/tail are updated, and the
    ///   returned handle resolves to the new element.
    /// - provides: the linked element's handle. The clauses check the caller's
    ///   adjacency and the whole wiring — the new element's group, label and
    ///   links, both neighbours' back-links, and the head or tail an absent
    ///   neighbour moves — while the payload identity stays prose, because
    ///   `value` is moved into the slot.
    /// - fails: [`OrderError::CapacityExhausted`] when no slot is available;
    ///   [`OrderError::Inconsistent`] when a neighbour index or the group does
    ///   not name a live slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`OrderError::CapacityExhausted`] when no slot is available, and
    /// [`OrderError::Inconsistent`] when a neighbour index or the group does
    /// not name a live slot.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the independent sequence model detects lost, repeated
    ///   or misplaced payloads; L3 covers both ends, interior insertion and
    ///   slot reuse.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::insert_after_and_before_place_correctly`
    /// - witness: `order::tests::slot_reuse_distinguishes_generation`
    #[inline]
    #[spec(
        requires: match (prev_index, next_index) {
            (Some(prev), Some(next)) => self
                .occupied(prev)
                .is_some_and(|occupied| occupied.next == Some(next)),
            (Some(prev), None) => self.tail == Some(prev),
            (None, Some(next)) => self.head == Some(next),
            (None, None) => false,
        },
        ensures: |ret| ret.as_ref().ok().is_none_or(|pos| self
            .resolve(*pos)
            .is_some_and(|occupied| occupied.group == group
                && occupied.label == label
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
        group: GroupIndex,
        label: BottomLabel,
        value: T,
    ) -> Result<Pos, OrderError>
    {
        let pos = self.alloc(group, label, prev_index, next_index, value)?;
        match prev_index {
            Some(prev) => self.set_next(prev, Some(pos.index))?,
            None => self.head = Some(pos.index),
        }
        match next_index {
            Some(next) => self.set_prev(next, Some(pos.index))?,
            None => self.tail = Some(pos.index),
        }
        self.join_group(group, pos.index, prev_index, next_index)?;
        Ok(pos)
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

    /// Iterates `(handle, &payload)` over every element in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.iter()
    }
}

impl<'order, T> Iterator for Iter<'order, T>
{
    type Item = (Pos, &'order T);

    /// The next element in order, paired with its handle.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields each live element exactly once in list order, pairing
    ///   a handle carrying that element's current generation with a borrow of
    ///   its payload, and `None` once the walk passes the last element.
    /// - provides: the forward step of the in-order walk.
    /// - fails: the walk stops rather than looping if a link does not resolve,
    ///   which no sequence of public operations produces.
    /// - panics: none.
    /// - intension: one `next` link is followed per call, holding one slot
    ///   index of state.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the model checks the entire yielded sequence; L3
    ///   separates each cursor advance, absorbing end-of-list absence and
    ///   refusal at a dangling link. No claim is made about malformed cycles.
    /// - witness: `tests::oracle::matches_reference_model`
    /// - witness: `order::tests::iterator_follows_links_and_preserves_terminal_absence`
    #[spec(
        captures: before = self.cursor,
        ensures: |ret| ret.as_ref().map_or_else(
            || self.cursor == before && before.is_none_or(|index| self.order.occupied(index).is_none()),
            |pair| before == Some(pair.0.index) && self.order.pos_at(pair.0.index) == Some(pair.0)
                && self.order.occupied(pair.0.index).is_some_and(|occupied| self.cursor == occupied.next
                    && core::ptr::eq(core::ptr::from_ref(pair.1), &raw const occupied.value))),
    )]
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
mod tests;
