//! The L machine's two-region store: an append-only **heap region** of values,
//! memo cells and environment bindings, and a walkable **frame region** of
//! continuation frames.
//!
//! # The heap region
//!
//! [`HeapValue`]s are immutable once allocated and addressed by
//! [`HeapValueId`]; sharing a value is sharing its address. A thunk owns one
//! memo [`CellId`], the store's only mutable state: a cell is
//! [`MemoState::Unforced`] until a force opens it, [`MemoState::InProgress`]
//! while the forcing runs (the black hole), and [`MemoState::Forced`] once the
//! forcing's value is written back. Cell identity is nominal: two thunks share
//! a cell exactly when they are one allocation. The store enforces the
//! transition table: a write-back or a decline of a cell not in progress is
//! refused, and nothing leaves [`MemoState::Forced`].
//!
//! Environments are persistent chains in the heap region: an [`Environment`]
//! is the innermost binding of its producer chain and of its covalue chain, so
//! extending one never copies it and a closure captures one by value.
//!
//! # The frame region
//!
//! Frames stack in pushing order and every frame carries a fresh
//! [`FrameSerial`]. A [`ContinuationMark`] names a height together with the
//! serial of the frame directly below it, so a mark taken before a frame was
//! popped and another pushed at the same height is recognized as stale rather
//! than resumed into the wrong continuation. Returning through a mark shrinks
//! the region to it; an update frame dropped by a shrink declines its cell
//! back to [`MemoState::Unforced`], so an abandoned forcing leaves no black
//! hole behind.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;

use crate::boundary::FamilyAddress as _;
use crate::boundary::FrameHeight;
use crate::boundary::FrameSerial;
use crate::boundary::NodeCount;
use crate::boundary::address_wrapper;
use crate::il::CommandId;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::ProducerId;

address_wrapper! {
    /// The address of a [`HeapValue`] in a [`Store`].
    pub struct HeapValueId;
}

address_wrapper! {
    /// The address of a memo cell in a [`Store`].
    pub struct CellId;
}

address_wrapper! {
    /// The address of one producer binding of an environment chain.
    pub struct ValueBindingId;
}

address_wrapper! {
    /// The address of one covalue binding of an environment chain.
    pub struct CovalueBindingId;
}

/// A machine value: what a producer evaluates to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum HeapValue
{
    /// A base-type literal.
    Literal(Literal),
    /// A constructor applied to evaluated fields.
    Constructed
    {
        /// The head.
        tag: ConstructorTag,
        /// The fields, left to right.
        fields: Box<[HeapValueId]>,
    },
    /// A thunk: a suspended command, the environment it closes over, and the
    /// memo cell its forcing writes back to.
    Thunk
    {
        /// The suspended command, binding one covariable.
        body: CommandId,
        /// The captured environment.
        environment: Environment,
        /// The memo cell.
        cell: CellId,
    },
    /// A negative value: a copattern object or a suspended context capture,
    /// closed over its environment.
    Closure
    {
        /// The closed producer: a [`crate::ProducerNode::Cocase`] or a
        /// [`crate::ProducerNode::Mu`].
        producer: ProducerId,
        /// The captured environment.
        environment: Environment,
    },
    /// A constant with no body to run: an owed or refused declaration, which
    /// the machine carries as itself.
    Opaque(ConstantIndex),
}

/// The state of a memo cell.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MemoState
{
    /// Never forced, or forced and abandoned.
    Unforced,
    /// A forcing is running: the black hole.
    InProgress,
    /// Forced, with the value the forcing wrote back.
    Forced(HeapValueId),
}

/// What opening a force on a cell found.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ForceEntry
{
    /// The cell was forced: its cached value, unchanged.
    Cached(HeapValueId),
    /// The cell was unforced and is now in progress; the opener owns the
    /// write-back or the decline.
    Opened,
    /// The cell was already in progress: a re-entrant force, which runs the
    /// body inline and writes nothing.
    Reentrant,
}

/// The innermost producer binding of an environment, or none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueScope
{
    /// No producer is bound.
    Empty,
    /// The innermost binding.
    Innermost(ValueBindingId),
}

/// The innermost covalue binding of an environment, or none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CovalueScope
{
    /// No covariable is bound.
    Empty,
    /// The innermost binding.
    Innermost(CovalueBindingId),
}

/// An environment: the producer chain and the covalue chain a command runs
/// under.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Environment
{
    /// The producer bindings, innermost first.
    values: ValueScope,
    /// The covalue bindings, innermost first.
    covalues: CovalueScope,
}

impl Environment
{
    /// The environment binding nothing.
    pub const EMPTY: Self = Self {
        values: ValueScope::Empty,
        covalues: CovalueScope::Empty,
    };

    /// The producer chain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn values(self) -> ValueScope
    {
        self.values
    }

    /// The covalue chain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn covalues(self) -> CovalueScope
    {
        self.covalues
    }
}

/// One producer binding: the value and the chain it extends.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ValueBinding
{
    /// The bound value.
    value: HeapValueId,
    /// The chain this binding extends.
    outer: ValueScope,
}

/// One covalue binding: the continuation mark and the chain it extends.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct CovalueBinding
{
    /// The bound continuation.
    mark: ContinuationMark,
    /// The chain this binding extends.
    outer: CovalueScope,
}

/// A continuation: a height of the frame region, and the serial of the frame
/// directly below that height when the mark was taken.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContinuationMark
{
    /// The height the continuation starts at.
    height: FrameHeight,
    /// The serial of the frame at `height - 1`, or the base serial at height
    /// `0`.
    serial: FrameSerial,
}

impl ContinuationMark
{
    /// The base of the frame region: the terminal continuation `★`.
    pub const BASE: Self = Self {
        height: FrameHeight::ZERO,
        serial: FrameSerial::BASE,
    };

    /// The height the continuation starts at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn height(self) -> FrameHeight
    {
        self.height
    }
}

/// A continuation frame.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Frame
{
    /// A pending observation with its evaluated producer arguments.
    Destructor
    {
        /// The head.
        tag: DestructorTag,
        /// The evaluated producer arguments, left to right.
        arguments: Box<[HeapValueId]>,
    },
    /// A pending value binder `μ̃x. s`.
    Bind
    {
        /// The command, binding one producer variable.
        body: CommandId,
        /// The environment it runs under.
        environment: Environment,
    },
    /// A pending pattern match.
    Case
    {
        /// The [`crate::ConsumerNode::Case`] whose arms are tried.
        arms: ConsumerId,
        /// The environment the chosen arm runs under.
        environment: Environment,
    },
    /// The write-back of a forcing: the value arriving here is the cell's.
    Update
    {
        /// The cell in progress.
        cell: CellId,
    },
}

/// One frame and the serial it was pushed under.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct FrameEntry
{
    /// The frame.
    frame: Frame,
    /// Its serial.
    serial: FrameSerial,
}

/// The families of the heap region, for a full-region refusal.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HeapFamily
{
    /// The values.
    Values,
    /// The memo cells.
    Cells,
    /// The producer bindings.
    ValueBindings,
    /// The covalue bindings.
    CovalueBindings,
}

/// Why the store refused an operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StoreFault
{
    /// A heap family has reached its address ceiling.
    RegionFull(HeapFamily),
    /// The frame serials are exhausted.
    SerialsExhausted,
    /// A value address names no value of this store.
    DanglingValue(HeapValueId),
    /// A cell address names no cell of this store.
    DanglingCell(CellId),
    /// A transition needs the cell in progress, and it is not.
    CellNotInProgress
    {
        /// The cell.
        cell: CellId,
        /// The state it was found in.
        found: MemoState,
    },
    /// A continuation mark names a frame no longer on the region.
    StaleMark(ContinuationMark),
}

impl fmt::Display for StoreFault
{
    /// Names the refused operation's subject.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::RegionFull(family) => {
                let name = match family {
                    | HeapFamily::Values => "value",
                    | HeapFamily::Cells => "cell",
                    | HeapFamily::ValueBindings => "producer binding",
                    | HeapFamily::CovalueBindings => "covalue binding",
                };
                write!(f, "the {name} family of the heap is full")
            },
            | Self::SerialsExhausted => f.write_str("the frame serials are exhausted"),
            | Self::DanglingValue(id) => write!(f, "value {id} is not in the store"),
            | Self::DanglingCell(id) => write!(f, "cell {id} is not in the store"),
            | Self::CellNotInProgress { cell, .. } => write!(f, "cell {cell} is not in progress"),
            | Self::StaleMark(mark) => write!(
                f,
                "the continuation at height {} names a popped frame",
                mark.height
            ),
        }
    }
}

impl core::error::Error for StoreFault
{
}

/// The two-region store.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Store
{
    /// The heap's values.
    values: Vec<HeapValue>,
    /// The memo cells.
    cells: Vec<MemoState>,
    /// The producer bindings of every environment chain.
    value_bindings: Vec<ValueBinding>,
    /// The covalue bindings of every environment chain.
    covalue_bindings: Vec<CovalueBinding>,
    /// The frame region, bottom first.
    frames: Vec<FrameEntry>,
    /// The serial of the most recently pushed frame, or the base serial.
    last_serial: FrameSerial,
}

impl Store
{
    /// An empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Allocate a value in the heap region.
    ///
    /// # Specification
    /// - requires: every address `value` names was allocated by this store.
    /// - ensures: on success a fresh address, above every value address already
    ///   allocated, reading back as `value`.
    /// - provides: the one append point of the value family.
    /// - fails: [`StoreFault::RegionFull`] at the address ceiling, the store
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dense distinct allocations, exact retrieval and the
    ///   first missing offset distinguish address reuse, a shifted offset and a
    ///   misplaced value. The helper covers the ceiling with zero-sized slices;
    ///   the store is not populated to the ceiling.
    /// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.values.len()],
        ensures: |ret| match ret {
            | Ok(id) => usize::try_from(u32::from(id)) == Ok(entry)
                && entry.checked_add(1) == Some(self.values.len()),
            | Err(error) => error == StoreFault::RegionFull(HeapFamily::Values)
                && self.values.len() == entry,
        },
    )]
    pub fn allocate(
        &mut self,
        value: HeapValue,
    ) -> Result<HeapValueId, StoreFault>
    {
        let id =
            HeapValueId::next_in(&self.values).ok_or(StoreFault::RegionFull(HeapFamily::Values))?;
        self.values.push(value);
        Ok(id)
    }

    /// Resolve a value address, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some(value)` exactly when the store allocated the address.
    /// - provides: the read side of the value family.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, first, last and exact-end reads observe
    ///   distinct values, distinguishing a wrong offset and endpoint
    ///   acceptance.
    /// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| match ret {
        | Some(value) => usize::try_from(u32::from(id)).ok()
            .and_then(|offset| self.values.get(offset))
            .is_some_and(|held| core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(value))),
        | None => usize::try_from(u32::from(id)).map_or(true, |offset| offset >= self.values.len()),
    })]
    pub fn value(
        &self,
        id: HeapValueId,
    ) -> Option<&HeapValue>
    {
        id.read_in(&self.values)
    }

    /// Allocate a fresh unforced memo cell.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success a fresh address, above every cell address already
    ///   allocated, whose state is [`MemoState::Unforced`].
    /// - provides: the nominal identity of a thunk's memo.
    /// - fails: [`StoreFault::RegionFull`] at the address ceiling, the store
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dense fresh allocation and aliasing exactly by
    ///   address separate nominal identity from structural identity.
    /// - witness: `store::tests::cell_write_back_is_shared_and_nominal`
    /// - witness: `tests::csl_fibration::nominal_identity_freshness_and_alias_coherence`
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.cells.len()],
        ensures: |ret| match ret {
            | Ok(id) => usize::try_from(u32::from(id)) == Ok(entry)
                && entry.checked_add(1) == Some(self.cells.len())
                && self.cell(id) == Some(MemoState::Unforced),
            | Err(error) => error == StoreFault::RegionFull(HeapFamily::Cells)
                && self.cells.len() == entry,
        },
    )]
    pub fn allocate_cell(&mut self) -> Result<CellId, StoreFault>
    {
        let id = CellId::next_in(&self.cells).ok_or(StoreFault::RegionFull(HeapFamily::Cells))?;
        self.cells.push(MemoState::Unforced);
        Ok(id)
    }

    /// The state of a cell, or `None` when the address dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some(state)` exactly when the store allocated the cell.
    /// - provides: the read side of the cell family.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and exact-end addresses are absent, while two
    ///   cells in different states retain their individual identity. Wrong
    ///   offsets and fabricated default states change the observer.
    /// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
    /// - witness: `store::tests::cell_write_back_is_shared_and_nominal`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret == usize::try_from(u32::from(id)).ok()
        .and_then(|offset| self.cells.get(offset)).copied()
    )]
    pub fn cell(
        &self,
        id: CellId,
    ) -> Option<MemoState>
    {
        id.read_in(&self.cells).copied()
    }

    /// Open a force on a cell.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`ForceEntry::Cached`] with the cached value for a forced
    ///   cell; [`ForceEntry::Opened`] for an unforced cell, which is now in
    ///   progress; [`ForceEntry::Reentrant`] for a cell already in progress,
    ///   which is unchanged. No other cell changes.
    /// - provides: the entry of the call-by-need protocol and its black hole.
    /// - fails: [`StoreFault::DanglingCell`], the store unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three states separate the three entries; the
    ///   generated traces assert that no other cell changes.
    /// - witness: `store::tests::cell_write_back_is_shared_and_nominal`
    /// - witness: `tests::csl_fibration::black_hole_discipline_under_reentry`
    /// - witness: `tests::csl_fibration::frame_preservation_under_forcing`
    /// - witness: `store::tests::cell_refusals_preserve_state_and_error_precedence`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.cell(cell)],
        ensures: |ret| match entry {
            | None => ret == Err(StoreFault::DanglingCell(cell)) && self.cell(cell).is_none(),
            | Some(MemoState::Unforced) => ret == Ok(ForceEntry::Opened)
                && self.cell(cell) == Some(MemoState::InProgress),
            | Some(MemoState::InProgress) => ret == Ok(ForceEntry::Reentrant)
                && self.cell(cell) == entry,
            | Some(MemoState::Forced(value)) => ret == Ok(ForceEntry::Cached(value))
                && self.cell(cell) == entry,
        },
    )]
    pub fn begin_force(
        &mut self,
        cell: CellId,
    ) -> Result<ForceEntry, StoreFault>
    {
        let state = self.cell_mut(cell)?;
        match *state {
            | MemoState::Forced(value) => Ok(ForceEntry::Cached(value)),
            | MemoState::InProgress => Ok(ForceEntry::Reentrant),
            | MemoState::Unforced => {
                *state = MemoState::InProgress;
                Ok(ForceEntry::Opened)
            },
        }
    }

    /// Write a forcing's value back to its cell.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cell, in progress on entry, is [`MemoState::Forced`] with
    ///   exactly `value`; no other cell changes.
    /// - provides: the write-back that makes a second force a cache hit.
    /// - fails: [`StoreFault::DanglingValue`] or [`StoreFault::DanglingCell`]
    ///   for an address this store did not allocate, and
    ///   [`StoreFault::CellNotInProgress`] for a cell unforced or already
    ///   forced; the store is then unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a write-back to a cell in progress, and one to a cell
    ///   in each other state, separate the transition from its refusals.
    /// - witness: `store::tests::cell_write_back_is_shared_and_nominal`
    /// - witness: `tests::csl_fibration::write_back_purity_caches_the_exact_probe_allocation`
    /// - witness: `tests::csl_fibration::black_hole_discipline_under_reentry`
    /// - witness: `store::tests::cell_refusals_preserve_state_and_error_precedence`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.cell(cell)],
        ensures: |ret| if self.value(value).is_none() {
            ret == Err(StoreFault::DanglingValue(value)) && self.cell(cell) == entry
        } else { match entry {
            | None => ret == Err(StoreFault::DanglingCell(cell)) && self.cell(cell).is_none(),
            | Some(MemoState::InProgress) => ret.is_ok()
                && self.cell(cell) == Some(MemoState::Forced(value)),
            | Some(found) => ret == Err(StoreFault::CellNotInProgress { cell, found })
                && self.cell(cell) == entry,
        } },
    )]
    pub fn write_back(
        &mut self,
        cell: CellId,
        value: HeapValueId,
    ) -> Result<(), StoreFault>
    {
        if self.value(value).is_none() {
            return Err(StoreFault::DanglingValue(value));
        }
        let state = self.cell_mut(cell)?;
        if *state != MemoState::InProgress {
            return Err(StoreFault::CellNotInProgress {
                cell,
                found: *state,
            });
        }
        *state = MemoState::Forced(value);
        Ok(())
    }

    /// Decline a forcing: return its cell to unforced.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cell, in progress on entry, is [`MemoState::Unforced`];
    ///   no other cell changes.
    /// - provides: the release of a black hole whose forcing was abandoned.
    /// - fails: [`StoreFault::DanglingCell`], and
    ///   [`StoreFault::CellNotInProgress`] for a cell not in progress; the
    ///   store is then unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each memo state and a missing cell separate
    ///   successful release, wrong-state refusal and dangling refusal. Exact
    ///   error payloads and post-states expose a cleared cache or an unreleased
    ///   black hole.
    /// - witness: `store::tests::frames_shrink_to_a_mark`
    /// - witness: `tests::csl_fibration::black_hole_discipline_under_reentry`
    /// - witness: `store::tests::cell_refusals_preserve_state_and_error_precedence`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.cell(cell)],
        ensures: |ret| match entry {
            | None => ret == Err(StoreFault::DanglingCell(cell)) && self.cell(cell).is_none(),
            | Some(MemoState::InProgress) => ret.is_ok() && self.cell(cell) == Some(MemoState::Unforced),
            | Some(found) => ret == Err(StoreFault::CellNotInProgress { cell, found })
                && self.cell(cell) == entry,
        },
    )]
    pub fn decline(
        &mut self,
        cell: CellId,
    ) -> Result<(), StoreFault>
    {
        let state = self.cell_mut(cell)?;
        if *state != MemoState::InProgress {
            return Err(StoreFault::CellNotInProgress {
                cell,
                found: *state,
            });
        }
        *state = MemoState::Unforced;
        Ok(())
    }

    /// The number of values allocated.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value_count(&self) -> NodeCount
    {
        NodeCount::from(self.values.len())
    }

    /// The number of cells allocated.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cell_count(&self) -> NodeCount
    {
        NodeCount::from(self.cells.len())
    }

    /// Extend an environment's producer chain with one binding.
    ///
    /// # Specification
    /// - requires: `value` and the chain were allocated by this store.
    /// - ensures: on success an environment whose producer index `0` reads
    ///   `value` and whose index `i + 1` reads what index `i` read in
    ///   `environment`; the covalue chain is unchanged.
    /// - provides: the one way a producer variable is bound.
    /// - fails: [`StoreFault::RegionFull`], the store unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lookup at index `0` and at index `1` after two
    ///   bindings, and past the chain, separate the shift from the base.
    /// - witness: `store::tests::environments_bind_innermost_first`
    /// - witness: `store::tests::both_binding_chains_preserve_outer_and_opposite_scopes`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.value_bindings.len()],
        ensures: |ret| match ret {
            | Ok(extended) => extended.covalues == environment.covalues
                && entry.checked_add(1) == Some(self.value_bindings.len())
                && match extended.values {
                    | ValueScope::Empty => false,
                    | ValueScope::Innermost(id) => usize::try_from(u32::from(id)) == Ok(entry)
                        && id.read_in(&self.value_bindings).is_some_and(|binding|
                            binding.value == value && binding.outer == environment.values),
                },
            | Err(error) => error == StoreFault::RegionFull(HeapFamily::ValueBindings)
                && self.value_bindings.len() == entry,
        },
    )]
    pub fn bind_value(
        &mut self,
        environment: Environment,
        value: HeapValueId,
    ) -> Result<Environment, StoreFault>
    {
        let id = ValueBindingId::next_in(&self.value_bindings)
            .ok_or(StoreFault::RegionFull(HeapFamily::ValueBindings))?;
        self.value_bindings.push(ValueBinding {
            value,
            outer: environment.values,
        });
        Ok(Environment {
            values: ValueScope::Innermost(id),
            covalues: environment.covalues,
        })
    }

    /// Extend an environment's covalue chain with one binding.
    ///
    /// # Specification
    /// - requires: the chain was allocated by this store.
    /// - ensures: on success an environment whose covariable index `0` reads
    ///   `mark` and whose index `i + 1` reads what index `i` read in
    ///   `environment`; the producer chain is unchanged.
    /// - provides: the one way a covariable is bound.
    /// - fails: [`StoreFault::RegionFull`], the store unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and two-element chains, distinct payloads,
    ///   exact-end indices and dangling links distinguish reversed order, an
    ///   off-by-one index and accidental coupling of the two namespaces.
    /// - witness: `store::tests::environments_bind_innermost_first`
    /// - witness: `store::tests::both_binding_chains_preserve_outer_and_opposite_scopes`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.covalue_bindings.len()],
        ensures: |ret| match ret {
            | Ok(extended) => extended.values == environment.values
                && entry.checked_add(1) == Some(self.covalue_bindings.len())
                && match extended.covalues {
                    | CovalueScope::Empty => false,
                    | CovalueScope::Innermost(id) => usize::try_from(u32::from(id)) == Ok(entry)
                        && id.read_in(&self.covalue_bindings).is_some_and(|binding|
                            binding.mark == mark && binding.outer == environment.covalues),
                },
            | Err(error) => error == StoreFault::RegionFull(HeapFamily::CovalueBindings)
                && self.covalue_bindings.len() == entry,
        },
    )]
    pub fn bind_covalue(
        &mut self,
        environment: Environment,
        mark: ContinuationMark,
    ) -> Result<Environment, StoreFault>
    {
        let id = CovalueBindingId::next_in(&self.covalue_bindings)
            .ok_or(StoreFault::RegionFull(HeapFamily::CovalueBindings))?;
        self.covalue_bindings.push(CovalueBinding {
            mark,
            outer: environment.covalues,
        });
        Ok(Environment {
            values: environment.values,
            covalues: CovalueScope::Innermost(id),
        })
    }

    /// The value a producer index reads in an environment, or `None` when the
    /// index counts past its chain.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value of the binding `index` links out from the
    ///   innermost; `None` past the chain or at a dangling link.
    /// - provides: variable lookup, iterative over the chain.
    /// - fails: `None`, the one reason an unbound index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and two-element chains, distinct payloads,
    ///   exact-end indices and dangling links distinguish reversed order, an
    ///   off-by-one index and accidental coupling of the two namespaces.
    /// - witness: `store::tests::environments_bind_innermost_first`
    /// - witness: `store::tests::both_binding_chains_preserve_outer_and_opposite_scopes`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret == usize::try_from(u32::from(index)).ok()
        .and_then(|offset| self.bound_values(environment).nth(offset))
    )]
    pub fn lookup_value(
        &self,
        environment: Environment,
        index: DeBruijnIndex,
    ) -> Option<HeapValueId>
    {
        let mut scope = environment.values;
        let mut remaining = u32::from(index);
        loop {
            let ValueScope::Innermost(id) = scope
            else {
                return None;
            };
            let binding = id.read_in(&self.value_bindings)?;
            let Some(next) = remaining.checked_sub(1)
            else {
                return Some(binding.value);
            };
            remaining = next;
            scope = binding.outer;
        }
    }

    /// The continuation a covariable index reads in an environment, or `None`
    /// when the index counts past its chain.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the mark of the binding `index` links out from the innermost;
    ///   `None` past the chain or at a dangling link.
    /// - provides: covariable lookup, iterative over the chain.
    /// - fails: `None`, the one reason an unbound index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and two-element chains, distinct payloads,
    ///   exact-end indices and dangling links distinguish reversed order, an
    ///   off-by-one index and accidental coupling of the two namespaces.
    /// - witness: `store::tests::environments_bind_innermost_first`
    /// - witness: `store::tests::both_binding_chains_preserve_outer_and_opposite_scopes`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret == usize::try_from(u32::from(index)).ok()
        .and_then(|offset| core::iter::successors(
            match environment.covalues {
                | CovalueScope::Empty => None,
                | CovalueScope::Innermost(id) => id.read_in(&self.covalue_bindings),
            },
            |binding| match binding.outer {
                | CovalueScope::Empty => None,
                | CovalueScope::Innermost(id) => id.read_in(&self.covalue_bindings),
            },
        ).nth(offset).map(|binding| binding.mark))
    )]
    pub fn lookup_covalue(
        &self,
        environment: Environment,
        index: CovariableIndex,
    ) -> Option<ContinuationMark>
    {
        let mut scope = environment.covalues;
        let mut remaining = u32::from(index);
        loop {
            let CovalueScope::Innermost(id) = scope
            else {
                return None;
            };
            let binding = id.read_in(&self.covalue_bindings)?;
            let Some(next) = remaining.checked_sub(1)
            else {
                return Some(binding.mark);
            };
            remaining = next;
            scope = binding.outer;
        }
    }

    /// The values an environment's producer chain binds, innermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the `i`-th item is what [`Self::lookup_value`] reads at index
    ///   `i`; the walk ends past the chain or at a dangling link.
    /// - provides: the closing substitution a readback builds from a captured
    ///   environment, in one pass rather than one lookup per index.
    /// - fails: never; a dangling link ends the walk.
    /// - panics: none.
    /// - executable: none — anodized cannot instrument a postcondition on this
    ///   opaque return type (E0562: `impl Trait` in a closure return type).
    ///   There is no nontrivial precondition; replacing the opaque return type
    ///   would change the public API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and two-element chains, distinct payloads,
    ///   exact-end indices and dangling links distinguish reversed order, an
    ///   off-by-one index and accidental coupling of the two namespaces.
    /// - witness: `store::tests::environments_bind_innermost_first`
    /// - witness: `store::tests::both_binding_chains_preserve_outer_and_opposite_scopes`
    #[inline]
    pub fn bound_values(
        &self,
        environment: Environment,
    ) -> impl Iterator<Item = HeapValueId>
    {
        let mut scope = environment.values;
        core::iter::from_fn(move || {
            let ValueScope::Innermost(id) = scope
            else {
                return None;
            };
            let binding = id.read_in(&self.value_bindings)?;
            scope = binding.outer;
            Some(binding.value)
        })
    }

    /// Push a frame under a fresh serial.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the region is one frame higher, `frame` on top, under a
    ///   serial above every serial already used.
    /// - provides: the one push of the frame region.
    /// - fails: [`StoreFault::SerialsExhausted`], the store unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mark taken over a popped and re-pushed height is
    ///   refused as stale, which only fresh serials make observable.
    /// - witness: `store::tests::frames_shrink_to_a_mark`
    /// - witness: `store::tests::frame_serial_exhaustion_preserves_the_region`
    #[inline]
    #[anodized::spec(
        captures: [height = self.frames.len(), serial = self.last_serial],
        ensures: |ret| match ret {
            | Ok(()) => height.checked_add(1) == Some(self.frames.len())
                && usize::from(serial).checked_add(1) == Some(usize::from(self.last_serial))
                && self.mark().serial == self.last_serial,
            | Err(error) => error == StoreFault::SerialsExhausted
                && self.frames.len() == height && self.last_serial == serial,
        },
    )]
    pub fn push_frame(
        &mut self,
        frame: Frame,
    ) -> Result<(), StoreFault>
    {
        let serial = usize::from(self.last_serial)
            .checked_add(1)
            .map(FrameSerial::from)
            .ok_or(StoreFault::SerialsExhausted)?;
        self.frames.push(FrameEntry { frame, serial });
        self.last_serial = serial;
        Ok(())
    }

    /// Pop the top frame, or `None` at the base.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the region is one frame lower and the popped frame is
    ///   returned; `None` on an empty region, which is unchanged.
    /// - provides: the one pop of the frame region.
    /// - fails: `None`, the one reason an empty region.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct stacked frames are popped in reverse order,
    ///   then the empty region answers absence. Marks observe height and serial
    ///   preservation, separating bottom-pop, repeated-pop and serial reuse.
    /// - witness: `store::tests::frame_serial_exhaustion_preserves_the_region`
    /// - witness: `store::tests::frames_shrink_to_a_mark`
    #[inline]
    #[anodized::spec(
        captures: [height = self.frames.len(), serial = self.last_serial],
        ensures: |ref ret| self.frames.len() == height.saturating_sub(1)
            && ret.is_some() == (height != 0) && self.last_serial == serial,
    )]
    pub fn pop_frame(&mut self) -> Option<Frame>
    {
        self.frames.pop().map(|entry| entry.frame)
    }

    /// The continuation the region currently is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the current height with the top frame's serial, or
    ///   [`ContinuationMark::BASE`] on an empty region.
    /// - provides: the mark a covariable binds.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — base, two distinct live heights and a popped/replaced
    ///   height observe both mark fields. Stale-mark rejection distinguishes
    ///   serial reuse from a mark based only on height.
    /// - witness: `store::tests::frames_shrink_to_a_mark`
    /// - witness: `store::tests::frame_serial_exhaustion_preserves_the_region`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret.height == FrameHeight::from(self.frames.len())
        && ret.serial == self.frames.last().map_or(FrameSerial::BASE, |entry| entry.serial)
    )]
    pub fn mark(&self) -> ContinuationMark
    {
        self.frames
            .last()
            .map_or(ContinuationMark::BASE, |entry| ContinuationMark {
                height: FrameHeight::from(self.frames.len()),
                serial: entry.serial,
            })
    }

    /// The frame region's height.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn frame_height(&self) -> FrameHeight
    {
        FrameHeight::from(self.frames.len())
    }

    /// The frames, bottom first: the walkable continuation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn frames(&self) -> impl Iterator<Item = &Frame>
    {
        self.frames.iter().map(|entry| &entry.frame)
    }

    /// Shrink the frame region to a continuation mark.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the region's height is the mark's, the frames
    ///   below it are untouched, and every update frame dropped has declined
    ///   its cell to [`MemoState::Unforced`].
    /// - provides: returning through a covariable: the continuation it names
    ///   becomes the current one.
    /// - fails: [`StoreFault::StaleMark`] when the mark's height exceeds the
    ///   region or the frame at its height is not the one it named, the store
    ///   unchanged; a decline's own refusal, at the first dropped update frame
    ///   whose cell is not in progress.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a live mark below the top, a stale mark over a
    ///   re-pushed height, and a dropped update frame separate the shrink, its
    ///   refusal and its decline.
    /// - witness: `store::tests::frames_shrink_to_a_mark`
    /// - witness: `store::tests::shrinking_rejects_stale_marks_and_reports_dropped_update_faults`
    #[inline]
    #[anodized::spec(
        captures: [entry = self.mark()],
        ensures: |ret| match ret {
            | Ok(()) => self.mark() == mark,
            | Err(StoreFault::StaleMark(found)) => found == mark && self.mark() == entry,
            | Err(_) => self.frames.len() >= usize::from(mark.height)
                && self.frames.len() < usize::from(entry.height),
        },
    )]
    pub fn shrink_to(
        &mut self,
        mark: ContinuationMark,
    ) -> Result<(), StoreFault>
    {
        let height = usize::from(mark.height);
        let below = match height.checked_sub(1) {
            | None => FrameSerial::BASE,
            | Some(offset) => self
                .frames
                .get(offset)
                .map(|entry| entry.serial)
                .ok_or(StoreFault::StaleMark(mark))?,
        };
        if below != mark.serial {
            return Err(StoreFault::StaleMark(mark));
        }
        while self.frames.len() > height {
            let Some(entry) = self.frames.pop()
            else {
                break;
            };
            if let Frame::Update { cell } = entry.frame {
                self.decline(cell)?;
            }
        }
        Ok(())
    }

    /// The mutable state of a cell.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cell's state, for in-place transition.
    /// - provides: the one mutable read of the cell family.
    /// - fails: [`StoreFault::DanglingCell`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — transition tests visit every memo state and a missing
    ///   address. Exact cell state and error payload distinguish wrong-cell
    ///   mutation and a fabricated state for a dangling cell.
    /// - witness: `store::tests::cell_write_back_is_shared_and_nominal`
    /// - witness: `store::tests::cell_refusals_preserve_state_and_error_precedence`
    #[anodized::spec(
        captures: [entry = self.cell(cell)],
        ensures: |ref ret| match *ret {
            | Ok(ref state) => Some(**state) == entry,
            | Err(error) => entry.is_none() && error == StoreFault::DanglingCell(cell),
        },
    )]
    fn cell_mut(
        &mut self,
        cell: CellId,
    ) -> Result<&mut MemoState, StoreFault>
    {
        usize::try_from(u32::from(cell))
            .ok()
            .and_then(|offset| self.cells.get_mut(offset))
            .ok_or(StoreFault::DanglingCell(cell))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;

    use super::*;

    /// The decimal digits a test literal is spelled with.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Digits(&'static str);

    /// The non-negative integer value spelled by `digits`.
    ///
    /// # Specification
    /// - requires: digits is a nonempty unsigned decimal spelling.
    /// - ensures: that nonnegative integer as a literal heap value, with
    ///   leading zeroes removed except for zero itself.
    /// - provides: numeric fixture values independent of their heap address.
    /// - panics: on a malformed decimal spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid decimal fixtures used by heap identity and
    ///   shared-cache scenarios have their canonical payload checked under
    ///   enforcement. These distinguish the wrong literal kind, sign or value;
    ///   malformed spellings are outside the fixture domain.
    /// - witness: `store::tests::cell_write_back_is_shared_and_nominal`
    /// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
    #[anodized::spec(
        requires: !digits.0.is_empty() && digits.0.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ref ret| match *ret {
            | HeapValue::Literal(Literal::Integer(ref integer)) => {
                let significant = digits.0.trim_start_matches('0');
                let expected = if significant.is_empty() { "0" } else { significant };
                let actual: &str = integer.magnitude().as_ref();
                integer.sign() == Sign::NonNegative && actual == expected
            },
            | _ => false,
        },
    )]
    fn integer(digits: Digits) -> HeapValue
    {
        HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
        )))
    }

    /// A write-back through one address is what every holder of that address
    /// reads, and a second cell — even one a thunk of equal content would own
    /// — is untouched: identity is the address, not the content.
    #[test]
    fn cell_write_back_is_shared_and_nominal()
    {
        let mut store = Store::new();
        let shared = store.allocate_cell().expect("room");
        let other = store.allocate_cell().expect("room");
        assert_ne!(shared, other, "two allocations are two cells");
        let alias = shared;

        assert_eq!(
            Ok(ForceEntry::Opened),
            store.begin_force(shared),
            "an unforced cell opens"
        );
        assert_eq!(
            Ok(ForceEntry::Reentrant),
            store.begin_force(alias),
            "the alias sees the black hole"
        );
        let value = store.allocate(integer(Digits("9"))).expect("room");
        assert_eq!(
            Ok(()),
            store.write_back(shared, value),
            "the opener writes back"
        );

        assert_eq!(
            Ok(ForceEntry::Cached(value)),
            store.begin_force(alias),
            "the alias reads the exact value written"
        );
        assert_eq!(
            Some(MemoState::Unforced),
            store.cell(other),
            "the other cell is untouched"
        );
        assert_eq!(
            Err(StoreFault::CellNotInProgress {
                cell: shared,
                found: MemoState::Forced(value),
            }),
            store.write_back(shared, value),
            "a forced cell takes no second write-back"
        );
        assert_eq!(
            Err(StoreFault::CellNotInProgress {
                cell: other,
                found: MemoState::Unforced,
            }),
            store.decline(other),
            "an unforced cell cannot be declined"
        );
    }

    /// A covariable's mark shrinks the region to its height and declines the
    /// update frames it drops; a mark over a popped and re-pushed height is
    /// stale.
    #[test]
    fn frames_shrink_to_a_mark()
    {
        let mut store = Store::new();
        let cell = store.allocate_cell().expect("room");
        store
            .push_frame(Frame::Destructor {
                tag: DestructorTag::Force,
                arguments: Box::from([]),
            })
            .expect("room");
        let mark = store.mark();
        assert_eq!(
            Ok(ForceEntry::Opened),
            store.begin_force(cell),
            "the cell opens"
        );
        store.push_frame(Frame::Update { cell }).expect("room");
        store
            .push_frame(Frame::Destructor {
                tag: DestructorTag::Force,
                arguments: Box::from([]),
            })
            .expect("room");
        assert_eq!(
            FrameHeight::from(3_usize),
            store.frame_height(),
            "three frames"
        );

        assert_eq!(Ok(()), store.shrink_to(mark), "a live mark shrinks");
        assert_eq!(
            FrameHeight::from(1_usize),
            store.frame_height(),
            "back at the mark"
        );
        assert_eq!(
            Some(MemoState::Unforced),
            store.cell(cell),
            "the dropped update declined its cell"
        );

        let popped = store.pop_frame();
        assert!(popped.is_some(), "the marked frame pops");
        store
            .push_frame(Frame::Destructor {
                tag: DestructorTag::Force,
                arguments: Box::from([]),
            })
            .expect("room");
        assert_eq!(
            Err(StoreFault::StaleMark(mark)),
            store.shrink_to(mark),
            "the height is re-pushed under another serial"
        );
        assert_eq!(
            Ok(()),
            store.shrink_to(ContinuationMark::BASE),
            "the base is always live"
        );
        assert_eq!(
            FrameHeight::ZERO,
            store.frame_height(),
            "the region is empty"
        );
    }

    /// Bindings are read innermost first, in each chain independently.
    #[test]
    fn environments_bind_innermost_first()
    {
        let mut store = Store::new();
        let first = store.allocate(integer(Digits("1"))).expect("room");
        let second = store.allocate(integer(Digits("2"))).expect("room");
        let outer = store.bind_value(Environment::EMPTY, first).expect("room");
        let inner = store.bind_value(outer, second).expect("room");
        let index = |raw: u32| DeBruijnIndex::from(raw);
        assert_eq!(
            Some(second),
            store.lookup_value(inner, index(0)),
            "index 0 is the innermost"
        );
        assert_eq!(
            Some(first),
            store.lookup_value(inner, index(1)),
            "index 1 is the next out"
        );
        assert_eq!(
            None,
            store.lookup_value(inner, index(2)),
            "past the chain is unbound"
        );
        assert_eq!(
            None,
            store.lookup_covalue(inner, CovariableIndex::from(0_u32)),
            "no covariable is bound"
        );

        let marked = store
            .bind_covalue(inner, ContinuationMark::BASE)
            .expect("room");
        assert_eq!(
            Some(ContinuationMark::BASE),
            store.lookup_covalue(marked, CovariableIndex::from(0_u32)),
            "the covalue chain reads its binding"
        );
        assert_eq!(
            Some(second),
            store.lookup_value(marked, index(0)),
            "the producer chain is unchanged"
        );
        assert_eq!(
            alloc::vec![second, first],
            store.bound_values(marked).collect::<alloc::vec::Vec<_>>(),
            "the walk reads the chain innermost first, as the lookups do"
        );
    }

    /// Heap and memo families retain exact identities at their allocation
    /// boundaries.
    #[test]
    fn heap_reads_preserve_identity_at_the_end()
    {
        let mut store = Store::new();
        assert_eq!(None, store.value(HeapValueId::from(0_u32)));
        assert_eq!(None, store.cell(CellId::from(0_u32)));
        let first = store.allocate(integer(Digits("11"))).expect("room");
        let last = store.allocate(integer(Digits("29"))).expect("room");
        assert_eq!(HeapValueId::from(0_u32), first);
        assert_eq!(HeapValueId::from(1_u32), last);
        assert_eq!(Some(&integer(Digits("11"))), store.value(first));
        assert_eq!(Some(&integer(Digits("29"))), store.value(last));
        assert_eq!(None, store.value(HeapValueId::from(2_u32)));
        let cell = store.allocate_cell().expect("room");
        assert_eq!(CellId::from(0_u32), cell);
        assert_eq!(Some(MemoState::Unforced), store.cell(cell));
        assert_eq!(None, store.cell(CellId::from(1_u32)));
    }

    /// Every memo refusal preserves its target, including competing missing
    /// addresses.
    #[test]
    fn cell_refusals_preserve_state_and_error_precedence()
    {
        let mut store = Store::new();
        let value = store.allocate(integer(Digits("7"))).expect("room");
        let cell = store.allocate_cell().expect("room");
        let missing_cell = CellId::from(1_u32);
        let missing_value = HeapValueId::from(1_u32);
        assert_eq!(
            Err(StoreFault::DanglingCell(missing_cell)),
            store.begin_force(missing_cell)
        );
        assert_eq!(
            Err(StoreFault::DanglingCell(missing_cell)),
            store.decline(missing_cell)
        );
        assert_eq!(
            Err(StoreFault::DanglingValue(missing_value)),
            store.write_back(missing_cell, missing_value)
        );
        assert_eq!(
            Err(StoreFault::DanglingCell(missing_cell)),
            store.write_back(missing_cell, value)
        );
        for state in [
            MemoState::Unforced,
            MemoState::InProgress,
            MemoState::Forced(value),
        ] {
            match state {
                | MemoState::Unforced => {},
                | MemoState::InProgress => {
                    store.begin_force(cell).expect("live cell");
                },
                | MemoState::Forced(cached) => {
                    store.begin_force(cell).expect("live cell");
                    store.write_back(cell, cached).expect("in progress");
                },
            }
            assert_eq!(
                Err(StoreFault::DanglingValue(missing_value)),
                store.write_back(cell, missing_value)
            );
            assert_eq!(Some(state), store.cell(cell));
            if state == MemoState::InProgress {
                assert_eq!(Ok(()), store.decline(cell));
                assert_eq!(Some(MemoState::Unforced), store.cell(cell));
            }
            else {
                let refusal = StoreFault::CellNotInProgress { cell, found: state };
                assert_eq!(Err(refusal), store.write_back(cell, value));
                assert_eq!(Err(refusal), store.decline(cell));
                assert_eq!(Some(state), store.cell(cell));
            }
        }
    }

    /// Producer and covalue chains shift independently and stop at missing
    /// links.
    #[test]
    fn both_binding_chains_preserve_outer_and_opposite_scopes()
    {
        let mut store = Store::new();
        let first = store.allocate(integer(Digits("1"))).expect("room");
        let second = store.allocate(integer(Digits("2"))).expect("room");
        let empty = Environment::EMPTY;
        assert_eq!(None, store.lookup_value(empty, DeBruijnIndex::from(0_u32)));
        assert_eq!(
            None,
            store.lookup_covalue(empty, CovariableIndex::from(0_u32))
        );
        assert_eq!(None, store.bound_values(empty).next());
        let initial = store.bind_value(empty, first).expect("room");
        let initial = store
            .bind_covalue(initial, ContinuationMark::BASE)
            .expect("room");
        store
            .push_frame(Frame::Destructor {
                tag: DestructorTag::Force,
                arguments: Box::from([]),
            })
            .expect("room");
        let mark = store.mark();
        let extended = store.bind_covalue(initial, mark).expect("room");
        let extended = store.bind_value(extended, second).expect("room");
        for (index, value, covalue) in [
            (0_u32, Some(second), Some(mark)),
            (1, Some(first), Some(ContinuationMark::BASE)),
            (2, None, None),
        ] {
            assert_eq!(
                value,
                store.lookup_value(extended, DeBruijnIndex::from(index))
            );
            assert_eq!(
                covalue,
                store.lookup_covalue(extended, CovariableIndex::from(index))
            );
        }
        assert_eq!(
            Some(first),
            store.lookup_value(initial, DeBruijnIndex::from(0_u32))
        );
        assert_eq!(
            Some(ContinuationMark::BASE),
            store.lookup_covalue(initial, CovariableIndex::from(0_u32))
        );
        assert_eq!(
            alloc::vec![second, first],
            store.bound_values(extended).collect::<Vec<_>>()
        );
        let dangling = Environment {
            values: ValueScope::Innermost(ValueBindingId::from(u32::MAX)),
            covalues: CovalueScope::Innermost(CovalueBindingId::from(u32::MAX)),
        };
        assert_eq!(
            None,
            store.lookup_value(dangling, DeBruijnIndex::from(0_u32))
        );
        assert_eq!(
            None,
            store.lookup_covalue(dangling, CovariableIndex::from(0_u32))
        );
        assert_eq!(None, store.bound_values(dangling).next());
    }

    /// Exhausting serials refuses a push without popping or reusing a frame.
    #[test]
    fn frame_serial_exhaustion_preserves_the_region()
    {
        let mut store = Store::new();
        let force = Frame::Destructor {
            tag: DestructorTag::Force,
            arguments: Box::from([]),
        };
        let apply = Frame::Destructor {
            tag: DestructorTag::Apply,
            arguments: Box::from([]),
        };
        store.push_frame(force.clone()).expect("room");
        let first = store.mark();
        store.last_serial = FrameSerial::from(usize::MAX.saturating_sub(1));
        store
            .push_frame(apply.clone())
            .expect("last representable serial");
        let last = store.mark();
        assert_eq!(FrameSerial::from(usize::MAX), last.serial);
        assert_eq!(FrameHeight::from(2_usize), last.height);
        assert_eq!(
            Err(StoreFault::SerialsExhausted),
            store.push_frame(force.clone())
        );
        assert_eq!(last, store.mark());
        assert_eq!(Some(apply), store.pop_frame());
        assert_eq!(first, store.mark());
        assert_eq!(Some(force.clone()), store.pop_frame());
        assert_eq!(None, store.pop_frame());
        assert_eq!(ContinuationMark::BASE, store.mark());
        assert_eq!(Err(StoreFault::SerialsExhausted), store.push_frame(force));
        assert_eq!(ContinuationMark::BASE, store.mark());
    }

    /// Stale marks preserve the region; a faulty dropped update is reported
    /// after its pop.
    #[test]
    fn shrinking_rejects_stale_marks_and_reports_dropped_update_faults()
    {
        let mut store = Store::new();
        let force = Frame::Destructor {
            tag: DestructorTag::Force,
            arguments: Box::from([]),
        };
        store.push_frame(force.clone()).expect("room");
        let old = store.mark();
        assert_eq!(Some(force.clone()), store.pop_frame());
        assert_eq!(Err(StoreFault::StaleMark(old)), store.shrink_to(old));
        assert_eq!(ContinuationMark::BASE, store.mark());
        store.push_frame(force).expect("room");
        let live = store.mark();
        assert_eq!(Err(StoreFault::StaleMark(old)), store.shrink_to(old));
        assert_eq!(live, store.mark());
        let cell = store.allocate_cell().expect("room");
        store.push_frame(Frame::Update { cell }).expect("room");
        assert_eq!(
            Err(StoreFault::CellNotInProgress {
                cell,
                found: MemoState::Unforced
            }),
            store.shrink_to(live)
        );
        assert_eq!(live, store.mark());
        assert_eq!(Some(MemoState::Unforced), store.cell(cell));
        let missing = CellId::from(1_u32);
        store
            .push_frame(Frame::Update { cell: missing })
            .expect("room");
        assert_eq!(
            Err(StoreFault::DanglingCell(missing)),
            store.shrink_to(live)
        );
        assert_eq!(live, store.mark());
        assert_eq!(Ok(()), store.shrink_to(ContinuationMark::BASE));
        assert_eq!(ContinuationMark::BASE, store.mark());
    }
}
