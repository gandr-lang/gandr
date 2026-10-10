//! The memo-cell heap read as a partial commutative monoid, and the four
//! right-lifting conditions its force protocol must meet.
//!
//! A heap is a finite map from nominal cell addresses to memo states;
//! composition is disjoint union and the unit is the empty heap. A store
//! operation right-lifts along a framing `h = h₁ * h₂` when, its footprint in
//! `h₁`, running it on the composite yields `h₁' * h₂` with the frame `h₂`
//! preserved pointwise. The four conditions, each a property over generated
//! operation traces run against a real [`Store`]:
//!
//! - **RL1, frame preservation.** A step on one cell leaves every other cell
//!   exactly as it was.
//! - **RL2, nominal identity.** Allocation is fresh, dense and append-only;
//!   every handle of a cell — a copy of its address — reads what the address
//!   reads, and distinct allocations never alias.
//! - **RL3, black-hole discipline.** The only transitions are `Unforced →
//!   InProgress` by an opening force, `InProgress → Forced` by a write-back and
//!   `InProgress → Unforced` by a decline; a re-entrant force writes nothing;
//!   `Forced` is absorbing; a refused step writes nothing.
//! - **RL4, write-back purity.** A write-back caches exactly the value it was
//!   given, every later force of the cell returns exactly that value, and a
//!   decline leaves no cache behind.
//!
//! The store enforces the transition table itself, so the generated traces
//! are arbitrary rather than machine-legal: an illegal step is refused, and
//! the properties assert that the refusal changed nothing.
//!
//! The values and environment chains of the heap region are immutable once
//! allocated, so the four conditions are live exactly on the cells.

use alloc::vec::Vec;

use gandr_core_sequent::CellId;
use gandr_core_sequent::ForceEntry;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::MemoState;
use gandr_core_sequent::Store;
use gandr_core_sequent::StoreFault;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use proptest::prelude::*;

/// A generator-side slot: which tracked cell an operation targets, wrapped
/// into the allocated range when the trace runs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct CellSlot(usize);

/// Which value a write-back hands the store.
#[derive(Clone, Copy, Debug)]
enum ValuePick
{
    /// A value allocated for this step.
    Fresh,
    /// The most recently allocated value, if any.
    Reused,
    /// An address the store never allocated.
    Dangling,
}

/// One generated store operation.
#[derive(Clone, Copy, Debug)]
enum Op
{
    /// Allocate a fresh cell.
    Allocate,
    /// Copy a cell's handle.
    Share(CellSlot),
    /// Open a force on a cell.
    Force(CellSlot),
    /// Write a value back to a cell.
    WriteBack(CellSlot, ValuePick),
    /// Decline a cell's forcing.
    Decline(CellSlot),
    /// Read a cell's state.
    Observe(CellSlot),
}

/// What one step answered.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Outcome
{
    /// A cell was allocated at this address.
    Allocated(CellId),
    /// A handle was copied.
    Shared,
    /// A force found this.
    Forced(ForceEntry),
    /// A write-back of this value succeeded.
    WroteBack(HeapValueId),
    /// A decline succeeded.
    Declined,
    /// The store refused the step.
    Refused(StoreFault),
    /// An observation read this state.
    Observed(MemoState),
    /// No cell existed to target.
    Skipped,
}

/// A tracked cell: its address and every handle copied from it.
#[derive(Clone, Debug)]
struct Tracked
{
    /// The address allocation returned.
    id: CellId,
    /// Copies of the address handed out by sharing.
    handles: Vec<CellId>,
}

/// The heap image at one instant: every tracked cell's state at its address,
/// and through each of its handles.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CellView
{
    /// The state read at the address.
    at_address: Option<MemoState>,
    /// The states read through the handles.
    through_handles: Vec<Option<MemoState>>,
}

/// One step of a trace, with the heap image around it.
#[derive(Clone, Debug)]
struct Step
{
    /// The operation.
    op: Op,
    /// The tracked cell it targeted, if any.
    subject: Option<usize>,
    /// The heap image before.
    before: Vec<CellView>,
    /// The heap image after.
    after: Vec<CellView>,
    /// What the step answered.
    outcome: Outcome,
}

/// A whole run.
#[derive(Debug)]
struct Trace
{
    /// The steps, in order.
    steps: Vec<Step>,
    /// The cells, in allocation order.
    cells: Vec<Tracked>,
    /// The store after the last step.
    store: Store,
}

/// The step a write-back allocates its value at, which spells the value.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Seed(usize);

/// A literal value to write back, distinct per seed.
///
/// # Specification
/// trivial.
fn literal(seed: Seed) -> HeapValue
{
    HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(alloc::format!("{}", seed.0)).expect("decimal digits"),
    )))
}

/// The heap image over the tracked cells.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one view per tracked cell, with its address and every handle
///   observed independently through the store in their recorded order.
/// - provides: a state image without assuming alias coherence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — bounded operation traces compare untouched cells and
///   alias observations, including fresh, active and memoized states. The
///   pointwise predicate challenges a fabricated or reordered image; the trace
///   laws challenge lost cells and diverging aliases. Neither observation
///   asserts an unbounded concurrency result.
/// - witness: `tests::csl_fibration::frame_preservation_under_forcing`
/// - witness: `tests::csl_fibration::nominal_identity_freshness_and_alias_coherence`
/// - witness: `tests::csl_fibration::black_hole_discipline_under_reentry`
#[anodized::spec(ensures: |ref ret| ret.len() == cells.len()
    && ret.iter().zip(cells).all(|(view, cell)| view.at_address == store.cell(cell.id)
        && view.through_handles.len() == cell.handles.len()
        && view.through_handles.iter().zip(&cell.handles).all(|(&state, &handle)| state == store.cell(handle)))
)]
fn image(
    store: &Store,
    cells: &[Tracked],
) -> Vec<CellView>
{
    cells
        .iter()
        .map(|tracked| CellView {
            at_address: store.cell(tracked.id),
            through_handles: tracked
                .handles
                .iter()
                .map(|&handle| store.cell(handle))
                .collect(),
        })
        .collect()
}

/// Replay a generated operation sequence against a fresh store.
///
/// # Specification
/// - ensures: one step per operation, each with the heap image before and after
///   it; the store is driven only through its public operations.
/// - panics: when the store refuses an allocation, which a trace of at most 64
///   steps cannot reach.
///
/// # Adequacy
/// - hypothesis: L3 — traces of fewer than 64 operations over the generated
///   slot and value choices observe frame preservation, nominal identity, alias
///   coherence and legal memo transitions. Consecutive images and operation
///   alignment challenge a dropped or reordered step; direct final-store
///   observations constrain the model. No concurrency or beyond-ceiling
///   allocation behavior is covered.
/// - witness: `tests::csl_fibration::frame_preservation_under_forcing`
/// - witness: `tests::csl_fibration::nominal_identity_freshness_and_alias_coherence`
/// - witness: `tests::csl_fibration::black_hole_discipline_under_reentry`
#[anodized::spec(ensures: |ref ret| ret.steps.len() == ops.len()
    && ret.steps.iter().zip(ops).all(|(step, &op)| match (step.op, op) {
        | (Op::Allocate, Op::Allocate) => true,
        | (Op::Share(CellSlot(first)), Op::Share(CellSlot(second)))
        | (Op::Force(CellSlot(first)), Op::Force(CellSlot(second)))
        | (Op::Decline(CellSlot(first)), Op::Decline(CellSlot(second)))
        | (Op::Observe(CellSlot(first)), Op::Observe(CellSlot(second))) => first == second,
        | (Op::WriteBack(CellSlot(first), value), Op::WriteBack(CellSlot(second), other)) =>
            first == second && core::mem::discriminant(&value) == core::mem::discriminant(&other),
        | _ => false,
    })
    && ret.steps.first().is_none_or(|first| first.before.is_empty())
    && ret.steps.windows(2).all(|pair| pair.first().zip(pair.get(1)).is_some_and(|(first, second)| first.after == second.before))
    && ret.cells.len() == usize::from(ret.store.cell_count())
    && ret.cells.iter().all(|cell| cell.handles.first() == Some(&cell.id) && cell.handles.iter().all(|&handle| handle == cell.id))
    && ret.steps.last().is_none_or(|last| last.after.len() == ret.cells.len()
        && last.after.iter().zip(&ret.cells).all(|(view, cell)| view.at_address == ret.store.cell(cell.id)))
)]
fn run(ops: &[Op]) -> Trace
{
    let mut store = Store::new();
    let mut cells: Vec<Tracked> = Vec::new();
    let mut last_value: Option<HeapValueId> = None;
    let mut steps = Vec::new();
    for (seed, &op) in ops.iter().enumerate() {
        let before = image(&store, &cells);
        let target = |slot: CellSlot| slot.0.checked_rem(cells.len());
        let (subject, outcome) = match op {
            | Op::Allocate => {
                let id = store
                    .allocate_cell()
                    .expect("the trace stays far below the ceiling");
                cells.push(Tracked {
                    id,
                    handles: alloc::vec![id],
                });
                (None, Outcome::Allocated(id))
            },
            | Op::Share(slot) => match target(slot) {
                | Some(index) => {
                    let id = cells[index].id;
                    cells[index].handles.push(id);
                    (Some(index), Outcome::Shared)
                },
                | None => (None, Outcome::Skipped),
            },
            | Op::Force(slot) => match target(slot) {
                | Some(index) => {
                    let handle = *cells[index]
                        .handles
                        .last()
                        .expect("a cell keeps its handle");
                    let outcome = match store.begin_force(handle) {
                        | Ok(entry) => Outcome::Forced(entry),
                        | Err(fault) => Outcome::Refused(fault),
                    };
                    (Some(index), outcome)
                },
                | None => (None, Outcome::Skipped),
            },
            | Op::WriteBack(slot, pick) => match target(slot) {
                | Some(index) => {
                    let value = match pick {
                        | ValuePick::Fresh => {
                            let fresh = store.allocate(literal(Seed(seed))).expect("room");
                            last_value = Some(fresh);
                            fresh
                        },
                        | ValuePick::Reused => match last_value {
                            | Some(value) => value,
                            | None => {
                                let fresh = store.allocate(literal(Seed(seed))).expect("room");
                                last_value = Some(fresh);
                                fresh
                            },
                        },
                        | ValuePick::Dangling => HeapValueId::from(u32::MAX),
                    };
                    let outcome = match store.write_back(cells[index].id, value) {
                        | Ok(()) => Outcome::WroteBack(value),
                        | Err(fault) => Outcome::Refused(fault),
                    };
                    (Some(index), outcome)
                },
                | None => (None, Outcome::Skipped),
            },
            | Op::Decline(slot) => match target(slot) {
                | Some(index) => {
                    let outcome = match store.decline(cells[index].id) {
                        | Ok(()) => Outcome::Declined,
                        | Err(fault) => Outcome::Refused(fault),
                    };
                    (Some(index), outcome)
                },
                | None => (None, Outcome::Skipped),
            },
            | Op::Observe(slot) => match target(slot) {
                | Some(index) => {
                    let state = store
                        .cell(cells[index].id)
                        .expect("a tracked cell resolves");
                    (Some(index), Outcome::Observed(state))
                },
                | None => (None, Outcome::Skipped),
            },
        };
        let after = image(&store, &cells);
        steps.push(Step {
            op,
            subject,
            before,
            after,
            outcome,
        });
    }
    Trace {
        steps,
        cells,
        store,
    }
}

/// A generated operation, weighted so cells exist and get forced.
///
/// # Specification
/// trivial.
fn arb_op() -> impl Strategy<Value = Op>
{
    let slot = (0_usize .. 8_usize).prop_map(CellSlot);
    let pick = prop_oneof![
        3 => Just(ValuePick::Fresh),
        1 => Just(ValuePick::Reused),
        1 => Just(ValuePick::Dangling),
    ];
    prop_oneof![
        2 => Just(Op::Allocate),
        1 => slot.clone().prop_map(Op::Share),
        4 => slot.clone().prop_map(Op::Force),
        3 => (slot.clone(), pick).prop_map(|(slot, pick)| Op::WriteBack(slot, pick)),
        2 => slot.clone().prop_map(Op::Decline),
        1 => slot.prop_map(Op::Observe),
    ]
}

/// A generated trace.
///
/// # Specification
/// trivial.
fn arb_ops() -> impl Strategy<Value = Vec<Op>>
{
    proptest::collection::vec(arb_op(), 0_usize .. 64_usize)
}

/// The state a step's subject read before and after it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the addressed before and after states in that order, or none if
///   the subject, either view or either state is absent.
/// - provides: the transition pair without treating missing data as a state.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — skipped and allocating operations have no subject pair;
///   targeted operations expose the legal memo transitions. The pointwise
///   predicate and protocol law distinguish a missing or exchanged endpoint
///   within generated traces; arbitrary damaged trace records are outside the
///   fixture domain.
/// - witness: `tests::csl_fibration::black_hole_discipline_under_reentry`
/// - witness: `tests::csl_fibration::frame_preservation_under_forcing`
#[anodized::spec(ensures: |ret| ret == step.subject.and_then(|index|
    step.before.get(index).and_then(|view| view.at_address)
        .zip(step.after.get(index).and_then(|view| view.at_address))
))]
fn subject_states(step: &Step) -> Option<(MemoState, MemoState)>
{
    let index = step.subject?;
    let before = step.before.get(index)?.at_address?;
    let after = step.after.get(index)?.at_address?;
    Some((before, after))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// **RL1 — frame preservation.** Every cell a step does not target is
    /// identical before and after it, at its address and through every
    /// handle.
    #[test]
    fn frame_preservation_under_forcing(ops in arb_ops())
    {
        let trace = run(&ops);
        for step in &trace.steps {
            for (index, before) in step.before.iter().enumerate() {
                if step.subject == Some(index) {
                    continue;
                }
                prop_assert_eq!(
                    Some(before),
                    step.after.get(index),
                    "cell {} changed under {:?} on another cell",
                    index,
                    step.op
                );
            }
        }
    }

    /// **RL2 — nominal identity.** Allocation is fresh, dense and
    /// append-only; every handle reads what the address reads.
    #[test]
    fn nominal_identity_freshness_and_alias_coherence(ops in arb_ops())
    {
        let trace = run(&ops);
        for (index, tracked) in trace.cells.iter().enumerate() {
            prop_assert_eq!(
                usize::try_from(u32::from(tracked.id)).ok(),
                Some(index),
                "cell addresses are dense in allocation order"
            );
        }
        prop_assert_eq!(
            usize::from(trace.store.cell_count()),
            trace.cells.len(),
            "every allocation is registered exactly once"
        );
        for step in &trace.steps {
            let grew = matches!(step.outcome, Outcome::Allocated(_));
            prop_assert_eq!(
                step.after.len(),
                if grew { step.before.len().saturating_add(1) } else { step.before.len() },
                "only an allocation changes the extent, and by one"
            );
            if let Outcome::Allocated(id) = step.outcome {
                prop_assert_eq!(
                    usize::try_from(u32::from(id)).ok(),
                    Some(step.before.len()),
                    "an allocation returned a reused or non-dense address"
                );
            }
            for (index, view) in step.after.iter().enumerate() {
                prop_assert!(view.at_address.is_some(), "cell {} reads at its address", index);
                for handle in &view.through_handles {
                    prop_assert_eq!(
                        &view.at_address,
                        handle,
                        "a handle of cell {} diverged from its address",
                        index
                    );
                }
            }
        }
    }

    /// **RL3 — black-hole discipline.** Only the three protocol transitions
    /// occur, each by its own step; a re-entrant force and a refusal write
    /// nothing; `Forced` is absorbing.
    #[test]
    fn black_hole_discipline_under_reentry(ops in arb_ops())
    {
        let trace = run(&ops);
        for step in &trace.steps {
            let Some((before, after)) = subject_states(step) else {
                continue;
            };
            match (before, after) {
                | (MemoState::Unforced, MemoState::InProgress) => prop_assert_eq!(
                    step.outcome,
                    Outcome::Forced(ForceEntry::Opened),
                    "a black hole opened without an opening force"
                ),
                | (MemoState::InProgress, MemoState::Forced(value)) => prop_assert_eq!(
                    step.outcome,
                    Outcome::WroteBack(value),
                    "a cell was forced outside a write-back"
                ),
                | (MemoState::InProgress, MemoState::Unforced) => prop_assert_eq!(
                    step.outcome,
                    Outcome::Declined,
                    "a black hole cleared outside a decline"
                ),
                | (unchanged, same) => prop_assert_eq!(
                    unchanged,
                    same,
                    "an illegal transition under {:?}",
                    step.op
                ),
            }
            if matches!(before, MemoState::Forced(_)) {
                prop_assert_eq!(before, after, "a forced cell left its state under {:?}", step.op);
            }
            if step.outcome == Outcome::Forced(ForceEntry::Reentrant) {
                prop_assert_eq!(MemoState::InProgress, before, "re-entry fired off the black hole");
                prop_assert_eq!(before, after, "a re-entrant force wrote the cell");
            }
            if let Outcome::Refused(_) = step.outcome {
                prop_assert_eq!(before, after, "a refused step wrote the cell");
            }
            if let Outcome::Observed(state) = step.outcome {
                prop_assert_eq!(before, state, "an observation misreported the cell");
            }
        }
    }

    /// **RL4 — write-back purity.** A write-back caches exactly its value, a
    /// later force returns exactly the cache, the cache never changes once
    /// set, and a decline leaves no cache.
    #[test]
    fn write_back_purity_caches_the_exact_probe_allocation(ops in arb_ops())
    {
        let trace = run(&ops);
        for step in &trace.steps {
            let Some((before, after)) = subject_states(step) else {
                continue;
            };
            match step.outcome {
                | Outcome::WroteBack(value) => prop_assert_eq!(
                    MemoState::Forced(value),
                    after,
                    "the write-back cached something other than its value"
                ),
                | Outcome::Forced(ForceEntry::Cached(value)) => prop_assert_eq!(
                    MemoState::Forced(value),
                    before,
                    "a cache hit returned something other than the cache"
                ),
                | Outcome::Declined => prop_assert_eq!(
                    MemoState::Unforced,
                    after,
                    "a decline left a cache behind"
                ),
                | _ => {},
            }
        }
        for index in 0 .. trace.cells.len() {
            let mut cached: Option<HeapValueId> = None;
            for step in &trace.steps {
                let Some(MemoState::Forced(value)) = step.after.get(index).and_then(|view| view.at_address) else {
                    continue;
                };
                match cached {
                    | Some(existing) => prop_assert_eq!(existing, value, "cell {}'s cache changed", index),
                    | None => cached = Some(value),
                }
            }
        }
    }
}
