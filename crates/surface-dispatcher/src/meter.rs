//! The allocation meter: the running count of the allocations each thread
//! made, which a counting global allocator advances and the timings layer
//! reads.
//!
//! # A thread counts its own allocations
//!
//! **Choice.** Each thread keeps its running count in a thread-local cell. A
//! counting global allocator, which the process installs, calls [`allocated`]
//! once for each allocation. [`Allocations`] reads the cell of its own thread.
//! So an allocation costs one thread-local add, and a reading one thread-local
//! load, with no atomic and no shared cache line. A process that installs no
//! counting allocator never advances a cell, and [`counting`] tells the two
//! apart once, by one allocation of its own.
//!
//! **Alternatives.** One process-wide atomic counter costs each allocation a
//! shared cache line. Its span over a phase also holds the work of each other
//! job that runs at the same time, and the hub runs an admission beside the
//! next judgement. A meter that the caller passes to each allocation needs the
//! allocator to find the caller, and the global allocator has no such
//! argument.
//!
//! **Reversal.** A phase whose fork jobs allocate on the pool's threads counts
//! only the allocations of its own thread. When the pool adds each job's
//! allocations to the thread that forked it, a reading holds them too.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-layers names the wall and the allocations of each phase as
//!   the timings layer's sample.

use core::cell::Cell;
use core::sync::atomic::AtomicU8;
use core::sync::atomic::Ordering;

use gandr_core_checker::bridge::AllocationCount;
use gandr_core_checker::bridge::Meter;
use gandr_core_checker::bridge::metered;
use quenchant_shape::shape::Maybe;

std::thread_local! {
    /// The allocations the thread made so far.
    static ALLOCATED: Cell<u64> = const { Cell::new(0) };
}

/// Whether [`counting`] has not probed yet.
const UNPROBED: u8 = 0;

/// Whether the probe saw the thread's count advance.
const COUNTED: u8 = 1;

/// Whether the probe saw the thread's count stay.
const UNCOUNTED: u8 = 2;

/// What [`counting`] found, once it probed.
static PROBED: AtomicU8 = AtomicU8::new(UNPROBED);

/// Count one allocation of the calling thread.
///
/// A counting global allocator calls it once for each allocation it serves.
/// It allocates nothing, takes no lock and never panics, so the allocator can
/// call it before it serves the block.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the calling thread's count is one more, or unchanged once the
///   thread's locals are gone.
/// - panics: none.
/// - executable: none — the effect is on a thread-local cell, which only a
///   later reading observes.
///
/// # Adequacy
/// - hypothesis: L3 — two calls on one thread advance its count by two, and a
///   call on another thread leaves it.
/// - witness: `meter::tests::each_call_counts_one_allocation_of_its_own_thread`
#[inline]
pub fn allocated()
{
    let _gone = ALLOCATED.try_with(|count| count.set(count.get().wrapping_add(1)));
}

/// The meter that reads the calling thread's running count.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Allocations;

impl Meter for Allocations
{
    /// The calling thread's running count, zero once its locals are gone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn allocations(&mut self) -> AllocationCount
    {
        AllocationCount::from(ALLOCATED.try_with(Cell::get).unwrap_or(0))
    }
}

/// The meter of the process's allocations, when a counting global allocator
/// calls [`allocated`], or why none counts them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Allocations`] exactly when one allocation of the first call's
///   thread advanced its count, else [`metered::Absent::Unmetered`]; each later
///   call answers the first call's answer.
/// - panics: none.
/// - executable: none — the probe is an allocation, an effect that only the
///   allocator observes.
///
/// # Adequacy
/// - hypothesis: L3 — this crate's tests run under the system allocator, which
///   calls no [`allocated`], and read no meter at the first call and again at a
///   later one.
/// - witness: `meter::tests::a_process_with_no_counting_allocator_has_no_meter`
#[inline]
pub fn counting() -> Maybe<Allocations, metered::Absent>
{
    let counted = match PROBED.load(Ordering::Relaxed) {
        COUNTED => true,
        UNCOUNTED => false,
        _ => {
            let before = Allocations.allocations();
            drop(core::hint::black_box(Box::new(core::hint::black_box(0_u8))));
            let counted = Allocations.allocations() > before;
            PROBED.store(if counted { COUNTED } else { UNCOUNTED }, Ordering::Relaxed);
            counted
        },
    };
    if counted {
        Maybe::Present(Allocations)
    }
    else {
        Maybe::Absent(metered::Absent::Unmetered)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_checker::bridge::Meter as _;
    use gandr_core_checker::bridge::metered;
    use quenchant_shape::shape::Maybe;

    use super::Allocations;
    use super::allocated;
    use super::counting;

    /// Two calls of `allocated` on one thread advance that thread's count by
    /// two, and a call on another thread advances that thread's count alone.
    /// A count kept in one cell for each process, or an add of another step,
    /// breaks a comparison.
    #[test]
    fn each_call_counts_one_allocation_of_its_own_thread()
    {
        let before = Allocations.allocations();
        allocated();
        allocated();
        let after = Allocations.allocations();
        assert_eq!(
            u64::from(after.since(before)),
            2,
            "two calls count two allocations of the thread"
        );
        let other = std::thread::spawn(|| {
            let start = Allocations.allocations();
            allocated();
            u64::from(Allocations.allocations().since(start))
        })
        .join()
        .expect("the other thread runs");
        assert_eq!(other, 1, "the other thread counts its own call");
        assert_eq!(
            Allocations.allocations(),
            after,
            "another thread's call leaves this thread's count"
        );
    }

    /// This test process installs no counting allocator, so the probe's own
    /// allocation leaves its thread's count, and `counting` answers no meter at
    /// the first call and at a later one. A probe that read another thread's
    /// count, or a later call that probed again and answered otherwise, breaks
    /// the comparison.
    #[test]
    fn a_process_with_no_counting_allocator_has_no_meter()
    {
        assert_eq!(
            counting(),
            Maybe::Absent(metered::Absent::Unmetered),
            "the system allocator counts no allocation"
        );
        assert_eq!(
            counting(),
            Maybe::Absent(metered::Absent::Unmetered),
            "a later call answers as the first"
        );
    }
}
