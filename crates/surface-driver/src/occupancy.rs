//! The occupancy a `check --activity` prints: the walk forks its lowerings
//! through the pool's recording fork, and one hub thread folds the activity
//! ring while the walk runs. After the walk, each thread's busy time, the
//! marks its ring dropped and the events that reached the fold late print to
//! standard error, one line for each thread and one line for the run.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-layers — the activity layer: one ring for each core, one
//!   fold at the hub's tick, the occupancy of each core and the late count.

use core::ops::ControlFlow;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use core::time::Duration;
use std::io;

use gandr_core_fork::activity::Activity;
use gandr_core_fork::activity::Declared;
use gandr_core_fork::activity::Fold;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Row;
use gandr_core_fork::activity::Slots;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::RunReport;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::activity_clock;

/// The hub's tick: one frame at sixty frames a second.
const TICK: Duration = Duration::from_nanos(16_666_667);

/// The marks each ring holds between two ticks: 32 KiB of slots for each
/// thread. A ring that fills drops its oldest mark and counts it.
const SLOTS: core::num::NonZeroUsize = core::num::NonZeroUsize::MIN.saturating_add(1_023);

/// What the fold of a walk's activity left: each thread's row, the events it
/// numbered and the walk's wall time.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Occupied
{
    /// The row of each thread: the pool's threads in order, then the calling
    /// thread's.
    rows: Vec<Row>,
    /// The events the fold numbered over the whole walk.
    events: usize,
    /// The hub's clock from the walk's start to its end.
    wall: Nanos,
}

/// `walk` visited on `pool` as [`Walk::visit`] visits it, each lowering job
/// marked on `rings`, rings of `pool` that another thread folds: the hub's,
/// while the toolset watches its activity for a job.
///
/// # Specification
/// - requires: `rings` are `pool`'s, as `Pool::activity` makes them.
/// - ensures: the steps and the report [`Walk::visit`] gives.
/// - fails: as [`Walk::visit`].
/// - panics: as [`Walk::visit`].
/// - executable: none — the marks are a side channel.
///
/// # Adequacy
/// - hypothesis: L3 — a `check` through the toolset of a hub reaches its caller
///   with the activity of its walk, and its output is a `check`'s.
/// - witness: `tests::cli::the_toolset_checks_a_corpus_as_the_command_line_does`
pub fn recorded<Stop, Visitor>(
    walk: Walk,
    (pool, rings): (&Pool, &Activity),
    visitor: Visitor,
) -> ControlFlow<Stop, RunReport>
where
    Visitor: FnMut(Step<'_>) -> ControlFlow<Stop>,
{
    walk.visit_recording(
        &pool.recording(rings, (Task::Fork, World::from(0_u32)), |_| Declared::NONE),
        visitor,
    )
}

/// `walk` visited on `pool` as [`Walk::visit`] visits it, each lowering job
/// marked in the pool's activity ring, and the ring folded on one hub thread
/// at each [`TICK`] until the walk ends.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the steps and the report [`Walk::visit`] gives, and the rows the
///   fold left after one last tick at the walk's end.
/// - fails: as [`Walk::visit`].
/// - panics: as [`Walk::visit`], and as the hub thread when it panics.
/// - executable: none — the hub thread's fold is a side channel.
///
/// # Adequacy
/// - hypothesis: L3 — a `check --activity` prints one line for each thread of
///   the pool, one for the calling thread and one for the run, and its other
///   output is a `check`'s.
/// - witness: `tests::cli::check_prints_each_thread_s_occupancy_6298`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "pool: the hub's fold is the one consumer of the rings, and it drains them on its own thread while the pool's threads fill them"
    )
)]
pub fn visited<Stop, Visitor>(
    walk: Walk,
    pool: &Pool,
    visitor: Visitor,
) -> (ControlFlow<Stop, RunReport>, Occupied)
where
    Visitor: FnMut(Step<'_>) -> ControlFlow<Stop>,
{
    let activity = pool.activity(Slots::from(SLOTS));
    let recording = pool.recording(&activity, (Task::Fork, World::from(0_u32)), |_| {
        Declared::NONE
    });
    let done = AtomicBool::new(false);
    let started = activity_clock();
    std::thread::scope(|scope| {
        let hub = scope.spawn(|| {
            let mut fold = Fold::new(&activity);
            let mut events = 0_usize;
            loop {
                let ending = done.load(Ordering::Acquire);
                let card = fold.tick(&activity, activity_clock());
                events = events.saturating_add(card.events.len());
                if ending {
                    break (card.rows.to_vec(), events);
                }
                std::thread::sleep(TICK);
            }
        });
        let visited = walk.visit_recording(&recording, visitor);
        let ended = activity_clock();
        done.store(true, Ordering::Release);
        let (rows, events) = match hub.join() {
            Ok(folded) => folded,
            Err(panic) => std::panic::resume_unwind(panic),
        };
        let wall = Nanos::from(u64::from(ended).saturating_sub(u64::from(started)));
        (visited, Occupied { rows, events, wall })
    })
}

impl Occupied
{
    /// Print one line for each thread, then one line for the run, to
    /// `stderr`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each line starts `activity: `. A thread's line names the
    ///   thread, its busy time, its share of the wall time in tenths of a
    ///   percent, the marks its ring dropped and its late events. The run's
    ///   line names the events, the wall time and the sums.
    /// - fails: the first write `stderr` refuses.
    /// - panics: none.
    /// - executable: none — writes to a stream.
    ///
    /// # Errors
    /// As the specification's fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the printed lines are one for each thread and one for
    ///   the run, each in its form.
    /// - witness: `tests::cli::check_prints_each_thread_s_occupancy_6298`
    pub fn print(
        &self,
        stderr: &mut dyn io::Write,
    ) -> io::Result<()>
    {
        let wall = u64::from(self.wall);
        let last = self.rows.len().saturating_sub(1);
        // A time as whole milliseconds and the microseconds past them.
        let millis = |nanos: u64| {
            (
                nanos.checked_div(1_000_000).unwrap_or_default(),
                nanos
                    .checked_rem(1_000_000)
                    .and_then(|past| past.checked_div(1_000))
                    .unwrap_or_default(),
            )
        };
        let (mut busy, mut dropped, mut late) = (0_u64, 0_u64, 0_u64);
        for (index, row) in self.rows.iter().enumerate() {
            let total = u64::from(row.total());
            busy = busy.saturating_add(total);
            dropped = dropped.saturating_add(u64::from(row.dropped()));
            late = late.saturating_add(u64::from(row.late()));
            let permille = total
                .saturating_mul(1_000)
                .checked_div(wall)
                .unwrap_or_default();
            let thread = if index == last {
                String::from("caller")
            }
            else {
                format!("thread {index}")
            };
            let (whole, past) = millis(total);
            writeln!(
                stderr,
                "activity: {thread}: busy {whole}.{past:03} ms, {}.{} % of the wall, {} dropped, {} late",
                permille.checked_div(10).unwrap_or_default(),
                permille.checked_rem(10).unwrap_or_default(),
                u64::from(row.dropped()),
                u64::from(row.late()),
            )?;
        }
        let ((wall_whole, wall_past), (busy_whole, busy_past)) = (millis(wall), millis(busy));
        writeln!(
            stderr,
            "activity: {} events over {wall_whole}.{wall_past:03} ms, busy {busy_whole}.{busy_past:03} ms, {dropped} dropped, {late} late",
            self.events,
        )
    }
}
