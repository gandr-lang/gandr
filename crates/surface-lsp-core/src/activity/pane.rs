//! The hub's fold of the ticks into the activity pane of one renderer: the
//! task that each core runs now, and the lengths of the tasks that ended in
//! the window.
//!
//! # The hub folds, the view draws
//!
//! **Choice.** The render-bus face keeps one [`Pane`] for each attached
//! renderer. Each tick that the renderer hears goes through [`Pane::hear`],
//! which answers the [`PoolActivity`] of the tick: for each core, the last 32
//! cells of its row, the kind of its innermost open task, its busy time over
//! the window and the lengths of its tasks that ended in the window, at p50
//! and p99. The totals row sums the cores. So each number that the view shows
//! is a field of a frame, and the view folds nothing.
//!
//! **Alternatives.** The view can fold the events into the lengths itself, but
//! then each face folds them again, and a face that attaches late misses the
//! starts of the open tasks. The shared fold of [`super::Activities`] can keep
//! the lengths for every watcher, but the toolset's watchers read the events
//! and not the lengths.
//!
//! **Reversal.** A second face that reads the lengths moves the fold into the
//! shared fold.

use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;
use gandr_surface_render_remote::CoreActivity;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::Lengths;
use gandr_surface_render_remote::Load;
use gandr_surface_render_remote::PoolActivity;
use gandr_surface_render_remote::SAMPLES;
use gandr_surface_render_remote::SampleUnit;
use gandr_surface_render_remote::Samples;
use gandr_surface_render_remote::TaskKind;

use super::TICK;
use super::Tick;

/// The span of the window, in nanoseconds: the two seconds that a row of the
/// fold holds.
const WINDOW: u64 = 2_000_000_000;

/// The most task lengths that the pane keeps for one core. A core that ends
/// more tasks in the window keeps the latest.
const LENGTHS: usize = 1024;

/// What the pane keeps of one core.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Kept
{
    /// The world of the last task of the core.
    world: Option<World>,
    /// The open tasks of the core, the outermost first, each with its start.
    open: Vec<(Task, Nanos)>,
    /// The end and the length of each task of the core that ended in the
    /// window, the oldest first.
    ended: VecDeque<(Nanos, Nanos)>,
}

/// The hub's fold of the ticks into the activity pane, for one renderer.
///
/// # Specification
/// - provides: [`Pane::hear`], which folds a tick and answers the pane's
///   activity at it.
/// - panics: none.
/// - executable: none — the state is the open tasks and the lengths of each
///   core.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Pane::hear`].
/// - witness: `activity::pane::tests::the_pane_shows_the_task_now_and_the_lengths_of_the_window`
#[derive(Debug, Default)]
pub struct Pane
{
    /// What the pane keeps of each core, in the order of the cores.
    cores: Vec<Kept>,
    /// The lengths of one row, which the percentiles reorder.
    scratch: Vec<Count>,
}

/// The kind of `task`, as the wire names it.
///
/// # Specification
/// trivial.
const fn kind(task: Task) -> TaskKind
{
    match task {
        Task::Fork => TaskKind::Fork,
        Task::Replay => TaskKind::Replay,
        Task::Compile => TaskKind::Compile,
        Task::Fetch => TaskKind::Fetch,
    }
}

/// The lengths at p50 and p99 of the lengths that `scratch` holds, by the
/// nearest rank, and none when it holds none. The order of `scratch` changes.
///
/// # Specification
/// trivial.
fn percentiles(scratch: &mut [Count]) -> Option<Lengths>
{
    let held = scratch.len();
    if held == 0 {
        return None;
    }
    let rank = |percent: usize| percent.saturating_mul(held).div_ceil(100).saturating_sub(1);
    let p50 = *scratch.select_nth_unstable(rank(50)).1;
    let p99 = *scratch.select_nth_unstable(rank(99)).1;
    Some(Lengths { p50, p99 })
}

impl Pane
{
    /// Fold `tick` into the pane, and answer the pane's activity at it.
    ///
    /// # Specification
    /// - requires: the ticks reach the pane in the order of the fold.
    /// - ensures: one row for each row of `tick`, in its order, and the totals.
    ///   A start opens a task on its core, and an end closes the innermost open
    ///   task and keeps its length. An end with no open task closes nothing.
    ///   The `now` of a core is its innermost open task, and its world is the
    ///   world of its last event. Its occupancy is the last 32 cells of its row
    ///   under the ceiling of one tick, its busy time is the sum of the cells
    ///   of the row, and its lengths are those of its tasks that ended in the
    ///   two seconds before the tick, at p50 and p99 by the nearest rank. The
    ///   totals sum the occupancy and the busy time of the cores, under the
    ///   ceiling of one tick for each core, and their lengths are those of
    ///   every core.
    /// - provides: the data of the activity frame of the render bus.
    /// - fails: never.
    /// - panics: none.
    /// - intension: linear in the events of the tick, the cores and the lengths
    ///   of the window; at most 1024 lengths kept for each core.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two cores, one with an open task inside a closed one
    ///   and one with three closed tasks, give the task now, the lengths at p50
    ///   and p99 and the totals; a later tick past the window drops the
    ///   lengths.
    /// - witness: `activity::pane::tests::the_pane_shows_the_task_now_and_the_lengths_of_the_window`
    #[spec(ensures: |ret| ret.cores.len() == tick.rows.len())]
    pub fn hear(
        &mut self,
        tick: &Tick,
    ) -> PoolActivity
    {
        if self.cores.len() < tick.rows.len() {
            self.cores.resize_with(tick.rows.len(), Kept::default);
        }
        for event in &tick.events {
            let Some(kept) = self.cores.get_mut(usize::from(event.core))
            else {
                continue;
            };
            kept.world = Some(event.world);
            match event.edge {
                Edge::Start => kept.open.push((event.task, event.clock)),
                Edge::End => {
                    if let Some((_, start)) = kept.open.pop() {
                        if kept.ended.len() >= LENGTHS {
                            let _oldest = kept.ended.pop_front();
                        }
                        let length = u64::from(event.clock).saturating_sub(u64::from(start));
                        kept.ended.push_back((event.clock, Nanos::from(length)));
                    }
                },
            }
        }
        let since = u64::from(tick.clock).saturating_sub(WINDOW);
        // A cell holds at most the time of one tick, and the totals hold it
        // for each core: the fixed scales of the occupancy.
        let span = u64::try_from(TICK.as_nanos()).unwrap_or(u64::MAX);
        let mut occupied = [0_u64; SAMPLES];
        let mut busy = 0_u64;
        let mut cores = Vec::with_capacity(tick.rows.len());
        for (index, (row, kept)) in tick.rows.iter().zip(&mut self.cores).enumerate() {
            let stale = kept
                .ended
                .partition_point(|&(end, _)| u64::from(end) < since);
            drop(kept.ended.drain(.. stale));
            let cells = row.cells();
            let newest = cells.clone().skip(cells.len().saturating_sub(SAMPLES));
            let mut samples = [Count(0); SAMPLES];
            for ((cell, sample), total) in newest.zip(&mut samples).zip(&mut occupied) {
                let cell = u64::from(cell);
                *total = total.saturating_add(cell);
                *sample = Count(cell);
            }
            let spent = cells.map(u64::from).fold(0_u64, u64::saturating_add);
            busy = busy.saturating_add(spent);
            self.scratch.clear();
            self.scratch.extend(
                kept.ended
                    .iter()
                    .map(|&(_, length)| Count(u64::from(length))),
            );
            cores.push(CoreActivity {
                world: kept.world.map(|world| Count(u64::from(u32::from(world)))),
                core: Count(u64::try_from(index).unwrap_or(u64::MAX)),
                now: kept.open.last().map(|&(task, _)| kind(task)),
                load: Load {
                    occupancy: Samples::bounded(SampleUnit::Nanoseconds, samples, Count(span)),
                    busy: Count(spent),
                    lengths: percentiles(&mut self.scratch),
                },
            });
        }
        self.scratch.clear();
        self.scratch.extend(self.cores.iter().flat_map(|kept| {
            kept.ended
                .iter()
                .map(|&(_, length)| Count(u64::from(length)))
        }));
        let width = u64::try_from(cores.len()).unwrap_or(u64::MAX);
        PoolActivity {
            window: Count(WINDOW),
            cores,
            totals: Load {
                occupancy: Samples::bounded(
                    SampleUnit::Nanoseconds,
                    occupied.map(Count),
                    Count(span.saturating_mul(width)),
                ),
                busy: Count(busy),
                lengths: percentiles(&mut self.scratch),
            },
        }
    }
}

#[cfg(test)]
mod tests;
