use alloc::boxed::Box;
use core::num::NonZeroU16;
use core::num::NonZeroUsize;
use core::time::Duration;

use gandr_core_fork::activity::Activity;
use gandr_core_fork::activity::Core;
use gandr_core_fork::activity::Cores;
use gandr_core_fork::activity::Declared;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Fold;
use gandr_core_fork::activity::Mark;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Slots;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::Lengths;
use gandr_surface_render_remote::TaskKind;

use super::Pane;
use crate::activity::Tick;

/// The clock of the fold at `at`.
///
/// # Specification
/// trivial.
fn clock(at: Duration) -> Nanos
{
    Nanos::from(u64::try_from(at.as_nanos()).unwrap_or(u64::MAX))
}

/// The mark of `task` at the `edge` given, at `at`.
///
/// # Specification
/// trivial.
fn mark(
    task: Task,
    edge: Edge,
    at: Duration,
) -> Mark
{
    Mark {
        task,
        edge,
        declaration: Declared::NONE,
        world: World::from(0_u32),
        clock: clock(at),
    }
}

/// The tick of `fold` over `activity` at `at`, as the hub's fold makes it.
///
/// # Specification
/// trivial.
fn tick(
    fold: &mut Fold,
    activity: &Activity,
    at: Duration,
) -> Tick
{
    let clock = clock(at);
    let card = fold.tick(activity, clock);
    Tick {
        clock,
        events: Box::from(card.events),
        rows: Box::from(card.rows),
    }
}

#[test]
fn the_pane_shows_the_task_now_and_the_lengths_of_the_window()
{
    let activity = Activity::new(
        Cores::from(NonZeroU16::new(2).expect("two cores")),
        Slots::from(NonZeroUsize::new(64).expect("64 slots")),
    );
    let mut fold = Fold::new(&activity);
    {
        let first = activity.producer(Core::from(0)).expect("the first ring");
        first.record(mark(Task::Replay, Edge::Start, Duration::from_millis(1)));
        first.record(mark(Task::Fork, Edge::Start, Duration::from_millis(2)));
        first.record(mark(Task::Fork, Edge::End, Duration::from_millis(5)));
        let second = activity.producer(Core::from(1)).expect("the second ring");
        for (start, end) in [(10, 11), (12, 14), (15, 20)] {
            second.record(mark(Task::Fork, Edge::Start, Duration::from_millis(start)));
            second.record(mark(Task::Fork, Edge::End, Duration::from_millis(end)));
        }
    }
    let mut pane = Pane::default();
    let shown = pane.hear(&tick(&mut fold, &activity, Duration::from_millis(30)));
    let &[ref first, ref second] = shown.cores.as_slice()
    else {
        panic!("one row per core: {shown:#?}");
    };
    assert_eq!(
        (first.world, first.now, second.now),
        (Some(Count(0)), Some(TaskKind::Replay), None),
        "the first core runs its replay now, and the second is idle"
    );
    assert_eq!(
        first.load.lengths,
        Some(Lengths {
            p50: Count(3_000_000),
            p99: Count(3_000_000),
        }),
        "the fork that ended inside the open replay is the one length of the first core"
    );
    assert_eq!(
        second.load.lengths,
        Some(Lengths {
            p50: Count(2_000_000),
            p99: Count(5_000_000),
        }),
        "the lengths 1, 2 and 5 ms give p50 2 ms and p99 5 ms by the nearest rank"
    );
    assert_eq!(
        (first.load.busy, second.load.busy, shown.totals.busy),
        (Count(29_000_000), Count(8_000_000), Count(37_000_000)),
        "the open replay counts up to the tick, the nested fork once, and the totals sum the cores"
    );
    assert_eq!(
        (
            first.load.occupancy.ceiling(),
            shown.totals.occupancy.ceiling()
        ),
        (Some(Count(16_666_667)), Some(Count(33_333_334))),
        "a cell holds one tick at most, and the totals one tick for each core"
    );
    for row in [first, second] {
        assert_eq!(
            row.load
                .occupancy
                .values()
                .iter()
                .map(|cell| cell.0)
                .sum::<u64>(),
            row.load.busy.0,
            "each busy cell of the window lies in the last 32 cells"
        );
    }
    let summed: alloc::vec::Vec<Count> = first
        .load
        .occupancy
        .values()
        .iter()
        .zip(second.load.occupancy.values())
        .map(|(left, right)| Count(left.0.saturating_add(right.0)))
        .collect();
    assert_eq!(
        shown.totals.occupancy.values(),
        summed.as_slice(),
        "the totals sum the occupancy of the cores cell by cell"
    );
    assert_eq!(
        shown.totals.lengths,
        Some(Lengths {
            p50: Count(2_000_000),
            p99: Count(5_000_000),
        }),
        "the totals take the lengths of every core"
    );
    let later = pane.hear(&tick(&mut fold, &activity, Duration::from_millis(2_100)));
    assert_eq!(
        later
            .cores
            .iter()
            .map(|row| (row.now, row.load.lengths))
            .collect::<alloc::vec::Vec<_>>(),
        [(Some(TaskKind::Replay), None), (None, None)],
        "past the window, no length is left, and the replay still runs"
    );
}
