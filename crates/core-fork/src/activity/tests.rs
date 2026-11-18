extern crate std;

use alloc::vec::Vec;
use core::num::NonZeroU16;
use core::num::NonZeroUsize;

use super::*;

/// One core.
const ONE: Cores = Cores(NonZeroU16::MIN);

/// A ring of eight slots.
const EIGHT: Slots = Slots(NonZeroUsize::new(8).unwrap());

/// The mark of a fork job on `declaration`, at `clock`, in world zero.
///
/// # Specification
/// trivial.
fn mark(
    edge: Edge,
    declaration: Declaration,
    clock: Nanos,
) -> Mark
{
    Mark {
        task: Task::Fork,
        edge,
        declaration: Declared::from(declaration),
        world: World(0),
        clock,
    }
}

/// The sum of a row's cells.
///
/// # Specification
/// trivial.
fn busy(row: &Row) -> Nanos
{
    Nanos(row.cells().map(u64::from).sum::<u64>())
}

/// Whether the events of `card` are in the order of their sequence numbers,
/// each one past the last number of the tick before.
///
/// # Specification
/// trivial.
fn numbered_on(
    card: &ActivityCard<'_>,
    last: &mut Last,
) -> Numbered
{
    let mut numbered = Numbered::Yes;
    for event in card.events {
        if let Last::Seen(previous) = *last
            && event.sequence.0 != previous.0.saturating_add(1)
        {
            numbered = Numbered::No;
        }
        *last = Last::Seen(event.sequence);
    }
    numbered
}

/// The last sequence number a test saw, if any.
#[derive(Clone, Copy)]
enum Last
{
    /// No event is seen yet.
    Unseen,
    /// The last event seen has this number.
    Seen(Sequence),
}

/// Whether a card's numbers follow on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Numbered
{
    /// Each number is one past the number before it.
    Yes,
    /// A number is out of turn.
    No,
}

#[test]
fn one_producer_s_events_reach_the_card_in_order()
{
    let activity = Activity::new(ONE, EIGHT);
    let mut fold = Fold::new(&activity);
    let producer = activity.producer(Core(0)).unwrap();
    for (edge, declaration, clock) in [
        (Edge::Start, 0_u32, 10_u64),
        (Edge::End, 0, 20),
        (Edge::Start, 1, 30),
    ] {
        producer.record(mark(edge, Declaration(declaration), Nanos(clock)));
    }
    let card = fold.tick(&activity, Nanos(40));
    let read: Vec<(u64, Edge, u32, u64, usize)> = card
        .events
        .iter()
        .map(|event| {
            (
                u64::from(event.sequence),
                event.edge,
                event.declaration.0,
                u64::from(event.clock),
                usize::from(event.core),
            )
        })
        .collect();
    assert_eq!(
        read,
        [
            (0, Edge::Start, 0, 10, 0),
            (1, Edge::End, 0, 20, 0),
            (2, Edge::Start, 1, 30, 0),
        ],
        "the card holds each mark once, in the order written, numbered from zero, with its core"
    );
    assert!(
        fold.tick(&activity, Nanos(40)).events.is_empty(),
        "a tick gives only the events since the last tick"
    );
    producer.record(mark(Edge::End, Declaration(1), Nanos(50)));
    let later: Vec<u64> = fold
        .tick(&activity, Nanos(60))
        .events
        .iter()
        .map(|event| u64::from(event.sequence))
        .collect();
    assert_eq!(later, [3], "a later tick numbers on from the last number");
}

#[test]
fn two_producers_merge_in_the_order_of_the_clock()
{
    let activity = Activity::new(Cores(NonZeroU16::new(2).unwrap()), EIGHT);
    let mut fold = Fold::new(&activity);
    let first = activity.producer(Core(0)).unwrap();
    let second = activity.producer(Core(1)).unwrap();
    first.record(mark(Edge::Start, Declaration(0), Nanos(1)));
    second.record(mark(Edge::Start, Declaration(1), Nanos(2)));
    second.record(mark(Edge::End, Declaration(1), Nanos(3)));
    first.record(mark(Edge::End, Declaration(0), Nanos(4)));
    second.record(mark(Edge::Start, Declaration(2), Nanos(4)));
    let card = fold.tick(&activity, Nanos(5));
    let read: Vec<(u64, u64, usize, Edge)> = card
        .events
        .iter()
        .map(|event| {
            (
                u64::from(event.sequence),
                u64::from(event.clock),
                usize::from(event.core),
                event.edge,
            )
        })
        .collect();
    assert_eq!(
        read,
        [
            (0, 1, 0, Edge::Start),
            (1, 2, 1, Edge::Start),
            (2, 3, 1, Edge::End),
            (3, 4, 0, Edge::End),
            (4, 4, 1, Edge::Start),
        ],
        "the runs of the two rings merge by the clock, then by the core, and are numbered in that order"
    );
    let rows: Vec<u64> = card.rows.iter().map(|row| u64::from(busy(row))).collect();
    assert_eq!(
        rows,
        [3, 2],
        "each core is busy from its start to its end, and an open task up to the tick"
    );
}

#[test]
fn a_full_ring_drops_its_oldest_event_and_counts_the_drop()
{
    let activity = Activity::new(ONE, Slots(NonZeroUsize::new(2).unwrap()));
    let mut fold = Fold::new(&activity);
    let producer = activity.producer(Core(0)).unwrap();
    for clock in [1_u64, 2, 3] {
        producer.record(mark(Edge::Start, Declaration(0), Nanos(clock)));
    }
    let card = fold.tick(&activity, Nanos(4));
    let kept: Vec<u64> = card
        .events
        .iter()
        .map(|event| u64::from(event.clock))
        .collect();
    assert_eq!(kept, [2, 3], "the ring keeps its newest marks");
    let dropped: Vec<u64> = card
        .rows
        .iter()
        .map(|row| u64::from(row.dropped()))
        .collect();
    assert_eq!(dropped, [1], "the ring counts the mark it dropped");
}

#[test]
fn a_core_has_one_producer_at_a_time()
{
    let activity = Activity::new(ONE, EIGHT);
    let held = activity.producer(Core(0)).unwrap();
    assert_eq!(
        activity.producer(Core(0)).err(),
        Some(Unclaimable::Held),
        "a second producer of one core is refused"
    );
    drop(held);
    assert!(
        activity.producer(Core(0)).is_ok(),
        "a dropped producer frees its ring"
    );
    assert_eq!(
        activity.producer(Core(1)).err(),
        Some(Unclaimable::Absent),
        "a core past the count has no ring"
    );
}

#[test]
fn a_task_fills_the_cells_it_spans()
{
    let activity = Activity::new(ONE, EIGHT);
    let mut fold = Fold::new(&activity);
    let producer = activity.producer(Core(0)).unwrap();
    let start = CELL.saturating_mul(10).saturating_add(8_333_333);
    let end = CELL.saturating_mul(11).saturating_add(4_166_666);
    producer.record(mark(Edge::Start, Declaration(0), Nanos(start)));
    producer.record(mark(Edge::End, Declaration(0), Nanos(end)));
    let card = fold.tick(&activity, Nanos(CELL.saturating_mul(12)));
    let row = card.rows.first().unwrap();
    let cells: Vec<u64> = row.cells().map(u64::from).collect();
    assert_eq!(cells.len(), CELLS, "a row reads 120 cells");
    let newest: Vec<u64> = cells.iter().skip(117).copied().collect();
    assert_eq!(
        newest,
        [CELL.saturating_sub(8_333_333), 4_166_666, 0],
        "the task's time splits between cells 10 and 11, and the tick's cell 12 is idle"
    );
    assert_eq!(
        u64::from(busy(row)),
        end.saturating_sub(start),
        "the cells sum to the task's time"
    );
}

#[test]
fn nested_tasks_count_once_and_an_open_task_counts_up_to_the_tick()
{
    let activity = Activity::new(ONE, EIGHT);
    let mut fold = Fold::new(&activity);
    let producer = activity.producer(Core(0)).unwrap();
    let base = CELL.saturating_mul(5);
    let at = |offset: u64| Nanos(base.saturating_add(offset));
    producer.record(mark(Edge::Start, Declaration(0), at(0)));
    producer.record(mark(Edge::Start, Declaration(1), at(100)));
    producer.record(mark(Edge::End, Declaration(1), at(200)));
    let first = fold.tick(&activity, at(1_000));
    assert_eq!(
        u64::from(busy(first.rows.first().unwrap())),
        1_000,
        "the inner task adds nothing, and the open outer task counts up to the tick"
    );
    producer.record(mark(Edge::End, Declaration(0), at(1_500)));
    let second = fold.tick(&activity, at(2_000));
    assert_eq!(
        u64::from(busy(second.rows.first().unwrap())),
        1_500,
        "the outer task's end adds only the time after the last tick"
    );
}

#[test]
fn time_older_than_the_window_leaves_the_row()
{
    let activity = Activity::new(ONE, EIGHT);
    let mut fold = Fold::new(&activity);
    let producer = activity.producer(Core(0)).unwrap();
    producer.record(mark(Edge::Start, Declaration(0), Nanos(0)));
    producer.record(mark(Edge::End, Declaration(0), Nanos(CELL)));
    let inside = fold.tick(&activity, Nanos(CELL.saturating_mul(50)));
    assert_eq!(
        u64::from(busy(inside.rows.first().unwrap())),
        CELL,
        "the task's cell is inside the window"
    );
    let past = fold.tick(&activity, Nanos(CELL.saturating_mul(200)));
    assert_eq!(
        u64::from(busy(past.rows.first().unwrap())),
        0,
        "the window moved past the task's cell"
    );
    assert_eq!(
        u64::from(past.rows.first().unwrap().total()),
        CELL,
        "the total keeps the time that the window left"
    );
}

#[test]
fn a_late_event_takes_the_next_number_is_counted_and_lands_in_its_own_cell()
{
    let activity = Activity::new(Cores(NonZeroU16::new(2).unwrap()), EIGHT);
    let mut fold = Fold::new(&activity);
    let first = activity.producer(Core(0)).unwrap();
    let second = activity.producer(Core(1)).unwrap();
    first.record(mark(Edge::Start, Declaration(0), Nanos(10)));
    first.record(mark(Edge::End, Declaration(0), Nanos(28)));
    second.record(mark(Edge::Start, Declaration(1), Nanos(5)));
    let before = fold.tick(&activity, Nanos(30));
    assert!(
        before
            .events
            .iter()
            .all(|event| event.arrival == Arrival::InTurn),
        "a tick's own marks merge by the clock and arrive in turn"
    );
    let open: Vec<u64> = before.rows.iter().map(|row| u64::from(busy(row))).collect();
    assert_eq!(
        open,
        [18, 25],
        "the second core's open task counts up to the tick"
    );
    second.record(mark(Edge::End, Declaration(1), Nanos(20)));
    second.record(mark(Edge::Start, Declaration(2), Nanos(22)));
    second.record(mark(Edge::End, Declaration(2), Nanos(35)));
    first.record(mark(Edge::Start, Declaration(3), Nanos(29)));
    first.record(mark(Edge::End, Declaration(3), Nanos(31)));
    let after = fold.tick(&activity, Nanos(40));
    let read: Vec<(u64, u64, usize, Edge, Arrival)> = after
        .events
        .iter()
        .map(|event| {
            (
                u64::from(event.sequence),
                u64::from(event.clock),
                usize::from(event.core),
                event.edge,
                event.arrival,
            )
        })
        .collect();
    assert_eq!(
        read,
        [
            (3, 20, 1, Edge::End, Arrival::Late),
            (4, 22, 1, Edge::Start, Arrival::Late),
            (5, 29, 0, Edge::Start, Arrival::InTurn),
            (6, 31, 0, Edge::End, Arrival::InTurn),
            (7, 35, 1, Edge::End, Arrival::InTurn),
        ],
        "an event earlier than the latest clock numbered takes the next number and is marked late"
    );
    let late: Vec<u64> = after.rows.iter().map(|row| u64::from(row.late())).collect();
    assert_eq!(late, [0, 2], "each core's row counts its late events");
    let rows: Vec<u64> = after.rows.iter().map(|row| u64::from(busy(row))).collect();
    assert_eq!(
        rows,
        [20, 28],
        "the late end takes back the time the tick counted past it, and the cells hold each task's own time"
    );
    let totals: Vec<u64> = after
        .rows
        .iter()
        .map(|row| u64::from(row.total()))
        .collect();
    assert_eq!(
        totals,
        [20, 28],
        "the total takes back the late end's time too"
    );
}

#[test]
fn a_worker_writes_its_core_s_ring_without_a_claim()
{
    let activity = Activity::new(Cores(NonZeroU16::new(2).unwrap()), EIGHT);
    let mut fold = Fold::new(&activity);
    let held = activity.producer(Core(0)).unwrap();
    let worker = activity.worker(Core(0)).unwrap();
    held.record(mark(Edge::Start, Declaration(4), Nanos(1)));
    worker.record(Mark {
        task: Task::Fetch,
        edge: Edge::Start,
        declaration: Declared::NONE,
        world: World(0),
        clock: Nanos(2),
    });
    let card = fold.tick(&activity, Nanos(3));
    let read: Vec<(Task, Maybe<Declaration, unnamed::Absent>)> = card
        .events
        .iter()
        .map(|event| (event.task, event.declaration.declaration()))
        .collect();
    assert_eq!(
        read,
        [
            (Task::Fork, Maybe::Present(Declaration(4))),
            (Task::Fetch, Maybe::Absent(unnamed::Absent::Unnamed)),
        ],
        "a worker writes the ring that a producer holds, and a mark of no declaration reads as unnamed"
    );
    assert_eq!(
        activity.worker(Core(2)).err(),
        Some(Unclaimable::Absent),
        "a core past the count has no ring"
    );
    assert_eq!(
        activity.cores(),
        Cores(NonZeroU16::new(2).unwrap()),
        "the activity holds a ring for each core"
    );
}

#[test]
fn producers_on_their_threads_reach_the_fold_once_each_in_order()
{
    const CORES: u16 = 4;
    const PAIRS: u32 = 1_000;
    let activity = Activity::new(
        Cores(NonZeroU16::new(CORES).unwrap()),
        Slots(NonZeroUsize::new(4_096).unwrap()),
    );
    let mut fold = Fold::new(&activity);
    let now = Nanos(u64::from(PAIRS).saturating_mul(2));
    let mut seen: Vec<Event> = Vec::new();
    let mut last = Last::Unseen;
    let mut numbered = Numbered::Yes;
    std::thread::scope(|scope| {
        let mut running = Vec::new();
        for index in 0 .. CORES {
            let producer = activity.producer(Core(index)).unwrap();
            running.push(scope.spawn(move || {
                for pair in 0 .. PAIRS {
                    let clock = u64::from(pair).saturating_mul(2);
                    producer.record(mark(Edge::Start, Declaration(pair), Nanos(clock)));
                    producer.record(mark(
                        Edge::End,
                        Declaration(pair),
                        Nanos(clock.saturating_add(1)),
                    ));
                }
            }));
        }
        while running.iter().any(|thread| !thread.is_finished()) {
            let card = fold.tick(&activity, now);
            if numbered_on(&card, &mut last) == Numbered::No {
                numbered = Numbered::No;
            }
            seen.extend_from_slice(card.events);
        }
    });
    let card = fold.tick(&activity, now);
    if numbered_on(&card, &mut last) == Numbered::No {
        numbered = Numbered::No;
    }
    seen.extend_from_slice(card.events);
    assert_eq!(
        numbered,
        Numbered::Yes,
        "the fold numbers the events on, one by one, across its ticks"
    );
    let total =
        usize::from(CORES).saturating_mul(usize::try_from(PAIRS).unwrap().saturating_mul(2));
    assert_eq!(seen.len(), total, "the fold gives every mark once");
    for index in 0 .. CORES {
        let written: Vec<(u32, Edge)> = seen
            .iter()
            .filter(|event| event.core == Core(index))
            .map(|event| (event.declaration.0, event.edge))
            .collect();
        let expected: Vec<(u32, Edge)> = (0 .. PAIRS)
            .flat_map(|pair| [(pair, Edge::Start), (pair, Edge::End)])
            .collect();
        assert_eq!(
            written, expected,
            "core {index}'s events arrive in its order"
        );
    }
    for (index, row) in (0 .. CORES).zip(card.rows) {
        assert_eq!(
            u64::from(busy(row)),
            u64::from(PAIRS),
            "each core's cells sum to its busy time"
        );
        assert_eq!(u64::from(row.dropped()), 0, "no ring was full");
        let late = seen
            .iter()
            .filter(|event| event.core == Core(index) && event.arrival == Arrival::Late)
            .count();
        assert_eq!(
            u64::from(row.late()),
            u64::try_from(late).unwrap(),
            "core {index}'s row counts each of its late events"
        );
    }
}
