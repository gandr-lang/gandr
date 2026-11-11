use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::num::NonZeroUsize;

use gandr_core_fork::Fork as _;
use gandr_core_fork::activity::Activity;
use gandr_core_fork::activity::Core;
use gandr_core_fork::activity::Declaration;
use gandr_core_fork::activity::Declared;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Event;
use gandr_core_fork::activity::Fold;
use gandr_core_fork::activity::Slots;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;
use quenchant_shape::shape::Maybe;

use super::clock;
use super::marked;
use crate::pool::ItemIndex;
use crate::pool::Pool;
use crate::width::Threads;
use crate::width::Width;

/// A pool of four threads.
///
/// # Specification
/// trivial.
fn four() -> Pool
{
    Pool::new(Width::Threads(Threads::from(
        NonZeroUsize::new(4_usize).unwrap(),
    )))
}

/// Rings of a thousand slots.
///
/// # Specification
/// trivial.
fn slots() -> Slots
{
    Slots::from(NonZeroUsize::new(1_024_usize).unwrap())
}

/// The declaration of the item at `index`: its place past 100.
///
/// # Specification
/// trivial.
fn past_a_hundred(index: ItemIndex) -> Declared
{
    let place = u32::try_from(usize::from(index)).unwrap();
    Declared::from(Declaration::from(place.saturating_add(100)))
}

/// The events of one tick of a fresh fold over `activity`.
///
/// # Specification
/// trivial.
fn events(activity: &Activity) -> Vec<Event>
{
    let mut fold = Fold::new(activity);
    fold.tick(activity, clock()).events.to_vec()
}

#[test]
fn a_recorded_fork_marks_each_item_with_its_declaration()
{
    let pool = four();
    let activity = pool.activity(slots());
    let recording = pool.recording(&activity, (Task::Fork, World::from(0)), past_a_hundred);
    let mut items = [0_u32; 64];
    recording.each(
        &mut items,
        || (),
        |&mut (), item| *item = item.saturating_add(1),
    );
    assert!(items.iter().all(|&item| item == 1), "each item runs once");
    let events = events(&activity);
    let mut marked: BTreeMap<Declared, Vec<(Edge, Core)>> = BTreeMap::new();
    for event in &events {
        marked
            .entry(event.declaration)
            .or_default()
            .push((event.edge, event.core));
    }
    assert_eq!(marked.len(), 64, "each item's declaration is marked");
    for (index, (declared, edges)) in marked.iter().enumerate() {
        assert_eq!(
            *declared,
            past_a_hundred(ItemIndex(index)),
            "the site names each item's declaration by its place"
        );
        let [(Edge::Start, start), (Edge::End, end)] = *edges.as_slice()
        else {
            panic!("item {index} is marked once, start before end: {edges:?}");
        };
        assert_eq!(start, end, "a job starts and ends on one thread's ring");
        assert!(
            usize::from(start) < 4,
            "a job on the pool's threads marks a pool thread's ring"
        );
    }
    assert!(
        events.iter().all(|event| event.task == Task::Fork),
        "each mark names the fork's task"
    );
}

#[test]
fn a_recorded_join_marks_each_half()
{
    let pool = four();
    let activity = pool.activity(slots());
    let recording = pool.recording(&activity, (Task::Replay, World::from(1)), past_a_hundred);
    assert_eq!(
        recording.join(|| 'l', || 'r'),
        ('l', 'r'),
        "both halves run, in argument order"
    );
    let read: Vec<(
        Edge,
        Maybe<Declaration, gandr_core_fork::activity::unnamed::Absent>,
    )> = events(&activity)
        .iter()
        .map(|event| (event.edge, event.declaration.declaration()))
        .collect();
    let starts = read
        .iter()
        .filter(|&&(edge, _)| edge == Edge::Start)
        .count();
    assert_eq!(
        (read.len(), starts),
        (4, 2),
        "each half is marked once at its start and once at its end"
    );
    assert!(
        read.iter()
            .all(|&(_, declared)| matches!(declared, Maybe::Absent(_))),
        "a half names no declaration"
    );
}

#[test]
fn a_serial_recorded_fork_marks_the_calling_thread_s_ring()
{
    let pool = Pool::default();
    let activity = pool.activity(slots());
    let recording = pool.recording(&activity, (Task::Fork, World::from(0)), past_a_hundred);
    let mut items = [0_u32; 3];
    recording.each(
        &mut items,
        || (),
        |&mut (), item| *item = item.saturating_add(1),
    );
    let cores: Vec<usize> = events(&activity)
        .iter()
        .map(|event| usize::from(event.core))
        .collect();
    assert_eq!(
        cores, [1; 6],
        "a serial pool runs each job on the calling thread, which writes the last ring"
    );
}

#[test]
fn a_marked_task_is_one_start_and_one_end_on_its_thread_s_ring()
{
    let pool = four();
    let activity = pool.activity(slots());
    let declared = Declared::from(Declaration::from(7));
    assert_eq!(
        marked(&activity, (Task::Replay, World::from(2)), declared, || 'a'),
        'a',
        "the task answers what its work answers"
    );
    let read: Vec<(Edge, usize, Task, World, Declared)> = events(&activity)
        .iter()
        .map(|event| {
            (
                event.edge,
                usize::from(event.core),
                event.task,
                event.world,
                event.declaration,
            )
        })
        .collect();
    assert_eq!(
        read,
        [
            (Edge::Start, 4, Task::Replay, World::from(2), declared),
            (Edge::End, 4, Task::Replay, World::from(2), declared),
        ],
        "a thread outside the pool writes the last ring, start then end, with the task's kind, world and declaration"
    );
}
