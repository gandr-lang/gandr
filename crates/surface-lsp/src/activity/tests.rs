use alloc::sync::Arc;
use alloc::vec::Vec;
use core::num::NonZeroU16;
use core::num::NonZeroUsize;
use core::time::Duration;
use std::sync::mpsc::channel;

use gandr_core_fork::activity::Declared;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::marked;

use super::Activities;
use super::Cadence;
use super::lock;
use crate::server::Peer;

#[test]
fn a_watcher_hears_each_task_and_the_fold_ends_without_one()
{
    let activities = Activities::of(Arc::new(Pool::default()));
    assert!(
        activities.rings().is_none(),
        "with no watcher, no job writes a mark"
    );
    let (watcher, ticks) = channel();
    let peer = Peer::from(1_u64);
    activities
        .watch(peer, watcher, Cadence::Events)
        .expect("the host starts the fold's thread");
    let rings = activities
        .rings()
        .expect("while a watcher follows, each job writes the rings");
    marked(
        &rings,
        (Task::Replay, World::from(0)),
        Declared::NONE,
        || (),
    );
    let tick = ticks
        .recv_timeout(Duration::from_secs(5))
        .expect("the tick with the task reaches the watcher");
    let read: Vec<(Edge, Task)> = tick
        .events
        .iter()
        .map(|event| (event.edge, event.task))
        .collect();
    assert_eq!(
        read,
        [(Edge::Start, Task::Replay), (Edge::End, Task::Replay)],
        "the watcher hears the task's start, then its end"
    );
    assert_eq!(
        tick.rows.len(),
        NonZeroUsize::from(NonZeroU16::from(rings.cores())).get(),
        "the tick holds the row of each ring"
    );
    activities.unwatch(peer);
    assert!(
        activities.rings().is_none(),
        "once the last watcher leaves, no job writes a mark"
    );
    let ended = (0_u8 .. 100_u8).any(|_| {
        std::thread::sleep(Duration::from_millis(10));
        !lock(&activities.0.state).folds
    });
    assert!(ended, "the fold's thread ends once no watcher is left");
}

#[test]
fn a_watcher_of_the_rows_hears_the_occupancy_move()
{
    let activities = Activities::of(Arc::new(Pool::default()));
    let (rows_watcher, rows) = channel();
    let (events_watcher, events) = channel();
    let (pane, toolset) = (Peer::from(1_u64), Peer::from(2_u64));
    activities
        .watch(pane, rows_watcher, Cadence::Rows)
        .expect("the host starts the fold's thread");
    activities
        .watch(toolset, events_watcher, Cadence::Events)
        .expect("the fold's thread runs");
    let rings = activities.rings().expect("a watcher follows");
    marked(
        &rings,
        (Task::Replay, World::from(0)),
        Declared::NONE,
        || std::thread::sleep(Duration::from_millis(1)),
    );
    let mut heard = 0_usize;
    while heard < 2 {
        let tick = events
            .recv_timeout(Duration::from_secs(5))
            .expect("the ticks of the task reach the watcher of the events");
        assert!(!tick.events.is_empty(), "each tick it hears has an event");
        heard = heard.saturating_add(tick.events.len());
    }
    assert_eq!(heard, 2, "the task's start and its end");
    let moved = (0_u8 .. 10_u8)
        .filter_map(|_| rows.recv_timeout(Duration::from_secs(5)).ok())
        .filter(|tick| tick.events.is_empty())
        .count();
    assert!(
        moved > 0,
        "while the task's busy time is in the window, the watcher of the rows hears ticks with no event"
    );
    assert!(
        events.recv_timeout(Duration::from_millis(200)).is_err(),
        "the watcher of the events hears no tick with no event"
    );
    std::thread::sleep(Duration::from_millis(2_200));
    while rows.try_recv().is_ok() {}
    assert!(
        rows.recv_timeout(Duration::from_millis(200)).is_err(),
        "once the busy time leaves the window, the rows do not move and no tick is sent"
    );
    activities.unwatch(pane);
    activities.unwatch(toolset);
}
