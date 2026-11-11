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
        .watch(peer, watcher)
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
