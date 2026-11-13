//! The hub's fold of the activity ring: one fold for every watcher, and only
//! while a watcher follows it.
//!
//! # One thread folds while a watcher follows
//!
//! **Choice.** The workspace holds one [`Activities`]. A watcher, such as a
//! subscription of the toolset to the activity, gives a sender to
//! [`Activities::watch`]. The first watcher makes the rings of the pool and
//! their fold, and the hub keeps them. While the hub has a watcher, one thread
//! folds the rings once for each tick of 1/60 s, and it ends at the first tick
//! that finds no watcher. Each watcher states its [`Cadence`]. A watcher of the
//! events hears each tick that has events. A watcher of the rows, such as the
//! activity pane of the render bus, also hears each tick while a row holds
//! busy time in its window, so the occupancy moves while no event arrives. The
//! fold makes one shared [`Tick`] for the watchers that hear it. While the hub
//! has a watcher, each judgement and each admission runs at the activity sink,
//! so its fork sites mark the rings. A job reads whether the hub has a watcher
//! from one atomic flag, so a job of a hub with no watcher takes no lock.
//!
//! **Alternatives.** A fold for each watcher drains the rings twice, but the
//! rings have one consumer. A thread that ticks with no watcher wakes 60 times
//! a second for nothing. A watcher of the rows that hears every tick wakes 60
//! times a second while the pool is idle and its rows do not change.
//!
//! **Reversal.** A watcher that needs every tick, such as a clock face, takes
//! the ticks with no change too.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-stream: the hub folds, at most one frame for each tick of
//!   16 ms, and the activity card only appends.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use core::num::NonZeroUsize;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use core::time::Duration;
use std::io;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;
use std::sync::mpsc::Sender;
use std::thread;
use std::time::Instant;

use gandr_core_fork::activity::Activity;
use gandr_core_fork::activity::Event;
use gandr_core_fork::activity::Fold;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Row;
use gandr_core_fork::activity::Slots;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::activity_clock;

use crate::peer::Peer;

mod pane;

pub use self::pane::Pane;

/// The hub's tick: one frame at sixty frames a second.
const TICK: Duration = Duration::from_nanos(16_666_667);

/// The marks each ring holds between two ticks: 24 KiB for each thread. A
/// ring that fills drops its oldest mark and counts the drop.
const SLOTS: NonZeroUsize = NonZeroUsize::MIN.saturating_add(1_023);

/// Lock `mutex`, taking its state as it is when a holder panicked.
///
/// # Specification
/// trivial.
fn lock<Held>(mutex: &Mutex<Held>) -> MutexGuard<'_, Held>
{
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// One tick of the fold that a watcher hears, which every watcher shares.
///
/// It holds the hub's clock at the tick, the events since the last tick that a
/// watcher heard in the order of their sequence numbers, and the row of each
/// core.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Tick
{
    /// The hub's clock at the tick.
    pub clock: Nanos,
    /// The events since the last tick that a watcher heard, in the order of
    /// their sequence numbers.
    pub events: Box<[Event]>,
    /// The row of each core: the pool's threads in order, then the ring of
    /// every other thread.
    pub rows: Box<[Row]>,
}

/// Which ticks of the fold a watcher hears.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Cadence
{
    /// Each tick that has events.
    Events,
    /// Each tick that has events, each tick while a row holds busy time in its
    /// window, and the first tick after the last busy time leaves the window.
    Rows,
}

/// Where a watcher hears its ticks, and which ticks it hears.
type Watcher = (Sender<Arc<Tick>>, Cadence);

/// The rings of the pool and their fold, which the first watcher makes.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Held
{
    /// The rings, which each job at the activity sink writes.
    rings: Arc<Activity>,
    /// The fold, the one consumer of the rings and the one writer of the
    /// sequence numbers.
    fold: Fold,
}

/// The fold's state, which the fold's thread and the watchers change.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Folding
{
    /// The pool whose threads the rings follow.
    pool: Arc<Pool>,
    /// The rings and their fold, once a watcher made them.
    held: Option<Held>,
    /// Where each watcher hears its ticks.
    watchers: BTreeMap<Peer, Watcher>,
    /// Whether a thread folds now.
    folds: bool,
    /// Whether a row held busy time in its window at the last tick.
    busy: bool,
}

/// Whether the hub has a watcher, which a job reads with no lock. A job of a
/// hub with no watcher thus takes no lock.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Watched(AtomicBool);

impl Watched
{
    /// Follow `watchers`: the hub has a watcher while one is left.
    ///
    /// # Specification
    /// trivial.
    fn follow(
        &self,
        watchers: &BTreeMap<Peer, Watcher>,
    )
    {
        self.0.store(!watchers.is_empty(), Ordering::Release);
    }
}

/// What the fold's thread, the watchers and the jobs share.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Shared
{
    /// Whether the hub has a watcher.
    watched: Watched,
    /// The fold's state.
    state: Mutex<Folding>,
}

/// The hub's fold of the activity ring, and its watchers.
///
/// # Specification
/// - provides: [`Activities::watch`] and [`Activities::unwatch`], which start
///   and end a watcher, and the rings that each job writes while the hub has a
///   watcher.
/// - panics: none.
/// - executable: none — a thread and the rings' atomics carry the behaviour.
///
/// # Adequacy
/// - hypothesis: L3 — a watcher hears a task that a job marks, and once the
///   last watcher leaves, the thread ends and no job writes a mark.
/// - witness: `activity::tests::a_watcher_hears_each_task_and_the_fold_ends_without_one`
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Activities(Arc<Shared>);

impl Activities
{
    /// The fold of the activity of `pool`, with no watcher and no ring yet.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn of(pool: Arc<Pool>) -> Self
    {
        Self(Arc::new(Shared {
            watched: Watched::default(),
            state: Mutex::new(Folding {
                pool,
                ..Folding::default()
            }),
        }))
    }

    /// Admit `peer` as a watcher: each tick that `cadence` names goes to
    /// `watcher`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, `peer` watches with `watcher` at `cadence`, in place
    ///   of an earlier watcher of `peer`. The first watcher makes the rings of
    ///   the pool and their fold. When no thread folds, one thread starts to
    ///   fold.
    /// - fails: when the host refuses the thread; then `peer` does not watch.
    /// - panics: none.
    /// - executable: none — the effects are a thread and the rings' atomics.
    ///
    /// # Errors
    /// The host's refusal of the thread.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Activities`]. A watcher of the rows hears the
    ///   ticks after a task while its busy time stays in the window, and a
    ///   watcher of the events hears the tick of the task alone.
    /// - witness: `activity::tests::a_watcher_hears_each_task_and_the_fold_ends_without_one`
    /// - witness: `activity::tests::a_watcher_of_the_rows_hears_the_occupancy_move`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "pool: the hub's fold is the one consumer of the rings, and it drains them on its own thread while the pool's threads fill them"
        )
    )]
    pub fn watch(
        &self,
        peer: Peer,
        watcher: Sender<Arc<Tick>>,
        cadence: Cadence,
    ) -> io::Result<()>
    {
        let mut folding = lock(&self.0.state);
        if folding.held.is_none() {
            let rings = Arc::new(folding.pool.activity(Slots::from(SLOTS)));
            let fold = Fold::new(&rings);
            folding.held = Some(Held { rings, fold });
        }
        drop(folding.watchers.insert(peer, (watcher, cadence)));
        self.0.watched.follow(&folding.watchers);
        if !folding.folds {
            let shared = Arc::clone(&self.0);
            let started = thread::Builder::new()
                .name(String::from("gandr-activity"))
                .spawn(move || folded(&shared));
            if let Err(error) = started {
                drop(folding.watchers.remove(&peer));
                self.0.watched.follow(&folding.watchers);
                return Err(error);
            }
            folding.folds = true;
        }
        drop(folding);
        Ok(())
    }

    /// End the watch of `peer`. The thread ends at its next tick when no
    /// watcher is left.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn unwatch(
        &self,
        peer: Peer,
    )
    {
        let mut folding = lock(&self.0.state);
        drop(folding.watchers.remove(&peer));
        self.0.watched.follow(&folding.watchers);
    }

    /// The rings that a job writes, while the hub has a watcher. A walk that
    /// the toolset runs on the hub's pool records on them too.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rings(&self) -> Option<Arc<Activity>>
    {
        if !self.0.watched.0.load(Ordering::Acquire) {
            return None;
        }
        let folding = lock(&self.0.state);
        if folding.watchers.is_empty() {
            return None;
        }
        folding.held.as_ref().map(|held| Arc::clone(&held.rings))
    }
}

impl Folding
{
    /// One tick of the fold: fold the rings, and send the tick to each
    /// watcher whose cadence names it. `watched` follows the watchers that are
    /// left. With no watcher, no thread folds, and the fold breaks.
    ///
    /// # Specification
    /// trivial.
    fn ticked(
        &mut self,
        watched: &Watched,
    ) -> ControlFlow<()>
    {
        let Self {
            ref mut held,
            ref mut watchers,
            ref mut folds,
            ref mut busy,
            ..
        } = *self;
        let Some(held) = held.as_mut().filter(|_| !watchers.is_empty())
        else {
            *folds = false;
            return ControlFlow::Break(());
        };
        let clock = activity_clock();
        let card = held.fold.tick(&held.rings, clock);
        let evented = !card.events.is_empty();
        // The rows move while a row holds busy time in its window, and once
        // more when the last busy time leaves it.
        let moved = watchers
            .values()
            .any(|&(_, cadence)| cadence == Cadence::Rows)
            && {
                let was = *busy;
                *busy = card
                    .rows
                    .iter()
                    .any(|row| row.cells().any(|cell| u64::from(cell) > 0));
                was || *busy
            };
        if evented || moved {
            let mut shared: Option<Arc<Tick>> = None;
            watchers.retain(|_, &mut (ref watcher, cadence)| {
                if !evented && cadence == Cadence::Events {
                    return true;
                }
                let tick = shared.get_or_insert_with(|| {
                    Arc::new(Tick {
                        clock,
                        events: Box::from(card.events),
                        rows: Box::from(card.rows),
                    })
                });
                watcher.send(Arc::clone(tick)).is_ok()
            });
            watched.follow(watchers);
        }
        ControlFlow::Continue(())
    }
}

/// Fold the rings that `shared` holds once for each tick, and send each tick
/// to each watcher whose cadence names it, until a tick finds no watcher. The
/// ticks keep their period: a late wake shortens the next sleep, and a tick
/// later than a whole period skips the ticks that it missed.
///
/// # Specification
/// trivial.
fn folded(shared: &Shared)
{
    let mut next = Instant::now();
    while lock(&shared.state).ticked(&shared.watched).is_continue() {
        let now = Instant::now();
        next = next.checked_add(TICK).unwrap_or(now);
        let rest = next.saturating_duration_since(now);
        if rest.is_zero() {
            next = now;
        }
        else {
            thread::sleep(rest);
        }
    }
}

#[cfg(test)]
mod tests;
