//! The hub's watch over the files its documents' closures name, for the
//! connections whose client watches none.
//!
//! A client that watches files tells the server of a change on disk through
//! `workspace/didChangeWatchedFiles`, and the hub leaves it to. A connection
//! whose client cannot — and every face that only reads the hub's copies, the
//! model's session and the side view among them — would otherwise go on
//! answering from a closure checked against the files as they were. For each
//! such connection the hub follows the files its copies' closures named at
//! their last judgement, asks the operating system for the events of the
//! directories holding them, through `notify`'s recommended watcher, and hands
//! each changed file to that connection's loop, which rechecks the copies
//! naming it as a client's notification would.
//!
//! Directories are watched rather than files: an editor that saves by writing
//! a new file and renaming it over the old one replaces the file a per-file
//! watch held. A path is followed as [`named_path`] names it, and matched to
//! the system's events by the path it resolves to.
//!
//! The system's watcher is asked on a thread of its own. On macOS a watch
//! restarts the event stream, a call to `fseventsd` that every process's
//! registration waits its turn for, and under load it took longer than a
//! connection may keep its client waiting. While a registration is pending,
//! the followed files are read every [`POLL`] instead, so a change made then
//! is still handed on.
//!
//! [`named_path`]: gandr_surface_dispatcher::named_path

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::time::Duration;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Condvar;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;
use std::sync::mpsc;
use std::thread;
use std::time::SystemTime;

use anodized::spec;
use notify::Event;
use notify::EventKind;
use notify::RecommendedWatcher;
use notify::RecursiveMode;
use notify::Watcher as _;

use crate::quiet::Changes;
use crate::server::Peer;

/// How often the followed files are read while a registration is pending.
pub const POLL: Duration = Duration::from_millis(50);

/// What a followed file was when it was last read: its modification time
/// and length, or its absence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Stamp(Option<(Option<SystemTime>, u64)>);

impl Stamp
{
    /// The file at `path` as it is now.
    ///
    /// # Specification
    /// trivial.
    fn of(path: &Path) -> Self
    {
        Self(
            std::fs::metadata(path)
                .ok()
                .map(|metadata| (metadata.modified().ok(), metadata.len())),
        )
    }
}

/// The number of a set of directories asked of the system's watcher, in the
/// order they were asked.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Request(u64);

/// Which followed files a poll reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// Every one.
    Every,
    /// Every one while a registration is pending, else those in a refused
    /// directory.
    Due,
}

/// One connection the watch serves: where its loop takes changes, and the
/// paths its copies' closures name.
#[derive(Debug)]
struct Follower
{
    /// The loop's change handle.
    changes: Changes,
    /// The paths followed, as the closures named them.
    named: BTreeSet<PathBuf>,
}

/// What the watcher's thread, the arming thread and the polling thread read.
#[derive(Debug, Default)]
struct Followed
{
    /// Each connection the watch serves.
    followers: BTreeMap<Peer, Follower>,
    /// Each followed path's resolved form, to the path as named.
    resolved: BTreeMap<PathBuf, PathBuf>,
    /// Each followed path's resolved form, with the file as last read.
    stamps: BTreeMap<PathBuf, Stamp>,
    /// The latest set of directories asked for.
    asked: Request,
    /// The latest set of directories the system's watcher holds.
    applied: Request,
    /// The directories the system's watcher refused.
    refused: BTreeSet<PathBuf>,
    /// Whether the arming thread has ended, the watch dropped.
    closed: bool,
}

/// The value `mutex` holds, whether or not a thread panicked holding it.
///
/// # Specification
/// trivial.
fn lock(mutex: &Mutex<Followed>) -> MutexGuard<'_, Followed>
{
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Hand each of `named`, followed paths as named, to every connection whose
/// copies name it.
///
/// # Specification
/// trivial.
fn hand_on(
    held: &Followed,
    named: &[&PathBuf],
)
{
    for follower in held.followers.values() {
        let mut changed: Vec<PathBuf> = named
            .iter()
            .filter(|path| follower.named.contains(path.as_path()))
            .map(|path| (*path).clone())
            .collect();
        changed.sort_unstable();
        changed.dedup();
        if !changed.is_empty() {
            follower.changes.hand(changed);
        }
    }
}

/// Hand each followed file `event` names to every connection whose copies
/// name it, and keep the file as it is now.
///
/// # Specification
/// trivial.
fn handed(
    followed: &Mutex<Followed>,
    event: &Event,
)
{
    if !matches!(
        event.kind,
        EventKind::Create(_) | EventKind::Modify(_) | EventKind::Remove(_)
    ) {
        return;
    }
    let mut held = lock(followed);
    for path in &event.paths {
        if let Some(stamp) = held.stamps.get_mut(path) {
            *stamp = Stamp::of(path);
        }
    }
    let named: Vec<&PathBuf> = event
        .paths
        .iter()
        .filter_map(|path| held.resolved.get(path))
        .collect();
    if !named.is_empty() {
        hand_on(&held, &named);
    }
}

/// Read the followed files `reach` names and hand on each that changed since
/// it was last read.
///
/// # Specification
/// trivial.
fn polled(
    held: &mut Followed,
    reach: Reach,
)
{
    let every = match reach {
        Reach::Every => true,
        Reach::Due => held.asked != held.applied,
    };
    let mut changed: Vec<PathBuf> = Vec::new();
    for (real, was) in &mut held.stamps {
        if !every
            && !real
                .parent()
                .is_some_and(|directory| held.refused.contains(directory))
        {
            continue;
        }
        let now = Stamp::of(real);
        if now != *was {
            *was = now;
            if let Some(named) = held.resolved.get(real) {
                changed.push(named.clone());
            }
        }
    }
    if !changed.is_empty() {
        hand_on(held, &changed.iter().collect::<Vec<_>>());
    }
}

/// The arming thread: apply each set of directories asked for to the
/// system's watcher, the latest of those waiting, in one batch; then read
/// the followed files once more and mark the set applied.
///
/// # Specification
/// trivial.
fn arm(
    mut watcher: RecommendedWatcher,
    asked: &mpsc::Receiver<(Request, BTreeSet<PathBuf>)>,
    followed: &Mutex<Followed>,
    wake: &Condvar,
)
{
    let mut armed: BTreeSet<PathBuf> = BTreeSet::new();
    while let Ok(mut latest) = asked.recv() {
        while let Ok(later) = asked.try_recv() {
            latest = later;
        }
        let (number, directories) = latest;
        // The system's watcher answers from the thread that hands each event
        // on, and `handed` takes the followers there: asked while they are
        // held, the two would wait on each other (#1898).
        let mut refused: BTreeSet<PathBuf> = BTreeSet::new();
        let mut paths = watcher.paths_mut();
        for gone in armed.difference(&directories) {
            let _unwatched = paths.remove(gone);
        }
        for added in directories.difference(&armed) {
            if paths.add(added, RecursiveMode::NonRecursive).is_err() {
                let _refused = refused.insert(added.clone());
            }
        }
        let _committed = paths.commit();
        armed = directories.difference(&refused).cloned().collect();
        let mut held = lock(followed);
        // A change made while the registration was pending, after the last
        // poll, is read here: from now on the watcher reports it.
        polled(&mut held, Reach::Every);
        held.refused = refused;
        held.applied = number;
    }
    lock(followed).closed = true;
    wake.notify_all();
}

/// The polling thread: read the followed files every [`POLL`] while the
/// watch polls, and wait otherwise, until the watch is dropped.
///
/// # Specification
/// trivial.
fn poll(
    followed: &Mutex<Followed>,
    wake: &Condvar,
)
{
    loop {
        let held = lock(followed);
        if held.closed {
            return;
        }
        if held.asked == held.applied && held.refused.is_empty() {
            drop(wake.wait(held).unwrap_or_else(PoisonError::into_inner));
            continue;
        }
        drop(held);
        thread::sleep(POLL);
        polled(&mut lock(followed), Reach::Due);
    }
}

/// The hub's watch.
#[derive(Debug)]
pub struct Disk
{
    /// Where the arming thread, which holds the system's watcher, takes each
    /// set of directories asked for, with its number.
    arming: mpsc::Sender<(Request, BTreeSet<PathBuf>)>,
    /// The directories asked for, resolved.
    directories: BTreeSet<PathBuf>,
    /// What the watcher's thread, the arming thread and the polling thread
    /// read.
    followed: Arc<Mutex<Followed>>,
    /// What wakes the polling thread when a registration is asked for or the
    /// watch ends.
    wake: Arc<Condvar>,
}

impl Disk
{
    /// A watch following nothing yet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a watch that serves no connection and watches no directory,
    ///   with its arming thread and its polling thread started; both end once
    ///   the watch is dropped.
    /// - provides: the hub's one watch, shared by its connections.
    /// - fails: when the system's watcher cannot start, or a thread cannot be
    ///   spawned.
    /// - panics: none.
    ///
    /// # Errors
    /// The watcher's error when it cannot start; an I/O error when a thread
    /// cannot be spawned.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hub connection whose client watches nothing
    ///   republishes an open document when a file it imports is rewritten on
    ///   disk, with no notification sent; the watch hands a followed file on
    ///   when it is created, changed or removed, and not when it is only opened
    ///   or closed.
    /// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
    /// - witness: `disk::tests::only_a_write_to_a_followed_file_is_handed_on`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|disk| disk.directories.is_empty()))]
    #[inline]
    pub fn new() -> notify::Result<Self>
    {
        let followed = Arc::new(Mutex::new(Followed::default()));
        let wake = Arc::new(Condvar::new());
        let shared = Arc::clone(&followed);
        let watcher = notify::recommended_watcher(move |event: notify::Result<Event>| {
            if let Ok(event) = event {
                handed(&shared, &event);
            }
        })?;
        let (arming, asked) = mpsc::channel();
        let (armed, woken) = (Arc::clone(&followed), Arc::clone(&wake));
        let _arming = thread::Builder::new()
            .name(String::from("gandr-disk-arm"))
            .spawn(move || arm(watcher, &asked, &armed, &woken))
            .map_err(notify::Error::io)?;
        let (polled, woken) = (Arc::clone(&followed), Arc::clone(&wake));
        let _polling = thread::Builder::new()
            .name(String::from("gandr-disk-poll"))
            .spawn(move || poll(&polled, &woken))
            .map_err(notify::Error::io)?;
        Ok(Self {
            arming,
            directories: BTreeSet::new(),
            followed,
            wake,
        })
    }

    /// Follow `named` for `peer`, handing a change of any of them to
    /// `changes`; with `named` empty, stop serving `peer`. The paths the
    /// watch now reports, when they changed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `peer` is served with exactly `named` when it is not empty,
    ///   and not served otherwise. The directories holding a path any served
    ///   connection follows, as each resolves, are asked of the system's
    ///   watcher, and no others; the arming thread asks it, so the call never
    ///   waits on the registration. Until the watcher holds the latest set
    ///   asked for, every followed file is read every [`POLL`] (50 ms) and
    ///   handed on when its modification time, length or presence differs from
    ///   its last reading, the first taken here; once the watcher holds the
    ///   set, the files are read once more and the poll stops, events alone
    ///   handing changes on. A file in a directory the system refuses to watch
    ///   stays polled; a path that does not resolve goes unnoticed. When what
    ///   `peer` is served with changed, every path a served connection follows
    ///   that resolves, as named; `None` otherwise.
    /// - provides: a connection's resynchronisation after each message it
    ///   handled, and its leaving; the paths whose reads stand without a
    ///   `stat`.
    /// - fails: never; an unwatchable directory is polled.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Self::new`]'s witness; a second set
    ///   replaces the first and an empty one stops serving the connection;
    ///   watches and unwatches made for fifteen seconds, at most five hundred
    ///   pairs, return while a followed file is rewritten without pause; the
    ///   hub's witness run as 64 concurrent processes, whose registrations
    ///   `fseventsd` answers one at a time, is told of the rewrite in each.
    /// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
    /// - witness: `disk::tests::a_connection_follows_exactly_what_it_named_last`
    /// - witness: `disk::tests::a_follow_returns_while_its_files_keep_changing_1898`
    #[spec(captures: following = !named.is_empty(),
        ensures: lock(&self.followed).followers.contains_key(&peer) == following)]
    #[inline]
    pub fn follow(
        &mut self,
        peer: Peer,
        changes: &Changes,
        named: BTreeSet<PathBuf>,
    ) -> Option<BTreeSet<PathBuf>>
    {
        let mut held = lock(&self.followed);
        let unchanged = held
            .followers
            .get(&peer)
            .is_some_and(|follower| follower.named == named);
        if unchanged {
            return None;
        }
        if named.is_empty() {
            let _left = held.followers.remove(&peer);
        }
        else {
            let _replaced = held.followers.insert(peer, Follower {
                changes: changes.clone(),
                named,
            });
        }
        let mut resolved: BTreeMap<PathBuf, PathBuf> = BTreeMap::new();
        let mut directories: BTreeSet<PathBuf> = BTreeSet::new();
        for path in held.followers.values().flat_map(|follower| &follower.named) {
            let Ok(real) = std::fs::canonicalize(path)
            else {
                continue;
            };
            if let Some(directory) = real.parent() {
                let _held = directories.insert(directory.to_path_buf());
            }
            let _named = resolved.insert(real, path.clone());
        }
        let mut stamps = core::mem::take(&mut held.stamps);
        stamps.retain(|real, _| resolved.contains_key(real));
        for real in resolved.keys() {
            let _read = stamps
                .entry(real.clone())
                .or_insert_with(|| Stamp::of(real));
        }
        held.stamps = stamps;
        held.resolved = resolved;
        if directories != self.directories {
            held.asked = Request(held.asked.0.wrapping_add(1));
            // A send fails only once the arming thread has ended, which it
            // does only when this watch is dropped.
            let _sent = self.arming.send((held.asked, directories.clone()));
            self.wake.notify_all();
        }
        let watched = held.resolved.values().cloned().collect();
        drop(held);
        self.directories = directories;
        Some(watched)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::vec::Vec;
    use std::path::PathBuf;
    use std::sync::Mutex;

    use notify::Event;
    use notify::EventKind;
    use notify::event::AccessKind;
    use notify::event::AccessMode;
    use notify::event::CreateKind;
    use notify::event::ModifyKind;
    use notify::event::RemoveKind;

    use super::Disk;
    use super::Followed;
    use super::Follower;
    use super::Reach;
    use super::Request;
    use super::Stamp;
    use super::handed;
    use super::lock;
    use super::polled;
    use crate::quiet::Inbox;
    use crate::quiet::tests::handed as received;
    use crate::server::Peer;

    /// A file a connection follows is handed on when it is created, changed
    /// or removed, and not when it is only opened or closed: a save closes
    /// the file it wrote too, so the write's own event is the one to read.
    #[test]
    fn only_a_write_to_a_followed_file_is_handed_on()
    {
        let inbox = Inbox::default();
        let path = PathBuf::from("/followed/base.gandr");
        let followed = Mutex::new(Followed::default());
        {
            let mut held = lock(&followed);
            let _served = held.followers.insert(Peer::from(1_u64), Follower {
                changes: inbox.changes(),
                named: BTreeSet::from([path.clone()]),
            });
            let _resolved = held.resolved.insert(path.clone(), path.clone());
        }
        let after = |kind: EventKind| {
            handed(&followed, &Event::new(kind).add_path(path.clone()));
            received(&inbox)
        };

        assert!(
            after(EventKind::Access(AccessKind::Close(AccessMode::Write))).is_empty(),
            "closing a written file hands nothing on"
        );
        assert!(
            after(EventKind::Access(AccessKind::Open(AccessMode::Read))).is_empty(),
            "opening a file to read it hands nothing on"
        );
        assert_eq!(
            after(EventKind::Create(CreateKind::File)),
            [Vec::from([path.clone()])],
            "a created file is handed on"
        );
        assert_eq!(
            after(EventKind::Modify(ModifyKind::Any)),
            [Vec::from([path.clone()])],
            "a changed file is handed on"
        );
        assert_eq!(
            after(EventKind::Remove(RemoveKind::File)),
            [Vec::from([path.clone()])],
            "a removed file is handed on"
        );
    }

    /// #3019: a change made while the system's watcher has yet to hold the
    /// directories is handed on by the poll, and once it holds them the poll
    /// reads nothing but a refused directory's files, events handing the rest
    /// on. Each step writes the file a new length, so its reading differs.
    #[test]
    fn a_change_while_the_registration_is_pending_is_handed_on_3019()
    {
        let scratch = std::env::temp_dir().join(format!("gd-{}-3019", std::process::id()));
        drop(std::fs::remove_dir_all(&scratch));
        std::fs::create_dir_all(&scratch).expect("a scratch directory is made");
        let scratch = std::fs::canonicalize(&scratch).expect("the scratch directory resolves");
        let path = scratch.join("base.gandr");
        std::fs::write(&path, "def one = 1 ;\n").expect("the followed file is written");
        let inbox = Inbox::default();
        let mut held = Followed::default();
        let _served = held.followers.insert(Peer::from(1_u64), Follower {
            changes: inbox.changes(),
            named: BTreeSet::from([path.clone()]),
        });
        let _resolved = held.resolved.insert(path.clone(), path.clone());
        let _read = held.stamps.insert(path.clone(), Stamp::of(&path));
        let write = |text: &str| std::fs::write(&path, text).expect("the file is rewritten");

        write("def one = 11 ;\n");
        polled(&mut held, Reach::Due);
        assert!(
            received(&inbox).is_empty(),
            "with the directories held, the poll leaves a change to the events"
        );
        held.asked = Request(1);
        polled(&mut held, Reach::Due);
        assert_eq!(
            received(&inbox),
            [Vec::from([path.clone()])],
            "while a registration is pending, the poll hands the change on"
        );
        polled(&mut held, Reach::Due);
        assert!(
            received(&inbox).is_empty(),
            "a change read once is not handed on again"
        );
        write("def one = 111 ;\n");
        held.applied = Request(1);
        polled(&mut held, Reach::Every);
        assert_eq!(
            received(&inbox),
            [Vec::from([path.clone()])],
            "the last poll, once the set is held, reads every file"
        );
        write("def one = 1111 ;\n");
        let _refused = held.refused.insert(scratch.clone());
        polled(&mut held, Reach::Due);
        assert_eq!(
            received(&inbox),
            [Vec::from([path.clone()])],
            "a file in a refused directory stays polled"
        );
        drop(std::fs::remove_dir_all(&scratch));
    }

    /// A connection follows exactly the paths it named last: a second set
    /// replaces the first, and an empty one stops the watch serving it.
    #[test]
    fn a_connection_follows_exactly_what_it_named_last()
    {
        let inbox = Inbox::default();
        let mut disk = Disk::new().expect("the watcher starts");
        let peer = Peer::from(1_u64);
        let first = BTreeSet::from([PathBuf::from("/followed/first.gandr")]);
        let second = BTreeSet::from([PathBuf::from("/followed/second.gandr")]);
        let following = |disk: &Disk| {
            lock(&disk.followed)
                .followers
                .get(&peer)
                .map(|follower| follower.named.clone())
        };

        disk.follow(peer, &inbox.changes(), first.clone());
        assert_eq!(following(&disk), Some(first), "the first set is followed");
        disk.follow(peer, &inbox.changes(), second.clone());
        assert_eq!(
            following(&disk),
            Some(second),
            "a second set replaces the first"
        );
        disk.follow(peer, &inbox.changes(), BTreeSet::new());
        assert_eq!(
            following(&disk),
            None,
            "an empty set stops serving the connection"
        );
    }

    /// A connection that changes what it follows while the files it follows
    /// keep changing is answered, whatever the watcher's thread is handing
    /// on: the system's watcher replies to a watch or an unwatch from the
    /// thread that hands each event on, so a follow that held the followers
    /// while waiting for that reply waited on a thread waiting for the
    /// followers, and the hub stopped (#1898).
    ///
    /// The witness waits on progress, not on a deadline for the whole run:
    /// it fails only when no follow returns for a stall's length, which the
    /// deadlock does at once and a loaded machine, whose follows are slow but
    /// keep returning, does not (#1921). It follows for a span, at most a
    /// count of pairs, so its cost is the span wherever it runs and a stall
    /// is reported within the ceiling a test runs under: each pair re-arms
    /// the system's watcher twice, 30 to 60 ms a pair on macOS, and the
    /// deadlock came within 307 pairs in each of sixteen trials (#2124).
    #[test]
    fn a_follow_returns_while_its_files_keep_changing_1898()
    {
        use alloc::sync::Arc;
        use core::sync::atomic::AtomicBool;
        use core::sync::atomic::AtomicUsize;
        use core::sync::atomic::Ordering;
        use core::time::Duration;
        use std::sync::mpsc;
        use std::time::Instant;

        /// How long no follow may return before the hub is taken as stopped.
        const STALL: Duration = Duration::from_secs(10);
        /// How long the follows go on.
        const SPAN: Duration = Duration::from_secs(15);
        /// The most pairs of follows made within the span.
        const PAIRS: u32 = 500;
        /// How often the witness reads the follows' progress.
        const LOOK: Duration = Duration::from_secs(1);

        let scratch = std::env::temp_dir().join(format!("gd-{}-1898", std::process::id()));
        drop(std::fs::remove_dir_all(&scratch));
        let (busy, other) = (scratch.join("busy"), scratch.join("other"));
        for directory in [&busy, &other] {
            std::fs::create_dir_all(directory).expect("a scratch directory is made");
        }
        let (written, aside) = (busy.join("base.gandr"), other.join("aside.gandr"));
        for file in [&written, &aside] {
            std::fs::write(file, "def one = 1 ;\n").expect("a followed file is written");
        }
        let stop = Arc::new(AtomicBool::new(false));
        let writer = {
            let (stop, written) = (Arc::clone(&stop), written.clone());
            std::thread::spawn(move || {
                while !stop.load(Ordering::SeqCst) {
                    drop(std::fs::write(&written, "def one = 1 ;\n"));
                }
            })
        };
        let (done, finished) = mpsc::channel();
        let returned = Arc::new(AtomicUsize::new(0));
        let following = {
            let returned = Arc::clone(&returned);
            std::thread::spawn(move || {
                let inbox = Inbox::default();
                let mut disk = Disk::new().expect("the watcher starts");
                let peer = Peer::from(1_u64);
                let one = BTreeSet::from([written.clone()]);
                let both = BTreeSet::from([written, aside]);
                let start = Instant::now();
                for _ in 0_u32 .. PAIRS {
                    if start.elapsed() >= SPAN {
                        break;
                    }
                    disk.follow(peer, &inbox.changes(), both.clone());
                    disk.follow(peer, &inbox.changes(), one.clone());
                    let _before = returned.fetch_add(1, Ordering::SeqCst);
                }
                disk.follow(peer, &inbox.changes(), BTreeSet::new());
                let _sent = done.send(());
            })
        };
        let mut seen = returned.load(Ordering::SeqCst);
        let mut moved = Instant::now();
        let answered = loop {
            match finished.recv_timeout(LOOK) {
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    let now = returned.load(Ordering::SeqCst);
                    if now != seen {
                        seen = now;
                        moved = Instant::now();
                    }
                    else if moved.elapsed() >= STALL {
                        break Err(mpsc::RecvTimeoutError::Timeout);
                    }
                },
                answered @ (Ok(()) | Err(mpsc::RecvTimeoutError::Disconnected)) => break answered,
            }
        };
        stop.store(true, Ordering::SeqCst);
        writer.join().expect("the writer stops");
        drop(std::fs::remove_dir_all(&scratch));
        assert_eq!(
            answered,
            Ok(()),
            "every follow returns while the followed file keeps changing: none returned for \
             {STALL:?} after {seen} pairs"
        );
        following.join().expect("the follower ends");
    }
}
