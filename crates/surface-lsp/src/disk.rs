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
//! [`named_path`]: gandr_surface_dispatcher::named_path

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;

use anodized::spec;
use notify::Event;
use notify::EventKind;
use notify::RecommendedWatcher;
use notify::RecursiveMode;
use notify::Watcher as _;

use crate::quiet::Changes;
use crate::server::Peer;

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

/// What the watcher's thread reads.
#[derive(Debug, Default)]
struct Followed
{
    /// Each connection the watch serves.
    followers: BTreeMap<Peer, Follower>,
    /// Each followed path's resolved form, to the path as named.
    resolved: BTreeMap<PathBuf, PathBuf>,
}

/// The value `mutex` holds, whether or not a thread panicked holding it.
///
/// # Specification
/// trivial.
fn lock(mutex: &Mutex<Followed>) -> MutexGuard<'_, Followed>
{
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Hand each followed file `event` names to every connection whose copies
/// name it.
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
    let held = lock(followed);
    let named: Vec<&PathBuf> = event
        .paths
        .iter()
        .filter_map(|path| held.resolved.get(path))
        .collect();
    if named.is_empty() {
        return;
    }
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

/// The hub's watch.
#[derive(Debug)]
pub struct Disk
{
    /// The system's watcher.
    watcher: RecommendedWatcher,
    /// The directories it watches, resolved.
    directories: BTreeSet<PathBuf>,
    /// What the watcher's thread reads.
    followed: Arc<Mutex<Followed>>,
}

impl Disk
{
    /// A watch following nothing yet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a watch that serves no connection and watches no directory.
    /// - provides: the hub's one watch, shared by its connections.
    /// - fails: when the system's watcher cannot start.
    /// - panics: none.
    ///
    /// # Errors
    /// The watcher's error when it cannot start.
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
        let shared = Arc::clone(&followed);
        let watcher = notify::recommended_watcher(move |event: notify::Result<Event>| {
            if let Ok(event) = event {
                handed(&shared, &event);
            }
        })?;
        Ok(Self {
            watcher,
            directories: BTreeSet::new(),
            followed,
        })
    }

    /// Follow `named` for `peer`, handing a change of any of them to
    /// `changes`; with `named` empty, stop serving `peer`. The paths the
    /// watch now reports, when they changed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `peer` is served with exactly `named` when it is not empty,
    ///   and not served otherwise; the directories holding a path any served
    ///   connection follows, as each resolves, are watched and no others; a
    ///   path that does not resolve, or a directory the system refuses to
    ///   watch, goes unnoticed. When what `peer` is served with changed, every
    ///   path a served connection follows whose directory is watched, as named;
    ///   `None` otherwise. It returns while the followed files change: the
    ///   system's watcher is asked with the followers released.
    /// - provides: a connection's resynchronisation after each message it
    ///   handled, and its leaving; the paths whose reads stand without a
    ///   `stat`.
    /// - fails: never; an unwatchable path goes unnoticed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Self::new`]'s witness; a second set
    ///   replaces the first and an empty one stops serving the connection; five
    ///   hundred watches and unwatches return while a followed file is
    ///   rewritten without pause.
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
        held.resolved = resolved;
        // The system's watcher answers a watch or an unwatch from the thread
        // that hands each event on, and `handed` takes the followers there:
        // asked while they are held, the two would wait on each other (#1898).
        drop(held);
        for gone in self.directories.difference(&directories) {
            let _unwatched = self.watcher.unwatch(gone);
        }
        let mut refused: BTreeSet<PathBuf> = BTreeSet::new();
        for added in directories.difference(&self.directories) {
            if self
                .watcher
                .watch(added, RecursiveMode::NonRecursive)
                .is_err()
            {
                let _refused = refused.insert(added.clone());
            }
        }
        directories.retain(|directory| !refused.contains(directory));
        let watched = lock(&self.followed)
            .resolved
            .iter()
            .filter(|&(real, _)| {
                real.parent()
                    .is_some_and(|directory| directories.contains(directory))
            })
            .map(|(_, named)| named.clone())
            .collect();
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
    use super::handed;
    use super::lock;
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
    #[test]
    fn a_follow_returns_while_its_files_keep_changing_1898()
    {
        use alloc::sync::Arc;
        use core::sync::atomic::AtomicBool;
        use core::sync::atomic::Ordering;
        use core::time::Duration;
        use std::sync::mpsc;

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
        let following = std::thread::spawn(move || {
            let inbox = Inbox::default();
            let mut disk = Disk::new().expect("the watcher starts");
            let peer = Peer::from(1_u64);
            let one = BTreeSet::from([written.clone()]);
            let both = BTreeSet::from([written, aside]);
            for _ in 0_u32 .. 500_u32 {
                disk.follow(peer, &inbox.changes(), both.clone());
                disk.follow(peer, &inbox.changes(), one.clone());
            }
            disk.follow(peer, &inbox.changes(), BTreeSet::new());
            let _sent = done.send(());
        });
        let answered = finished.recv_timeout(Duration::from_secs(10));
        stop.store(true, Ordering::SeqCst);
        writer.join().expect("the writer stops");
        drop(std::fs::remove_dir_all(&scratch));
        assert_eq!(
            answered,
            Ok(()),
            "every follow returns while the followed file keeps changing"
        );
        following.join().expect("the follower ends");
    }
}
