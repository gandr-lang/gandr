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
    /// `changes`; with `named` empty, stop serving `peer`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `peer` is served with exactly `named` when it is not empty,
    ///   and not served otherwise; the directories holding a path any served
    ///   connection follows, as each resolves, are watched and no others; a
    ///   path that does not resolve, or a directory the system refuses to
    ///   watch, goes unnoticed.
    /// - provides: a connection's resynchronisation after each message it
    ///   handled, and its leaving.
    /// - fails: never; an unwatchable path goes unnoticed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Self::new`]'s witness; a second set
    ///   replaces the first and an empty one stops serving the connection.
    /// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
    /// - witness: `disk::tests::a_connection_follows_exactly_what_it_named_last`
    #[spec(captures: following = !named.is_empty(),
        ensures: lock(&self.followed).followers.contains_key(&peer) == following)]
    #[inline]
    pub fn follow(
        &mut self,
        peer: Peer,
        changes: &Changes,
        named: BTreeSet<PathBuf>,
    )
    {
        let mut held = lock(&self.followed);
        let unchanged = held
            .followers
            .get(&peer)
            .is_some_and(|follower| follower.named == named);
        if unchanged {
            return;
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
        drop(held);
        for gone in self.directories.difference(&directories) {
            let _unwatched = self.watcher.unwatch(gone);
        }
        for added in directories.difference(&self.directories) {
            let _watched = self.watcher.watch(added, RecursiveMode::NonRecursive);
        }
        self.directories = directories;
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
}
