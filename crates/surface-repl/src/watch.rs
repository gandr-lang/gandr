//! The terminal face's watch over the files the loop loaded.
//!
//! The watch asks the operating system for the events of each directory
//! holding a loaded file, through `notify`'s recommended watcher, rather than
//! for each file: an editor that saves by writing a new file and renaming it
//! over the old one replaces the file a per-file watch held. An event naming a
//! loaded file hands that file, as `:load` named it, to the face's notice once;
//! the face reads the next line before the same file is noticed again, so the
//! several events one save raises make one notice.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;

use anodized::spec;
use notify::Event;
use notify::EventKind;
use notify::RecommendedWatcher;
use notify::RecursiveMode;
use notify::Watcher;

/// What the watcher's thread reads: the loaded files by the path the system
/// reports for each, and those noticed since the face last read a line.
#[derive(Debug, Default)]
struct Watched
{
    /// Each loaded file's resolved path, to the path `:load` named it by.
    files: BTreeMap<PathBuf, PathBuf>,
    /// The files noticed since the face last read a line, as `:load` named
    /// them.
    noticed: BTreeSet<PathBuf>,
}

/// The value `mutex` holds, whether or not a thread panicked holding it.
///
/// # Specification
/// trivial.
fn lock(mutex: &Mutex<Watched>) -> MutexGuard<'_, Watched>
{
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Each loaded file changed on disk, handed to `notice` once while the face
/// waits for a line.
///
/// # Specification
/// trivial.
fn noticed<Notice>(
    watched: &Mutex<Watched>,
    event: &Event,
    notice: &mut Notice,
) where
    Notice: FnMut(&Path),
{
    if !matches!(
        event.kind,
        EventKind::Create(_) | EventKind::Modify(_) | EventKind::Remove(_)
    ) {
        return;
    }
    let mut held = lock(watched);
    for path in &event.paths {
        let Some(loaded) = held.files.get(path).cloned()
        else {
            continue;
        };
        if held.noticed.insert(loaded.clone()) {
            notice(&loaded);
        }
    }
}

/// A watch over the files a loop loaded, through the watcher `W`, the
/// system's own unless a test stands another in.
#[derive(Debug)]
pub struct DiskWatch<W = RecommendedWatcher>
{
    /// The watcher.
    watcher: W,
    /// The directories it watches, resolved.
    directories: BTreeSet<PathBuf>,
    /// The files it follows, as the loop last named them.
    loaded: Vec<PathBuf>,
    /// What the watcher's thread reads.
    watched: Arc<Mutex<Watched>>,
}

impl DiskWatch
{
    /// A watch following nothing yet, handing each loaded file changed on
    /// disk to `notice`, on the watcher's thread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a watch that follows no file; once [`Self::follow`] names
    ///   files, a creation, change or removal of one of them hands it, as
    ///   named, to `notice` once until the next [`Self::follow`].
    /// - provides: the terminal face's notice of a loaded file changed on disk.
    /// - fails: when the system's watcher cannot start.
    /// - panics: none.
    ///
    /// # Errors
    /// The watcher's error when it cannot start.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the handler it installs is [`noticed`], whose witness
    ///   hands a loaded file rewritten twice once, by the path it was loaded
    ///   by, and again after the next follow.
    /// - witness: `watch::tests::a_loaded_file_rewritten_is_noticed_once_per_line`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|watch|
        watch.loaded.is_empty() && watch.directories.is_empty()))]
    #[inline]
    pub fn new<Notice>(mut notice: Notice) -> notify::Result<Self>
    where
        Notice: FnMut(&Path) + Send + 'static,
    {
        let watched = Arc::new(Mutex::new(Watched::default()));
        let shared = Arc::clone(&watched);
        let watcher = notify::recommended_watcher(move |event: notify::Result<Event>| {
            if let Ok(event) = event {
                noticed(&shared, &event, &mut notice);
            }
        })?;
        Ok(Self {
            watcher,
            directories: BTreeSet::new(),
            loaded: Vec::new(),
            watched,
        })
    }
}

impl<W> DiskWatch<W>
where
    W: Watcher,
{
    /// Follow exactly `loaded`, the files the loop holds, now that the face
    /// read a line.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every file is noticeable again; when `loaded` differs from
    ///   the files last followed, each one that resolves is followed by its
    ///   resolved path, the directories holding them are watched and no other;
    ///   a file that does not resolve, or a directory the system refuses to
    ///   watch, goes unnoticed.
    /// - provides: the face's resynchronisation after each line.
    /// - fails: never; an unwatchable file goes unnoticed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a file followed is noticed once and noticed again
    ///   after the next follow.
    /// - witness: `watch::tests::a_loaded_file_rewritten_is_noticed_once_per_line`
    #[spec(ensures: lock(&self.watched).noticed.is_empty())]
    #[inline]
    pub fn follow<'path, Loaded>(
        &mut self,
        loaded: Loaded,
    ) where
        Loaded: Iterator<Item = &'path Path>,
    {
        let loaded: Vec<PathBuf> = loaded.map(Path::to_path_buf).collect();
        if loaded == self.loaded {
            lock(&self.watched).noticed.clear();
            return;
        }
        let mut files: BTreeMap<PathBuf, PathBuf> = BTreeMap::new();
        let mut directories: BTreeSet<PathBuf> = BTreeSet::new();
        for path in &loaded {
            let Ok(resolved) = std::fs::canonicalize(path)
            else {
                continue;
            };
            if let Some(directory) = resolved.parent() {
                let _held = directories.insert(directory.to_path_buf());
            }
            let _named = files.insert(resolved, path.clone());
        }
        for gone in self.directories.difference(&directories) {
            let _unwatched = self.watcher.unwatch(gone);
        }
        for added in directories.difference(&self.directories) {
            let _watched = self.watcher.watch(added, RecursiveMode::NonRecursive);
        }
        self.directories = directories;
        self.loaded = loaded;
        let mut held = lock(&self.watched);
        held.files = files;
        held.noticed.clear();
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use std::path::Path;
    use std::path::PathBuf;

    use notify::Event;
    use notify::EventKind;
    use notify::NullWatcher;
    use notify::event::DataChange;
    use notify::event::ModifyKind;

    use super::DiskWatch;
    use super::noticed;

    /// The watch is driven by the event the system reports for a rewrite,
    /// handed to [`noticed`] as the system's watcher hands it, rather than by
    /// waiting on that watcher: under a loaded file system its stream starts
    /// seconds late and delivers nothing for longer than any wait a test can
    /// afford, while what is asserted here is which events make a notice
    /// (#1968).
    #[test]
    fn a_loaded_file_rewritten_is_noticed_once_per_line()
    {
        let directory = std::env::temp_dir().join(format!("gandr-watch-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("the directory is made");
        let file = directory.join("loaded.gandr");
        std::fs::write(&file, "def a = 1 ;\n").expect("the file writes");
        let mut watch = DiskWatch {
            watcher: NullWatcher,
            directories: BTreeSet::new(),
            loaded: Vec::new(),
            watched: Arc::default(),
        };
        watch.follow(core::iter::once(file.as_path()));
        let rewritten = Event::new(EventKind::Modify(ModifyKind::Data(DataChange::Content)))
            .add_path(std::fs::canonicalize(&file).expect("the file resolves"));
        let mut notices: Vec<PathBuf> = Vec::new();
        noticed(&watch.watched, &rewritten, &mut |path: &Path| {
            notices.push(path.to_path_buf());
        });
        assert_eq!(
            notices,
            core::slice::from_ref(&file),
            "the rewrite is noticed by the path the file was loaded by"
        );
        noticed(&watch.watched, &rewritten, &mut |path: &Path| {
            notices.push(path.to_path_buf());
        });
        assert_eq!(
            notices,
            core::slice::from_ref(&file),
            "a second rewrite before the next line makes no second notice"
        );
        watch.follow(core::iter::once(file.as_path()));
        noticed(&watch.watched, &rewritten, &mut |path: &Path| {
            notices.push(path.to_path_buf());
        });
        assert_eq!(
            notices,
            [file.clone(), file.clone()],
            "after the next line the file is noticed again"
        );
        drop(std::fs::remove_dir_all(&directory));
    }
}
