//! The porter: the hub's thread that carries tokens between the host's
//! counter and the build tools' FIFO.
//!
//! The account of the two crossings stands in the documentation of the host's
//! module, under "The porter carries tokens to the build tools".

use alloc::ffi::CString;
use alloc::sync::Arc;
#[cfg(target_os = "linux")]
use core::mem::MaybeUninit;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use std::fs::File;
use std::fs::OpenOptions;
use std::fs::TryLockError;
use std::os::unix::ffi::OsStrExt as _;
#[cfg(target_os = "linux")]
use std::os::unix::io::OwnedFd;
use std::path::Path;
use std::path::PathBuf;
use std::thread::JoinHandle;

use quenchant_shape::shape::Maybe;
#[cfg(target_os = "linux")]
use rustix::fs::inotify;

use super::Class;
use super::Counter;
use super::FIFO;
use super::HUNGRY;
use super::Host;
use super::IDLE;
use super::Left;
use super::PORTER;
use super::STOCKED;
use super::TICK;
use super::left;
use super::wait;
use crate::pool::grant::Counted;
use crate::pool::grant::Fifo;

/// The bytes of one read of the watch: sixteen events of a watch that names no
/// file.
#[cfg(target_os = "linux")]
const EVENTS: usize = 256;

quenchant_shape::reason_enum! {
    /// Why a directory names no FIFO that a porter carries.
    pub mod unported {
        /// The reason a build names no host's FIFO.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No porter holds the porter's lock, or no hub made the file.
            Unheld,
            /// The porter's file does not open, or its lock fails.
            Unopened,
        }
    }
}

/// Whether a take of gandr waits on the counter.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Wanted
{
    /// A batch take or a keystroke's take waits.
    Waits,
    /// No take waits.
    Unwanted,
}

/// The hub's porter: a thread that carries tokens between the host's counter
/// and the build tools' FIFO, so the tools and gandr draw on one bound.
///
/// # Specification
/// - provides: the two crossings, a byte of the FIFO to the counter while a
///   take of gandr waits or past the one spare, and a free token of the counter
///   to an empty FIFO while no take of gandr waits.
/// - panics: none.
/// - executable: none — the FIFO and the counter are the host's, and the tools
///   and the holders change them at once.
///
/// # Adequacy
/// - hypothesis: L3 — a tool takes a spare, the porter stocks the next, and a
///   byte that the tool gives back reaches a take of gandr that waits; a porter
///   that dies gives its tokens back at the reap.
/// - witness: `pool::host::porter::tests::the_porter_carries_a_spare_to_a_tool_and_back_to_a_waiting_take`
/// - witness: `pool::host::porter::tests::a_dead_porter_s_tokens_come_back_at_the_reap`
#[derive(Debug)]
pub struct Porter
{
    /// What the porter's thread shares with the hub.
    carrying: Arc<Carrying>,
    /// The FIFO's path, which the porter takes away when it ends.
    path: PathBuf,
    /// The porter's thread, until the porter ends.
    thread: Option<JoinHandle<()>>,
    /// The thread of the FIFO's watch, until the porter ends.
    #[cfg(target_os = "linux")]
    watcher: Option<JoinHandle<()>>,
}

/// What the porter's thread holds: its slot of the counter, the FIFO's ends,
/// the word that stops it, and the porter's lock.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Carrying
{
    /// The porter's slot of the counter, which counts each token in the FIFO
    /// or in a tool's hands.
    host: Host,
    /// The FIFO's ends.
    fifo: Fifo,
    /// Set when the hub ends the porter.
    stop: AtomicBool,
    /// The watch of each read and each write of the FIFO.
    #[cfg(target_os = "linux")]
    watch: Watch,
    /// The porter's file, which the porter holds an exclusive lock on.
    _lock: File,
}

impl Carrying
{
    /// The counter that the porter's slot belongs to.
    ///
    /// # Specification
    /// trivial.
    fn counter(&self) -> &Counter
    {
        &self.host.mapping.segment().counter
    }
}

/// The porter's watch of the FIFO on Linux: an inotify instance with one
/// watch, which reports each read and each write of the FIFO.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
#[derive(Debug)]
struct Watch
{
    /// The inotify instance.
    instance: OwnedFd,
    /// The FIFO's watch in the instance.
    fifo: i32,
}

#[cfg(target_os = "linux")]
impl Watch
{
    /// Watch each read and each write of the FIFO at `path`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Returns the host's error for an instance or a watch that the host
    /// refuses, and for a path that holds a NUL.
    ///
    /// # Cost
    /// - allocation: the path's C string, setup
    fn on(path: &Path) -> std::io::Result<Self>
    {
        let instance = inotify::init(inotify::CreateFlags::CLOEXEC)?;
        let fifo = inotify::add_watch(
            &instance,
            path,
            inotify::WatchFlags::ACCESS | inotify::WatchFlags::MODIFY,
        )?;
        Ok(Self { instance, fifo })
    }
}

impl Porter
{
    /// Start the porter of the counter in `directory`: take the porter's lock,
    /// make the FIFO, join the counter, and start the thread.
    ///
    /// # Specification
    /// - requires: a hub owns the counter in `directory`.
    /// - ensures: as [`super::HostCounter::carry`].
    /// - fails: as [`super::HostCounter::carry`];
    ///   [`std::io::ErrorKind::NotConnected`] when the porter joins no slot.
    /// - panics: none.
    /// - executable: none — the FIFO and the counter are the host's.
    ///
    /// # Errors
    /// As [`super::HostCounter::carry`], and
    /// [`std::io::ErrorKind::NotConnected`] when the porter joins no slot of
    /// the counter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Porter`].
    /// - witness: `pool::host::porter::tests::the_porter_carries_a_spare_to_a_tool_and_back_to_a_waiting_take`
    ///
    /// # Cost
    /// - allocation: the porter's paths and state and threads, setup
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "io: the porter's thread waits on the counter's futex and reads the build tools' FIFO for the hub's life"
        )
    )]
    pub(super) fn start(directory: &Path) -> std::io::Result<Self>
    {
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(directory.join(PORTER))?;
        match lock.try_lock() {
            Ok(()) => {},
            Err(TryLockError::WouldBlock) => return Err(std::io::ErrorKind::WouldBlock.into()),
            Err(TryLockError::Error(error)) => return Err(error),
        }
        let path = directory.join(FIFO);
        made(&path)?;
        let fifo = Fifo::open(&path)?;
        #[cfg(target_os = "linux")]
        let watched = Watch::on(&path)?;
        let Maybe::Present(host) = Host::join(directory, Class::Batch)
        else {
            return Err(std::io::ErrorKind::NotConnected.into());
        };
        let carrying = Arc::new(Carrying {
            host,
            fifo,
            stop: AtomicBool::new(false),
            #[cfg(target_os = "linux")]
            watch: watched,
            _lock: lock,
        });
        let thread = std::thread::Builder::new()
            .name(String::from("gandr-porter"))
            .spawn({
                let carrying = Arc::clone(&carrying);
                move || carry(&carrying)
            })?;
        let porter = Self {
            carrying,
            path,
            thread: Some(thread),
            #[cfg(target_os = "linux")]
            watcher: None,
        };
        // A watch thread that does not start drops the porter, and the drop
        // stops the porter's thread.
        #[cfg(target_os = "linux")]
        let porter = {
            let mut porter = porter;
            porter.watcher = Some(
                std::thread::Builder::new()
                    .name(String::from("gandr-porter-watch"))
                    .spawn({
                        let carrying = Arc::clone(&porter.carrying);
                        move || watch(&carrying)
                    })?,
            );
            porter
        };
        Ok(porter)
    }

    /// The FIFO that a hub's porter carries in `directory`, while a porter
    /// holds the porter's lock there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the FIFO's path while a porter holds the lock;
    ///   [`unported::Absent::Unheld`] when no hub made the porter's file or its
    ///   lock is free, which the call takes and gives back at once;
    ///   [`unported::Absent::Unopened`] when the file does not open or the lock
    ///   fails. The call makes no file.
    /// - panics: none.
    /// - executable: none — the porter is another process's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a running porter's FIFO is named, and once the porter
    ///   ends none is.
    /// - witness: `pool::host::porter::tests::a_porter_s_fifo_is_named_while_it_carries`
    ///
    /// # Cost
    /// - allocation: the paths of the porter's lock and its FIFO, setup
    #[inline]
    pub fn carried(directory: &Path) -> Maybe<PathBuf, unported::Absent>
    {
        let lock = match File::open(directory.join(PORTER)) {
            Ok(lock) => lock,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                return Maybe::Absent(unported::Absent::Unheld);
            },
            Err(_) => return Maybe::Absent(unported::Absent::Unopened),
        };
        match lock.try_lock() {
            Err(TryLockError::WouldBlock) => Maybe::Present(directory.join(FIFO)),
            // The lock goes back as the file closes.
            Ok(()) => Maybe::Absent(unported::Absent::Unheld),
            Err(TryLockError::Error(_)) => Maybe::Absent(unported::Absent::Unopened),
        }
    }
}

impl Drop for Porter
{
    /// Take the FIFO's path away, stop the thread, and let the slot go: the
    /// thread gives each byte of the FIFO back, and the slot gives back the
    /// tokens in the tools' hands.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the host's error of the FIFO's removal, error path
    #[inline]
    fn drop(&mut self)
    {
        drop(std::fs::remove_file(&self.path));
        self.carrying.stop.store(true, Ordering::Release);
        let counter = self.carrying.counter();
        counter.porter_wakes.raise();
        // The watch's end reaches its thread as `IN_IGNORED`, and the thread
        // returns. A watch that the host already took away leaves nothing to
        // do.
        #[cfg(target_os = "linux")]
        let _removed =
            inotify::remove_watch(&self.carrying.watch.instance, self.carrying.watch.fifo);
        if let Some(thread) = self.thread.take() {
            drop(thread.join());
        }
        #[cfg(target_os = "linux")]
        if let Some(watcher) = self.watcher.take() {
            drop(watcher.join());
        }
    }
}

/// Whether a take of gandr waits on `counter`.
///
/// # Specification
/// trivial.
fn wanted(counter: &Counter) -> Wanted
{
    if counter.waiters.load(Ordering::SeqCst) > 0 || counter.urgent.load(Ordering::SeqCst) > 0 {
        Wanted::Waits
    }
    else {
        Wanted::Unwanted
    }
}

/// The porter's loop: make a crossing while one is due, else wait for a give,
/// a waiting take, a tool's read or write of the FIFO on Linux, or the tick.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the FIFO holds at most one spare while no take of gandr waits,
///   and none while one waits; when the porter stops, each byte of the FIFO is
///   the counter's again.
/// - panics: none.
/// - executable: none — the tools and the holders move tokens at once.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Porter`].
/// - witness: `pool::host::porter::tests::the_porter_carries_a_spare_to_a_tool_and_back_to_a_waiting_take`
fn carry(carrying: &Carrying)
{
    let Carrying {
        ref host,
        ref fifo,
        ref stop,
        ..
    } = *carrying;
    let counter = carrying.counter();
    while !stop.load(Ordering::Acquire) {
        // The porter reads the word before it counts the FIFO: a tool's read
        // or write after the count raises the word past `seen`, and the wait
        // returns at once.
        let seen = counter.porter_wakes.seen();
        let wants = wanted(counter);
        let porting = match fifo.count() {
            // The first crossing, past the one spare: the byte goes to the
            // counter.
            Counted::Past(token) => {
                host.give(token);
                continue;
            },
            // The first crossing: the spare goes to a take of gandr that waits.
            // A tool that takes the spare first leaves the porter nothing.
            Counted::Spare if wants == Wanted::Waits => {
                if let Maybe::Present(token) = fifo.take_now() {
                    host.give(token);
                }
                continue;
            },
            // The spare stays, and the porter's slot counts it all the while,
            // so no token crosses.
            Counted::Spare => STOCKED,
            // The second crossing: a free token of the counter goes to the
            // empty FIFO as its spare, while no take of gandr waits.
            Counted::Empty => match wants {
                Wanted::Unwanted => match host.take_now() {
                    Maybe::Present(token) => {
                        fifo.give(token);
                        STOCKED
                    },
                    Maybe::Absent(_) => HUNGRY,
                },
                Wanted::Waits => HUNGRY,
            },
        };
        counter.porting.store(porting, Ordering::SeqCst);
        // A give or a waiting take before the store found no word to wake the
        // porter by, so the porter reads the counter again before it waits.
        let due = match wanted(counter) {
            Wanted::Unwanted => porting == HUNGRY && left(counter) == Left::Free,
            Wanted::Waits => porting == STOCKED,
        };
        if !due && !stop.load(Ordering::Acquire) {
            wait(&counter.porter_wakes, seen, TICK);
        }
        counter.porting.store(IDLE, Ordering::SeqCst);
    }
    // The hub ends: each byte of the FIFO goes back to the counter.
    loop {
        match fifo.count() {
            Counted::Past(token) => host.give(token),
            Counted::Spare => match fifo.take_now() {
                Maybe::Present(token) => host.give(token),
                Maybe::Absent(_) => return,
            },
            Counted::Empty => return,
        }
    }
}

/// The thread of the porter's watch on Linux: it raises the porter's word at
/// each read and each write of the FIFO, so a tool that takes the spare or
/// gives a byte back wakes the porter.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns once the porter takes the watch away, or once a read of
///   the instance fails; the porter then waits for the tick alone.
/// - panics: none.
/// - executable: none — the tools read and write the FIFO at once.
///
/// # Adequacy
/// - hypothesis: L3 — a tool's read of the spare wakes the porter, which stocks
///   the next spare before the tick.
/// - witness: `pool::host::porter::tests::the_porter_carries_a_spare_to_a_tool_and_back_to_a_waiting_take`
#[cfg(target_os = "linux")]
fn watch(carrying: &Carrying)
{
    let counter = carrying.counter();
    let mut buffer = [MaybeUninit::<u8>::uninit(); EVENTS];
    let mut events = inotify::Reader::new(&carrying.watch.instance, &mut buffer);
    loop {
        match events.next() {
            Ok(event) if event.events().contains(inotify::ReadFlags::IGNORED) => return,
            Ok(_) => counter.porter_wakes.raise(),
            Err(rustix::io::Errno::INTR) => {},
            Err(_) => return,
        }
    }
}

/// Make an empty FIFO at `path`, readable and writable by its owner alone, in
/// place of a file that a hub before left there.
///
/// # Specification
/// trivial.
///
/// # Errors
/// Returns the host's error for a remove or a `mkfifo` that fails, and
/// [`std::io::ErrorKind::InvalidInput`] for a path that holds a NUL.
fn made(path: &Path) -> std::io::Result<()>
{
    match std::fs::remove_file(path) {
        Ok(()) => {},
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {},
        Err(error) => return Err(error),
    }
    let spelled = CString::new(path.as_os_str().as_bytes())
        .map_err(|nul| std::io::Error::new(std::io::ErrorKind::InvalidInput, nul))?;
    // SAFETY: the path is a string that ends in NUL and outlives the call, and
    // the call reads it alone.
    let made = unsafe { libc::mkfifo(spelled.as_ptr(), 0o600) };
    if made == 0 {
        Ok(())
    }
    else {
        Err(std::io::Error::last_os_error())
    }
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;
    use core::sync::atomic::Ordering;
    use core::time::Duration;
    use std::io::BufRead as _;
    use std::io::BufReader;
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;
    use std::process::Stdio;
    use std::time::Instant;

    use quenchant_shape::shape::Maybe;

    use super::super::Class;
    use super::super::FIFO;
    use super::super::FREE;
    use super::super::Host;
    use super::super::HostCounter;
    use super::Porter;
    use crate::pool::grant::Fifo;
    use crate::width::Threads;

    /// The variable that names the directory of a child that runs a porter.
    const CHILD: &str = "GANDR_HOST_PORTER_CHILD";

    /// The free tokens of a counter.
    #[repr(transparent)]
    #[derive(Debug, PartialEq, Eq)]
    struct Free(u64);

    /// The free tokens of `counter`.
    ///
    /// # Specification
    /// trivial.
    fn free(counter: &HostCounter) -> Free
    {
        Free(
            counter
                .mapping
                .segment()
                .counter
                .word
                .load(Ordering::SeqCst)
                & FREE,
        )
    }

    /// Read the free tokens of `counter` until they are `wanted`, for at most
    /// five seconds.
    ///
    /// # Specification
    /// trivial.
    fn settles(
        counter: &HostCounter,
        wanted: &Free,
    ) -> Free
    {
        let since = Instant::now();
        loop {
            let read = free(counter);
            if read == *wanted || since.elapsed() > Duration::from_secs(5) {
                return read;
            }
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    /// `directory`, emptied and made again for one test.
    ///
    /// # Specification
    /// trivial.
    fn fresh(directory: PathBuf) -> PathBuf
    {
        drop(std::fs::remove_dir_all(&directory));
        std::fs::create_dir_all(&directory).unwrap();
        directory
    }

    #[test]
    fn the_porter_carries_a_spare_to_a_tool_and_back_to_a_waiting_take()
    {
        let directory =
            fresh(std::env::temp_dir().join(format!("gandr-porter-carry-{}", std::process::id())));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(2).unwrap())).unwrap();
        let porter = counter.carry().unwrap();
        let tool = Fifo::open(&directory.join(FIFO)).unwrap();
        // The tool waits on the FIFO, as make and cargo do.
        let first = tool.take();
        assert!(
            matches!(first, Maybe::Present(_)),
            "the tool reads the porter's spare"
        );
        let second = tool.take();
        assert!(
            matches!(second, Maybe::Present(_)),
            "the porter stocks the second token once the FIFO is empty"
        );
        assert_eq!(
            settles(&counter, &Free(0)),
            Free(0),
            "the tool holds both tokens of the counter"
        );
        let Maybe::Present(keystroke) = Host::join(&directory, Class::Keystroke)
        else {
            panic!("the process joins the hub's counter");
        };
        let Maybe::Present(token) = first
        else {
            panic!("the tool holds its first token");
        };
        // The tool gives one byte back while no take of gandr waits, so it
        // stands in the FIFO as the spare.
        tool.give(token);
        let since = Instant::now();
        assert!(
            matches!(keystroke.take(), Maybe::Present(_)),
            "the keystroke's waiting take wakes the porter, which carries the spare to it"
        );
        assert!(
            since.elapsed() < Duration::from_secs(1),
            "the spare reaches the waiting take before its first reap"
        );
        drop(porter);
        drop(keystroke);
        assert_eq!(
            settles(&counter, &Free(2)),
            Free(2),
            "the porter's end gives back the token in the tool's hands, and the keystroke's end its own"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn a_porter_s_fifo_is_named_while_it_carries()
    {
        let directory =
            fresh(std::env::temp_dir().join(format!("gandr-porter-named-{}", std::process::id())));
        assert!(
            matches!(Porter::carried(&directory), Maybe::Absent(_)),
            "a directory that no hub used names no FIFO"
        );
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(1).unwrap())).unwrap();
        let porter = counter.carry().unwrap();
        assert!(
            matches!(Porter::carried(&directory), Maybe::Present(ref fifo) if *fifo == directory.join(FIFO)),
            "a running porter's FIFO is named"
        );
        drop(porter);
        assert!(
            matches!(Porter::carried(&directory), Maybe::Absent(_)),
            "once the porter ends, its free lock names no FIFO"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    /// The child's part: start a porter, wait for it to stock its spare, say
    /// so, and wait to die.
    ///
    /// # Specification
    /// trivial.
    fn carry_and_hold(directory: &Path)
    {
        let porter = Porter::start(directory).unwrap();
        let since = Instant::now();
        // The porter's slot holds the spare once the counter's free tokens
        // fall from four to three.
        while porter.carrying.counter().word.load(Ordering::SeqCst) & FREE == 4 {
            assert!(
                since.elapsed() < Duration::from_secs(5),
                "the porter stocks its spare"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
        println!("stocked");
        std::thread::sleep(Duration::from_secs(60));
    }

    #[test]
    fn a_dead_porter_s_tokens_come_back_at_the_reap()
    {
        if let Some(directory) = std::env::var_os(CHILD) {
            carry_and_hold(Path::new(&directory));
            return;
        }
        let directory =
            fresh(std::env::temp_dir().join(format!("gandr-porter-dead-{}", std::process::id())));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(4).unwrap())).unwrap();
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "pool::host::porter::tests::a_dead_porter_s_tokens_come_back_at_the_reap",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, &directory)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        // The harness writes the test's name before the child's own output, on
        // the same line.
        let mut lines = BufReader::new(child.stdout.take().unwrap()).lines();
        assert!(
            lines.any(|line| line.is_ok_and(|line| line.ends_with("stocked"))),
            "the child says that its porter stocked the FIFO"
        );
        assert_eq!(
            free(&counter),
            Free(3),
            "the porter's slot counts the spare in the FIFO"
        );
        child.kill().unwrap();
        child.wait().unwrap();
        counter.reap();
        assert_eq!(
            free(&counter),
            Free(4),
            "the reap gives back the dead porter's spare"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }
}
