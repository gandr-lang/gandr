//! The porter: the thread of a holder of the build tools, which carries
//! tokens between the host's counter and the holder's own FIFO.
//!
//! The account of the two crossings stands in the documentation of the host's
//! module, under "Each holder of the build tools carries a FIFO of its own".

use alloc::ffi::CString;
use alloc::sync::Arc;
#[cfg(target_os = "linux")]
use core::mem::MaybeUninit;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
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
use super::Host;
use super::Left;
use super::Porting;
use super::TICK;
use super::left;
use super::wait;
use crate::pool::grant::Counted;
use crate::pool::grant::Fifo;

/// The bytes of one read of the watch: sixteen events of a watch that names no
/// file.
#[cfg(target_os = "linux")]
const EVENTS: usize = 256;

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

/// A holder's porter: a thread of the process that holds the counter for a
/// build, which carries tokens between the counter and the process's own FIFO,
/// so the build's tools and gandr draw on one bound.
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
///   byte that the tool gives back reaches a take of gandr that waits; a holder
///   that ends or dies gives back the tokens that its tools kept, and they
///   reach the tool of another holder.
/// - witness: `pool::host::porter::tests::the_porter_carries_a_spare_to_a_tool_and_back_to_a_waiting_take`
/// - witness: `pool::host::porter::tests::a_dead_porter_s_tokens_come_back_at_the_reap`
/// - witness: `pool::host::porter::tests::a_holder_s_end_reaches_the_tool_of_another_holder_7688`
/// - witness: `pool::host::porter::tests::a_holder_s_end_counts_the_token_its_tool_kept_7688`
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

/// The tokens that a holder's tools read from its FIFO and did not write back,
/// which the holder's slot gives back to the counter at the holder's end.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Reaped(u32);

impl core::fmt::Display for Reaped
{
    /// The count, as a decimal number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

impl Reaped
{
    /// No token: each tool wrote back each token that it read.
    pub const NONE: Self = Self(0);
}

/// What the porter's thread holds: its slot of the counter, the FIFO's ends,
/// and the word that stops it.
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
    /// Set when the holder ends the porter.
    stop: AtomicBool,
    /// The watch of each read and each write of the FIFO.
    #[cfg(target_os = "linux")]
    watch: Watch,
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
    /// Hold the counter in `directory` for a build: join the counter with a
    /// slot of this process's own, make this process's FIFO beside the
    /// segment, and start the porter's threads.
    ///
    /// # Specification
    /// - requires: a hub owns the counter in `directory`.
    /// - ensures: a porter with a slot of its own, and an empty FIFO at
    ///   [`Porter::fifo`], which the porter stocks with one spare token. Once
    ///   the porter drops, or its process dies, the slot gives back each token
    ///   in the FIFO or in the hands of its tools.
    /// - fails: the host's error for a FIFO, a watch or a thread that fails,
    ///   and the call leaves no FIFO then; [`std::io::ErrorKind::NotConnected`]
    ///   when the process joins no slot.
    /// - panics: none.
    /// - executable: none — the FIFO and the counter are the host's.
    ///
    /// # Errors
    /// Returns the host's error for a FIFO, a watch or a thread that fails,
    /// and [`std::io::ErrorKind::NotConnected`] when the process joins no slot
    /// of the counter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Porter`].
    /// - witness: `pool::host::porter::tests::the_porter_carries_a_spare_to_a_tool_and_back_to_a_waiting_take`
    /// - witness: `pool::host::porter::tests::a_holder_s_end_reaches_the_tool_of_another_holder_7688`
    ///
    /// # Cost
    /// - allocation: the porter's paths and state and threads, setup
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "io: the porter's thread waits on the counter's futex and reads the build tools' FIFO for the holder's life"
        )
    )]
    #[inline]
    pub fn hold(directory: &Path) -> std::io::Result<Self>
    {
        let Maybe::Present(host) = Host::join(directory, Class::Batch)
        else {
            return Err(std::io::ErrorKind::NotConnected.into());
        };
        let path = host.fifo(directory);
        made(&path)?;
        let carrying = match opened(&path, host) {
            Ok(carrying) => Arc::new(carrying),
            Err(error) => {
                drop(std::fs::remove_file(&path));
                return Err(error);
            },
        };
        let mut porter = Self {
            carrying,
            path,
            thread: None,
            #[cfg(target_os = "linux")]
            watcher: None,
        };
        // A thread that does not start drops the porter, and the drop takes
        // the FIFO away and stops the thread that did start.
        porter.thread = Some(
            std::thread::Builder::new()
                .name(String::from("gandr-porter"))
                .spawn({
                    let carrying = Arc::clone(&porter.carrying);
                    move || carry(&carrying)
                })?,
        );
        #[cfg(target_os = "linux")]
        {
            porter.watcher = Some(
                std::thread::Builder::new()
                    .name(String::from("gandr-porter-watch"))
                    .spawn({
                        let carrying = Arc::clone(&porter.carrying);
                        move || watch(&carrying)
                    })?,
            );
        }
        Ok(porter)
    }

    /// The path of this holder's FIFO, which a build names as
    /// `--jobserver-auth=fifo:<path>` in `MAKEFLAGS`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn fifo(&self) -> &Path
    {
        &self.path
    }

    /// End the hold and count the tokens that the build's tools kept. The
    /// porter stops, gives each byte of its FIFO back to the counter, and
    /// takes the FIFO's path away. Then the slot gives back each token that
    /// the tools read and did not write back.
    ///
    /// # Specification
    /// - ensures: the FIFO's path is gone, and each byte of the FIFO is back in
    ///   the counter. The result counts the tokens that the slot gives back for
    ///   the tools' hands, and it is 0 when each tool wrote its tokens back.
    /// - panics: none.
    /// - executable: none — the FIFO and the counter are the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a token that a tool reads and keeps counts one, and
    ///   the spare in the FIFO counts none.
    /// - witness: `pool::host::porter::tests::a_holder_s_end_counts_the_token_its_tool_kept_7688`
    ///
    /// # Cost
    /// - allocation: the host's error of the FIFO's removal, error path
    #[inline]
    #[must_use]
    pub fn end(mut self) -> Reaped
    {
        self.stop();
        Reaped(self.carrying.host.held().0)
    }

    /// Take the FIFO's path away and stop the threads. The porter's thread
    /// gives each byte of the FIFO back before it returns. A second call does
    /// nothing more.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the host's error of the FIFO's removal, error path
    fn stop(&mut self)
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

/// What a porter's thread holds for the FIFO at `path` and the slot `host`:
/// the FIFO's ends and, on Linux, its watch.
///
/// # Specification
/// trivial.
///
/// # Errors
/// Returns the host's error for a FIFO or a watch that does not open.
///
/// # Cost
/// - allocation: the FIFO's ends and its watch, setup
fn opened(
    path: &Path,
    host: Host,
) -> std::io::Result<Carrying>
{
    Ok(Carrying {
        host,
        fifo: Fifo::open(path)?,
        stop: AtomicBool::new(false),
        #[cfg(target_os = "linux")]
        watch: Watch::on(path)?,
    })
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
        self.stop();
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
            Counted::Spare => Porting::Stocked,
            // The second crossing: a free token of the counter goes to the
            // empty FIFO as its spare, while no take of gandr waits.
            Counted::Empty => match wants {
                Wanted::Unwanted => match host.take_now() {
                    Maybe::Present(token) => {
                        fifo.give(token);
                        Porting::Stocked
                    },
                    Maybe::Absent(_) => Porting::Hungry,
                },
                Wanted::Waits => Porting::Hungry,
            },
        };
        host.post(porting);
        // A give or a waiting take before the store found no word to wake the
        // porter by, so the porter reads the counter again before it waits.
        let due = match wanted(counter) {
            Wanted::Unwanted => porting == Porting::Hungry && left(counter) == Left::Free,
            Wanted::Waits => porting == Porting::Stocked,
        };
        if !due && !stop.load(Ordering::Acquire) {
            wait(&counter.porter_wakes, seen, TICK);
        }
        host.unpost();
    }
    // The holder ends: each byte of the FIFO goes back to the counter.
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
    use super::super::FREE;
    use super::super::Host;
    use super::super::HostCounter;
    use super::Porter;
    use super::Reaped;
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
        let porter = Porter::hold(&directory).unwrap();
        let tool = Fifo::open(porter.fifo()).unwrap();
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
    fn a_holder_s_end_reaches_the_tool_of_another_holder_7688()
    {
        let directory = fresh(
            std::env::temp_dir().join(format!("gandr-porter-holders-{}", std::process::id())),
        );
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(1).unwrap())).unwrap();
        let first = Porter::hold(&directory).unwrap();
        let first_tool = Fifo::open(first.fifo()).unwrap();
        assert!(
            matches!(first_tool.take(), Maybe::Present(_)),
            "the first holder's tool takes the one token, and keeps it"
        );
        let second = Porter::hold(&directory).unwrap();
        assert_ne!(
            first.fifo(),
            second.fifo(),
            "each holder makes a FIFO of its own"
        );
        let second_tool = Fifo::open(second.fifo()).unwrap();
        let (sent, received) = std::sync::mpsc::channel();
        // The second holder's tool waits on its FIFO, as make and cargo do.
        let waiting = std::thread::spawn(move || {
            sent.send(matches!(second_tool.take(), Maybe::Present(_)))
                .unwrap();
        });
        assert!(
            received.recv_timeout(Duration::from_millis(100)).is_err(),
            "no token reaches the second tool while the first tool keeps the one token"
        );
        drop(first);
        assert_eq!(
            received.recv_timeout(Duration::from_secs(5)),
            Ok(true),
            "the first holder's end gives back its tool's token, and the second porter carries it to the second tool"
        );
        waiting.join().unwrap();
        drop(second);
        assert_eq!(
            settles(&counter, &Free(1)),
            Free(1),
            "the second holder's end gives back the token that its tool kept"
        );
        let porters = &counter.mapping.segment().counter;
        assert_eq!(
            (
                porters.hungry.load(Ordering::SeqCst),
                porters.stocked.load(Ordering::SeqCst)
            ),
            (0, 0),
            "no porter stays counted once each holder ends"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn a_holder_s_end_counts_the_token_its_tool_kept_7688()
    {
        let directory =
            fresh(std::env::temp_dir().join(format!("gandr-porter-kept-{}", std::process::id())));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(2).unwrap())).unwrap();
        let porter = Porter::hold(&directory).unwrap();
        let tool = Fifo::open(porter.fifo()).unwrap();
        assert!(
            matches!(tool.take(), Maybe::Present(_)),
            "the tool reads the porter's spare, and keeps it as a rustc does"
        );
        assert_eq!(
            settles(&counter, &Free(0)),
            Free(0),
            "the porter stocks the counter's other token as its next spare"
        );
        assert_eq!(
            porter.end(),
            Reaped(1),
            "the end counts the token in the tool's hands, and not the spare in the FIFO"
        );
        assert_eq!(
            free(&counter),
            Free(2),
            "the end gives back the spare and the token that the tool kept"
        );
        drop(tool);
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
        let porter = Porter::hold(directory).unwrap();
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
        let porters = &counter.mapping.segment().counter;
        assert_eq!(
            (
                porters.hungry.load(Ordering::SeqCst),
                porters.stocked.load(Ordering::SeqCst)
            ),
            (0, 0),
            "the reap takes the dead porter's wait off the counter"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }
}
