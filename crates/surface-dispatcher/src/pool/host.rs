//! The host's tokens: one atomic counter in a segment that the hub owns.
//!
//! **One counter bounds the host.** The segment is a file in the runtime
//! directory, which each process that takes the host's tokens maps. Its
//! counter holds the free tokens and a generation in one word. A take is one
//! add that lowers the count and raises the generation, and a give is one add.
//! A take that finds no free token adds its token back. A free take makes no
//! system call, and no take retries under contention.
//!
//! **A take that finds no token waits.** It reads the count of wakes, counts
//! itself among the waiters, and reads the counter again. It then waits on the
//! count of wakes with a futex. A give that finds a waiter raises the count of
//! wakes and wakes one waiter. A give that finds no waiter makes no system
//! call.
//!
//! **Each holder has a slot.** A process that joins claims a slot with an
//! exclusive lock on the slot's file. The slot holds the process's pid and the
//! count of tokens that the process holds. The kernel lets the lock go when
//! the process dies. So a reaper that takes the lock knows that the holder is
//! dead, and a pid that another process took since misleads no reaper. The
//! reaper gives the slot's tokens back.
//!
//! **A crash between two steps loses no token.** A holder counts a move in its
//! slot's mark before it moves a token between its slot and the counter, and it
//! takes the move off the mark after. The threads of one process share its
//! slot, so the mark counts each of their moves. A reaper that finds a dead
//! slot with its mark audits the
//! segment. The audit counts the free tokens and the tokens of each slot,
//! between two reads of the generation that agree and with no slot marked. It
//! then gives back the tokens that the count lacks, or takes off a lent token
//! whose lender died.
//!
//! **The hub owns the segment.** A hub holds a shared lock on the owner's file
//! for its life, and it reaps on its idle tick. Each hub of the host holds the
//! same shared lock, so the hubs of two builds or two workspaces share the
//! counter. The first hub sets the counter under an exclusive lock on the
//! setter's file, which a hub holds only while it sets the counter. A process
//! joins the counter only while a hub holds the owner's lock. With no hub, the
//! process takes its grant from a jobserver, or runs with none. A take that
//! waits a second reaps the segment itself, so a dead holder's tokens come
//! back after a hub dies too.
//!
//! **A keystroke goes first.** Each process takes as a keystroke or as a
//! batch. A keystroke's take that finds no token counts itself among the
//! counter's urgent takes while it waits, and a give wakes an urgent take
//! first. A batch take that finds an urgent take refuses once, so the token
//! stays free for the keystroke. The next take of the batch after the refusal
//! takes the token all the same. So a batch waits at most one retry at each
//! boundary of its jobs, and a stream of keystrokes starves no batch.
//!
//! **Each holder of the build tools carries a FIFO of its own.** A process
//! that holds the counter for a build, as `gandr tokens` does for one build
//! command, joins the counter with a slot of its own and makes its FIFO beside
//! the segment, `tokens3.<slot>.fifo`. So the directory holds one FIFO for each
//! slot at most, and a holder makes its FIFO afresh over the one that a dead
//! holder of its slot left. Its porter, a thread of that process, makes
//! two crossings, and nothing else moves a token between that FIFO and the
//! counter. It moves a byte of the FIFO to the counter while a take of gandr
//! waits, or while the FIFO holds more than one byte. It moves a free token of
//! the counter to the FIFO while the FIFO holds no byte and no take of gandr
//! waits. So the FIFO holds at most one spare token, and the porter stocks the
//! next one only when a tool reads the spare: a reader that waits on an empty
//! FIFO raises no event that the porter can read. The holder's slot counts
//! each token in its FIFO or in the hands of its tools. So when the holder
//! ends or dies, the slot gives back each token that its tools kept, and a
//! token that a tool takes with it when the tool dies stays lost for one
//! holder's life at most. A give wakes the porters whose FIFO is empty, and a
//! take of gandr that waits wakes the porters whose FIFO holds a spare. On
//! Linux, an inotify watch of the FIFO wakes its porter at each read and each
//! write of a tool, and `FIONREAD` counts the FIFO's bytes, so the porter
//! reads only a byte that crosses. On macOS, a tool's read or write wakes
//! nothing, so the porter reads the FIFO again at its tick. `FIONREAD` reads a
//! FIFO as empty there, so the porter counts the bytes by one read of two
//! bytes at most, and it writes a lone spare back. Its slot counts the spare
//! all the while, so that write moves no token.
//!
//! **Alternatives.** The jobserver's FIFO costs two system calls for each
//! token, and it keeps no record of the holder of a byte. A pid alone names a
//! holder that the kernel may give to another process before the reap. On
//! Linux, `rustix` waits on a futex with no `unsafe`. The `atomic-wait` crate
//! waits within one process alone, and `libc` needs `unsafe` for the call. On
//! macOS, `libc` binds `os_sync_wait_on_address`, the one wait across
//! processes that the system names. Reversal: a futex across processes in
//! `std`.
//!
//! # References
//!
//! - `vault:01a1d2ce-8890-7cf2-a94b-b73109f5689a` — anchor: the shared pool
//!   page, § pool-tokens: one atomic in shared memory for each host, a futex
//!   when it reads zero, and a slot for each holder that the hub reaps by its
//!   pid.

use core::num::NonZeroUsize;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicI32;
use core::sync::atomic::AtomicU32;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use core::time::Duration;
use std::fs::File;
use std::fs::OpenOptions;
use std::fs::TryLockError;
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;

use memmap2::MmapMut;
use quenchant_shape::shape::Maybe;

use super::grant::Token;
use super::grant::untaken;
use crate::width::Threads;

#[cfg(unix)]
mod porter;

#[cfg(unix)]
pub use self::porter::Porter;
#[cfg(unix)]
pub use self::porter::Reaped;

quenchant_shape::reason_enum! {
    /// Why a process takes no token of the host's counter.
    pub mod unhosted {
        /// The reason the process joins no counter.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No hub holds the owner's lock.
            Unowned,
            /// The segment does not open, or holds no counter.
            Unopened,
            /// Each slot has a live holder.
            Full,
        }
    }
}

/// Whom the takes of a process serve.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Class
{
    /// An edit that a person waits on: its takes go first.
    Keystroke,
    /// A check, a build or a tool: its takes wait behind a keystroke's.
    Batch,
}

/// The first word of a segment whose counter is set: `gandrtk3`.
const MAGIC: u64 = u64::from_le_bytes(*b"gandrtk3");

/// The slots of a segment: the processes that hold the host's tokens at once.
const SLOTS: usize = 256;

/// One step of the generation: the bits above the free count.
const GENERATION: u64 = 1 << 32;

/// The bits of the free count in the counter's word.
const FREE: u64 = GENERATION - 1;

/// The least free count that reads as below zero: a take that found no token
/// lowered the count, and it adds the token back.
const BELOW_ZERO: u64 = 1 << 31;

/// How long a take waits on the futex before it reads the counter again.
///
/// economy: 50 ms. A wake that the futex misses costs at most this long, and
/// a waiter reads the counter twenty times a second. #7543 reaps a dead giver
/// at its death and wakes its waiters, so a take waits with no timeout.
const WAIT: Duration = Duration::from_millis(50);

/// How long a take waits in all before it reaps the segment itself.
///
/// economy: 1 s. A hub reaps every half second; a waiter reaps only when no
/// hub did, so it adds one scan of the slots each second of its wait. #7543
/// gives the waiter the owner's lock when the hub dies, and it reaps then.
const STARVED: Duration = Duration::from_secs(1);

/// The tries of an audit before it leaves the segment to the next reap.
const AUDITS: usize = 64;

/// The file of the segment, in the runtime directory. The name carries the
/// segment's layout, so a build of another layout keeps a counter of its own
/// and never sets this one afresh under its holders.
const SEGMENT: &str = "tokens3";

/// The owner's file, which each hub holds a shared lock on.
const OWNER: &str = "tokens3.lock";

/// The setter's file: a hub holds an exclusive lock on it only while it sets
/// the counter.
const SETTER: &str = "tokens3.set";

/// The directory of the slots' files.
const SLOT_FILES: &str = "tokens3.d";

/// The first part of the name of a holder's FIFO in the runtime directory,
/// `tokens3.<slot>.fifo`. A tool names the FIFO as
/// `--jobserver-auth=fifo:<path>` in `MAKEFLAGS`, and a process of gandr that
/// a holder's FIFO names takes the counter beside it.
const FIFO_STEM: &str = "tokens3.";

/// The last part of the name of a holder's FIFO.
const FIFO_END: &str = ".fifo";

/// How long the porter waits before it reads the FIFO again.
///
/// economy: 10 ms on a host other than Linux. There a tool's read or write of
/// the FIFO wakes no porter, so a tool that took the spare waits at most this
/// long for the next one when no give wakes the porter. An idle porter reads
/// the FIFO, writes its spare back and waits once each tick: three system
/// calls. #7627 wakes the porter on macOS by a kqueue event, and the tick goes.
#[cfg(all(unix, not(target_os = "linux")))]
const TICK: Duration = Duration::from_millis(10);

/// How long the porter waits before it reads the FIFO again.
///
/// economy: as [`WAIT`] on Linux. The porter's watch wakes the porter at each
/// read and each write of the FIFO, and the tick only bounds a wake that the
/// watch misses, as [`WAIT`] bounds one that the futex misses. #7627 raises the
/// porter's word at each wake that the watch could miss, and the tick goes.
#[cfg(target_os = "linux")]
const TICK: Duration = WAIT;

/// A slot's porter word for [`Porting::Idle`].
const IDLE: u32 = 0;

/// A slot's porter word for [`Porting::Hungry`].
const HUNGRY: u32 = 1;

/// A slot's porter word for [`Porting::Stocked`].
const STOCKED: u32 = 2;

/// What wakes a holder's porter while it waits, as its slot records it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Porting
{
    /// The porter waits on no event, or the slot has no porter.
    Idle,
    /// The porter's FIFO holds no byte, so a give wakes the porter.
    Hungry,
    /// The porter's FIFO holds a spare, so a take of gandr that waits wakes
    /// the porter.
    Stocked,
}

/// Whether a file's name is the name of a holder's FIFO.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FifoName
{
    /// `tokens3.<slot>.fifo`.
    Holder,
    /// Any other name.
    Other,
}

/// Whether the file at `path` has the name of a holder's FIFO,
/// `tokens3.<slot>.fifo`.
///
/// # Specification
/// trivial.
pub(super) fn fifo_name(path: &Path) -> FifoName
{
    let held = path
        .file_name()
        .and_then(|name| name.to_str())
        .and_then(|name| name.strip_prefix(FIFO_STEM))
        .and_then(|rest| rest.strip_suffix(FIFO_END))
        .is_some_and(|place| !place.is_empty() && place.bytes().all(|byte| byte.is_ascii_digit()));
    if held {
        FifoName::Holder
    }
    else {
        FifoName::Other
    }
}

/// The directory of the host's runtime files for this user:
/// `$XDG_RUNTIME_DIR/gandr`, or `<temporary directory>/gandr-$USER` without
/// that variable.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn runtime_directory() -> PathBuf
{
    std::env::var_os("XDG_RUNTIME_DIR").map_or_else(
        || {
            let mut name = std::ffi::OsString::from("gandr-");
            name.push(std::env::var_os("USER").unwrap_or_default());
            std::env::temp_dir().join(name)
        },
        |runtime| PathBuf::from(runtime).join("gandr"),
    )
}

/// The segment's head: what an opener reads before it reads the counter.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(C, align(64))]
struct Head
{
    /// [`MAGIC`] once the counter is set.
    magic: AtomicU64,
    /// The host's tokens.
    width: AtomicU32,
}

/// The counter, on a cache line of its own.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(C, align(64))]
struct Counter
{
    /// The free tokens in the low 32 bits, and the generation above them.
    word: AtomicU64,
    /// The batch takes that wait for a token.
    waiters: AtomicU32,
    /// The count of wakes, which a waiting batch take waits on.
    wakes: Eventcount,
    /// The keystroke takes that wait for a token: a batch take that finds one
    /// refuses once.
    urgent: AtomicU32,
    /// The count of wakes, which a waiting keystroke take waits on.
    urgent_wakes: Eventcount,
    /// The porters whose FIFO holds no byte: a give wakes them.
    hungry: AtomicU32,
    /// The porters whose FIFO holds a spare: a take of gandr that waits wakes
    /// them.
    stocked: AtomicU32,
    /// The count of the porters' wakes, which each porter waits on.
    porter_wakes: Eventcount,
}

/// One holder's slot, on a cache line of its own.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(C, align(64))]
struct Slot
{
    /// The holder's pid, for a reader; zero for no holder.
    pid: AtomicU32,
    /// The tokens that the holder holds: below zero while it lends the
    /// process's own token.
    held: AtomicI32,
    /// The holder's moves of a token between the slot and the counter that are
    /// under way, and its moves into or out of the urgent takes.
    marked: AtomicU32,
    /// The holder's keystroke takes that wait, which the counter's urgent
    /// takes count too.
    urging: AtomicU32,
    /// What wakes the holder's porter while it waits: [`IDLE`], [`HUNGRY`] or
    /// [`STOCKED`]. The counter's porters of that word count it too.
    porting: AtomicU32,
}

impl Slot
{
    /// What wakes the holder's porter, as the slot records it.
    ///
    /// # Specification
    /// trivial.
    fn porting(&self) -> Porting
    {
        match self.porting.load(Ordering::SeqCst) {
            HUNGRY => Porting::Hungry,
            STOCKED => Porting::Stocked,
            _ => Porting::Idle,
        }
    }

    /// Record `porting` as what wakes the holder's porter.
    ///
    /// # Specification
    /// trivial.
    fn set_porting(
        &self,
        porting: Porting,
    )
    {
        let word = match porting {
            Porting::Idle => IDLE,
            Porting::Hungry => HUNGRY,
            Porting::Stocked => STOCKED,
        };
        self.porting.store(word, Ordering::SeqCst);
    }
}

/// The segment that the file maps: the head, the counter and the slots.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(C)]
struct Segment
{
    /// The head.
    head: Head,
    /// The counter.
    counter: Counter,
    /// The slots.
    slots: [Slot; SLOTS],
}

/// How a segment opens: set to the host's tokens when no counter stands in
/// it, or joined as it stands.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opening
{
    /// Create the file, and set a counter of these tokens when none stands.
    Set(Threads),
    /// Open the file as it stands, with its counter set.
    Join,
}

/// Whether an audit is due after a reclaim.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Audit
{
    /// The reclaim left the counter whole.
    Whole,
    /// The holder died in the middle of a move, or while it lent a token.
    Due,
}

/// Whether a hub holds the owner's lock.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Owned
{
    /// A hub holds it.
    Owned,
    /// No hub holds it.
    Unowned,
}

/// The place of a slot in the segment.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Place(usize);

/// Whether the counter holds a free token.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Left
{
    /// A token is free.
    Free,
    /// No token is free.
    Spent,
}

/// A count of tokens that goes back to the counter.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Count(u32);

/// The count of wakes that a waiter read before it waits.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Wakes(u32);

/// A count of wakes, which a waiter waits on with a futex.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(transparent)]
struct Eventcount(AtomicU32);

impl Eventcount
{
    /// The count that a waiter reads before it counts itself and waits.
    ///
    /// # Specification
    /// trivial.
    fn seen(&self) -> Wakes
    {
        Wakes(self.0.load(Ordering::Acquire))
    }

    /// Raise the count and wake one waiter.
    ///
    /// # Specification
    /// trivial.
    fn raise(&self)
    {
        self.0.fetch_add(1, Ordering::Release);
        wake(self);
    }
}

/// A segment mapped into this process.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(transparent)]
struct Mapping(MmapMut);

impl Mapping
{
    /// The segment of the file at `path`, opened as `opening` states.
    ///
    /// # Specification
    /// - requires: a caller of [`Opening::Set`] holds the owner's lock alone.
    /// - ensures: a map of a whole segment whose counter is set; an
    ///   [`Opening::Set`] that finds no counter sets one of its tokens, with
    ///   every slot empty.
    /// - fails: the host's error, or [`std::io::ErrorKind::InvalidData`] for a
    ///   file that holds no whole segment, or no counter where it joins.
    /// - panics: none.
    /// - executable: none — the file is the host's, and other processes map it.
    ///
    /// # Errors
    /// Returns the host's error for an open or a map that fails, and
    /// [`std::io::ErrorKind::InvalidData`] for a file that holds no segment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hub sets the counter, and a process joins it.
    /// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
    ///
    /// # Cost
    /// - allocation: the path's C string of the open, setup
    /// - allocation: the host's error of an open, a length or a map, error path
    fn opened(
        path: &Path,
        opening: Opening,
    ) -> std::io::Result<Self>
    {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(matches!(opening, Opening::Set(_)))
            .truncate(false)
            .open(path)?;
        let size = u64::try_from(size_of::<Segment>()).unwrap_or(u64::MAX);
        if file.metadata()?.len() < size {
            match opening {
                Opening::Set(_) => file.set_len(size)?,
                Opening::Join => return Err(std::io::ErrorKind::InvalidData.into()),
            }
        }
        // SAFETY: the file is never cut shorter than a segment, and each access
        // goes through an atomic of `Segment`, so another process that writes
        // the file at once races with no plain read or write here.
        let map = unsafe { MmapMut::map_mut(&file) }?;
        if map.len() < size_of::<Segment>() {
            return Err(std::io::ErrorKind::InvalidData.into());
        }
        let mapping = Self(map);
        let segment = mapping.segment();
        let set = segment.head.magic.load(Ordering::Acquire) == MAGIC;
        match opening {
            Opening::Set(width) if !set => {
                let width = u32::try_from(NonZeroUsize::from(width).get()).unwrap_or(u32::MAX);
                for slot in &segment.slots {
                    slot.pid.store(0, Ordering::Relaxed);
                    slot.held.store(0, Ordering::Relaxed);
                    slot.marked.store(0, Ordering::Relaxed);
                    slot.urging.store(0, Ordering::Relaxed);
                    slot.porting.store(IDLE, Ordering::Relaxed);
                }
                segment.counter.waiters.store(0, Ordering::Relaxed);
                segment.counter.urgent.store(0, Ordering::Relaxed);
                segment.counter.hungry.store(0, Ordering::Relaxed);
                segment.counter.stocked.store(0, Ordering::Relaxed);
                segment.head.width.store(width, Ordering::Relaxed);
                segment
                    .counter
                    .word
                    .store(u64::from(width), Ordering::Relaxed);
                segment.head.magic.store(MAGIC, Ordering::Release);
            },
            Opening::Set(_) => {},
            Opening::Join if set => {},
            Opening::Join => return Err(std::io::ErrorKind::InvalidData.into()),
        }
        Ok(mapping)
    }

    /// The segment that the map holds.
    ///
    /// # Specification
    /// trivial.
    #[expect(
        clippy::cast_ptr_alignment,
        reason = "a map starts on a page, which each alignment of a segment divides"
    )]
    fn segment(&self) -> &Segment
    {
        // SAFETY: `opened` checks that the map holds a whole segment, and a map
        // starts on a page, which each alignment of the segment divides. Each
        // field of a segment is an atomic, which holds a value at each bit
        // pattern and which another thread or process may change. The borrow
        // ends before the map.
        unsafe { &*self.0.as_ptr().cast::<Segment>() }
    }
}

/// The hub's hold on the host's counter: its shared lock on the owner's file,
/// and the segment that it reaps.
///
/// # Specification
/// - provides: the segment's counter, set once to the host's tokens, and the
///   reap of each dead holder's slot.
/// - panics: none.
/// - executable: none — the segment is the host's, and other processes map it.
///
/// # Adequacy
/// - hypothesis: L3 — a holder that dies with four tokens gives them back at
///   the next reap.
/// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
#[derive(Debug)]
pub struct HostCounter
{
    /// The segment.
    mapping: Mapping,
    /// The directory of the slots' files.
    slots: PathBuf,
    /// The owner's file, which this hub holds a shared lock on.
    owner: File,
}

impl Drop for HostCounter
{
    /// Let the owner's lock go before the owner's file closes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        let_go(&self.owner);
    }
}

impl HostCounter
{
    /// The host's counter in `directory`, set to `width` tokens when no
    /// counter stands there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a hold whose shared lock on the owner's file tells each
    ///   process that a hub owns the counter; each dead holder's slot is reaped
    ///   before the call returns.
    /// - fails: the host's error for a file or a lock that fails.
    /// - panics: none.
    /// - executable: none — the segment is the host's.
    ///
    /// # Errors
    /// Returns the host's error for a directory, a file, a lock or a map that
    /// fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostCounter`].
    /// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
    ///
    /// # Cost
    /// - allocation: the paths of the counter's files, setup
    /// - allocation: the host's error of a directory, a file, a lock or a map,
    ///   error path
    #[inline]
    pub fn with(
        directory: &Path,
        width: Threads,
    ) -> std::io::Result<Self>
    {
        let slots = directory.join(SLOT_FILES);
        std::fs::create_dir_all(&slots)?;
        let owner = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(directory.join(OWNER))?;
        let setter = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(directory.join(SETTER))?;
        // The exclusive lock sets the counter once, whichever hub starts
        // first. It is a file apart from the owner's, whose shared lock each
        // running hub holds, so a later hub does not wait on them.
        setter.lock()?;
        let mapping = Mapping::opened(&directory.join(SEGMENT), Opening::Set(width));
        setter.unlock()?;
        let mapping = mapping?;
        owner.lock_shared()?;
        let counter = Self {
            mapping,
            slots,
            owner,
        };
        counter.reap();
        Ok(counter)
    }

    /// Give back the tokens of each holder that died, and audit the counter
    /// when a holder died in the middle of a move.
    ///
    /// # Specification
    /// - ensures: each slot whose holder died holds no token, and its tokens
    ///   are free again.
    /// - panics: none.
    /// - executable: none — the slots' holders are other processes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostCounter`].
    /// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
    /// - witness: `pool::host::tests::a_move_cut_off_between_its_steps_loses_no_token`
    #[inline]
    pub fn reap(&self)
    {
        reap(self.mapping.segment(), &self.slots);
    }
}

/// This process's hold on the host's counter: the segment, and the slot that
/// it claimed.
///
/// # Specification
/// - provides: a take with no wait, a take that waits, and a give, each on the
///   host's counter.
/// - panics: none.
/// - executable: none — the counter is the host's, and other processes share
///   it.
///
/// # Adequacy
/// - hypothesis: L3 — a pool under a counter of one token runs at most two
///   parts at once, and gives the token back.
/// - witness: `pool::tests::a_hosted_pool_runs_as_many_parts_as_it_holds_tokens`
#[derive(Debug)]
pub struct Host
{
    /// The segment.
    mapping: Mapping,
    /// The directory of the slots' files, for a reap of a starved take.
    slots: PathBuf,
    /// The slot that this process claimed.
    place: Place,
    /// Whom this process's takes serve.
    class: Class,
    /// Whether a batch take refused since this process last took a token, so
    /// its next take takes the token all the same.
    deferred: AtomicBool,
    /// The slot's file, which this process holds an exclusive lock on.
    claim: File,
}

impl Host
{
    /// Join the host's counter in `directory` as `class`, while a hub owns it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a hold on a slot that no live process holds; the tokens that
    ///   a dead holder left in the slot are free again.
    /// - fails: [`unhosted::Absent::Unowned`] when no hub holds the owner's
    ///   lock; [`unhosted::Absent::Unopened`] for a segment or a slot's file
    ///   that does not open; [`unhosted::Absent::Full`] when each slot has a
    ///   live holder.
    /// - panics: none.
    /// - executable: none — the hub and the holders are other processes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a process joins while a hub owns the counter, and its
    ///   tokens come back when it dies.
    /// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
    /// - witness: `pool::host::tests::no_process_joins_a_counter_that_no_hub_owns`
    ///
    /// # Cost
    /// - allocation: the paths of the segment and of the slots' files, setup
    /// - allocation: the host's error of a map, an open or a lock, error path
    #[inline]
    pub fn join(
        directory: &Path,
        class: Class,
    ) -> Maybe<Self, unhosted::Absent>
    {
        if owned(directory) == Owned::Unowned {
            return Maybe::Absent(unhosted::Absent::Unowned);
        }
        let Ok(mapping) = Mapping::opened(&directory.join(SEGMENT), Opening::Join)
        else {
            return Maybe::Absent(unhosted::Absent::Unopened);
        };
        let slots = directory.join(SLOT_FILES);
        for (at, slot) in mapping.segment().slots.iter().enumerate() {
            let Ok(file) = slot_file(&slots, Place(at))
            else {
                return Maybe::Absent(unhosted::Absent::Unopened);
            };
            match file.try_lock() {
                Ok(()) => {
                    if reclaim(&mapping.segment().counter, slot) == Audit::Due {
                        audit(mapping.segment());
                    }
                    slot.pid.store(std::process::id(), Ordering::Relaxed);
                    return Maybe::Present(Self {
                        mapping,
                        slots,
                        place: Place(at),
                        class,
                        deferred: AtomicBool::new(false),
                        claim: file,
                    });
                },
                Err(TryLockError::WouldBlock) => {},
                Err(TryLockError::Error(_)) => return Maybe::Absent(unhosted::Absent::Unopened),
            }
        }
        Maybe::Absent(unhosted::Absent::Full)
    }

    /// The host's tokens: the width that the hub set the counter to, which
    /// the host's profile names or the logical count gives.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the width in the segment's head, at least one.
    /// - panics: none.
    /// - executable: none — the segment is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a joiner reads the width that the hub's counter opens
    ///   at.
    /// - witness: `pool::host::tests::a_joiner_reads_the_width_that_the_hub_opens_at_7706`
    #[inline]
    #[must_use]
    pub fn width(&self) -> Threads
    {
        let width = self.mapping.segment().head.width.load(Ordering::Relaxed);
        usize::try_from(width)
            .ok()
            .and_then(NonZeroUsize::new)
            .map_or(Threads::ONE, Threads::from)
    }

    /// This process's slot.
    ///
    /// # Specification
    /// trivial.
    fn slot(&self) -> &Slot
    {
        let slots = &self.mapping.segment().slots;
        // The place came from the slots' own enumeration, so it is in range;
        // the first slot stands for a place that is not, which none is.
        slots.get(self.place.0).unwrap_or(&slots[0])
    }

    /// The path of the FIFO of this process's slot in `directory`,
    /// `tokens3.<slot>.fifo`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the FIFO's path, setup
    #[cfg(unix)]
    pub(super) fn fifo(
        &self,
        directory: &Path,
    ) -> PathBuf
    {
        directory.join(format!("{FIFO_STEM}{}{FIFO_END}", self.place.0))
    }

    /// Count this process's porter among the porters that `porting` wakes, in
    /// the counter and then in the slot, until [`Host::unpost`].
    ///
    /// # Specification
    /// - requires: the slot records [`Porting::Idle`].
    /// - ensures: the counter's porters of `porting` and the slot count the
    ///   porter, under the slot's mark; [`Porting::Idle`] counts nothing.
    /// - panics: none.
    /// - executable: none — the counter is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a porter that dies while it waits leaves no wake to
    ///   the counter after the reap.
    /// - witness: `pool::host::porter::tests::a_dead_porter_s_tokens_come_back_at_the_reap`
    #[cfg(unix)]
    pub(super) fn post(
        &self,
        porting: Porting,
    )
    {
        if porting == Porting::Idle {
            return;
        }
        let counter = &self.mapping.segment().counter;
        let slot = self.slot();
        slot.marked.fetch_add(1, Ordering::SeqCst);
        raise_porters(counter, porting);
        slot.set_porting(porting);
        slot.marked.fetch_sub(1, Ordering::Release);
    }

    /// Take this process's porter off the porters that its slot records, in
    /// the slot and then in the counter.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot records [`Porting::Idle`], and the counter counts
    ///   the porter no more, under the slot's mark.
    /// - panics: none.
    /// - executable: none — the counter is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Host::post`].
    /// - witness: `pool::host::porter::tests::a_dead_porter_s_tokens_come_back_at_the_reap`
    #[cfg(unix)]
    pub(super) fn unpost(&self)
    {
        let counter = &self.mapping.segment().counter;
        let slot = self.slot();
        let porting = slot.porting();
        if porting == Porting::Idle {
            return;
        }
        slot.marked.fetch_add(1, Ordering::SeqCst);
        slot.set_porting(Porting::Idle);
        lower_porters(counter, porting);
        slot.marked.fetch_sub(1, Ordering::Release);
    }

    /// The tokens that this process's slot counts: those in its porter's FIFO
    /// and those in its tools' hands. A slot that lends counts none.
    ///
    /// # Specification
    /// trivial.
    #[cfg(unix)]
    fn held(&self) -> Count
    {
        Count(u32::try_from(self.slot().held.load(Ordering::SeqCst)).unwrap_or(0))
    }

    /// A token, when one is free, with no wait.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a token that the counter held, now counted in this process's
    ///   slot, or [`untaken::Absent::Busy`] when the counter holds none. A
    ///   batch take that finds an urgent take refuses once, and its next take
    ///   after the refusal reads the counter all the same.
    /// - panics: none.
    /// - executable: none — the counter is the host's, and other processes
    ///   change it at once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Host`]; a batch refuses one take for each urgent
    ///   take that it finds, and takes on the next.
    /// - witness: `pool::tests::a_hosted_pool_runs_as_many_parts_as_it_holds_tokens`
    /// - witness: `pool::host::tests::a_batch_take_refuses_once_for_a_waiting_keystroke`
    #[inline]
    pub fn take_now(&self) -> Maybe<Token, untaken::Absent>
    {
        let counter = &self.mapping.segment().counter;
        if self.class == Class::Batch
            && counter.urgent.load(Ordering::SeqCst) > 0
            && !self.deferred.swap(true, Ordering::Relaxed)
        {
            return Maybe::Absent(untaken::Absent::Busy);
        }
        let slot = self.slot();
        slot.marked.fetch_add(1, Ordering::SeqCst);
        // The add raises the generation and lowers the count. On a counter with
        // no free token it borrows from the generation, and the add back gives
        // the token back and raises the generation once.
        let before = counter.word.fetch_add(GENERATION - 1, Ordering::SeqCst) & FREE;
        if before == 0 || before >= BELOW_ZERO {
            let restored = counter.word.fetch_add(1, Ordering::SeqCst).wrapping_add(1) & FREE;
            slot.marked.fetch_sub(1, Ordering::Release);
            // A give between the two adds found the count below one, and a
            // waiter that read it then waits. The add back frees that token, so
            // it wakes the waiter.
            if restored != 0 && restored < BELOW_ZERO {
                rouse(counter);
            }
            return Maybe::Absent(untaken::Absent::Busy);
        }
        slot.held.fetch_add(1, Ordering::Relaxed);
        slot.marked.fetch_sub(1, Ordering::Release);
        if self.deferred.load(Ordering::Relaxed) {
            self.deferred.store(false, Ordering::Relaxed);
        }
        Maybe::Present(Token::COUNTED)
    }

    /// A token, after a wait for one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a token that the counter held, now counted in this process's
    ///   slot. A wait of a second or more reaps the segment, so a dead holder's
    ///   tokens come back with no hub.
    /// - panics: none.
    /// - executable: none — the counter is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a party that parks lends its token and takes one
    ///   again, and the counter holds each token once the fork ends.
    /// - witness: `pool::tests::a_hosted_pool_runs_as_many_parts_as_it_holds_tokens`
    #[inline]
    pub fn take(&self) -> Maybe<Token, untaken::Absent>
    {
        let counter = &self.mapping.segment().counter;
        let mut since = Instant::now();
        loop {
            if let Maybe::Present(token) = self.take_now() {
                return Maybe::Present(token);
            }
            match self.class {
                Class::Keystroke => {
                    let seen = counter.urgent_wakes.seen();
                    let wanting = self.want();
                    if left(counter) == Left::Spent {
                        wait(&counter.urgent_wakes, seen, WAIT);
                    }
                    drop(wanting);
                },
                Class::Batch => {
                    let seen = counter.wakes.seen();
                    counter.waiters.fetch_add(1, Ordering::SeqCst);
                    summon(counter);
                    if left(counter) == Left::Spent {
                        wait(&counter.wakes, seen, WAIT);
                    }
                    counter.waiters.fetch_sub(1, Ordering::SeqCst);
                },
            }
            if since.elapsed() >= STARVED {
                reap(self.mapping.segment(), &self.slots);
                since = Instant::now();
            }
        }
    }

    /// Count a keystroke of this process among the counter's urgent takes
    /// until the hold drops, so a batch take refuses once and a give wakes it
    /// first. A batch's hold counts nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: while the hold stands, the counter's urgent takes and this
    ///   process's slot each count it once; a porter whose FIFO holds a spare
    ///   wakes and carries it to the counter.
    /// - panics: none.
    /// - executable: none — the counter is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a batch take refuses once while a keystroke wants a
    ///   token, and a dead keystroke's want is reaped.
    /// - witness: `pool::host::tests::a_batch_take_refuses_once_for_a_waiting_keystroke`
    #[inline]
    pub fn want(&self) -> Wanting<'_>
    {
        if self.class == Class::Batch {
            return Wanting::NONE;
        }
        let counter = &self.mapping.segment().counter;
        let slot = self.slot();
        // The mark keeps an audit off the two counts while they differ, and a
        // holder that dies between them leaves the audit due.
        slot.marked.fetch_add(1, Ordering::SeqCst);
        counter.urgent.fetch_add(1, Ordering::SeqCst);
        slot.urging.fetch_add(1, Ordering::SeqCst);
        slot.marked.fetch_sub(1, Ordering::Release);
        summon(counter);
        Wanting(Some(self))
    }

    /// Give `token` back to the counter.
    ///
    /// # Specification
    /// - requires: the token came from this counter, or it is the process's own
    ///   token that a party lends while it parks.
    /// - ensures: the counter holds the token again, and one waiter wakes.
    /// - panics: none.
    /// - executable: none — the counter is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Host::take`].
    /// - witness: `pool::tests::a_hosted_pool_runs_as_many_parts_as_it_holds_tokens`
    #[inline]
    pub fn give(
        &self,
        _token: Token,
    )
    {
        let slot = self.slot();
        slot.marked.fetch_add(1, Ordering::SeqCst);
        slot.held.fetch_sub(1, Ordering::Relaxed);
        let counter = &self.mapping.segment().counter;
        counter.word.fetch_add(1 + GENERATION, Ordering::SeqCst);
        slot.marked.fetch_sub(1, Ordering::Release);
        rouse(counter);
    }
}

/// A keystroke's place among the counter's urgent takes, which it leaves when
/// it drops.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(transparent)]
#[must_use = "a dropped hold leaves the urgent takes at once"]
pub struct Wanting<'host>(Option<&'host Host>);

impl Wanting<'_>
{
    /// A hold that counts nothing: a batch's, or a FIFO's.
    pub const NONE: Self = Self(None);
}

impl Drop for Wanting<'_>
{
    /// Leave the counter's urgent takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        let Some(host) = self.0
        else {
            return;
        };
        let counter = &host.mapping.segment().counter;
        let slot = host.slot();
        slot.marked.fetch_add(1, Ordering::SeqCst);
        slot.urging.fetch_sub(1, Ordering::SeqCst);
        counter.urgent.fetch_sub(1, Ordering::SeqCst);
        slot.marked.fetch_sub(1, Ordering::Release);
    }
}

impl Drop for Host
{
    /// Give back what this process still holds, then let the slot go.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        if reclaim(&self.mapping.segment().counter, self.slot()) == Audit::Due {
            audit(self.mapping.segment());
        }
        let_go(&self.claim);
    }
}

/// Whether a hub holds the owner's lock in `directory`.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the path of the owner's file, setup
/// - allocation: the host's error of an open or a lock, error path
fn owned(directory: &Path) -> Owned
{
    let Ok(owner) = File::open(directory.join(OWNER))
    else {
        return Owned::Unowned;
    };
    // An exclusive lock that this process takes means that no hub holds the
    // shared one. The probe lets its lock go before the close.
    match owner.try_lock() {
        Err(TryLockError::WouldBlock) => Owned::Owned,
        Ok(()) => {
            let_go(&owner);
            Owned::Unowned
        },
        Err(TryLockError::Error(_)) => Owned::Unowned,
    }
}

/// Let the lock on `file` go before the file closes.
///
/// A close lets a lock go only when no other descriptor of the open file
/// lives. A child that a spawn forks holds a copy of each descriptor until
/// it execs, so a close in that window keeps the lock past the close. An
/// unlock lets it go at once, whatever copies live.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the host's error of an unlock, error path
fn let_go(file: &File)
{
    // An unlock that fails leaves the lock to the close.
    let _unlocked: std::io::Result<()> = file.unlock();
}

/// The file of the slot at `place`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// Returns the host's error for an open that fails.
fn slot_file(
    slots: &Path,
    place: Place,
) -> std::io::Result<File>
{
    OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(slots.join(place.0.to_string()))
}

/// Give back the tokens of each slot whose holder died, then audit the counter
/// when a holder died in the middle of a move.
///
/// # Specification
/// - ensures: each slot whose lock no live process holds holds no token.
/// - panics: none.
/// - executable: none — the slots' holders are other processes.
///
/// # Adequacy
/// - hypothesis: L3 — as [`HostCounter`].
/// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
///
/// # Cost
/// - allocation: the host's error of a slot's lock, error path
fn reap(
    segment: &Segment,
    slots: &Path,
)
{
    let mut audit_due = Audit::Whole;
    for (at, slot) in segment.slots.iter().enumerate() {
        if slot.held.load(Ordering::Acquire) == 0_i32
            && slot.marked.load(Ordering::Acquire) == 0
            && slot.urging.load(Ordering::Acquire) == 0
            && slot.porting() == Porting::Idle
        {
            continue;
        }
        let Ok(file) = slot_file(slots, Place(at))
        else {
            continue;
        };
        // A lock that the reaper takes means that the holder died: the kernel
        // let its lock go. The reaper lets its own lock go before the close.
        if file.try_lock().is_ok() {
            if reclaim(&segment.counter, slot) == Audit::Due {
                audit_due = Audit::Due;
            }
            let_go(&file);
        }
    }
    if audit_due == Audit::Due {
        audit(segment);
    }
}

/// Give back the tokens of `slot`, whose holder died or ends, take its urgent
/// takes and its porter's wait off the counter, and empty it.
///
/// # Specification
/// - requires: the caller holds the slot's lock.
/// - ensures: the slot holds no token, no urgent take, no porter's wait and no
///   mark; the tokens it held are free again. [`Audit::Due`] when the slot held
///   a mark or a lent token.
/// - panics: none.
/// - executable: none — the counter is the host's.
///
/// # Adequacy
/// - hypothesis: L3 — as [`HostCounter`].
/// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
fn reclaim(
    counter: &Counter,
    slot: &Slot,
) -> Audit
{
    let marked = slot.marked.swap(0, Ordering::SeqCst);
    let held = slot.held.swap(0, Ordering::SeqCst);
    let urging = slot.urging.swap(0, Ordering::SeqCst);
    // No other process writes the slot while the caller holds its lock.
    let porting = slot.porting();
    slot.set_porting(Porting::Idle);
    slot.pid.store(0, Ordering::Relaxed);
    if urging != 0 {
        // The holder counts its want in the counter before its slot, so the
        // counter holds at least the slot's count.
        let _left = counter
            .urgent
            .try_update(Ordering::SeqCst, Ordering::SeqCst, |urgent| {
                Some(urgent.saturating_sub(urging))
            });
    }
    // The holder counts its porter in the counter before its slot, as it
    // counts a want.
    lower_porters(counter, porting);
    let lent = match u32::try_from(held) {
        Ok(0) => Audit::Whole,
        Ok(count) => {
            give_back(counter, Count(count));
            Audit::Whole
        },
        Err(_) => Audit::Due,
    };
    if marked == 0 { lent } else { Audit::Due }
}

/// Give `count` tokens back to `counter`, and wake its waiters.
///
/// # Specification
/// trivial.
fn give_back(
    counter: &Counter,
    count: Count,
)
{
    counter.word.fetch_add(
        u64::from(count.0).wrapping_add(GENERATION),
        Ordering::SeqCst,
    );
    for _ in 0 .. count.0 {
        rouse(counter);
    }
}

/// Wake one waiter of `counter`: an urgent take first, then a batch take, then
/// the porters whose FIFO is empty.
///
/// # Specification
/// trivial.
fn rouse(counter: &Counter)
{
    let word = if counter.urgent.load(Ordering::SeqCst) > 0 {
        &counter.urgent_wakes
    }
    else if counter.waiters.load(Ordering::SeqCst) > 0 {
        &counter.wakes
    }
    else if counter.hungry.load(Ordering::SeqCst) > 0 {
        &counter.porter_wakes
    }
    else {
        return;
    };
    word.raise();
}

/// Wake the porters whose FIFO holds a spare, so one of them carries its spare
/// to a take of gandr that waits.
///
/// # Specification
/// trivial.
fn summon(counter: &Counter)
{
    if counter.stocked.load(Ordering::SeqCst) > 0 {
        counter.porter_wakes.raise();
    }
}

/// Count one porter more among the counter's porters of `porting`;
/// [`Porting::Idle`] counts nothing.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn raise_porters(
    counter: &Counter,
    porting: Porting,
)
{
    let porters = match porting {
        Porting::Idle => return,
        Porting::Hungry => &counter.hungry,
        Porting::Stocked => &counter.stocked,
    };
    porters.fetch_add(1, Ordering::SeqCst);
}

/// Count one porter less among the counter's porters of `porting`, never
/// below zero; [`Porting::Idle`] counts nothing.
///
/// # Specification
/// trivial.
fn lower_porters(
    counter: &Counter,
    porting: Porting,
)
{
    let porters = match porting {
        Porting::Idle => return,
        Porting::Hungry => &counter.hungry,
        Porting::Stocked => &counter.stocked,
    };
    let _left = porters.try_update(Ordering::SeqCst, Ordering::SeqCst, |count| {
        Some(count.saturating_sub(1))
    });
}

/// Whether `counter` holds a free token.
///
/// # Specification
/// trivial.
fn left(counter: &Counter) -> Left
{
    let free = counter.word.load(Ordering::SeqCst) & FREE;
    if free == 0 || free >= BELOW_ZERO {
        Left::Spent
    }
    else {
        Left::Free
    }
}

/// Count the free tokens and each slot's tokens, and give back what the count
/// lacks against the host's tokens, or take off a surplus. Count the urgent
/// takes of the slots, and set the counter's to their sum.
///
/// # Specification
/// - requires: each dead holder's slot is reclaimed.
/// - ensures: when a count reads two equal words around the slots and no slot
///   marked, the free tokens and the slots' tokens sum to the host's tokens,
///   and the counter's urgent takes and porters are the slots'. After
///   [`AUDITS`] counts that no move leaves alone, the counter stays as it was,
///   for the next reap.
/// - panics: none.
/// - executable: none — the holders move tokens at once.
///
/// # Adequacy
/// - hypothesis: L3 — a take cut off between its two steps, and a lent token
///   whose lender died, each leave the counter whole after the reap.
/// - witness: `pool::host::tests::a_move_cut_off_between_its_steps_loses_no_token`
fn audit(segment: &Segment)
{
    let width = i64::from(segment.head.width.load(Ordering::Relaxed));
    for _ in 0 .. AUDITS {
        let urgent = segment.counter.urgent.load(Ordering::SeqCst);
        let hungry = segment.counter.hungry.load(Ordering::SeqCst);
        let stocked = segment.counter.stocked.load(Ordering::SeqCst);
        let before = segment.counter.word.load(Ordering::SeqCst);
        let mut held = 0_i64;
        let mut urging = 0_u32;
        let mut starving = 0_u32;
        let mut stocking = 0_u32;
        let mut quiet = Audit::Whole;
        for slot in &segment.slots {
            if slot.marked.load(Ordering::SeqCst) != 0 {
                quiet = Audit::Due;
                break;
            }
            held = held.saturating_add(i64::from(slot.held.load(Ordering::SeqCst)));
            urging = urging.saturating_add(slot.urging.load(Ordering::SeqCst));
            match slot.porting() {
                Porting::Hungry => starving = starving.saturating_add(1),
                Porting::Stocked => stocking = stocking.saturating_add(1),
                Porting::Idle => {},
            }
        }
        let after = segment.counter.word.load(Ordering::SeqCst);
        if quiet == Audit::Due || before != after {
            std::thread::yield_now();
            continue;
        }
        // A want or a porter that moved since the first read leaves the count
        // to it.
        let _set = segment.counter.urgent.compare_exchange(
            urgent,
            urging,
            Ordering::SeqCst,
            Ordering::Relaxed,
        );
        let _set = segment.counter.hungry.compare_exchange(
            hungry,
            starving,
            Ordering::SeqCst,
            Ordering::Relaxed,
        );
        let _set = segment.counter.stocked.compare_exchange(
            stocked,
            stocking,
            Ordering::SeqCst,
            Ordering::Relaxed,
        );
        let free = i64::try_from(after & FREE).unwrap_or(i64::MAX);
        let lost = width.saturating_sub(free).saturating_sub(held);
        let Ok(next) = u64::try_from(free.saturating_add(lost))
        else {
            return;
        };
        if lost == 0 {
            return;
        }
        let word = (after & !FREE).wrapping_add(GENERATION) | (next & FREE);
        if segment
            .counter
            .word
            .compare_exchange(after, word, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
        {
            if lost > 0 {
                for _ in 0 .. lost {
                    rouse(&segment.counter);
                }
            }
            return;
        }
    }
}

/// Wait on `word`, a count of wakes, while it holds `seen`, for at most
/// `timeout`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn wait(
    word: &Eventcount,
    seen: Wakes,
    timeout: Duration,
)
{
    let timeout = rustix::thread::futex::Timespec {
        tv_sec: i64::try_from(timeout.as_secs()).unwrap_or(i64::MAX),
        tv_nsec: i64::from(timeout.subsec_nanos()),
    };
    // A wait that a signal or a changed word ends reads the counter again.
    let _ended = rustix::thread::futex::wait(
        &word.0,
        rustix::thread::futex::Flags::empty(),
        seen.0,
        Some(&timeout),
    );
}

/// Wake one waiter on `word`, a count of wakes.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn wake(word: &Eventcount)
{
    let _woken = rustix::thread::futex::wake(&word.0, rustix::thread::futex::Flags::empty(), 1);
}

/// Wait on `word`, a count of wakes, while it holds `seen`, for at most
/// `timeout`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "macos")]
fn wait(
    word: &Eventcount,
    seen: Wakes,
    timeout: Duration,
)
{
    let timeout = u64::try_from(timeout.as_nanos()).unwrap_or(u64::MAX);
    // SAFETY: the count of wakes is an aligned atomic of four bytes in a shared
    // map that outlives the call, and the call reads it and writes nothing.
    let _ended = unsafe {
        libc::os_sync_wait_on_address_with_timeout(
            word.0.as_ptr().cast(),
            u64::from(seen.0),
            size_of::<AtomicU32>(),
            libc::OS_SYNC_WAIT_ON_ADDRESS_SHARED,
            libc::OS_CLOCK_MACH_ABSOLUTE_TIME,
            timeout,
        )
    };
}

/// Wake one waiter on `word`, a count of wakes.
///
/// # Specification
/// trivial.
#[cfg(target_os = "macos")]
fn wake(word: &Eventcount)
{
    // SAFETY: the count of wakes is an aligned atomic of four bytes in a shared
    // map that outlives the call, and the call writes nothing.
    let _woken = unsafe {
        libc::os_sync_wake_by_address_any(
            word.0.as_ptr().cast(),
            size_of::<AtomicU32>(),
            libc::OS_SYNC_WAKE_BY_ADDRESS_SHARED,
        )
    };
}

/// Wait for at most a millisecond: a host with no futex across processes
/// reads the counter again after it.
///
/// # Specification
/// trivial.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn wait(
    _word: &Eventcount,
    _seen: Wakes,
    timeout: Duration,
)
{
    std::thread::sleep(timeout.min(Duration::from_millis(1)));
}

/// Wake nothing: a waiter on a host with no futex across processes reads the
/// counter again after its sleep.
///
/// # Specification
/// trivial.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn wake(_word: &Eventcount)
{
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;
    use core::sync::atomic::Ordering;
    use std::io::BufRead as _;
    use std::io::BufReader;
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;
    use std::process::Stdio;

    use quenchant_shape::shape::Maybe;

    use super::Class;
    use super::FREE;
    use super::Host;
    use super::HostCounter;
    use super::unhosted;
    use crate::width::Threads;

    /// The variable that names the directory of a child that holds tokens.
    const CHILD: &str = "GANDR_HOST_TOKENS_CHILD";

    /// The free tokens of a counter.
    #[repr(transparent)]
    #[derive(Debug, PartialEq, Eq)]
    struct Free(u64);

    /// The name of one test's scratch directory.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Scratch(&'static str);

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

    /// A fresh directory for the test that `name` names.
    ///
    /// # Specification
    /// trivial.
    fn scratch(name: Scratch) -> PathBuf
    {
        let Scratch(name) = name;
        let directory =
            std::env::temp_dir().join(format!("gandr-host-{name}-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        std::fs::create_dir_all(&directory).unwrap();
        directory
    }

    /// The child's part: join, take four tokens, say so, and wait to die.
    ///
    /// # Specification
    /// trivial.
    fn hold_four(directory: &Path)
    {
        let Maybe::Present(host) = Host::join(directory, Class::Batch)
        else {
            panic!("the child joins the hub's counter");
        };
        for _ in 0_i32 .. 4_i32 {
            assert!(
                matches!(host.take_now(), Maybe::Present(_)),
                "the child takes a token"
            );
        }
        println!("held");
        std::thread::sleep(core::time::Duration::from_secs(60));
    }

    #[test]
    fn a_dead_holder_of_four_tokens_gives_them_back_at_the_reap()
    {
        if let Some(directory) = std::env::var_os(CHILD) {
            hold_four(Path::new(&directory));
            return;
        }
        let directory = scratch(Scratch("dead"));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(8).unwrap())).unwrap();
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap",
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
            lines.any(|line| line.is_ok_and(|line| line.ends_with("held"))),
            "the child says that it holds its tokens"
        );
        assert_eq!(
            free(&counter),
            Free(4),
            "the child holds four of the eight tokens"
        );
        counter.reap();
        assert_eq!(
            free(&counter),
            Free(4),
            "a reap leaves a live holder's tokens alone"
        );
        child.kill().unwrap();
        child.wait().unwrap();
        counter.reap();
        assert_eq!(
            free(&counter),
            Free(8),
            "the reap gives the dead child's four tokens back"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn a_move_cut_off_between_its_steps_loses_no_token()
    {
        let directory = scratch(Scratch("cut"));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(4).unwrap())).unwrap();
        let segment = counter.mapping.segment();
        let slot = &segment.slots[7];
        // A take that lowered the counter and died before it counted the token
        // in its slot, its mark still set.
        slot.marked.store(1, Ordering::SeqCst);
        segment.counter.word.fetch_sub(1, Ordering::SeqCst);
        counter.reap();
        assert_eq!(
            free(&counter),
            Free(4),
            "the audit gives the cut-off take's token back"
        );
        // A party that lent the process's own token and died while it parked.
        slot.held.store(-1, Ordering::SeqCst);
        segment.counter.word.fetch_add(1, Ordering::SeqCst);
        counter.reap();
        assert_eq!(
            free(&counter),
            Free(4),
            "the audit takes the dead lender's token off"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn a_move_cut_off_beside_a_whole_move_of_its_process_loses_no_token()
    {
        let directory = scratch(Scratch("beside"));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(4).unwrap())).unwrap();
        let Maybe::Present(host) = Host::join(&directory, Class::Batch)
        else {
            panic!("the process joins the hub's counter");
        };
        // One thread's take lowered the counter and stopped before it counted
        // the token in the slot, its mark set.
        host.slot().marked.fetch_add(1, Ordering::SeqCst);
        counter
            .mapping
            .segment()
            .counter
            .word
            .fetch_sub(1, Ordering::SeqCst);
        // A second thread of the process takes a token and gives it back.
        let Maybe::Present(token) = host.take_now()
        else {
            panic!("the second thread takes a token");
        };
        host.give(token);
        // The process ends while the first move stays cut off.
        drop(host);
        assert_eq!(
            free(&counter),
            Free(4),
            "the audit gives the cut-off take's token back"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn no_process_joins_a_counter_that_no_hub_owns()
    {
        let directory = scratch(Scratch("unowned"));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(2).unwrap())).unwrap();
        drop(counter);
        assert!(
            matches!(
                Host::join(&directory, Class::Batch),
                Maybe::Absent(unhosted::Absent::Unowned)
            ),
            "a counter whose hub let go of the owner's lock takes no joiner"
        );
        drop(std::fs::remove_dir_all(&directory));
    }

    /// #7687: a child that a spawn forks holds a copy of each descriptor until
    /// it execs. The copy here stands for that child, and lives past the drop.
    #[test]
    fn a_copy_of_the_owner_s_file_keeps_no_lock_past_the_hub_s_drop_7687()
    {
        let directory = scratch(Scratch("copied"));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(2).unwrap())).unwrap();
        let copy = counter.owner.try_clone().unwrap();
        drop(counter);
        assert!(
            matches!(
                Host::join(&directory, Class::Batch),
                Maybe::Absent(unhosted::Absent::Unowned)
            ),
            "the hub's drop lets the owner's lock go while a copy lives"
        );
        drop(copy);
        drop(std::fs::remove_dir_all(&directory));
    }

    /// #7706: the hub sets the counter to the profile's width, and each joiner
    /// reads that width, not the host's topology.
    #[test]
    fn a_joiner_reads_the_width_that_the_hub_opens_at_7706()
    {
        let directory = scratch(Scratch("width"));
        let width = Threads::from(NonZeroUsize::new(6).unwrap());
        let counter = HostCounter::with(&directory, width).unwrap();
        let Maybe::Present(host) = Host::join(&directory, Class::Batch)
        else {
            panic!("the process joins the hub's counter");
        };
        assert_eq!(host.width(), width, "a joiner reads the hub's width");
        drop(host);
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn a_batch_take_refuses_once_for_a_waiting_keystroke()
    {
        let directory = scratch(Scratch("classes"));
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(1).unwrap())).unwrap();
        let (Maybe::Present(keystroke), Maybe::Present(batch)) = (
            Host::join(&directory, Class::Keystroke),
            Host::join(&directory, Class::Batch),
        )
        else {
            panic!("both processes join the hub's counter");
        };
        let Maybe::Present(token) = batch.take_now()
        else {
            panic!("the batch takes the one token");
        };
        assert!(
            matches!(keystroke.take_now(), Maybe::Absent(_)),
            "the keystroke finds no token"
        );
        let wanting = keystroke.want();
        batch.give(token);
        assert!(
            matches!(batch.take_now(), Maybe::Absent(_)),
            "the batch's next take refuses once while the keystroke waits"
        );
        let Maybe::Present(token) = keystroke.take_now()
        else {
            panic!("the freed token stays for the keystroke");
        };
        keystroke.give(token);
        let Maybe::Present(token) = batch.take_now()
        else {
            panic!("the take after the refusal takes the token all the same");
        };
        batch.give(token);
        assert!(
            matches!(batch.take_now(), Maybe::Absent(_)),
            "the next boundary refuses once again while the keystroke waits"
        );
        let Maybe::Present(token) = batch.take_now()
        else {
            panic!("and the take after it takes the token");
        };
        batch.give(token);
        drop(wanting);
        // A keystroke that dies while it waits leaves its want counted in its
        // slot and in the counter, as its hold never drops.
        keystroke.slot().urging.fetch_add(1, Ordering::SeqCst);
        counter
            .mapping
            .segment()
            .counter
            .urgent
            .fetch_add(1, Ordering::SeqCst);
        drop(keystroke);
        let Maybe::Present(token) = batch.take_now()
        else {
            panic!("the end of the keystroke's process takes its want off the counter");
        };
        batch.give(token);
        drop(batch);
        assert_eq!(free(&counter), Free(1), "the counter holds its token again");
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }
}
