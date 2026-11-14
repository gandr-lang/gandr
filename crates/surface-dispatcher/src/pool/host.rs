//! The host's tokens: one atomic counter in a segment that the hub owns.
//!
//! **One counter bounds the host.** The segment is a file in the runtime
//! directory, which each process that takes the host's tokens maps. Its
//! counter holds the free tokens and a generation in one word. A take is one
//! compare-and-swap that lowers the count, and a give is one add. A free take
//! makes no system call.
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
//! **A crash between two steps loses no token.** A holder marks its slot
//! before it moves a token between its slot and the counter, and it clears the
//! mark after. A reaper that finds a dead slot with its mark audits the
//! segment. The audit counts the free tokens and the tokens of each slot,
//! between two reads of the generation that agree and with no slot marked. It
//! then gives back the tokens that the count lacks, or takes off a lent token
//! whose lender died.
//!
//! **The hub owns the segment.** A hub holds a shared lock on the owner's file
//! for its life, and it reaps on its idle tick. A process joins the counter
//! only while a hub holds that lock. With no hub, the process takes its grant
//! from a jobserver, or runs with none. A take that waits a second reaps the
//! segment itself, so a dead holder's tokens come back after a hub dies too.
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
use crate::width::Width;

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

/// The first word of a segment whose counter is set: `gandrtk1`.
const MAGIC: u64 = u64::from_le_bytes(*b"gandrtk1");

/// The slots of a segment: the processes that hold the host's tokens at once.
const SLOTS: usize = 256;

/// One step of the generation: the bits above the free count.
const GENERATION: u64 = 1 << 32;

/// The bits of the free count in the counter's word.
const FREE: u64 = GENERATION - 1;

/// How long a take waits on the futex before it reads the counter again.
///
/// economy: 50 ms. A wake that the futex misses costs at most this long, and
/// a waiter reads the counter twenty times a second.
const WAIT: Duration = Duration::from_millis(50);

/// How long a take waits in all before it reaps the segment itself.
///
/// economy: 1 s. A hub reaps every half second; a waiter reaps only when no
/// hub did, so it adds one scan of the slots each second of its wait.
const STARVED: Duration = Duration::from_secs(1);

/// The tries of an audit before it leaves the segment to the next reap.
const AUDITS: usize = 64;

/// The file of the segment, in the runtime directory.
const SEGMENT: &str = "tokens";

/// The owner's file, which each hub holds a shared lock on.
const OWNER: &str = "tokens.lock";

/// The directory of the slots' files.
const SLOT_FILES: &str = "tokens.d";

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
    /// The takes that wait for a token.
    waiters: AtomicU32,
    /// The count of wakes, which a waiting take waits on.
    wakes: AtomicU32,
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
    /// One while the holder moves a token between the slot and the counter.
    marked: AtomicU32,
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
                }
                segment.counter.waiters.store(0, Ordering::Relaxed);
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
    _owner: File,
}

impl HostCounter
{
    /// The host's counter in `directory`, set to the host's performance cores
    /// when no counter stands there.
    ///
    /// # Specification
    /// - requires: `directory` is the runtime directory, readable by its owner
    ///   alone.
    /// - ensures: as [`HostCounter::with`] at the host's performance cores.
    /// - fails: as [`HostCounter::with`].
    /// - panics: none.
    /// - executable: none — the segment is the host's.
    ///
    /// # Errors
    /// As [`HostCounter::with`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostCounter`].
    /// - witness: `pool::host::tests::a_dead_holder_of_four_tokens_gives_them_back_at_the_reap`
    #[inline]
    pub fn open(directory: &Path) -> std::io::Result<Self>
    {
        Self::with(directory, Width::PerformanceCores.whole())
    }

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
        // The exclusive lock sets the counter once, whichever hub starts
        // first; the shared lock then tells each process that a hub owns it.
        owner.lock()?;
        let mapping = Mapping::opened(&directory.join(SEGMENT), Opening::Set(width));
        owner.unlock()?;
        let mapping = mapping?;
        owner.lock_shared()?;
        let counter = Self {
            mapping,
            slots,
            _owner: owner,
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
    /// The slot's file, which this process holds an exclusive lock on.
    _claim: File,
}

impl Host
{
    /// Join the host's counter in `directory`, while a hub owns it.
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
    #[inline]
    pub fn join(directory: &Path) -> Maybe<Self, unhosted::Absent>
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
                        _claim: file,
                    });
                },
                Err(TryLockError::WouldBlock) => {},
                Err(TryLockError::Error(_)) => return Maybe::Absent(unhosted::Absent::Unopened),
            }
        }
        Maybe::Absent(unhosted::Absent::Full)
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

    /// A token, when one is free, with no wait.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a token that the counter held, now counted in this process's
    ///   slot, or [`untaken::Absent::Busy`] when the counter holds none.
    /// - panics: none.
    /// - executable: none — the counter is the host's, and other processes
    ///   change it at once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Host`].
    /// - witness: `pool::tests::a_hosted_pool_runs_as_many_parts_as_it_holds_tokens`
    #[inline]
    pub fn take_now(&self) -> Maybe<Token, untaken::Absent>
    {
        let counter = &self.mapping.segment().counter;
        let slot = self.slot();
        slot.marked.store(1, Ordering::SeqCst);
        let mut word = counter.word.load(Ordering::Relaxed);
        loop {
            if word & FREE == 0 {
                slot.marked.store(0, Ordering::Release);
                return Maybe::Absent(untaken::Absent::Busy);
            }
            match counter.word.compare_exchange_weak(
                word,
                word.wrapping_sub(1).wrapping_add(GENERATION),
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(now) => word = now,
            }
        }
        slot.held.fetch_add(1, Ordering::Relaxed);
        slot.marked.store(0, Ordering::Release);
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
            let seen = Wakes(counter.wakes.load(Ordering::Acquire));
            counter.waiters.fetch_add(1, Ordering::SeqCst);
            if counter.word.load(Ordering::SeqCst) & FREE == 0 {
                wait(&counter.wakes, seen, WAIT);
            }
            counter.waiters.fetch_sub(1, Ordering::SeqCst);
            if since.elapsed() >= STARVED {
                reap(self.mapping.segment(), &self.slots);
                since = Instant::now();
            }
        }
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
        slot.marked.store(1, Ordering::SeqCst);
        slot.held.fetch_sub(1, Ordering::Relaxed);
        let counter = &self.mapping.segment().counter;
        counter.word.fetch_add(1 + GENERATION, Ordering::SeqCst);
        slot.marked.store(0, Ordering::Release);
        rouse(counter);
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
    }
}

/// Whether a hub holds the owner's lock in `directory`.
///
/// # Specification
/// trivial.
fn owned(directory: &Path) -> Owned
{
    let Ok(owner) = File::open(directory.join(OWNER))
    else {
        return Owned::Unowned;
    };
    // An exclusive lock that this process takes means that no hub holds the
    // shared one; the file's close lets it go.
    match owner.try_lock() {
        Err(TryLockError::WouldBlock) => Owned::Owned,
        Ok(()) | Err(TryLockError::Error(_)) => Owned::Unowned,
    }
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
fn reap(
    segment: &Segment,
    slots: &Path,
)
{
    let mut audit_due = Audit::Whole;
    for (at, slot) in segment.slots.iter().enumerate() {
        if slot.held.load(Ordering::Acquire) == 0_i32 && slot.marked.load(Ordering::Acquire) == 0 {
            continue;
        }
        let Ok(file) = slot_file(slots, Place(at))
        else {
            continue;
        };
        // A lock that the reaper takes means that the holder died: the kernel
        // let its lock go. The file's close lets the reaper's lock go.
        if file.try_lock().is_ok() && reclaim(&segment.counter, slot) == Audit::Due {
            audit_due = Audit::Due;
        }
    }
    if audit_due == Audit::Due {
        audit(segment);
    }
}

/// Give back the tokens of `slot`, whose holder died or ends, and empty it.
///
/// # Specification
/// - requires: the caller holds the slot's lock.
/// - ensures: the slot holds no token and no mark; the tokens it held are free
///   again. [`Audit::Due`] when the slot held a mark or a lent token.
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
    slot.pid.store(0, Ordering::Relaxed);
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

/// Wake one waiter of `counter`, when one waits.
///
/// # Specification
/// trivial.
fn rouse(counter: &Counter)
{
    if counter.waiters.load(Ordering::SeqCst) > 0 {
        counter.wakes.fetch_add(1, Ordering::Release);
        wake(&counter.wakes);
    }
}

/// Count the free tokens and each slot's tokens, and give back what the count
/// lacks against the host's tokens, or take off a surplus.
///
/// # Specification
/// - requires: each dead holder's slot is reclaimed.
/// - ensures: when a count reads two equal words around the slots and no slot
///   marked, the free tokens and the slots' tokens sum to the host's tokens.
///   After [`AUDITS`] counts that no move leaves alone, the counter stays as it
///   was, for the next reap.
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
        let before = segment.counter.word.load(Ordering::SeqCst);
        let mut held = 0_i64;
        let mut quiet = Audit::Whole;
        for slot in &segment.slots {
            if slot.marked.load(Ordering::SeqCst) != 0 {
                quiet = Audit::Due;
                break;
            }
            held = held.saturating_add(i64::from(slot.held.load(Ordering::SeqCst)));
        }
        let after = segment.counter.word.load(Ordering::SeqCst);
        if quiet == Audit::Due || before != after {
            std::thread::yield_now();
            continue;
        }
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

/// Wait on `word` while it holds `seen`, for at most `timeout`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn wait(
    word: &AtomicU32,
    seen: Wakes,
    timeout: Duration,
)
{
    let timeout = rustix::thread::futex::Timespec {
        tv_sec: i64::try_from(timeout.as_secs()).unwrap_or(i64::MAX),
        tv_nsec: i64::from(timeout.subsec_nanos()),
    };
    // A wait that a signal or a changed word ends reads the counter again.
    drop(rustix::thread::futex::wait(
        word,
        rustix::thread::futex::Flags::empty(),
        seen.0,
        Some(&timeout),
    ));
}

/// Wake one waiter on `word`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn wake(word: &AtomicU32)
{
    drop(rustix::thread::futex::wake(
        word,
        rustix::thread::futex::Flags::empty(),
        1,
    ));
}

/// Wait on `word` while it holds `seen`, for at most `timeout`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "macos")]
fn wait(
    word: &AtomicU32,
    seen: Wakes,
    timeout: Duration,
)
{
    let timeout = u64::try_from(timeout.as_nanos()).unwrap_or(u64::MAX);
    // SAFETY: `word` is an aligned atomic of four bytes in a shared map that
    // outlives the call, and the call reads it and writes nothing.
    let _ended = unsafe {
        libc::os_sync_wait_on_address_with_timeout(
            word.as_ptr().cast(),
            u64::from(seen.0),
            size_of::<AtomicU32>(),
            libc::OS_SYNC_WAIT_ON_ADDRESS_SHARED,
            libc::OS_CLOCK_MACH_ABSOLUTE_TIME,
            timeout,
        )
    };
}

/// Wake one waiter on `word`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "macos")]
fn wake(word: &AtomicU32)
{
    // SAFETY: `word` is an aligned atomic of four bytes in a shared map that
    // outlives the call, and the call writes nothing.
    let _woken = unsafe {
        libc::os_sync_wake_by_address_any(
            word.as_ptr().cast(),
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
    _word: &AtomicU32,
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
fn wake(_word: &AtomicU32)
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

    use super::FREE;
    use super::Host;
    use super::HostCounter;
    use super::unhosted;
    use crate::width::Threads;

    /// The variable that names the directory of a child that holds tokens.
    const CHILD: &str = "GANDR_HOST_TOKENS_CHILD";

    /// The free tokens of `counter`.
    fn free(counter: &HostCounter) -> u64
    {
        counter
            .mapping
            .segment()
            .counter
            .word
            .load(Ordering::SeqCst)
            & FREE
    }

    /// A fresh directory for one test.
    fn scratch(name: &str) -> PathBuf
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-host-{name}-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        std::fs::create_dir_all(&directory).unwrap();
        directory
    }

    /// The child's part: join, take four tokens, say so, and wait to die.
    fn hold_four(directory: &Path)
    {
        let Maybe::Present(host) = Host::join(directory)
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
        let directory = scratch("dead");
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
            4,
            "the child holds four of the eight tokens"
        );
        counter.reap();
        assert_eq!(
            free(&counter),
            4,
            "a reap leaves a live holder's tokens alone"
        );
        child.kill().unwrap();
        child.wait().unwrap();
        counter.reap();
        assert_eq!(
            free(&counter),
            8,
            "the reap gives the dead child's four tokens back"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn a_move_cut_off_between_its_steps_loses_no_token()
    {
        let directory = scratch("cut");
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
            4,
            "the audit gives the cut-off take's token back"
        );
        // A party that lent the process's own token and died while it parked.
        slot.held.store(-1, Ordering::SeqCst);
        segment.counter.word.fetch_add(1, Ordering::SeqCst);
        counter.reap();
        assert_eq!(
            free(&counter),
            4,
            "the audit takes the dead lender's token off"
        );
        drop(counter);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn no_process_joins_a_counter_that_no_hub_owns()
    {
        let directory = scratch("unowned");
        let counter =
            HostCounter::with(&directory, Threads::from(NonZeroUsize::new(2).unwrap())).unwrap();
        drop(counter);
        assert!(
            matches!(
                Host::join(&directory),
                Maybe::Absent(unhosted::Absent::Unowned)
            ),
            "a counter whose hub let go of the owner's lock takes no joiner"
        );
        drop(std::fs::remove_dir_all(&directory));
    }
}
