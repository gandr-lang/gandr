//! The regions of a run that grow: one memory bound over them, where the
//! bound comes from, the address space each region reserves for it, and the
//! report a run gives when it stops there.
//!
//! The heap and the window region of a run grow with its input. The bound
//! holds their sum, so a run heavy in windows and a run heavy in objects share
//! one number. Each region reserves address space for the whole bound, up to
//! its share of the process's address space, and commits it in chunks of
//! [`CHUNK`]. The stencils compare each allocation against the committed end.
//! Past that end the cold branch commits the next chunks, and it refuses a
//! commit that takes the sum past the bound. The kernel gives a page its
//! memory when the run first writes it.
//!
//! The address space is a second account beside the bound. Each thread that
//! runs a program keeps a set of regions, so a process holds many sets at
//! once. A host with a small address space cannot give each set the whole
//! bound twice. So the regions of a process reserve together at most a
//! quarter of its address space, the least of `RLIMIT_AS` and the host's user
//! space. Each region asks the least of the bound and its share, the quarter
//! divided by twice the host's width. The rest of the space stays for the
//! executable, its libraries, the allocator and the thread stacks.
//!
//! The bound is a policy of the invocation. The driver binds it once with
//! [`bind`], from `--memory`, before the first run. Without a binding, the
//! first run reads the memory that the host makes available, once for each
//! process ([`Memory::host`]). Every run of the process reads one bound with
//! [`bound`], as every run reads one native policy.
//!
//! # Boundaries
//!
//! - **One run, one sum.** Each run commits within the bound on its own, so the
//!   regions of concurrent runs can pass the bound together. One account for
//!   the runs of one invocation removes this ceiling (#6457).
//! - **The frame region stays fixed.** It keeps its own bound and its own exit,
//!   outside the sum.
//! - **A region can stop at its share.** A run whose region passes its share
//!   stops at the reservation, and the stop names it. A share that the account
//!   or the host cannot give halves, down to one chunk.
//!
//! # References
//!
//! - `vault:01a178aa-608d-75d0-8f71-e6fe4289f327` — lineage: the compiled
//!   runtime's representation question (§ runtime-question-what-runtime-means):
//!   the compiled code compares each allocation against the extent that the
//!   record gives.
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: the
//!   regions are the run's LAM (§ 4), and the bound is a parameter of the
//!   regions that changes no judgement of the model.

use alloc::string::ToString as _;
use core::fmt;
use core::fmt::Write as _;
use core::num::NonZeroUsize;
use core::str::FromStr;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::sync::OnceLock;

use gandr_runtime_stencils::CHUNK;
use gandr_runtime_stencils::Word;
use gandr_runtime_stencils::Words;

/// The bytes of one word.
const WORD: u64 = 8;

/// The units a size takes, smallest first, each with its bytes.
const UNITS: [(&str, u64); 5] = [
    ("B", 1),
    ("KiB", 1 << 10),
    ("MiB", 1 << 20),
    ("GiB", 1 << 30),
    ("TiB", 1 << 40),
];

/// The bound on a host that reports no memory: 4 GiB. A web host reads its
/// memory with the web targets' runtime (#4881).
const UNREAD: Bytes = Bytes(1 << 32);

/// The invocation's bound, bound once.
static BOUND: OnceLock<Memory> = OnceLock::new();

/// A size in bytes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bytes(u64);

impl Bytes
{
    /// The bytes that `words` hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of_words(words: Words) -> Self
    {
        Self(
            u64::try_from(words.0)
                .unwrap_or(u64::MAX)
                .saturating_mul(WORD),
        )
    }

    /// The whole words that these bytes hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn words(self) -> Words
    {
        Words(usize::try_from(self.0.checked_div(WORD).unwrap_or(0)).unwrap_or(usize::MAX))
    }

    /// The bytes from `base` to `end`, two addresses of one region.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    fn between(
        base: *mut Word,
        end: *mut Word,
    ) -> Self
    {
        Self(u64::try_from(end.addr().saturating_sub(base.addr())).unwrap_or(u64::MAX))
    }

    /// The size as a count of its largest unit that divides it: `2 GiB`,
    /// `512 MiB`, or bytes as `1 000 001 B`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn spelled(self) -> Spelled
    {
        Spelled(self)
    }
}

impl From<u64> for Bytes
{
    /// This many bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: u64) -> Self
    {
        Self(bytes)
    }
}

impl From<Bytes> for u64
{
    /// The count of bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Bytes) -> Self
    {
        bytes.0
    }
}

impl fmt::Display for Bytes
{
    /// The count, its digits in groups of three: `2 147 483 648`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a count of one, three, four and ten digits groups
    ///   from the right; a group from the left changes each.
    /// - witness: `regions::tests::a_count_groups_its_digits_by_three`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&Grouped(self.0), f)
    }
}

/// A size as its largest unit that divides it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spelled(Bytes);

impl fmt::Display for Spelled
{
    /// The count of the unit, grouped, then the unit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sizes of whole GiB, whole MiB and odd bytes spell in
    ///   their largest unit, and each spelling reads back as its size.
    /// - witness: `regions::tests::a_size_reads_back_as_it_spells`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let bytes = self.0.0;
        let (unit, size) = UNITS
            .iter()
            .rev()
            .find(|&&(_, size)| bytes.is_multiple_of(size))
            .copied()
            .unwrap_or(("B", 1));
        fmt::Display::fmt(&Grouped(bytes.checked_div(size).unwrap_or(bytes)), f)?;
        write!(f, " {unit}")
    }
}

/// Why a text names no size.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unsized
{
    /// The text opens with no digit.
    Digits,
    /// The unit after the digits is none of `B`, `KiB`, `MiB`, `GiB` and
    /// `TiB`.
    Unit,
    /// The size passes 2⁶⁴ bytes.
    Overflow,
    /// The size is zero, which holds no word.
    Zero,
}

impl fmt::Display for Unsized
{
    /// Why the text names no size, in a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Digits => "a size opens with its digits, as `8GiB` does",
            Self::Unit => "a size's unit is `B`, `KiB`, `MiB`, `GiB` or `TiB`",
            Self::Overflow => "the size passes 2⁶⁴ bytes",
            Self::Zero => "a memory bound of zero bytes holds no word",
        })
    }
}

impl core::error::Error for Unsized
{
}

impl FromStr for Bytes
{
    type Err = Unsized;

    /// The size that `text` names: digits, then a unit, `8GiB` or `8 GiB`;
    /// digits alone are bytes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The [`Unsized`] that names why the text names no size.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each unit, a size with a space and one without, bare
    ///   bytes, an unknown unit, no digits, an overflow and zero each read as
    ///   their size or their refusal.
    /// - witness: `regions::tests::a_size_reads_its_units_and_refuses_the_rest`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Unsized>
    {
        let split = text
            .find(|character: char| !character.is_ascii_digit())
            .unwrap_or(text.len());
        let (digits, unit) = text.split_at(split);
        let count: u64 = match digits.parse() {
            Ok(count) => count,
            Err(_) if digits.is_empty() => return Err(Unsized::Digits),
            Err(_) => return Err(Unsized::Overflow),
        };
        let unit = unit.trim_start();
        let size = if unit.is_empty() {
            1
        }
        else {
            UNITS
                .iter()
                .find(|&&(name, _)| name == unit)
                .map(|&(_, size)| size)
                .ok_or(Unsized::Unit)?
        };
        match count.checked_mul(size) {
            Some(0) => Err(Unsized::Zero),
            Some(bytes) => Ok(Self(bytes)),
            None => Err(Unsized::Overflow),
        }
    }
}

/// Where a run's memory bound comes from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Origin
{
    /// The invocation's `--memory`.
    Flag,
    /// The memory that the host makes available at start: the least of
    /// `MemAvailable`, the `memory.max` of the process's cgroup and
    /// `RLIMIT_AS`.
    Available,
    /// Half of the host's physical memory, on a host that reports no
    /// available memory.
    Physical,
    /// The bound of a host that reports no memory at all.
    Unread,
}

/// The memory bound of the runs of one invocation, and its origin.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Memory
{
    /// The bound.
    bytes: Bytes,
    /// Where it comes from.
    origin: Origin,
}

/// One reading of the host: the three figures that the available memory is
/// the least of, each read one time.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Readings
{
    /// The host's `MemAvailable`.
    available: Option<Bytes>,
    /// The `memory.max` of the process's cgroup.
    cgroup: Option<Bytes>,
    /// The process's `RLIMIT_AS`.
    address_space: Option<Bytes>,
}

impl Readings
{
    /// Read the three figures of the host now.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn now() -> Self
    {
        Self {
            available: available(),
            cgroup: cgroup(),
            address_space: address_space(),
        }
    }
}

impl Memory
{
    /// The bound that the invocation's `--memory` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flag(bytes: Bytes) -> Self
    {
        Self {
            bytes,
            origin: Origin::Flag,
        }
    }

    /// The bound that the host gives now: the bound of one reading of the
    /// host, by [`Memory::of`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn host() -> Self
    {
        Self::of(Readings::now())
    }

    /// The bound that `readings` give: the least of its three figures, else
    /// half of the host's physical memory, else 4 GiB.
    ///
    /// # Specification
    /// - ensures: the origin names which of the three the readings gave.
    /// - executable: none — the fallback reads the host's physical memory.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — on a Linux host the bound is at most the
    ///   `MemAvailable` of its readings and its origin is the available memory;
    ///   a bound that skips the least of the three passes it.
    /// - witness: `regions::tests::the_host_bound_is_at_most_its_available_memory_6649`
    #[inline]
    #[must_use]
    fn of(readings: Readings) -> Self
    {
        let available = [readings.available, readings.cgroup, readings.address_space]
            .into_iter()
            .flatten()
            .min();
        if let Some(bytes) = available {
            return Self {
                bytes,
                origin: Origin::Available,
            };
        }
        physical().map_or(
            Self {
                bytes: UNREAD,
                origin: Origin::Unread,
            },
            |bytes| Self {
                bytes: Bytes(bytes.0.checked_div(2).unwrap_or(0)),
                origin: Origin::Physical,
            },
        )
    }

    /// The bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bytes(self) -> Bytes
    {
        self.bytes
    }

    /// Where the bound comes from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(self) -> Origin
    {
        self.origin
    }
}

impl fmt::Display for Memory
{
    /// The bound with its origin: `--memory 2 GiB`, or the host's memory
    /// with its count of bytes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each origin renders apart from the others and names
    ///   the bound's size.
    /// - witness: `regions::tests::each_origin_names_itself_and_its_size`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.origin {
            Origin::Flag => write!(f, "--memory {}", self.bytes.spelled()),
            Origin::Available => write!(f, "the host's available memory, {} bytes", self.bytes),
            Origin::Physical => {
                write!(
                    f,
                    "half of the host's physical memory, {} bytes",
                    self.bytes
                )
            },
            Origin::Unread => write!(
                f,
                "the bound of a host that reports no memory, {} bytes",
                self.bytes
            ),
        }
    }
}

/// Bind the invocation's memory bound, once, before its first run.
///
/// # Specification
/// - ensures: every later [`bound`] reads `memory`.
/// - executable: none — the binding is the process's.
///
/// # Adequacy
/// - hypothesis: L3 — a first binding and a later one: the first holds for
///   every read, and the later one is refused with the bound in force.
/// - witness: `regions::tests::the_first_binding_holds_and_a_later_one_is_refused`
///
/// # Errors
/// The bound already in force, when an earlier binding or a run fixed it.
#[inline]
pub fn bind(memory: Memory) -> Result<(), Memory>
{
    BOUND.set(memory).map_err(|_bound| bound())
}

/// The memory bound that every run of the process takes: the bound that
/// [`bind`] gave, else the host's, read once.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn bound() -> Memory
{
    *BOUND.get_or_init(Memory::host)
}

/// The region that asked for the chunk a run could not commit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Region
{
    /// The heap.
    Heap,
    /// The window region.
    Windows,
}

impl fmt::Display for Region
{
    /// The region's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Heap => "the heap",
            Self::Windows => "the window region",
        })
    }
}

/// What a region found short of the chunk it asked for.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Short
{
    /// The bound: the regions hold it whole.
    Bound,
    /// The region's reservation: the host gave no more address space, or
    /// the account gave no more of its share.
    Reservation
    {
        /// The bytes that the region reserved.
        reserved: Bytes,
        /// The process's account of address space at the stop.
        standing: Standing,
    },
}

/// The process's account of address space when a run stops at a
/// reservation.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Standing
{
    /// The account of the space that the probe read.
    Bounded
    {
        /// The most that one region asks.
        share: Bytes,
        /// What the budget holds beyond the live reservations.
        left: Bytes,
        /// The space that the probe read.
        space: Bytes,
    },
    /// A host that maps nothing reports no space.
    Unread,
}

/// The process's account of address space now, as a stop reports it.
///
/// # Specification
/// trivial.
#[must_use]
pub(crate) fn standing() -> Standing
{
    account().standing()
}

/// The code-word jumps a run spent.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Step(u64);

impl From<usize> for Step
{
    /// This many jumps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(jumps: usize) -> Self
    {
        Self(u64::try_from(jumps).unwrap_or(u64::MAX))
    }
}

/// A run's stop at its memory: what each region held, at which step, and
/// which region asked for the chunk that did not fit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Held
{
    /// The region that asked.
    pub asked: Region,
    /// What it found short.
    pub short: Short,
    /// The heap's committed bytes.
    pub heap: Bytes,
    /// The window region's committed bytes.
    pub windows: Bytes,
    /// The jumps the run spent.
    pub step: Step,
    /// The bound.
    pub bound: Memory,
}

impl fmt::Display for Held
{
    /// The stop as the report states it: the sum, the step, each region,
    /// the region that asked, the bound with its origin, and the remedy; a
    /// stop at a reservation names the reservation, the share, the account's
    /// remainder and the space beside the bound.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stop at the bound names both regions, the region
    ///   that asked, the origin and the remedy, and a stop at a reservation
    ///   names the reservation, the share, the remainder, the space and the
    ///   bound; a region named for the other, or a figure of the account named
    ///   for another, changes them.
    /// - witness: `regions::tests::a_stop_names_its_regions_its_origin_and_its_remedy`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let sum = Bytes(self.heap.0.saturating_add(self.windows.0));
        write!(
            f,
            "the run held {sum} bytes across its regions at step {}: the window region {}, the \
             heap {}; {} asked for one more chunk past ",
            Bytes(self.step.0),
            self.windows,
            self.heap,
            self.asked
        )?;
        match self.short {
            Short::Bound => write!(f, "{}; raise --memory", self.bound),
            Short::Reservation {
                reserved,
                standing: Standing::Bounded { share, left, space },
            } => write!(
                f,
                "the {reserved} bytes of address space that it reserved, its share {share} with \
                 {left} left of a quarter of the process's {space} bytes of address space, \
                 within {}",
                self.bound
            ),
            Short::Reservation {
                reserved,
                standing: Standing::Unread,
            } => write!(
                f,
                "the {reserved} bytes of address space that the host reserved for it, which \
                 reports no address space, within {}",
                self.bound
            ),
        }
    }
}

/// The part of a process's address space that the regions of its runs
/// reserve together: one quarter. The rest stays for the executable, its
/// libraries, the allocator and the thread stacks.
const BUDGET_PART: u64 = 4;

/// The process's account of the address space that its regions reserve,
/// read once.
static ACCOUNT: OnceLock<Account> = OnceLock::new();

/// The exponent of the first size that the probe of a process's address
/// space asks: 2⁴⁷ bytes, the user space of a 4-level x86-64 host or a
/// 48-bit arm64 host.
const PROBE_TOP: u32 = 47;

/// The address space of a process.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Space
{
    /// The host grants the process one mapping of this many bytes.
    Bounded(Bytes),
    /// The host maps nothing, so it reports no space.
    Unread,
}

impl Space
{
    /// The space that the host grants the process now: the largest power of
    /// two, from 2⁴⁷ bytes down, that one probe mapping takes. The answer
    /// holds `RLIMIT_AS`, the paging mode and the host's policy together.
    ///
    /// # Specification
    /// - ensures: the space is the largest power of two at or below 2⁴⁷ bytes
    ///   that the host grants as one mapping, or no space when it grants none;
    ///   the process holds no probe mapping after the call.
    /// - executable: none — the host decides what it maps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the host is the oracle: it maps the space again as
    ///   one probe, and it refuses twice the space unless the space is 2⁴⁷
    ///   bytes; a probe that skips a size or keeps its mapping changes one.
    /// - witness: `regions::tests::the_space_is_the_largest_probe_that_the_host_grants_6877`
    #[cfg(unix)]
    fn host() -> Self
    {
        (0 ..= PROBE_TOP)
            .rev()
            .filter_map(|power| 1_u64.checked_shl(power))
            .map(Bytes)
            .find(|&bytes| probe(bytes) == Probe::Granted)
            .map_or(Self::Unread, Self::Bounded)
    }

    /// The space of a host with no mapping: none, so each region asks the
    /// whole bound.
    ///
    /// # Specification
    /// trivial.
    #[cfg(not(unix))]
    const fn host() -> Self
    {
        Self::Unread
    }
}

/// The threads that a host runs at once: the width of the pool that takes
/// region sets.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Width(NonZeroUsize);

impl Width
{
    /// The host's width, or one thread when the host reports none.
    ///
    /// # Specification
    /// trivial.
    fn host() -> Self
    {
        Self(std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN))
    }
}

/// What the host answers one probe mapping.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Probe
{
    /// The host mapped the probe.
    Granted,
    /// The host refused it.
    Refused,
}

/// Map `bytes` of inaccessible address space with no commit charge, and
/// unmap it at once.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn probe(bytes: Bytes) -> Probe
{
    let Ok(length) = usize::try_from(bytes.0)
    else {
        return Probe::Refused;
    };
    #[cfg(target_os = "linux")]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE;
    #[cfg(not(target_os = "linux"))]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
    // SAFETY: an anonymous inaccessible mapping at an address the kernel
    // picks touches no memory the process holds.
    let base = unsafe { libc::mmap(core::ptr::null_mut(), length, libc::PROT_NONE, flags, -1, 0) };
    if base == libc::MAP_FAILED {
        return Probe::Refused;
    }
    // SAFETY: the mapping is the probe's own, and nothing reads it.
    let _unmapped = unsafe { libc::munmap(base, length) };
    Probe::Granted
}

/// The address space that the regions of one process reserve together.
///
/// # Specification
/// trivial.
#[derive(Debug)]
enum Account
{
    /// A process whose space the probe read.
    Bounded
    {
        /// The space that the probe read.
        space: Bytes,
        /// The bytes that the live reservations may hold together.
        budget: Bytes,
        /// The words that one region asks at most.
        share: Words,
        /// The bytes that the live reservations hold.
        held: AtomicU64,
    },
    /// A process whose space is unread: each region asks the whole bound.
    Unbounded,
}

impl Account
{
    /// The account of a process with `space` on a host `width` threads wide.
    ///
    /// # Specification
    /// - ensures: a bounded space gives a budget of a quarter of it and a share
    ///   of the budget divided by twice `width`, never below one chunk; an
    ///   unread space bounds nothing.
    /// - executable: none — unwitnessable provenance: the space and the width
    ///   are the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a space of 64 GiB on 16 threads gives a budget of 16
    ///   GiB and a share of 512 MiB, and a space too small for a chunk a share
    ///   still gives one chunk; a budget or a share divided otherwise changes
    ///   one of them.
    /// - witness: `regions::tests::each_region_of_a_small_space_asks_its_share_6877`
    fn of(
        space: Space,
        width: Width,
    ) -> Self
    {
        match space {
            Space::Unread => Self::Unbounded,
            Space::Bounded(space) => {
                let budget = Bytes(space.0.checked_div(BUDGET_PART).unwrap_or(0));
                let regions = u64::try_from(width.0.get())
                    .unwrap_or(u64::MAX)
                    .saturating_mul(2);
                let share = Bytes(budget.0.checked_div(regions).unwrap_or(0)).words();
                Self::Bounded {
                    space,
                    budget,
                    share: Words(share.0.max(CHUNK.0)),
                    held: AtomicU64::new(0),
                }
            },
        }
    }

    /// Debit what a region that asks `words` may reserve: the least of
    /// `words` and the share, halved until the budget holds it, never below
    /// one chunk.
    ///
    /// # Specification
    /// - ensures: the grant is at most `words` and the share, or one chunk; the
    ///   account holds it until [`Self::refund`] gives it back.
    /// - executable: none — unwitnessable provenance: the account is shared by
    ///   every thread of the process, so another debit can move it between a
    ///   call and a check.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sets of a host twice as wide as the budget plans
    ///   for: the planned sets take their share, the later ones fit what the
    ///   budget holds or take one chunk, and a refund gives the share back; a
    ///   grant past the budget or a refund that keeps a byte changes them.
    /// - witness: `regions::tests::each_region_of_a_small_space_asks_its_share_6877`
    fn grant(
        &self,
        words: Words,
    ) -> Words
    {
        match *self {
            Self::Unbounded => words,
            Self::Bounded {
                budget,
                share,
                ref held,
                ..
            } => {
                let asked = Words(words.0.min(share.0));
                let mut now = held.load(Ordering::Relaxed);
                loop {
                    let left = Bytes(budget.0.saturating_sub(now)).words();
                    let granted = fitted(asked, left);
                    let after = now.saturating_add(Bytes::of_words(granted).0);
                    match held.compare_exchange_weak(
                        now,
                        after,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return granted,
                        Err(seen) => now = seen,
                    }
                }
            },
        }
    }

    /// Credit `words` that a reservation gives back.
    ///
    /// # Specification
    /// trivial.
    fn refund(
        &self,
        words: Words,
    )
    {
        match *self {
            Self::Unbounded => {},
            Self::Bounded { ref held, .. } => {
                let bytes = Bytes::of_words(words).0;
                // The update never declines, so it always succeeds.
                let _updated = held.try_update(Ordering::Relaxed, Ordering::Relaxed, |now| {
                    Some(now.saturating_sub(bytes))
                });
            },
        }
    }

    /// The account as a stop at a reservation reports it: the share, what
    /// the budget holds beyond the live reservations, and the space.
    ///
    /// # Specification
    /// trivial.
    fn standing(&self) -> Standing
    {
        match *self {
            Self::Unbounded => Standing::Unread,
            Self::Bounded {
                space,
                budget,
                share,
                ref held,
            } => Standing::Bounded {
                share: Bytes::of_words(share),
                left: Bytes(budget.0.saturating_sub(held.load(Ordering::Relaxed))),
                space,
            },
        }
    }
}

/// The first of `words` and its halvings, down to one chunk, that `left`
/// holds, or the last of them when none does.
///
/// # Specification
/// trivial.
fn fitted(
    words: Words,
    left: Words,
) -> Words
{
    let mut asked = words.0;
    while asked > left.0 && asked > CHUNK.0 {
        asked = asked.checked_div(2).unwrap_or(0).max(CHUNK.0);
    }
    Words(asked)
}

/// The process's account, read the first time a region reserves.
///
/// # Specification
/// trivial.
fn account() -> &'static Account
{
    ACCOUNT.get_or_init(|| Account::of(Space::host(), Width::host()))
}

/// The address space one region of a run reserves: the whole bound, up to
/// the region's share of the process's account, or as much of that as the
/// host gives, down to one chunk.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub(crate) struct Reservation
{
    /// The region's first word.
    base: *mut Word,
    /// The words reserved.
    words: Words,
    /// The words the last run committed, which [`Self::release`] gives back
    /// past the first chunk.
    committed: *mut Word,
    /// The allocation that holds the region, on a host with no mapping.
    #[cfg(not(unix))]
    backing: alloc::vec::Vec<Word>,
}

impl Reservation
{
    /// Reserve `words` of address space, up to the share that the process's
    /// account grants, or half of that when the host refuses, and so on down
    /// to one chunk.
    ///
    /// # Specification
    /// - ensures: the reservation holds at most `words` and the share; it holds
    ///   none only when the host refuses even one chunk. The account holds what
    ///   the reservation holds until the reservation drops.
    /// - executable: none — the host decides what it maps.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a request that the host maps and one that it refuses:
    ///   the first holds its words, and the second halves to what the host
    ///   maps, never below one chunk.
    /// - witness: `regions::tests::a_reservation_holds_at_most_what_it_asks_and_at_least_one_chunk`
    #[must_use]
    pub(crate) fn of(words: Words) -> Self
    {
        let account = account();
        let granted = account.grant(words);
        let reserved = core::iter::successors(Some(granted.0), |&asked| {
            (asked > CHUNK.0).then(|| asked.checked_div(2).unwrap_or(0).max(CHUNK.0))
        })
        .find_map(|asked| Self::mapped(Words(asked)))
        .unwrap_or_else(Self::empty);
        account.refund(Words(granted.0.saturating_sub(reserved.words.0)));
        reserved
    }

    /// The reservation of no words: every commit past its base refuses.
    ///
    /// # Specification
    /// trivial.
    fn empty() -> Self
    {
        Self {
            base: core::ptr::null_mut(),
            words: Words(0),
            committed: core::ptr::null_mut(),
            #[cfg(not(unix))]
            backing: alloc::vec::Vec::new(),
        }
    }

    /// Map `words` of anonymous memory with no commit charge, or nothing
    /// when the host refuses.
    ///
    /// # Specification
    /// trivial.
    #[cfg(unix)]
    fn mapped(words: Words) -> Option<Self>
    {
        let bytes = words.0.checked_mul(core::mem::size_of::<Word>())?;
        #[cfg(target_os = "linux")]
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE;
        #[cfg(not(target_os = "linux"))]
        let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
        // SAFETY: an anonymous private mapping at an address the kernel
        // picks touches no memory the process holds.
        let base = unsafe {
            libc::mmap(
                core::ptr::null_mut(),
                bytes,
                libc::PROT_READ | libc::PROT_WRITE,
                flags,
                -1,
                0,
            )
        };
        (base != libc::MAP_FAILED).then(|| {
            let base = base.cast::<Word>();
            Self {
                base,
                words,
                committed: base,
            }
        })
    }

    /// Allocate `words` of capacity, or nothing when the allocator refuses.
    ///
    /// # Specification
    /// trivial.
    #[cfg(not(unix))]
    fn mapped(words: Words) -> Option<Self>
    {
        let mut backing = alloc::vec::Vec::new();
        backing.try_reserve_exact(words.0).ok()?;
        let base = backing.as_mut_ptr();
        Some(Self {
            base,
            words,
            committed: base,
            backing,
        })
    }

    /// The region's first word.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn base(&self) -> *mut Word
    {
        self.base
    }

    /// One past the region's last reserved word.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn end(&self) -> *mut Word
    {
        self.base.wrapping_add(self.words.0)
    }

    /// The bytes reserved.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn bytes(&self) -> Bytes
    {
        Bytes::of_words(self.words)
    }

    /// The bytes from the region's base to `limit`, its committed end.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn held(
        &self,
        limit: *mut Word,
    ) -> Bytes
    {
        Bytes::between(self.base, limit)
    }

    /// Record `limit` as the committed end that the run reached.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn hold(
        &mut self,
        limit: *mut Word,
    )
    {
        self.committed = self.committed.max(limit);
    }

    /// Give the host back the pages past the region's first chunk, which
    /// the last run committed, so an idle region keeps one chunk.
    ///
    /// # Specification
    /// - ensures: the pages past the first chunk read as zero when a later run
    ///   writes them, and hold no memory until then.
    /// - executable: none — the pages' memory is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held word in the first chunk and a held word past
    ///   it: the first keeps its value, and the second reads zero; a release
    ///   from the base, or none at all, changes one of them.
    /// - witness: `regions::tests::a_released_region_keeps_its_first_chunk_and_zeroes_the_rest`
    pub(crate) fn release(&mut self)
    {
        let kept = self.base.wrapping_add(CHUNK.0.min(self.words.0));
        if self.committed > kept {
            #[cfg(unix)]
            {
                let bytes = Bytes::between(kept, self.committed);
                // SAFETY: the pages lie inside this mapping, past the words
                // any later run reads before it writes them.
                let _released = unsafe {
                    libc::madvise(
                        kept.cast(),
                        usize::try_from(bytes.0).unwrap_or(usize::MAX),
                        libc::MADV_DONTNEED,
                    )
                };
            }
        }
        self.committed = self.base;
    }
}

impl Drop for Reservation
{
    /// Unmap the region, and credit its words to the process's account.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        #[cfg(unix)]
        if !self.base.is_null() {
            // SAFETY: the mapping is this reservation's, and no run holds it
            // once its set drops.
            let _unmapped = unsafe {
                libc::munmap(
                    self.base.cast(),
                    self.words.0.saturating_mul(core::mem::size_of::<Word>()),
                )
            };
        }
        account().refund(self.words);
    }
}

/// A count, written with its digits in groups of three, a space between.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Grouped(u64);

impl From<u64> for Grouped
{
    /// The count `count`, to write in groups.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u64) -> Self
    {
        Self(count)
    }
}

impl fmt::Display for Grouped
{
    /// The digits in groups of three from the right, a space between.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let digits = self.0.to_string();
        let length = digits.len();
        for (index, digit) in digits.char_indices() {
            if index > 0 && length.wrapping_sub(index).is_multiple_of(3) {
                f.write_char(' ')?;
            }
            f.write_char(digit)?;
        }
        Ok(())
    }
}

/// The host's `MemAvailable`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn available() -> Option<Bytes>
{
    let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
    let line = meminfo
        .lines()
        .find_map(|line| line.strip_prefix("MemAvailable:"))?;
    let kib: u64 = line.trim().strip_suffix("kB")?.trim_end().parse().ok()?;
    kib.checked_mul(1 << 10).map(Bytes)
}

/// The host's `MemAvailable`, which only Linux reports.
///
/// # Specification
/// trivial.
#[cfg(not(target_os = "linux"))]
const fn available() -> Option<Bytes>
{
    None
}

/// The `memory.max` of the process's own cgroup, when it names a number.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn cgroup() -> Option<Bytes>
{
    let cgroups = std::fs::read_to_string("/proc/self/cgroup").ok()?;
    let path = cgroups.lines().find_map(|line| line.strip_prefix("0::"))?;
    let max = std::fs::read_to_string(alloc::format!("/sys/fs/cgroup{path}/memory.max")).ok()?;
    max.trim().parse().ok().map(Bytes)
}

/// The `memory.max` of the process's cgroup, which only Linux has.
///
/// # Specification
/// trivial.
#[cfg(not(target_os = "linux"))]
const fn cgroup() -> Option<Bytes>
{
    None
}

/// The process's `RLIMIT_AS`, when it is finite.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn address_space() -> Option<Bytes>
{
    let mut limit = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: `limit` is a live record of the type the call writes.
    let read = unsafe { libc::getrlimit(libc::RLIMIT_AS, &raw mut limit) };
    (read == 0 && limit.rlim_cur != libc::RLIM_INFINITY).then_some(Bytes(limit.rlim_cur))
}

/// The process's `RLIMIT_AS`, which a host with no C library lacks.
///
/// # Specification
/// trivial.
#[cfg(not(unix))]
const fn address_space() -> Option<Bytes>
{
    None
}

/// The host's physical memory.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn physical() -> Option<Bytes>
{
    // SAFETY: `sysconf` reads a configuration value and writes nothing.
    let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
    // SAFETY: as above.
    let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    let pages = u64::try_from(pages).ok()?;
    let size = u64::try_from(size).ok()?;
    pages.checked_mul(size).map(Bytes)
}

/// The host's physical memory, which a host with no C library does not
/// report.
///
/// # Specification
/// trivial.
#[cfg(not(unix))]
const fn physical() -> Option<Bytes>
{
    None
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;
    use core::num::NonZeroUsize;

    use gandr_runtime_stencils::Word;
    use gandr_runtime_stencils::Words;

    use super::Account;
    use super::Bytes;
    use super::CHUNK;
    use super::Held;
    use super::Memory;
    use super::Origin;
    use super::Region;
    use super::Reservation;
    use super::Short;
    use super::Space;
    use super::Standing;
    use super::Step;
    use super::Unsized;
    use super::bind;
    use super::bound;

    /// A count groups its digits by three from the right.
    #[test]
    fn a_count_groups_its_digits_by_three()
    {
        for (count, grouped) in [
            (7_u64, "7"),
            (123, "123"),
            (1_234, "1 234"),
            (1_u64 << 31_u32, "2 147 483 648"),
        ] {
            assert_eq!(grouped, Bytes(count).to_string(), "{count}");
        }
    }

    /// A size spells in its largest unit that divides it, and the spelling
    /// reads back as the size.
    #[test]
    fn a_size_reads_back_as_it_spells()
    {
        for (bytes, spelled) in [
            (2_u64 << 30_u32, "2 GiB"),
            (512 << 20_u32, "512 MiB"),
            (1_536 << 10_u32, "1 536 KiB"),
            (1_000_001, "1 000 001 B"),
        ] {
            let size = Bytes(bytes);
            assert_eq!(spelled, size.spelled().to_string(), "{bytes}");
            assert_eq!(
                Ok(size),
                spelled.replace(' ', "").parse::<Bytes>(),
                "{spelled} reads back"
            );
        }
    }

    /// A size reads each unit, with a space or without, and bare bytes; it
    /// refuses an unknown unit, no digits, an overflow and zero.
    #[test]
    fn a_size_reads_its_units_and_refuses_the_rest()
    {
        assert_eq!(Ok(Bytes(8 << 30)), "8GiB".parse(), "no space");
        assert_eq!(Ok(Bytes(8 << 30)), "8 GiB".parse(), "a space");
        assert_eq!(Ok(Bytes(256 << 20)), "256MiB".parse(), "MiB");
        assert_eq!(Ok(Bytes(1 << 40)), "1TiB".parse(), "TiB");
        assert_eq!(Ok(Bytes(4 << 10)), "4KiB".parse(), "KiB");
        assert_eq!(Ok(Bytes(4_096)), "4096".parse(), "bare bytes");
        assert_eq!(Ok(Bytes(4_096)), "4096B".parse(), "bytes by name");
        assert_eq!(Err(Unsized::Unit), "8GB".parse::<Bytes>(), "a decimal unit");
        assert_eq!(Err(Unsized::Digits), "GiB".parse::<Bytes>(), "no digits");
        assert_eq!(Err(Unsized::Digits), "".parse::<Bytes>(), "nothing");
        assert_eq!(
            Err(Unsized::Overflow),
            "16777216TiB".parse::<Bytes>(),
            "past 2⁶⁴ bytes"
        );
        assert_eq!(Err(Unsized::Zero), "0GiB".parse::<Bytes>(), "zero");
    }

    /// Each origin renders apart from the others, and each names the size.
    #[test]
    fn each_origin_names_itself_and_its_size()
    {
        let bytes = Bytes(2 << 30);
        let rendered = [
            Origin::Flag,
            Origin::Available,
            Origin::Physical,
            Origin::Unread,
        ]
        .map(|origin| Memory { bytes, origin }.to_string());
        assert_eq!("--memory 2 GiB", rendered[0], "the flag as it spells");
        for (index, text) in rendered.iter().enumerate().skip(1) {
            assert!(text.contains("2 147 483 648 bytes"), "{text}");
            for other in rendered.iter().skip(index + 1) {
                assert_ne!(text, other, "two origins render alike");
            }
        }
    }

    /// A stop at the bound names the sum, both regions, the region that
    /// asked, the origin and the remedy; a stop at a reservation names the
    /// reservation.
    #[test]
    fn a_stop_names_its_regions_its_origin_and_its_remedy()
    {
        let mut held = Held {
            asked: Region::Windows,
            short: Short::Bound,
            heap: Bytes(512 << 20_u32),
            windows: Bytes(1_610_612_736),
            step: Step(184_210),
            bound: Memory::flag(Bytes(2 << 30)),
        };
        assert_eq!(
            "the run held 2 147 483 648 bytes across its regions at step 184 210: the window \
             region 1 610 612 736, the heap 536 870 912; the window region asked for one more \
             chunk past --memory 2 GiB; raise --memory",
            held.to_string()
        );
        held.asked = Region::Heap;
        assert!(
            held.to_string().contains("; the heap asked for"),
            "the heap asks: {held}"
        );
        held.short = Short::Reservation {
            reserved: Bytes(1 << 30),
            standing: Standing::Bounded {
                share: Bytes(512 << 20_u32),
                left: Bytes(0),
                space: Bytes(64 << 30),
            },
        };
        assert!(
            held.to_string().ends_with(
                "past the 1 073 741 824 bytes of address space that it reserved, its share \
                 536 870 912 with 0 left of a quarter of the process's 68 719 476 736 bytes of \
                 address space, within --memory 2 GiB"
            ),
            "{held}"
        );
        held.short = Short::Reservation {
            reserved: Bytes(1 << 30),
            standing: Standing::Unread,
        };
        assert!(
            held.to_string().ends_with(
                "past the 1 073 741 824 bytes of address space that the host reserved for it, \
                 which reports no address space, within --memory 2 GiB"
            ),
            "{held}"
        );
    }

    /// The first binding holds for every read, and a later binding is
    /// refused with the bound in force. A test that read the bound first
    /// fixes it, so the first binding here may meet that bound.
    #[test]
    fn the_first_binding_holds_and_a_later_one_is_refused()
    {
        let first = Memory::flag(Bytes(9 << 20_u32));
        let held = bind(first).err().unwrap_or(first);
        assert_eq!(held, bound());
        assert_eq!(Err(held), bind(Memory::flag(Bytes(16 << 20_u32))));
        assert_eq!(held, bound());
    }

    /// A reservation holds the words it asks for where the host maps them,
    /// and halves a request that the host refuses down to what it maps,
    /// never below one chunk.
    #[test]
    fn a_reservation_holds_at_most_what_it_asks_and_at_least_one_chunk()
    {
        let asked = Words(CHUNK.0.saturating_mul(3));
        assert_eq!(asked, Reservation::of(asked).words);
        let huge = Words(usize::MAX.wrapping_shr(3));
        let halved = Reservation::of(huge).words;
        assert!(halved.0 < huge.0, "{halved:?}");
        assert!(halved.0 >= CHUNK.0, "{halved:?}");
    }

    /// The regions of a process with 64 GiB of space on 16 threads share a
    /// budget of 16 GiB: each of 32 regions takes its share of 512 MiB, a
    /// later region takes one chunk, and a refund gives the share back. A
    /// space too small for a chunk still gives each region one chunk. Before
    /// the account, each region asked the whole bound and took what the host
    /// gave, so the sixth set found no space on the `riscv64` runner.
    #[test]
    fn each_region_of_a_small_space_asks_its_share_6877()
    {
        let width = super::Width(NonZeroUsize::new(16).unwrap_or(NonZeroUsize::MIN));
        let account = Account::of(Space::Bounded(Bytes(64 << 30)), width);
        let share = Bytes(512 << 20_u32).words();
        let bound = Bytes(122 << 30).words();
        for region in 0_u32 .. 32_u32 {
            assert_eq!(share, account.grant(bound), "region {region}");
        }
        assert_eq!(CHUNK, account.grant(bound), "past the budget");
        let small = Words(CHUNK.0.saturating_mul(3));
        account.refund(Words(CHUNK.0.saturating_add(share.0)));
        assert_eq!(small, account.grant(small), "a region that asks less");
        account.refund(small);
        assert_eq!(share, account.grant(bound), "the share given back");
        let tiny = Account::of(Space::Bounded(Bytes(1 << 20)), width);
        assert_eq!(CHUNK, tiny.grant(bound), "a space too small for a chunk");
    }

    /// The space is a power of two that the host maps again as one probe,
    /// and the host refuses twice it, unless it is 2⁴⁷ bytes.
    #[cfg(unix)]
    #[test]
    fn the_space_is_the_largest_probe_that_the_host_grants_6877()
    {
        let Space::Bounded(space) = Space::host()
        else {
            panic!("a unix host maps a probe");
        };
        assert!(space.0.is_power_of_two(), "{space}");
        assert_eq!(super::Probe::Granted, super::probe(space), "{space}");
        if space.0 < 1 << super::PROBE_TOP {
            assert_eq!(
                super::Probe::Refused,
                super::probe(Bytes(space.0.saturating_mul(2))),
                "{space}"
            );
        }
    }

    /// A region holds the bytes of one word for each word from its base to
    /// a limit, on every host. The memory bound reads these bytes when it
    /// stops a run.
    #[test]
    fn a_region_holds_a_word_s_bytes_for_each_word_6578()
    {
        let region = Reservation::of(CHUNK);
        let word = u64::try_from(core::mem::size_of::<Word>()).unwrap_or(u64::MAX);
        assert_eq!(Bytes(0), region.held(region.base()));
        assert_eq!(
            Bytes(word.saturating_mul(3)),
            region.held(region.base().wrapping_add(3))
        );
        assert_eq!(region.bytes(), region.held(region.end()));
    }

    /// Past a run, a region keeps the words of its first chunk and gives
    /// back the pages past it, which read as zero again.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_released_region_keeps_its_first_chunk_and_zeroes_the_rest()
    {
        let mut region = Reservation::of(Words(CHUNK.0.saturating_mul(2)));
        let first = region.base();
        let past = first.wrapping_add(CHUNK.0);
        // SAFETY: the word lies inside the reservation's first chunk.
        unsafe {
            first.write(Word::from(7_usize));
        }
        // SAFETY: the word lies inside the reservation's second chunk.
        unsafe {
            past.write(Word::from(7_usize));
        }
        region.hold(past.wrapping_add(1));
        region.release();
        // SAFETY: as above; the mapping stays the region's until it drops.
        let kept = unsafe { first.read() };
        // SAFETY: as above.
        let given = unsafe { past.read() };
        assert_eq!(Word::from(7_usize), kept);
        assert_eq!(Word::ZERO, given);
    }

    /// On a Linux host the bound is at most `MemAvailable`, and its origin
    /// is the available memory. The test reads the host one time, so another
    /// process cannot move the bound and the figure apart.
    #[cfg(target_os = "linux")]
    #[test]
    fn the_host_bound_is_at_most_its_available_memory_6649()
    {
        let readings = super::Readings::now();
        let available = readings.available.expect("Linux reports MemAvailable");
        let host = Memory::of(readings);
        assert_eq!(Origin::Available, host.origin(), "{host}");
        assert!(host.bytes() <= available, "{host} past {available}");
    }
}
