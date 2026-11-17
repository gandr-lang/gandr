//! The activity ring: which task each worker of the driver's pool runs, and
//! when the task starts and ends.
//!
//! Each worker of the pool is a producer, and it owns one ring. At the start
//! and at the end of each task, the producer writes one fixed-size [`Mark`]
//! into its ring. The write is one push into the producer's own ring: it
//! takes no lock, and it writes no cache line that another producer writes. A
//! full ring drops its oldest mark and counts the drop, so a slow consumer
//! never stops a producer.
//!
//! One consumer, the hub, folds the rings once for each tick with
//! [`Fold::tick`]. The fold merges the marks of all the rings by the clock,
//! then by the core, and gives each [`Event`] its [`Sequence`] in that order.
//! So the hub is the one writer of the sequence number. An event that
//! reaches the fold late takes the next number and is counted, as
//! [`Arrival`] states. The fold keeps the occupancy of each core over the
//! last two seconds as 120 cells, one for each sixtieth of a second. The
//! [`ActivityCard`] of a tick holds the events since the last tick and the
//! row of each core. The stream appends each card's events to its ledger, so
//! the ledger is the append-only block of the stream, keyed by the sequence
//! number.
//!
//! The module compiles only with the `instrument` feature. A build without
//! the feature carries none of its bytes.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — newest: the engine surface,
//!   § engine-surface-activity: the rows of the activity pane, which this fold
//!   fills; § engine-surface-stream: the append-only activity card, keyed by
//!   the sequence number.

use alloc::boxed::Box;
use alloc::collections::BinaryHeap;
use alloc::vec::Vec;
use core::cell::Cell;
use core::cmp::Reverse;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::num::NonZeroU16;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;

use crossbeam_queue::ArrayQueue;
use quenchant_shape::shape::Maybe;

/// How many cells hold the occupancy of one core.
const CELLS: usize = 120;

/// The cell count, as the clock counts.
const CELLS_ON_THE_CLOCK: u64 = 120;

/// The time that one cell covers, in nanoseconds: a sixtieth of a second,
/// rounded down. The 120 cells of a row cover two seconds.
const CELL: u64 = 16_666_666;

/// The number of a cell on the clock: a clock reading divided by the time of
/// one cell.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CellNumber(u64);

impl CellNumber
{
    /// The cell that holds the clock reading `clock`.
    ///
    /// # Specification
    /// trivial.
    const fn of(clock: Nanos) -> Self
    {
        Self(match clock.0.checked_div(CELL) {
            Some(number) => number,
            None => 0,
        })
    }

    /// The place of this cell in a row's array.
    ///
    /// # Specification
    /// trivial.
    fn slot(self) -> Slot
    {
        Slot(
            usize::try_from(self.0.checked_rem(CELLS_ON_THE_CLOCK).unwrap_or_default())
                .unwrap_or_default(),
        )
    }
}

/// The place of a cell in a row's array.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot(usize);

/// The kind of a task that a worker runs.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Task
{
    /// A job that a check forks onto the pool.
    Fork,
    /// The kernel's replay of a declaration.
    Replay,
    /// The compilation of a declaration.
    Compile,
    /// The fetch of a chunk from the store.
    Fetch,
}

/// The end of a task that an event marks.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Edge
{
    /// The task starts.
    Start,
    /// The task ends.
    End,
}

/// The ordinal of the declaration that a task works on, in its program's
/// order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Declaration(u32);

impl From<u32> for Declaration
{
    /// The declaration at `ordinal`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(ordinal: u32) -> Self
    {
        Self(ordinal)
    }
}

impl From<Declaration> for u32
{
    /// The ordinal of `declaration`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(declaration: Declaration) -> Self
    {
        declaration.0
    }
}

quenchant_shape::reason_enum! {
    /// Why an event names no declaration.
    pub mod unnamed {
        /// The reason an event names no declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The task works on no one declaration: a chunk fetch, or a fork
            /// job over a whole component.
            Unnamed,
        }
    }
}

/// The declaration that a task works on, or none, in four bytes.
///
/// The ordinal `u32::MAX` stands for none, so a mark stays 24 bytes and an
/// event 32. A declaration at that ordinal reads as none.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Declared(u32);

impl Declared
{
    /// No declaration.
    pub const NONE: Self = Self(u32::MAX);

    /// The declaration that the task works on, or why it names none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn declaration(self) -> Maybe<Declaration, unnamed::Absent>
    {
        if self.0 == u32::MAX {
            Maybe::Absent(unnamed::Absent::Unnamed)
        }
        else {
            Maybe::Present(Declaration(self.0))
        }
    }
}

impl From<Declaration> for Declared
{
    /// The task works on `declaration`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(declaration: Declaration) -> Self
    {
        Self(declaration.0)
    }
}

/// A core of the pool: the index of the worker that owns a ring.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Core(u16);

impl From<u16> for Core
{
    /// The core at `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u16) -> Self
    {
        Self(index)
    }
}

impl From<Core> for usize
{
    /// The index of `core`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(core: Core) -> Self
    {
        Self::from(core.0)
    }
}

/// The world that a task runs in. A deployment's ledger is the union of the
/// ledgers of its worlds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct World(u32);

impl From<u32> for World
{
    /// The world at `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<World> for u32
{
    /// The index of `world`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(world: World) -> Self
    {
        world.0
    }
}

/// A reading of the hub's clock, or a duration on it, in nanoseconds. The
/// producers and the fold read one monotonic clock.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Nanos(u64);

impl From<u64> for Nanos
{
    /// The reading `nanoseconds`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nanoseconds: u64) -> Self
    {
        Self(nanoseconds)
    }
}

impl From<Nanos> for u64
{
    /// The nanoseconds of `nanos`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nanos: Nanos) -> Self
    {
        nanos.0
    }
}

/// The place of an event in the ledger of one [`Fold`]. The fold gives the
/// numbers in the order of its merge, so no two events share one.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Sequence(u64);

impl From<Sequence> for u64
{
    /// The number of `sequence`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(sequence: Sequence) -> Self
    {
        sequence.0
    }
}

/// The count of the events that a full ring dropped.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Dropped(u64);

impl From<Dropped> for u64
{
    /// The count of `dropped`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(dropped: Dropped) -> Self
    {
        dropped.0
    }
}

/// The count of the events that reached the fold late: each one's clock
/// precedes the latest clock that the fold numbered before it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Late(u64);

impl From<Late> for u64
{
    /// The count of `late`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(late: Late) -> Self
    {
        late.0
    }
}

/// How an event reached the fold: in turn, or late.
///
/// A producer reads the clock, then pushes; a preemption between the two
/// puts an event with an earlier clock into a later tick. The fold never
/// reorders what it numbered, so it numbers that event next and marks it
/// late.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Arrival
{
    /// The event's clock is no earlier than the clock of any event numbered
    /// before it.
    InTurn,
    /// The event's clock precedes the latest clock numbered before it.
    Late,
}

/// What a producer states about a task when it starts or ends it. A ring
/// holds marks: 24 bytes each.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Mark
{
    /// The kind of the task.
    pub task: Task,
    /// The end of the task.
    pub edge: Edge,
    /// The declaration that the task works on.
    pub declaration: Declared,
    /// The world that the task runs in.
    pub world: World,
    /// The hub's clock when the task starts or ends.
    pub clock: Nanos,
}

/// One start or one end of a task, as the fold numbers it: 32 bytes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Event
{
    /// The event's place in the ledger: the order in which the fold
    /// numbered it.
    pub sequence: Sequence,
    /// The hub's clock when the task starts or ends.
    pub clock: Nanos,
    /// The declaration that the task works on.
    pub declaration: Declared,
    /// The world that the task runs in.
    pub world: World,
    /// The core that runs the task.
    pub core: Core,
    /// The kind of the task.
    pub task: Task,
    /// The end of the task.
    pub edge: Edge,
    /// Whether the event reached the fold in turn or late.
    pub arrival: Arrival,
}

// An event is four words, and the mark that a ring holds is three: a cache
// line holds two slots of a ring.
const _: () = assert!(size_of::<Event>() == 32, "an event is 32 bytes");
const _: () = assert!(size_of::<Mark>() == 24, "a mark is 24 bytes");

/// How many cores an [`Activity`] holds a ring for: the width of the pool.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Cores(NonZeroU16);

impl From<NonZeroU16> for Cores
{
    /// `count` cores.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: NonZeroU16) -> Self
    {
        Self(count)
    }
}

impl From<Cores> for NonZeroU16
{
    /// The count of `cores`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cores: Cores) -> Self
    {
        cores.0
    }
}

/// How many events one ring holds before it drops the oldest.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Slots(NonZeroUsize);

impl From<NonZeroUsize> for Slots
{
    /// `count` slots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: NonZeroUsize) -> Self
    {
        Self(count)
    }
}

impl From<Slots> for NonZeroUsize
{
    /// The count of slots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(slots: Slots) -> Self
    {
        slots.0
    }
}

/// The ring of one producer, on cache lines of its own.
///
/// # Specification
/// trivial.
#[repr(align(128))]
#[derive(Debug)]
struct Ring
{
    /// The marks not yet folded, oldest first.
    events: ArrayQueue<Mark>,
    /// The count of the events that the ring dropped when it was full.
    dropped: AtomicU64,
    /// Whether a [`Producer`] holds the ring.
    held: AtomicBool,
}

/// The rings of one pool, one for each core.
///
/// # Specification
/// - provides: a [`Producer`] for each core through [`Activity::producer`], and
///   the rings that [`Fold::tick`] drains.
/// - panics: none.
/// - executable: none — a holder of atomics; its producers and its fold carry
///   the behaviour.
///
/// # Adequacy
/// - hypothesis: L3 — producers on several threads, with a fold that ticks
///   beside them, give each event once, each core's events in its order, and
///   distinct sequence numbers.
/// - witness: `activity::tests::producers_on_their_threads_reach_the_fold_once_each_in_order`
#[repr(transparent)]
#[derive(Debug)]
pub struct Activity
{
    /// The rings, one for each core, in the order of the cores.
    rings: Box<[Ring]>,
}

impl Activity
{
    /// The rings of a pool of `cores` workers, each ring of `slots` events.
    ///
    /// # Specification
    /// - ensures: one empty ring for each core, each of `slots` events, and no
    ///   producer held.
    /// - panics: none.
    /// - executable: none — the rings are atomics, which a postcondition does
    ///   not read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ring of two slots drops its oldest event at the
    ///   third, and a core past the count is refused.
    /// - witness: `activity::tests::a_full_ring_drops_its_oldest_event_and_counts_the_drop`
    /// - witness: `activity::tests::a_core_has_one_producer_at_a_time`
    #[inline]
    #[must_use]
    pub fn new(
        cores: Cores,
        slots: Slots,
    ) -> Self
    {
        let rings = core::iter::repeat_with(|| Ring {
            events: ArrayQueue::new(slots.0.get()),
            dropped: AtomicU64::new(0),
            held: AtomicBool::new(false),
        })
        .take(NonZeroUsize::from(cores.0).get())
        .collect();
        Self { rings }
    }

    /// The producer that writes the ring of `core`.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the ring of `core` is held until the producer is
    ///   dropped, so one thread at a time writes it.
    /// - fails: [`Unclaimable::Absent`] for a core past the count, and
    ///   [`Unclaimable::Held`] while another producer holds the ring.
    /// - panics: none.
    /// - executable: none — the hold is an atomic flag.
    ///
    /// # Errors
    /// - [`Unclaimable::Absent`]: the activity holds no ring for `core`.
    /// - [`Unclaimable::Held`]: a producer holds the ring of `core`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a second claim of one core is refused, a claim after
    ///   the first producer's drop is admitted, and a core past the count is
    ///   refused.
    /// - witness: `activity::tests::a_core_has_one_producer_at_a_time`
    #[inline]
    pub fn producer(
        &self,
        core: Core,
    ) -> Result<Producer<'_>, Unclaimable>
    {
        let ring = self
            .rings
            .get(usize::from(core))
            .ok_or(Unclaimable::Absent)?;
        ring.held
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .map_err(|_held| Unclaimable::Held)?;
        Ok(Producer {
            ring,
            unshared: PhantomData,
        })
    }

    /// The writer of the ring of `core` for a thread of a pool, which takes
    /// no claim.
    ///
    /// A pool's index names one thread, and a worker that runs a nested job
    /// while it waits writes from that thread, so the ring keeps one writer
    /// without a claim. A claim would refuse the nested job's writer.
    ///
    /// # Specification
    /// - requires: one thread at a time writes through the workers and the
    ///   producer of `core`.
    /// - fails: [`Unclaimable::Absent`] for a core past the count.
    /// - panics: none.
    /// - executable: none — a borrow of one ring.
    ///
    /// # Errors
    /// - [`Unclaimable::Absent`]: the activity holds no ring for `core`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a worker's marks reach the fold beside a producer's,
    ///   and a core past the count is refused.
    /// - witness: `activity::tests::a_worker_writes_its_core_s_ring_without_a_claim`
    #[inline]
    pub fn worker(
        &self,
        core: Core,
    ) -> Result<Worker<'_>, Unclaimable>
    {
        self.rings
            .get(usize::from(core))
            .map(|ring| Worker { ring })
            .ok_or(Unclaimable::Absent)
    }

    /// How many rings the activity holds: the cores it was made for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cores(&self) -> Cores
    {
        let count = u16::try_from(self.rings.len()).unwrap_or(u16::MAX);
        Cores(NonZeroU16::new(count).unwrap_or(NonZeroU16::MIN))
    }
}

/// Push `mark` into `ring`, and count the oldest mark that a full ring drops.
///
/// # Specification
/// trivial.
#[inline]
fn push(
    ring: &Ring,
    mark: Mark,
)
{
    if ring.events.force_push(mark).is_some() {
        ring.dropped.fetch_add(1, Ordering::Relaxed);
    }
}

/// The writer of one ring for a thread of a pool: [`Activity::worker`].
///
/// # Specification
/// - provides: [`Worker::record`], the write of one mark.
/// - panics: none.
/// - executable: none — a borrow of one ring.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Activity::worker`].
/// - witness: `activity::tests::a_worker_writes_its_core_s_ring_without_a_claim`
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Worker<'activity>
{
    /// The ring that this worker writes.
    ring: &'activity Ring,
}

impl Worker<'_>
{
    /// Write `mark` into the ring, as [`Producer::record`] does.
    ///
    /// # Specification
    /// - requires: as [`Producer::record`], and the requirement of
    ///   [`Activity::worker`].
    /// - ensures: as [`Producer::record`].
    /// - panics: none.
    /// - intension: one push into the ring; no lock and no allocation.
    /// - executable: none — the ring is a queue of atomics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Activity::worker`].
    /// - witness: `activity::tests::a_worker_writes_its_core_s_ring_without_a_claim`
    #[inline]
    pub fn record(
        &self,
        mark: Mark,
    )
    {
        push(self.ring, mark);
    }
}

/// Why [`Activity::producer`] gives no producer.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unclaimable
{
    /// The activity holds no ring for the core.
    Absent,
    /// Another producer holds the ring.
    Held,
}

/// The one writer of one ring. A producer is not shared between threads, so
/// the order of its ring is the order in which its thread wrote.
///
/// # Specification
/// - provides: [`Producer::record`], the write of one mark.
/// - panics: none.
/// - executable: none — a borrow of one ring.
///
/// # Adequacy
/// - hypothesis: L3 — the events of one producer reach the fold in the order it
///   wrote them.
/// - witness: `activity::tests::one_producer_s_events_reach_the_card_in_order`
#[derive(Debug)]
pub struct Producer<'activity>
{
    /// The ring that this producer writes.
    ring: &'activity Ring,
    /// A producer is not `Sync`, so one thread writes its ring.
    unshared: PhantomData<Cell<()>>,
}

impl Producer<'_>
{
    /// Write `mark` into the ring.
    ///
    /// # Specification
    /// - requires: the clock of `mark` is no earlier than the clock of the
    ///   producer's last mark, so the ring is in the order of the clock.
    /// - ensures: the ring holds the mark; when the ring was full, its oldest
    ///   mark is dropped and the drop is counted.
    /// - panics: none.
    /// - intension: one push into the producer's own ring; no lock, no
    ///   allocation and no cache line that another producer writes.
    /// - executable: none — the ring is a queue of atomics, which a
    ///   postcondition does not read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ring of two slots written three times keeps the
    ///   last two marks and counts one drop.
    /// - witness: `activity::tests::a_full_ring_drops_its_oldest_event_and_counts_the_drop`
    /// - witness: `activity::tests::one_producer_s_events_reach_the_card_in_order`
    #[inline]
    pub fn record(
        &self,
        mark: Mark,
    )
    {
        push(self.ring, mark);
    }
}

impl Drop for Producer<'_>
{
    /// Free the ring for the next producer of its core.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        self.ring.held.store(false, Ordering::Release);
    }
}

/// The occupancy of one core over the last two seconds, the drops of its
/// ring, and its late events.
///
/// # Specification
/// - provides: [`Row::cells`], the busy time of each cell, oldest first;
///   [`Row::dropped`], the drops of the core's ring; [`Row::late`], the core's
///   events that reached the fold late.
/// - panics: none.
/// - executable: none — a fold's state.
///
/// # Adequacy
/// - hypothesis: L3 — a task across a cell boundary splits its time between the
///   two cells, nested tasks count once, an open task counts up to the tick and
///   not again at its end, and time older than two seconds leaves the row.
/// - witness: `activity::tests::a_task_fills_the_cells_it_spans`
/// - witness: `activity::tests::nested_tasks_count_once_and_an_open_task_counts_up_to_the_tick`
/// - witness: `activity::tests::time_older_than_the_window_leaves_the_row`
/// - witness: `activity::tests::a_late_event_takes_the_next_number_is_counted_and_lands_in_its_own_cell`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Row
{
    /// The busy nanoseconds of each cell, at the cell's number modulo the
    /// count of the cells.
    cells: [u32; CELLS],
    /// The newest cell.
    newest: CellNumber,
    /// How many tasks of the core are open.
    open: u32,
    /// Since when the core is busy, while a task is open.
    since: Nanos,
    /// The drops of the core's ring.
    dropped: Dropped,
    /// The core's events that reached the fold late.
    late: Late,
    /// The busy time of the core since the fold began, net of the time a
    /// late end took back.
    total: Nanos,
}

impl Row
{
    /// The row of a core that ran nothing.
    ///
    /// # Specification
    /// trivial.
    const fn idle() -> Self
    {
        Self {
            cells: [0; CELLS],
            newest: CellNumber(0),
            open: 0,
            since: Nanos(0),
            dropped: Dropped(0),
            late: Late(0),
            total: Nanos(0),
        }
    }

    /// The busy time of each cell over the last two seconds, oldest first.
    ///
    /// # Specification
    /// - ensures: 120 readings, each at most the time of one cell; the last is
    ///   the cell of the latest tick.
    /// - panics: none.
    /// - executable: none — an iterator over the cells.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cells of a task across a boundary, and of a
    ///   window that moved past old time.
    /// - witness: `activity::tests::a_task_fills_the_cells_it_spans`
    /// - witness: `activity::tests::time_older_than_the_window_leaves_the_row`
    #[inline]
    #[must_use]
    pub const fn cells(&self) -> Cells<'_>
    {
        Cells {
            row: self,
            taken: 0,
        }
    }

    /// The drops of the core's ring.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn dropped(&self) -> Dropped
    {
        self.dropped
    }

    /// The core's events that reached the fold late.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn late(&self) -> Late
    {
        self.late
    }

    /// The busy time of the core since the fold began, beyond the window of
    /// the cells: the time each closed task held the core, and each open task
    /// up to the latest tick.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn total(&self) -> Nanos
    {
        self.total
    }

    /// Open a task at `clock`.
    ///
    /// # Specification
    /// trivial.
    fn start(
        &mut self,
        clock: Nanos,
    )
    {
        if self.open == 0 {
            self.since = clock;
        }
        self.open = self.open.saturating_add(1);
    }

    /// Close a task at `clock`. The busy time is added when the last open
    /// task closes. An end whose start the ring dropped closes nothing. A
    /// late end, earlier than the tick that last counted the open task,
    /// takes back the time from the end up to that tick.
    ///
    /// # Specification
    /// trivial.
    fn end(
        &mut self,
        clock: Nanos,
    )
    {
        if self.open == 0 {
            return;
        }
        self.open = self.open.saturating_sub(1);
        if self.open == 0 {
            if clock < self.since {
                self.change(clock, self.since, Change::TakeBack);
            }
            else {
                self.change(self.since, clock, Change::Add);
            }
        }
    }

    /// Count the time of the open tasks up to `now`, then move the window to
    /// the cell of `now`.
    ///
    /// # Specification
    /// trivial.
    fn tick(
        &mut self,
        now: Nanos,
    )
    {
        if self.open > 0 && self.since < now {
            self.change(self.since, now, Change::Add);
            self.since = now;
        }
        self.advance(CellNumber::of(now));
    }

    /// Add the busy time from `from` to `to` to the cells that it spans,
    /// inside the window, or take it back.
    ///
    /// # Specification
    /// trivial.
    fn change(
        &mut self,
        from: Nanos,
        to: Nanos,
        change: Change,
    )
    {
        if to <= from {
            return;
        }
        let spent = to.0.saturating_sub(from.0);
        self.total = Nanos(match change {
            Change::Add => self.total.0.saturating_add(spent),
            Change::TakeBack => self.total.0.saturating_sub(spent),
        });
        let last = CellNumber::of(Nanos(to.0.saturating_sub(1)));
        self.advance(last);
        let oldest = self
            .newest
            .0
            .saturating_sub(CELLS_ON_THE_CLOCK.saturating_sub(1));
        let first = CellNumber::of(from).0.max(oldest);
        for number in (first ..= last.0).map(CellNumber) {
            let start = number.0.saturating_mul(CELL).max(from.0);
            let end = number.0.saturating_add(1).saturating_mul(CELL).min(to.0);
            let span = u32::try_from(end.saturating_sub(start)).unwrap_or(u32::MAX);
            if let Some(cell) = self.cells.get_mut(number.slot().0) {
                *cell = match change {
                    Change::Add => cell.saturating_add(span),
                    Change::TakeBack => cell.saturating_sub(span),
                };
            }
        }
    }

    /// Move the newest cell to `number`, and clear each cell that the window
    /// leaves.
    ///
    /// # Specification
    /// trivial.
    fn advance(
        &mut self,
        number: CellNumber,
    )
    {
        if number <= self.newest {
            return;
        }
        let steps = number
            .0
            .saturating_sub(self.newest.0)
            .min(CELLS_ON_THE_CLOCK);
        let cleared = number.0.saturating_sub(steps);
        for step in 1 ..= steps {
            if let Some(cell) = self
                .cells
                .get_mut(CellNumber(cleared.saturating_add(step)).slot().0)
            {
                *cell = 0;
            }
        }
        self.newest = number;
    }
}

/// Whether [`Row::change`] adds busy time to the cells or takes back time
/// that a tick counted.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Change
{
    /// Add the span to the cells.
    Add,
    /// Take the span back from the cells.
    TakeBack,
}

/// The busy time of each cell of a [`Row`], oldest first.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Cells<'row>
{
    /// The row read.
    row: &'row Row,
    /// How many cells are read.
    taken: u64,
}

impl Iterator for Cells<'_>
{
    type Item = Nanos;

    /// The busy time of the next cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Nanos>
    {
        if self.taken >= CELLS_ON_THE_CLOCK {
            return None;
        }
        // The cell `newest + 1 + taken - 120` has the place of the cell
        // `newest + 1 + taken`, so no subtraction can wrap.
        let number = CellNumber(
            self.row
                .newest
                .0
                .saturating_add(1)
                .saturating_add(self.taken),
        );
        self.taken = self.taken.saturating_add(1);
        let busy = self
            .row
            .cells
            .get(number.slot().0)
            .copied()
            .unwrap_or_default();
        Some(Nanos(u64::from(busy)))
    }

    /// The cells not yet read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let left =
            usize::try_from(CELLS_ON_THE_CLOCK.saturating_sub(self.taken)).unwrap_or_default();
        (left, Some(left))
    }
}

impl ExactSizeIterator for Cells<'_>
{
}

impl FusedIterator for Cells<'_>
{
}

/// What one tick of the fold gives the stream: the events since the last
/// tick, in the order of their sequence numbers, and the row of each core.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct ActivityCard<'fold>
{
    /// The events since the last tick, in the order of their sequence
    /// numbers.
    pub events: &'fold [Event],
    /// The row of each core, in the order of the cores.
    pub rows: &'fold [Row],
}

/// The hub's fold of the rings of one [`Activity`]: the one consumer.
///
/// # Specification
/// - provides: [`Fold::tick`], which drains the rings and answers the card.
/// - panics: none.
/// - executable: none — the fold's buffers.
///
/// # Adequacy
/// - hypothesis: L3 — the marks of two producers reach one card in the order of
///   the clock, a late mark takes the next number and is counted, and producers
///   on their threads reach the fold once each.
/// - witness: `activity::tests::two_producers_merge_in_the_order_of_the_clock`
/// - witness: `activity::tests::a_late_event_takes_the_next_number_is_counted_and_lands_in_its_own_cell`
/// - witness: `activity::tests::producers_on_their_threads_reach_the_fold_once_each_in_order`
#[derive(Debug)]
pub struct Fold
{
    /// The marks drained in this tick, ring after ring.
    drained: Vec<Mark>,
    /// Where the run of each ring ends in `drained`.
    ends: Vec<usize>,
    /// The next mark of each run that is not yet merged.
    next: Vec<usize>,
    /// The first mark of each run that is not yet merged, the earliest clock
    /// first, then the lowest core.
    heads: BinaryHeap<Reverse<(Nanos, usize)>>,
    /// The events of this tick, in the order of their sequence numbers.
    merged: Vec<Event>,
    /// The sequence number of the next event.
    sequence: Sequence,
    /// The latest clock that the fold numbered.
    latest: Nanos,
    /// The row of each core.
    rows: Box<[Row]>,
    /// The most marks one tick drains from one ring.
    slots: usize,
}

impl Fold
{
    /// The fold of the rings of `activity`, with its buffers made for a tick
    /// that drains every ring whole.
    ///
    /// # Specification
    /// - ensures: one idle row for each core of `activity`, buffers that hold
    ///   every slot of every ring, the first sequence number zero, and no clock
    ///   numbered.
    /// - panics: none.
    /// - executable: none — the buffers' capacity is the observation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first tick after the fold is made gives the
    ///   events written before it.
    /// - witness: `activity::tests::one_producer_s_events_reach_the_card_in_order`
    #[inline]
    #[must_use]
    pub fn new(activity: &Activity) -> Self
    {
        let cores = activity.rings.len();
        let slots = activity
            .rings
            .first()
            .map_or(0, |ring| ring.events.capacity());
        let events = cores.saturating_mul(slots);
        Self {
            drained: Vec::with_capacity(events),
            ends: Vec::with_capacity(cores),
            next: Vec::with_capacity(cores),
            heads: BinaryHeap::with_capacity(cores),
            merged: Vec::with_capacity(events),
            sequence: Sequence(0),
            latest: Nanos(0),
            rows: core::iter::repeat_with(Row::idle).take(cores).collect(),
            slots,
        }
    }

    /// Drain the rings of `activity` at the clock reading `now`, merge their
    /// marks by the clock, number the events, and fold them into the rows.
    ///
    /// # Specification
    /// - requires: `activity` is the activity this fold was made for, and `now`
    ///   is no earlier than the clock of any mark drained.
    /// - ensures: the card's events are the marks drained in this tick, at most
    ///   one ring's slots from each ring, ordered by the clock and then by the
    ///   core, and numbered on from the last tick's numbers. An event whose
    ///   clock precedes the latest clock numbered before it is marked late and
    ///   counted in its core's row. Each row holds the busy time of its core up
    ///   to `now`, by the clock of each event, and the drops of its ring.
    /// - panics: none.
    /// - intension: no allocation once the buffers are made; the merge is
    ///   linear in the events, times the logarithm of the cores.
    /// - executable: none — the rings are atomics, which a postcondition does
    ///   not read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two producers' interleaved events, a core's nested
    ///   and open tasks, and producers on threads beside the fold.
    /// - witness: `activity::tests::two_producers_merge_in_the_order_of_the_clock`
    /// - witness: `activity::tests::nested_tasks_count_once_and_an_open_task_counts_up_to_the_tick`
    /// - witness: `activity::tests::a_late_event_takes_the_next_number_is_counted_and_lands_in_its_own_cell`
    /// - witness: `activity::tests::producers_on_their_threads_reach_the_fold_once_each_in_order`
    #[inline]
    pub fn tick(
        &mut self,
        activity: &Activity,
        now: Nanos,
    ) -> ActivityCard<'_>
    {
        self.drain(activity);
        self.merge();
        for event in &self.merged {
            if let Some(row) = self.rows.get_mut(usize::from(event.core)) {
                match event.edge {
                    Edge::Start => row.start(event.clock),
                    Edge::End => row.end(event.clock),
                }
                if event.arrival == Arrival::Late {
                    row.late = Late(row.late.0.saturating_add(1));
                }
            }
        }
        for (row, ring) in self.rows.iter_mut().zip(activity.rings.iter()) {
            row.tick(now);
            row.dropped = Dropped(ring.dropped.load(Ordering::Relaxed));
        }
        ActivityCard {
            events: &self.merged,
            rows: &self.rows,
        }
    }

    /// Drain at most one ring's slots from each ring into `drained`, and
    /// mark where each ring's run ends.
    ///
    /// # Specification
    /// trivial.
    fn drain(
        &mut self,
        activity: &Activity,
    )
    {
        self.drained.clear();
        self.ends.clear();
        for ring in &activity.rings {
            for _ in 0 .. self.slots {
                let Some(mark) = ring.events.pop()
                else {
                    break;
                };
                self.drained.push(mark);
            }
            self.ends.push(self.drained.len());
        }
    }

    /// Merge the runs of `drained` into `merged` by the clock, then by the
    /// core, and number each event. Each run is in the order of the clock,
    /// because one producer writes its ring as its clock moves on. An event
    /// whose clock precedes the latest clock numbered is numbered next and
    /// marked late: the fold never reorders what it numbered.
    ///
    /// # Specification
    /// trivial.
    fn merge(&mut self)
    {
        self.merged.clear();
        self.next.clear();
        self.heads.clear();
        let mut start = 0;
        for (run, &end) in self.ends.iter().enumerate() {
            self.next.push(start);
            if let Some(first) = self.drained.get(start)
                && start < end
            {
                self.heads.push(Reverse((first.clock, run)));
            }
            start = end;
        }
        while let Some(Reverse((_, run))) = self.heads.pop() {
            let (Some(next), Some(&end)) = (self.next.get_mut(run), self.ends.get(run))
            else {
                continue;
            };
            let Some(&mark) = self.drained.get(*next)
            else {
                continue;
            };
            let arrival = if mark.clock < self.latest {
                Arrival::Late
            }
            else {
                self.latest = mark.clock;
                Arrival::InTurn
            };
            self.merged.push(Event {
                sequence: self.sequence,
                clock: mark.clock,
                declaration: mark.declaration,
                world: mark.world,
                core: Core(u16::try_from(run).unwrap_or(u16::MAX)),
                task: mark.task,
                edge: mark.edge,
                arrival,
            });
            self.sequence = Sequence(self.sequence.0.saturating_add(1));
            *next = next.saturating_add(1);
            if *next < end
                && let Some(following) = self.drained.get(*next)
            {
                self.heads.push(Reverse((following.clock, run)));
            }
        }
    }
}

#[cfg(test)]
mod tests;
