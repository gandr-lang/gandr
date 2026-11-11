//! The timings layer: the wall and the allocations of each phase of a
//! recheck, sampled for each declaration where the phase runs for each
//! declaration and for the document otherwise, and kept in rings of the last
//! 32 samples.
//!
//! # A sample is two readings at the boundaries of a phase
//!
//! **Choice.** [`Timings`] is the sink of the timings layer. At each phase
//! boundary it reads the monotonic clock and the allocation meter of its
//! thread ([`Allocations`]), and a phase's sample is the difference of two
//! readings: a [`Spent`]. The parse and the lowering run once for the
//! document, so they sample the document. The incremental pass judges one item
//! after another, so it samples each item it judges, from the end of the item
//! before it. An item that it adopts runs no judgement and writes no sample.
//! The kernel admits one declaration after another, so a metered admission
//! ([`Positioning::Metered`]) samples each declaration it crosses. The
//! judgement and the admission also sample the document, which the recheck's
//! timing line reads.
//!
//! The account keeps a [`SampleRing`] of the last [`WINDOW`] samples for each
//! phase of the document, and for the judgement and the admission of each
//! declaration. A ring is a fixed array: a sample overwrites the oldest one
//! and allocates nothing. [`SampleRing::spread`] folds a ring into its p50 and
//! its p99, each by a selection over a copy of the ring on the stack.
//!
//! **Alternatives.** A mean hides the tail that the p99 shows. A histogram of
//! fixed buckets answers a percentile only to its bucket's width. A sort of the
//! ring costs `n log n` where a selection costs `n`. Two readings for each item
//! cost twice the readings, because the end of one item is the start of the
//! next.
//!
//! **Reversal.** A phase that a later unit runs for each declaration, such as
//! the compile step, samples each declaration too. When the pool adds each
//! fork job's allocations to the thread that forked it (#6537), a phase's
//! allocations hold those of its fork jobs.
//!
//! # What it does not cover
//!
//! The allocation count is the count of the thread that runs the phase, so the
//! molding jobs of a parse on the pool's other threads are not in it; #6537
//! adds them. A process that installs no counting allocator counts no
//! allocation, and each of its samples says so
//! ([`metered::Absent::Unmetered`]). The hub compiles no declaration, so no
//! phase names a compile step yet.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-layers decides the timings layer and its cost; §
//!   engine-surface-items keeps p50 and p99 over the last 32 rechecks in the
//!   account row.

use alloc::vec::Vec;
use core::time::Duration;
use std::time::Instant;

use anodized::spec;
use gandr_core_checker::bridge::AllocationCount;
use gandr_core_checker::bridge::Meter as _;
use gandr_core_checker::bridge::Spent;
use gandr_core_checker::bridge::metered;
use gandr_core_incremental::Adoption;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_dispatcher::Allocations;
use gandr_surface_dispatcher::Positioning;
use quenchant_shape::shape::Maybe;

use crate::instrument::Instrument;
use crate::instrument::Phase;

quenchant_shape::reason_enum! {
    /// Why a sink answers no timing column, or a ring or a row no sample.
    pub mod untimed {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The sink's layer is not the timings layer.
            Unselected,
            /// No run of the phase was sampled.
            Unsampled,
        }
    }
}

/// How many samples a ring keeps: the window of its p50 and its p99.
pub const WINDOW: usize = 32;

/// How many samples a ring holds, or a fold read: at most [`WINDOW`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SampleCount(usize);

impl From<SampleCount> for usize
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: SampleCount) -> Self
    {
        count.0
    }
}

/// The last [`WINDOW`] samples of one phase, the oldest overwritten first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: holds the last `min(n, WINDOW)` of the `n` samples pushed, in the
///   order they were pushed.
/// - provides: the window that [`SampleRing::spread`] folds.
/// - panics: none.
/// - executable: none — the ring has no call boundary of its own; its methods
///   carry the predicates.
///
/// # Adequacy
/// - hypothesis: L2 — every sequence of up to 80 generated samples reads back
///   its last 32 in order, and folds to the nearest-rank p50 and p99 of a
///   sorted copy of them.
/// - witness: `tests::timings::a_ring_folds_its_last_window_into_its_p50_and_p99`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SampleRing
{
    /// The samples, the slot `next` the oldest once the ring is full.
    samples: [Spent; WINDOW],
    /// The slot the next sample is written to.
    next: usize,
    /// How many slots hold a sample: at most [`WINDOW`].
    held: usize,
}

impl Default for SampleRing
{
    /// An empty ring.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        let empty = Spent::new(Duration::ZERO, Maybe::Absent(metered::Absent::Unmetered));
        Self {
            samples: [empty; WINDOW],
            next: 0,
            held: 0,
        }
    }
}

/// The p50 and the p99 of one quantity over a ring, each by its nearest rank.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Percentiles<T>
{
    /// The value at rank `ceil(n / 2)` of the `n` sorted values.
    p50: T,
    /// The value at rank `ceil(99 n / 100)` of the `n` sorted values.
    p99: T,
}

impl<T> Percentiles<T>
where
    T: Copy,
{
    /// The p50.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn p50(&self) -> T
    {
        self.p50
    }

    /// The p99.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn p99(&self) -> T
    {
        self.p99
    }
}

/// What a ring folds to: its wall's p50 and p99, its allocations' p50 and
/// p99 when each of its samples counted them, and the window they span.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Spread
{
    /// How many samples the fold read.
    held: usize,
    /// The wall's percentiles.
    wall: Percentiles<Duration>,
    /// The allocations' percentiles, or why a sample counted none.
    allocations: Maybe<Percentiles<AllocationCount>, metered::Absent>,
}

impl Spread
{
    /// How many samples the fold read: the window of the percentiles.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn held(&self) -> SampleCount
    {
        SampleCount(self.held)
    }

    /// The wall's p50 and p99.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wall(&self) -> Percentiles<Duration>
    {
        self.wall
    }

    /// The allocations' p50 and p99, or why a sample counted none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn allocations(&self) -> Maybe<Percentiles<AllocationCount>, metered::Absent>
    {
        self.allocations
    }
}

/// The p50 and the p99 of `values`, each by its nearest rank: two selections,
/// and no sort.
///
/// # Specification
/// - requires: `values` is not empty.
/// - ensures: the values at ranks `ceil(n / 2)` and `ceil(99 n / 100)` of
///   `values` sorted, `n` its length; `values` is permuted.
/// - panics: none: each rank is at least one and at most `n`.
///
/// # Adequacy
/// - hypothesis: L2 — as [`SampleRing`].
/// - witness: `tests::timings::a_ring_folds_its_last_window_into_its_p50_and_p99`
#[spec(requires: !values.is_empty())]
fn percentiles<T>(values: &mut [T]) -> Percentiles<T>
where
    T: Copy + Ord,
{
    let rank = |percent: usize| {
        values
            .len()
            .saturating_mul(percent)
            .div_ceil(100)
            .saturating_sub(1)
    };
    let (p50, p99) = (rank(50), rank(99));
    let p99 = *values.select_nth_unstable(p99).1;
    let p50 = *values.select_nth_unstable(p50).1;
    Percentiles { p50, p99 }
}

impl SampleRing
{
    /// Keep `sample`, in place of the oldest one when the ring is full: one
    /// write into the array, and no allocation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the ring holds one more sample, up to [`WINDOW`], and
    ///   `sample` is its latest.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`SampleRing`].
    /// - witness: `tests::timings::a_ring_folds_its_last_window_into_its_p50_and_p99`
    #[spec(captures: [before = self.held],
        ensures: self.held == before.saturating_add(1).min(WINDOW)
            && self.latest() == Maybe::Present(sample))]
    #[inline]
    pub fn push(
        &mut self,
        sample: Spent,
    )
    {
        if let Some(slot) = self.samples.get_mut(self.next) {
            *slot = sample;
        }
        let next = self.next.saturating_add(1);
        self.next = if next < WINDOW { next } else { 0 };
        self.held = self.held.saturating_add(1).min(WINDOW);
    }

    /// How many samples the ring holds: at most [`WINDOW`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn held(&self) -> SampleCount
    {
        SampleCount(self.held)
    }

    /// The samples the ring holds, the oldest first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`SampleRing::held`] samples, in the order they were pushed.
    /// - panics: none.
    /// - executable: none — the result is a lazy iterator, so the call returns
    ///   no value that a predicate reads.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`SampleRing`].
    /// - witness: `tests::timings::a_ring_folds_its_last_window_into_its_p50_and_p99`
    #[inline]
    pub fn samples(&self) -> impl Iterator<Item = Spent> + '_
    {
        let start = if self.held < WINDOW { 0 } else { self.next };
        self.samples
            .iter()
            .cycle()
            .skip(start)
            .take(self.held)
            .copied()
    }

    /// The latest sample, or [`untimed::Absent::Unsampled`] when the ring
    /// holds none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn latest(&self) -> Maybe<Spent, untimed::Absent>
    {
        if self.held == 0 {
            return Maybe::Absent(untimed::Absent::Unsampled);
        }
        self.samples
            .get(self.next.checked_sub(1).unwrap_or(WINDOW.saturating_sub(1)))
            .copied()
            .map_or(Maybe::Absent(untimed::Absent::Unsampled), Maybe::Present)
    }

    /// The ring folded into its p50 and its p99: by four selections over a
    /// copy of the ring on the stack, never a sort, and no allocation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`untimed::Absent::Unsampled`] for an empty ring; otherwise
    ///   the nearest-rank p50 and p99 of the walls it holds, and of their
    ///   allocations when each sample counted them, else
    ///   [`metered::Absent::Unmetered`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`SampleRing`].
    /// - witness: `tests::timings::a_ring_folds_its_last_window_into_its_p50_and_p99`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(ref spread) if spread.held == self.held)
        == (self.held > 0))]
    #[inline]
    pub fn spread(&self) -> Maybe<Spread, untimed::Absent>
    {
        let mut walls = [Duration::ZERO; WINDOW];
        let mut counts = [AllocationCount::default(); WINDOW];
        let mut counted = true;
        for ((wall, count), sample) in walls.iter_mut().zip(counts.iter_mut()).zip(self.samples()) {
            *wall = sample.wall();
            match sample.allocations() {
                Maybe::Present(allocations) => *count = allocations,
                Maybe::Absent(_) => counted = false,
            }
        }
        let (Some(walls), Some(counts)) =
            (walls.get_mut(.. self.held), counts.get_mut(.. self.held))
        else {
            return Maybe::Absent(untimed::Absent::Unsampled);
        };
        if walls.is_empty() {
            return Maybe::Absent(untimed::Absent::Unsampled);
        }
        Maybe::Present(Spread {
            held: self.held,
            wall: percentiles(walls),
            allocations: if counted {
                Maybe::Present(percentiles(counts))
            }
            else {
                Maybe::Absent(metered::Absent::Unmetered)
            },
        })
    }
}

/// One ring for each phase of a document.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PhaseRings
{
    /// The parse's samples.
    parse: SampleRing,
    /// The lowering's samples.
    lower: SampleRing,
    /// The judgement's samples.
    judge: SampleRing,
    /// The admission's samples.
    admit: SampleRing,
}

impl PhaseRings
{
    /// The ring of `phase`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ring(
        &self,
        phase: Phase,
    ) -> &SampleRing
    {
        match phase {
            Phase::Parse => &self.parse,
            Phase::Lower => &self.lower,
            Phase::Judge => &self.judge,
            Phase::Admit => &self.admit,
        }
    }

    /// Keep `sample` in the ring of `phase`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn push(
        &mut self,
        phase: Phase,
        sample: Spent,
    )
    {
        match phase {
            Phase::Parse => self.parse.push(sample),
            Phase::Lower => self.lower.push(sample),
            Phase::Judge => self.judge.push(sample),
            Phase::Admit => self.admit.push(sample),
        }
    }
}

/// The rings of one declaration: one for each phase that runs for each
/// declaration.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RowRings
{
    /// The samples of the incremental pass's judgement of the declaration.
    judge: SampleRing,
    /// The samples of the kernel's admission of the declaration.
    admit: SampleRing,
}

impl RowRings
{
    /// The samples of the incremental pass's judgement of the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn judge(&self) -> &SampleRing
    {
        &self.judge
    }

    /// The samples of the kernel's admission of the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admit(&self) -> &SampleRing
    {
        &self.admit
    }

    /// Keep `sample` of the declaration's judgement.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn judged(
        &mut self,
        sample: Spent,
    )
    {
        self.judge.push(sample);
    }

    /// Keep `sample` of the declaration's admission.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn admitted(
        &mut self,
        sample: Spent,
    )
    {
        self.admit.push(sample);
    }
}

/// The clock's and the meter's readings at one boundary.
#[derive(Clone, Copy, Debug)]
struct Reading
{
    /// The clock's reading.
    at: Instant,
    /// The thread's running allocation count, when the process counts it.
    allocations: Maybe<AllocationCount, metered::Absent>,
}

impl Reading
{
    /// The readings now: the clock's, and `meter`'s when the process counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn now(meter: Maybe<Allocations, metered::Absent>) -> Self
    {
        Self {
            at: Instant::now(),
            allocations: meter.map(|mut meter| meter.allocations()),
        }
    }

    /// What the span from `earlier` to this reading spent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn since(
        self,
        earlier: Self,
    ) -> Spent
    {
        Spent::new(
            self.at.saturating_duration_since(earlier.at),
            match (self.allocations, earlier.allocations) {
                (Maybe::Present(now), Maybe::Present(then)) => Maybe::Present(now.since(then)),
                (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => Maybe::Absent(reason),
            },
        )
    }
}

/// One phase's span in a column: the readings at its entry while it runs,
/// and its sample once it ends.
#[derive(Clone, Copy, Debug)]
struct Span
{
    /// The readings at the entry, while the phase runs.
    entered: Maybe<Reading, untimed::Absent>,
    /// The sample, once the phase ended.
    sample: Maybe<Spent, untimed::Absent>,
}

/// The span of no phase.
const UNSPANNED: Span = Span {
    entered: Maybe::Absent(untimed::Absent::Unsampled),
    sample: Maybe::Absent(untimed::Absent::Unsampled),
};

/// The span of each phase of a column.
#[derive(Clone, Copy, Debug)]
struct Spans
{
    /// The parse's span.
    parse: Span,
    /// The lowering's span.
    lower: Span,
    /// The judgement's span.
    judge: Span,
    /// The admission's span.
    admit: Span,
}

impl Spans
{
    /// The span of `phase`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn of(
        &self,
        phase: Phase,
    ) -> &Span
    {
        match phase {
            Phase::Parse => &self.parse,
            Phase::Lower => &self.lower,
            Phase::Judge => &self.judge,
            Phase::Admit => &self.admit,
        }
    }

    /// The span of `phase`, to change.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn of_mut(
        &mut self,
        phase: Phase,
    ) -> &mut Span
    {
        match phase {
            Phase::Parse => &mut self.parse,
            Phase::Lower => &mut self.lower,
            Phase::Judge => &mut self.judge,
            Phase::Admit => &mut self.admit,
        }
    }
}

/// What one job of a recheck sampled: each phase of the document it ran, and
/// each item its incremental pass judged.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a phase entered then left holds one sample; an item judged
///   between two boundaries of the pass holds one sample; an item adopted holds
///   none.
/// - provides: what the account takes into its rings when the job ends.
/// - panics: none.
/// - executable: none — the column has no call boundary of its own; its methods
///   carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Timings`].
/// - witness: `tests::timings::a_recheck_samples_each_phase_and_each_judged_declaration`
#[derive(Clone, Debug)]
pub struct TimingColumn
{
    /// The meter of the process's allocations, or why none counts them.
    meter: Maybe<Allocations, metered::Absent>,
    /// The span of each phase entered.
    spans: Spans,
    /// The readings at the end of the pass's last item, or at its start.
    boundary: Maybe<Reading, untimed::Absent>,
    /// Each item the pass judged, by its position, with its sample, in the
    /// pass's order.
    judged: Vec<(ConstantIndex, Spent)>,
}

impl TimingColumn
{
    /// An empty column, reading `meter` when the process counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    const fn new(meter: Maybe<Allocations, metered::Absent>) -> Self
    {
        Self {
            meter,
            spans: Spans {
                parse: UNSPANNED,
                lower: UNSPANNED,
                judge: UNSPANNED,
                admit: UNSPANNED,
            },
            boundary: Maybe::Absent(untimed::Absent::Unsampled),
            judged: Vec::new(),
        }
    }

    /// `phase` starts: read the clock and the meter.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entered(
        &mut self,
        phase: Phase,
    )
    {
        let reading = Reading::now(self.meter);
        self.spans.of_mut(phase).entered = Maybe::Present(reading);
    }

    /// `phase` ends: read the clock and the meter, and keep the phase's
    /// sample when it was entered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn left(
        &mut self,
        phase: Phase,
    )
    {
        let reading = Reading::now(self.meter);
        let span = self.spans.of_mut(phase);
        if let Maybe::Present(start) = span.entered {
            span.sample = Maybe::Present(reading.since(start));
            span.entered = Maybe::Absent(untimed::Absent::Unsampled);
        }
    }

    /// The incremental pass starts its first item: read the clock and the
    /// meter.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn opened(&mut self)
    {
        self.boundary = Maybe::Present(Reading::now(self.meter));
    }

    /// The incremental pass passed the item at `constant`: read the clock and
    /// the meter once, and keep the item's sample when the pass judged it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one more sample at `constant` when `adoption` is
    ///   [`Adoption::Judged`] and the pass opened, none otherwise; the next
    ///   item's span starts here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Timings`].
    /// - witness: `tests::timings::a_recheck_samples_each_phase_and_each_judged_declaration`
    #[spec(captures: [before = self.judged.len(), opened = matches!(self.boundary, Maybe::Present(_))],
        ensures: self.judged.len() == before.saturating_add(usize::from(adoption == Adoption::Judged && opened)))]
    #[inline]
    pub(crate) fn passed(
        &mut self,
        constant: ConstantIndex,
        adoption: Adoption,
    )
    {
        let reading = Reading::now(self.meter);
        if let (Adoption::Judged, Maybe::Present(start)) = (adoption, self.boundary) {
            self.judged.push((constant, reading.since(start)));
        }
        self.boundary = Maybe::Present(reading);
    }

    /// The sample of `phase`, or [`untimed::Absent::Unsampled`] when the job
    /// did not run it whole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn sample(
        &self,
        phase: Phase,
    ) -> Maybe<Spent, untimed::Absent>
    {
        self.spans.of(phase).sample
    }

    /// Each item the incremental pass judged, by its position, with its
    /// sample, in the pass's order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn judged(&self) -> &[(ConstantIndex, Spent)]
    {
        &self.judged
    }
}

/// The sink of the timings layer: one column of samples for each job of a
/// recheck.
///
/// A hub makes one for each job of a recheck, so each column starts empty. It
/// reads the meter only when the process counts its allocations
/// ([`gandr_surface_dispatcher::counting`]).
///
/// # Specification
/// - requires: a sink observes. It never changes a verdict, a report or the
///   session's state, the account's rings aside.
/// - ensures: after a judgement, the column holds a sample of the parse, the
///   lowering and the judgement, and one of each item the incremental pass
///   judged; after an admission, a sample of the admission, and the admission
///   records what each crossed declaration spent.
/// - provides: the samples the account takes into its rings.
/// - panics: none.
/// - executable: none — the sink's effects are the session's; the witness reads
///   them through the account.
///
/// # Adequacy
/// - hypothesis: L3 — a corpus source rechecked twice at this sink reads one
///   more sample of each phase of the document after each recheck, one
///   judgement sample of each declaration, because the second recheck adopts
///   each item, and one admission sample of each declaration for each admission
///   that crossed it.
/// - witness: `tests::timings::a_recheck_samples_each_phase_and_each_judged_declaration`
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Timings
{
    /// The column of the job.
    column: TimingColumn,
}

impl Default for Timings
{
    /// A sink with an empty column, which reads the meter when the process
    /// counts its allocations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            column: TimingColumn::new(gandr_surface_dispatcher::counting()),
        }
    }
}

impl Timings
{
    /// The column of the job.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn column(&self) -> &TimingColumn
    {
        &self.column
    }
}

impl Instrument for Timings
{
    /// Read the clock and the meter at the start of `phase`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entered(
        &mut self,
        phase: Phase,
    )
    {
        self.column.entered(phase);
    }

    /// Read the clock and the meter at the end of `phase`, and keep its
    /// sample.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn left(
        &mut self,
        phase: Phase,
    )
    {
        self.column.left(phase);
    }

    /// The column of the job.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn timings(&mut self) -> Maybe<&mut TimingColumn, untimed::Absent>
    {
        Maybe::Present(&mut self.column)
    }

    /// Each crossed declaration's position, census and wall, and its
    /// allocations when the process counts them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn positioning(&self) -> Positioning
    {
        match self.column.meter {
            Maybe::Present(_) => Positioning::Metered,
            Maybe::Absent(_) => Positioning::Positioned,
        }
    }
}
