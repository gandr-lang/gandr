//! Standing-pool latency and throughput with independently verified job
//! results.
//!
//! Each stream contains exactly 25 batches of each selected family. Task grain
//! groups consecutive family instances; partial final tasks are not padded.
//! Stream time per family is amortized throughput, not single-family latency.
//! The latter is measured separately, including dispatch and collection.
//!
//! # Width sweep
//!
//! `GANDR_SWEEP=1` replaces the transport matrix with one fixed transport —
//! `rtrb` busy polling, batch publication, drain 32, member grain — swept over
//! 1 to 12 workers, with the dispatcher spinning on the result rings or
//! executing one round-robin shard itself. Each family is measured alone as
//! 25 sequential single-family exchanges under three judgments: minting rows
//! over per-instance consumer clones (the original row), lookup-only rows over
//! one binding shared by reference, and empty jobs (the hand-off floor). After
//! the timed exchanges, each cell repeats every exchange once with allocation
//! counting on, on every executing thread; `heap` is the number of heap
//! allocations those rows made. `SWEEP-SERIAL` reports the serial costs the
//! bound divides by: the fast and reference schema checks, plain replay, both
//! row shapes, the largest member of each, and the allocations of one warm
//! serial pass of each row shape.

use alloc::sync::Arc;
use std::io::Write as _;

use super::Admission;
use super::Arena;
use super::Budget;
use super::Case;
use super::Choice;
use super::Consumer;
use super::Duration;
use super::Instant;
use super::Natural;
use super::Proposal;
use super::Refusal;
use super::Row;
use super::Schema;
use super::StageError;
use super::Step;
use super::Threads;
use super::Work;
use super::io;
use super::lookup;
use super::minting;
use super::plain;
use super::queues::Kind;
use super::queues::Publication;
use super::queues::Share;
use super::queues::Wake;
use super::queues::Wire;
use super::queues::standing;

/// An admitted family and independently measured reference observations.
pub(super) struct Workload
{
    /// Fixture label.
    pub case: Case,
    /// Family ordinal within that fixture.
    pub index: Natural,
    /// Original materialized terms, never shared mutably.
    pub arena: Arena,
    /// Immutable checked schema.
    pub schema: Schema,
    /// The producer's proposal, for repeated schema timing.
    pub proposal: Proposal,
    /// Equations in original producer order.
    pub members: Vec<Step>,
    /// Guard choices in corresponding order.
    pub rows: Vec<Vec<Choice>>,
    /// Schema preparation duration.
    pub schema_time: Duration,
    /// One-time fixed-content binding duration, excluding the arena clone.
    pub binding_time: Duration,
    /// Largest individually observed serial admission.
    pub largest: Duration,
}

/// Which independent judgment a task runs.
#[derive(Clone, Copy, Debug)]
pub(super) enum Mode
{
    /// Unchanged local rule replay.
    Plain,
    /// The original row: guard validation into fresh vectors and instance
    /// records interned into a per-instance consumer clone.
    Minting,
    /// Guard validation into reused buffers and exact lookup in one binding
    /// shared by every worker.
    Lookup,
    /// One empty job per member: the hand-off floor.
    Empty,
    /// A different rule must be refused, independently of scheduling.
    PoisonRule,
}

impl Mode
{
    /// Stable label for output rows.
    ///
    /// # Specification
    /// trivial.
    fn label(self) -> super::queues::Label
    {
        super::queues::Label(match self {
            | Self::Plain => "plain",
            | Self::Minting => "minting",
            | Self::Lookup => "lookup",
            | Self::Empty => "empty",
            | Self::PoisonRule => "poison-rule",
        })
    }
}

/// Task granularity, independent of transport publication.
#[derive(Clone, Copy)]
enum Grain
{
    /// One equation per task.
    Member,
    /// One or more consecutive complete family instances.
    Families(Natural),
}

impl Grain
{
    /// Stable label for output rows.
    ///
    /// # Specification
    /// trivial.
    fn label(self) -> super::queues::Label
    {
        super::queues::Label(match self {
            | Self::Member => "member",
            | Self::Families(Natural(1)) => "family",
            | Self::Families(Natural(4)) => "families4",
            | Self::Families(_) => "families16",
        })
    }
}

/// Whether a task counts the heap allocations its rows make.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Census
{
    /// Rows run unobserved; timed exchanges use this.
    Off,
    /// Rows run inside a thread-local allocation count.
    On,
}

/// Copy-sized job descriptor; arenas remain worker-owned outside queues.
#[derive(Clone, Copy, Debug)]
pub(super) struct Task
{
    /// Dense identity used to detect duplicate or missing completions.
    id: Natural,
    /// Half-open interval of repeated family instances.
    instances: [Natural; 2],
    /// Half-open member interval; upper bound is clamped to each family.
    members: [Natural; 2],
    /// Judgment selected for the whole measurement.
    mode: Mode,
    /// Whether the executing thread counts the rows' allocations.
    census: Census,
}

/// Queue protocol shared by all transports.
#[derive(Clone, Copy, Debug)]
pub(super) enum Command
{
    /// Execute a real job.
    Run(Task),
    /// Return an empty job with its identity intact.
    Ping(Natural),
    /// Stop one worker after all receipts have been collected.
    Stop,
}

/// Semantic counters, including the exact number of equations processed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct Stats
{
    /// Equations processed.
    members: usize,
    /// Ordinary replay budget consumed.
    fuel: usize,
    /// Materialized side records inspected.
    comparisons: usize,
    /// Row choices checked.
    choices: usize,
    /// Changed records instantiated or located.
    instantiations: usize,
    /// Materialized classifier records inspected.
    classifiers: usize,
}

/// Preserve the originating judgment's refusal in a worker receipt.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Failure
{
    /// Malformed observer coordinate.
    Coordinate,
    /// Unchanged replay refusal.
    Plain(StageError),
    /// Guarded judgment refusal.
    Admission(Refusal),
}

/// The allocations a task's rows made, when they were counted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Heap
{
    /// The task ran without a census.
    Uncounted,
    /// Heap allocations made by the executing thread during the task.
    Counted(u64),
}

/// One completed job, not merely a wakeup or completion count.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Receipt
{
    /// Echoed identity, validated before the next measurement.
    pub id: Natural,
    /// Exact counters or originating refusal.
    pub result: Result<Stats, Failure>,
    /// The task's allocation census; never part of the differential.
    pub heap: Heap,
}

impl Receipt
{
    /// Empty-job receipt used for warmup and ping-pong.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn empty(id: Natural) -> Self
    {
        Self {
            id,
            result: Ok(Stats {
                members: 0,
                fuel: 0,
                comparisons: 0,
                choices: 0,
                instantiations: 0,
                classifiers: 0,
            }),
            heap: Heap::Uncounted,
        }
    }
}

/// Worker-owned scratch, cloned before any timed dispatch.
#[derive(Clone)]
pub(super) enum Scratch<'schema>
{
    /// Ordinary replay arenas, one per family instance.
    Plain(Vec<Arena>),
    /// Bound schema namespaces, one per family instance, and the row buffers.
    Minting(Vec<Consumer<'schema>>, Row),
    /// One binding per family shared by every clone, and private row buffers.
    Lookup(Arc<[Consumer<'schema>]>, Row),
    /// No scratch.
    Empty,
}

impl<'schema> Scratch<'schema>
{
    /// Prepare all 25 batches, importing fixed content once before cloning.
    ///
    /// # Specification
    /// - ensures: only the selected judgment's scratch is allocated; lookup
    ///   bindings are shared by every clone of the scratch.
    /// - fails: schema binding refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the originating admission refusal.
    pub(super) fn new(
        workload: &'schema [Workload],
        mode: Mode,
    ) -> Result<Self, Refusal>
    {
        let bindings = || {
            workload
                .iter()
                .map(|family| {
                    family
                        .schema
                        .bind(family.arena.clone(), &mut Budget(10_000_000))
                })
                .collect::<Result<Vec<_>, _>>()
        };
        match mode {
            | Mode::Plain => Ok(Self::Plain(
                (0 .. 25)
                    .flat_map(|_| workload.iter().map(|family| family.arena.clone()))
                    .collect(),
            )),
            | Mode::Minting | Mode::PoisonRule => {
                let consumers = bindings()?;
                Ok(Self::Minting(
                    (0 .. 25).flat_map(|_| consumers.iter().cloned()).collect(),
                    Row::default(),
                ))
            },
            | Mode::Lookup => Ok(Self::Lookup(Arc::from(bindings()?), Row::default())),
            | Mode::Empty => Ok(Self::Empty),
        }
    }

    /// Execute the selected real judgment over exactly the task's ranges.
    ///
    /// # Specification
    /// - requires: scratch was prepared for the task's judgment.
    /// - ensures: preserves the originating refusal and every declared counter.
    /// - fails: invalid observer coordinate, replay refusal, or admission
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns Failure without manufacturing a successful observation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — serial receipts detect scheduling-dependent work or
    ///   verdicts.
    /// - witness: `template::tests::compressed_admission_matches_plain_families`
    pub(super) fn execute(
        &mut self,
        task: Task,
        workload: &[Workload],
    ) -> Result<Stats, Failure>
    {
        let mut stats = Stats::default();
        for instance in task.instances[0].0 .. task.instances[1].0 {
            let index = instance
                .checked_rem(workload.len())
                .ok_or(Failure::Coordinate)?;
            let family = workload.get(index).ok_or(Failure::Coordinate)?;
            let end = task.members[1].0.min(family.members.len());
            let members = family
                .members
                .get(task.members[0].0 .. end)
                .ok_or(Failure::Coordinate)?;
            let rows = family
                .rows
                .get(task.members[0].0 .. end)
                .ok_or(Failure::Coordinate)?;
            for (step, choices) in members.iter().zip(rows) {
                let step = if matches!(task.mode, Mode::PoisonRule) {
                    Step {
                        rule: gandr_kernel_term::stage::Rule::Congruence,
                        ..*step
                    }
                }
                else {
                    *step
                };
                let admission = match *self {
                    | Self::Plain(ref mut arenas) => {
                        let arena = arenas.get_mut(instance).ok_or(Failure::Coordinate)?;
                        let Work(fuel) = plain(arena, step).map_err(Failure::Plain)?;
                        stats.fuel = stats.fuel.saturating_add(fuel);
                        Admission::default()
                    },
                    | Self::Minting(ref mut consumers, ref mut row) => {
                        let consumer = consumers.get_mut(instance).ok_or(Failure::Coordinate)?;
                        minting(&family.schema, consumer, choices, step, row)
                            .map_err(Failure::Admission)?
                    },
                    | Self::Lookup(ref consumers, ref mut row) => {
                        let consumer = consumers.get(index).ok_or(Failure::Coordinate)?;
                        lookup(&family.schema, consumer, choices, step, row)
                            .map_err(Failure::Admission)?
                    },
                    | Self::Empty => Admission::default(),
                };
                stats.comparisons = stats.comparisons.saturating_add(admission.comparisons.0);
                stats.choices = stats.choices.saturating_add(admission.choices.0);
                stats.instantiations = stats
                    .instantiations
                    .saturating_add(admission.instantiations.0);
                stats.classifiers = stats.classifiers.saturating_add(admission.classifiers.0);
                stats.members = stats.members.saturating_add(1);
            }
        }
        Ok(stats)
    }
}

/// Execute one protocol command and preserve its identity.
///
/// # Specification
/// - requires: command is not Stop; Stop is consumed by the worker loop.
/// - ensures: empty jobs do no kernel work; real jobs return their exact
///   result; a census task also reports the executing thread's allocations.
/// - panics: none.
pub(super) fn execute(
    command: Command,
    scratch: &mut Scratch<'_>,
    workload: &[Workload],
) -> Receipt
{
    match command {
        | Command::Run(task) => match task.census {
            | Census::Off => Receipt {
                id: task.id,
                result: scratch.execute(task, workload),
                heap: Heap::Uncounted,
            },
            | Census::On => {
                let mut result = Err(Failure::Coordinate);
                let counted = allocation_counter::measure(|| {
                    result = scratch.execute(task, workload);
                });
                Receipt {
                    id: task.id,
                    result,
                    heap: Heap::Counted(counted.count_total),
                }
            },
        },
        | Command::Ping(id) => Receipt::empty(id),
        | Command::Stop => Receipt {
            id: Natural(usize::MAX),
            result: Err(Failure::Coordinate),
            heap: Heap::Uncounted,
        },
    }
}

/// Build a dense, ordered task list for the chosen range and grain.
///
/// # Specification
/// - ensures: every selected member occurs once, with no padded family batches.
/// - panics: none.
fn tasks(
    workload: &[Workload],
    instances: [Natural; 2],
    grain: Grain,
    mode: Mode,
    census: Census,
) -> Vec<Command>
{
    let mut tasks = Vec::new();
    match grain {
        | Grain::Member => {
            for instance in instances[0].0 .. instances[1].0 {
                let count = instance
                    .checked_rem(workload.len())
                    .and_then(|index| workload.get(index))
                    .map_or(0, |family| family.members.len());
                for member in 0 .. count {
                    tasks.push(Command::Run(Task {
                        id: Natural(tasks.len()),
                        instances: [Natural(instance), Natural(instance.saturating_add(1))],
                        members: [Natural(member), Natural(member.saturating_add(1))],
                        mode,
                        census,
                    }));
                }
            }
        },
        | Grain::Families(count) => {
            for start in (instances[0].0 .. instances[1].0).step_by(count.0) {
                tasks.push(Command::Run(Task {
                    id: Natural(tasks.len()),
                    instances: [
                        Natural(start),
                        Natural(start.saturating_add(count.0).min(instances[1].0)),
                    ],
                    members: [Natural(0), Natural(usize::MAX)],
                    mode,
                    census,
                }));
            }
        },
    }
    tasks
}

/// Independently evaluate the entire task list before starting any pool.
///
/// # Specification
/// - ensures: expected receipts include both task identity and semantic work.
/// - panics: none.
fn oracle(
    workload: &[Workload],
    tasks: &[Command],
    scratch: &mut Scratch<'_>,
) -> Vec<Receipt>
{
    tasks
        .iter()
        .map(|command| execute(*command, scratch, workload))
        .collect()
}

/// Reject duplicate, missing or changed results after timing stops.
///
/// # Specification
/// - ensures: sorted receipt identities and results equal the serial or
///   specified refusal oracle; allocation censuses are not compared.
/// - fails: any changed identity, refusal or work counter.
/// - panics: none.
///
/// # Errors
/// Returns invalid data for an observer differential failure.
fn verify(
    actual: &mut [Receipt],
    expected: &[Receipt],
) -> io::Result<()>
{
    actual.sort_unstable_by_key(|receipt| receipt.id);
    if actual.len() != expected.len()
        || actual
            .iter()
            .zip(expected)
            .any(|(actual, expected)| (actual.id, actual.result) != (expected.id, expected.result))
    {
        return Err(io::Error::other(
            "handoff verdict, identity or work differential",
        ));
    }
    Ok(())
}

/// An amortized stream or sequential single-family latency measurement.
#[derive(Clone, Copy)]
enum Schedule
{
    /// Submit all 25 batches together, packing family grain across batches.
    Stream,
    /// Submit and collect each family batch before the next starts.
    Latency,
}

/// One measured cell: every exchange's wall time and the rows' allocations.
struct Cell
{
    /// Wall time per timed exchange, in submission order.
    elapsed: Vec<Duration>,
    /// Allocations counted by the census exchanges, or none taken.
    heap: Heap,
}

/// Measure one transport/grain/mode with preparation and validation excluded.
///
/// # Specification
/// - ensures: exactly 25 batches per family; startup, clones and oracles
///   excluded. With a census, every batch is exchanged once more after the
///   timed batches with allocation counting on, and the counts are summed.
/// - fails: transport or semantic differential failure.
/// - panics: none.
///
/// # Errors
/// Returns the transport or differential error.
///
/// # Adequacy
/// - hypothesis: L2 — every matrix cell preserves complete serial receipts.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
fn measure(
    workload: &[Workload],
    wire: Wire,
    threads: Threads,
    grain: Grain,
    mode: Mode,
    schedule: Schedule,
    census: Census,
) -> io::Result<Cell>
{
    let count = workload.len().saturating_mul(25);
    let span = match schedule {
        | Schedule::Stream => count,
        | Schedule::Latency => 1,
    };
    let mut scratch = Scratch::new(workload, mode).map_err(io::Error::other)?;
    let batches: Vec<_> = (0 .. count)
        .step_by(span.max(1))
        .map(|start| {
            let range = [
                Natural(start),
                Natural(start.saturating_add(span).min(count)),
            ];
            let jobs = tasks(workload, range, grain, mode, Census::Off);
            let counted = tasks(workload, range, grain, mode, census);
            let expected = oracle(workload, &jobs, &mut scratch);
            if expected.iter().any(|receipt| receipt.result.is_err()) {
                return Err(io::Error::other(
                    "serial reference refused measured workload",
                ));
            }
            Ok((jobs, counted, expected))
        })
        .collect::<io::Result<Vec<_>>>()?;
    let mut elapsed = Vec::with_capacity(batches.len());
    let mut heap = Heap::Uncounted;
    standing(wire, threads, workload, mode, |pool| {
        let waves: Vec<_> = batches
            .iter()
            .map(|batch| (pool.prepare(&batch.0), pool.prepare(&batch.1)))
            .collect();
        let mut receipts = Vec::with_capacity(
            batches
                .iter()
                .map(|batch| batch.0.len())
                .max()
                .unwrap_or_default(),
        );
        for (batch, wave) in batches.iter().zip(&waves) {
            receipts.clear();
            let start = Instant::now();
            pool.exchange(&wave.0, &mut receipts)?;
            elapsed.push(start.elapsed());
            verify(&mut receipts, &batch.2)?;
        }
        if census == Census::On {
            let mut total = 0_u64;
            for (batch, wave) in batches.iter().zip(&waves) {
                receipts.clear();
                pool.exchange(&wave.1, &mut receipts)?;
                verify(&mut receipts, &batch.2)?;
                for receipt in &receipts {
                    if let Heap::Counted(count) = receipt.heap {
                        total = total.saturating_add(count);
                    }
                }
            }
            heap = Heap::Counted(total);
        }
        Ok(())
    })?;
    Ok(Cell { elapsed, heap })
}

/// Measure empty-job round trips; output both round-trip and half-trip
/// estimates.
///
/// # Specification
/// - ensures: reports nearest-rank median/p99 from 10,000 validated round
///   trips.
/// - fails: transport, echo or output failure.
/// - panics: none.
///
/// # Errors
/// Returns I/O or invalid-data errors.
fn latency(
    output: &mut io::BufWriter<io::StdoutLock<'_>>,
    wire: Wire,
) -> io::Result<()>
{
    let mut samples = Vec::with_capacity(10_000);
    standing(wire, Threads(1), &[], Mode::Plain, |pool| {
        let wave = pool.prepare(&[Command::Ping(Natural(0))]);
        let mut receipts = Vec::with_capacity(1);
        for index in 0_usize .. 10_100 {
            receipts.clear();
            let start = Instant::now();
            pool.exchange(&wave, &mut receipts)?;
            let elapsed = start.elapsed();
            if receipts != [Receipt::empty(Natural(0))] {
                return Err(io::Error::other("empty job echo mismatch"));
            }
            if index >= 100 {
                samples.push(elapsed.as_nanos());
            }
        }
        Ok(())
    })?;
    samples.sort_unstable();
    let median = samples.get(4_999).ok_or(io::ErrorKind::InvalidData)?;
    let p99 = samples.get(9_899).ok_or(io::ErrorKind::InvalidData)?;
    writeln!(
        output,
        "HANDOFF-PING,{},publication={},drain={},samples=10000,rtt_median_ns={median},rtt_p99_ns={p99}",
        wire.kind.label(),
        wire.publication.label(),
        wire.drain.0
    )
}

/// Exercise refused equations through every real transport before timing.
///
/// # Specification
/// - ensures: changed rules return `SidesMismatch` at all worker counts.
/// - fails: any transport or refusal differential.
/// - panics: none.
///
/// # Errors
/// Returns I/O or differential errors.
fn refusals(
    workload: &[Workload],
    wire: Wire,
    threads: Threads,
) -> io::Result<()>
{
    let family = workload.first().ok_or(io::ErrorKind::InvalidInput)?;
    let workload = core::slice::from_ref(family);
    let jobs = tasks(
        workload,
        [Natural(0), Natural(25)],
        Grain::Families(Natural(1)),
        Mode::PoisonRule,
        Census::Off,
    );
    let expected: Vec<_> = (0 .. 25)
        .map(|id| Receipt {
            id: Natural(id),
            result: Err(Failure::Admission(Refusal::SidesMismatch)),
            heap: Heap::Uncounted,
        })
        .collect();
    standing(wire, threads, workload, Mode::PoisonRule, |pool| {
        let wave = pool.prepare(&jobs);
        let mut receipts = Vec::with_capacity(jobs.len());
        pool.exchange(&wave, &mut receipts)?;
        verify(&mut receipts, &expected)
    })
}

/// Run all required transport, grain, publication and drain cells.
///
/// # Specification
/// - ensures: selected cells exercise all worker counts and exact serial
///   oracles.
/// - fails: any transport, differential or output error.
/// - panics: none.
///
/// # Errors
/// Returns the originating observer I/O error.
///
/// # Adequacy
/// - hypothesis: L2 — all independent equations survive transport and dispatch
///   changes.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
pub(super) fn run(
    output: &mut io::BufWriter<io::StdoutLock<'_>>,
    workload: &[Workload],
) -> io::Result<()>
{
    if std::env::var_os("GANDR_SWEEP").is_some() {
        return sweep(output, workload);
    }
    let Ok(selected) = std::env::var("GANDR_HANDOFF")
    else {
        return Ok(());
    };
    for kind in [
        Kind::Channel,
        Kind::Rtrb(Wake::Busy),
        Kind::Rtrb(Wake::Park),
        Kind::Ringbuf(Wake::Busy),
        Kind::Ringbuf(Wake::Park),
        Kind::Steal,
    ] {
        if selected != "all" && selected != kind.label().0 {
            continue;
        }
        for publication in [Publication::Each, Publication::Batch] {
            for drain in [Natural(1), Natural(32)] {
                if matches!(kind, Kind::Channel | Kind::Steal)
                    && (publication != Publication::Each || drain.0 != 1)
                {
                    continue;
                }
                let wire = Wire {
                    kind,
                    publication,
                    drain,
                    share: Share::Spin,
                };
                latency(output, wire)?;
                for threads in [1, 2, 4, 8] {
                    refusals(workload, wire, Threads(threads))?;
                }
                for grain in [
                    Grain::Member,
                    Grain::Families(Natural(1)),
                    Grain::Families(Natural(4)),
                    Grain::Families(Natural(16)),
                ] {
                    for threads in [1, 2, 4, 8] {
                        for selection in
                            workload.iter().map(core::slice::from_ref).chain([workload])
                        {
                            let (label, index) = if selection.len() == 1 {
                                let family = selection.first().ok_or(io::ErrorKind::InvalidData)?;
                                (family.case.to_string(), family.index.0)
                            }
                            else {
                                (String::from("mixed"), 0)
                            };
                            let cell = |mode: Mode, schedule: Schedule| {
                                measure(
                                    selection,
                                    wire,
                                    Threads(threads),
                                    grain,
                                    mode,
                                    schedule,
                                    Census::Off,
                                )
                                .map(|cell| cell.elapsed.into_iter().sum::<Duration>())
                            };
                            let plain = cell(Mode::Plain, Schedule::Stream)?;
                            let admission = cell(Mode::Minting, Schedule::Stream)?;
                            let latency = if threads == 8 && selection.len() == 1 {
                                cell(Mode::Minting, Schedule::Latency)?
                            }
                            else {
                                Duration::ZERO
                            };
                            let (schema, largest) = selection
                                .first()
                                .map_or((Duration::ZERO, Duration::ZERO), |family| {
                                    (family.schema_time, family.largest)
                                });
                            let binding = selection
                                .first()
                                .map_or(Duration::ZERO, |family| family.binding_time);
                            writeln!(
                                output,
                                "HANDOFF,{},publication={},drain={},grain={},threads={threads},case={label},family={index},batches={},plain_ns={},admit_ns={},latency8_ns={},schema_ns={},largest_ns={},binding_ns={}",
                                kind.label(),
                                publication.label(),
                                drain.0,
                                grain.label(),
                                selection.len().saturating_mul(25),
                                plain.as_nanos(),
                                admission.as_nanos(),
                                latency.as_nanos(),
                                schema.as_nanos(),
                                largest.as_nanos(),
                                binding.as_nanos()
                            )?;
                            output.flush()?;
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

/// Order statistics of one sample set.
struct Summary
{
    /// The fastest sample.
    min: Duration,
    /// The nearest-rank upper median.
    median: Duration,
    /// The arithmetic mean.
    mean: Duration,
}

/// Minimum, median and mean of a sample set.
///
/// # Specification
/// - ensures: nearest-rank upper median; zeros for an empty set.
/// - panics: none.
fn summary(samples: &mut [Duration]) -> Summary
{
    samples.sort_unstable();
    let total: Duration = samples.iter().sum();
    let count = u32::try_from(samples.len()).unwrap_or(u32::MAX).max(1);
    Summary {
        min: samples.first().copied().unwrap_or_default(),
        median: samples
            .get(samples.len().div_ceil(2).saturating_sub(1))
            .copied()
            .unwrap_or_default(),
        mean: total.checked_div(count).unwrap_or_default(),
    }
}

/// Median of 25 timed repetitions, each prepared outside its interval.
///
/// # Specification
/// - ensures: `prepare` runs before each timer starts; `run` is timed.
/// - fails: the first preparation or run error.
/// - panics: none.
///
/// # Errors
/// Returns the originating error.
fn median<T, E>(
    mut prepare: impl FnMut() -> Result<T, E>,
    mut run: impl FnMut(T) -> Result<(), E>,
) -> Result<Duration, E>
{
    let mut samples = Vec::with_capacity(25);
    for _ in 0_usize .. 25 {
        let input = prepare()?;
        let start = Instant::now();
        run(input)?;
        samples.push(start.elapsed());
    }
    Ok(summary(&mut samples).median)
}

/// The largest per-member mean over 100 repetitions of `row`.
///
/// # Specification
/// - ensures: every member runs 100 times; the result is the largest mean.
/// - fails: the first row refusal.
/// - panics: none.
///
/// # Errors
/// Returns the row refusal.
fn largest(
    family: &Workload,
    mut row: impl FnMut(&[Choice], Step) -> Result<Admission, Refusal>,
) -> Result<Duration, Refusal>
{
    let mut largest = Duration::ZERO;
    for (step, choices) in family.members.iter().zip(&family.rows) {
        let start = Instant::now();
        for _ in 0_u32 .. 100 {
            row(choices, *step)?;
        }
        largest = largest.max(start.elapsed().checked_div(100).unwrap_or_default());
    }
    Ok(largest)
}

/// Serial costs of one family: both schema paths, plain replay, both row
/// shapes, their largest members and their warm allocations.
///
/// # Specification
/// - ensures: every row admits; allocation counts cover one serial pass of all
///   rows after a warm-up pass on the same buffers.
/// - fails: any schema, replay, admission or output error.
/// - panics: none.
///
/// # Errors
/// Returns the originating error as I/O.
fn serial(
    output: &mut io::BufWriter<io::StdoutLock<'_>>,
    family: &Workload,
) -> io::Result<()>
{
    let schema_fast = median(
        || Ok(family.proposal.clone()),
        |proposal| Schema::check(proposal, &mut Budget(10_000_000)).map(|_| ()),
    )
    .map_err(io::Error::other)?;
    let schema_reference = median(
        || Ok(family.proposal.clone()),
        |proposal| Schema::check_reference(proposal, &mut Budget(10_000_000)).map(|_| ()),
    )
    .map_err(io::Error::other)?;
    let plain_time = median(
        || Ok(family.arena.clone()),
        |mut arena| {
            for step in &family.members {
                plain(&mut arena, *step)?;
            }
            Ok::<_, StageError>(())
        },
    )
    .map_err(io::Error::other)?;
    let bound = family
        .schema
        .bind(family.arena.clone(), &mut Budget(10_000_000))
        .map_err(io::Error::other)?;
    let mut buffer = Row::default();
    let rows_minting = |consumer: &mut Consumer<'_>, buffer: &mut Row| {
        for (step, choices) in family.members.iter().zip(&family.rows) {
            minting(&family.schema, consumer, choices, *step, buffer)?;
        }
        Ok::<_, Refusal>(())
    };
    let minting_time = median(
        || Ok(bound.clone()),
        |mut consumer| rows_minting(&mut consumer, &mut buffer),
    )
    .map_err(io::Error::other)?;
    let mut fresh = bound.clone();
    rows_minting(&mut bound.clone(), &mut buffer).map_err(io::Error::other)?;
    let mut refused = Ok(());
    let heap_minting = allocation_counter::measure(|| {
        refused = rows_minting(&mut fresh, &mut buffer);
    });
    refused.map_err(io::Error::other)?;
    let rows_lookup = |buffer: &mut Row| {
        for (step, choices) in family.members.iter().zip(&family.rows) {
            lookup(&family.schema, &bound, choices, *step, buffer)?;
        }
        Ok::<_, Refusal>(())
    };
    let lookup_time = median(|| Ok(()), |()| rows_lookup(&mut buffer)).map_err(io::Error::other)?;
    let mut refused = Ok(());
    let heap_lookup = allocation_counter::measure(|| {
        refused = rows_lookup(&mut buffer);
    });
    refused.map_err(io::Error::other)?;
    let mut warm = bound.clone();
    let largest_minting = largest(family, |choices, step| {
        minting(&family.schema, &mut warm, choices, step, &mut buffer)
    })
    .map_err(io::Error::other)?;
    let largest_lookup = largest(family, |choices, step| {
        lookup(&family.schema, &bound, choices, step, &mut buffer)
    })
    .map_err(io::Error::other)?;
    let (checks, _, affected) = family.schema.work();
    writeln!(
        output,
        "SWEEP-SERIAL,{},family={},k={},obligations={},D={},schema_fast_ns={},schema_reference_ns={},plain_ns={},rows_minting_ns={},rows_lookup_ns={},largest_minting_ns={},largest_lookup_ns={},heap_minting={},heap_lookup={}",
        family.case,
        family.index.0,
        family.members.len(),
        checks.0,
        affected.0,
        schema_fast.as_nanos(),
        schema_reference.as_nanos(),
        plain_time.as_nanos(),
        minting_time.as_nanos(),
        lookup_time.as_nanos(),
        largest_minting.as_nanos(),
        largest_lookup.as_nanos(),
        heap_minting.count_total,
        heap_lookup.count_total
    )
}

/// Sweep pool width and the dispatcher's share for every family alone.
///
/// # Specification
/// - ensures: every cell is verified against its serial oracle; every family
///   reports its serial costs first.
/// - fails: any transport, differential or output error.
/// - panics: none.
///
/// # Errors
/// Returns the originating observer I/O error.
///
/// # Adequacy
/// - hypothesis: L2 — every pooled receipt equals its serial oracle at every
///   width and share.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
fn sweep(
    output: &mut io::BufWriter<io::StdoutLock<'_>>,
    workload: &[Workload],
) -> io::Result<()>
{
    for family in workload {
        serial(output, family)?;
        let selection = core::slice::from_ref(family);
        for share in [Share::Spin, Share::Work] {
            let wire = Wire {
                kind: Kind::Rtrb(Wake::Busy),
                publication: Publication::Batch,
                drain: Natural(32),
                share,
            };
            for workers in 1 ..= 12 {
                refusals(selection, wire, Threads(workers))?;
                for mode in [Mode::Minting, Mode::Lookup, Mode::Empty] {
                    let mut cell = measure(
                        selection,
                        wire,
                        Threads(workers),
                        Grain::Member,
                        mode,
                        Schedule::Latency,
                        Census::On,
                    )?;
                    let Summary { min, median, mean } = summary(&mut cell.elapsed);
                    let Heap::Counted(heap) = cell.heap
                    else {
                        return Err(io::ErrorKind::InvalidData.into());
                    };
                    writeln!(
                        output,
                        "SWEEP,{},family={},k={},mode={},workers={workers},share={},exchanges={},min_ns={},median_ns={},mean_ns={},heap={heap}",
                        family.case,
                        family.index.0,
                        family.members.len(),
                        mode.label(),
                        share.label(),
                        cell.elapsed.len(),
                        min.as_nanos(),
                        median.as_nanos(),
                        mean.as_nanos()
                    )?;
                }
            }
            output.flush()?;
        }
    }
    Ok(())
}
