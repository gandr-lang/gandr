//! Standing-pool latency and throughput with independently verified job
//! results.
//!
//! Each stream contains exactly 25 batches of each selected family. Task grain
//! groups consecutive family instances; partial final tasks are not padded.
//! Stream time per family is amortized throughput, not single-family latency.
//! The latter is measured separately, including dispatch and collection.

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
use super::Refusal;
use super::Schema;
use super::StageError;
use super::Step;
use super::Threads;
use super::Work;
use super::io;
use super::member;
use super::plain;
use super::queues::Kind;
use super::queues::Publication;
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
    /// Guard validation and exact side admission.
    Admission,
    /// A different rule must be refused, independently of scheduling.
    PoisonRule,
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
    /// Changed records instantiated.
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

/// One completed job, not merely a wakeup or completion count.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Receipt
{
    /// Echoed identity, validated before the next measurement.
    pub id: Natural,
    /// Exact counters or originating refusal.
    pub result: Result<Stats, Failure>,
}

impl Receipt
{
    /// Empty-job receipt used for warmup and ping-pong.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn empty(id: Natural) -> Self
    {
        Self {
            id,
            result: Ok(Stats::default()),
        }
    }
}

/// Worker-owned scratch, cloned before any timed dispatch.
#[derive(Clone)]
pub(super) enum Scratch<'schema>
{
    /// Ordinary replay arenas, one per family instance.
    Plain(Vec<Arena>),
    /// Bound schema namespaces, one per family instance.
    Admission(Vec<Consumer<'schema>>),
}

impl<'schema> Scratch<'schema>
{
    /// Prepare all 25 batches, importing fixed content once before cloning.
    ///
    /// # Specification
    /// - ensures: only the selected judgment's scratch is allocated.
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
        match mode {
            | Mode::Plain => Ok(Self::Plain(
                (0 .. 25)
                    .flat_map(|_| workload.iter().map(|family| family.arena.clone()))
                    .collect(),
            )),
            | Mode::Admission | Mode::PoisonRule => {
                let consumers = workload
                    .iter()
                    .map(|family| {
                        family
                            .schema
                            .bind(family.arena.clone(), &mut Budget(10_000_000))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Self::Admission(
                    (0 .. 25).flat_map(|_| consumers.iter().cloned()).collect(),
                ))
            },
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
            let family = instance
                .checked_rem(workload.len())
                .ok_or(Failure::Coordinate)?;
            let family = workload.get(family).ok_or(Failure::Coordinate)?;
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
                match *self {
                    | Self::Plain(ref mut arenas) => {
                        let arena = arenas.get_mut(instance).ok_or(Failure::Coordinate)?;
                        let Work(fuel) = plain(arena, *step).map_err(Failure::Plain)?;
                        stats.fuel = stats.fuel.saturating_add(fuel);
                    },
                    | Self::Admission(ref mut consumers) => {
                        let consumer = consumers.get_mut(instance).ok_or(Failure::Coordinate)?;
                        let step = if matches!(task.mode, Mode::PoisonRule) {
                            Step {
                                rule: gandr_kernel_term::stage::Rule::Congruence,
                                ..*step
                            }
                        }
                        else {
                            *step
                        };
                        let Admission {
                            comparisons,
                            choices,
                            instantiations,
                            classifiers,
                            ..
                        } = member(&family.schema, consumer, choices, step)
                            .map_err(Failure::Admission)?;
                        stats.comparisons = stats.comparisons.saturating_add(comparisons.0);
                        stats.choices = stats.choices.saturating_add(choices.0);
                        stats.instantiations =
                            stats.instantiations.saturating_add(instantiations.0);
                        stats.classifiers = stats.classifiers.saturating_add(classifiers.0);
                    },
                }
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
///   result.
/// - panics: none.
pub(super) fn execute(
    command: Command,
    scratch: &mut Scratch<'_>,
    workload: &[Workload],
) -> Receipt
{
    match command {
        | Command::Run(task) => Receipt {
            id: task.id,
            result: scratch.execute(task, workload),
        },
        | Command::Ping(id) => Receipt::empty(id),
        | Command::Stop => Receipt {
            id: Natural(usize::MAX),
            result: Err(Failure::Coordinate),
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
/// - ensures: sorted receipts equal the serial or specified refusal oracle.
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
    if actual != expected {
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

/// Measure one transport/grain/mode with preparation and validation excluded.
///
/// # Specification
/// - ensures: exactly 25 batches per family; startup, clones and oracles
///   excluded.
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
) -> io::Result<Duration>
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
            let jobs = tasks(
                workload,
                [
                    Natural(start),
                    Natural(start.saturating_add(span).min(count)),
                ],
                grain,
                mode,
            );
            let expected = oracle(workload, &jobs, &mut scratch);
            if expected.iter().any(|receipt| receipt.result.is_err()) {
                return Err(io::Error::other(
                    "serial reference refused measured workload",
                ));
            }
            Ok((jobs, expected))
        })
        .collect::<io::Result<Vec<_>>>()?;
    let mut elapsed = Duration::ZERO;
    standing(wire, threads, workload, mode, |pool| {
        for batch in &batches {
            let jobs = &batch.0;
            let expected = &batch.1;
            let wave = pool.prepare(jobs);
            let mut receipts = Vec::with_capacity(jobs.len());
            let start = Instant::now();
            pool.exchange(&wave, &mut receipts)?;
            elapsed = elapsed.saturating_add(start.elapsed());
            verify(&mut receipts, expected)?;
        }
        Ok(())
    })?;
    Ok(elapsed)
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
    );
    let expected: Vec<_> = (0 .. 25)
        .map(|id| Receipt {
            id: Natural(id),
            result: Err(Failure::Admission(Refusal::SidesMismatch)),
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
                            let plain = measure(
                                selection,
                                wire,
                                Threads(threads),
                                grain,
                                Mode::Plain,
                                Schedule::Stream,
                            )?;
                            let admission = measure(
                                selection,
                                wire,
                                Threads(threads),
                                grain,
                                Mode::Admission,
                                Schedule::Stream,
                            )?;
                            let latency = if threads == 8 && selection.len() == 1 {
                                measure(
                                    selection,
                                    wire,
                                    Threads(threads),
                                    grain,
                                    Mode::Admission,
                                    Schedule::Latency,
                                )?
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
