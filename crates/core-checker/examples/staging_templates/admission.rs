//! Exact guarded admission, measured against the same local replay judgment.
//!
//! Discovery, fixed-schema binding and arena cloning are outside batch timing.
//! Each worker owns an interned consumer clone and borrows one immutable
//! schema. Scoped rows include thread creation; pool rows exclude it. Totals
//! cover 25 batches. Full typed certificate replay remains a separate baseline
//! in the parent.
//!
//! # Hand-off protocol and measurement
//!
//! Set `GANDR_HANDOFF=all` when running the release observer to compare
//! standing `crossbeam-channel` MPMC, `crossbeam-deque` work stealing, and
//! per-worker `rtrb`/`ringbuf` SPSC pairs. The rings compare busy polling with
//! 64 spins followed by park/unpark, individual publication with slice/chunk
//! publication, and draining 1 or up to 32 jobs. All transports use member,
//! family, 4-family and 16-family tasks at 1/2/4/8 workers, over exactly 25
//! copies of each selected family. Queue capacity is 16,384 descriptors; mixed
//! streams fit without padding or dropped jobs. Busy polling reserves worker
//! execution capacity but does not set CPU affinity.
//!
//! `HANDOFF` stream totals measure amortized throughput. `latency8_ns`
//! separately measures 25 sequential single-family exchanges, so grouping
//! families cannot masquerade as lower single-family latency. `HANDOFF-PING`
//! reports median and p99 empty-job round trips after 100 warmups; half a round
//! trip is an amortized per-message cost, not a directly measured one-way
//! latency. Every timed stream is checked against serial verdicts and counters,
//! and every transport exercises the changed-rule refusal at all worker counts.
//! `COMPRESSED` retains the scoped-thread baseline, with one worker executing
//! directly. Schema validation and fixed-content binding are timed separately;
//! cloning and pool creation are outside batch timing.
//!
//! These are observer-only dev-dependencies: channel/deque enable `std`,
//! ringbuf enables `alloc`, and rtrb uses no default features. The established
//! Crossbeam implementations provide the MPMC and stealing controls; the two
//! maintained SPSC crates expose different batched APIs under the same
//! protocol. Neither enters the kernel. Keep both rings while measuring their
//! tradeoff; replacing one requires repeatable latency or throughput evidence
//! on the intended wake policy and grain, including the CPU cost of busy
//! polling.

#[path = "frozen.rs"]
mod frozen;
#[path = "handoff.rs"]
mod handoff;
#[path = "queues.rs"]
mod queues;

use std::io::Write as _;

use gandr_kernel_core::admission::Admission;
use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Consumer;
use gandr_kernel_core::admission::Proposal;
use gandr_kernel_core::admission::Refusal;
use gandr_kernel_core::admission::Row;
use gandr_kernel_core::admission::Schema;
use gandr_kernel_core::admission::Work;
use gandr_kernel_term::stage::Step;
use quenchant_shape::shape::Maybe;

use super::Analysis;
use super::Arena;
use super::Budget;
use super::Case;
use super::Certificate;
use super::Duration;
use super::InheritanceCache;
use super::Instant;
use super::Natural;
use super::PriceGate;
use super::Production;
use super::ProgramId;
use super::Stage;
use super::StageError;
use super::Term;
use super::analyze;
use super::fixture;
use super::harvest;
use super::io;
use super::produce;

/// Number of scoped workers requested for one independent family.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Threads(usize);

/// One observed batch's wall time and semantic work.
#[derive(Default)]
struct Measurement
{
    /// Sum of 25 independent batches, with preparation excluded.
    elapsed: Duration,
    /// Kernel replay fuel, or exact side comparisons.
    work: Work,
    /// Substitution choices validated.
    choices: Work,
    /// Exact records instantiated above selected points.
    instantiations: Work,
    /// Materialized classifier records inspected once.
    classifiers: Work,
}

/// Replay one local equation without claiming endpoint typing for open terms.
///
/// # Specification
/// - ensures: the unchanged kernel checks the equation under a closed reflexive
///   endpoint, exactly as schema inheritance does.
/// - fails: the kernel's local equation or work refusal.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError`.
///
/// # Adequacy
/// - hypothesis: L2 — the paired measurement compares this independent replay
///   with every admitted harvested member.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
fn plain(
    arena: &mut Arena,
    step: Step,
) -> Result<Work, StageError>
{
    let endpoint = arena.alloc(Term::Natural(Stage::Outer, Natural(0)))?;
    let certificate = Certificate {
        source: endpoint,
        target: endpoint,
        steps: Vec::from([step]),
    };
    let mut budget = Budget(10_000_000);
    gandr_kernel_core::stage::replay(arena, &[], &certificate, &mut budget)?;
    Ok(Work(10_000_000_usize.saturating_sub(budget.0)))
}

/// Measure serial or scoped-parallel replay over the same antichain members.
///
/// # Specification
/// - ensures: every member replays; thread counts affect scheduling only.
/// - fails: replay refusal or a worker panic as a typed measurement failure.
/// - panics: none.
///
/// # Errors
/// Returns the underlying `StageError` or Unbalanced on worker panic.
///
/// # Adequacy
/// - hypothesis: L2 — verdicts and work equal their serial observations.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
fn replay_measure(
    arena: &Arena,
    members: &[Step],
    threads: Threads,
) -> Result<Measurement, StageError>
{
    let chunk = members.len().div_ceil(threads.0).max(1);
    let mut result = Measurement::default();
    for _ in 0_usize .. 25 {
        let arenas: Vec<_> = members.chunks(chunk).map(|_| arena.clone()).collect();
        let start = Instant::now();
        let work = if threads.0 == 1 {
            let mut arena = arenas.into_iter().next().ok_or(StageError::Unbalanced)?;
            members.iter().try_fold(0_usize, |total, step| {
                let work = plain(&mut arena, *step)?;
                Ok(total.saturating_add(work.0))
            })?
        }
        else {
            std::thread::scope(|scope| {
                let mut handles = Vec::with_capacity(threads.0);
                for (members, mut arena) in members.chunks(chunk).zip(arenas) {
                    handles.push(scope.spawn(move || {
                        members.iter().try_fold(0_usize, |total, step| {
                            let work = plain(&mut arena, *step)?;
                            Ok::<_, StageError>(total.saturating_add(work.0))
                        })
                    }));
                }
                handles.into_iter().try_fold(0_usize, |total, handle| {
                    let work = handle.join().map_err(|_panic| StageError::Unbalanced)?;
                    let work = work?;
                    Ok::<_, StageError>(total.saturating_add(work))
                })
            })?
        };
        result.elapsed = result.elapsed.saturating_add(start.elapsed());
        result.work.0 = result.work.0.saturating_add(work);
    }
    Ok(result)
}

/// Check an original row and compare its sides, interning the instance into
/// an owned consumer clone, with no rule replay or member export.
///
/// # Specification
/// - ensures: observes exactly the kernel's compressed instance judgment.
/// - fails: the kernel's named row or side refusal.
/// - panics: none.
///
/// # Errors
/// Returns `Refusal` unchanged.
///
/// # Adequacy
/// - hypothesis: L2 — every row is compared to its independently harvested
///   sides.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
fn minting(
    schema: &Schema,
    consumer: &mut Consumer<'_>,
    choices: &[Choice],
    step: Step,
    row: &mut Row,
) -> Result<Admission, Refusal>
{
    let substitution = schema.substitute_minting(schema.classifiers(), choices)?;
    substitution.admit(consumer, step, row, &mut Budget(10_000_000))
}

/// Check a row into reused buffers and compare its sides by lookup in a
/// shared binding, with no rule replay, member export or allocation.
///
/// # Specification
/// - ensures: observes exactly the kernel's compressed instance judgment.
/// - fails: the kernel's named row or side refusal.
/// - panics: none.
///
/// # Errors
/// Returns `Refusal` unchanged.
///
/// # Adequacy
/// - hypothesis: L2 — every row is compared to its independently harvested
///   sides.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
fn lookup(
    schema: &Schema,
    consumer: &Consumer<'_>,
    choices: &[Choice],
    step: Step,
    row: &mut Row,
) -> Result<Admission, Refusal>
{
    let mut substitution = schema.substitute(schema.classifiers(), choices, row)?;
    substitution.admit(consumer, step, &mut Budget(10_000_000))
}

/// Measure independent compressed members under the requested worker count.
///
/// # Specification
/// - ensures: each worker owns a consumer clone; verdict/work must equal the
///   serial observer in the calling differential.
/// - fails: named admission refusal or a worker panic as Malformed.
/// - panics: none.
///
/// # Errors
/// Returns `Refusal`.
///
/// # Adequacy
/// - hypothesis: L2 — independent rows cannot change verdict with scheduling.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
fn admission_measure(
    schema: &Schema,
    consumer: &Consumer<'_>,
    members: &[Step],
    rows: &[Vec<Choice>],
    threads: Threads,
) -> Result<Measurement, Refusal>
{
    let chunk = members.len().div_ceil(threads.0).max(1);
    let mut result = Measurement::default();
    for _ in 0_usize .. 25 {
        let consumers: Vec<_> = members.chunks(chunk).map(|_| consumer.clone()).collect();
        let start = Instant::now();
        let observations = if threads.0 == 1 {
            let mut consumer = consumers.into_iter().next().ok_or(Refusal::Malformed)?;
            let mut row = Row::default();
            members
                .iter()
                .zip(rows)
                .map(|(step, choices)| minting(schema, &mut consumer, choices, *step, &mut row))
                .collect::<Result<Vec<_>, _>>()?
        }
        else {
            std::thread::scope(|scope| {
                let handles: Vec<_> = members
                    .chunks(chunk)
                    .zip(rows.chunks(chunk))
                    .zip(consumers)
                    .map(|((members, rows), mut consumer)| {
                        scope.spawn(move || {
                            let mut row = Row::default();
                            members
                                .iter()
                                .zip(rows)
                                .map(|(step, choices)| {
                                    minting(schema, &mut consumer, choices, *step, &mut row)
                                })
                                .collect::<Result<Vec<_>, _>>()
                        })
                    })
                    .collect();
                let mut observations = Vec::with_capacity(members.len());
                for handle in handles {
                    let batch = handle.join().map_err(|_panic| Refusal::Malformed)?;
                    observations.extend(batch?);
                }
                Ok::<_, Refusal>(observations)
            })?
        };
        result.elapsed = result.elapsed.saturating_add(start.elapsed());
        for observation in observations {
            result.work.0 = result.work.0.saturating_add(observation.comparisons.0);
            result.choices.0 = result.choices.0.saturating_add(observation.choices.0);
            result.instantiations.0 = result
                .instantiations
                .0
                .saturating_add(observation.instantiations.0);
            result.classifiers.0 = result
                .classifiers
                .0
                .saturating_add(observation.classifiers.0);
        }
    }
    Ok(result)
}

/// Execute the parent workload set, preserving its exact memo-aware price gate.
///
/// # Specification
/// - ensures: all paying families admit every original member, compare with
///   local replay, and retain verdict/work at 1, 2, 4 and 8 workers; nonpaying
///   families retain plain replay rather than receiving fabricated speedups.
/// - fails: production, schema, replay, differential or output failure.
/// - panics: none.
///
/// # Errors
/// Returns the originating typed error, boxed only at the executable boundary.
///
/// # Adequacy
/// - hypothesis: L2/L3 — harvested and generated inputs, distinct work counters
///   and the independent plain path distinguish replay removal from caching it.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
pub fn run(
    output: &mut io::BufWriter<io::StdoutLock<'_>>
) -> Result<(), Box<dyn core::error::Error>>
{
    let mut workload = Vec::new();
    let source = match std::env::var("GANDR_INPUT") {
        | Ok(name) if name == "frozen" => Source::Frozen,
        | _ => Source::Natural,
    };
    let cases = (0 ..= 8)
        .map(|n| Case::Power(Natural(n)))
        .chain((0 ..= 8).map(|n| Case::DoubleProduct(Natural(n))))
        .chain([Case::PowerSeries, Case::DoubleProductSeries])
        .chain([2, 8, 64].into_iter().flat_map(|k| {
            [2, 4].into_iter().map(move |arms| Case::Generated {
                members: Natural(k),
                arms: Natural(arms),
            })
        }));
    for case in cases {
        let input = fixture(case)?;
        let families = harvest(&input.arena, ProgramId(0), &input.certificates)?;
        for (index, family) in families.iter().enumerate() {
            let (arena, members) = match source {
                | Source::Natural => (input.arena.clone(), family.members.clone()),
                | Source::Frozen => match frozen::load(case, Natural(index))? {
                    | Maybe::Present(loaded) => loaded,
                    | Maybe::Absent(_) => continue,
                },
            };
            let analysis = analyze(&arena, family.program, &members)?;
            let production = produce(
                &arena,
                family.program,
                &members,
                PriceGate::Memoized,
                &mut InheritanceCache::new(),
                &mut Budget(10_000_000),
            )?;
            if !matches!(production, Production::Go(_)) {
                writeln!(
                    output,
                    "COMPRESSED-PLAIN,{case},family={index},members={}",
                    members.len()
                )?;
                continue;
            }
            let Analysis::Candidate(candidate) = analysis
            else {
                return Err(StageError::Unbalanced.into());
            };
            let admission = candidate.admission_candidate()?;
            let proposal = admission.proposal.clone();
            let start = Instant::now();
            let schema = Schema::check(admission.proposal, &mut Budget(10_000_000))?;
            let schema_time = start.elapsed();
            let (checks, fuel, affected) = schema.work();
            let bound = arena.clone();
            let start = Instant::now();
            let consumer = schema.bind(bound, &mut Budget(10_000_000))?;
            let binding_time = start.elapsed();
            let serial =
                admission_measure(&schema, &consumer, &members, &admission.rows, Threads(1))?;
            let baseline = replay_measure(&arena, &members, Threads(1))?;
            let mut largest = Duration::ZERO;
            let mut largest_consumer = consumer.clone();
            let mut row = Row::default();
            for (choices, step) in admission.rows.iter().zip(&members) {
                let start = Instant::now();
                minting(&schema, &mut largest_consumer, choices, *step, &mut row)?;
                largest = largest.max(start.elapsed());
            }
            let rule = members.first().ok_or(StageError::Unbalanced)?.rule;
            let rule = match rule {
                | gandr_kernel_term::stage::Rule::Congruence => "congruence",
                | gandr_kernel_term::stage::Rule::Beta => "beta",
                | gandr_kernel_term::stage::Rule::SpliceQuote => "splice-quote",
                | gandr_kernel_term::stage::Rule::QuoteSplice => "quote-splice",
                | gandr_kernel_term::stage::Rule::IterateZero => "iterate-zero",
                | gandr_kernel_term::stage::Rule::IterateSuccessor => "iterate-successor",
                | gandr_kernel_term::stage::Rule::Eliminate => "eliminate",
            };
            for threads in [1, 2, 4, 8] {
                let admitted = admission_measure(
                    &schema,
                    &consumer,
                    &members,
                    &admission.rows,
                    Threads(threads),
                )?;
                let plain = replay_measure(&arena, &members, Threads(threads))?;
                if admitted.work != serial.work
                    || admitted.choices != serial.choices
                    || admitted.instantiations != serial.instantiations
                    || admitted.classifiers != serial.classifiers
                    || plain.work != baseline.work
                {
                    return Err(StageError::InvalidCertificate.into());
                }
                writeln!(
                    output,
                    "COMPRESSED,{case},family={index},rule={rule},k={},threads={threads},schema_ns={},checks={},schema_fuel={},D={},row_ops={},comparisons={},classifier_ops={},instance_ops={},plain_fuel={},plain_ns={},admit_ns={},largest_ns={},binding_ns={}",
                    members.len(),
                    schema_time.as_nanos(),
                    checks.0,
                    fuel.0,
                    affected.0,
                    admitted.choices.0,
                    admitted.work.0,
                    admitted.classifiers.0,
                    admitted.instantiations.0,
                    plain.work.0,
                    plain.elapsed.as_nanos(),
                    admitted.elapsed.as_nanos(),
                    largest.as_nanos(),
                    binding_time.as_nanos()
                )?;
            }
            workload.push(handoff::Workload {
                case,
                index: Natural(index),
                arena,
                schema,
                proposal,
                members,
                rows: admission.rows,
                schema_time,
                binding_time,
                largest,
            });
        }
    }
    handoff::run(output, &workload)?;
    Ok(())
}

/// Which equation occurrences the admission workload measures.
#[derive(Clone, Copy)]
enum Source
{
    /// Families regenerated by the current producer and canonical arena.
    Natural,
    /// The captured pre-interning occurrences, remapped before timing.
    Frozen,
}
