//! Exact guarded admission, measured against the same local replay judgment.
//!
//! Discovery and arena cloning are outside timed intervals. Every worker owns
//! its replay scratch; guarded workers borrow one immutable schema and arena.
//! Both parallel paths include scope/thread creation. Totals cover 25 batches.
//! Full typed certificate replay remains a separate baseline in the parent.

use std::io::Write as _;

use gandr_kernel_core::admission::Admission;
use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Refusal;
use gandr_kernel_core::admission::Schema;
use gandr_kernel_core::admission::Work;
use gandr_kernel_term::stage::Step;

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

/// Check a row and compare its sides, with no rule replay or member export.
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
fn member(
    schema: &Schema,
    arena: &Arena,
    choices: &[Choice],
    step: Step,
) -> Result<Admission, Refusal>
{
    let row = schema.substitute(schema.classifiers(), choices)?;
    row.admit(arena, step, &mut Budget(10_000_000))
}

/// Measure independent compressed members under the requested worker count.
///
/// # Specification
/// - ensures: every worker borrows immutable syntax and schema; verdict/work
///   must equal the serial observer in the calling differential.
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
    arena: &Arena,
    members: &[Step],
    rows: &[Vec<Choice>],
    threads: Threads,
) -> Result<Measurement, Refusal>
{
    let chunk = members.len().div_ceil(threads.0).max(1);
    let mut result = Measurement::default();
    for _ in 0_usize .. 25 {
        let start = Instant::now();
        let observations = if threads.0 == 1 {
            members
                .iter()
                .zip(rows)
                .map(|(step, choices)| member(schema, arena, choices, *step))
                .collect::<Result<Vec<_>, _>>()?
        }
        else {
            std::thread::scope(|scope| {
                let handles: Vec<_> = members
                    .chunks(chunk)
                    .zip(rows.chunks(chunk))
                    .map(|(members, rows)| {
                        scope.spawn(move || {
                            members
                                .iter()
                                .zip(rows)
                                .map(|(step, choices)| member(schema, arena, choices, *step))
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
            let analysis = analyze(&input.arena, family.program, &family.members)?;
            let production = produce(
                &input.arena,
                family.program,
                &family.members,
                PriceGate::Memoized,
                &mut InheritanceCache::new(),
                &mut Budget(10_000_000),
            )?;
            if !matches!(production, Production::Go(_)) {
                writeln!(
                    output,
                    "COMPRESSED-PLAIN,{case},family={index},members={}",
                    family.members.len()
                )?;
                continue;
            }
            let Analysis::Candidate(candidate) = analysis
            else {
                return Err(StageError::Unbalanced.into());
            };
            let admission = candidate.admission_candidate()?;
            let start = Instant::now();
            let schema = Schema::check(admission.proposal, &mut Budget(10_000_000))?;
            let schema_time = start.elapsed();
            let (checks, fuel, affected) = schema.work();
            let serial = admission_measure(
                &schema,
                &input.arena,
                &family.members,
                &admission.rows,
                Threads(1),
            )?;
            let baseline = replay_measure(&input.arena, &family.members, Threads(1))?;
            let mut largest = Duration::ZERO;
            for (choices, step) in admission.rows.iter().zip(&family.members) {
                let start = Instant::now();
                member(&schema, &input.arena, choices, *step)?;
                largest = largest.max(start.elapsed());
            }
            let rule = family.members.first().ok_or(StageError::Unbalanced)?.rule;
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
                    &input.arena,
                    &family.members,
                    &admission.rows,
                    Threads(threads),
                )?;
                let plain = replay_measure(&input.arena, &family.members, Threads(threads))?;
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
                    "COMPRESSED,{case},family={index},rule={rule},k={},threads={threads},schema_ns={},checks={},schema_fuel={},D={},row_ops={},comparisons={},classifier_ops={},instance_ops={},plain_fuel={},plain_ns={},admit_ns={},largest_ns={}",
                    family.members.len(),
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
                    largest.as_nanos()
                )?;
            }
        }
    }
    Ok(())
}
