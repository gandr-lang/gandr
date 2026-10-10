//! Strict-staging family costs, replay differential, timing and heap residency.
//!
//! Run with `cargo run -p gandr-core-checker --example staging_templates
//! --release`. Timings exclude family discovery and arena cloning; production
//! has its own measurement. Heap columns are scoped allocator high-water marks,
//! not RSS. Readmission residency includes a newly owned input arena and
//! certificates. Generated template residency instead owns the template and one
//! regenerated source/member at a time. Production peak is reported separately
//! because discovering a family still materializes its input certificates.
//!
//! Both gates get fresh caches. Candidate JSON and every substitution are
//! serialized outside timing/allocation scopes; plain bytes sum independent
//! reachable-graph equations, with no normalization intermediates. Refused
//! candidates' byte rows describe syntax, not accepted templates. JSON images
//! include classifier tables, constructor payloads and edges, roots, rules and
//! all guarded arms. A substitution is a guard row in declared point order.
//! ADMISSION measures a template clone and one admission's scratch while
//! borrowing fixture sources; unlike RESIDENCY it does not charge source input.
//! The work price combines template nodes and a kernel-fuel allowance, not
//! elapsed time; `checks_fuel` is observed from the caller's consumed budget.
//! A candidate image owns a compacted graph; borrowed wrappers encode its
//! classifiers and guards without a parallel recursive syntax tree. Interning
//! maps and cache counters are excluded. These are format-specific observations
//! against independent per-equation DAGs, not optimal cross-member
//! deduplication and not a persistence or decoding API.
//!
//! The crate's staging page records the measurement dependencies, alternatives
//! and conditions for changing them alongside the observed family costs.

extern crate alloc;

#[path = "staging_templates/admission.rs"]
mod admission;

use core::time::Duration;
use std::io;
use std::io::Write as _;
use std::time::Instant;

use anodized::spec;
use gandr_core_checker::template::Analysis;
use gandr_core_checker::template::Family;
use gandr_core_checker::template::FamilyPrices;
use gandr_core_checker::template::PriceGate;
use gandr_core_checker::template::Production;
use gandr_core_checker::template::ProgramId;
use gandr_core_checker::template::analyze;
use gandr_core_checker::template::harvest;
use gandr_core_checker::template::plain_image;
use gandr_core_checker::template::produce;
use gandr_core_checker::template::readmit;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;
use gandr_theory_deep_inference::InheritanceCache;

/// The observer boundary retains syntax, encoding and output failures.
#[derive(Debug)]
enum ObservationError
{
    /// A malformed equation, failed replay or exhausted work allowance.
    Stage(StageError),
    /// The explicit measurement image could not be serialized.
    Image(serde_json::Error),
    /// A report row could not be written.
    Output(io::Error),
    /// The kernel refused a guarded admission the observer measures.
    Admission(gandr_kernel_core::admission::Refusal),
}

impl core::fmt::Display for ObservationError
{
    /// Render the original diagnostic at the failed boundary.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Stage(ref error) => error.fmt(f),
            | Self::Image(ref error) => error.fmt(f),
            | Self::Output(ref error) => error.fmt(f),
            | Self::Admission(ref error) => error.fmt(f),
        }
    }
}

impl core::error::Error for ObservationError
{
}

impl From<StageError> for ObservationError
{
    /// Preserve a stage refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(error: StageError) -> Self
    {
        Self::Stage(error)
    }
}

impl From<serde_json::Error> for ObservationError
{
    /// Preserve an image-encoding refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(error: serde_json::Error) -> Self
    {
        Self::Image(error)
    }
}

impl From<io::Error> for ObservationError
{
    /// Preserve an output failure.
    ///
    /// # Specification
    /// trivial.
    fn from(error: io::Error) -> Self
    {
        Self::Output(error)
    }
}

impl From<gandr_kernel_core::admission::Refusal> for ObservationError
{
    /// Preserve a guarded-admission refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(error: gandr_kernel_core::admission::Refusal) -> Self
    {
        Self::Admission(error)
    }
}

/// A reproducible workload, with harvested and generated classes separate.
#[derive(Clone, Copy, Debug)]
enum Case
{
    /// Strict power specialization at one exponent.
    Power(Natural),
    /// A second program, with two recurring input arms at one exponent.
    DoubleProduct(Natural),
    /// Controlled cancellation families; members and distinct bodies.
    Generated
    {
        /// Family cardinality.
        members: Natural,
        /// Number of distinct numeral bodies.
        arms: Natural,
    },
    /// One program harvested jointly across all nine power instances.
    PowerSeries,
    /// The second program harvested jointly across exponents and both arms.
    DoubleProductSeries,
}

impl core::fmt::Display for Case
{
    /// Render a stable workload label.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Power(n) => write!(f, "pow:{}", n.0),
            | Self::DoubleProduct(n) => write!(f, "double:{}", n.0),
            | Self::PowerSeries => f.write_str("pow:0..8"),
            | Self::DoubleProductSeries => f.write_str("double:0..8"),
            | Self::Generated { members, arms } => write!(f, "generated:{}:{}", members.0, arms.0),
        }
    }
}

/// A program's actual producer output, before template discovery.
#[derive(Clone)]
struct Fixture
{
    /// Shared source arena, including normalizer allocations.
    arena: Arena,
    /// Ordinary hypotheses for complete typed replay.
    context: Vec<TypeId>,
    /// Complete certificates, including congruence premises.
    certificates: Vec<Certificate>,
}

/// Construct the second program: each iteration multiplies by its input twice.
///
/// # Specification
/// - ensures: constructs one exponent-independent meta iterator over lifted
///   naturals, with step `p -> <~x * ~p * ~x>`.
/// - fails: arena allocation errors.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError` from arena construction.
///
/// # Adequacy
/// - hypothesis: L2 — complete kernel replay checks every produced equation;
///   the executable compares both input arms and all exponents zero through
///   eight.
/// - witness: `tests::harvested_workloads_preserve_typed_replay_and_power_values`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|root|
    matches!(arena.term(*root), Ok(Term::Lambda(_, _)))))]
fn double_product(arena: &mut Arena) -> Result<TermId, StageError>
{
    let outer = arena.alloc_type(Type::Nat(Stage::Outer))?;
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0))))?;
    let lifted = arena.alloc_type(Type::Lift(inner))?;
    let one = arena.alloc(Term::Natural(Stage::Inner(Model(0)), Natural(1)))?;
    let initial = arena.alloc(Term::Quote(one))?;
    let input = arena.alloc(Term::Variable(Index(1)))?;
    let input = arena.alloc(Term::Splice(input))?;
    let previous = arena.alloc(Term::Variable(Index(0)))?;
    let previous = arena.alloc(Term::Splice(previous))?;
    let product = arena.alloc(Term::Multiply(input, previous))?;
    let product = arena.alloc(Term::Multiply(product, input))?;
    let body = arena.alloc(Term::Quote(product))?;
    let step = arena.alloc(Term::Lambda(lifted, body))?;
    let exponent = arena.alloc(Term::Variable(Index(1)))?;
    let body = arena.alloc(Term::Iterate(exponent, initial, step))?;
    let body = arena.alloc(Term::Lambda(lifted, body))?;
    arena.alloc(Term::Lambda(outer, body))
}

/// Build one standalone generated source without retaining any other member.
///
/// # Specification
/// - ensures: the returned source is a quote/splice cancellation at the
///   numeral.
/// - fails: arena allocation errors.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError` from arena construction.
///
/// # Adequacy
/// - hypothesis: L2 — typed plain and projected replay agree on every member.
/// - witness: `tests::measured_ownership_scopes_release_their_working_sets`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|root|
    matches!(arena.term(*root), Ok(Term::Splice(_)))))]
fn cancellation(
    arena: &mut Arena,
    value: Natural,
) -> Result<TermId, StageError>
{
    let body = arena.alloc(Term::Natural(Stage::Inner(Model(0)), value))?;
    let quote = arena.alloc(Term::Quote(body))?;
    arena.alloc(Term::Splice(quote))
}

/// Run the real strict producer for one workload.
///
/// # Specification
/// - ensures: harvested inputs use meta-level iteration, never a host unrolling
///   of the residual. Generated inputs are labeled independently.
/// - fails: syntax, normalization or checked arithmetic errors.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError`; Overflow for an invalid generated arm count.
///
/// # Adequacy
/// - hypothesis: L2 — complete replay checks all outputs; power execution at
///   input three independently checks strict residual semantics.
/// - witness: `tests::harvested_workloads_preserve_typed_replay_and_power_values`
/// - witness: `tests::measurements_preserve_structural_and_replay_refusals`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|fixture|
    fixture.certificates.len() == match case {
        Case::Power(_) => 1,
        Case::DoubleProduct(_) => 2,
        Case::PowerSeries => 9,
        Case::DoubleProductSeries => 18,
        Case::Generated { members, .. } => members.0,
    }))]
fn fixture(case: Case) -> Result<Fixture, StageError>
{
    let mut arena = Arena::default();
    let token = arena.alloc_type(Type::In(Model(0)))?;
    let mut certificates = Vec::new();
    match case {
        | Case::Power(_)
        | Case::DoubleProduct(_)
        | Case::PowerSeries
        | Case::DoubleProductSeries => {
            let power = matches!(case, Case::Power(_) | Case::PowerSeries);
            let exponents = match case {
                | Case::Power(n) | Case::DoubleProduct(n) => n.0 ..= n.0,
                | Case::PowerSeries | Case::DoubleProductSeries => 0_usize ..= 8,
                | Case::Generated { .. } => return Err(StageError::Unbalanced),
            };
            let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0))))?;
            let program = if power {
                gandr_core_nbe::stage::power(&mut arena, Model(0))?
            }
            else {
                double_product(&mut arena)?
            };
            let arms: &[Natural] = if power {
                &[Natural(0)]
            }
            else {
                &[Natural(2), Natural(3)]
            };
            for exponent in exponents {
                for arm in arms {
                    let number = arena.alloc(Term::Natural(Stage::Outer, Natural(exponent)))?;
                    let source = arena.alloc(Term::Apply(program, number))?;
                    let input = if power {
                        arena.alloc(Term::Variable(Index(0)))?
                    }
                    else {
                        arena.alloc(Term::Natural(Stage::Inner(Model(0)), *arm))?
                    };
                    let input = arena.alloc(Term::Quote(input))?;
                    let source = arena.alloc(Term::Apply(source, input))?;
                    let source = if power {
                        let source = arena.alloc(Term::Splice(source))?;
                        let source = arena.alloc(Term::Lambda(inner, source))?;
                        arena.alloc(Term::Quote(source))?
                    }
                    else {
                        source
                    };
                    let certificate = gandr_core_nbe::stage::normalize(
                        &mut arena,
                        source,
                        &mut Budget(10_000_000),
                    )?;
                    certificates.push(certificate);
                }
            }
        },
        | Case::Generated { members, arms } => {
            for member in 0 .. members.0 {
                let arm = member.checked_rem(arms.0).ok_or(StageError::Overflow)?;
                let source = cancellation(&mut arena, Natural(arm))?;
                let certificate =
                    gandr_core_nbe::stage::normalize(&mut arena, source, &mut Budget(10_000_000))?;
                certificates.push(certificate);
            }
        },
    }
    Ok(Fixture {
        arena,
        context: Vec::from([token]),
        certificates,
    })
}

/// Measure ordinary and guarded complete replay, with fresh scratch per repeat.
///
/// # Specification
/// - ensures: every guarded verdict equals plain replay's classifier; durations
///   cover replay only, with cloning outside the timed interval.
/// - fails: replay refusal or a differential disagreement.
/// - panics: none.
/// - executable: none — elapsed time and timed-region boundaries are external
///   observations; replay equality is checked within every measured iteration.
///
/// # Errors
/// Propagates `StageError`; `InvalidCertificate` for a differential
/// disagreement.
///
/// # Adequacy
/// - hypothesis: L2 — full typed replay is the independent authority.
/// - witness: `tests::harvested_workloads_preserve_typed_replay_and_power_values`
/// - witness: `tests::measurements_preserve_structural_and_replay_refusals`
fn replay_times(
    input: &Fixture,
    productions: &[Production],
) -> Result<(Duration, Duration), StageError>
{
    let mut plain_time = Duration::ZERO;
    let mut guarded_time = Duration::ZERO;
    for _ in 0_usize .. 25 {
        let mut plain = input.arena.clone();
        let mut guarded = input.arena.clone();
        for certificate in &input.certificates {
            let start = Instant::now();
            let expected = gandr_kernel_core::stage::replay(
                &mut plain,
                &input.context,
                certificate,
                &mut Budget(10_000_000),
            );
            plain_time = plain_time.saturating_add(start.elapsed());
            let start = Instant::now();
            let actual = readmit(
                &mut guarded,
                &input.context,
                certificate,
                productions,
                &mut Budget(10_000_000),
            );
            guarded_time = guarded_time.saturating_add(start.elapsed());
            if actual != expected {
                return Err(StageError::InvalidCertificate);
            }
            actual?;
        }
    }
    Ok((plain_time, guarded_time))
}

/// Record newly owned plain-family readmission residency.
///
/// # Specification
/// - ensures: the counter includes cloned input arena, every certificate and
///   replay scratch, with all those allocations dropped before it closes.
/// - fails: complete replay refusals.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError` from replay.
///
/// # Adequacy
/// - hypothesis: L2 — ordinary replay remains the semantic observer; the
///   allocator counter is measurement evidence, with no pinned byte threshold.
/// - witness: `tests::measured_ownership_scopes_release_their_working_sets`
/// - witness: `tests::measurements_preserve_structural_and_replay_refusals`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|info|
    info.bytes_current == 0 && info.count_current == 0))]
fn plain_residency(input: &Fixture) -> Result<allocation_counter::AllocationInfo, StageError>
{
    let mut result = Ok(());
    let info = allocation_counter::measure(|| {
        let mut owned = input.clone();
        result = owned.certificates.iter().try_for_each(|certificate| {
            gandr_kernel_core::stage::replay(
                &mut owned.arena,
                &owned.context,
                certificate,
                &mut Budget(10_000_000),
            )
            .map(|_| ())
        });
    });
    result?;
    Ok(info)
}

/// Measure template residency while regenerating and dropping one member at a
/// time.
///
/// # Specification
/// - ensures: a generated family owns the template but no member list or source
///   family arena; every member is matched, instantiated, replayed and dropped.
/// - fails: a declined family or member replay refusal.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::InvalidCertificate` for no template, or replay errors.
///
/// # Adequacy
/// - hypothesis: L2 — every generated admission is also observed by plain
///   replay.
/// - witness: `tests::measured_ownership_scopes_release_their_working_sets`
/// - witness: `tests::measurements_preserve_structural_and_replay_refusals`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|info|
    info.bytes_current == 0 && info.count_current == 0))]
fn template_residency(
    production: &Production,
    members: Natural,
    arms: Natural,
) -> Result<allocation_counter::AllocationInfo, StageError>
{
    let Production::Go(ref template) = *production
    else {
        return Err(StageError::InvalidCertificate);
    };
    let mut result = Ok(());
    let info = allocation_counter::measure(|| {
        let template = template.clone();
        result = (|| {
            for member in 0 .. members.0 {
                let arm = member.checked_rem(arms.0).ok_or(StageError::Overflow)?;
                let mut arena = Arena::default();
                let source = cancellation(&mut arena, Natural(arm))?;
                let substitution = template.peak_substitution(&arena, source)?;
                let (mut instance, step) = template.instantiate(&substitution)?;
                let token = instance.alloc_type(Type::In(Model(0)))?;
                let certificate = Certificate {
                    source: step.source,
                    target: step.target,
                    steps: Vec::from([step]),
                };
                gandr_kernel_core::stage::replay(
                    &mut instance,
                    &[token],
                    &certificate,
                    &mut Budget(10_000_000),
                )?;
            }
            Ok(())
        })();
    });
    result?;
    Ok(info)
}

/// An actual serialized byte length, never a node-count estimate.
#[derive(Clone, Copy)]
#[repr(transparent)]
struct ImageSize(usize);

/// Kernel work units actually consumed during inheritance.
#[repr(transparent)]
struct KernelFuel(usize);

/// Format-specific observations, made outside timed and allocator scopes.
struct FamilyObservation
{
    /// Prices are cold-cache prices for both routes.
    prices: FamilyPrices,
    /// Generalized point nodes, including any target-only points.
    points: gandr_theory_deep_inference::NodeCount,
    /// Complete candidate image, including every guarded arm.
    template: ImageSize,
    /// Sum of independently encoded member substitution rows.
    substitutions: ImageSize,
    /// Sum of independent reachable-graph equation images.
    plain: ImageSize,
}

/// Charge actual compact JSON images for both representations.
///
/// # Specification
/// - ensures: charges all substitutions even for a refused candidate, whose
///   bytes are descriptive rather than an admission claim.
/// - fails: syntax, serialization, uniform-family or size-overflow failure.
/// - panics: none.
/// - executable: none — byte counts require running the serializer; the
///   independent image witness checks what those bytes represent.
///
/// # Errors
/// Propagates the original observer error.
///
/// # Adequacy
/// - hypothesis: L2 — real serializer output, with literals and classifiers,
///   separates stored bytes from the node-cost model.
/// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
/// - witness: `tests::measurements_preserve_structural_and_replay_refusals`
fn observe_family(
    arena: &Arena,
    family: &Family,
) -> Result<FamilyObservation, ObservationError>
{
    let Analysis::Candidate(candidate) = analyze(arena, family.program, &family.members)?
    else {
        return Err(StageError::InvalidCertificate.into());
    };
    let image = candidate.image()?;
    let template = serde_json::to_vec(&image)?.len();
    let mut substitutions = 0_usize;
    for substitution in candidate.substitutions() {
        substitutions = substitutions
            .checked_add(serde_json::to_vec(&substitution)?.len())
            .ok_or(StageError::Overflow)?;
    }
    let mut plain = 0_usize;
    for step in &family.members {
        let image = plain_image(arena, step)?;
        plain = plain
            .checked_add(serde_json::to_vec(&image)?.len())
            .ok_or(StageError::Overflow)?;
    }
    Ok(FamilyObservation {
        prices: candidate.prices(),
        points: gandr_theory_deep_inference::NodeCount::from(candidate.points().count()),
        template: ImageSize(template),
        substitutions: ImageSize(substitutions),
        plain: ImageSize(plain),
    })
}

/// Measure template plus one admission's scratch, with fixture sources
/// borrowed.
///
/// # Specification
/// - ensures: the template clone remains resident while each admission's
///   independent materialization and replay is released before the next one.
/// - fails: any projection or replay failure.
/// - panics: none.
///
/// # Errors
/// Propagates the actual admission error.
///
/// # Adequacy
/// - hypothesis: L2 — the witness checks the admitted equations against plain
///   replay. Allocator peaks are observations of the executable, not pinned
///   test values; the borrowed fixture arena is explicitly excluded.
/// - witness: `tests::measured_ownership_scopes_release_their_working_sets`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|info|
    u64::try_from(info.bytes_current).is_ok_and(|live| live <= info.bytes_max)
        && u64::try_from(info.count_current).is_ok_and(|live| live <= info.count_max)))]
fn admission_residency(
    template: &gandr_core_checker::template::Template,
    arena: &Arena,
    family: &[gandr_kernel_term::stage::Step],
) -> Result<allocation_counter::AllocationInfo, StageError>
{
    let mut result = Ok(());
    let mut retained = None;
    let info = allocation_counter::measure(|| {
        retained = Some(template.clone());
        if let Some(ref owned) = retained {
            result = family
                .iter()
                .try_for_each(|step| owned.admit(arena, step.source, &mut Budget(10_000_000)));
        }
    });
    result?;
    Ok(info)
}

/// Emit reproducible cost rows and exercise the actual strict-staging APIs.
///
/// # Specification
/// - ensures: reports all harvested families and generated controls separately,
///   verifies complete replay equality, and executes every power residual.
/// - fails: I/O, producer, projection, replay or residual execution failure.
/// - panics: none.
/// - executable: none — stdout rows and timing scopes are external effects; the
///   command checks replay equality and residual values before success.
///
/// # Errors
/// Propagates the original error from each exercised boundary.
///
/// # Adequacy
/// - hypothesis: L2 — the executable runs independently of the test runner;
///   power results, differential verdicts and emitted gate rows are its
///   observers.
/// - witness: `tests::harvested_workloads_preserve_typed_replay_and_power_values`
/// - witness: `tests::measurements_preserve_structural_and_replay_refusals`
fn main() -> Result<(), ObservationError>
{
    let mut output = io::BufWriter::new(io::stdout().lock());
    writeln!(
        output,
        "class,gate,family,rule,k,F,s,f,points,T,c,combined,old_price,memo_price,template_bytes,substitution_bytes,total_bytes,plain_bytes,checks,hits,checks_fuel,inheritance_steps,plain_steps,admissions,instance_steps,verdict"
    )?;
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
        let mut input = fixture(case)?;
        let families = harvest(&input.arena, ProgramId(0), &input.certificates)?;
        let observations = families
            .iter()
            .map(|family| observe_family(&input.arena, family))
            .collect::<Result<Vec<_>, _>>()?;
        for gate in [PriceGate::Unmemoized, PriceGate::Memoized] {
            let gate_name = match gate {
                | PriceGate::Unmemoized => "unmemoized",
                | PriceGate::Memoized => "memoized",
            };
            let mut cache = InheritanceCache::new();
            let mut productions = Vec::new();
            let mut fuels = Vec::with_capacity(families.len());
            let mut error: Result<(), StageError> = Ok(());
            let start = Instant::now();
            let production_heap = allocation_counter::measure(|| {
                error = families.iter().try_for_each(|family| {
                    let mut budget = Budget(10_000_000);
                    let production = produce(
                        &input.arena,
                        family.program,
                        &family.members,
                        gate,
                        &mut cache,
                        &mut budget,
                    )?;
                    fuels.push(KernelFuel(
                        10_000_000_usize
                            .checked_sub(budget.0)
                            .ok_or(StageError::Overflow)?,
                    ));
                    productions.push(production);
                    Ok(())
                });
            });
            error?;
            let production_time = start.elapsed();
            for (index, (((family, production), observation), fuel)) in families
                .iter()
                .zip(&productions)
                .zip(&observations)
                .zip(&fuels)
                .enumerate()
            {
                let mut cost = production.cost();
                let mut admissions = 0_usize;
                if let Production::Go(ref template) = *production {
                    for step in &family.members {
                        template.admit(&input.arena, step.source, &mut Budget(10_000_000))?;
                        admissions = admissions.checked_add(1).ok_or(StageError::Overflow)?;
                    }
                }
                cost.admissions = gandr_theory_deep_inference::AdmissionCount::from(admissions);
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
                let verdict = match *production {
                    | Production::Go(_) => "pays",
                    | Production::WorkBoundExceeded { .. } => "no-pay:check-bound",
                    | Production::Plain { reason, .. } => match reason {
                        | gandr_theory_deep_inference::TemplateRefusal::DoesNotPay { .. } => {
                            "no-pay:price"
                        },
                        | gandr_theory_deep_inference::TemplateRefusal::EntryOutsidePeak {
                            ..
                        } => "no-pay:target-only-point",
                        | gandr_theory_deep_inference::TemplateRefusal::NotInherited { .. } => {
                            "no-pay:inheritance"
                        },
                        | gandr_theory_deep_inference::TemplateRefusal::EmptyFamily => {
                            "no-pay:empty"
                        },
                        | gandr_theory_deep_inference::TemplateRefusal::SkeletonDivergence {
                            ..
                        } => "no-pay:divergence",
                        | gandr_theory_deep_inference::TemplateRefusal::Ungeneralizable => {
                            "no-pay:anti-unification"
                        },
                        | gandr_theory_deep_inference::TemplateRefusal::ArmAddressCollision {
                            ..
                        } => "no-pay:collision",
                    },
                };
                writeln!(
                    output,
                    "{case},{gate_name},{index},{rule},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{verdict}",
                    usize::from(cost.members),
                    usize::from(cost.plain_size),
                    usize::from(cost.template_size),
                    usize::from(cost.expansion_factor),
                    usize::from(observation.points),
                    usize::from(observation.prices.triples),
                    usize::from(observation.prices.check_bound),
                    usize::from(observation.prices.triples)
                        .checked_mul(usize::from(observation.prices.check_bound))
                        .and_then(|work| work.checked_add(usize::from(cost.template_size)))
                        .ok_or(StageError::Overflow)?,
                    if observation.prices.unmemoized.is_ok() {
                        "pass"
                    }
                    else {
                        "refuse"
                    },
                    if observation.prices.memoized.is_ok() {
                        "pass"
                    }
                    else {
                        "refuse"
                    },
                    observation.template.0,
                    observation.substitutions.0,
                    observation
                        .template
                        .0
                        .checked_add(observation.substitutions.0)
                        .ok_or(StageError::Overflow)?,
                    observation.plain.0,
                    usize::from(cost.triples_checked),
                    usize::from(cost.cache_hits),
                    fuel.0,
                    usize::from(cost.replayed_steps),
                    usize::from(cost.plain_replayed_steps),
                    usize::from(cost.admissions),
                    admissions
                )?;
            }
            let (plain_time, guarded_time) = replay_times(&input, &productions)?;
            let plain_heap = plain_residency(&input)?;
            writeln!(
                output,
                "RUN,{case},{gate_name},equations={},families={},production_ns={},plain_ns_25={},guarded_ns_25={},production_peak={},plain_peak={},plain_live_end={}",
                input
                    .certificates
                    .iter()
                    .map(|certificate| certificate.steps.len())
                    .sum::<usize>(),
                families.len(),
                production_time.as_nanos(),
                plain_time.as_nanos(),
                guarded_time.as_nanos(),
                production_heap.bytes_max,
                plain_heap.bytes_max,
                plain_heap.bytes_current
            )?;
            if let Case::Generated { members, arms } = case
                && let Some(production @ &Production::Go(_)) = productions.first()
            {
                let heap = template_residency(production, members, arms)?;
                writeln!(
                    output,
                    "RESIDENCY,{case},{gate_name},template_peak={},template_live_end={}",
                    heap.bytes_max, heap.bytes_current
                )?;
            }
            for (index, (family, production)) in families.iter().zip(&productions).enumerate() {
                if let Production::Go(ref template) = *production {
                    let heap = admission_residency(template, &input.arena, &family.members)?;
                    writeln!(
                        output,
                        "ADMISSION,{case},{gate_name},family={index},working_peak={},template_live_end={}",
                        heap.bytes_max, heap.bytes_current
                    )?;
                }
            }
        }
        if matches!(case, Case::Power(_) | Case::PowerSeries) {
            for (index, certificate) in input.certificates.iter().enumerate() {
                let exponent = match case {
                    | Case::Power(n) => n,
                    | Case::PowerSeries => Natural(index),
                    | Case::DoubleProduct(_)
                    | Case::DoubleProductSeries
                    | Case::Generated { .. } => return Err(StageError::Unbalanced.into()),
                };
                let residual = gandr_core_checker::stage::compile(
                    &mut input.arena,
                    &input.context,
                    certificate,
                    &mut Budget(10_000_000),
                )?;
                let result = residual.execute(Natural(3))?;
                let exponent =
                    u32::try_from(exponent.0).map_err(|_overflow| StageError::Overflow)?;
                let expected = 3_usize.checked_pow(exponent).ok_or(StageError::Overflow)?;
                if result.0 != expected {
                    return Err(StageError::InvalidCertificate.into());
                }
                writeln!(output, "EXECUTE,{case},input=3,result={}", result.0)?;
            }
        }
    }
    admission::run(&mut output)?;
    output.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn harvested_workloads_preserve_typed_replay_and_power_values()
    {
        for case in [
            Case::Power(Natural(0)),
            Case::Power(Natural(3)),
            Case::DoubleProduct(Natural(2)),
        ] {
            let mut input = fixture(case).unwrap();
            let families = harvest(&input.arena, ProgramId(0), &input.certificates).unwrap();
            for gate in [PriceGate::Unmemoized, PriceGate::Memoized] {
                let mut cache = InheritanceCache::new();
                let productions = families
                    .iter()
                    .map(|family| {
                        produce(
                            &input.arena,
                            family.program,
                            &family.members,
                            gate,
                            &mut cache,
                            &mut Budget(1_000_000),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                replay_times(&input, &productions).unwrap();
                for certificate in &input.certificates {
                    let expected = gandr_kernel_core::stage::replay(
                        &mut input.arena,
                        &input.context,
                        certificate,
                        &mut Budget(1_000_000),
                    );
                    assert_eq!(
                        readmit(
                            &mut input.arena,
                            &input.context,
                            certificate,
                            &productions,
                            &mut Budget(1_000_000)
                        ),
                        expected
                    );
                    assert!(expected.is_ok());
                    if let Case::Power(exponent) = case {
                        let residual = gandr_core_checker::stage::compile(
                            &mut input.arena,
                            &input.context,
                            certificate,
                            &mut Budget(1_000_000),
                        )
                        .unwrap();
                        let expected = 3_usize
                            .checked_pow(u32::try_from(exponent.0).unwrap())
                            .unwrap();
                        assert_eq!(residual.execute(Natural(3)).unwrap(), Natural(expected));
                    }
                }
            }
        }
    }

    #[test]
    fn measured_ownership_scopes_release_their_working_sets()
    {
        let members = Natural(64);
        let arms = Natural(2);
        let input = fixture(Case::Generated { members, arms }).unwrap();
        let families = harvest(&input.arena, ProgramId(0), &input.certificates).unwrap();
        let family = &families[0];
        let produced = produce(
            &input.arena,
            family.program,
            &family.members,
            PriceGate::Memoized,
            &mut InheritanceCache::new(),
            &mut Budget(1_000_000),
        )
        .unwrap();
        let plain = plain_residency(&input).unwrap();
        let streamed = template_residency(&produced, members, arms).unwrap();
        assert_eq!((plain.bytes_current, plain.count_current), (0, 0));
        assert_eq!((streamed.bytes_current, streamed.count_current), (0, 0));
        let Production::Go(ref template) = produced
        else {
            panic!("paying cancellation family")
        };
        let admitted = admission_residency(template, &input.arena, &family.members).unwrap();
        let retained = allocation_counter::measure(|| {
            let owned = template.clone();
            core::mem::drop(owned);
        });
        assert_eq!(
            u64::try_from(admitted.bytes_current).unwrap(),
            retained.bytes_total
        );
        assert_eq!(
            u64::try_from(admitted.count_current).unwrap(),
            retained.count_total
        );
    }

    #[test]
    fn measurements_preserve_structural_and_replay_refusals()
    {
        assert!(matches!(
            fixture(Case::Generated {
                members: Natural(1),
                arms: Natural(0)
            }),
            Err(StageError::Overflow)
        ));
        let mut input = fixture(Case::Generated {
            members: Natural(64),
            arms: Natural(2),
        })
        .unwrap();
        let mut families = harvest(&input.arena, ProgramId(0), &input.certificates).unwrap();
        families[0].members.clear();
        assert!(matches!(
            observe_family(&input.arena, &families[0]),
            Err(ObservationError::Stage(StageError::InvalidCertificate))
        ));
        let plain = produce(
            &input.arena,
            ProgramId(0),
            &[],
            PriceGate::Memoized,
            &mut InheritanceCache::new(),
            &mut Budget(0),
        )
        .unwrap();
        assert_eq!(
            template_residency(&plain, Natural(1), Natural(1)),
            Err(StageError::InvalidCertificate)
        );
        input.certificates[0].steps[0].rule = gandr_kernel_term::stage::Rule::QuoteSplice;
        assert_eq!(
            replay_times(&input, &[]),
            Err(StageError::InvalidCertificate)
        );
        assert_eq!(plain_residency(&input), Err(StageError::InvalidCertificate));
    }
}
