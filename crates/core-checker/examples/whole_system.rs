//! Throwaway research scaffold on `research-whole-system`: the staged
//! pipeline of a whole program, measured per level, serial and forked.
//! Nothing here lands; it is committed only as evidence.
//!
//! `whole_system profile E` prints per-unit serial costs of every stage for
//! `pow:0..E` and `double:0..E`.
//! `whole_system program E W LEVELS` runs the whole program at width W with
//! the named levels forked (`d` certificates, `p` producer families, `t`
//! producer triples, `r` rows, `o` obligations, `x` readmission beside the
//! producer), prints wall, CPU and a verdict digest.
//! `whole_system rows` sweeps the recursive row split.

#![allow(
    warnings,
    unused,
    clippy::all,
    clippy::pedantic,
    clippy::restriction,
    clippy::nursery,
    clippy::cargo
)]

use std::cell::RefCell;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::sync::Mutex;
use std::time::Duration;
use std::time::Instant;

use gandr_core_checker::template::Analysis;
use gandr_core_checker::template::AnalyzePhase;
use gandr_core_checker::template::Family;
use gandr_core_checker::template::PriceGate;
use gandr_core_checker::template::Production;
use gandr_core_checker::template::ProgramId;
use gandr_core_checker::template::analyze;
use gandr_core_checker::template::analyze_observed;
use gandr_core_checker::template::harvest;
use gandr_core_checker::template::produce;
use gandr_kernel_core::admission::Admission;
use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Fork;
use gandr_kernel_core::admission::Proposal;
use gandr_kernel_core::admission::Refusal;
use gandr_kernel_core::admission::RowScratch;
use gandr_kernel_core::admission::Schema;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;
use gandr_theory_deep_inference::InheritanceCache;
use rayon::prelude::*;

#[path = "whole_system/frozen.rs"]
mod frozen;

type Res<T> = Result<T, Box<dyn std::error::Error + Send + Sync>>;

// ---------------------------------------------------------------- CPU time

/// `suseconds_t`: 32 bits on Darwin, 64 on Linux.
#[cfg(target_os = "macos")]
type Usec = i32;
#[cfg(not(target_os = "macos"))]
type Usec = i64;

#[repr(C)]
#[derive(Default)]
struct Timeval
{
    sec: i64,
    usec: Usec,
}

#[repr(C)]
#[derive(Default)]
struct Rusage
{
    utime: Timeval,
    stime: Timeval,
    rest: [i64; 14],
}

unsafe extern "C" {
    fn getrusage(
        who: i32,
        usage: *mut Rusage,
    ) -> i32;
}

/// User plus system time of every thread of this process.
fn cpu_time() -> Duration
{
    let mut usage = Rusage::default();
    unsafe { getrusage(0, &mut usage) };
    let user = Duration::new(usage.utime.sec as u64, usage.utime.usec as u32 * 1000);
    let system = Duration::new(usage.stime.sec as u64, usage.stime.usec as u32 * 1000);
    user + system
}

/// The 1, 5 and 15 minute load averages, slash-separated.
fn load_average() -> String
{
    if let Ok(text) = std::fs::read_to_string("/proc/loadavg") {
        return text
            .split_whitespace()
            .take(3)
            .collect::<Vec<_>>()
            .join("/");
    }
    std::process::Command::new("sysctl")
        .args(["-n", "vm.loadavg"])
        .output()
        .map(|out| {
            String::from_utf8_lossy(&out.stdout)
                .trim()
                .trim_matches(|c| c == '{' || c == '}')
                .trim()
                .replace(' ', "/")
        })
        .unwrap_or_default()
}

// ---------------------------------------------------------------- programs

#[derive(Clone, Copy, Debug)]
enum Case
{
    Power(usize, usize),
    Double(usize, usize),
    Generated
    {
        members: usize,
        arms: usize,
    },
}

impl core::fmt::Display for Case
{
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Power(lo, hi) if lo == hi => write!(f, "pow:{lo}"),
            | Self::Double(lo, hi) if lo == hi => write!(f, "double:{lo}"),
            | Self::Power(lo, hi) => write!(f, "pow:{lo}..{hi}"),
            | Self::Double(lo, hi) => write!(f, "double:{lo}..{hi}"),
            | Self::Generated { members, arms } => write!(f, "generated:{members}:{arms}"),
        }
    }
}

#[derive(Clone)]
struct Fixture
{
    arena: Arena,
    context: Vec<TypeId>,
    certificates: Vec<Certificate>,
    /// Serial normalization time per source.
    normalize: Vec<Duration>,
}

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

fn cancellation(
    arena: &mut Arena,
    value: Natural,
) -> Result<TermId, StageError>
{
    let body = arena.alloc(Term::Natural(Stage::Inner(Model(0)), value))?;
    let quote = arena.alloc(Term::Quote(body))?;
    arena.alloc(Term::Splice(quote))
}

/// The sources of one program, built into `arena` and not yet normalized.
fn sources(
    arena: &mut Arena,
    case: Case,
) -> Result<Vec<TermId>, StageError>
{
    let mut out = Vec::new();
    match case {
        | Case::Power(lo, top) | Case::Double(lo, top) => {
            let power = matches!(case, Case::Power(..));
            let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0))))?;
            let program = if power {
                gandr_core_nbe::stage::power(arena, Model(0))?
            }
            else {
                double_product(arena)?
            };
            let arms: &[usize] = if power { &[0] } else { &[2, 3] };
            for exponent in lo ..= top {
                for arm in arms {
                    let number = arena.alloc(Term::Natural(Stage::Outer, Natural(exponent)))?;
                    let source = arena.alloc(Term::Apply(program, number))?;
                    let input = if power {
                        arena.alloc(Term::Variable(Index(0)))?
                    }
                    else {
                        arena.alloc(Term::Natural(Stage::Inner(Model(0)), Natural(*arm)))?
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
                    out.push(source);
                }
            }
        },
        | Case::Generated { members, arms } => {
            for member in 0 .. members {
                out.push(cancellation(arena, Natural(member % arms))?);
            }
        },
    }
    Ok(out)
}

fn fixture(case: Case) -> Result<Fixture, StageError>
{
    let mut arena = Arena::default();
    let token = arena.alloc_type(Type::In(Model(0)))?;
    let roots = sources(&mut arena, case)?;
    let mut certificates = Vec::new();
    let mut normalize = Vec::new();
    for source in roots {
        let start = Instant::now();
        let certificate =
            gandr_core_nbe::stage::normalize(&mut arena, source, &mut Budget(10_000_000))?;
        normalize.push(start.elapsed());
        certificates.push(certificate);
    }
    Ok(Fixture {
        arena,
        context: Vec::from([token]),
        certificates,
        normalize,
    })
}

/// The number of terms and of classifiers `arena` holds.
fn extent(arena: &Arena) -> (usize, usize)
{
    let count = |present: &dyn Fn(usize) -> bool| {
        let mut high = 1;
        while present(high - 1) {
            high *= 2;
        }
        let mut low = high / 2;
        // invariant: present(low - 1) or low == 0, and !present(high - 1)
        while low < high {
            let mid = (low + high) / 2;
            if present(mid) {
                low = mid + 1;
            }
            else {
                high = mid;
            }
        }
        low
    };
    (
        count(&|i| arena.term(TermId(i)).is_ok()),
        count(&|i| arena.ty(TypeId(i)).is_ok()),
    )
}

/// Import what one source's normalization added above `floor` into `main`,
/// in its own allocation order, and remap its certificate.
fn merge(
    main: &mut Arena,
    worker: &Arena,
    floor: (usize, usize),
    certificate: &Certificate,
) -> Result<Certificate, StageError>
{
    let (terms, types) = extent(worker);
    let mut type_map: Vec<TypeId> = (0 .. floor.1).map(TypeId).collect();
    for index in floor.1 .. types {
        let ty = match worker.ty(TypeId(index))? {
            | Type::Arrow(a, b) => Type::Arrow(type_map[a.0], type_map[b.0]),
            | Type::Lift(inner) => Type::Lift(type_map[inner.0]),
            | leaf => leaf,
        };
        type_map.push(main.alloc_type(ty)?);
    }
    let mut term_map: Vec<TermId> = (0 .. floor.0).map(TermId).collect();
    for index in floor.0 .. terms {
        let term = match worker.term(TermId(index))? {
            | Term::Code(ty) => Term::Code(type_map[ty.0]),
            | Term::Lambda(ty, body) => Term::Lambda(type_map[ty.0], body),
            | Term::Eliminate(body, ty) => Term::Eliminate(body, type_map[ty.0]),
            | term => term,
        };
        let mut children = [gandr_kernel_term::stage::Child::Vacant; 3];
        for (child, output) in term.children().into_iter().zip(&mut children) {
            if let gandr_kernel_term::stage::Child::Present(child) = child {
                *output = gandr_kernel_term::stage::Child::Present(term_map[child.0]);
            }
        }
        term_map.push(main.alloc(term.rebuild(children)?)?);
    }
    Ok(Certificate {
        source: term_map[certificate.source.0],
        target: term_map[certificate.target.0],
        steps: certificate
            .steps
            .iter()
            .map(|step| Step {
                source: term_map[step.source.0],
                target: term_map[step.target.0],
                rule: step.rule,
            })
            .collect(),
    })
}

/// Normalize every source in its own snapshot of the program arena, then
/// merge the snapshots into one arena in source order.
fn fixture_forked(case: Case) -> Result<(Fixture, Duration), StageError>
{
    let mut arena = Arena::default();
    let token = arena.alloc_type(Type::In(Model(0)))?;
    let roots = sources(&mut arena, case)?;
    let floor = extent(&arena);
    let normalized: Vec<(Arena, Certificate, Duration)> = roots
        .par_iter()
        .map(|&source| {
            let start = Instant::now();
            let mut worker = arena.clone();
            let certificate =
                gandr_core_nbe::stage::normalize(&mut worker, source, &mut Budget(10_000_000))?;
            Ok((worker, certificate, start.elapsed()))
        })
        .collect::<Result<_, StageError>>()?;
    let start = Instant::now();
    let mut certificates = Vec::with_capacity(normalized.len());
    let mut normalize = Vec::with_capacity(normalized.len());
    for (worker, certificate, elapsed) in &normalized {
        certificates.push(merge(&mut arena, worker, floor, certificate)?);
        normalize.push(*elapsed);
    }
    let merged = start.elapsed();
    Ok((
        Fixture {
            arena,
            context: Vec::from([token]),
            certificates,
            normalize,
        },
        merged,
    ))
}

// ---------------------------------------------------------------- forks

/// A rayon fork for the kernel's obligation jobs.
struct RayonFork;

impl Fork for RayonFork
{
    fn run(
        &self,
        count: usize,
        job: &(dyn Fn(usize) -> Result<[usize; 2], Refusal> + Sync),
    ) -> Vec<Result<[usize; 2], Refusal>>
    {
        (0 .. count).into_par_iter().map(job).collect()
    }
}

/// BLAKE3-shaped lazy binary split: below `leaf` items run serially.
fn split<T: Sync, R: Send>(
    items: &[T],
    offset: usize,
    leaf: usize,
    work: &(impl Fn(usize, &[T]) -> R + Sync),
    merge: &(impl Fn(R, R) -> R + Sync),
) -> R
{
    if items.len() <= leaf.max(1) {
        return work(offset, items);
    }
    let mid = items.len() / 2;
    let (left, right) = items.split_at(mid);
    let (a, b) = rayon::join(
        || split(left, offset, leaf, work, merge),
        || split(right, offset + mid, leaf, work, merge),
    );
    merge(a, b)
}

thread_local! {
    /// Per-worker row buffers, keyed by the schema they were sized for.
    static SCRATCH: RefCell<(usize, RowScratch)> = RefCell::new((0, RowScratch::default()));
}

/// A fresh key per admitted family, so a reused schema address never reuses
/// a scratch sized for another schema.
static GENERATION: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

fn fnv(
    digest: &mut u64,
    value: &impl Hash,
)
{
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    *digest = digest.rotate_left(5) ^ hasher.finish();
}

// ---------------------------------------------------------------- stages

/// One paying family, ready for admission.
struct Paying
{
    family: usize,
    proposal: gandr_kernel_core::admission::Proposal,
    rows: Vec<Vec<Choice>>,
    members: Vec<Step>,
}

/// What a whole-program check records for determinism.
#[derive(Default)]
struct Outcome
{
    digest: u64,
    stages: Vec<(&'static str, Duration)>,
}

#[derive(Clone, Copy, Default)]
struct Levels
{
    declarations: bool,
    producer: bool,
    rows: bool,
    obligations: bool,
    beside: bool,
    normalize: bool,
    leaf: usize,
}

impl Levels
{
    fn parse(
        text: &str,
        leaf: usize,
    ) -> Self
    {
        Self {
            declarations: text.contains('d'),
            producer: text.contains('p'),
            rows: text.contains('r'),
            obligations: text.contains('o'),
            beside: text.contains('x'),
            normalize: text.contains('n'),
            leaf,
        }
    }
}

/// Kernel replay of every certificate: the program's trusted check.
fn readmission(
    input: &Fixture,
    forked: bool,
) -> Result<Vec<(bool, usize)>, StageError>
{
    if forked {
        input
            .certificates
            .par_iter()
            .map_init(
                || input.arena.clone(),
                |arena, certificate| {
                    let mut budget = Budget(10_000_000);
                    let result = gandr_kernel_core::stage::replay(
                        arena,
                        &input.context,
                        certificate,
                        &mut budget,
                    );
                    Ok((result.is_ok(), 10_000_000 - budget.0))
                },
            )
            .collect()
    }
    else {
        let mut arena = input.arena.clone();
        input
            .certificates
            .iter()
            .map(|certificate| {
                let mut budget = Budget(10_000_000);
                let result = gandr_kernel_core::stage::replay(
                    &mut arena,
                    &input.context,
                    certificate,
                    &mut budget,
                );
                Ok((result.is_ok(), 10_000_000 - budget.0))
            })
            .collect()
    }
}

/// One family through the producer: anti-unify, propose, inheritance checks.
fn produce_family(
    arena: &Arena,
    family: &Family,
    index: usize,
    cache: &mut InheritanceCache,
) -> Result<(String, Option<Paying>), StageError>
{
    let analysis = analyze(arena, family.program, &family.members)?;
    let (production, paying) = match analysis {
        | Analysis::Candidate(candidate) => {
            let admission = candidate.admission_candidate().ok();
            let production =
                candidate.produce(PriceGate::Memoized, cache, &mut Budget(10_000_000))?;
            let paying = match (&production, admission) {
                | (Production::Go(_), Some(admission)) => Some(Paying {
                    family: index,
                    proposal: admission.proposal,
                    rows: admission.rows,
                    members: family.members.clone(),
                }),
                | _ => None,
            };
            (production, paying)
        },
        | Analysis::Refused { reason, cost } => (Production::Plain { reason, cost }, None),
    };
    Ok((format!("{production:?}"), paying))
}

/// Admission of one paying family: fast schema, binding, shared rows.
fn admit_family(
    arena: &Arena,
    paying: &Paying,
    levels: Levels,
) -> Result<(usize, usize, usize, usize), Refusal>
{
    let proposal = paying.proposal.clone();
    let schema = if levels.obligations {
        Schema::check_forked(proposal, &mut Budget(10_000_000), &RayonFork)?
    }
    else {
        Schema::check_observed(proposal, &mut Budget(10_000_000), &mut |_| {}, true)?
    };
    let (checks, fuel, affected) = schema.work();
    let shared = schema.bind(arena.clone(), &mut Budget(10_000_000))?;
    let members = &paying.members;
    let rows = &paying.rows;
    let pairs: Vec<(usize, Step)> = (0 .. members.len()).map(|i| (i, members[i])).collect();
    let generation = GENERATION.fetch_add(1, core::sync::atomic::Ordering::Relaxed) + 1;
    let row_work = |_: usize, chunk: &[(usize, Step)]| -> Result<usize, Refusal> {
        SCRATCH.with(|cell| {
            let mut cell = cell.borrow_mut();
            let key = generation;
            if cell.0 != key {
                *cell = (key, RowScratch::new(&schema));
            }
            let scratch = &mut cell.1;
            let mut work = 0;
            for &(i, step) in chunk {
                let admitted = schema.admit_shared(
                    &shared,
                    &rows[i],
                    step,
                    scratch,
                    &mut Budget(10_000_000),
                )?;
                work += admitted.choices.0 + admitted.instantiations.0 + admitted.comparisons.0;
            }
            Ok(work)
        })
    };
    let work = if levels.rows {
        split(&pairs, 0, levels.leaf, &row_work, &|a, b| Ok(a? + b?))?
    }
    else {
        row_work(0, &pairs)?
    };
    Ok((checks.0, fuel.0, affected.0, work))
}

/// The whole program, every stage, at the requested levels.
fn whole_program(
    case: Case,
    levels: Levels,
) -> Result<Outcome, Box<dyn std::error::Error + Send + Sync>>
{
    let mut outcome = Outcome::default();
    let mut digest = 0_u64;
    let start = Instant::now();
    let input = if levels.normalize {
        let (input, merged) = fixture_forked(case)?;
        outcome.stages.push(("merge", merged));
        input
    }
    else {
        fixture(case)?
    };
    outcome.stages.insert(0, ("normalize", start.elapsed()));
    let checker = |input: &Fixture| readmission(input, levels.declarations);
    let producer = |input: &Fixture| -> Result<
        (
            Vec<String>,
            Vec<(usize, usize, usize, usize)>,
            Vec<(&'static str, Duration)>,
        ),
        Box<dyn std::error::Error + Send + Sync>,
    > {
        let mut stages = Vec::new();
        let start = Instant::now();
        let families = harvest(&input.arena, ProgramId(0), &input.certificates)?;
        stages.push(("harvest", start.elapsed()));
        let start = Instant::now();
        let produced: Vec<(String, Option<Paying>)> = if levels.producer {
            families
                .par_iter()
                .enumerate()
                .map(|(index, family)| {
                    produce_family(&input.arena, family, index, &mut InheritanceCache::new())
                })
                .collect::<Result<_, _>>()?
        }
        else {
            let mut cache = InheritanceCache::new();
            families
                .iter()
                .enumerate()
                .map(|(index, family)| produce_family(&input.arena, family, index, &mut cache))
                .collect::<Result<_, _>>()?
        };
        stages.push(("produce", start.elapsed()));
        let start = Instant::now();
        let mut productions = Vec::new();
        let mut paying = Vec::new();
        for (production, family) in produced {
            productions.push(production);
            if let Some(family) = family {
                paying.push(family);
            }
        }
        let admitted: Vec<(usize, usize, usize, usize)> = if levels.producer {
            paying
                .par_iter()
                .map(|family| admit_family(&input.arena, family, levels))
                .collect::<Result<_, _>>()
                .map_err(|e: Refusal| e.to_string())?
        }
        else {
            paying
                .iter()
                .map(|family| admit_family(&input.arena, family, levels))
                .collect::<Result<_, _>>()
                .map_err(|e: Refusal| e.to_string())?
        };
        stages.push(("admission", start.elapsed()));
        Ok((productions, admitted, stages))
    };
    let start = Instant::now();
    let (verdicts, produced) = if levels.beside {
        let (verdicts, produced) = rayon::join(|| checker(&input), || producer(&input));
        (verdicts?, produced.map_err(|e| e.to_string())?)
    }
    else {
        let produced = producer(&input).map_err(|e| e.to_string())?;
        let ckstart = Instant::now();
        let verdicts = checker(&input)?;
        outcome.stages.push(("readmission", ckstart.elapsed()));
        (verdicts, produced)
    };
    let (productions, admitted, stages) = produced;
    outcome.stages.extend(stages);
    outcome.stages.push(("check_and_produce", start.elapsed()));
    for production in &productions {
        fnv(&mut digest, production);
    }
    for admitted in &admitted {
        fnv(&mut digest, admitted);
    }
    for verdict in &verdicts {
        fnv(&mut digest, verdict);
    }
    outcome.digest = digest;
    Ok(outcome)
}

// ---------------------------------------------------------------- modes

fn profile(top: usize) -> Result<(), Box<dyn std::error::Error + Send + Sync>>
{
    println!("# load {}", load_average());
    for pass in 0 .. 3 {
        // Three passes; only the last, warm one prints.
        macro_rules! out {
        ($($t:tt)*) => {
            if pass == 2 {
                println!($($t)*);
            }
        };
    }
        for case in [Case::Power(0, top), Case::Double(0, top)] {
            let input = fixture(case)?;
            let steps: usize = input.certificates.iter().map(|c| c.steps.len()).sum();
            for (i, t) in input.normalize.iter().enumerate() {
                out!(
                    "PROFILE,{case},normalize,unit={i},steps={},ns={}",
                    input.certificates[i].steps.len(),
                    t.as_nanos()
                );
            }
            let start = Instant::now();
            let families = harvest(&input.arena, ProgramId(0), &input.certificates)?;
            out!(
                "PROFILE,{case},harvest,unit=all,families={},steps={steps},ns={}",
                families.len(),
                start.elapsed().as_nanos()
            );
            let mut cache = InheritanceCache::new();
            let mut paying = Vec::new();
            for (index, family) in families.iter().enumerate() {
                let start = Instant::now();
                let mut marks: Vec<Instant> = Vec::with_capacity(4);
                let analysis = analyze_observed(
                    &input.arena,
                    family.program,
                    &family.members,
                    &mut |_: AnalyzePhase| marks.push(Instant::now()),
                )?;
                let analyze_ns = start.elapsed().as_nanos();
                let phase_ns: Vec<u128> = core::iter::once(start)
                    .chain(marks.iter().copied())
                    .collect::<Vec<_>>()
                    .windows(2)
                    .map(|w| (w[1] - w[0]).as_nanos())
                    .collect();
                let phases = format!(
                    "import_ns={},size_ns={},generalize_ns={},count_ns={}",
                    phase_ns.first().unwrap_or(&0),
                    phase_ns.get(1).unwrap_or(&0),
                    phase_ns.get(2).unwrap_or(&0),
                    phase_ns.get(3).unwrap_or(&0)
                );
                let Analysis::Candidate(candidate) = analysis
                else {
                    out!(
                        "PROFILE,{case},family,unit={index},k={},analyze_ns={analyze_ns},{phases},propose_ns=0,checks_ns=0,verdict=refused",
                        family.members.len()
                    );
                    continue;
                };
                let start = Instant::now();
                let admission = candidate.admission_candidate().ok();
                let propose_ns = start.elapsed().as_nanos();
                let triples = usize::from(candidate.prices().triples);
                let start = Instant::now();
                let production =
                    candidate.produce(PriceGate::Memoized, &mut cache, &mut Budget(10_000_000))?;
                let checks_ns = start.elapsed().as_nanos();
                let verdict = matches!(production, Production::Go(_));
                out!(
                    "PROFILE,{case},family,unit={index},k={},triples={triples},analyze_ns={analyze_ns},{phases},propose_ns={propose_ns},checks_ns={checks_ns},verdict={}",
                    family.members.len(),
                    if verdict { "pays" } else { "plain" }
                );
                if let (true, Some(admission)) = (verdict, admission) {
                    paying.push(Paying {
                        family: index,
                        proposal: admission.proposal,
                        rows: admission.rows,
                        members: family.members.clone(),
                    });
                }
            }
            for family in &paying {
                let start = Instant::now();
                let schema = Schema::check_observed(
                    family.proposal.clone(),
                    &mut Budget(10_000_000),
                    &mut |_| {},
                    true,
                )?;
                let schema_ns = start.elapsed().as_nanos();
                let start = Instant::now();
                let shared = schema.bind(input.arena.clone(), &mut Budget(10_000_000))?;
                let bind_ns = start.elapsed().as_nanos();
                let mut scratch = RowScratch::new(&schema);
                let start = Instant::now();
                for (choices, step) in family.rows.iter().zip(&family.members) {
                    schema.admit_shared(
                        &shared,
                        choices,
                        *step,
                        &mut scratch,
                        &mut Budget(10_000_000),
                    )?;
                }
                let rows_ns = start.elapsed().as_nanos();
                out!(
                    "PROFILE,{case},admission,unit={},k={},obligations={},schema_ns={schema_ns},bind_ns={bind_ns},rows_ns={rows_ns}",
                    family.family,
                    family.members.len(),
                    schema.obligation_count()
                );
            }
            let mut arena = input.arena.clone();
            for (i, certificate) in input.certificates.iter().enumerate() {
                let start = Instant::now();
                gandr_kernel_core::stage::replay(
                    &mut arena,
                    &input.context,
                    certificate,
                    &mut Budget(10_000_000),
                )?;
                out!(
                    "PROFILE,{case},readmission,unit={i},steps={},ns={}",
                    certificate.steps.len(),
                    start.elapsed().as_nanos()
                );
            }
            let start = Instant::now();
            let _clone = input.arena.clone();
            out!(
                "PROFILE,{case},arena_clone,unit=all,ns={}",
                start.elapsed().as_nanos()
            );
        }
    }
    Ok(())
}

fn program(
    top: usize,
    widths: &[usize],
    levels_text: &str,
    leaf: usize,
    reps: usize,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>>
{
    println!("# load {}", load_average());
    for case in [Case::Power(0, top), Case::Double(0, top)] {
        let mut serial_digest = None;
        for &width in widths {
            let levels = if width == 0 {
                Levels::default()
            }
            else {
                Levels::parse(levels_text, leaf)
            };
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(width.max(1))
                .build()?;
            pool.install(|| -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
                // warm-up
                let warm = whole_program(case, levels)?;
                let mut walls = Vec::new();
                let mut cpus = Vec::new();
                let mut stage_sums: Vec<(&'static str, Duration)> = Vec::new();
                for _ in 0..reps {
                    let cpu0 = cpu_time();
                    let wall0 = Instant::now();
                    let outcome = whole_program(case, levels)?;
                    let wall = wall0.elapsed();
                    let cpu = cpu_time() - cpu0;
                    if outcome.digest != warm.digest {
                        return Err("digest moved between repetitions".into());
                    }
                    walls.push(wall);
                    cpus.push(cpu);
                    if stage_sums.is_empty() {
                        stage_sums = outcome.stages.clone();
                    } else {
                        for (sum, (_, t)) in stage_sums.iter_mut().zip(&outcome.stages) {
                            sum.1 += *t;
                        }
                    }
                }
                let digest = warm.digest;
                let same = *serial_digest.get_or_insert(digest) == digest;
                let wall: Duration = walls.iter().sum();
                let cpu: Duration = cpus.iter().sum();
                walls.sort();
                let median = walls[walls.len() / 2];
                let stages: Vec<String> = stage_sums
                    .iter()
                    .map(|(name, t)| format!("{name}_us={:.1}", t.as_secs_f64() * 1e6 / reps as f64))
                    .collect();
                println!(
                    "PROGRAM,{case},width={width},levels={},leaf={leaf},reps={reps},median_wall_us={:.1},mean_wall_us={:.1},busy_cores={:.2},utilization16={:.3},digest={digest:016x},same_as_serial={same},load={},{}",
                    if width == 0 { "serial" } else { levels_text },
                    median.as_secs_f64() * 1e6,
                    wall.as_secs_f64() * 1e6 / reps as f64,
                    cpu.as_secs_f64() / wall.as_secs_f64(),
                    cpu.as_secs_f64() / wall.as_secs_f64() / 16.0,
                    load_average(),
                    stages.join(",")
                );
                Ok(())
            })?;
        }
    }
    Ok(())
}

/// One paying family, natural or frozen, ready for row admission.
struct RowFamily
{
    label: String,
    arena: Arena,
    members: Vec<Step>,
    rows: Vec<Vec<Choice>>,
    proposal: Proposal,
}

/// The 16 natural paying families, or their frozen captures.
fn row_families(frozen: bool) -> Res<Vec<RowFamily>>
{
    let cases = (2 ..= 8)
        .map(|n| Case::Double(n, n))
        .chain([Case::Power(0, 8), Case::Double(0, 8)])
        .chain([(8, 2), (64, 2), (64, 4)].map(|(members, arms)| Case::Generated { members, arms }));
    let mut out = Vec::new();
    for case in cases {
        let input = fixture(case)?;
        let families = harvest(&input.arena, ProgramId(0), &input.certificates)?;
        for (index, family) in families.iter().enumerate() {
            let (arena, members) = if frozen {
                match frozen::load(&case.to_string(), Natural(index))? {
                    | Some(loaded) => loaded,
                    | None => continue,
                }
            }
            else {
                (input.arena.clone(), family.members.clone())
            };
            let production = produce(
                &arena,
                family.program,
                &members,
                PriceGate::Memoized,
                &mut InheritanceCache::new(),
                &mut Budget(10_000_000),
            )?;
            if !matches!(production, Production::Go(_)) {
                continue;
            }
            let Analysis::Candidate(candidate) = analyze(&arena, family.program, &members)?
            else {
                continue;
            };
            let admission = candidate.admission_candidate()?;
            out.push(RowFamily {
                label: format!("{case}/{index}"),
                arena,
                members,
                rows: admission.rows,
                proposal: admission.proposal,
            });
        }
    }
    Ok(out)
}

fn median_ns(samples: &mut Vec<Duration>) -> u128
{
    samples.sort_unstable();
    samples[samples.len() / 2].as_nanos()
}

fn admission_work(admission: &Admission) -> usize
{
    admission.choices.0
        + admission.affected.0
        + admission.comparisons.0
        + admission.instantiations.0
        + admission.classifiers.0
}

/// The recursive row split on real rows: leaf and width swept, shared and
/// hinted rows, the schema's obligations forked, and obligations beside rows.
fn rows() -> Res<()>
{
    let frozen = std::env::var("GANDR_FROZEN").is_ok();
    let widths: Vec<usize> = std::env::var("GANDR_WIDTHS")
        .ok()
        .map(|s| s.split(',').filter_map(|w| w.parse().ok()).collect())
        .unwrap_or_else(|| vec![1, 2, 4, 6, 8, 12, 16]);
    let leaves = [1_usize, 2, 4, 8, 16, 32, 64];
    let reps = 25;
    println!(
        "# load {} frozen={frozen} nanozone={}",
        load_average(),
        std::env::var("MallocNanoZone").unwrap_or_default()
    );
    let families = row_families(frozen)?;
    for family in &families {
        let k = family.members.len();
        let schema = Schema::check_observed(
            family.proposal.clone(),
            &mut Budget(10_000_000),
            &mut |_| {},
            true,
        )?;
        let shared = schema.bind(family.arena.clone(), &mut Budget(10_000_000))?;
        let mut scratch = RowScratch::new(&schema);
        let hints: Vec<Vec<TermId>> = family
            .rows
            .iter()
            .map(|choices| {
                schema
                    .hints(&shared, choices, &mut scratch)?
                    .ok_or(Refusal::Malformed)
            })
            .collect::<Result<_, Refusal>>()?;
        let oracle: usize = family
            .members
            .iter()
            .zip(&family.rows)
            .map(|(step, choices)| {
                schema
                    .admit_shared(
                        &shared,
                        choices,
                        *step,
                        &mut scratch,
                        &mut Budget(10_000_000),
                    )
                    .map(|a| admission_work(&a))
            })
            .sum::<Result<usize, Refusal>>()?;
        let oracle_hinted: usize = (0 .. family.members.len())
            .map(|i| {
                schema
                    .admit_hinted(
                        &shared,
                        &family.rows[i],
                        family.members[i],
                        &hints[i],
                        &mut scratch,
                        &mut Budget(10_000_000),
                    )
                    .map(|a| admission_work(&a))
            })
            .sum::<Result<usize, Refusal>>()?;
        let indices: Vec<usize> = (0 .. k).collect();
        let (oracle_checks, oracle_fuel, _) = schema.work();
        let obligations = schema.obligation_count();
        // Serial references.
        let serial = |hinted: bool, scratch: &mut RowScratch| -> Result<usize, Refusal> {
            let mut work = 0;
            for i in 0 .. k {
                let admitted = if hinted {
                    schema.admit_hinted(
                        &shared,
                        &family.rows[i],
                        family.members[i],
                        &hints[i],
                        scratch,
                        &mut Budget(10_000_000),
                    )?
                }
                else {
                    schema.admit_shared(
                        &shared,
                        &family.rows[i],
                        family.members[i],
                        scratch,
                        &mut Budget(10_000_000),
                    )?
                };
                work += admission_work(&admitted);
            }
            Ok(work)
        };
        let mut serial_ns = [0_u128; 2];
        for (slot, hinted) in [(0, false), (1, true)] {
            let mut samples = Vec::with_capacity(reps);
            for _ in 0 .. reps + 5 {
                let start = Instant::now();
                let work = serial(hinted, &mut scratch)?;
                samples.push(start.elapsed());
                if work != if hinted { oracle_hinted } else { oracle } {
                    return Err("serial work moved".into());
                }
            }
            samples.drain(.. 5);
            serial_ns[slot] = median_ns(&mut samples);
        }
        let mut samples = Vec::with_capacity(reps);
        for _ in 0 .. reps {
            let start = Instant::now();
            Schema::check_observed(
                family.proposal.clone(),
                &mut Budget(10_000_000),
                &mut |_| {},
                true,
            )?;
            samples.push(start.elapsed());
        }
        let schema_ns = median_ns(&mut samples);
        println!(
            "SERIAL,{},k={k},obligations={obligations},schema_fast_ns={schema_ns},shared_ns={},hinted_ns={}",
            family.label, serial_ns[0], serial_ns[1]
        );
        for &width in &widths {
            let pool = rayon::ThreadPoolBuilder::new().num_threads(width).build()?;
            pool.install(|| -> Res<()> {
                let generation = GENERATION.fetch_add(1, core::sync::atomic::Ordering::Relaxed) + 1;
                for (mode, hinted) in [("shared", false), ("hinted", true), ("empty", false)] {
                    for &leaf in &leaves {
                        if leaf > k && leaf != 64 {
                            continue;
                        }
                        let work = |_: usize, chunk: &[usize]| -> Result<usize, Refusal> {
                            if mode == "empty" {
                                return Ok(chunk.len());
                            }
                            SCRATCH.with(|cell| {
                                let mut cell = cell.borrow_mut();
                                if cell.0 != generation {
                                    *cell = (generation, RowScratch::new(&schema));
                                }
                                let scratch = &mut cell.1;
                                let mut work = 0;
                                for &i in chunk {
                                    let admitted = if hinted {
                                        schema.admit_hinted(&shared, &family.rows[i], family.members[i], &hints[i], scratch, &mut Budget(10_000_000))?
                                    } else {
                                        schema.admit_shared(&shared, &family.rows[i], family.members[i], scratch, &mut Budget(10_000_000))?
                                    };
                                    work += admission_work(&admitted);
                                }
                                Ok(work)
                            })
                        };
                        let mut samples = Vec::with_capacity(reps);
                        for rep in 0..reps + 5 {
                            let start = Instant::now();
                            let total = split(&indices, 0, leaf, &work, &|a, b| Ok(a? + b?))?;
                            let elapsed = start.elapsed();
                            let expected = match mode { "empty" => k, "hinted" => oracle_hinted, _ => oracle };
                            if total != expected {
                                return Err(format!("{mode} work {total} != {expected}").into());
                            }
                            if rep >= 5 {
                                samples.push(elapsed);
                            }
                        }
                        let median = median_ns(&mut samples);
                        let serial = match mode {
                            "shared" => serial_ns[0],
                            "hinted" => serial_ns[1],
                            _ => 0,
                        };
                        println!("SPLIT,{},k={k},mode={mode},width={width},leaf={leaf},median_ns={median},serial_ns={serial}", family.label);
                    }
                }
                // The schema's obligations forked, committed in order.
                let mut samples = Vec::with_capacity(reps);
                for rep in 0..reps + 5 {
                    let start = Instant::now();
                    let forked = Schema::check_forked(family.proposal.clone(), &mut Budget(10_000_000), &RayonFork)?;
                    let elapsed = start.elapsed();
                    let (checks, fuel, _) = forked.work();
                    if (checks, fuel) != (oracle_checks, oracle_fuel) {
                        return Err("forked schema work moved".into());
                    }
                    if rep >= 5 {
                        samples.push(elapsed);
                    }
                }
                let forked_ns = median_ns(&mut samples);
                // Schema then rows, both forked; and obligations beside rows
                // (proxy: the checked schema's obligations re-discharged in one
                // join with the rows).
                let indices_o: Vec<usize> = (0..obligations).collect();
                let mut samples = Vec::with_capacity(reps);
                for rep in 0..reps + 5 {
                    let start = Instant::now();
                    let (o, r) = rayon::join(
                        || {
                            split(&indices_o, 0, 1, &|_, chunk: &[usize]| -> Result<usize, Refusal> {
                                let mut fuel = 0;
                                for &i in chunk {
                                    fuel += schema.discharge(i, &mut Budget(10_000_000))?;
                                }
                                Ok(fuel)
                            }, &|a, b| Ok(a? + b?))
                        },
                        || {
                            split(&indices, 0, 8, &|_, chunk: &[usize]| -> Result<usize, Refusal> {
                                SCRATCH.with(|cell| {
                                    let mut cell = cell.borrow_mut();
                                    if cell.0 != generation {
                                        *cell = (generation, RowScratch::new(&schema));
                                    }
                                    let scratch = &mut cell.1;
                                    let mut work = 0;
                                    for &i in chunk {
                                        work += admission_work(&schema.admit_hinted(&shared, &family.rows[i], family.members[i], &hints[i], scratch, &mut Budget(10_000_000))?);
                                    }
                                    Ok(work)
                                })
                            }, &|a, b| Ok(a? + b?))
                        },
                    );
                    let elapsed = start.elapsed();
                    if o? != oracle_fuel.0 || r? != oracle_hinted {
                        return Err("overlap work moved".into());
                    }
                    if rep >= 5 {
                        samples.push(elapsed);
                    }
                }
                let overlap_ns = median_ns(&mut samples);
                println!(
                    "OBLIGATIONS,{},k={k},obligations={obligations},width={width},schema_fast_ns={schema_ns},forked_ns={forked_ns},overlap_hinted_ns={overlap_ns}",
                    family.label
                );
                Ok(())
            })?;
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>>
{
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(String::as_str).unwrap_or("profile");
    let top: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(8);
    match mode {
        | "profile" => profile(top),
        | "program" => {
            let widths: Vec<usize> = args
                .get(3)
                .map(|s| s.split(',').filter_map(|w| w.parse().ok()).collect())
                .unwrap_or_else(|| vec![0, 1, 2, 4, 6, 8, 12, 16]);
            let levels = args.get(4).cloned().unwrap_or_else(|| "dpro".into());
            let leaf: usize = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(8);
            let reps: usize = args.get(6).and_then(|s| s.parse().ok()).unwrap_or(15);
            program(top, &widths, &levels, leaf, reps)
        },
        | "rows" => rows(),
        | _ => Err("unknown mode".into()),
    }
}
