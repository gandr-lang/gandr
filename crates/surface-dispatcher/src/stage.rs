//! The `stage` verb: build staging observer programs and check each through
//! the checker's program entry, on a pool of the driver's width.
//!
//! # The pool is the driver's; the checker forks through it
//!
//! [`gandr_core_checker::staging::check`] names no thread: it hands each
//! stage's independent jobs to a [`Fork`]. Here that fork is a `rayon` pool of
//! the invocation's width, built once per invocation and entered once per
//! program; at one thread it is the checker's [`Serial`] fork and no pool is
//! built. Every program of one invocation is checked through one memo, in
//! order, so a later program drafts from the templates an earlier one left.
//!
//! # The stage verb checks staged programs on a stealing pool
//!
//! `ProgramSpec` reads `pow:LO..HI`, the power iterator at each exponent from
//! `LO` through `HI` with its input left free under a quoted lambda, and
//! `double:LO..HI`, the double-product iterator at each exponent and the inner
//! inputs two and three. `Staging::run` builds each program into an arena of
//! its own and checks it with `gandr-core-checker`'s `staging::check`:
//! normalization by source, one merge, the harvest, and the readmissions beside
//! the family admissions. Every program of a run goes through one `Memo`, in
//! order, so a later program drafts from the templates an earlier one left. A
//! `Staged` line counts the certificates readmitted and the families by
//! admission class. `StageRun::verdict` is `Faulted` when a program was not
//! built or its check stopped, `Refused` when a certificate was not readmitted,
//! and `Readmitted` otherwise, so a fault outranks a refusal.
//!
//! **The digest is what the width must not change.** `StageRun::digest` folds
//! each program's spelling, merged arena, certificates, readmissions and
//! families, and each admission's class and schema. It folds no time, and no
//! admission's origin or drafting, which the memo's controller decides from
//! measured time. Every width digests alike: the stage tests compare one, three
//! and the host's width, and the driver's suite compares both streams and the
//! exit. The digest is a hash of each value's structural rendering and holds on
//! one build; it is not a format.
//!
//! **`rayon`, built once per run.** The checker names no thread: it forks
//! through `gandr_core_checker::fork::Fork`, and the dispatcher's fork is a
//! `rayon` pool of the run's width, built once per run and entered once per
//! program. Each forked stage spawns one task per worker, at most one per item;
//! the tasks take items from one shared cursor, and each makes its worker state
//! — an arena snapshot, a drafter — on its first item, so a stage clones no
//! more snapshots than it has busy workers. The readmissions and the family
//! admissions are the two halves of one `rayon::join`, and each half forks per
//! item inside it. At one thread no pool is built, and the checker's serial
//! fork is the reference every width is tested against.
//!
//! The check forks below the source and nests a per-item fork inside each half
//! of a join, which is the walk's recorded reversal for `rayon`. The
//! alternatives were these:
//!
//! - _`std::thread::scope` and a cursor per stage, the walk's pool._ A per-item
//!   fork inside each half of a join starts a second set of threads beside the
//!   first, so the halves either oversubscribe the cores or run one after the
//!   other. Reversal: a check whose stages do not nest.
//! - _[`chili`](https://crates.io/crates/chili), a heartbeat-scheduled `join`._
//!   It offers `join` without a scope for the per-item fork, and one maintainer
//!   carries it. Reversal: a scope and a release history in it, and a measured
//!   gain on this verb.
//!
//! `rayon` is the ecosystem's standard data-parallel pool, maintained by many
//! contributors, with default features off; it brings `rayon-core` and the
//! `crossbeam` deque and epoch crates. The choice reverses on an advisory
//! against `rayon` or `rayon-core` that no release fixes, an unmaintained mark,
//! or a measured loss against scoped threads on this verb.

use core::fmt;
use core::fmt::Write as _;
use core::hash::Hasher as _;
use core::num::NonZeroUsize;
use core::str::FromStr;
use core::time::Duration;
use std::hash::DefaultHasher;
use std::sync::Mutex;
use std::time::Instant;

use anodized::spec;
use gandr_core_checker::fork::Fork;
use gandr_core_checker::fork::Serial;
use gandr_core_checker::staging;
use gandr_core_checker::staging::Allowance;
use gandr_core_checker::staging::Checked;
use gandr_core_checker::staging::ProgramError;
use gandr_core_checker::staging::Readmission;
use gandr_core_checker::template::Clock;
use gandr_core_checker::template::FamilyAdmission;
use gandr_core_checker::template::Memo;
use gandr_core_checker::template::PriceGate;
use gandr_core_checker::template::ProgramId;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Extent;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;

use crate::width::Threads;
use crate::width::Width;

/// The work each job of a staged check may spend: ample for every program the
/// verb builds at exponents into the hundreds.
const ALLOWANCE: Allowance = Allowance {
    normalizing: Budget(100_000_000),
    replaying: Budget(100_000_000),
    admitting: Budget(1_000_000_000),
};

/// The admission price every family is checked under: the memo's.
const GATE: PriceGate = PriceGate::Memoized;

/// A staging observer program's body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Body
{
    /// `pow`, `λn. λx. iter n <1> (λp.<~x * ~p>)`, its input left free under a
    /// quoted lambda.
    Power,
    /// `double`, `λn. λx. iter n <1> (λp.<~x * ~p * ~x>)`, over the inner
    /// inputs two and three.
    Double,
}

/// One program the `stage` verb checks: its body specialized at every
/// exponent of an inclusive range, spelled `pow:LO..HI` or `double:LO..HI`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProgramSpec
{
    /// The body.
    body: Body,
    /// The first exponent.
    low: Natural,
    /// The last exponent, at or above the first.
    high: Natural,
}

/// Why a spelling names no program.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpecError
{
    /// No `body:LO..HI` shape.
    Shape,
    /// The body is neither `pow` nor `double`.
    Body,
    /// An exponent is not a natural number.
    Exponent,
    /// The range ends before it starts.
    Reversed,
}

impl fmt::Display for SpecError
{
    /// Say what the spelling lacks.
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
            Self::Shape => "expected `pow:LO..HI` or `double:LO..HI`",
            Self::Body => "the program is neither `pow` nor `double`",
            Self::Exponent => "an exponent is not a natural number",
            Self::Reversed => "the range ends before it starts",
        })
    }
}

impl core::error::Error for SpecError
{
}

impl FromStr for ProgramSpec
{
    type Err = SpecError;

    /// Read `pow:LO..HI` or `double:LO..HI`, both exponents inclusive.
    ///
    /// # Specification
    /// - ensures: the body the prefix names, at `LO ..= HI` in decimal.
    /// - fails: [`SpecError::Shape`] without a colon and `..`,
    ///   [`SpecError::Body`] for another prefix, [`SpecError::Exponent`] for an
    ///   exponent that is not a decimal natural, [`SpecError::Reversed`] when
    ///   `HI < LO`.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the [`SpecError`] that applies first, in the order above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refusal and both bodies at a single exponent and
    ///   a range have exact answers, and every accepted spelling prints back
    ///   unchanged.
    /// - witness: `stage::tests::spellings_read_and_print_alike`
    #[inline]
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|spec| spec.low <= spec.high))]
    fn from_str(spelling: &str) -> Result<Self, SpecError>
    {
        let (body, range) = spelling.split_once(':').ok_or(SpecError::Shape)?;
        let (low, high) = range.split_once("..").ok_or(SpecError::Shape)?;
        let body = match body {
            "pow" => Body::Power,
            "double" => Body::Double,
            _ => return Err(SpecError::Body),
        };
        let low = low.parse().map_err(|_unparsed| SpecError::Exponent)?;
        let high = high.parse().map_err(|_unparsed| SpecError::Exponent)?;
        if high < low {
            return Err(SpecError::Reversed);
        }
        Ok(Self {
            body,
            low: Natural(low),
            high: Natural(high),
        })
    }
}

impl fmt::Display for ProgramSpec
{
    /// The spelling the program was read from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let body = match self.body {
            Body::Power => "pow",
            Body::Double => "double",
        };
        write!(f, "{body}:{}..{}", self.low.0, self.high.0)
    }
}

impl ProgramSpec
{
    /// Build the program in a fresh arena: the model's hypothesis, the body,
    /// then one source per exponent — the power's `<λx. ~(pow n <x>)>`, the
    /// double's `double n <2>` and `double n <3>`.
    ///
    /// # Specification
    /// - ensures: one source per exponent for the power and two for the double,
    ///   exponents ascending, under the one hypothesis `In 0`.
    /// - fails: the arena's coordinate bound.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Overflow`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every source built normalizes and readmits through
    ///   the kernel, and the double's twice the power's count.
    /// - witness: `stage::tests::every_width_stages_the_serial_run`
    #[inline]
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|program|
        program.sources.len() == self.high.0.saturating_sub(self.low.0).saturating_add(1)
            .saturating_mul(match self.body { Body::Power => 1, Body::Double => 2 })))]
    pub fn program(
        self,
        id: ProgramId,
    ) -> Result<staging::Program, StageError>
    {
        let mut arena = Arena::default();
        let model = Model(0);
        let hypothesis = arena.alloc_type(Type::In(model))?;
        let inner = arena.alloc_type(Type::Nat(Stage::Inner(model)))?;
        let function = match self.body {
            Body::Power => gandr_core_nbe::stage::power(&mut arena, model)?,
            Body::Double => gandr_core_nbe::stage::double(&mut arena, model)?,
        };
        let mut sources = Vec::new();
        for exponent in self.low.0 ..= self.high.0 {
            let numeral = arena.alloc(Term::Natural(Stage::Outer, Natural(exponent)))?;
            let applied = arena.alloc(Term::Apply(function, numeral))?;
            match self.body {
                Body::Power => {
                    let input = arena.alloc(Term::Variable(Index(0)))?;
                    let input = arena.alloc(Term::Quote(input))?;
                    let source = arena.alloc(Term::Apply(applied, input))?;
                    let source = arena.alloc(Term::Splice(source))?;
                    let source = arena.alloc(Term::Lambda(inner, source))?;
                    let source = arena.alloc(Term::Quote(source))?;
                    sources.push(source);
                },
                Body::Double => {
                    for input in [Natural(2), Natural(3)] {
                        let input = arena.alloc(Term::Natural(Stage::Inner(model), input))?;
                        let input = arena.alloc(Term::Quote(input))?;
                        let source = arena.alloc(Term::Apply(applied, input))?;
                        sources.push(source);
                    }
                },
            }
        }
        Ok(staging::Program {
            arena,
            context: Vec::from([hypothesis]),
            sources,
            id,
        })
    }
}

/// The process's monotonic clock, from the run's start.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
struct Monotonic(Instant);

impl Clock for Monotonic
{
    /// Time since the run started.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn now(&mut self) -> Duration
    {
        self.0.elapsed()
    }
}

/// The pool the driver's width runs on, as the checker's fork: each forked
/// stage spawns one task per worker, at most one per item, and each task
/// takes items from one shared cursor until none is left.
///
/// # Specification
/// - provides: a [`Fork`] whose every task makes its worker state once, on its
///   first item, so a stage clones no more snapshots than it has workers with
///   work; halves join through `rayon::join`.
/// - panics: none of its own; a job's panic resumes at the fork.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L2 — programs checked at three workers and at the host's width
///   print the serial run, digest and verdict.
/// - witness: `stage::tests::every_width_stages_the_serial_run`
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
struct Pooled(Threads);

impl Fork for Pooled
{
    /// Run `job` on every item from one task per worker, each taking items
    /// from a shared cursor.
    ///
    /// # Specification
    /// - ensures: `job` runs once per item; each task makes its state on its
    ///   first item and keeps it for the rest. A stage of one item, or a pool
    ///   of one worker, runs on the calling thread.
    /// - panics: a job's panic, at the end of the scope.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no item, one item, fewer items than workers and many
    ///   more, counting each item's visits and the states made, distinguish a
    ///   skipped or repeated item and a state made per item or per idle worker.
    /// - witness: `stage::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    #[inline]
    fn each<Item, State, Start, Job>(
        &self,
        items: &mut [Item],
        start: Start,
        job: Job,
    ) where
        Item: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
    {
        let workers = NonZeroUsize::from(self.0).get().min(items.len());
        if workers <= 1 {
            Serial.each(items, start, job);
            return;
        }
        let cursor = Mutex::new(items.iter_mut());
        rayon::scope(|scope| {
            for _ in 0 .. workers {
                scope.spawn(|_| {
                    let mut state = None;
                    loop {
                        // A poisoned cursor only means another task's job
                        // panicked; the panic resumes when the scope ends.
                        let next = match cursor.lock() {
                            Ok(mut items) => items.next(),
                            Err(poisoned) => poisoned.into_inner().next(),
                        };
                        let Some(item) = next
                        else {
                            break;
                        };
                        job(state.get_or_insert_with(&start), item);
                    }
                });
            }
        });
    }

    /// Run both halves through `rayon::join`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn join<Left, Right, LeftOutput, RightOutput>(
        &self,
        left: Left,
        right: Right,
    ) -> (LeftOutput, RightOutput)
    where
        Left: FnOnce() -> LeftOutput + Send,
        Right: FnOnce() -> RightOutput + Send,
        LeftOutput: Send,
        RightOutput: Send,
    {
        rayon::join(left, right)
    }
}

/// Where a staged check's jobs run.
#[derive(Debug)]
enum Workers
{
    /// The calling thread alone.
    Serial,
    /// A pool, and the fork over it.
    Pooled(rayon::ThreadPool, Pooled),
}

impl Workers
{
    /// Check `program` through `memo` on these workers.
    ///
    /// # Specification
    /// - ensures: what [`staging::check`] returns for the program at the verb's
    ///   gate and allowance, on the calling thread or inside the pool.
    /// - fails: as [`staging::check`].
    /// - panics: none of its own.
    /// - executable: none — a dispatch to [`staging::check`], whose contract
    ///   carries the postcondition.
    ///
    /// # Errors
    /// Returns the [`ProgramError`] of the first source that failed.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Pooled`].
    /// - witness: `stage::tests::every_width_stages_the_serial_run`
    fn check(
        &self,
        program: staging::Program,
        memo: &mut Memo,
        clock: &Monotonic,
    ) -> Result<Checked, ProgramError>
    {
        match *self {
            Self::Serial => staging::check(program, memo, GATE, ALLOWANCE, &Serial, clock),
            Self::Pooled(ref pool, ref fork) => {
                pool.install(|| staging::check(program, memo, GATE, ALLOWANCE, fork, clock))
            },
        }
    }
}

/// Why the verb could not start its pool.
#[derive(Debug)]
#[repr(transparent)]
pub struct PoolFault(rayon::ThreadPoolBuildError);

impl fmt::Display for PoolFault
{
    /// Name the pool's error.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "the worker pool did not start: {}", self.0)
    }
}

impl core::error::Error for PoolFault
{
}

/// The `stage` verb's run, not yet started: its programs, in order, and the
/// width to check them at.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Staging
{
    /// The programs, in order.
    programs: Vec<ProgramSpec>,
    /// The workers each program's stages fork onto.
    width: Width,
}

/// Why one program has no check: it could not be built, or a source failed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StageFault
{
    /// The program's syntax did not fit the arena.
    Built(StageError),
    /// A source failed to normalize, merge or harvest.
    Checked(ProgramError),
}

impl fmt::Display for StageFault
{
    /// Name the failure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Built(error) => write!(f, "the program was not built: {error}"),
            Self::Checked(error) => write!(f, "{error}"),
        }
    }
}

/// One program of a run, checked.
#[derive(Debug)]
pub struct Staged
{
    /// The program's spelling.
    spec: ProgramSpec,
    /// Its check, or why it has none.
    outcome: Result<Checked, StageFault>,
}

impl Staged
{
    /// The program's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn spec(&self) -> ProgramSpec
    {
        self.spec
    }

    /// The program's check, or why it has none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn outcome(&self) -> &Result<Checked, StageFault>
    {
        &self.outcome
    }
}

/// The summary's count of each family admission class.
#[derive(Clone, Copy, Debug, Default)]
struct Classes
{
    /// Admitted whole.
    admitted: usize,
    /// Admitted for the template subfamily alone.
    partial: usize,
    /// Left plain.
    plain: usize,
    /// Refused by the kernel.
    refused: usize,
    /// Over the kernel's work bound.
    bound: usize,
    /// Whose admission failed.
    faulted: usize,
}

impl Classes
{
    /// Count every admission.
    ///
    /// # Specification
    /// - ensures: each admission counted once, under its class.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the summary lines of the power and double programs
    ///   count every family at every width.
    /// - witness: `stage::tests::every_width_stages_the_serial_run`
    #[spec(ensures: |output| [output.admitted, output.partial, output.plain, output.refused,
        output.bound, output.faulted].iter().sum::<usize>() == checked.admissions.len())]
    fn of(checked: &Checked) -> Self
    {
        let mut classes = Self::default();
        for admission in &checked.admissions {
            let count = match *admission {
                Ok(ref report) => match report.admission {
                    FamilyAdmission::Admitted { .. } => &mut classes.admitted,
                    FamilyAdmission::Partial { .. } => &mut classes.partial,
                    FamilyAdmission::Plain(_) => &mut classes.plain,
                    FamilyAdmission::Refused(_) => &mut classes.refused,
                    FamilyAdmission::WorkBoundExceeded(_) => &mut classes.bound,
                },
                Err(_) => &mut classes.faulted,
            };
            *count = count.saturating_add(1);
        }
        classes
    }
}

impl fmt::Display for Staged
{
    /// One line: the spelling, the certificates readmitted, and each family
    /// class's count; or the spelling and the fault.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let checked = match self.outcome {
            Ok(ref checked) => checked,
            Err(fault) => return write!(f, "{}: {fault}", self.spec),
        };
        let readmitted = checked
            .readmissions
            .iter()
            .filter(|readmission| **readmission == Readmission::Readmitted)
            .count();
        let Classes {
            admitted,
            partial,
            plain,
            refused,
            bound,
            faulted,
        } = Classes::of(checked);
        write!(
            f,
            "{}: {readmitted} of {} certificates readmitted; {} families: {admitted} admitted, \
             {partial} partial, {plain} plain, {refused} refused, {bound} over the work bound, \
             {faulted} faulted",
            self.spec,
            checked.readmissions.len(),
            checked.admissions.len(),
        )
    }
}

/// The verb's verdict over its whole run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StageVerdict
{
    /// Every certificate was readmitted and every family admitted without a
    /// fault.
    Readmitted,
    /// The kernel refused a certificate.
    Refused,
    /// A program could not be checked, or a family's admission failed.
    Faulted,
}

impl fmt::Display for StageVerdict
{
    /// The verdict's name.
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
            Self::Readmitted => "readmitted",
            Self::Refused => "refused",
            Self::Faulted => "faulted",
        })
    }
}

/// A digest of everything a run decided: what no width, clock or schedule
/// may change.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct RunDigest(u64);

impl fmt::Display for RunDigest
{
    /// Sixteen hexadecimal digits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{:016x}", self.0)
    }
}

/// Text written straight into a hasher, so a digest formats without
/// allocating.
#[repr(transparent)]
struct Feed<'hasher>(&'hasher mut DefaultHasher);

impl fmt::Write for Feed<'_>
{
    /// Hash the text's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_str(
        &mut self,
        s: &str,
    ) -> fmt::Result
    {
        self.0.write(s.as_bytes());
        Ok(())
    }
}

/// A run's programs, checked in order.
#[derive(Debug)]
#[repr(transparent)]
pub struct StageRun
{
    /// Each program's check, in order.
    programs: Vec<Staged>,
}

impl StageRun
{
    /// Each program's check, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn programs(&self) -> &[Staged]
    {
        &self.programs
    }

    /// The run's verdict: faulted when any program or family admission
    /// faulted, refused when the kernel refused any certificate, readmitted
    /// otherwise.
    ///
    /// # Specification
    /// - ensures: `Faulted` exactly when a program has no check or an admission
    ///   failed; otherwise `Refused` exactly when a readmission was refused.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — a readmitted run, an unbuildable program, a
    ///   refused certificate and a faulted admission give each verdict, and a
    ///   fault outranks a refusal in any order.
    /// - witness: `stage::tests::every_width_stages_the_serial_run`
    /// - witness: `stage::tests::a_fault_outranks_a_refusal`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every program's admissions and readmissions once; the check walks the admissions once"
        )
    )]
    #[spec(ensures: |output| (output == StageVerdict::Faulted) == self.programs.iter().any(|staged|
        staged.outcome.as_ref().map_or(true, |checked| checked.admissions.iter().any(Result::is_err))))]
    pub fn verdict(&self) -> StageVerdict
    {
        let mut verdict = StageVerdict::Readmitted;
        for staged in &self.programs {
            let Ok(ref checked) = staged.outcome
            else {
                return StageVerdict::Faulted;
            };
            if checked.admissions.iter().any(Result::is_err) {
                return StageVerdict::Faulted;
            }
            if checked
                .readmissions
                .iter()
                .any(|readmission| *readmission != Readmission::Readmitted)
            {
                verdict = StageVerdict::Refused;
            }
        }
        verdict
    }

    /// The run's digest: each program's spelling and, for a checked program,
    /// its merged syntax, certificates, readmissions, families and each
    /// admission's class and schema; for a faulted one, the fault.
    ///
    /// # Specification
    /// - ensures: a fold of every decision the run made and of nothing the
    ///   schedule or the clock decides: no time, and no admission's origin or
    ///   drafting, which the memo's controller decides by time.
    /// - panics: none.
    /// - intension: equal runs digest equally on one build; the digest is not
    ///   stable across toolchains.
    /// - executable: none — a hash; the witnesses compare digests across widths
    ///   and program lists.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — runs at one, three and the host's workers digest
    ///   alike, and a different program list digests differently.
    /// - witness: `stage::tests::every_width_stages_the_serial_run`
    #[inline]
    #[must_use]
    #[expect(
        clippy::use_debug,
        reason = "the digest folds the outputs' complete structural rendering; the kernel's \
                  and checker's output types carry Debug, not Hash"
    )]
    pub fn digest(&self) -> RunDigest
    {
        let mut hasher = DefaultHasher::new();
        let whole = Extent {
            terms: TermId(0),
            types: TypeId(0),
        };
        for staged in &self.programs {
            let mut feed = Feed(&mut hasher);
            // Formatting into the hasher cannot fail: `Feed` never errs.
            let _written = writeln!(feed, "{}", staged.spec);
            let checked = match staged.outcome {
                Ok(ref checked) => checked,
                Err(fault) => {
                    let _written = writeln!(feed, "{fault}");
                    continue;
                },
            };
            let _written = write!(
                feed,
                "{:?}{:?}{:?}{:?}{:?}",
                checked.arena.types_above(whole),
                checked.arena.terms_above(whole),
                checked.certificates,
                checked.readmissions,
                checked.families,
            );
            for admission in &checked.admissions {
                let _written = match *admission {
                    Ok(ref report) => match report.admission {
                        FamilyAdmission::Admitted { ref schema, .. } => {
                            write!(feed, "admitted {schema:?}")
                        },
                        ref other @ (FamilyAdmission::Partial { .. }
                        | FamilyAdmission::Plain(_)
                        | FamilyAdmission::WorkBoundExceeded(_)
                        | FamilyAdmission::Refused(_)) => write!(feed, "{other:?}"),
                    },
                    Err(error) => write!(feed, "{error}"),
                };
            }
        }
        RunDigest(hasher.finish())
    }
}

impl Staging
{
    /// The run of `programs`, in order, at `width`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        programs: Vec<ProgramSpec>,
        width: Width,
    ) -> Self
    {
        Self { programs, width }
    }

    /// The programs, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn programs(&self) -> &[ProgramSpec]
    {
        &self.programs
    }

    /// The width the run forks at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn width(&self) -> Width
    {
        self.width
    }

    /// Build and check every program in order through one memo, forking each
    /// program's stages on a pool of the run's width.
    ///
    /// # Specification
    /// - ensures: one check per program, in order: the `n`th program is
    ///   harvested as producer `n` and drafts from the templates every earlier
    ///   one left. At one thread no pool is built and every stage runs on the
    ///   calling thread; wider, one pool of that many workers is built and
    ///   every program checks inside it. Every line, the digest and the verdict
    ///   are the same at every width.
    /// - fails: the pool's build error.
    /// - panics: none of its own.
    ///
    /// # Errors
    /// Returns [`PoolFault`] when the pool does not start.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the power and double programs run at one, three and
    ///   the host's workers and are compared line for line, digest and verdict.
    /// - witness: `stage::tests::every_width_stages_the_serial_run`
    #[inline]
    #[spec(captures: [programs = self.programs.len()],
        ensures: |output| output.as_ref().ok().is_none_or(|run| run.programs.len() == programs))]
    pub fn run(self) -> Result<StageRun, PoolFault>
    {
        let threads = self.width.threads();
        let workers = if threads == Threads::ONE {
            Workers::Serial
        }
        else {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(NonZeroUsize::from(threads).get())
                .build()
                .map_err(PoolFault)?;
            Workers::Pooled(pool, Pooled(threads))
        };
        let clock = Monotonic(Instant::now());
        let mut memo = Memo::default();
        let mut programs = Vec::with_capacity(self.programs.len());
        for (index, spec) in self.programs.into_iter().enumerate() {
            let outcome = match spec.program(ProgramId(index)) {
                Ok(program) => workers
                    .check(program, &mut memo, &clock)
                    .map_err(StageFault::Checked),
                Err(error) => Err(StageFault::Built(error)),
            };
            programs.push(Staged { spec, outcome });
        }
        Ok(StageRun { programs })
    }
}

#[cfg(test)]
mod tests
{
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering;

    use super::*;

    #[test]
    fn spellings_read_and_print_alike()
    {
        for spelling in ["pow:0..8", "double:0..32", "pow:7..7", "double:3..12"] {
            let spec: ProgramSpec = spelling.parse().unwrap();
            assert_eq!(spec.to_string(), spelling);
        }
        assert_eq!(
            "double:2..5".parse(),
            Ok(ProgramSpec {
                body: Body::Double,
                low: Natural(2),
                high: Natural(5),
            })
        );
        for (spelling, error) in [
            ("pow", SpecError::Shape),
            ("pow:3", SpecError::Shape),
            ("triple:0..4", SpecError::Body),
            ("pow:a..4", SpecError::Exponent),
            ("pow:0..-1", SpecError::Exponent),
            ("pow:0..", SpecError::Exponent),
            ("double:5..4", SpecError::Reversed),
        ] {
            assert_eq!(spelling.parse::<ProgramSpec>(), Err(error), "{spelling}");
        }
    }

    /// The run of `programs` at `width`: each program's line, the digest and
    /// the verdict.
    ///
    /// # Specification
    /// trivial.
    fn printed(
        programs: &[ProgramSpec],
        width: Width,
    ) -> (Vec<String>, RunDigest, StageVerdict)
    {
        let run = Staging::new(programs.to_vec(), width).run().unwrap();
        (
            run.programs().iter().map(ToString::to_string).collect(),
            run.digest(),
            run.verdict(),
        )
    }

    #[test]
    fn every_width_stages_the_serial_run()
    {
        let three = Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(2)));
        let spellings = ["pow:0..8", "double:0..8", "pow:0..12", "double:4..12"]
            .map(|spelling| spelling.parse::<ProgramSpec>().unwrap());
        let serial = printed(&spellings, Width::SERIAL);
        assert_eq!(serial.2, StageVerdict::Readmitted);
        assert!(
            serial.0[0].starts_with("pow:0..8: 9 of 9 certificates readmitted;"),
            "{:?}",
            serial.0
        );
        assert!(
            serial.0[1].starts_with("double:0..8: 18 of 18 certificates readmitted;"),
            "{:?}",
            serial.0
        );
        for width in [three, Width::PerformanceCores] {
            assert_eq!(printed(&spellings, width), serial, "{width:?}");
        }
        let reordered = ["double:0..8", "pow:0..8"].map(|spelling| spelling.parse().unwrap());
        assert_ne!(
            printed(&reordered, Width::SERIAL).1,
            printed(&spellings[.. 2], Width::SERIAL).1
        );
    }

    #[test]
    fn a_pool_visits_each_item_once_from_a_state_per_busy_worker()
    {
        let workers = 4_usize;
        let fork = Pooled(Threads::from(NonZeroUsize::new(workers).unwrap()));
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        for count in [0_usize, 1, 3, 64] {
            let made = AtomicUsize::new(0);
            let mut visits = vec![0_usize; count];
            pool.install(|| {
                fork.each(
                    &mut visits,
                    || {
                        made.fetch_add(1, Ordering::Relaxed);
                    },
                    |_state, visited| *visited = visited.checked_add(1).unwrap(),
                );
            });
            assert!(visits.iter().all(|&visited| visited == 1), "{count} items");
            let made = made.load(Ordering::Relaxed);
            assert_eq!(made == 0, count == 0, "{count} items");
            assert!(
                made <= count.min(workers),
                "{made} states for {count} items"
            );
        }
    }

    #[test]
    fn a_fault_outranks_a_refusal()
    {
        let spec: ProgramSpec = "pow:0..0".parse().unwrap();
        let refused = || Staged {
            spec,
            outcome: Ok(Checked {
                arena: Arena::default(),
                certificates: Vec::new(),
                readmissions: Vec::from([
                    Readmission::Readmitted,
                    Readmission::Refused(StageError::Exhausted),
                ]),
                families: Vec::new(),
                admissions: Vec::new(),
                spent: staging::Stages::default(),
            }),
        };
        let unbuilt = || Staged {
            spec,
            outcome: Err(StageFault::Built(StageError::Overflow)),
        };
        let failed = || Staged {
            spec,
            outcome: Ok(Checked {
                arena: Arena::default(),
                certificates: Vec::new(),
                readmissions: Vec::new(),
                families: Vec::new(),
                admissions: Vec::from([Err(StageError::Exhausted)]),
                spent: staging::Stages::default(),
            }),
        };
        let verdict = |programs: Vec<Staged>| StageRun { programs }.verdict();
        assert_eq!(verdict(Vec::from([refused()])), StageVerdict::Refused);
        assert_eq!(verdict(Vec::new()), StageVerdict::Readmitted);
        for pair in [
            [refused(), unbuilt()],
            [unbuilt(), refused()],
            [refused(), failed()],
            [failed(), refused()],
        ] {
            assert_eq!(verdict(Vec::from(pair)), StageVerdict::Faulted);
        }
        assert_eq!(
            unbuilt().to_string(),
            "pow:0..0: the program was not built: stage arithmetic overflow"
        );
    }
}
