//! The dovetailing scheduler: a run of a set of obligations in bounded
//! quanta, in a fixed order, within a budget.
//!
//! A run visits the live obligations in the order that the caller gave them.
//! Each visit is a turn, and a turn does at most one [`Quantum`] of steps on
//! one obligation. A round is one turn for each live obligation. So no
//! obligation that never settles keeps a later obligation from its quantum:
//! each live obligation gets its quantum once in each round. A [`Budget`]
//! bounds the total steps of a run, and a run never goes past it. A run stops
//! when every obligation settles, at its limit of [`Rounds`], when its budget
//! is spent, or at a cancellation that the caller signals between turns.
//!
//! The scheduler keeps its place between runs. A run that stops inside a
//! round leaves the next turn where it stopped, so a later run goes on with
//! the same obligation. The order of turns depends only on the obligations,
//! the quantum and the run limits, so two schedulers given the same input do
//! the same steps.
//!
//! # Items
//!
//! - [`Dovetail`] — the scheduler and its obligations.
//! - [`Quantum`], [`Budget`], [`Rounds`] — the bounds of a turn and of a run.
//! - [`Report`] — what a run did, and each obligation's outcome.

use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU32;
use core::ops::Deref;

use anodized::spec;

use crate::bisection::PieceCount;
use crate::cache::Cache;
use crate::cache::CacheRefusal;
use crate::cache::Lookup;
use crate::certificate::CertificateRefusal;
use crate::certificate::CheckerQuotas;
use crate::certificate::StepCount;
use crate::codec::CheckpointBytes;
use crate::codec::DecodeError;
use crate::codec::EncodedCheckpoint;
use crate::codec::read_checkpoint;
use crate::codec::write_checkpoint;
use crate::plan::PlanError;
use crate::semidecision::Obligation;
use crate::semidecision::Outcome;
use crate::semidecision::Progress;
use crate::validate::ValidatedPlan;

/// Why a checkpoint does not resume.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResumeError
{
    /// The bytes are malformed, or they are not canonical.
    Decode(DecodeError),
    /// The quantum is no steps.
    Quantum,
    /// The cursor names no live obligation.
    Cursor,
    /// An obligation names no node of the plan, or a node of another sort
    /// than its demand takes.
    Obligation(PlanError),
    /// The steps of an obligation do not replay.
    Replay(CertificateRefusal),
    /// The steps replay, but the machine does not write them for a live
    /// obligation: a chain of another node, a split of an enclosure that a
    /// later step narrows, or a step that concludes.
    Steps,
}

impl fmt::Display for ResumeError
{
    /// Write the refusal as one line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return match *self {
            Self::Decode(ref error) => write!(f, "the checkpoint's bytes are refused: {error}"),
            Self::Quantum => f.write_str("the checkpoint's quantum is no steps"),
            Self::Cursor => f.write_str("the checkpoint's cursor names no live obligation"),
            Self::Obligation(ref error) => {
                write!(f, "an obligation of the checkpoint names no node of its sort: {error}")
            },
            Self::Replay(ref refusal) => {
                write!(f, "the steps of an obligation of the checkpoint do not replay: {refusal}")
            },
            Self::Steps => f.write_str(
                "the steps of an obligation of the checkpoint are not steps that the machine writes for a live obligation",
            ),
        };
    }
}

impl core::error::Error for ResumeError
{
}

/// The most steps that one turn does on one obligation.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Quantum(NonZeroU32);

impl From<NonZeroU32> for Quantum
{
    /// The quantum of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: NonZeroU32) -> Self
    {
        return Self(steps);
    }
}

impl From<Quantum> for u64
{
    /// The steps of the quantum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(quantum: Quantum) -> Self
    {
        return core::num::NonZeroU64::from(quantum.0).get();
    }
}

impl From<Quantum> for NonZeroU32
{
    /// The steps of the quantum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(quantum: Quantum) -> Self
    {
        return quantum.0;
    }
}

/// The most steps that one run does in total.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Budget(u64);

impl From<u64> for Budget
{
    /// The budget of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: u64) -> Self
    {
        return Self(steps);
    }
}

/// The most rounds that one run completes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rounds(u64);

impl From<u64> for Rounds
{
    /// The limit of `rounds` rounds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rounds: u64) -> Self
    {
        return Self(rounds);
    }
}

/// The place of an obligation in the order of turns.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Position(usize);

impl From<usize> for Position
{
    /// The obligation at `index` in the order of turns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        return Self(index);
    }
}

impl From<Position> for usize
{
    /// The index of the obligation in the order of turns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: Position) -> Self
    {
        return position.0;
    }
}

/// A count of certificate steps.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Steps(u64);

impl From<u64> for Steps
{
    /// The count of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: u64) -> Self
    {
        return Self(steps);
    }
}

impl From<Steps> for u64
{
    /// The steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: Steps) -> Self
    {
        return steps.0;
    }
}

/// The work of one run.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Work
{
    /// The certificate steps that the run did.
    pub steps: u64,
    /// The rounds that the run completed.
    pub rounds: u64,
}

/// Why a run stopped.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Stop
{
    /// Every obligation settled.
    Settled,
    /// The run completed its limit of rounds.
    Rounds,
    /// The run spent its budget.
    Budget,
    /// The caller signalled a cancellation.
    Cancelled,
}

/// One obligation in the scheduler, and the steps done on it over all runs.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Entry
{
    /// The work on the obligation.
    progress: Progress,
    /// The steps done on the obligation.
    spent: u64,
}

/// The scheduler: the obligations of a run over one validated plan, the
/// bounds of each turn, and the place of the next turn.
///
/// The scheduler holds its plan through `Plan`: a borrow of the plan, or a
/// holder that shares it, so a scheduler can stay beside the plan it runs.
///
/// # Specification
/// - invariant: `cursor` is below the number of obligations, or zero when there
///   is none, and `live` counts the obligations that are live.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Dovetail<Plan>
{
    /// The plan that the obligations name.
    plan: Plan,
    /// The most steps of one turn.
    quantum: Quantum,
    /// The bounds of each certificate.
    quotas: CheckerQuotas,
    /// The obligations, in the order of their turns.
    entries: Vec<Entry>,
    /// The obligation of the next turn.
    cursor: usize,
    /// The number of live obligations.
    live: usize,
}

impl<Plan> Dovetail<Plan>
where
    Plan: Deref<Target = ValidatedPlan>,
{
    /// The scheduler of `obligations` over `plan`, each turn at most `quantum`
    /// steps, each certificate within `quotas`.
    ///
    /// # Specification
    /// - ensures: every obligation is live, and the first turn goes to the
    ///   first obligation.
    /// - panics: none.
    /// - intension: one record for each obligation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::run`].
    /// - witness: `tests::dovetail::two_obligations_run_round_by_round`
    #[spec(ensures: |ref result| result.live == result.entries.len() && result.cursor == 0)]
    #[inline]
    #[must_use]
    pub fn new<Obligations>(
        plan: Plan,
        obligations: Obligations,
        quantum: Quantum,
        quotas: CheckerQuotas,
    ) -> Self
    where
        Obligations: IntoIterator<Item = Obligation>,
    {
        let entries: Vec<Entry> = obligations
            .into_iter()
            .map(|obligation| Entry {
                progress: Progress::new(obligation),
                spent: 0,
            })
            .collect();
        return Self {
            plan,
            quantum,
            quotas,
            live: entries.len(),
            entries,
            cursor: 0,
        };
    }

    /// Run the obligations in turns until they settle, `rounds` rounds
    /// complete, `budget` is spent, or `cancelled` answers `true`.
    ///
    /// # Specification
    /// - ensures: each turn goes to the obligation at the cursor when it is
    ///   live, and does at most a quantum of steps on it, or the rest of the
    ///   budget when that is less. A round completes when the cursor passes the
    ///   last obligation. `cancelled` is asked before each turn on a live
    ///   obligation, and the run stops before that turn when it answers `true`.
    ///   The run does at most `budget` steps. A run with a limit of no rounds
    ///   does nothing. A run that starts inside a round completes that round,
    ///   and the round counts.
    /// - provides: the minimum service of every live obligation: in each round
    ///   that completes within the budget, each live obligation gets its
    ///   quantum or settles.
    /// - panics: none.
    /// - intension: each turn is linear in the quantum; a round is linear in
    ///   the obligations.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated obligations under generated quanta, budgets
    ///   and rounds: the work stays within the budget, each certificate
    ///   replays, and two schedulers given one input agree. L3 — a settling
    ///   obligation behind and before one that never settles, a budget that
    ///   ends inside a turn, and a cancellation inside a round, each resumed.
    /// - witness: `tests::dovetail::two_obligations_run_round_by_round`
    /// - witness: `tests::dovetail::each_live_obligation_gets_its_quantum_in_each_round`
    /// - witness: `tests::dovetail::a_run_past_its_budget_is_exhausted_and_resumes`
    /// - witness: `tests::dovetail::a_cancelled_run_resumes_at_the_next_turn`
    /// - witness: `tests::dovetail::every_certificate_replays_to_its_evidence`
    #[spec(ensures: |ref report| report.work.steps <= budget.0)]
    #[inline]
    pub fn run<Cancelled>(
        &mut self,
        budget: Budget,
        rounds: Rounds,
        mut cancelled: Cancelled,
    ) -> Report<'_, Plan>
    where
        Cancelled: FnMut() -> bool,
    {
        let mut work = Work::default();
        let stop = loop {
            if self.live == 0 {
                break Stop::Settled;
            }
            if rounds.0 == 0 || (self.cursor == 0 && work.rounds >= rounds.0) {
                break Stop::Rounds;
            }
            let plan: &ValidatedPlan = &self.plan;
            let quotas = self.quotas;
            if let Some(entry) = self
                .entries
                .get_mut(self.cursor)
                .filter(|entry| entry.progress.settled().is_none())
            {
                if cancelled() {
                    break Stop::Cancelled;
                }
                let left = budget.0.saturating_sub(work.steps);
                if left == 0 {
                    break Stop::Budget;
                }
                let allowance = Steps(left.min(u64::from(self.quantum)));
                let done = entry.progress.advance(plan, allowance, &quotas).0;
                entry.spent = entry.spent.saturating_add(done);
                work.steps = work.steps.saturating_add(done);
                if entry.progress.settled().is_some() {
                    self.live = self.live.saturating_sub(1);
                }
            }
            self.cursor = self.cursor.saturating_add(1);
            if self.cursor >= self.entries.len() {
                self.cursor = 0;
                work.rounds = work.rounds.saturating_add(1);
            }
        };
        return Report {
            dovetail: self,
            stop,
            work,
        };
    }

    /// The steps done on the obligation at `position` over all runs, or `None`
    /// past the obligations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn spent(
        &self,
        position: Position,
    ) -> Option<Steps>
    {
        return self.entries.get(position.0).map(|entry| Steps(entry.spent));
    }

    /// The certificate steps written so far for the obligation at `position`,
    /// or `None` past the obligations. A resumed scheduler replays these
    /// steps in [`Self::resume`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn written(
        &self,
        position: Position,
    ) -> Option<StepCount>
    {
        return self
            .entries
            .get(position.0)
            .map(|entry| StepCount::from(entry.progress.steps().len()));
    }

    /// The most pieces that the search of the obligation at `position` holds
    /// at once, or `None` past the obligations. The count is zero for an
    /// obligation that searches no domain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn regions(
        &self,
        position: Position,
    ) -> Option<PieceCount>
    {
        return self
            .entries
            .get(position.0)
            .map(|entry| entry.progress.regions());
    }

    /// The obligation at `position`, or `None` past the obligations. A resumed
    /// scheduler holds only the obligations that were live at its checkpoint,
    /// so a position names an obligation of this scheduler alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn obligation(
        &self,
        position: Position,
    ) -> Option<Obligation>
    {
        return self
            .entries
            .get(position.0)
            .map(|entry| entry.progress.obligation());
    }

    /// Settle each obligation that has no step yet from `cache`, and the
    /// refusals of the entries that left it.
    ///
    /// # Specification
    /// - ensures: an obligation that the cache answers settles with the cached
    ///   certificate, which replays against the scheduler's plan within its
    ///   quotas, and it spends no step. An obligation with steps stays as it
    ///   is. A scheduler that never consults a cache does no work for one.
    /// - panics: none.
    /// - executable: none — the clause speaks of the certificate's replay.
    /// - intension: one lookup for each obligation that has no step.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every obligation of the machine's test corpus settles
    ///   alike from the cache and from a run. L3 — a refused entry.
    /// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
    /// - witness: `tests::cache::an_entry_that_does_not_replay_leaves_by_name`
    #[inline]
    pub fn consult(
        &mut self,
        cache: &mut Cache,
    ) -> Vec<(Position, CacheRefusal)>
    {
        let mut refusals = Vec::new();
        for (index, entry) in self.entries.iter_mut().enumerate() {
            let Some(obligation) = entry.progress.fresh()
            else {
                continue;
            };
            match cache.lookup(&self.plan, obligation, &self.quotas) {
                Lookup::Hit(certificate) => {
                    entry.progress.adopt(certificate);
                    self.live = self.live.saturating_sub(1);
                },
                Lookup::Miss => {},
                Lookup::Refused(refusal) => refusals.push((Position(index), refusal)),
            }
        }
        return refusals;
    }

    /// Store the certificate of each obligation that the scheduler certified
    /// by its own steps in `cache`, and the refusals of the certificates that
    /// did not enter it.
    ///
    /// # Specification
    /// - ensures: the cache holds the certificate of each obligation that a run
    ///   certified, up to its bound. An obligation that a consultation settled
    ///   spent no step, and the cache holds its certificate already, so it adds
    ///   nothing. A suspended, pending, exhausted or cancelled obligation adds
    ///   nothing.
    /// - panics: none.
    /// - executable: none — the clause speaks of the cache's entries.
    /// - intension: one store, and so one replay, for each obligation that a
    ///   run certified.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the machine's test corpus run with a cache adds an
    ///   entry for each certificate alone, and a run that the cache settles
    ///   records with no refusal.
    /// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
    /// - witness: `tests::cache::the_square_root_of_two_refines_alike_from_the_cache`
    #[inline]
    pub fn record(
        &self,
        cache: &mut Cache,
    ) -> Vec<(Position, CacheRefusal)>
    {
        let mut refusals = Vec::new();
        for (index, entry) in self.entries.iter().enumerate() {
            if entry.spent == 0 {
                continue;
            }
            if let Some(Outcome::Certified(certificate)) = entry.progress.settled()
                && let Err(refusal) = cache.store(
                    &self.plan,
                    entry.progress.obligation(),
                    certificate,
                    &self.quotas,
                )
            {
                refusals.push((Position(index), refusal));
            }
        }
        return refusals;
    }

    /// The checkpoint of the scheduler: its live obligations and the place of
    /// the next turn, as canonical bytes.
    ///
    /// # Specification
    /// - ensures: the bytes hold the quantum, the quotas, each live obligation
    ///   in the order of its turns with the steps spent on it and the steps of
    ///   its certificate so far, and the position among them of the live
    ///   obligation of the next turn. A settled obligation is not in the bytes.
    ///   [`Self::resume`] reads the bytes back to a scheduler that goes on as
    ///   this one goes on.
    /// - panics: none.
    /// - executable: none — the clause speaks of the scheduler that the bytes
    ///   resume to.
    /// - intension: one write of the live obligations' steps, in one
    ///   allocation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a checkpoint at every turn of generated runs resumes
    ///   to the certificates of the run that never stops. L3 — a checkpoint
    ///   after one quantum of the refinement of the square root of two.
    /// - witness: `tests::checkpoint::a_resumed_run_certifies_as_an_unbroken_one`
    /// - witness: `tests::checkpoint::every_checkpoint_resumes_to_the_unbroken_run`
    #[inline]
    #[must_use]
    pub fn checkpoint(&self) -> CheckpointBytes
    {
        let live = self
            .entries
            .iter()
            .filter(|entry| entry.progress.settled().is_none());
        // The next turn goes to the first live obligation at or after the
        // cursor, and after the last one to the first.
        let before = self.entries.get(.. self.cursor).map_or(0, |entries| {
            entries
                .iter()
                .filter(|entry| entry.progress.settled().is_none())
                .count()
        });
        let cursor = Position(if before >= self.live { 0 } else { before });
        let held = live.map(|entry| {
            let obligation = entry.progress.obligation();
            (
                obligation.node(),
                obligation.demand(),
                Steps(entry.spent),
                entry.progress.steps(),
            )
        });
        return write_checkpoint((self.quantum, &self.quotas, cursor), held);
    }

    /// The scheduler that the checkpoint `bytes` holds, over `plan`.
    ///
    /// # Specification
    /// - ensures: each live obligation of the checkpoint names a node of `plan`
    ///   of the sort that its demand takes, and the steps of its certificate
    ///   replay in [`crate::certificate::check`]. The scheduler goes on as the
    ///   scheduler that wrote the checkpoint goes on: a run gives the same
    ///   certificates and the same reasons.
    /// - fails: refuses each corruption by name: a malformed layout
    ///   ([`ResumeError::Decode`]), a quantum of no steps
    ///   ([`ResumeError::Quantum`]), a cursor past the obligations
    ///   ([`ResumeError::Cursor`]), an obligation that names no node of `plan`
    ///   or a node of another sort ([`ResumeError::Obligation`]), steps that do
    ///   not replay ([`ResumeError::Replay`]), steps that the machine does not
    ///   write for a live obligation ([`ResumeError::Steps`]), and bytes that
    ///   differ from the canonical bytes of what they hold
    ///   ([`ResumeError::Decode`] of [`DecodeError::NotCanonical`]).
    /// - panics: none.
    /// - executable: none — the clause speaks of the runs of the resumed
    ///   scheduler.
    /// - intension: one read and one replay of the steps, linear in the bytes.
    ///
    /// # Errors
    /// Each [`ResumeError`] above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every checkpoint of generated runs resumes to the
    ///   unbroken run. L3 — each refusal on its smallest corruption.
    /// - witness: `tests::checkpoint::a_resumed_run_certifies_as_an_unbroken_one`
    /// - witness: `tests::checkpoint::every_checkpoint_resumes_to_the_unbroken_run`
    /// - witness: `tests::checkpoint::a_corrupt_checkpoint_is_refused_by_name`
    #[inline]
    pub fn resume(
        plan: Plan,
        bytes: EncodedCheckpoint<'_>,
    ) -> Result<Self, ResumeError>
    {
        let (quantum, quotas, cursor, held) = read_checkpoint(bytes)
            .map_err(ResumeError::Decode)?
            .into_parts();
        let quantum = quantum.ok_or(ResumeError::Quantum)?;
        if cursor.0 >= held.len().max(1) {
            return Err(ResumeError::Cursor);
        }
        let entries = held
            .into_iter()
            .map(|held| {
                let (node, demand, spent, steps) = held.into_parts();
                let obligation =
                    Obligation::new(&plan, node, demand).map_err(ResumeError::Obligation)?;
                let progress = Progress::resume(&plan, obligation, steps, &quotas)?;
                return Ok(Entry {
                    progress,
                    spent: spent.0,
                });
            })
            .collect::<Result<Vec<Entry>, ResumeError>>()?;
        let resumed = Self {
            plan,
            quantum,
            quotas,
            live: entries.len(),
            entries,
            cursor: cursor.0,
        };
        if resumed.checkpoint().as_ref() != bytes.as_ref() {
            return Err(ResumeError::Decode(DecodeError::NotCanonical));
        }
        return Ok(resumed);
    }
}

/// What a run did, and the outcome of each obligation when it stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Report<'run, Plan>
{
    /// The scheduler after the run.
    dovetail: &'run Dovetail<Plan>,
    /// Why the run stopped.
    stop: Stop,
    /// The work of the run.
    work: Work,
}

impl<'run, Plan> Report<'run, Plan>
where
    Plan: Deref<Target = ValidatedPlan>,
{
    /// Why the run stopped.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stop(&self) -> Stop
    {
        return self.stop;
    }

    /// The work of the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn work(&self) -> Work
    {
        return self.work;
    }

    /// The checkpoint of the scheduler after the run, as
    /// [`Dovetail::checkpoint`] writes it. A cancelled run hands it to its
    /// caller here.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn checkpoint(&self) -> CheckpointBytes
    {
        return self.dovetail.checkpoint();
    }

    /// The outcome of the obligation at `position`, or `None` past the
    /// obligations.
    ///
    /// # Specification
    /// - ensures: a settled obligation's certificate or reason. A live
    ///   obligation is [`Outcome::Pending`] after a run that completed its
    ///   rounds, [`Outcome::Exhausted`] after a run that spent its budget, and
    ///   [`Outcome::Cancelled`] after a cancelled run. No outcome of a live
    ///   obligation carries evidence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Dovetail::run`].
    /// - witness: `tests::dovetail::two_obligations_run_round_by_round`
    /// - witness: `tests::dovetail::a_run_past_its_budget_is_exhausted_and_resumes`
    /// - witness: `tests::dovetail::a_cancelled_run_resumes_at_the_next_turn`
    #[spec(ensures: |ref output| output.is_some() == (position.0 < self.dovetail.entries.len()))]
    #[inline]
    #[must_use]
    pub fn outcome(
        &self,
        position: Position,
    ) -> Option<Outcome<'run>>
    {
        let entry = self.dovetail.entries.get(position.0)?;
        return Some(entry.progress.settled().unwrap_or(match self.stop {
            Stop::Settled | Stop::Rounds => Outcome::Pending,
            Stop::Budget => Outcome::Exhausted,
            Stop::Cancelled => Outcome::Cancelled,
        }));
    }
}
