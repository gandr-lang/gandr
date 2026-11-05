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
use core::num::NonZeroU32;

use anodized::spec;

use crate::certificate::CheckerQuotas;
use crate::semidecision::Obligation;
use crate::semidecision::Outcome;
use crate::semidecision::Progress;
use crate::validate::ValidatedPlan;

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
/// # Specification
/// - invariant: `cursor` is below the number of obligations, or zero when there
///   is none, and `live` counts the obligations that are live.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Dovetail<'plan>
{
    /// The plan that the obligations name.
    plan: &'plan ValidatedPlan,
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

impl<'plan> Dovetail<'plan>
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
        plan: &'plan ValidatedPlan,
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
    ) -> Report<'_, 'plan>
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
            let plan = self.plan;
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
}

/// What a run did, and the outcome of each obligation when it stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Report<'run, 'plan>
{
    /// The scheduler after the run.
    dovetail: &'run Dovetail<'plan>,
    /// Why the run stopped.
    stop: Stop,
    /// The work of the run.
    work: Work,
}

impl<'run> Report<'run, '_>
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
