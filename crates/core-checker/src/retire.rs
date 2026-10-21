//! Retirement: whether the work a run does is still wanted, polled where the
//! run stands between two of its steps.
//!
//! A run that judges a revision's items, or readmits a report's declarations,
//! may be overtaken by a newer revision that makes its answer stale. A
//! [`Retirement`] is what the run polls before each step: a read, never a
//! write, so one value serves every worker that reads it and nothing is shared
//! mutably. A run that reads [`Demand::Retired`] stops before its next step
//! and answers [`Polled::Retired`] with what it holds; a run that never does
//! answers [`Polled::Whole`], as it would with no poll at all.
//!
//! A poll is read only between steps: a judgement or a crossing in progress
//! finishes, so every verdict a run gives is the one a run nobody retired
//! gives. [`Unretired`] is the poll of work nobody retires; its retirement is
//! uninhabited, so a run under it answers [`Polled::whole`], its answer's type
//! unchanged.

use core::convert::Infallible;

/// The demand for a run's work: still wanted, or retired by something.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Demand<Retired>
{
    /// The work is wanted: the run takes its next step.
    Wanted,
    /// The work is retired: the run stops before its next step.
    Retired(Retired),
}

/// The poll a run reads before each of its steps.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Retirement::demand`] is a read.
/// - executable: none — a poll's answer is the retiring party's to give.
///
/// # Adequacy
/// - hypothesis: L3 — a run polled to retirement stops at the step it polled
///   before, and a run resumed from what it held answers as a whole run does.
/// - witness: `bridge::tests::a_retired_readmission_resumes_from_its_record_1547`
pub trait Retirement
{
    /// What retires the work: whatever the retiring party names it by, such
    /// as the generation that superseded it.
    type Retired;

    /// The demand for the work.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Demand::Wanted`] while the work is wanted.
    /// - panics: none.
    /// - executable: none — whether the work is wanted is the retiring party's
    ///   to say, and no predicate over the poll alone states it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run stops before the step whose poll answered
    ///   retired, and takes every step whose poll answered wanted.
    /// - witness: `bridge::tests::a_retired_readmission_resumes_from_its_record_1547`
    fn demand(&self) -> Demand<Self::Retired>;
}

/// The poll of work nobody retires.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Unretired;

impl Retirement for Unretired
{
    type Retired = Infallible;

    /// Always wanted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn demand(&self) -> Demand<Infallible>
    {
        Demand::Wanted
    }
}

/// What a run that polls retirement answers: its whole answer, or what retired
/// it beside what it held then.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Polled<Whole, Retired, Held>
{
    /// The run took every step.
    Whole(Whole),
    /// The run was retired before a step, holding this.
    Retired(Retired, Held),
}

impl<Whole, Held> Polled<Whole, Infallible, Held>
{
    /// The whole answer of a run nobody could retire.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn whole(self) -> Whole
    {
        match self {
            Self::Whole(whole) => whole,
            Self::Retired(never, _) => match never {},
        }
    }
}
