//! The fork of one declaration's check: the seam where the independent
//! obligations of a declaration run apart.
//!
//! A check owes code obligations while it runs, and its last drain discharges
//! them. The obligations that the drain holds at its start do not read each
//! other's answers: each check reads the arena and the session as they stand.
//! An [`ObligationFork`] runs each of them as a [`Job`] on a worker that the
//! driver provides. The kernel folds the jobs in the serial order. A job that
//! refuses, or that the fork does not run, sends the kernel back to its serial
//! drain. So the seam adds no trust, and a forked check gives the verdict of
//! the serial check.
//!
//! A job costs more to fork and to join than a few obligations cost to check.
//! So only a drain of many obligations forks, and each job checks a run of
//! them. The runs read the size of the drain and the [`ForkWidth`] alone, so
//! a check at one width forks the same jobs each time.
//!
//! The seam is object-safe, so a [`Judgement`](crate::Judgement) carries it
//! without a type parameter. The kernel sits below the core crates, so it
//! states the seam itself. The driver's pool implements it.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — newest: §
//!   kernel-reassessment-design item 11 — the independent obligations of one
//!   check fork under one seam, and the serial check is the reference.

use alloc::sync::Arc;
use core::fmt;
use core::num::NonZeroUsize;

/// One part of a declaration's check that a fork runs apart.
///
/// # Specification
/// - provides: a computation that keeps its answer in itself, so the kernel
///   reads it after the fork returns.
/// - panics: none of its own; a check's panic is its own.
/// - executable: none — the trait states the shape the kernel's parts take.
pub trait Job: Send
{
    /// Run this part to its end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the part holds its answer. A part that runs again keeps its
    ///   first answer.
    /// - panics: none of its own.
    /// - executable: none — the answer is the part's own state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the forked drain's witnesses compare each verdict
    ///   with the serial check's.
    /// - declaration-only: the obligation is each implementation's.
    fn run(&mut self);
}

/// Runs the parts of one declaration's check on the workers that the driver
/// provides.
///
/// # Specification
/// - provides: each job run one time, on any worker, in any order, possibly at
///   once.
/// - panics: a panic of a job, wherever it ran.
/// - executable: none — the schedule is the implementation's.
pub trait ObligationFork: Sync
{
    /// Run each of `jobs` one time.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on return, each job has run one time. A job that did not run
    ///   holds no answer, and the kernel then checks serially.
    /// - panics: a panic of a job.
    /// - executable: none — "one time" is a property of the schedule, which a
    ///   postcondition over the jobs cannot observe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the forked drain's witnesses run the jobs in the
    ///   serial order, in the reverse order and on threads of their own.
    /// - declaration-only: the obligation is each implementation's schedule.
    fn run_jobs(
        &self,
        jobs: &mut [&mut dyn Job],
    );

    /// How many jobs this fork runs at once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same width on each call.
    /// - panics: none.
    /// - executable: none — the width is the implementation's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the forked drain's witnesses split a drain at the
    ///   width of their fork, and count the jobs.
    /// - declaration-only: the obligation is each implementation's.
    fn workers(&self) -> ForkWidth;
}

/// How many jobs a fork runs at once: the workers it has, the calling thread
/// among them.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct ForkWidth(NonZeroUsize);

impl From<NonZeroUsize> for ForkWidth
{
    /// A fork of `workers` workers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(workers: NonZeroUsize) -> Self
    {
        Self(workers)
    }
}

impl From<ForkWidth> for NonZeroUsize
{
    /// The workers of `width`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(width: ForkWidth) -> Self
    {
        width.0
    }
}

/// Whether one check forks its independent obligations, and through which
/// fork.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Default)]
#[repr(transparent)]
pub struct Forking<'session>(Option<&'session dyn ObligationFork>);

impl<'session> Forking<'session>
{
    /// A check that forks through `fork`, or that runs each obligation on the
    /// calling thread, in order, when `fork` is none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn new(fork: Option<&'session dyn ObligationFork>) -> Self
    {
        Self(fork)
    }

    /// The fork, if the check forks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn fork(self) -> Option<&'session dyn ObligationFork>
    {
        self.0
    }
}

impl fmt::Debug for Forking<'_>
{
    /// `forked` or `serial`: the fork itself is the driver's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(if self.0.is_some() { "forked" } else { "serial" })
    }
}

/// The fork that an environment's checks run their obligations through,
/// shared with each copy of the environment: none by default, so each check
/// runs its obligations on the calling thread.
///
/// # Specification
/// trivial.
#[derive(Clone, Default)]
#[repr(transparent)]
pub struct SharedFork(Option<Arc<dyn ObligationFork + Send>>);

impl SharedFork
{
    /// Each check running its obligations on the calling thread, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn serial() -> Self
    {
        Self(None)
    }

    /// Each check running the obligations of its last drain apart through
    /// `fork`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn through(fork: Arc<dyn ObligationFork + Send>) -> Self
    {
        Self(Some(fork))
    }

    /// The fork of one check, if the checks fork.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn forking(&self) -> Option<&dyn ObligationFork>
    {
        self.0
            .as_deref()
            .map(|fork| -> &dyn ObligationFork { fork })
    }
}

impl fmt::Debug for SharedFork
{
    /// `forked` or `serial`: the fork itself is the driver's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(if self.0.is_some() { "forked" } else { "serial" })
    }
}
