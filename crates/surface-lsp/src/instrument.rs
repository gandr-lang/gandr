//! The sink each recheck runs at: the hub's one choice of the instrument's
//! layer for each job of a recheck.
//!
//! # A client's subscription chooses the sink of each job
//!
//! **Choice.** A connection holds its client's [`Subscription`], and each job
//! of a recheck, the judgement and the admission, carries a copy of it. The
//! job runs through [`Subscription::run`], which chooses the sink once, before
//! the job starts, and runs the job generic over that sink. So the choice is
//! one branch for each job, never one for each event. Without the
//! `instrument` feature the subscription holds nothing, and each job runs at
//! [`Silent`] with no branch at all.
//!
//! **Alternatives.** A sink chosen at each event costs one branch for each
//! event. A sink behind a trait object costs one indirect call for each event,
//! and the compiler cannot remove a call on the silent sink.
//!
//! # What it does not cover
//!
//! A client cannot subscribe to a layer yet, because the subscription on the
//! render bus is a later unit. Until then, each subscription holds the silent
//! layer, and the layer units add their layers beside it.

use gandr_surface_session::Instrument;
use gandr_surface_session::Silent;

/// The instrument layer a client subscribed to.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Layer
{
    /// No layer: each job runs at [`Silent`].
    Silent,
}

/// What a client subscribed to, read once by each job of a recheck.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Subscription
{
    /// The layer the client subscribed to.
    #[cfg(feature = "instrument")]
    layer: Layer,
}

impl Subscription
{
    /// The subscription of a client that subscribed to no layer.
    pub const SILENT: Self = Self {
        #[cfg(feature = "instrument")]
        layer: Layer::Silent,
    };
}

/// A job of a recheck, run generic over the sink its subscription chose.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the job's answer does not depend on the sink it runs at.
/// - provides: the one shape the hub's choice of sink runs a job in.
/// - panics: none.
/// - executable: none — the law relates two runs at two sinks, and only one
///   sink is in this unit.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Subscription::run`].
/// - witness: `server::tests::a_change_during_a_judgement_retires_it_1547`
pub trait Job
{
    /// What the job answers.
    type Out;

    /// Run the job, telling `sink` what it does.
    ///
    /// # Specification
    /// trivial.
    fn run<Sink>(
        self,
        sink: &mut Sink,
    ) -> Self::Out
    where
        Sink: Instrument;
}

#[cfg(feature = "instrument")]
impl Subscription
{
    /// Run `job` at the sink of the subscribed layer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer of `job` run at the sink of the layer, [`Silent`]
    ///   for [`Layer::Silent`].
    /// - provides: the one branch of a job on its layer.
    /// - fails: never.
    /// - panics: only by propagating a panic of `job`.
    /// - executable: none — the sink is a type, and only `job` observes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each judgement and admission of the hub's suites runs
    ///   through it, and their diagnostics and timing lines are those of a hub
    ///   built without the feature.
    /// - witness: `server::tests::a_change_during_a_judgement_retires_it_1547`
    /// - witness: `server::tests::a_change_during_an_admission_retires_it_1547`
    #[inline]
    pub fn run<Run>(
        self,
        job: Run,
    ) -> Run::Out
    where
        Run: Job,
    {
        match self.layer {
            Layer::Silent => job.run(&mut Silent),
        }
    }
}

#[cfg(not(feature = "instrument"))]
impl Subscription
{
    /// Run `job` at [`Silent`]: without the `instrument` feature no other
    /// sink is compiled, so there is nothing to choose.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer of `job` run at [`Silent`].
    /// - provides: the job's run with no branch on a layer.
    /// - fails: never.
    /// - panics: only by propagating a panic of `job`.
    /// - executable: none — the sink is a type, and only `job` observes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each judgement and admission of the hub's suites runs
    ///   through it.
    /// - witness: `server::tests::a_change_during_a_judgement_retires_it_1547`
    /// - witness: `server::tests::a_change_during_an_admission_retires_it_1547`
    #[inline]
    #[expect(
        clippy::unused_self,
        reason = "the subscription holds nothing without the feature, and its run keeps one signature in both builds"
    )]
    pub fn run<Run>(
        self,
        job: Run,
    ) -> Run::Out
    where
        Run: Job,
    {
        job.run(&mut Silent)
    }
}
