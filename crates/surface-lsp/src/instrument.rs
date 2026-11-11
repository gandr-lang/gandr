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
//! # The activity follows the hub, not the client
//!
//! While the hub has a watcher of the activity, each job takes the activity
//! layer in place of its client's (`Subscription::recording`, with the
//! `instrument` feature). The job then runs as one task between two marks on
//! the ring of its thread, at a sink that answers the rings, so the fork sites
//! inside it mark their own jobs. The rings follow the pool, which every
//! connection shares, so one watcher makes every connection's jobs mark them.
//!
//! # What it does not cover
//!
//! A client cannot subscribe to a layer yet, because the subscription on the
//! render bus is a later unit. Until then, each connection holds the silent
//! layer, and a test selects another layer through its constant, such as
//! `Subscription::COUNTS`, `Subscription::TIMINGS` or `Subscription::TRACE`,
//! with the `instrument` feature.

#[cfg(feature = "instrument")]
use alloc::sync::Arc;

#[cfg(feature = "instrument")]
use gandr_core_fork::activity::Activity;
#[cfg(feature = "instrument")]
use gandr_core_fork::activity::Declared;
#[cfg(feature = "instrument")]
use gandr_core_fork::activity::Task;
#[cfg(feature = "instrument")]
use gandr_core_fork::activity::World;
#[cfg(feature = "instrument")]
use gandr_surface_dispatcher::marked;
#[cfg(feature = "instrument")]
use gandr_surface_session::Counts;
use gandr_surface_session::Instrument;
use gandr_surface_session::Silent;
#[cfg(feature = "instrument")]
use gandr_surface_session::Timings;
#[cfg(feature = "instrument")]
use gandr_surface_session::Trace;
#[cfg(feature = "instrument")]
use gandr_surface_session::unrecorded;
#[cfg(feature = "instrument")]
use quenchant_shape::shape::Maybe;

/// The instrument layer a job runs at.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
#[derive(Clone, Debug)]
pub enum Layer
{
    /// No layer: each job runs at [`Silent`].
    Silent,
    /// The activity: each job runs as one task on the rings, and its fork
    /// sites mark their jobs.
    Activity(Arc<Activity>),
    /// The counts layer: each job runs at a fresh [`Counts`], so each recheck
    /// counts into its own column.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "a client subscribes through the render bus, a later unit; until then a test selects the layer"
        )
    )]
    Counts,
    /// The timings layer: each job runs at a fresh [`Timings`], so each
    /// recheck samples into its own column.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "a client subscribes through the render bus, a later unit; until then a test selects the layer"
        )
    )]
    Timings,
    /// The trace layer: each job runs at a fresh [`Trace`], so each recheck
    /// folds the steps of each item it judges into the item's tree.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "a client subscribes through the render bus, a later unit; until then a test selects the layer"
        )
    )]
    Trace,
}

/// What a client subscribed to, read once by each job of a recheck.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug)]
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

    /// The subscription of a client that subscribed to the counts layer.
    #[cfg(feature = "instrument")]
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "a client subscribes through the render bus, a later unit; until then a test selects the layer"
        )
    )]
    pub const COUNTS: Self = Self {
        layer: Layer::Counts,
    };

    /// The subscription of a client that subscribed to the timings layer.
    #[cfg(feature = "instrument")]
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "a client subscribes through the render bus, a later unit; until then a test selects the layer"
        )
    )]
    pub const TIMINGS: Self = Self {
        layer: Layer::Timings,
    };

    /// The subscription of a client that subscribed to the trace layer.
    #[cfg(feature = "instrument")]
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "a client subscribes through the render bus, a later unit; until then a test selects the layer"
        )
    )]
    pub const TRACE: Self = Self {
        layer: Layer::Trace,
    };

    /// The subscription of a job while the hub has a watcher of the activity:
    /// the job marks `rings`.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[must_use]
    pub(crate) const fn recording(rings: Arc<Activity>) -> Self
    {
        Self {
            layer: Layer::Activity(rings),
        }
    }
}

/// The sink of a job at the activity layer: it answers the rings, so each
/// fork site of the job marks its jobs, and it records nothing else.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
#[repr(transparent)]
struct Rings<'activity>(&'activity Activity);

#[cfg(feature = "instrument")]
impl Instrument for Rings<'_>
{
    /// The rings that the job's fork sites mark.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn activity(&self) -> Maybe<&Activity, unrecorded::Absent>
    {
        Maybe::Present(self.0)
    }
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

    /// The kind of task the job is on the activity ring.
    #[cfg(feature = "instrument")]
    const TASK: Task;

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
    ///   for [`Layer::Silent`], a fresh [`Counts`] for [`Layer::Counts`], a
    ///   fresh [`Timings`] for [`Layer::Timings`] and a fresh [`Trace`] for
    ///   [`Layer::Trace`]. At [`Layer::Activity`], `job` runs as one task of
    ///   its kind between two marks on the ring of its thread, at a sink that
    ///   answers the rings.
    /// - provides: the one branch of a job on its layer.
    /// - fails: never.
    /// - panics: only by propagating a panic of `job`.
    /// - executable: none — the sink is a type, and only `job` observes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each judgement and admission of the hub's suites runs
    ///   through it, and their diagnostics and timing lines are those of a hub
    ///   built without the feature. While a watcher follows the activity, an
    ///   edit's judgement and admission each reach the watcher as one task.
    /// - witness: `server::tests::a_change_during_a_judgement_retires_it_1547`
    /// - witness: `server::tests::a_change_during_an_admission_retires_it_1547`
    /// - witness: `server::tests::a_watched_edit_marks_its_judgement_and_its_admission`
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
            Layer::Counts => job.run(&mut Counts::default()),
            Layer::Timings => job.run(&mut Timings::default()),
            Layer::Trace => job.run(&mut Trace::default()),
            Layer::Activity(ref rings) => {
                marked(rings, (Run::TASK, World::from(0)), Declared::NONE, || {
                    job.run(&mut Rings(rings))
                })
            },
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
