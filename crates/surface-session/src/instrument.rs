//! The instrument: the one seam through which the engine records its own
//! work.
//!
//! # The engine records its work through one sink
//!
//! **Choice.** [`Instrument`] has one method for each event kind that the
//! session observes. The session's judgement and its admission take the sink
//! as a type parameter, so each call to the sink is a static call. [`Silent`]
//! is a zero-sized sink, and each of its methods has an empty body. A
//! judgement made generic over [`Silent`] has no call left to make, so the
//! compiler removes each call, and a build that records nothing costs
//! nothing. A layer of the instrument is a sink. It implements the methods of
//! its layer and keeps the empty body of each other method.
//!
//! | Event | Method | Layer | Where the session tells the sink |
//! | --- | --- | --- | --- |
//! | a phase starts | [`Instrument::entered`] | timings | before the parse, the lowering, the judgement and the admission |
//! | a phase ends | [`Instrument::left`] | timings | after each of them, on each path out, a fault and a retirement included |
//! | forms molded | [`Instrument::molded`] | counts | once for each parse, with the forms it molded |
//! | items judged | [`Instrument::judged`] | counts | once for each incremental pass that ran whole, with the items it judged |
//! | declarations crossed | [`Instrument::crossed`] | counts | once for each admission that ran whole, with the declarations it offered the kernel again |
//! | a fork job starts or ends | `Instrument::activity` | activity | at each fork site of the judgement: with the rings it answers, the site forks through the pool's recording fork, whose jobs mark the rings |
//! | each declaration's work | `Instrument::counts` | counts | each item the incremental pass adopts or judges, and each declaration's molded forms and obligations after the lowering, into the column the sink answers |
//! | what an admission records | `Instrument::positioning` | counts | once for each admission, before it starts |
//!
//! `Instrument::activity` takes `&self` and answers a shared handle: the
//! rings are per thread and lock-free, and the pool's threads write them
//! while the session's thread holds the sink. `Instrument::counts` answers
//! the column of the counts layer, and the session counts into it directly,
//! so a sink that answers no column costs no attribution. These three methods
//! exist with the `instrument` feature alone.
//!
//! **Alternatives.** A trait object costs one indirect call for each event,
//! and the compiler cannot remove a call on the silent sink. A flag that each
//! site reads costs one branch for each event. A sink that the session holds
//! gives a document one sink for its whole life, but a client chooses its
//! layer for each recheck.
//!
//! **Reversal.** A layer whose events come from inside the checker, the kernel
//! or the pool, such as a memo hit or a schedule event, needs its site to take
//! the sink too. The unit of that layer adds its method here and makes its
//! site generic over the sink, with [`Silent`] as the sink of every caller
//! that records nothing.
//!
//! # What it does not cover
//!
//! Each judgement step and each replay step has its site inside the checker
//! and the kernel, so no method here names it yet. A fork job deeper than the
//! session's fork sites, such as a kernel replay inside a judgement, is marked
//! with the kind of its site. The hub does not compile a declaration, so no
//! phase names a compile step yet.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-layers decides the one sink, the silent sink, the
//!   `instrument` feature and the choice of sink for each recheck.

#[cfg(feature = "instrument")]
use gandr_core_fork::activity::Activity;
use gandr_core_incremental::ItemCount;
#[cfg(feature = "instrument")]
use gandr_surface_dispatcher::Positioning;
use gandr_surface_lowering::DeclarationCount;
#[cfg(feature = "instrument")]
use quenchant_shape::shape::Maybe;

#[cfg(feature = "instrument")]
use crate::counts::CountColumn;
#[cfg(feature = "instrument")]
use crate::counts::uncounted;
use crate::forms::FormCount;

#[cfg(feature = "instrument")]
quenchant_shape::reason_enum! {
    /// Why a sink answers no rings.
    pub mod unrecorded {
        /// The reason a sink answers no rings.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The sink's layer is not the activity.
            Unselected,
        }
    }
}

/// A phase of a judgement or an admission, as the timings layer reads its
/// boundaries.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Phase
{
    /// The parse of the revision through the form store.
    Parse,
    /// The lowering of the parsed revision.
    Lower,
    /// The judgement of the lowered revision and its incremental pass.
    Judge,
    /// The kernel's readmission of the judged revision.
    Admit,
}

/// A sink for the events of the engine's own work.
///
/// Each method has an empty body, so a sink implements the methods of its
/// layer and no others.
///
/// # Specification
/// - requires: a sink observes. It never changes a verdict, a report or the
///   session's state.
/// - ensures: the session tells the sink each event of a judgement and an
///   admission in the order the event occurs, each phase entered before it is
///   left.
/// - provides: the one seam each instrument layer records through.
/// - panics: none.
/// - executable: none — the trait states the events, and the order of the calls
///   is an effect that only a sink observes.
///
/// # Adequacy
/// - hypothesis: L3 — a recording sink is told each phase of a judgement and of
///   an admission, entered then left, in order, and the counts the submission
///   and the admission report. A judgement that skipped a boundary or told a
///   count twice changes the recorded events.
/// - witness: `tests::instrument::a_judgement_tells_its_sink_each_phase_and_count`
/// - witness: `tests::instrument::an_admission_tells_its_sink_what_it_crossed`
pub trait Instrument
{
    /// `phase` starts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entered(
        &mut self,
        _phase: Phase,
    )
    {
    }

    /// `phase` ends.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn left(
        &mut self,
        _phase: Phase,
    )
    {
    }

    /// A parse molded `forms` of its revision's forms, and took up the others
    /// from the form store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn molded(
        &mut self,
        _forms: FormCount,
    )
    {
    }

    /// An incremental pass judged `items` of its revision's items, and adopted
    /// the others.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn judged(
        &mut self,
        _items: ItemCount,
    )
    {
    }

    /// An admission offered the kernel `declarations` again, and resumed the
    /// others from a readmission it held.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn crossed(
        &mut self,
        _declarations: DeclarationCount,
    )
    {
    }

    /// The rings that the fork jobs of the judgement write, when this sink
    /// records the activity.
    ///
    /// # Specification
    /// - ensures: the default answers [`unrecorded::Absent::Unselected`], so a
    ///   fork site forks through the pool as it stands and writes no mark.
    /// - panics: none.
    /// - executable: none — a handle the sink holds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sink that answers rings sees a mark for each fork
    ///   job of a parse, and a silent sink sees none.
    /// - witness: `tests::instrument::a_sink_with_rings_sees_each_fork_job_of_its_parse`
    #[cfg(feature = "instrument")]
    #[inline]
    fn activity(&self) -> Maybe<&Activity, unrecorded::Absent>
    {
        Maybe::Absent(unrecorded::Absent::Unselected)
    }

    /// The column that this sink counts each declaration's work into, when it
    /// records the counts.
    ///
    /// # Specification
    /// - ensures: the default answers [`uncounted::Absent::Unselected`], so the
    ///   session attributes no form and counts nothing.
    /// - panics: none.
    /// - executable: none — a handle the sink holds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sink that answers a column reads each declaration's
    ///   counts in the account, and a silent sink reads none.
    /// - witness: `tests::counts::a_second_recheck_counts_no_judged_item`
    #[cfg(feature = "instrument")]
    #[inline]
    fn counts(&mut self) -> Maybe<&mut CountColumn, uncounted::Absent>
    {
        Maybe::Absent(uncounted::Absent::Unselected)
    }

    /// What an admission at this sink records of each declaration it crosses.
    ///
    /// # Specification
    /// - ensures: the default answers [`Positioning::Unpositioned`], so an
    ///   admission records nothing and reads no clock.
    /// - panics: none.
    /// - executable: none — a constant of the sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Instrument::counts`].
    /// - witness: `tests::counts::a_second_recheck_counts_no_judged_item`
    #[cfg(feature = "instrument")]
    #[inline]
    fn positioning(&self) -> Positioning
    {
        Positioning::Unpositioned
    }
}

/// The sink that records nothing.
///
/// Zero-sized, and each method keeps its empty body, so a judgement generic
/// over it has no recording state and no call to make.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Silent;

impl Instrument for Silent
{
}

/// `work`, run inside `phase` with `sink`: `sink` is told the phase starts
/// before it and ends after it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `sink` is told [`Instrument::entered`] of `phase`, then `work`
///   runs once with `sink`, then `sink` is told [`Instrument::left`] of
///   `phase`. The answer is the answer of `work`.
/// - provides: both boundaries of a phase on each path out of it, a fault and a
///   retirement included, since `work` answers each of them.
/// - fails: never; a fault of `work` is in its answer.
/// - panics: only by propagating a panic of `work`.
/// - executable: none — the two calls are effects that only the sink observes.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Instrument`].
/// - witness: `tests::instrument::a_judgement_tells_its_sink_each_phase_and_count`
#[inline]
pub fn within<Sink, Work, Out>(
    sink: &mut Sink,
    phase: Phase,
    work: Work,
) -> Out
where
    Sink: Instrument,
    Work: FnOnce(&mut Sink) -> Out,
{
    sink.entered(phase);
    let out = work(sink);
    sink.left(phase);
    out
}
