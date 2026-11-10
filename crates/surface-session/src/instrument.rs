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
//! The memo's hits and misses, the nodes named, each judgement step, each
//! replay step and each schedule event have their sites inside the checker,
//! the kernel and the pool, so no method here names them yet. The hub does
//! not compile a declaration, so no phase names a compile step yet.

use gandr_core_incremental::ItemCount;
use gandr_surface_lowering::DeclarationCount;

use crate::forms::FormCount;

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

/// `work`, run inside `phase`: `sink` is told the phase starts before it and
/// ends after it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `sink` is told [`Instrument::entered`] of `phase`, then `work`
///   runs once, then `sink` is told [`Instrument::left`] of `phase`. The answer
///   is the answer of `work`.
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
pub fn within<Sink, Out>(
    sink: &mut Sink,
    phase: Phase,
    work: impl FnOnce() -> Out,
) -> Out
where
    Sink: Instrument,
{
    sink.entered(phase);
    let out = work();
    sink.left(phase);
    out
}
