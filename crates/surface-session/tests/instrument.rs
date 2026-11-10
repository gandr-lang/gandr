//! The instrument: a recording sink is told what a judgement and an admission
//! do, in order, with the counts the session reports.

use gandr_core_checker::Polled;
use gandr_core_checker::Unretired;
use gandr_core_incremental::ItemCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_lowering::DeclarationCount;
use gandr_surface_session::FormCount;
use gandr_surface_session::Instrument;
use gandr_surface_session::Phase;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::session;
use crate::common::submit;

/// One event a sink was told.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Event
{
    /// A phase started.
    Entered(Phase),
    /// A phase ended.
    Left(Phase),
    /// A parse molded this many forms.
    Molded(FormCount),
    /// An incremental pass judged this many items.
    Judged(ItemCount),
    /// An admission offered the kernel this many declarations again.
    Crossed(DeclarationCount),
}

/// A sink that keeps each event it is told, in order.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Recorded(Vec<Event>);

impl Instrument for Recorded
{
    /// Keep the start of `phase`.
    ///
    /// # Specification
    /// trivial.
    fn entered(
        &mut self,
        phase: Phase,
    )
    {
        self.0.push(Event::Entered(phase));
    }

    /// Keep the end of `phase`.
    ///
    /// # Specification
    /// trivial.
    fn left(
        &mut self,
        phase: Phase,
    )
    {
        self.0.push(Event::Left(phase));
    }

    /// Keep the forms a parse molded.
    ///
    /// # Specification
    /// trivial.
    fn molded(
        &mut self,
        forms: FormCount,
    )
    {
        self.0.push(Event::Molded(forms));
    }

    /// Keep the items an incremental pass judged.
    ///
    /// # Specification
    /// trivial.
    fn judged(
        &mut self,
        items: ItemCount,
    )
    {
        self.0.push(Event::Judged(items));
    }

    /// Keep the declarations an admission offered the kernel again.
    ///
    /// # Specification
    /// trivial.
    fn crossed(
        &mut self,
        declarations: DeclarationCount,
    )
    {
        self.0.push(Event::Crossed(declarations));
    }
}

/// A judgement tells its sink the parse, the lowering and the judgement, each
/// entered then left, in that order. After the parse it tells the forms the
/// parse molded, and after the judgement the items the incremental pass
/// judged: the counts its submission reports. The revision edits one form of
/// the one before it, so it molds and judges fewer than all, and a count of
/// the whole revision changes the events.
#[test]
fn a_judgement_tells_its_sink_each_phase_and_count()
{
    let mut session = session(SourceRoot::Strict);
    let _first = submit(&mut session, "def a : Integer ; def a = 1 ; def b = a ;");
    let mut recorded = Recorded::default();
    let Ok(Polled::Whole(judged)) = session.judge_reading_retiring(
        SourceText::from("def a : Integer ; def a = 2 ; def b = a ;"),
        |_| (),
        (&Unretired, &mut recorded),
    )
    else {
        panic!("the revision is judged whole");
    };
    let Maybe::Present(resumed) = judged.resumed()
    else {
        panic!("the judgement ran its incremental pass");
    };
    let (molded, items) = (judged.forms().molded(), resumed.census().judged);
    assert!(
        usize::from(molded) < usize::from(judged.forms().forms())
            && usize::from(items) < usize::from(resumed.census().items),
        "the edit molds and judges fewer than all: {molded:?} forms and {items:?} items"
    );
    assert_eq!(
        recorded.0,
        [
            Event::Entered(Phase::Parse),
            Event::Left(Phase::Parse),
            Event::Molded(molded),
            Event::Entered(Phase::Lower),
            Event::Left(Phase::Lower),
            Event::Entered(Phase::Judge),
            Event::Left(Phase::Judge),
            Event::Judged(items),
        ],
        "each phase entered then left, in order, each count after its phase"
    );
}

/// An admission tells its sink the admission entered then left, then the
/// declarations it offered the kernel again: the count its settle reports.
#[test]
fn an_admission_tells_its_sink_what_it_crossed()
{
    let mut session = session(SourceRoot::Strict);
    let _judged = session
        .judge_reading(
            SourceText::from("def a : Integer ; def a = 1 ; def b = a ;"),
            |_| (),
        )
        .expect("the revision is judged");
    let Maybe::Present(detached) = session.admission()
    else {
        panic!("the judgement left its admission");
    };
    let mut recorded = Recorded::default();
    let ran = detached.run(&Unretired, &mut recorded).whole();
    let Ok(Maybe::Present(admitted)) = session.settle(ran)
    else {
        panic!("the admission settles");
    };
    assert!(
        usize::from(admitted.crossed()) > 0_usize,
        "a first admission offers the kernel each declaration it judged"
    );
    assert_eq!(
        recorded.0,
        [
            Event::Entered(Phase::Admit),
            Event::Left(Phase::Admit),
            Event::Crossed(admitted.crossed()),
        ],
        "the admission entered then left, then its crossed declarations"
    );
}
