use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use quenchant_shape::shape::Maybe;

use super::BranchStatus;
use super::Liveness;
use super::MatchOrigin;
use super::SynthesisEvent;
use super::SynthesisStream;
use crate::boundary::MatchOrdinal;
use crate::boundary::SourceItemOrdinal;
use crate::boundary::SubmissionOrdinal;
use crate::checkpoint::Resume;
use crate::checkpoint::check_program;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;

/// A coordinate of a fixture origin.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Coordinate(usize);

/// A two-item resume of trivially typed items, so the events under test
/// are the ones this module builds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two unsigned integer items with repeated keys are judged in a
///   fresh program, producing aligned checkpoint, handle and adoption vectors
///   and synthesised typings.
/// - panics: if the fixed ascending program or its order cannot be built.
///
/// # Adequacy
/// - hypothesis: L3 — the ordered and replacement liveness scenarios use this
///   two-item resume and observe its item prefix before liveness events. This
///   fixture does not cover refused items or resumed adoption.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
#[spec(ensures: |ret| ret.checkpoints().items().len() == 2
        && ret.handles().len() == 2 && ret.adoptions().len() == 2
        && ret.checkpoints().items().iter().all(|checkpoint| matches!(*checkpoint.typing(), crate::typing::Typing::Synthesised { .. })))]
fn two_item_resume() -> Resume
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::zero(),
    )));
    let items = (0_usize .. 2_usize)
        .map(|position| {
            Item::new(
                ItemKey::from("item"),
                Declaration::new(
                    ConstantIndex::from(position),
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(zero),
                    OriginToken::from(position),
                ),
            )
        })
        .collect();
    let mut program = Program::new(arena, items).expect("ascending");
    check_program(&mut program, CheckBudget::DEFAULT).expect("the order builds")
}

/// One origin, in fixture coordinates.
///
/// # Specification
/// trivial.
fn origin(
    submission: Coordinate,
    source_item: Coordinate,
    match_index: Coordinate,
) -> MatchOrigin
{
    MatchOrigin {
        submission: SubmissionOrdinal::from(submission.0),
        source_item: SourceItemOrdinal::from(source_item.0),
        match_index: MatchOrdinal::from(match_index.0),
    }
}

/// The origins of the stream's match events, in order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exactly the match-event origins are returned in their input
///   order; framing, item and missing-source events contribute nothing.
///
/// # Adequacy
/// - hypothesis: L3 — ordered streams with multiple origins, replacement and a
///   missing-source marker distinguish filtering from source-item indexing. The
///   witnessed inputs are constructed streams, not arbitrary permutations.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
/// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
#[spec(ensures: |ret| ret.iter().copied().eq(events.iter().filter_map(|event| match *event {
        SynthesisEvent::Match { origin, .. } => Some(origin),
        SynthesisEvent::Started { .. } | SynthesisEvent::Item { .. } | SynthesisEvent::SourceNotRetained { .. } | SynthesisEvent::Completed => None,
    })))]
fn match_origins(events: &[SynthesisEvent]) -> Vec<MatchOrigin>
{
    events
        .iter()
        .filter_map(|event| match *event {
            SynthesisEvent::Match { origin, .. } => Some(origin),
            SynthesisEvent::Started { .. }
            | SynthesisEvent::Item { .. }
            | SynthesisEvent::SourceNotRetained { .. }
            | SynthesisEvent::Completed => None,
        })
        .collect()
}

#[test]
fn liveness_follows_the_items_in_origin_order()
{
    let mut liveness = Liveness::new();
    let _displaced = liveness.insert(origin(Coordinate(0), Coordinate(1), Coordinate(0)), vec![
        BranchStatus::Refuted,
        BranchStatus::Possibly,
    ]);
    let _displaced = liveness.insert(origin(Coordinate(0), Coordinate(0), Coordinate(1)), vec![
        BranchStatus::Satisfied,
    ]);
    let events: Vec<SynthesisEvent> =
        SynthesisStream::from_resume_with_liveness(&two_item_resume(), &liveness).collect();
    assert_eq!(
        match_origins(&events),
        [
            origin(Coordinate(0), Coordinate(0), Coordinate(1)),
            origin(Coordinate(0), Coordinate(1), Coordinate(0)),
        ],
        "ascending by origin, whatever order the producer recorded them in"
    );
    let first_match = events
        .iter()
        .position(|event| matches!(*event, SynthesisEvent::Match { .. }))
        .expect("the liveness is on the stream");
    assert_eq!(
        events
            .iter()
            .take(first_match)
            .filter(|event| matches!(**event, SynthesisEvent::Item { .. }))
            .count(),
        2_usize,
        "both item events precede the liveness"
    );
    assert!(
        events.contains(&SynthesisEvent::Match {
            origin: origin(Coordinate(0), Coordinate(1), Coordinate(0)),
            branches: vec![BranchStatus::Refuted, BranchStatus::Possibly],
        }),
        "the branches are published verbatim"
    );
    assert_eq!(
        events.last(),
        Some(&SynthesisEvent::Completed),
        "the stream closes last"
    );
}

#[test]
fn an_origin_carries_exactly_one_liveness_entry()
{
    let mut liveness = Liveness::new();
    let at = origin(Coordinate(0), Coordinate(0), Coordinate(0));
    assert_eq!(
        liveness.insert(at, vec![BranchStatus::Possibly]),
        Maybe::Absent(super::displaced::Absent::Fresh),
        "the first recording displaces nothing"
    );
    assert_eq!(
        liveness.insert(at, vec![BranchStatus::Refuted]),
        Maybe::Present(vec![BranchStatus::Possibly]),
        "the second is reported as a displacement"
    );
    let events: Vec<SynthesisEvent> =
        SynthesisStream::from_resume_with_liveness(&two_item_resume(), &liveness).collect();
    assert_eq!(
        match_origins(&events),
        [at],
        "the stream carries one event for the origin"
    );
    assert!(
        events.contains(&SynthesisEvent::Match {
            origin: at,
            branches: vec![BranchStatus::Refuted],
        }),
        "the latest vector replaces the displaced value"
    );
}

#[test]
fn an_unretained_submission_is_published_not_omitted()
{
    let mut liveness = Liveness::new();
    liveness.mark_unretained(SubmissionOrdinal::from(0_usize));
    assert!(
        !bool::from(liveness.is_empty()),
        "a mark alone publishes liveness"
    );
    let _displaced = liveness.insert(origin(Coordinate(1), Coordinate(0), Coordinate(0)), vec![
        BranchStatus::Possibly,
    ]);
    assert!(
        !bool::from(liveness.is_empty()),
        "marks and matches both count"
    );
    let events: Vec<SynthesisEvent> =
        SynthesisStream::from_resume_with_liveness(&two_item_resume(), &liveness).collect();
    assert!(
        events.contains(&SynthesisEvent::SourceNotRetained {
            submission: SubmissionOrdinal::from(0_usize),
        }),
        "submission 0 is named as unretained"
    );
    assert_eq!(
        match_origins(&events),
        [origin(Coordinate(1), Coordinate(0), Coordinate(0))],
        "only the retained submission publishes statuses"
    );
}

#[test]
fn an_empty_stream_finishes_once_and_remains_exhausted()
{
    let mut program = Program::new(CoreArena::new(), Vec::new()).expect("empty program");
    let resume = check_program(&mut program, CheckBudget::DEFAULT).expect("empty order");
    let mut stream = SynthesisStream::from_resume(&resume);
    assert_eq!(
        stream.next(),
        Some(SynthesisEvent::Started {
            item_count: crate::boundary::ItemCount::from(0_usize)
        })
    );
    assert_eq!(stream.next(), Some(SynthesisEvent::Completed));
    for _ in 0_usize .. 3_usize {
        assert_eq!(stream.next(), None);
    }
}

#[test]
fn a_plain_stream_addresses_each_source_item_once()
{
    let resume = two_item_resume();
    let mut stream = SynthesisStream::from_resume(&resume);
    assert_eq!(
        stream.next(),
        Some(SynthesisEvent::Started {
            item_count: crate::boundary::ItemCount::from(2_usize)
        })
    );
    for ordinal in 0_usize .. 2 {
        let Some(SynthesisEvent::Item { index, handle, .. }) = stream.next()
        else {
            panic!("each source item has an event");
        };
        assert_eq!(usize::from(index), ordinal);
        assert!(
            matches!(resume.reference(handle), Maybe::Present(&crate::region::Reference::Item { occurrence, .. }) if usize::from(occurrence) == ordinal)
        );
    }
    assert_eq!(stream.next(), Some(SynthesisEvent::Completed));
    assert_eq!(stream.next(), None);
}

#[test]
fn an_empty_branch_vector_remains_a_match()
{
    let mut liveness = Liveness::new();
    assert!(bool::from(liveness.is_empty()));
    let at = origin(
        Coordinate(9),
        Coordinate(usize::MAX),
        Coordinate(usize::MAX),
    );
    assert_eq!(
        liveness.insert(at, Vec::new()),
        Maybe::Absent(super::displaced::Absent::Fresh)
    );
    assert!(!bool::from(liveness.is_empty()));
    let events: Vec<SynthesisEvent> =
        SynthesisStream::from_resume_with_liveness(&two_item_resume(), &liveness).collect();
    assert_eq!(match_origins(&events), [at]);
    assert!(events.contains(&SynthesisEvent::Match {
        origin: at,
        branches: Vec::new()
    }));
}

#[test]
fn unretained_marks_dominate_stored_matches()
{
    let mut liveness = Liveness::new();
    let hidden = origin(Coordinate(0), Coordinate(0), Coordinate(0));
    let retained = origin(
        Coordinate(1),
        Coordinate(usize::MAX),
        Coordinate(usize::MAX),
    );
    assert_eq!(
        liveness.insert(hidden, vec![BranchStatus::Satisfied]),
        Maybe::Absent(super::displaced::Absent::Fresh)
    );
    liveness.mark_unretained(SubmissionOrdinal::from(0_usize));
    liveness.mark_unretained(SubmissionOrdinal::from(0_usize));
    let Maybe::Present(displaced) = liveness.insert(hidden, vec![BranchStatus::Possibly])
    else {
        panic!("marking does not erase the stored vector");
    };
    assert_eq!(displaced.as_slice(), [BranchStatus::Satisfied]);
    assert_eq!(
        liveness.insert(retained, vec![BranchStatus::Refuted]),
        Maybe::Absent(super::displaced::Absent::Fresh)
    );
    let mut tail =
        SynthesisStream::from_resume_with_liveness(&two_item_resume(), &liveness).skip(3);
    assert_eq!(
        tail.next(),
        Some(SynthesisEvent::SourceNotRetained {
            submission: SubmissionOrdinal::from(0_usize)
        })
    );
    let Some(SynthesisEvent::Match { origin, branches }) = tail.next()
    else {
        panic!("the retained source match follows the missing-source event");
    };
    assert_eq!(origin, retained);
    assert_eq!(branches.as_slice(), [BranchStatus::Refuted]);
    assert_eq!(tail.next(), Some(SynthesisEvent::Completed));
    assert_eq!(tail.next(), None);
}
