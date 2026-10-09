//! The synthesis stream: ordered, resumable events over one validated resume.
//!
//! # Items first, then liveness by origin
//!
//! A stream opens with the item count, carries one event per item in source
//! order — its handle, its typing and whether it was adopted — then the match
//! liveness its producer computed, and closes. Liveness follows the items
//! rather than interleaving with them: an item is addressed by core position,
//! a match by the source coordinates its producer gives it, and one source
//! item may lower to several core items, so there is no item a match belongs
//! beside. A submission whose source records the producer no longer holds is
//! named by an event of its own rather than left silent, because silence
//! would read as a submission with no matches. The stream reads its inputs
//! and computes nothing, so a run that adopted and a run that judged publish
//! the same events but for the adoption marks.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::boundary::ItemCount;
use crate::boundary::ItemOrdinal;
use crate::boundary::LivenessEmpty;
use crate::boundary::MatchOrdinal;
use crate::boundary::SourceItemOrdinal;
use crate::boundary::SubmissionOrdinal;
use crate::checkpoint::Adoption;
use crate::checkpoint::Resume;
use crate::order::ItemHandle;
use crate::typing::Typing;

quenchant_shape::reason_enum! {
    /// Why recording a match displaced nothing.
    pub mod displaced {
        /// The reason nothing was displaced.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The origin carried no entry before.
            Fresh,
        }
    }
}

/// How one branch of a match stands against its scrutinee.
///
/// A scrutinee holding a hole leaves some branches undecided; calling such a
/// branch refuted hides a match the finished program will take, and calling
/// it satisfied claims one it may not. `Possibly` is the third answer that
/// keeps checking from blocking on an unfinished program.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BranchStatus
{
    /// The branch matches, whatever any hole is filled with.
    Satisfied,
    /// Some hole decides whether the branch matches.
    Possibly,
    /// The branch cannot match, whatever any hole is filled with.
    Refuted,
}

/// Where one analysed match came from, in its producer's own coordinates.
///
/// No core position appears here: a match is a fact about source the
/// programmer wrote, and the stream never interprets the coordinates beyond
/// identifying and ordering matches by them.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MatchOrigin
{
    /// The submission the match was written in.
    pub submission: SubmissionOrdinal,
    /// The source item of that submission owning the match.
    pub source_item: SourceItemOrdinal,
    /// Which match of the source item this is.
    pub match_index: MatchOrdinal,
}

/// The match liveness a stream publishes, keyed by origin.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Liveness
{
    /// One entry per analysed match.
    matches: BTreeMap<MatchOrigin, Vec<BranchStatus>>,
    /// The submissions whose source records were not retained.
    unretained: BTreeSet<SubmissionOrdinal>,
}

impl Liveness
{
    /// An empty map: nothing analysed, nothing missing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Record one match's per-branch statuses at its origin.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the map holds exactly one entry for `origin`, `branches`.
    /// - provides: the entry this call displaced, so a producer publishing a
    ///   match twice is caught; `displaced::Absent::Fresh` when there was none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the keyed insert, separated by
    ///   recording one origin twice and counting the stream's match events.
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    #[inline]
    pub fn insert(
        &mut self,
        origin: MatchOrigin,
        branches: Vec<BranchStatus>,
    ) -> Maybe<Vec<BranchStatus>, displaced::Absent>
    {
        match self.matches.insert(origin, branches) {
            | Some(previous) => Maybe::Present(previous),
            | None => Maybe::Absent(displaced::Absent::Fresh),
        }
    }

    /// Name a submission whose source records were not retained.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stream names the submission in an event of its own and
    ///   publishes none of its matches.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the unretained mark, separated by an
    ///   unretained submission beside a retained one.
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    #[inline]
    pub fn mark_unretained(
        &mut self,
        submission: SubmissionOrdinal,
    )
    {
        let _fresh = self.unretained.insert(submission);
    }

    /// Whether the map publishes nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> LivenessEmpty
    {
        LivenessEmpty::from(self.matches.is_empty() && self.unretained.is_empty())
    }
}

/// One event of the synthesis stream.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SynthesisEvent
{
    /// The stream opens over this many items.
    Started
    {
        /// The number of items.
        item_count: ItemCount,
    },
    /// One item's typing.
    Item
    {
        /// The item's source ordinal.
        index: ItemOrdinal,
        /// The item's identity across revisions.
        handle: ItemHandle,
        /// The item's typing.
        typing: Typing,
        /// Whether its checkpoint was adopted.
        adoption: Adoption,
    },
    /// One match's per-branch liveness.
    Match
    {
        /// The match, in its producer's coordinates.
        origin: MatchOrigin,
        /// One status per branch, in source order.
        branches: Vec<BranchStatus>,
    },
    /// A submission whose source records are gone, so no liveness can be
    /// computed for it.
    SourceNotRetained
    {
        /// The submission.
        submission: SubmissionOrdinal,
    },
    /// The stream closes after every item and match.
    Completed,
}

/// A deterministic, resumable sequence of synthesis events.
#[derive(Clone, Debug)]
pub struct SynthesisStream
{
    /// The events, in order.
    events: Vec<SynthesisEvent>,
    /// The next event to hand out.
    cursor: usize,
}

impl SynthesisStream
{
    /// The stream of `resume` with no liveness.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stream [`Self::from_resume_with_liveness`] gives with an
    ///   empty map.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn from_resume(resume: &Resume) -> Self
    {
        Self::from_resume_with_liveness(resume, &Liveness::new())
    }

    /// The stream of `resume` and the liveness its producer computed.
    ///
    /// # Specification
    /// - requires: nothing of `liveness` beyond its type: an origin naming no
    ///   item of `resume` is published unchanged, because the stream is not the
    ///   authority on which matches exist.
    /// - ensures: `Started`, then one `Item` per item in source order, then per
    ///   submission ascending either its `SourceNotRetained` or its `Match`
    ///   events in origin order, then `Completed`.
    /// - provides: a stream that is a function of its inputs alone.
    /// - panics: none.
    /// - intension: one pass over the items and one range walk per submission
    ///   over the matches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the section order, the keying and
    ///   the unretained events, separated by matches recorded out of order, an
    ///   origin recorded twice, an unretained submission beside a retained one,
    ///   and an empty map.
    /// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    /// - witness: `stream::tests::absent_liveness_leaves_the_stream_unchanged`
    #[inline]
    #[must_use]
    pub fn from_resume_with_liveness(
        resume: &Resume,
        liveness: &Liveness,
    ) -> Self
    {
        let items = resume.checkpoints().items();
        let mut events = Vec::with_capacity(items.len().saturating_add(2));
        events.push(SynthesisEvent::Started {
            item_count: ItemCount::from(items.len()),
        });
        for (index, ((checkpoint, &adoption), &handle)) in items
            .iter()
            .zip(resume.adoptions())
            .zip(resume.handles())
            .enumerate()
        {
            events.push(SynthesisEvent::Item {
                index: ItemOrdinal::from(index),
                handle,
                typing: checkpoint.typing().clone(),
                adoption,
            });
        }
        let mut submissions: BTreeSet<SubmissionOrdinal> = liveness.unretained.clone();
        submissions.extend(liveness.matches.keys().map(|origin| origin.submission));
        for submission in submissions {
            if liveness.unretained.contains(&submission) {
                events.push(SynthesisEvent::SourceNotRetained { submission });
                continue;
            }
            let first = MatchOrigin {
                submission,
                source_item: SourceItemOrdinal::from(0_usize),
                match_index: MatchOrdinal::from(0_usize),
            };
            let last = MatchOrigin {
                submission,
                source_item: SourceItemOrdinal::from(usize::MAX),
                match_index: MatchOrdinal::from(usize::MAX),
            };
            for (&origin, branches) in liveness.matches.range(first ..= last) {
                events.push(SynthesisEvent::Match {
                    origin,
                    branches: branches.clone(),
                });
            }
        }
        events.push(SynthesisEvent::Completed);
        Self { events, cursor: 0 }
    }
}

impl Iterator for SynthesisStream
{
    type Item = SynthesisEvent;

    /// The next event, or the end of the stream.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        let event = self.events.get(self.cursor).cloned();
        if event.is_some() {
            self.cursor = self.cursor.saturating_add(1);
        }
        event
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

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
    /// trivial.
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
    /// trivial.
    fn match_origins(events: &[SynthesisEvent]) -> Vec<MatchOrigin>
    {
        events
            .iter()
            .filter_map(|event| match *event {
                | SynthesisEvent::Match { origin, .. } => Some(origin),
                | _ => None,
            })
            .collect()
    }

    #[test]
    fn liveness_follows_the_items_in_origin_order()
    {
        let mut liveness = Liveness::new();
        let _displaced =
            liveness.insert(origin(Coordinate(0), Coordinate(1), Coordinate(0)), vec![
                BranchStatus::Refuted,
                BranchStatus::Possibly,
            ]);
        let _displaced = liveness
            .insert(origin(Coordinate(0), Coordinate(0), Coordinate(1)), vec![
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
    }

    #[test]
    fn an_unretained_submission_is_published_not_omitted()
    {
        let mut liveness = Liveness::new();
        liveness.mark_unretained(SubmissionOrdinal::from(0_usize));
        let _displaced = liveness
            .insert(origin(Coordinate(1), Coordinate(0), Coordinate(0)), vec![
                BranchStatus::Possibly,
            ]);
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
    fn absent_liveness_leaves_the_stream_unchanged()
    {
        let resume = two_item_resume();
        let plain: Vec<SynthesisEvent> = SynthesisStream::from_resume(&resume).collect();
        let empty: Vec<SynthesisEvent> =
            SynthesisStream::from_resume_with_liveness(&resume, &Liveness::new()).collect();
        assert_eq!(plain, empty, "no liveness, no extra events");
        assert!(
            bool::from(Liveness::new().is_empty()),
            "the empty map says so of itself"
        );
        assert!(
            !plain.iter().any(|event| matches!(
                *event,
                SynthesisEvent::Match { .. } | SynthesisEvent::SourceNotRetained { .. }
            )),
            "nothing liveness-shaped appears"
        );
    }
}
