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
///
/// # Specification
/// - requires: the producer classifies a branch against its scrutinee and the
///   possible fillings of holes.
/// - ensures: the three labels remain distinct when stored and published;
///   transport does not turn uncertainty into satisfaction or refutation.
/// - executable: none — the declaration has no call boundary and carries
///   neither the branch nor its scrutinee; classification is the producer's
///   obligation, not a property the stream can reconstruct.
///
/// # Adequacy
/// - hypothesis: L3 — supplied satisfied, possible and refuted labels survive
///   the liveness map and event stream in their recorded order. These witnesses
///   establish transport only, not the truth of a producer's classification.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
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
///
/// # Specification
/// - requires: the producer interprets the coordinates in its source records.
/// - ensures: origins are identified and ordered lexicographically by
///   submission, source item and match index, not by a core item position.
/// - executable: none — this declaration has no call boundary; comparison is
///   derived from its ordered fields and source ownership is external.
///
/// # Adequacy
/// - hypothesis: L3 — reversed insertion order separates source-item priority
///   from match-index priority; an extreme retained origin beside an unretained
///   submission witnesses submission order without a core-item membership test.
///   The cases do not certify the producer's source-coordinate assignment.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
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
///
/// # Specification
/// - requires: recorded statuses and source-retention marks come from a
///   producer; they may name no item of a particular core resume.
/// - ensures: one latest branch vector is held per origin, including an empty
///   vector; a marked submission publishes one missing-source event instead of
///   any stored matches from that submission.
/// - executable: none — this declaration has no call boundary. Mutation and
///   stream-construction predicates check its state and publication relations;
///   the producer's classification and retention facts are external.
///
/// # Adequacy
/// - hypothesis: L3 — replacement, a zero-branch match, idempotent marking and
///   insertion on both sides of a retention mark separate latest-value storage
///   from publication. Semantic classification remains a producer obligation.
/// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
/// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
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
    /// - hypothesis: L3 — insertion, displacement and exact latest publication
    ///   distinguish replacement from accidental duplicate or stale entries. A
    ///   zero-branch vector remains an entry rather than being dropped. These
    ///   cases do not establish whether the supplied statuses are true.
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    /// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
    #[anodized::spec(
        captures: [before_length = self.matches.len(), previous_length = self.matches.get(&origin).map(Vec::len), incoming_length = branches.len()],
        ensures: |ret| self.matches.get(&origin).is_some_and(|stored| stored.len() == incoming_length)
            && before_length.checked_add(usize::from(previous_length.is_none())) == Some(self.matches.len())
            && match ret {
                Maybe::Present(ref displaced) => Some(displaced.len()) == previous_length,
                Maybe::Absent(displaced::Absent::Fresh) => previous_length.is_none(),
            }
    )]
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
    /// - hypothesis: L3 — a submission with no stored matches still publishes
    ///   its mark; repeated marking and insertions before and after a mark
    ///   retain one missing-source event and suppress that submission's
    ///   matches.
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    /// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
    #[anodized::spec(
        captures: [before = self.unretained.len(), present = self.unretained.contains(&submission)],
        ensures: self.unretained.contains(&submission)
            && before.checked_add(usize::from(!present)) == Some(self.unretained.len())
    )]
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
    /// - requires: nothing.
    /// - ensures: true exactly when neither a match entry nor a missing-source
    ///   mark is held; an entry with zero branches still publishes a match.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, match-only, mark-only and combined states
    ///   distinguish the two independent ways liveness can be nonempty.
    /// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    #[anodized::spec(ensures: |ret| bool::from(ret) == (self.matches.is_empty() && self.unretained.is_empty()))]
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> LivenessEmpty
    {
        LivenessEmpty::from(self.matches.is_empty() && self.unretained.is_empty())
    }
}

/// One event of the synthesis stream.
///
/// # Specification
/// - requires: an event is interpreted as part of its stream and against the
///   resume or producer coordinates its payload names.
/// - ensures: streams frame ordered item events and then ordered liveness
///   events; a missing-source marker is not an empty set of matches.
/// - executable: none — this declaration has no call boundary; sequence
///   position and the source of its payload are external to an isolated event.
///
/// # Adequacy
/// - hypothesis: L3 — item-prefix ordering, exact branch vectors,
///   missing-source dominance and an empty framed stream distinguish the
///   observable event classes. The witnesses cover generated streams, not
///   arbitrary event lists.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
/// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
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
///
/// # Specification
/// - requires: constructed from a validated resume and optional liveness.
/// - ensures: its cursor begins before Started, advances once per yielded event
///   and stays exhausted after Completed; events retain their specified source
///   order and payload interpretation.
/// - executable: none — this declaration has no requires/ensures call boundary;
///   constructor and iterator predicates check framing and cursor transitions,
///   while resume and producer provenance are external.
///
/// # Adequacy
/// - hypothesis: L3 — nonempty item and liveness streams distinguish section
///   order; the empty resume distinguishes framing from item presence and
///   repeated terminal reads from a restarted iterator. The observed streams do
///   not establish producer provenance or an unbounded work estimate.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
/// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and two-item resumes separate framing from item
    ///   presence. The repeated key retains distinct source occurrences, and
    ///   three terminal reads distinguish exhaustion from a restarted iterator.
    ///   Other item counts and typing variants remain outside these finite
    ///   cases.
    /// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
    /// - witness: `stream::tests::a_plain_stream_addresses_each_source_item_once`
    #[anodized::spec(ensures: |ret| {
        let count = resume.checkpoints().items().len();
        ret.events.len().checked_sub(2) == Some(count)
            && ret.cursor == 0
            && matches!(ret.events.first(), Some(&SynthesisEvent::Started { item_count }) if usize::from(item_count) == count)
            && ret.events.last() == Some(&SynthesisEvent::Completed)
            && ret
                .events
                .get(1 .. count.saturating_add(1))
                .is_some_and(|events| {
                    events
                        .iter()
                        .enumerate()
                        .all(|(ordinal, event)| match *event {
                            | SynthesisEvent::Item {
                                index,
                                handle,
                                ref typing,
                                adoption,
                            } => {
                                usize::from(index) == ordinal
                                    && resume.handles().get(ordinal) == Some(&handle)
                                    && resume.adoptions().get(ordinal) == Some(&adoption)
                                    && resume
                                        .checkpoints()
                                        .items()
                                        .get(ordinal)
                                        .is_some_and(|checkpoint| checkpoint.typing() == typing)
                            },
                            | _ => false,
                        })
                })
    })]
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
    /// - hypothesis: L3 — reversed origin insertion, replacement, empty branch
    ///   vectors, missing-source marks without matches and marks that suppress
    ///   stored matches distinguish section order, origin order and precedence.
    ///   An extreme source origin remains independent of core item membership.
    ///   These finite cases do not establish an unbounded work estimate.
    /// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    /// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
    /// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
    #[anodized::spec(ensures: |ret| {
        let count = resume.checkpoints().items().len();
        let retained = liveness
            .matches
            .keys()
            .filter(|origin| !liveness.unretained.contains(&origin.submission))
            .count();
        let tail_count = liveness.unretained.len().checked_add(retained);
        ret.events.len().checked_sub(2) == tail_count.and_then(|tail| count.checked_add(tail))
            && ret.cursor == 0
            && matches!(ret.events.first(), Some(&SynthesisEvent::Started { item_count }) if usize::from(item_count) == count)
            && ret.events.last() == Some(&SynthesisEvent::Completed)
            && ret
                .events
                .get(1 .. count.saturating_add(1))
                .is_some_and(|events| {
                    events
                        .iter()
                        .enumerate()
                        .all(|(ordinal, event)| match *event {
                            | SynthesisEvent::Item {
                                index,
                                handle,
                                ref typing,
                                adoption,
                            } => {
                                usize::from(index) == ordinal
                                    && resume.handles().get(ordinal) == Some(&handle)
                                    && resume.adoptions().get(ordinal) == Some(&adoption)
                                    && resume
                                        .checkpoints()
                                        .items()
                                        .get(ordinal)
                                        .is_some_and(|checkpoint| checkpoint.typing() == typing)
                            },
                            | _ => false,
                        })
                })
            && ret
                .events
                .iter()
                .skip(count.saturating_add(1))
                .take(ret.events.len().saturating_sub(count).saturating_sub(2))
                .all(|event| match *event {
                    | SynthesisEvent::Match {
                        origin,
                        ref branches,
                    } => {
                        !liveness.unretained.contains(&origin.submission)
                            && liveness.matches.get(&origin) == Some(branches)
                    },
                    | SynthesisEvent::SourceNotRetained { submission } => {
                        liveness.unretained.contains(&submission)
                    },
                    | _ => false,
                })
            && ret
                .events
                .iter()
                .skip(count.saturating_add(1))
                .zip(ret.events.iter().skip(count.saturating_add(2)))
                .all(|(left, right)| match (left, right) {
                    | (
                        &SynthesisEvent::Match { origin: left, .. },
                        &SynthesisEvent::Match { origin: right, .. },
                    ) => left < right,
                    | (
                        &SynthesisEvent::Match { origin, .. },
                        &SynthesisEvent::SourceNotRetained { submission },
                    ) => origin.submission < submission,
                    | (
                        &SynthesisEvent::SourceNotRetained { submission },
                        &SynthesisEvent::Match { origin, .. },
                    ) => submission < origin.submission,
                    | (
                        &SynthesisEvent::SourceNotRetained { submission: left },
                        &SynthesisEvent::SourceNotRetained { submission: right },
                    ) => left < right,
                    | (_, &SynthesisEvent::Completed) => true,
                    | _ => false,
                })
    })]
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
    /// - requires: nothing.
    /// - ensures: the next stored event is yielded and the cursor advances
    ///   once; when no event remains, None is returned and the cursor stays
    ///   fixed, including on repeated calls after completion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete nonempty streams witness ordered
    ///   advancement; an empty resume yields Started then Completed, followed
    ///   by three terminal reads. This finite boundary distinguishes early
    ///   stopping and restart.
    /// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
    /// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
    #[anodized::spec(
        captures: [before = self.cursor],
        ensures: |ret| ret.as_ref() == self.events.get(before)
            && self.cursor == if ret.is_some() { before.saturating_add(1) } else { before }
    )]
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
    /// - requires: nothing.
    /// - ensures: two unsigned integer items with repeated keys are judged in a
    ///   fresh program, producing aligned checkpoint, handle and adoption
    ///   vectors and synthesised typings.
    /// - panics: if the fixed ascending program or its order cannot be built.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ordered and replacement liveness scenarios use
    ///   this two-item resume and observe its item prefix before liveness
    ///   events. This fixture does not cover refused items or resumed adoption.
    /// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    #[anodized::spec(ensures: |ret| ret.checkpoints().items().len() == 2
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
    /// - hypothesis: L3 — ordered streams with multiple origins, replacement
    ///   and a missing-source marker distinguish filtering from source-item
    ///   indexing. The witnessed inputs are constructed streams, not arbitrary
    ///   permutations.
    /// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    #[anodized::spec(ensures: |ret| ret.iter().copied().eq(events.iter().filter_map(|event| match *event {
        SynthesisEvent::Match { origin, .. } => Some(origin),
        _ => None,
    })))]
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
        let _displaced = liveness
            .insert(origin(Coordinate(1), Coordinate(0), Coordinate(0)), vec![
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
}
