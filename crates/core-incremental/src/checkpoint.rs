//! Checkpoints and resume: one forward pass that adopts what still answers
//! and judges the rest.
//!
//! # Record provenance and reuse validation
//!
//! An item's checkpoint records its content, its footprint, the support its
//! judgement consulted — each signature answer it read, by reference — and
//! its typing. A later revision recalls a checkpoint by content, through the
//! one check memo batch and incremental runs share, and adopts it only when
//! three things hold: every recorded answer equals, pointwise and by content,
//! the answer the edited program's table gives at that point of the pass; no
//! reference in the item's type positions, nor in any recorded answer's type,
//! names a definition whose value changed; and the adopted type can be seated.
//! Otherwise the item is judged again. Persisted checkpoints go through the
//! same pass as in-memory records. Neither decoding nor this pass proves that
//! recorded typing and support truthfully describe a prior judgement.
//!
//! # The same pass, two memos
//!
//! Batch checking is the pass at [`NullMemo`], which recalls nothing, so every
//! item is judged; incremental checking is the pass at [`OrderedMemo`] built
//! from the base checkpoints. The incremental law — incremental equals
//! batch — assumes those records faithfully describe earlier checker results
//! under their recorded allowance. The differential tests compare the two
//! memos against the checker's own batch entry; deliberate mutations expose
//! the premise rather than establishing authentication of arbitrary records.
//!
//! # A value change closes over readers, once
//!
//! A definition whose content changed, or which was inserted or deleted,
//! seeds the value-changed set, and the set closes over the footprints' read
//! relation through reverse edges with a worklist: every edge is crossed at
//! most once, so the closure is linear in the program's reads. An opaque
//! item, whose reads are unknown, reads everything once anything changed.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::FormedValueType;
use gandr_core_checker::Support;
use gandr_core_checker::check_declaration_supported;
use gandr_core_checker::form_value_type;
use gandr_core_checker::signature_table;
use gandr_core_checker::unfolding;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_check_memo::OrderedMemo;
use gandr_theory_orders::OrderError;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemCount;
use crate::boundary::ItemOrdinal;
use crate::codec::write_item_content;
use crate::content::ArenaNode;
use crate::content::Encoded;
use crate::content::ItemContent;
use crate::content::Opacity;
use crate::content::TypeContent;
use crate::content::encode_item;
use crate::content::seating;
use crate::footprint::Footprint;
use crate::footprint::footprint_of;
use crate::order::ItemHandle;
use crate::order::ItemOrder;
use crate::order::SpliceCensus;
use crate::order::handle;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;
use crate::typing::Projection;
use crate::typing::Typing;

quenchant_shape::reason_enum! {
    /// Why an item has no memo identity, or no checkpoint to adopt.
    pub mod recall {
        /// The reason nothing is recalled.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The item holds an unresolved id, so it has no identity.
            Opaque,
            /// The memo holds no checkpoint of the same content.
            Missed,
            /// A recorded answer differs from the one the edited table gives.
            Outdated,
            /// A type position reads a definition whose value changed.
            ValueRead,
            /// The adopted type could not be seated in the edited arena.
            Unseated,
        }
    }
}

/// What the signature table answers for a reference.
///
/// # Specification
/// - executable: none — an answer stores content, not the signature table that
///   answered the query.
///
/// # Adequacy
/// - hypothesis: L2 — differential edit cases compare recorded typings with
///   fresh checking; the constructed invalidation guard separately tests
///   references inside an answer without claiming checker provenance.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `checkpoint::tests::recorded_answer_references_participate_in_value_invalidation`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Answer
{
    /// No type is held.
    Untyped,
    /// This type is held.
    Typed(TypeContent),
}

/// One answer a judgement consulted, by the reference it asked about.
///
/// # Specification
/// - executable: none — a stored reference-answer pair cannot attest that a
///   judgement consulted it.
///
/// # Adequacy
/// - hypothesis: L2 — changed support invalidates reuse; canonicalization
///   preserves the first answer for a repeated reference.
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
/// - witness: `checkpoint::tests::support_canonicalization_keeps_the_first_answer`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Answered
{
    /// The reference asked about.
    reference: Reference,
    /// The answer given.
    answer: Answer,
}

impl Answered
{
    /// The answer `answer` given for `reference`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        reference: Reference,
        answer: Answer,
    ) -> Self
    {
        Self { reference, answer }
    }

    /// The reference asked about.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reference(&self) -> &Reference
    {
        &self.reference
    }

    /// The answer given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn answer(&self) -> &Answer
    {
        &self.answer
    }
}

/// One item's checkpoint.
///
/// # Specification
/// - executable: none — raw checkpoint parts are admitted; construction does
///   not certify prior checking.
///
/// # Adequacy
/// - hypothesis: L3 — differential teeth corrupt typing, support and footprint
///   to separate what adoption reads from what its evidence must validate.
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
/// - witness: `tests::incremental::a_suppressed_invalidation_signal_is_caught`
/// - witness: `tests::incremental::a_stored_footprint_is_not_an_adoption_input`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ItemCheckpoint
{
    /// The item's content.
    content: ItemContent,
    /// The item's footprint, carried for inspection; never an adoption input.
    footprint: Footprint,
    /// The answers the judgement consulted, ascending by reference.
    support: Vec<Answered>,
    /// The item's typing.
    typing: Typing,
}

impl ItemCheckpoint
{
    /// The checkpoint of these parts, its support put in canonical order.
    ///
    /// # Specification
    /// - requires: nothing — raw parts are admitted. Construction canonicalizes
    ///   support but does not establish a prior judgement's truth.
    /// - ensures: the parts, with the support ascending by reference and each
    ///   reference once, its first answer kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — mixed references and conflicting duplicates test
    ///   canonical order and first-answer retention. The attribute bounds order
    ///   and cardinality without retaining an owned copy of the incoming
    ///   support.
    /// - witness: `checkpoint::tests::support_canonicalization_keeps_the_first_answer`
    #[spec(
        captures: [count = support.len()],
        ensures: |ret| {
            ret.support.len() <= count
                && ret.support.windows(2).all(|pair| {
                    pair.first()
                        .zip(pair.last())
                        .is_none_or(|(left, right)| left.reference < right.reference)
                })
        },
    )]
    #[inline]
    #[must_use]
    pub fn new(
        content: ItemContent,
        footprint: Footprint,
        support: Vec<Answered>,
        typing: Typing,
    ) -> Self
    {
        Self {
            content,
            footprint,
            support: canonical_support(support),
            typing,
        }
    }

    /// The item's content.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn content(&self) -> &ItemContent
    {
        &self.content
    }

    /// The item's footprint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn footprint(&self) -> &Footprint
    {
        &self.footprint
    }

    /// The answers the judgement consulted, ascending by reference.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn support(&self) -> &[Answered]
    {
        &self.support
    }

    /// The item's typing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn typing(&self) -> &Typing
    {
        &self.typing
    }

    /// The checkpoint with its footprint replaced, for a test that shows the
    /// stored footprint is no adoption input.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_footprint(
        self,
        footprint: Footprint,
    ) -> Self
    {
        Self { footprint, ..self }
    }

    /// The checkpoint with its typing replaced, for a test that shows a stale
    /// typing is caught by the differential.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_typing(
        self,
        typing: Typing,
    ) -> Self
    {
        Self { typing, ..self }
    }

    /// The checkpoint with its support replaced, for a test that shows a
    /// suppressed invalidation signal is caught by the differential.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the replacement support is ascending and unique by reference,
    ///   retaining the first answer for each reference; other fields are
    ///   retained.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — conflicting duplicates distinguish first-answer
    ///   retention; the differential corruption witness exercises replacement
    ///   before reuse.
    /// - witness: `checkpoint::tests::support_canonicalization_keeps_the_first_answer`
    /// - witness: `tests::incremental::a_suppressed_invalidation_signal_is_caught`
    #[spec(
        captures: [count = support.len()],
        ensures: |ret| {
            ret.support.len() <= count
                && ret.support.windows(2).all(|pair| {
                    pair.first()
                        .zip(pair.last())
                        .is_none_or(|(left, right)| left.reference < right.reference)
                })
        },
    )]
    #[inline]
    #[must_use]
    pub fn with_support(
        self,
        support: Vec<Answered>,
    ) -> Self
    {
        Self {
            support: canonical_support(support),
            ..self
        }
    }
}

/// A complete checkpoint set: the allowance it was judged under and one
/// checkpoint per item, in source order.
///
/// # Specification
/// - executable: none — the record has no original program or checking context
///   to certify its provenance.
///
/// # Adequacy
/// - hypothesis: L2 — persistence preserves supported records; subsequent reuse
///   is compared with fresh checking over the finite generated edit domain.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `tests::incremental::incremental_equals_from_scratch`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Checkpoints
{
    /// The allowance every judgement of the set ran under.
    budget: CheckBudget,
    /// One checkpoint per item, in source order.
    items: Vec<ItemCheckpoint>,
}

impl Checkpoints
{
    /// The set of `items` judged under `budget`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        budget: CheckBudget,
        items: Vec<ItemCheckpoint>,
    ) -> Self
    {
        Self { budget, items }
    }

    /// The allowance every judgement of the set ran under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn budget(&self) -> CheckBudget
    {
        self.budget
    }

    /// One checkpoint per item, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn items(&self) -> &[ItemCheckpoint]
    {
        &self.items
    }

    /// The checkpoints, by value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_items(self) -> Vec<ItemCheckpoint>
    {
        self.items
    }
}

/// Whether an item's checkpoint was adopted or the item judged.
///
/// # Specification
/// - executable: none — the tag carries no judgement or validated checkpoint to
///   establish how it arose.
///
/// # Adequacy
/// - hypothesis: L3 — unchanged items are reused, a body-only edit preserves a
///   dependent type, and a type change forces that dependent to be judged.
/// - witness: `tests::incremental::noop_edit_adopts_everything`
/// - witness: `tests::incremental::body_edit_adopts_the_type_stable_dependent`
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Adoption
{
    /// The base checkpoint still answered and was adopted.
    Adopted,
    /// The item was judged.
    Judged,
}

/// The work one resume did, counted per item and per edge.
///
/// The counts are the pass's declared intension: every one is linear in the
/// program, which is what the recheck witness pins at growing sizes.
///
/// # Specification
/// - executable: none — a census value alone cannot replay the work whose
///   counts it records.
///
/// # Adequacy
/// - hypothesis: L2 — exact adoption counts and a finite growing-size family
///   bound the accounting evidence; saturation is checked independently at
///   usize limits.
/// - witness: `tests::incremental::noop_edit_adopts_everything`
/// - witness: `tests::defects::items_visited_for_a_head_edit_grow_linearly`
/// - witness: `checkpoint::tests::census_increment_saturates_at_the_boundary`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ResumeCensus
{
    /// Items of the edited program, each encoded once.
    pub items: ItemCount,
    /// Memo recalls made.
    pub recalled: ItemCount,
    /// Items whose checkpoint was adopted.
    pub adopted: ItemCount,
    /// Items judged.
    pub judged: ItemCount,
    /// Seats minted for adopted synthesised types.
    pub minted: ItemCount,
    /// Recalled items declined because a recorded answer no longer holds.
    pub outdated: ItemCount,
    /// Recalled items declined because a type position of theirs reads a
    /// definition whose value changed: the guard against an answer that
    /// depends on a value while only types are compared.
    pub value_reads: ItemCount,
    /// Definitions that seeded the value-changed set.
    pub seeds: ItemCount,
    /// Reverse read edges the closure crossed.
    pub closure_edges: ItemCount,
    /// Definitions in the closed value-changed set.
    pub value_changed: ItemCount,
    /// What the splice did to the item order.
    pub splice: SpliceCensus,
}

/// Why a resume could not complete.
///
/// # Specification
/// - executable: none — an error tag carries no order operation whose refusal
///   it could establish.
///
/// # Adequacy
/// - hypothesis: L2 — successful finite edit chains exercise propagation
///   boundaries; order-capacity exhaustion is not witnessed by this crate.
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ResumeError
{
    /// The item order could not be built or spliced.
    Order(OrderError),
}

impl fmt::Display for ResumeError
{
    /// Writes the failure's message.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Order(error) => write!(f, "the item order failed: {error}"),
        }
    }
}

impl core::error::Error for ResumeError
{
}

/// One revision's checkpoints, how each was reached, and the item order that
/// carries identity to the next revision.
///
/// # Specification
/// - executable: none — the record cannot reconstruct the checking history; its
///   constructors and resume operations check observable correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — differential checking, explicit adoption cases and
///   revision handle transitions bound the relation among checkpoints, marks
///   and identity.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::noop_edit_adopts_everything`
/// - witness: `checkpoint::tests::revision_handles_track_insertions_and_deletions`
pub struct Resume
{
    /// The checkpoints, one per item.
    checkpoints: Checkpoints,
    /// Whether each item was adopted or judged.
    adoptions: Vec<Adoption>,
    /// Each item's handle.
    handles: Vec<ItemHandle>,
    /// The order the handles live in.
    order: ItemOrder,
    /// The work the pass did.
    census: ResumeCensus,
}

impl fmt::Debug for Resume
{
    /// Writes the checkpoints, adoptions and census; the order is opaque.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("Resume")
            .field("checkpoints", &self.checkpoints)
            .field("adoptions", &self.adoptions)
            .field("census", &self.census)
            .finish_non_exhaustive()
    }
}

impl Resume
{
    /// A resume standing for restored checkpoints, judged by nothing in this
    /// process, each item under a fresh handle.
    ///
    /// # Specification
    /// - requires: nothing — this restores structure, not judgement provenance;
    ///   the next resume checks applicability of the recorded answers.
    /// - ensures: on success the checkpoints, every item marked judged, one
    ///   fresh handle per item, and an empty census.
    /// - fails: [`ResumeError::Order`] when the order cannot be built.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ResumeError::Order`] — the order-maintenance structure refused.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — empty and nonempty restoration provide fresh ordered
    ///   handles; subsequent insertion and deletion check retained and stale
    ///   identities. Order-capacity failures are outside the witnessed domain.
    /// - witness: `checkpoint::tests::revision_handles_track_insertions_and_deletions`
    #[spec(
        captures: [count = checkpoints.items.len(), budget = checkpoints.budget],
        ensures: |ret| {
            ret.as_ref().is_ok_and(|restored| {
                restored.checkpoints.items.len() == count
                    && restored.checkpoints.budget == budget
                    && restored.adoptions.len() == count
                    && restored
                        .adoptions
                        .iter()
                        .all(|mark| *mark == Adoption::Judged)
                    && restored.handles.len() == count
                    && restored.census == ResumeCensus::default()
                    && restored
                        .handles
                        .iter()
                        .zip(&restored.checkpoints.items)
                        .all(|(&handle, item)| {
                            restored.order.reference(handle)
                                == Maybe::Present(item.content.reference())
                        })
            }) || ret.is_err()
        },
    )]
    #[inline]
    pub fn from_checkpoints(checkpoints: Checkpoints) -> Result<Self, ResumeError>
    {
        let references: Vec<Reference> = checkpoints
            .items
            .iter()
            .map(|checkpoint| checkpoint.content.reference().clone())
            .collect();
        let (order, handles) = ItemOrder::seeded(&references).map_err(ResumeError::Order)?;
        Ok(Self {
            adoptions: alloc::vec![Adoption::Judged; checkpoints.items.len()],
            checkpoints,
            handles,
            order,
            census: ResumeCensus::default(),
        })
    }

    /// The checkpoints, one per item.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn checkpoints(&self) -> &Checkpoints
    {
        &self.checkpoints
    }

    /// Each item's typing, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn typings(&self) -> impl Iterator<Item = &Typing>
    {
        self.checkpoints
            .items
            .iter()
            .map(|checkpoint| &checkpoint.typing)
    }

    /// Whether each item was adopted or judged, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn adoptions(&self) -> &[Adoption]
    {
        &self.adoptions
    }

    /// How many items were adopted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn adopted_count(&self) -> ItemCount
    {
        self.census.adopted
    }

    /// Each item's handle, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn handles(&self) -> &[ItemHandle]
    {
        &self.handles
    }

    /// How two handles' items stand in this revision's source order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: their order, in constant time.
    /// - provides: `handle::Absent::Stale` when either handle names no item of
    ///   this revision.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — insertion orders retained and fresh identities;
    ///   deletion makes either stale operand fail independently.
    /// - witness: `checkpoint::tests::revision_handles_track_insertions_and_deletions`
    #[spec(
        ensures: |ret| match (
            self.handles.iter().position(|&handle| handle == left),
            self.handles.iter().position(|&handle| handle == right),
        ) {
            | (Some(left), Some(right)) => ret == Maybe::Present(left.cmp(&right)),
            | _ => ret == Maybe::Absent(handle::Absent::Stale),
        },
    )]
    #[inline]
    pub fn compare(
        &self,
        left: ItemHandle,
        right: ItemHandle,
    ) -> Maybe<Ordering, handle::Absent>
    {
        self.order.compare(left, right)
    }

    /// The reference of the item `handle` names in this revision.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the item's reference.
    /// - provides: `handle::Absent::Stale` for a handle of a deleted or
    ///   reordered item.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — retained handles name the same item after insertion;
    ///   deleting an item makes its old handle stale rather than naming its
    ///   neighbour.
    /// - witness: `checkpoint::tests::revision_handles_track_insertions_and_deletions`
    #[spec(
        ensures: |ret| {
            self.handles
                .iter()
                .position(|&held| held == handle)
                .and_then(|index| self.checkpoints.items.get(index))
                .map_or_else(
                    || ret == Maybe::Absent(handle::Absent::Stale),
                    |item| ret == Maybe::Present(item.content.reference()),
                )
        },
    )]
    #[inline]
    pub fn reference(
        &self,
        handle: ItemHandle,
    ) -> Maybe<&Reference, handle::Absent>
    {
        self.order.reference(handle)
    }

    /// The work the pass did.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn census(&self) -> ResumeCensus
    {
        self.census
    }
}

/// Judge every item of `program` under `budget`: the batch run.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success one checkpoint per item, each judged, with the typing
///   the checker's batch entry gives the same declarations in a fresh context,
///   and one fresh handle per item.
/// - provides: the batch half of the incremental law: the pass at [`NullMemo`].
/// - fails: [`ResumeError::Order`] when the order cannot be built.
/// - panics: none.
///
/// # Errors
/// [`ResumeError::Order`] — the order-maintenance structure refused.
///
/// # Adequacy
/// - hypothesis: L2 — the property suite compares every generated program's
///   batch checkpoints against the checker's batch entry, projected.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
#[spec(
    ensures: |ret| {
        ret.as_ref().is_ok_and(|checked| {
            checked.checkpoints.budget == budget
                && checked.checkpoints.items.len() == program.items().len()
                && checked.adoptions.len() == program.items().len()
                && checked.handles.len() == program.items().len()
                && usize::from(checked.census.items) == program.items().len()
                && usize::from(checked.census.adopted)
                    .checked_add(usize::from(checked.census.judged))
                    == Some(program.items().len())
                && checked
                    .checkpoints
                    .items
                    .iter()
                    .map(|item| item.content.reference())
                    .eq(program.references().iter())
                && checked
                    .adoptions
                    .iter()
                    .all(|mark| *mark == Adoption::Judged)
                && usize::from(checked.census.adopted) == 0
        }) || ret.is_err()
    },
)]
#[inline]
pub fn check_program(
    program: &mut Program,
    budget: CheckBudget,
) -> Result<Resume, ResumeError>
{
    let empty = Checkpoints::new(budget, Vec::new());
    let (order, base_handles) = ItemOrder::seeded(&[]).map_err(ResumeError::Order)?;
    advance::<NullMemoChoice>(&empty, order, &base_handles, program)
}

/// Resume from `base` onto the edited program, carrying item identity.
///
/// # Specification
/// - requires: nothing — `base` may be any checkpoint set, of any program.
/// - ensures: on success one answer per edited item under base's allowance,
///   each adopted only when the reuse checks hold; references surviving in
///   order keep their handles. Typings equal batch when the recorded typing and
///   complete support faithfully describe prior judgements of the recorded
///   content under that allowance. Forged records need not equal batch.
/// - provides: incremental reuse, not authentication of cached judgements.
/// - fails: [`ResumeError::Order`] when the order cannot be spliced.
/// - panics: none.
///
/// # Errors
/// [`ResumeError::Order`] — the order-maintenance structure refused.
///
/// # Adequacy
/// - hypothesis: L2 — generated programs and edit chains start from faithful
///   checker results and compare the resume against batch, with adoption made
///   non-vacuous by the precision probe. L3 mutation witnesses distinguish this
///   equivalence premise from validation of arbitrary recorded typings.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
/// - witness: `tests::incremental::body_edit_adopts_the_type_stable_dependent`
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
/// - witness: `tests::incremental::a_suppressed_invalidation_signal_is_caught`
#[spec(
    captures: [budget = base.checkpoints.budget],
    ensures: |ret| {
        ret.as_ref().is_ok_and(|resumed| {
            resumed.checkpoints.budget == budget
                && resumed.checkpoints.items.len() == edited.items().len()
                && resumed.adoptions.len() == edited.items().len()
                && resumed.handles.len() == edited.items().len()
                && usize::from(resumed.census.items) == edited.items().len()
                && usize::from(resumed.census.adopted)
                    .checked_add(usize::from(resumed.census.judged))
                    == Some(edited.items().len())
                && resumed
                    .checkpoints
                    .items
                    .iter()
                    .map(|item| item.content.reference())
                    .eq(edited.references().iter())
        }) || ret.is_err()
    },
)]
#[inline]
pub fn resume(
    base: Resume,
    edited: &mut Program,
) -> Result<Resume, ResumeError>
{
    let Resume {
        checkpoints,
        handles,
        order,
        ..
    } = base;
    advance::<OrderedMemoChoice>(&checkpoints, order, &handles, edited)
}

/// Resume from restored checkpoints onto the edited program, every item under
/// a fresh handle.
///
/// # Specification
/// - requires: nothing — arbitrary restored records are admitted.
/// - ensures: as [`resume`], with fresh handles.
/// - fails: [`ResumeError::Order`] when the order cannot be built.
/// - panics: none.
///
/// # Errors
/// [`ResumeError::Order`] — the order-maintenance structure refused.
///
/// # Adequacy
/// - hypothesis: L2 — faithful supported records are restored from memory and
///   reopened files then reused. L3 mutations show that stored footprints are
///   not adoption inputs, while forged typing or support can defeat batch
///   equivalence and must be caught by the differential oracle.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `tests::incremental::a_stored_footprint_is_not_an_adoption_input`
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
/// - witness: `tests::incremental::a_suppressed_invalidation_signal_is_caught`
#[spec(
    ensures: |ret| {
        ret.as_ref().is_ok_and(|resumed| {
            resumed.checkpoints.budget == base.budget
                && resumed.checkpoints.items.len() == edited.items().len()
                && resumed.adoptions.len() == edited.items().len()
                && resumed.handles.len() == edited.items().len()
                && usize::from(resumed.census.items) == edited.items().len()
                && usize::from(resumed.census.adopted)
                    .checked_add(usize::from(resumed.census.judged))
                    == Some(edited.items().len())
                && resumed
                    .checkpoints
                    .items
                    .iter()
                    .map(|item| item.content.reference())
                    .eq(edited.references().iter())
        }) || ret.is_err()
    },
)]
#[inline]
pub fn resume_from(
    base: &Checkpoints,
    edited: &mut Program,
) -> Result<Resume, ResumeError>
{
    let references: Vec<Reference> = base
        .items
        .iter()
        .map(|checkpoint| checkpoint.content.reference().clone())
        .collect();
    let (order, handles) = ItemOrder::seeded(&references).map_err(ResumeError::Order)?;
    advance::<OrderedMemoChoice>(base, order, &handles, edited)
}

/// The memo identity of an item: its content, and the content's digest.
///
/// # Specification
/// - executable: none — the borrowed pair cannot rehash itself without
///   replaying serialization; `identity_of` establishes its producer boundary.
///
/// # Adequacy
/// - hypothesis: L2 — noisy arenas give identical canonical bytes; no-op reuse
///   uses content identity. These cases are not a collision-resistance proof.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `tests::incremental::noop_edit_adopts_everything`
pub struct ItemIdentity<'content>
{
    /// The content compared.
    content: &'content ItemContent,
    /// The digest the memo buckets by.
    digest: ContentDigest,
}

/// The one plane item identities are accounted to.
///
/// # Specification
/// - executable: none — the plane tag has no memo whose accounting it could
///   observe.
///
/// # Adequacy
/// - hypothesis: L2 — no-op reuse exercises the sole item plane; build
///   predicates check that its census equals the total. No multi-plane claim is
///   made here.
/// - witness: `tests::incremental::noop_edit_adopts_everything`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ItemPlane
{
    /// Item checkpoints.
    Items,
}

impl MemoKey for ItemIdentity<'_>
{
    type Plane = ItemPlane;

    /// The item plane.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane(&self) -> ItemPlane
    {
        ItemPlane::Items
    }

    /// The first sixteen bytes of the content's BLAKE3 digest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn digest(&self) -> ContentDigest
    {
        self.digest
    }

    /// Content equality, never digest equality.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Agree` exactly when the two contents are equal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — identical programs reuse their checkpoints; changed
    ///   content and type changes separate identity from support validity.
    /// - witness: `tests::incremental::noop_edit_adopts_everything`
    /// - witness: `tests::incremental::body_edit_adopts_the_type_stable_dependent`
    /// - witness: `tests::incremental::type_change_retypes_the_dependent`
    #[spec(
        ensures: |ret| (ret == ContentAgreement::Agree) == (self.content == other.content),
    )]
    #[inline]
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement
    {
        if self.content == other.content {
            ContentAgreement::Agree
        }
        else {
            ContentAgreement::Differ
        }
    }
}

/// The identity of `content`, unless it is opaque.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the content beside the first sixteen bytes of the BLAKE3 digest
///   of its canonical bytes, computed without buffering them.
/// - provides: `recall::Absent::Opaque` for content holding an unresolved node,
///   which has no canonical bytes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — noisy independent programs have identical bytes and
///   addresses; opaque content is refused reuse. The attribute checks input
///   correspondence and the opaque rejection, not a second serialization or
///   hash computation.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `tests::incremental::an_opaque_footprint_is_never_adopted`
#[spec(
    ensures: |ret| match ret {
        | Maybe::Present(ref identity) => {
            core::ptr::eq(&raw const *identity.content, &raw const *content)
                && content.opacity() == Opacity::Transparent
        },
        | Maybe::Absent(reason) => reason == recall::Absent::Opaque,
    },
)]
fn identity_of(content: &ItemContent) -> Maybe<ItemIdentity<'_>, recall::Absent>
{
    let mut hasher = blake3::Hasher::new();
    if write_item_content(&mut hasher, content).is_err() {
        return Maybe::Absent(recall::Absent::Opaque);
    }
    let [
        h0,
        h1,
        h2,
        h3,
        h4,
        h5,
        h6,
        h7,
        l0,
        l1,
        l2,
        l3,
        l4,
        l5,
        l6,
        l7,
        ..,
    ] = *hasher.finalize().as_bytes();
    Maybe::Present(ItemIdentity {
        content,
        digest: ContentDigest::new(
            DigestWord::from(u64::from_le_bytes([h0, h1, h2, h3, h4, h5, h6, h7])),
            DigestWord::from(u64::from_le_bytes([l0, l1, l2, l3, l4, l5, l6, l7])),
        ),
    })
}

/// A choice of memo for the pass: the type parameter that separates batch
/// from incremental.
///
/// # Specification
/// - executable: none — associated memo implementations determine observation
///   and storage; this trait has no transition body.
///
/// # Adequacy
/// - hypothesis: L2 — batch and ordered choices are compared against fresh
///   checking over the generated finite edit domain.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
trait MemoChoice
{
    /// The memo over identities of one lifetime.
    type Memo<'id>: CheckMemo<ItemIdentity<'id>, ItemOrdinal>;

    /// The memo holding `base`'s checkpoints, by identity.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a memo the pass may recall `base`'s items from.
    /// - panics: none.
    /// - executable: none — this required trait declaration has no body; each
    ///   concrete builder specifies its observable result.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the differential suite exercises both concrete memo
    ///   choices, not an arbitrary implementation of this private strategy
    ///   trait.
    /// - witness: `tests::incremental::incremental_equals_from_scratch`
    fn build(base: &Checkpoints) -> Self::Memo<'_>;
}

/// The batch choice: a memo that recalls nothing.
///
/// # Specification
/// trivial.
enum NullMemoChoice {}

impl MemoChoice for NullMemoChoice
{
    type Memo<'id> = NullMemo;

    /// The null memo.
    ///
    /// # Specification
    /// trivial.
    fn build(_base: &Checkpoints) -> NullMemo
    {
        NullMemo
    }
}

/// The incremental choice: an ordered memo over the base's identities.
///
/// # Specification
/// trivial.
enum OrderedMemoChoice {}

impl MemoChoice for OrderedMemoChoice
{
    type Memo<'id> = OrderedMemo<ItemIdentity<'id>, ItemOrdinal>;

    /// Every transparent base item, under its identity.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the memo answers each transparent base item's content with
    ///   its ordinal; of two items of equal content, the later one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — no-op and body-edit cases demonstrate actual reuse.
    ///   The attribute checks bounded single-plane accounting; capacity
    ///   exhaustion and adversarial duplicate restored identities are not
    ///   claimed as witnessed here.
    /// - witness: `tests::incremental::noop_edit_adopts_everything`
    /// - witness: `tests::incremental::body_edit_adopts_the_type_stable_dependent`
    #[spec(
        ensures: |ret| {
            usize::from(ret.entry_count()) <= base.items.len()
                && ret.plane_entry_count(ItemPlane::Items) == ret.entry_count()
        },
    )]
    fn build(base: &Checkpoints) -> OrderedMemo<ItemIdentity<'_>, ItemOrdinal>
    {
        let mut memo = OrderedMemo::new();
        for (index, checkpoint) in base.items.iter().enumerate() {
            if let Maybe::Present(identity) = identity_of(&checkpoint.content)
                && memo.remember(identity, ItemOrdinal::from(index)).is_err()
            {
                // economy: a memo whose accounting is at its ceiling records
                // nothing more; later items are judged, which costs reuse only.
                break;
            }
        }
        memo
    }
}

/// One item's outcome of the pass.
///
/// # Specification
/// - executable: none — an outcome alone lacks the preceding context that would
///   justify its adoption or judgement.
///
/// # Adequacy
/// - hypothesis: L3 — no-op reuse and type-change invalidation separate the two
///   outcome paths by exact marks and independent fresh typings.
/// - witness: `tests::incremental::noop_edit_adopts_everything`
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
struct Outcome
{
    /// The item's footprint.
    footprint: Footprint,
    /// The answers its judgement consulted, or its adopted checkpoint's.
    support: Vec<Answered>,
    /// Its typing.
    typing: Typing,
    /// Whether it was adopted.
    adoption: Adoption,
}

/// A base checkpoint recalled for an edited item, with its minted seat.
///
/// # Specification
/// - executable: none — the candidate does not carry the edited arena needed to
///   certify its optional seat.
///
/// # Adequacy
/// - hypothesis: L2 — unchanged items reuse their types; opaque content is not
///   adopted. Type-content minting supplies its own bounded seat evidence.
/// - witness: `tests::incremental::noop_edit_adopts_everything`
/// - witness: `tests::incremental::an_opaque_footprint_is_never_adopted`
struct Candidate<'base>
{
    /// The recalled checkpoint.
    checkpoint: &'base ItemCheckpoint,
    /// The seat minted for an unsigned item's synthesised type.
    seat: Maybe<ValueTypeId, seating::Absent>,
}

/// Increment a census count.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the prior count plus one, saturating at `usize::MAX`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, the last representable increment and the saturated
///   boundary distinguish increment from wraparound or premature saturation.
/// - witness: `checkpoint::tests::census_increment_saturates_at_the_boundary`
#[spec(
    captures: [before = usize::from(*count)],
    ensures: usize::from(*count) == before.saturating_add(1),
)]
fn bump(count: &mut ItemCount)
{
    *count = ItemCount::from(usize::from(*count).saturating_add(1));
}

/// Whether a recalled checkpoint still answers.
///
/// # Specification
/// - executable: none — a decision tag has no input support or changed-value
///   set to certify the decision.
///
/// # Adequacy
/// - hypothesis: L2 — type-change and nested recorded-answer cases separate
///   standing support from invalidated support through their guard consumers.
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
/// - witness: `checkpoint::tests::recorded_answer_references_participate_in_value_invalidation`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// It does.
    Stands,
    /// It does not; the item is judged.
    Falls,
}

/// Run the pass from `base` over `edited`, splice the order, and assemble the
/// resume.
///
/// # Specification
/// - requires: `base_handles` are `order`'s handles, one per item of `base`, in
///   order.
/// - ensures: as [`resume`] at the memo `Choice` builds.
/// - fails: [`ResumeError::Order`] when the splice fails.
/// - panics: none.
/// - intension: encodes each edited item once, recalls each at most once,
///   closes the value-changed set over each read edge at most once, and judges
///   or adopts each item once.
///
/// # Adequacy
/// - hypothesis: L2 — generated edits and a revision-handle chain compare the
///   assembled result with fresh checking and check identity retention. The
///   predicate checks input identity correspondence and output census shape.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `checkpoint::tests::revision_handles_track_insertions_and_deletions`
#[spec(
    requires: base_handles.len() == base.items.len()
        && base_handles.iter().zip(&base.items).all(|(&handle, item)| {
            order.reference(handle) == Maybe::Present(item.content.reference())
        }),
    ensures: |ret| {
        ret.as_ref().is_ok_and(|resumed| {
            resumed.checkpoints.budget == base.budget
                && resumed.checkpoints.items.len() == edited.items().len()
                && resumed.adoptions.len() == edited.items().len()
                && resumed.handles.len() == edited.items().len()
                && usize::from(resumed.census.items) == edited.items().len()
                && usize::from(resumed.census.adopted)
                    .checked_add(usize::from(resumed.census.judged))
                    == Some(edited.items().len())
                && resumed
                    .checkpoints
                    .items
                    .iter()
                    .map(|item| item.content.reference())
                    .eq(edited.references().iter())
        }) || ret.is_err()
    },
)]
fn advance<Choice>(
    base: &Checkpoints,
    mut order: ItemOrder,
    base_handles: &[ItemHandle],
    edited: &mut Program,
) -> Result<Resume, ResumeError>
where
    Choice: MemoChoice,
{
    let budget = base.budget;
    let mut census = ResumeCensus::default();
    let encoded: Vec<Encoded> = (0 .. edited.layout().items.len())
        .map(|index| encode_item(edited.arena(), edited.layout(), ItemOrdinal::from(index)))
        .collect();
    census.items = ItemCount::from(encoded.len());
    let outcomes = {
        let memo = Choice::build(base);
        pass::<Choice::Memo<'_>>(base, &memo, &encoded, edited, budget, &mut census)
    };
    let mut items = Vec::with_capacity(encoded.len());
    let mut adoptions = Vec::with_capacity(encoded.len());
    for (encoded, outcome) in encoded.into_iter().zip(outcomes) {
        adoptions.push(outcome.adoption);
        items.push(ItemCheckpoint {
            content: encoded.content,
            footprint: outcome.footprint,
            support: outcome.support,
            typing: outcome.typing,
        });
    }
    let base_references: Vec<&Reference> = base
        .items
        .iter()
        .map(|checkpoint| checkpoint.content.reference())
        .collect();
    let (handles, splice) = order
        .splice(base_handles, &base_references, edited.references())
        .map_err(ResumeError::Order)?;
    census.splice = splice;
    Ok(Resume {
        checkpoints: Checkpoints::new(budget, items),
        adoptions,
        handles,
        order,
        census,
    })
}

/// The forward pass: recall, seat, close, then adopt or judge each item in
/// order.
///
/// # Specification
/// - requires: `encoded` holds `edited`'s items' encodings, in order.
/// - ensures: one outcome per item, in order; an item is adopted only when its
///   recalled checkpoint's support holds pointwise against the answers of the
///   items already passed, no type position of it or of a recorded answer names
///   a value-changed definition, and its type can be seated; every other item
///   is judged in a context that has admitted exactly the items before it, as
///   batch does.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the differential suite compares the pass against the
///   checker's batch entry over generated programs and edit chains; L3 for the
///   teeth, where a corrupted typing, a corrupted support and a corrupted
///   footprint each show what the pass does and does not read.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::a_suppressed_invalidation_signal_is_caught`
/// - witness: `tests::incremental::a_stored_footprint_is_not_an_adoption_input`
/// - witness: `tests::incremental::an_opaque_footprint_is_never_adopted`
#[spec(
    requires: encoded.len() == edited.items().len()
        && encoded
            .iter()
            .map(|item| item.content.reference())
            .eq(edited.references().iter()),
    captures: [
        adopted = usize::from(census.adopted),
        judged = usize::from(census.judged),
        recalled = usize::from(census.recalled),
    ],
    ensures: |ret| {
        ret.len() == encoded.len()
            && usize::from(census.adopted)
                == adopted.saturating_add(
                    ret.iter()
                        .filter(|outcome| outcome.adoption == Adoption::Adopted)
                        .count(),
                )
            && usize::from(census.judged)
                == judged.saturating_add(
                    ret.iter()
                        .filter(|outcome| outcome.adoption == Adoption::Judged)
                        .count(),
                )
            && usize::from(census.recalled)
                == recalled.saturating_add(if Memo::ACTIVITY == MemoActivity::Active {
                    encoded.len()
                }
                else {
                    0
                })
            && ret.iter().zip(encoded).all(|(outcome, item)| {
                outcome.footprint.opacity() == item.content.opacity()
                    && outcome.support.windows(2).all(|pair| {
                        pair.first()
                            .zip(pair.last())
                            .is_none_or(|(left, right)| left.reference < right.reference)
                    })
            })
    },
)]
fn pass<'id, Memo>(
    base: &'id Checkpoints,
    memo: &Memo,
    encoded: &'id [Encoded],
    edited: &mut Program,
    budget: CheckBudget,
    census: &mut ResumeCensus,
) -> Vec<Outcome>
where
    Memo: CheckMemo<ItemIdentity<'id>, ItemOrdinal>,
{
    let active = Memo::ACTIVITY == MemoActivity::Active;
    let footprints: Vec<Footprint> = encoded
        .iter()
        .map(|item| footprint_of(&item.content))
        .collect();
    let mut candidates: Vec<Maybe<Candidate<'id>, recall::Absent>> =
        Vec::with_capacity(encoded.len());
    let mut value_changed = BTreeSet::new();
    if active {
        for item in encoded {
            bump(&mut census.recalled);
            let candidate = match identity_of(&item.content) {
                | Maybe::Present(identity) => match memo.recall(&identity) {
                    | Some(hit) => match base.items.get(usize::from(*hit.outcome())) {
                        | Some(checkpoint) => Maybe::Present(Candidate {
                            checkpoint,
                            seat: {
                                let (arena, layout) = edited.parts_mut();
                                seat_of(checkpoint, item, arena, layout, census)
                            },
                        }),
                        | None => Maybe::Absent(recall::Absent::Missed),
                    },
                    | None => Maybe::Absent(recall::Absent::Missed),
                },
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            };
            candidates.push(candidate);
        }
        value_changed = close_value_changes(base, encoded, &footprints, census);
    }
    let mut outcomes = Vec::with_capacity(encoded.len());
    let mut supplied: Vec<Answer> = Vec::with_capacity(encoded.len());
    let (arena, layout) = edited.parts_mut();
    let mut context = CheckingContext::new(arena, budget);
    for (index, (item, footprint)) in encoded.iter().zip(footprints).enumerate() {
        let ordinal = ItemOrdinal::from(index);
        let Some(declaration) = layout.items.get(index).map(|item| *item.declaration())
        else {
            break;
        };
        let adopted = match candidates.get(index) {
            | Some(&Maybe::Present(ref candidate)) => adopt(&mut context, &AdoptionInput {
                candidate,
                item,
                footprint: &footprint,
                declaration,
                layout,
                supplied: &supplied,
                ordinal,
                value_changed: &value_changed,
            }),
            | Some(&Maybe::Absent(_)) | None => Maybe::Absent(recall::Absent::Missed),
        };
        let (outcome, answer) = match adopted {
            | Maybe::Present((support, typing, answer)) => {
                bump(&mut census.adopted);
                (
                    Outcome {
                        footprint,
                        support,
                        typing,
                        adoption: Adoption::Adopted,
                    },
                    answer,
                )
            },
            | Maybe::Absent(reason) => {
                match reason {
                    | recall::Absent::Outdated => bump(&mut census.outdated),
                    | recall::Absent::ValueRead => bump(&mut census.value_reads),
                    | recall::Absent::Opaque
                    | recall::Absent::Missed
                    | recall::Absent::Unseated => {},
                }
                bump(&mut census.judged);
                let supported = check_declaration_supported(&mut context, &declaration);
                let arena = context.arena();
                let projection = Projection {
                    arena,
                    layout,
                    sites: &item.sites,
                };
                let typing = projection.typing(&supported.verdict());
                let support = answered(supported.support(), arena, layout);
                let answer = answer_of(context.signature(declaration.constant()), arena, layout);
                (
                    Outcome {
                        footprint,
                        support,
                        typing,
                        adoption: Adoption::Judged,
                    },
                    answer,
                )
            },
        };
        outcomes.push(outcome);
        supplied.push(answer);
    }
    outcomes
}

/// Mint the seat an unsigned item's adopted synthesised type is read from.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for an unsigned item whose recalled typing synthesised a type,
///   that type minted into `arena`; nothing for any other item.
/// - provides: `seating::Absent` naming why no seat was minted.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — no-op reuse exercises synthesised seats; an ascribed edit
///   exercises the non-minting branch. The counter counts attempts, including
///   named failures, rather than only successfully allocated seats.
/// - witness: `tests::incremental::noop_edit_adopts_everything`
/// - witness: `tests::incremental::satisfied_ascription_types_and_keeps_dependents_adoptable`
#[spec(
    captures: [before = usize::from(census.minted)],
    ensures: |ret| {
        if matches!(
            (item.content.signature(), &checkpoint.typing),
            (Maybe::Absent(_), &Typing::Synthesised { .. })
        ) {
            usize::from(census.minted) == before.saturating_add(1)
                && match ret {
                    | Maybe::Present(id) => arena.value_type(id).is_some(),
                    | Maybe::Absent(_) => true,
                }
        }
        else {
            usize::from(census.minted) == before
                && ret == Maybe::Absent(seating::Absent::Unseatable)
        }
    },
)]
fn seat_of(
    checkpoint: &ItemCheckpoint,
    item: &Encoded,
    arena: &mut CoreArena,
    layout: &Layout,
    census: &mut ResumeCensus,
) -> Maybe<ValueTypeId, seating::Absent>
{
    match (item.content.signature(), &checkpoint.typing) {
        | (Maybe::Absent(_), &Typing::Synthesised { ref produced, .. }) => {
            bump(&mut census.minted);
            produced.mint(arena, layout)
        },
        | _ => Maybe::Absent(seating::Absent::Unseatable),
    }
}

/// What one adoption decision reads.
///
/// # Specification
/// - executable: none — borrowed inputs cannot attest that supplied answers
///   were produced by preceding judgements.
///
/// # Adequacy
/// - hypothesis: L3 — independent differential checks validate reuse; the
///   constructed recorded-answer case isolates value invalidation without
///   asserting provenance.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `checkpoint::tests::recorded_answer_references_participate_in_value_invalidation`
struct AdoptionInput<'input, 'base>
{
    /// The recalled checkpoint and its seat.
    candidate: &'input Candidate<'base>,
    /// The edited item's encoding.
    item: &'input Encoded,
    /// The edited item's footprint.
    footprint: &'input Footprint,
    /// The edited item's declaration.
    declaration: gandr_core_checker::Declaration,
    /// The edited program.
    layout: &'input Layout,
    /// The answers of the items passed so far.
    supplied: &'input [Answer],
    /// The item's ordinal.
    ordinal: ItemOrdinal,
    /// The closed value-changed set.
    value_changed: &'input BTreeSet<Reference>,
}

/// Adopt the recalled checkpoint when it still answers.
///
/// # Specification
/// - requires: `input.supplied` holds the answer of every item before
///   `input.ordinal`.
/// - ensures: when the item is transparent, the support holds pointwise, no
///   type position meets the value-changed set and the type seats, the item is
///   admitted with its seated type and the checkpoint's support, typing and
///   answer are returned; otherwise the context is unchanged.
/// - provides: the reason the checkpoint does not answer: `Opaque`, `Outdated`,
///   `ValueRead` or `Unseated`, checked in that order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — changed support, an ascription reading a changed value
///   and opaque content separate three guards. Generated edits exercise
///   successful seating; this is not exhaustive evidence of refusal precedence
///   or context preservation on every formation error.
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
/// - witness: `tests::incremental::an_ascription_endpoint_is_a_read`
/// - witness: `tests::incremental::a_changed_value_reaches_through_an_untouched_definition`
/// - witness: `tests::incremental::an_opaque_footprint_is_never_adopted`
#[spec(
    requires: input.supplied.len() == usize::from(input.ordinal),
    ensures: |ret| {
        let transparent = input.item.content.opacity() == Opacity::Transparent;
        let supported =
            support_holds(input, &input.candidate.checkpoint.support) == Standing::Stands;
        let untouched = touches(input, &input.candidate.checkpoint.support) == Standing::Stands;
        match ret {
            | Maybe::Present((ref support, ref typing, _)) => {
                transparent
                    && supported
                    && untouched
                    && support == &input.candidate.checkpoint.support
                    && typing == &input.candidate.checkpoint.typing
            },
            | Maybe::Absent(reason) => {
                reason
                    == if !transparent {
                        recall::Absent::Opaque
                    }
                    else if !supported {
                        recall::Absent::Outdated
                    }
                    else if !untouched {
                        recall::Absent::ValueRead
                    }
                    else {
                        recall::Absent::Unseated
                    }
            },
        }
    },
)]
fn adopt(
    context: &mut CheckingContext<'_>,
    input: &AdoptionInput<'_, '_>,
) -> Maybe<(Vec<Answered>, Typing, Answer), recall::Absent>
{
    let checkpoint = input.candidate.checkpoint;
    if input.item.content.opacity() == Opacity::Opaque {
        return Maybe::Absent(recall::Absent::Opaque);
    }
    if support_holds(input, &checkpoint.support) == Standing::Falls {
        return Maybe::Absent(recall::Absent::Outdated);
    }
    if touches(input, &checkpoint.support) == Standing::Falls {
        return Maybe::Absent(recall::Absent::ValueRead);
    }
    let seat: Maybe<FormedValueType, signature_table::Absent>;
    let answer: Answer;
    match (input.declaration.signature(), &checkpoint.typing) {
        | (Maybe::Present(signature), _) => match form_value_type(context, signature) {
            | Ok(formed) => {
                seat = Maybe::Present(formed);
                answer = match input.item.content.signature_type() {
                    | Maybe::Present(ty) => Answer::Typed(ty),
                    | Maybe::Absent(_) => Answer::Untyped,
                };
            },
            | Err(_) => {
                seat = Maybe::Absent(signature_table::Absent::Untyped);
                answer = Answer::Untyped;
            },
        },
        | (Maybe::Absent(_), &Typing::Synthesised { ref produced, .. }) => {
            let Maybe::Present(minted) = input.candidate.seat
            else {
                return Maybe::Absent(recall::Absent::Unseated);
            };
            let Ok(formed) = form_value_type(context, minted)
            else {
                return Maybe::Absent(recall::Absent::Unseated);
            };
            seat = Maybe::Present(formed);
            answer = Answer::Typed(produced.clone());
        },
        | (Maybe::Absent(_), &(Typing::Checked { .. } | Typing::Owed | Typing::Refused(_))) => {
            seat = Maybe::Absent(signature_table::Absent::Untyped);
            answer = Answer::Untyped;
        },
    }
    let unfolds = match (&checkpoint.typing, input.declaration.body()) {
        | (&(Typing::Checked { .. } | Typing::Synthesised { .. }), Maybe::Present(body)) => {
            Maybe::Present(body)
        },
        | (_, Maybe::Absent(_)) | (&(Typing::Owed | Typing::Refused(_)), Maybe::Present(_)) => {
            Maybe::Absent(unfolding::Absent::Rigid)
        },
    };
    if context
        .adopt(input.declaration.constant(), seat, unfolds)
        .is_err()
    {
        return Maybe::Absent(recall::Absent::Unseated);
    }
    Maybe::Present((
        checkpoint.support.clone(),
        checkpoint.typing.clone(),
        answer,
    ))
}

/// Whether every recorded answer equals the answer the edited table gives.
///
/// # Specification
/// - requires: as [`adopt`].
/// - ensures: `Stands` exactly when, for each recorded answer, the item its
///   reference names in the edited program precedes this one and supplied an
///   equal answer, or no such item precedes it and the recorded answer is
///   `Untyped`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — type changes invalidate recorded answers while unchanged
///   types preserve body-edit reuse. The predicate reads preceding source
///   references and answers directly rather than the layout lookup map.
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
/// - witness: `tests::incremental::body_edit_adopts_the_type_stable_dependent`
#[spec(
    requires: input.supplied.len() == usize::from(input.ordinal),
    ensures: |ret| {
        (ret == Standing::Stands)
            == support.iter().all(|answered| {
                input
                    .layout
                    .references
                    .iter()
                    .take(usize::from(input.ordinal))
                    .zip(input.supplied)
                    .find(|&(reference, _)| *reference == answered.reference)
                    .map_or_else(
                        || answered.answer == Answer::Untyped,
                        |(_, current)| *current == answered.answer,
                    )
            })
    },
)]
fn support_holds(
    input: &AdoptionInput<'_, '_>,
    support: &[Answered],
) -> Standing
{
    let holds = support.iter().all(|answered| {
        let current = match input.layout.ordinal_of(&answered.reference) {
            | Maybe::Present(ordinal) if ordinal < input.ordinal => {
                input.supplied.get(usize::from(ordinal))
            },
            | Maybe::Present(_) | Maybe::Absent(_) => None,
        };
        match current {
            | Some(current) => *current == answered.answer,
            | None => answered.answer == Answer::Untyped,
        }
    });
    if holds {
        Standing::Stands
    }
    else {
        Standing::Falls
    }
}

/// Whether a type position of the item, or of a recorded answer's type,
/// names a value-changed definition.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Falls` exactly when a footprint type read or a reference inside
///   a typed recorded answer belongs to the changed-value set.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an ascription supplies a footprint type read; constructed
///   recorded answers separately contain abstract and code references. An
///   unrelated changed value and an untyped answer do not invalidate the guard.
/// - witness: `tests::incremental::a_type_stable_body_edit_reaches_a_type_position`
/// - witness: `checkpoint::tests::recorded_answer_references_participate_in_value_invalidation`
#[spec(
    ensures: |ret| {
        (ret == Standing::Falls)
            == (input
                .footprint
                .type_reads()
                .any(|reference| input.value_changed.contains(reference))
                || support.iter().any(|answered| match answered.answer {
                    | Answer::Typed(ref ty) => ty.nodes().iter().any(|node| match *node {
                        | crate::content::ContentNode::Constant(ref reference)
                        | crate::content::ContentNode::Abstract(ref reference) => {
                            input.value_changed.contains(reference)
                        },
                        | _ => false,
                    }),
                    | Answer::Untyped => false,
                }))
    },
)]
fn touches(
    input: &AdoptionInput<'_, '_>,
    support: &[Answered],
) -> Standing
{
    let changed = |reference: &Reference| input.value_changed.contains(reference);
    let touched = input.footprint.type_reads().any(changed)
        || support.iter().any(|answered| match answered.answer {
            | Answer::Typed(ref ty) => ty.references().any(changed),
            | Answer::Untyped => false,
        });
    if touched {
        Standing::Falls
    }
    else {
        Standing::Stands
    }
}

/// The support of a judgement, by reference, ascending, each once.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each consulted position's reference beside its answer's content,
///   ascending by reference; the unoccupied positions collapse into one entry,
///   all of whose answers are `Untyped`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — independent fresh judgements validate adopted support in
///   the differential suite; a dangling reader supplies an untyped answer. The
///   predicate bounds cardinality and canonical order, not a repeated
///   judgement.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::uncoordinated_rename_leaves_a_dangling_reader`
#[spec(
    ensures: |ret| {
        ret.len() <= support.consulted().len()
            && ret.windows(2).all(|pair| {
                pair.first()
                    .zip(pair.last())
                    .is_none_or(|(left, right)| left.reference < right.reference)
            })
    },
)]
fn answered(
    support: &Support,
    arena: &CoreArena,
    layout: &Layout,
) -> Vec<Answered>
{
    let answers: Vec<Answered> = support
        .consulted()
        .iter()
        .map(|consulted| Answered {
            reference: layout.resolve(consulted.constant()),
            answer: answer_of(consulted.answer(), arena, layout),
        })
        .collect();
    canonical_support(answers)
}

/// `support` ascending by reference, each reference once.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the entries sorted stably by reference, of each run of equal
///   references the first kept.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty support and unsorted conflicting duplicates
///   distinguish canonical order and first-answer retention. Reversing the
///   input changes the retained answers rather than preserving the previous
///   checkpoint support.
/// - witness: `checkpoint::tests::support_canonicalization_keeps_the_first_answer`
#[spec(
    captures: [count = support.len()],
    ensures: |ret| {
        ret.len() <= count
            && ret.windows(2).all(|pair| {
                pair.first()
                    .zip(pair.last())
                    .is_none_or(|(left, right)| left.reference < right.reference)
            })
    },
)]
fn canonical_support(mut support: Vec<Answered>) -> Vec<Answered>
{
    support.sort_by(|left, right| left.reference.cmp(&right.reference));
    support.dedup_by(|later, earlier| later.reference == earlier.reference);
    support
}

/// The content of a table answer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a present formed seat is represented as type content; an absent
///   seat is `Untyped`. Unresolved identifiers retain their value-type sort.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated finite programs and a dangling reader exercise
///   typed and untyped answers against independently checked results.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::uncoordinated_rename_leaves_a_dangling_reader`
#[spec(
    captures: [present = matches!(answer, Maybe::Present(_))],
    ensures: |ret| match ret {
        | Answer::Typed(ref ty) => {
            present
                && ty
                    .nodes()
                    .first()
                    .is_some_and(|node| node.sort() == crate::content::Sort::ValueType)
        },
        | Answer::Untyped => !present,
    },
)]
fn answer_of(
    answer: Maybe<FormedValueType, signature_table::Absent>,
    arena: &CoreArena,
    layout: &Layout,
) -> Answer
{
    match answer {
        | Maybe::Present(formed) => Answer::Typed(TypeContent::of(
            arena,
            layout,
            ArenaNode::ValueType(formed.id()),
        )),
        | Maybe::Absent(_) => Answer::Untyped,
    }
}

/// The value-changed set: the definitions inserted, deleted or changed, closed
/// over their readers.
///
/// # Specification
/// - requires: `footprints` are `encoded`'s, in order.
/// - ensures: the least set holding every reference whose item is in only one
///   of the two programs or whose content differs between them, and every
///   edited item reading a member; once the set is non-empty, every opaque
///   edited item and its readers.
/// - panics: none.
/// - intension: builds the reverse read map once and crosses each of its edges
///   at most once, so the closure is linear in the reads up to the maps'
///   logarithm.
///
/// # Adequacy
/// - hypothesis: L3 — transitive readers and a bystander separate closure
///   membership; a cycle terminates with exact edge counts. Opaque content
///   seeds no change by itself, but joins with its reader once another item
///   changes. A finite growing-size family checks linear accounting.
/// - witness: `tests::incremental::a_changed_value_reaches_through_an_untouched_definition`
/// - witness: `tests::defects::items_visited_for_a_head_edit_grow_linearly`
/// - witness: `checkpoint::tests::value_change_closure_handles_cycles_and_opaque_readers`
#[spec(
    requires: footprints.len() == encoded.len(),
    ensures: |ret| {
        usize::from(census.value_changed) == ret.len()
            && usize::from(census.seeds) <= ret.len()
            && encoded.iter().zip(footprints).all(|(item, footprint)| {
                ret.contains(item.content.reference())
                    || ((ret.is_empty() || footprint.opacity() == Opacity::Transparent)
                        && !footprint.reads().any(|reference| ret.contains(reference)))
            })
    },
)]
fn close_value_changes(
    base: &Checkpoints,
    encoded: &[Encoded],
    footprints: &[Footprint],
    census: &mut ResumeCensus,
) -> BTreeSet<Reference>
{
    let before: BTreeMap<&Reference, &ItemContent> = base
        .items
        .iter()
        .map(|checkpoint| (checkpoint.content.reference(), &checkpoint.content))
        .collect();
    let mut changed: BTreeSet<Reference> = BTreeSet::new();
    let mut worklist: Vec<Reference> = Vec::new();
    let seed = |reference: &Reference,
                changed: &mut BTreeSet<Reference>,
                worklist: &mut Vec<Reference>| {
        if changed.insert(reference.clone()) {
            worklist.push(reference.clone());
        }
    };
    let mut after: BTreeSet<&Reference> = BTreeSet::new();
    for item in encoded {
        let reference = item.content.reference();
        let _fresh = after.insert(reference);
        let same = before
            .get(reference)
            .is_some_and(|content| **content == item.content);
        if !same {
            seed(reference, &mut changed, &mut worklist);
        }
    }
    for reference in before.keys() {
        if !after.contains(*reference) {
            seed(reference, &mut changed, &mut worklist);
        }
    }
    census.seeds = ItemCount::from(changed.len());
    let mut readers: BTreeMap<&Reference, Vec<&Reference>> = BTreeMap::new();
    let mut opaque: Vec<&Reference> = Vec::new();
    for (item, footprint) in encoded.iter().zip(footprints) {
        if footprint.opacity() == Opacity::Opaque {
            opaque.push(item.content.reference());
        }
        for read in footprint.reads() {
            readers
                .entry(read)
                .or_default()
                .push(item.content.reference());
        }
    }
    if !changed.is_empty() {
        for reference in opaque {
            seed(reference, &mut changed, &mut worklist);
        }
    }
    while let Some(reference) = worklist.pop() {
        if let Some(edges) = readers.get(&reference) {
            for &reader in edges {
                bump(&mut census.closure_edges);
                seed(reader, &mut changed, &mut worklist);
            }
        }
    }
    census.value_changed = ItemCount::from(changed.len());
    changed
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::vec;

    use gandr_core_checker::Declaration;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::body;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use quenchant_shape::shape::Maybe;

    use super::AdoptionInput;
    use super::Answer;
    use super::Answered;
    use super::Candidate;
    use super::ItemCheckpoint;
    use super::Standing;
    use super::touches;
    use crate::boundary::ItemOrdinal;
    use crate::boundary::NodeIndex;
    use crate::boundary::Occurrence;
    use crate::content::ContentNode;
    use crate::content::TypeContent;
    use crate::content::encode_item;
    use crate::content::seating;
    use crate::footprint::footprint_of;
    use crate::region::Item;
    use crate::region::ItemKey;
    use crate::region::Program;
    use crate::region::Reference;
    use crate::typing::Typing;

    #[test]
    fn recorded_answer_references_participate_in_value_invalidation()
    {
        let declaration = Declaration::new(
            ConstantIndex::from(1_usize),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
            OriginToken::from(1_usize),
        );
        let program = Program::new(CoreArena::new(), vec![Item::new(
            ItemKey::from("target"),
            declaration,
        )])
        .expect("one position");
        let item = encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        );
        let footprint = footprint_of(&item.content);
        assert_eq!(footprint.type_reads().count(), 0_usize);
        let abstract_name = Reference::Item {
            key: ItemKey::from("abstract"),
            occurrence: Occurrence::from(0_usize),
        };
        let code_name = Reference::Item {
            key: ItemKey::from("code"),
            occurrence: Occurrence::from(0_usize),
        };
        let table = TypeContent::from_nodes(vec![
            ContentNode::Product(NodeIndex::from(1_usize), NodeIndex::from(2_usize)),
            ContentNode::Abstract(abstract_name.clone()),
            ContentNode::Element {
                code: NodeIndex::from(3_usize),
                target: Level::zero(),
            },
            ContentNode::Constant(code_name.clone()),
        ]);
        let checkpoint = ItemCheckpoint::new(
            item.content.clone(),
            footprint.clone(),
            vec![Answered::new(Reference::Unoccupied, Answer::Typed(table))],
            Typing::Owed,
        );
        let candidate = Candidate {
            checkpoint: &checkpoint,
            seat: Maybe::Absent(seating::Absent::Unseatable),
        };
        let unrelated = Reference::Item {
            key: ItemKey::from("unrelated"),
            occurrence: Occurrence::from(0_usize),
        };
        let untyped = [Answered::new(Reference::Unoccupied, Answer::Untyped)];
        for (name, support, expected) in [
            (&unrelated, checkpoint.support.as_slice(), Standing::Stands),
            (
                &abstract_name,
                checkpoint.support.as_slice(),
                Standing::Falls,
            ),
            (&code_name, checkpoint.support.as_slice(), Standing::Falls),
            (&abstract_name, untyped.as_slice(), Standing::Stands),
        ] {
            let value_changed = BTreeSet::from([name.clone()]);
            let input = AdoptionInput {
                candidate: &candidate,
                item: &item,
                footprint: &footprint,
                declaration,
                layout: program.layout(),
                supplied: &[],
                ordinal: ItemOrdinal::from(0_usize),
                value_changed: &value_changed,
            };
            assert_eq!(touches(&input, support), expected);
        }
    }

    #[test]
    fn census_increment_saturates_at_the_boundary()
    {
        for (before, expected) in [
            (0_usize, 1_usize),
            (usize::MAX.saturating_sub(1), usize::MAX),
            (usize::MAX, usize::MAX),
        ] {
            let mut count = crate::boundary::ItemCount::from(before);
            super::bump(&mut count);
            assert_eq!(usize::from(count), expected);
        }
    }

    #[test]
    fn support_canonicalization_keeps_the_first_answer()
    {
        let a = Reference::Item {
            key: ItemKey::from("a"),
            occurrence: Occurrence::from(0_usize),
        };
        let b = Reference::Item {
            key: ItemKey::from("b"),
            occurrence: Occurrence::from(0_usize),
        };
        let typed = Answer::Typed(TypeContent::from_nodes(vec![ContentNode::UnitType]));
        let mut support = vec![
            Answered::new(b.clone(), Answer::Untyped),
            Answered::new(a.clone(), typed.clone()),
            Answered::new(b.clone(), typed.clone()),
            Answered::new(a.clone(), Answer::Untyped),
        ];
        let program = crate::fixture::integers(CoreArena::new(), &[(
            crate::fixture::Key("owner"),
            crate::fixture::Digits("1"),
        )]);
        let item = encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        );
        let footprint = footprint_of(&item.content);
        let checkpoint =
            ItemCheckpoint::new(item.content, footprint, support.clone(), Typing::Owed);
        assert_eq!(checkpoint.support(), [
            Answered::new(a.clone(), typed.clone()),
            Answered::new(b.clone(), Answer::Untyped)
        ]);
        support.reverse();
        let checkpoint = checkpoint.with_support(support);
        assert_eq!(checkpoint.support(), [
            Answered::new(a, Answer::Untyped),
            Answered::new(b, typed)
        ]);
        assert_eq!(super::canonical_support(vec![]), vec![]);
    }

    #[test]
    fn revision_handles_track_insertions_and_deletions()
    {
        let empty = super::Resume::from_checkpoints(super::Checkpoints::new(
            gandr_core_checker::CheckBudget::DEFAULT,
            vec![],
        ))
        .expect("an empty restored revision");
        let mut original_program = crate::fixture::integers(CoreArena::new(), &[
            (crate::fixture::Key("a"), crate::fixture::Digits("1")),
            (crate::fixture::Key("c"), crate::fixture::Digits("3")),
        ]);
        let original = super::resume(empty, &mut original_program).expect("initial insertion");
        let foreign = *original.handles().first().expect("two items");
        let restored = super::Resume::from_checkpoints(original.checkpoints().clone())
            .expect("restored two-item revision");
        assert_eq!(
            restored.reference(foreign),
            Maybe::Absent(crate::order::handle::Absent::Stale)
        );
        let &[a, c] = restored.handles()
        else {
            panic!("two restored handles");
        };
        let mut inserted_program = crate::fixture::integers(CoreArena::new(), &[
            (crate::fixture::Key("a"), crate::fixture::Digits("1")),
            (crate::fixture::Key("b"), crate::fixture::Digits("2")),
            (crate::fixture::Key("c"), crate::fixture::Digits("3")),
        ]);
        let inserted =
            super::resume(restored, &mut inserted_program).expect("insert the middle item");
        let &[kept_a, b, kept_c] = inserted.handles()
        else {
            panic!("three handles after insertion");
        };
        assert_eq!((kept_a, kept_c), (a, c));
        assert_eq!(
            inserted.compare(a, b),
            Maybe::Present(core::cmp::Ordering::Less)
        );
        assert_eq!(
            inserted.compare(b, c),
            Maybe::Present(core::cmp::Ordering::Less)
        );
        assert_eq!(
            inserted.reference(c),
            Maybe::Present(&Reference::Item {
                key: ItemKey::from("c"),
                occurrence: Occurrence::from(0_usize)
            })
        );
        let mut deleted_program = crate::fixture::integers(CoreArena::new(), &[
            (crate::fixture::Key("a"), crate::fixture::Digits("1")),
            (crate::fixture::Key("b"), crate::fixture::Digits("2")),
        ]);
        let deleted = super::resume(inserted, &mut deleted_program).expect("delete the final item");
        assert_eq!(deleted.handles(), [a, b]);
        assert_eq!(
            deleted.compare(a, c),
            Maybe::Absent(crate::order::handle::Absent::Stale)
        );
        assert_eq!(
            deleted.compare(c, a),
            Maybe::Absent(crate::order::handle::Absent::Stale)
        );
        assert_eq!(
            deleted.reference(c),
            Maybe::Absent(crate::order::handle::Absent::Stale)
        );
        assert_eq!(
            deleted.compare(b, a),
            Maybe::Present(core::cmp::Ordering::Greater)
        );
        assert_eq!(
            deleted.compare(b, b),
            Maybe::Present(core::cmp::Ordering::Equal)
        );
    }

    #[test]
    fn value_change_closure_handles_cycles_and_opaque_readers()
    {
        let mut foreign_arena = CoreArena::new();
        let foreign = core::iter::repeat_with(|| foreign_arena.value_unit())
            .take(5_usize)
            .last()
            .expect("five values");
        let program_for = |signed: bool| {
            let mut arena = CoreArena::new();
            let unit = arena.value_type_unit();
            let bodies = [
                arena.value_constant(ConstantIndex::from(1_usize)),
                arena.value_constant(ConstantIndex::from(0_usize)),
                foreign,
                arena.value_constant(ConstantIndex::from(2_usize)),
                arena.value_unit(),
            ];
            let items = ["a", "b", "opaque", "reader", "bystander"]
                .into_iter()
                .zip(bodies)
                .enumerate()
                .map(|(position, (key, body))| {
                    Item::new(
                        ItemKey::from(key),
                        Declaration::new(
                            ConstantIndex::from(position),
                            if signed && position == 0 {
                                Maybe::Present(unit)
                            }
                            else {
                                Maybe::Absent(signature::Absent::Unsigned)
                            },
                            Maybe::Present(body),
                            OriginToken::from(position),
                        ),
                    )
                })
                .collect();
            Program::new(arena, items).expect("ascending positions")
        };
        let original = program_for(false);
        let before: alloc::vec::Vec<_> = (0 .. original.items().len())
            .map(|index| {
                encode_item(
                    original.arena(),
                    original.layout(),
                    ItemOrdinal::from(index),
                )
            })
            .collect();
        let footprints: alloc::vec::Vec<_> = before
            .iter()
            .map(|item| footprint_of(&item.content))
            .collect();
        let base = super::Checkpoints::new(
            gandr_core_checker::CheckBudget::DEFAULT,
            before
                .iter()
                .zip(&footprints)
                .map(|(item, footprint)| {
                    ItemCheckpoint::new(
                        item.content.clone(),
                        footprint.clone(),
                        vec![],
                        Typing::Owed,
                    )
                })
                .collect(),
        );
        let mut census = super::ResumeCensus::default();
        assert_eq!(
            super::close_value_changes(&base, &before, &footprints, &mut census),
            BTreeSet::new()
        );
        assert_eq!(census, super::ResumeCensus::default());
        let edited = program_for(true);
        let after: alloc::vec::Vec<_> = (0 .. edited.items().len())
            .map(|index| encode_item(edited.arena(), edited.layout(), ItemOrdinal::from(index)))
            .collect();
        let footprints: alloc::vec::Vec<_> = after
            .iter()
            .map(|item| footprint_of(&item.content))
            .collect();
        let changed = super::close_value_changes(&base, &after, &footprints, &mut census);
        let expected = ["a", "b", "opaque", "reader"]
            .into_iter()
            .map(|key| Reference::Item {
                key: ItemKey::from(key),
                occurrence: Occurrence::from(0_usize),
            })
            .collect();
        assert_eq!(changed, expected);
        assert_eq!(usize::from(census.seeds), 1_usize);
        assert_eq!(usize::from(census.value_changed), 4_usize);
        assert_eq!(usize::from(census.closure_edges), 3_usize);
    }
}
