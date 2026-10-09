//! Checkpoints and resume: one forward pass that adopts what still answers
//! and judges the rest.
//!
//! # Reuse is validated, never trusted
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
//! same pass, so a decoded set is as safe to resume from as one in memory.
//!
//! # The same pass, two memos
//!
//! Batch checking is the pass at [`NullMemo`], which recalls nothing, so every
//! item is judged; incremental checking is the pass at [`OrderedMemo`] built
//! from the base checkpoints. The incremental contract — incremental equals
//! batch — is therefore a statement about one function at two type
//! parameters, and the differential tests compare it against the checker's
//! own batch entry besides.
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

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::FormedValueType;
use gandr_core_checker::Support;
use gandr_core_checker::check_declaration_supported;
use gandr_core_checker::form_value_type;
use gandr_core_checker::signature_table;
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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Answer
{
    /// No type is held.
    Untyped,
    /// This type is held.
    Typed(TypeContent),
}

/// One answer a judgement consulted, by the reference it asked about.
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
    /// - requires: nothing — checkpoints are validated when adopted, never
    ///   trusted on construction.
    /// - ensures: the parts, with the support ascending by reference and each
    ///   reference once, its first answer kept.
    /// - panics: none.
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
    /// trivial.
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
    /// - requires: nothing — the checkpoints are validated by the next resume,
    ///   never here.
    /// - ensures: on success the checkpoints, every item marked judged, one
    ///   fresh handle per item, and an empty census.
    /// - fails: [`ResumeError::Order`] when the order cannot be built.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ResumeError::Order`] — the order-maintenance structure refused.
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
/// - provides: the batch half of the incremental contract: the pass at
///   [`NullMemo`].
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
/// - ensures: on success the typings the batch run gives `edited` under
///   `base`'s allowance, each item adopted only when validated; items whose
///   reference survives in order keep their handle.
/// - provides: the incremental half of the contract.
/// - fails: [`ResumeError::Order`] when the order cannot be spliced.
/// - panics: none.
///
/// # Errors
/// [`ResumeError::Order`] — the order-maintenance structure refused.
///
/// # Adequacy
/// - hypothesis: L2 — the differential suite compares the resume against batch
///   over generated programs and edit chains, with adoption asserted real by
///   the precision probe; L3 for the named adoption and invalidation cases.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
/// - witness: `tests::incremental::body_edit_adopts_the_type_stable_dependent`
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
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
/// - requires: nothing — restored checkpoints are validated as any others.
/// - ensures: as [`resume`], with fresh handles.
/// - fails: [`ResumeError::Order`] when the order cannot be built.
/// - panics: none.
///
/// # Errors
/// [`ResumeError::Order`] — the order-maintenance structure refused.
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
pub struct ItemIdentity<'content>
{
    /// The content compared.
    content: &'content ItemContent,
    /// The digest the memo buckets by.
    digest: ContentDigest,
}

/// The one plane item identities are accounted to.
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
    fn build(base: &Checkpoints) -> Self::Memo<'_>;
}

/// The batch choice: a memo that recalls nothing.
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
/// trivial.
fn bump(count: &mut ItemCount)
{
    *count = ItemCount::from(usize::from(*count).saturating_add(1));
}

/// Whether a recalled checkpoint still answers.
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
    let arena = context.arena();
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
/// - hypothesis: L3 — the surfaces are the four conditions, separated by an
///   item whose support fails, one whose type position reads a changed value,
///   one whose recorded answer's type does, and an opaque one.
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
/// - witness: `tests::incremental::an_ascription_endpoint_is_a_read`
/// - witness: `tests::incremental::a_changed_value_reaches_through_an_untouched_definition`
/// - witness: `tests::incremental::an_opaque_footprint_is_never_adopted`
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
    if context.adopt(input.declaration.constant(), seat).is_err() {
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
/// trivial.
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
fn canonical_support(mut support: Vec<Answered>) -> Vec<Answered>
{
    support.sort_by(|left, right| left.reference.cmp(&right.reference));
    support.dedup_by(|later, earlier| later.reference == earlier.reference);
    support
}

/// The content of a table answer.
///
/// # Specification
/// trivial.
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
/// - hypothesis: L3 — the surfaces are the seeds, the closure and the opaque
///   rule, separated by a change reaching a reader through an untouched
///   definition, a bystander left out, and a recheck count asserted linear at
///   four program sizes.
/// - witness: `tests::incremental::a_changed_value_reaches_through_an_untouched_definition`
/// - witness: `tests::defects::items_visited_for_a_head_edit_grow_linearly`
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
