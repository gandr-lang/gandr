//! The **shifting and substitution machines**: the two de Bruijn rewrites the
//! dependent arrow's rules stand on, as iterative walks over the arena with
//! their own memo instantiations.
//!
//! # Two rewrites, one engine, two planes
//!
//! Shifting raises every free index at or above a cutoff; substitution replaces
//! the innermost binder's variable by a value and lowers everything outside it
//! by one. They differ in exactly one arm — what a variable becomes — so they
//! share the walk and split at the leaf, and each is accounted to its own memo
//! plane so neither machine's reuse hides behind the other's numbers.
//!
//! # Why they are machines rather than functions
//!
//! Substitution is the function everyone writes recursively, and a recursive
//! one overflows the stack on a term a decoder built from bytes. Both rewrites
//! here are loops over an explicit task stack and an explicit results stack, so
//! they are total on any depth, and the frames they push are the
//! defunctionalized continuations the recursive presentation's call sites would
//! have been.
//!
//! **The one place the recursive presentation calls the other rewrite is a
//! scheduled task here rather than a nested call.** Substituting under binders
//! has to carry the replacement in past them, which is a shift; the engine
//! schedules that shift onto the same task stack, and its single result lands
//! exactly where the occurrence's own result would have. So the two rewrites
//! are one loop, and neither function reaches the other.
//!
//! # Unchanged is the identity, and that is what preserves sharing
//!
//! A node whose children all rewrite to themselves is **returned unchanged**
//! rather than re-minted. Two things follow. The arena does not grow by a copy
//! of every type a rewrite touches, which matters because a checker's
//! intermediates are minted past the admission watermark. And the sharing a
//! decode handed over survives a rewrite instead of being flattened into fresh
//! nodes — the property the whole representation is built around.
//!
//! A type carrying no code is closed, so it rewrites to itself and the walk
//! hands back the node it was given rather than a copy. That is the common case
//! and it costs nothing; a type that does carry a code rewrites through the
//! code, which is the whole of what makes a context of types stop being a
//! context of closed things.
//!
//! # The memo is content-keyed, and it creates sharing among intermediates
//!
//! Two structurally equal subjects at one binder depth are one rewrite, so a
//! shared subterm is rewritten once however many times it occurs — the property
//! that keeps a rewrite linear in distinct nodes rather than in occurrences.
//!
//! The consequence worth naming: the rewritten graph can share where the
//! original did not. That is sharing **created** by the kernel, and it is
//! admissible for a reason rather than by omission — it is created only among
//! nodes the kernel itself minted past the watermark, and nothing decides on
//! it. Conversion's identity fast path is positive-only, so more sharing can
//! make a comparison finish earlier and can never change a verdict; the trusted
//! base still takes no interning table of *decoded* values.

use alloc::vec::Vec;

use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_check_memo::OrderedMemo;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::encoding::ContentEncoding;
use crate::encoding::ContentTable;
use crate::encoding::RewriteGoal;
use crate::encoding::encode_rewrite;

/// A count of binders: a cutoff, a shift amount, or the depth a walk has
/// reached.
///
/// One type for the three because they are the same quantity measured from
/// three places, and because a bare integer in these signatures is exactly the
/// confusion that makes a de Bruijn rewrite wrong in a way no type catches.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderDepth(u32);

impl From<u32> for BinderDepth
{
    /// The depth of `depth` binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: u32) -> Self
    {
        Self(depth)
    }
}

impl From<BinderDepth> for u32
{
    /// How many binders `depth` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: BinderDepth) -> Self
    {
        depth.0
    }
}

impl From<BinderDepth> for usize
{
    /// The same count as a machine index.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the depth as a machine index, saturating at the ceiling
    ///   rather than wrapping.
    /// - provides: the one conversion into an index a telescope is measured
    ///   with.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn from(depth: BinderDepth) -> Self
    {
        Self::try_from(depth.0).unwrap_or(Self::MAX)
    }
}

impl BinderDepth
{
    /// No binders.
    pub const NONE: Self = Self(0);

    /// One binder further in, saturating at the ceiling.
    ///
    /// Saturation is the fail-safe direction: a depth at the ceiling is deeper
    /// than any representable index, so every variable below it reads as bound
    /// and no free index is rewritten by mistake.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one more than `self`, and `self` itself at the ceiling.
    /// - provides: the depth step every binding position takes, saturating in
    ///   the fail-safe direction: a depth at the ceiling reads every
    ///   representable index as bound, so no free index is rewritten by
    ///   mistake.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn deeper(self) -> Self
    {
        // reason: binder depth uses u32::MAX as its conservative ceiling.
        Self(u32::from(arith::saturating_add(
            arith::Int::from(self.0),
            arith::Int::from(1_u32),
        )))
    }

    /// The amount that raises an index past a telescope of `slots` binders.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one more than `slots`, saturating at the ceiling.
    /// - provides: the shift amount that raises an index past a telescope of
    ///   that many binders.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn past(slots: Self) -> Self
    {
        // reason: the shift amount clamps at the representable binder ceiling.
        Self(u32::from(arith::saturating_add(
            arith::Int::from(slots.0),
            arith::Int::from(1_u32),
        )))
    }
}

/// Which rewrite a support belongs to: the memo's accounting partition.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RewritePlane
{
    /// The shifting machine.
    Shift,
    /// The substitution machine.
    Substitute,
}

/// What one rewrite step produced: the node it rewrote to, in its own family.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RewriteOutcome
{
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(ComputationId),
    /// A value-type node.
    ValueType(ValueTypeId),
    /// A computation-type node.
    CompType(CompTypeId),
}

impl RewriteOutcome
{
    /// The value id this outcome carries, or the original when the families
    /// disagree.
    ///
    /// A family disagreement is unreachable — the engine pushes one result per
    /// child in the child's own family — and declining to the original is the
    /// fail-safe reading: an unrewritten node is always well-formed, where a
    /// fabricated one need not be.
    ///
    /// # Specification
    /// - requires: nothing; an outcome of the wrong family is admissible input
    ///   and declines to `original`.
    /// - ensures: the value id this outcome carries, and `original` for every
    ///   other family.
    /// - provides: the fail-safe unwrapping of a child's result — an
    ///   unrewritten node is always well formed, where a fabricated one need
    ///   not be.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    const fn value_or(
        self,
        original: ValueId,
    ) -> ValueId
    {
        match self {
            | Self::Value(id) => id,
            | Self::Computation(_) | Self::ValueType(_) | Self::CompType(_) => original,
        }
    }

    /// The computation id this outcome carries; see [`Self::value_or`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `value_or`, on the computation family.
    /// - provides: the fail-safe unwrapping of a child's result.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    const fn computation_or(
        self,
        original: ComputationId,
    ) -> ComputationId
    {
        match self {
            | Self::Computation(id) => id,
            | Self::Value(_) | Self::ValueType(_) | Self::CompType(_) => original,
        }
    }

    /// The value-type id this outcome carries; see [`Self::value_or`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `value_or`, on the value-type family.
    /// - provides: the fail-safe unwrapping of a child's result.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    const fn value_type_or(
        self,
        original: ValueTypeId,
    ) -> ValueTypeId
    {
        match self {
            | Self::ValueType(id) => id,
            | Self::Value(_) | Self::Computation(_) | Self::CompType(_) => original,
        }
    }

    /// The computation-type id this outcome carries; see [`Self::value_or`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `value_or`, on the computation-type family.
    /// - provides: the fail-safe unwrapping of a child's result.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    const fn comp_type_or(
        self,
        original: CompTypeId,
    ) -> CompTypeId
    {
        match self {
            | Self::CompType(id) => id,
            | Self::Value(_) | Self::Computation(_) | Self::ValueType(_) => original,
        }
    }
}

/// The complete support of one rewrite step, as content.
///
/// It holds no arena id: the canonical encoding of the subject, the binder
/// depth, and the rewrite's parameter, plus that encoding's digest. Equality is
/// byte equality of the encoding — the deciding comparison — and the digest
/// narrows a bucket without ever deciding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteSupport
{
    /// Which machine asked.
    plane: RewritePlane,
    /// The canonical content encoding.
    encoding: ContentEncoding,
    /// The digest of that encoding.
    digest: ContentDigest,
}

impl RewriteSupport
{
    /// Build the support of one rewrite goal.
    ///
    /// # Specification
    /// - requires: `table` is this session's and `arena` is the one it has been
    ///   used with.
    /// - ensures: two supports are equal exactly when the two goals rewrite the
    ///   same content the same way at the same binder depth.
    /// - provides: the rewrite memo's key. Session provenance and equality
    ///   across rewrite goals remain prose-only: a single invocation has no
    ///   history token or second goal with an independent semantic
    ///   interpretation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the plane split and the encoding,
    ///   separated by a shift and a substitution over one subject (two planes,
    ///   two encodings) and by one subject at two depths, each asserted
    ///   exactly.
    /// - witness: `rewrite::tests::two_rewrites_of_one_subject_are_two_supports`
    #[must_use]
    fn build(
        table: &mut ContentTable,
        arena: &TermArena,
        goal: RewriteGoal,
    ) -> Self
    {
        let plane = match goal {
            | RewriteGoal::Shift { .. } => RewritePlane::Shift,
            | RewriteGoal::Substitute { .. } => RewritePlane::Substitute,
        };
        let encoding = encode_rewrite(table, arena, goal);
        let digest = encoding.digest();
        Self {
            plane,
            encoding,
            digest,
        }
    }
}

impl MemoKey for RewriteSupport
{
    type Plane = RewritePlane;

    /// The machine this support was built for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane(&self) -> Self::Plane
    {
        self.plane
    }

    /// The digest of this support's canonical encoding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn digest(&self) -> ContentDigest
    {
        self.digest
    }

    /// The deciding comparison: byte equality of the canonical encodings.
    ///
    /// The plane is compared first and is redundant — the encoding opens with
    /// the goal's direction tag, and the two directions draw disjoint bytes —
    /// so the plane field is load-bearing for accounting rather than for
    /// agreement, exactly as it is on the checker's own key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `ContentAgreement::Agree` exactly when the two supports carry
    ///   the same plane and byte-equal canonical encodings; the digest is not
    ///   read, so a collision reaches this comparison and loses.
    /// - provides: the deciding comparison every rewrite the session reuses is
    ///   served on.
    /// - panics: none.
    #[inline]
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement
    {
        if self.plane == other.plane && self.encoding == other.encoding {
            ContentAgreement::Agree
        }
        else {
            ContentAgreement::Differ
        }
    }
}

/// The rewrite memo a session builds for itself: the default path.
pub type RewriteMemo = OrderedMemo<RewriteSupport, RewriteOutcome>;

/// Which rewrite the engine is running, with its parameter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rewrite
{
    /// Raise every free index at or above `cutoff` by `amount`.
    Shift
    {
        /// The cutoff, measured at the root.
        cutoff: BinderDepth,
        /// The amount every free index at or above the cutoff rises by.
        amount: BinderDepth,
    },
    /// Replace the innermost binder's variable by `replacement` and lower
    /// everything outside it by one.
    Substitute
    {
        /// The replacement value, in the context outside the binder.
        replacement: ValueId,
    },
}

impl Rewrite
{
    /// This rewrite's goal for `subject` at `depth`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn goal(
        self,
        subject: AnyNode,
        depth: BinderDepth,
    ) -> RewriteGoal
    {
        match self {
            | Self::Shift { cutoff, amount } => RewriteGoal::Shift {
                subject,
                depth,
                cutoff,
                amount,
            },
            | Self::Substitute { replacement } => RewriteGoal::Substitute {
                subject,
                depth,
                replacement,
            },
        }
    }
}

/// One step of the rewrite walk.
///
/// Every task carries the rewrite it belongs to, because a substitution
/// schedules shifts of its own: carrying the replacement under the binders the
/// walk crossed is a shift, and running it as tasks on this same stack is what
/// keeps the two rewrites one loop rather than one calling the other.
#[derive(Clone, Copy, Debug)]
enum RewriteTask
{
    /// Rewrite this node at this depth: consult the memo, else schedule its
    /// children and its own close.
    Open(AnyNode, BinderDepth, Rewrite),
    /// Every child of this node has a result on the stack; combine them.
    Close(AnyNode, BinderDepth, Rewrite),
    /// The result on top of the stack is this goal's answer, produced by a
    /// scheduled sub-walk rather than by a close; record it.
    Record(AnyNode, BinderDepth, Rewrite),
}

/// The shifted or substituted form of a value-type node.
///
/// # Specification
/// - requires: `table` is this session's; `memo` holds only entries this
///   session recorded against this arena.
/// - ensures: the node with every free index rewritten, minted into `arena` as
///   a checker intermediate; the node itself when nothing under it changed,
///   which is what preserves the sharing a decode handed over. The walk is
///   iterative, so it is total on any depth.
/// - provides: the context-lookup shift the checker performs at every variable.
///   Session origin and exact rewritten content remain prose-only: proving the
///   shift and unchanged-node reuse requires a separate semantic traversal, not
///   replaying the mutating rewrite.
/// - fails: never — an unreadable node rewrites to itself, which is the
///   fail-safe reading, and the goal that reaches it refuses on its own
///   account.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the variable arm and the unchanged
///   reuse, separated by a closed type (the same id back) and by the term-level
///   witnesses that exercise the same engine at a family where variables occur.
/// - witness: `rewrite::tests::a_closed_type_shifts_to_itself`
/// - witness: `rewrite::tests::a_code_carrying_type_rewrites_through_its_code`
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
/// - witness: `adversarial_depth::adversarial_depth::the_rewrite_machines_are_total_on_a_code_carrying_chain`
#[inline]
#[must_use]
pub fn shift_value_type<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    subject: ValueTypeId,
    cutoff: BinderDepth,
    amount: BinderDepth,
) -> ValueTypeId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let rewrite = Rewrite::Shift { cutoff, amount };
    run_rewrite(arena, table, memo, rewrite, AnyNode::ValueType(subject)).value_type_or(subject)
}

/// The shifted form of a value node; see [`shift_value_type`].
///
/// # Specification
/// - requires: as [`shift_value_type`].
/// - ensures: as [`shift_value_type`], over the value family, where the
///   variable arm is the one that does the work.
/// - provides: the value half of the shifting machine, which substitution uses
///   to carry a replacement under a binder. The inherited session and rewrite
///   clauses remain prose-only for the same reason as [`shift_value_type`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`shift_value_type`].
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
// No production caller yet: the checker reaches the shifting machine through
// its value-type face and the substitution machine through its computation-type
// face, and the other four faces exist because the machines are defined over all
// four families rather than because a call site wanted them. The expectation is
// scoped to the non-test build so it lapses — loudly — the moment one is wired.
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "family face awaiting its first production caller")
)]
#[must_use]
pub(crate) fn shift_value<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    subject: ValueId,
    cutoff: BinderDepth,
    amount: BinderDepth,
) -> ValueId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let rewrite = Rewrite::Shift { cutoff, amount };
    run_rewrite(arena, table, memo, rewrite, AnyNode::Value(subject)).value_or(subject)
}

/// The shifted form of a computation node; see [`shift_value_type`].
///
/// # Specification
/// - requires: as [`shift_value_type`].
/// - ensures: as [`shift_value_type`], over the computation family.
/// - provides: the computation half of the shifting machine. The inherited
///   session and rewrite clauses remain prose-only for the same reason as
///   [`shift_value_type`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`shift_value_type`]; the residue is the three binding
///   formers, whose bound positions each step the depth in by one.
/// - witness: `rewrite::tests::a_binder_spares_what_it_binds`
#[inline]
#[must_use]
pub(crate) fn shift_computation<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    subject: ComputationId,
    cutoff: BinderDepth,
    amount: BinderDepth,
) -> ComputationId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let rewrite = Rewrite::Shift { cutoff, amount };
    run_rewrite(arena, table, memo, rewrite, AnyNode::Computation(subject)).computation_or(subject)
}

/// The computation type `subject` with its innermost binder instantiated at
/// `replacement`.
///
/// This is the dependent arrow's elimination rule: applying a value to a
/// function of dependent type produces the codomain instantiated at that value.
///
/// # Specification
/// - requires: `subject` stands under exactly one binder more than
///   `replacement` does; `table` is this session's; `memo` holds only entries
///   this session recorded against this arena.
/// - ensures: every occurrence of the innermost binder's variable is replaced
///   by `replacement`, carried under each binder the walk crosses, and every
///   index outside that binder is lowered by one; the node itself when nothing
///   under it changed. The walk is iterative, so it is total on any depth.
/// - provides: the instantiation an application at a dependent head performs.
///   Binder and session provenance are not carried by these ids; exact
///   substitution and unchanged-node reuse require a separate semantic
///   traversal. These clauses remain prose-only.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the three variable cases — bound inside
///   the walk, the substituted index, and outside it — separated by a closed
///   type (unchanged) and by the term-level witnesses that exercise all three.
/// - witness: `rewrite::tests::a_closed_type_instantiates_to_itself`
/// - witness: `rewrite::tests::a_code_carrying_type_rewrites_through_its_code`
/// - witness: `rewrite::tests::substitution_replaces_lowers_and_spares`
/// - witness: `adversarial_depth::adversarial_depth::the_rewrite_machines_are_total_on_a_chain_deep_term`
#[inline]
#[must_use]
pub fn substitute_comp_type<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    subject: CompTypeId,
    replacement: ValueId,
) -> CompTypeId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let rewrite = Rewrite::Substitute { replacement };
    run_rewrite(arena, table, memo, rewrite, AnyNode::CompType(subject)).comp_type_or(subject)
}

/// The value type `subject` with its innermost binder instantiated at
/// `replacement`; see [`substitute_comp_type`].
///
/// # Specification
/// - requires: as [`substitute_comp_type`].
/// - ensures: as [`substitute_comp_type`], over the value-type family.
/// - provides: the value-type half of the substitution machine. The inherited
///   binder, session, and rewrite clauses remain prose-only for the same reason
///   as [`substitute_comp_type`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`substitute_comp_type`].
/// - witness: `rewrite::tests::a_closed_type_instantiates_to_itself`
// No production caller yet: the checker reaches the shifting machine through
// its value-type face and the substitution machine through its computation-type
// face, and the other four faces exist because the machines are defined over all
// four families rather than because a call site wanted them. The expectation is
// scoped to the non-test build so it lapses — loudly — the moment one is wired.
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "family face awaiting its first production caller")
)]
#[must_use]
pub(crate) fn substitute_value_type<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    subject: ValueTypeId,
    replacement: ValueId,
) -> ValueTypeId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let rewrite = Rewrite::Substitute { replacement };
    run_rewrite(arena, table, memo, rewrite, AnyNode::ValueType(subject)).value_type_or(subject)
}

/// The value `subject` with its innermost binder instantiated at `replacement`;
/// see [`substitute_comp_type`].
///
/// # Specification
/// - requires: as [`substitute_comp_type`].
/// - ensures: as [`substitute_comp_type`], over the value family, where the
///   variable arm is the one that does the work.
/// - provides: the value half of the substitution machine. The inherited
///   binder, session, and rewrite clauses remain prose-only for the same reason
///   as [`substitute_comp_type`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`substitute_comp_type`].
/// - witness: `rewrite::tests::substitution_replaces_lowers_and_spares`
// No production caller yet: the checker reaches the shifting machine through
// its value-type face and the substitution machine through its computation-type
// face, and the other four faces exist because the machines are defined over all
// four families rather than because a call site wanted them. The expectation is
// scoped to the non-test build so it lapses — loudly — the moment one is wired.
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "family face awaiting its first production caller")
)]
#[must_use]
pub(crate) fn substitute_value<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    subject: ValueId,
    replacement: ValueId,
) -> ValueId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let rewrite = Rewrite::Substitute { replacement };
    run_rewrite(arena, table, memo, rewrite, AnyNode::Value(subject)).value_or(subject)
}

/// The computation `subject` with its innermost binder instantiated at
/// `replacement`; see [`substitute_comp_type`].
///
/// # Specification
/// - requires: as [`substitute_comp_type`].
/// - ensures: as [`substitute_comp_type`], over the computation family.
/// - provides: the computation half of the substitution machine: the β-step a
///   conversion replay fires when a lambda meets an argument, a returner meets
///   a bind, or an injection meets a case. The inherited binder, session, and
///   rewrite clauses remain prose-only for the same reason as
///   [`substitute_comp_type`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`substitute_comp_type`]; the residue is the entry,
///   carried by the replay's reduction witnesses.
/// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
#[inline]
#[must_use]
pub(crate) fn substitute_computation<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    subject: ComputationId,
    replacement: ValueId,
) -> ComputationId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let rewrite = Rewrite::Substitute { replacement };
    run_rewrite(arena, table, memo, rewrite, AnyNode::Computation(subject)).computation_or(subject)
}

/// Drive one rewrite to completion over an explicit task stack and an explicit
/// results stack.
///
/// # Specification
/// - requires: `root` resolves in `arena`, or does not, in which case it
///   rewrites to itself.
/// - ensures: the rewritten node, minted into `arena` where a child changed and
///   reused where none did. Every node is opened once per distinct `(content,
///   depth)` pair when the memo is active and once per occurrence when it is
///   not, and **the answer is the same either way** — the memo is an
///   optimization above a results stack that carries every intermediate, never
///   the store the walk depends on.
/// - provides: the shared engine of the two rewrites. Exact rewritten content,
///   traversal counts, and memo independence remain prose-only: a return
///   predicate has neither the execution trace nor an independent rewrite over
///   the entry arena.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the walk is a loop over an explicit task stack, not recursion.
/// - measure: the multiset of scheduled opens, ordered by the arena position of
///   the node each names. An open pushes either its node's children, whose ids
///   are strictly below their parent's within a family, or — at the
///   carried-occurrence arm alone — one sub-walk open on the replacement. A
///   close and a record push nothing.
/// - boundedness: the arena is finite and acyclic by the minting invariant, and
///   a minted node is never opened, so the set of openable nodes is finite. The
///   carried-occurrence arm is the only one whose scheduled open is not a
///   child, and **its nesting is exactly one deep**: it fires only for a
///   substitution, and the sub-walk it schedules is a *shift*, for which
///   [`carried_occurrence`] returns nothing — so the sub-walk descends its own
///   children and can never schedule a third walk. Its subject is the
///   replacement, which is fixed before the outer walk starts and is therefore
///   not a node the outer walk can grow.
/// - input recursion: none.
///
/// # Adequacy
/// - hypothesis: L2 — the memoized and memoless runs are pinned against each
///   other over a shared composite, node for node, which is the differential
///   the memo's soundness rests on; the L3 residues are the per-former combine
///   arms, carried by the two rewrites' own witnesses.
/// - witness: `rewrite::tests::the_memoized_rewrite_agrees_with_the_memoless_one`
/// - witness: `adversarial_depth::adversarial_depth::the_rewrite_machines_are_total_on_a_chain_deep_term`
fn run_rewrite<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    rewrite: Rewrite,
    root: AnyNode,
) -> RewriteOutcome
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let mut tasks: Vec<RewriteTask> = Vec::new();
    let mut results: Vec<RewriteOutcome> = Vec::new();
    tasks.push(RewriteTask::Open(root, BinderDepth::NONE, rewrite));
    while let Some(task) = tasks.pop() {
        match task {
            | RewriteTask::Open(node, depth, step) => {
                let support = RewriteSupport::build(table, arena, step.goal(node, depth));
                if let Some(hit) = memo.recall(&support) {
                    results.push(*hit.outcome());
                    continue;
                }
                // The one arm that answers through a sub-walk rather than
                // through its children: the occurrence being substituted, where
                // the walk has crossed binders the replacement has to be carried
                // under. The sub-walk leaves exactly one result on the stack,
                // which is what this goal's parent was going to read anyway.
                match carried_occurrence(arena, step, node, depth) {
                    | Maybe::Present(replacement) => {
                        tasks.push(RewriteTask::Record(node, depth, step));
                        tasks.push(RewriteTask::Open(
                            AnyNode::Value(replacement),
                            BinderDepth::NONE,
                            Rewrite::Shift {
                                cutoff: BinderDepth::NONE,
                                amount: depth,
                            },
                        ));
                        continue;
                    },
                    | Maybe::Absent(
                        carrying::Absent::Shift
                        | carrying::Absent::NoCrossedBinders
                        | carrying::Absent::DifferentOccurrence
                        | carrying::Absent::UnreadableValue,
                    ) => {},
                }
                tasks.push(RewriteTask::Close(node, depth, step));
                push_rewrite_children(arena, node, depth, &mut tasks, step);
            },
            | RewriteTask::Close(node, depth, step) => {
                let outcome = close_rewrite(arena, step, node, depth, &mut results);
                let support = RewriteSupport::build(table, arena, step.goal(node, depth));
                // A memo at its ceiling declines to record. The walk proceeds
                // unmemoized from there, which costs reuse and never the answer.
                let _recorded = memo.remember(support, outcome);
                results.push(outcome);
            },
            | RewriteTask::Record(node, depth, step) => {
                if let Some(&outcome) = results.last() {
                    let support = RewriteSupport::build(table, arena, step.goal(node, depth));
                    let _recorded = memo.remember(support, outcome);
                }
            },
        }
    }
    results.pop().unwrap_or_else(|| outcome_of(root))
}

quenchant_shape::reason_enum! {
    /// Why the ordinary rewrite path needs no carrying shift.
    mod carrying {
        /// A carrying shortcut does not apply to this rewrite goal.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// Shifting substitutes no replacement.
            Shift,
            /// A replacement at depth zero crosses no binders.
            NoCrossedBinders,
            /// The node is not the variable occurrence being substituted.
            DifferentOccurrence,
            /// The ordinary unreadable-node path must handle this id.
            UnreadableValue,
        }
    }
}

/// The replacement a substitution has to carry under crossed binders, when this
/// goal is the occurrence being substituted and there are binders to cross.
///
/// A substitution at depth zero needs no carrying, so it takes the ordinary
/// close path and hands the replacement back as it stands; every other case
/// schedules the shift.
///
/// # Specification
/// - requires: `depth` is the number of binders the walk has crossed to reach
///   `node`.
/// - ensures: the replacement exactly when this is a substitution, some binder
///   has been crossed, and the node is the variable occurrence the depth names;
///   nothing in every other case, including a substitution at depth zero, which
///   takes the ordinary close path instead.
/// - provides: a replacement or [`Absent`]: `Shift` selects shifting,
///   `NoCrossedBinders` needs no raise, `DifferentOccurrence` is not the
///   target, and `UnreadableValue` leaves the ordinary unreadable-node path in
///   charge.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — crossing a binder raises the replacement, while depth
///   zero, a different occurrence and a shift retain their ordinary paths.
/// - witness: `rewrite::tests::a_replacement_is_carried_under_the_binders_it_crosses`
/// - witness: `rewrite::tests::substitution_replaces_lowers_and_spares`
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
///
/// [`Absent`]: carrying::Absent
#[inline]
fn carried_occurrence(
    arena: &TermArena,
    rewrite: Rewrite,
    node: AnyNode,
    depth: BinderDepth,
) -> Maybe<ValueId, carrying::Absent>
{
    let Rewrite::Substitute { replacement } = rewrite
    else {
        return Maybe::Absent(carrying::Absent::Shift);
    };
    if depth == BinderDepth::NONE {
        return Maybe::Absent(carrying::Absent::NoCrossedBinders);
    }
    let AnyNode::Value(id) = node
    else {
        return Maybe::Absent(carrying::Absent::DifferentOccurrence);
    };
    let Some(value) = arena.value(id)
    else {
        return Maybe::Absent(carrying::Absent::UnreadableValue);
    };
    match *value {
        | Value::Variable(index) if BinderDepth::from(u32::from(index)) == depth => {
            Maybe::Present(replacement)
        },
        | Value::Variable(_)
        | Value::Constant(_)
        | Value::Unit
        | Value::Literal(_)
        | Value::Pair(..)
        | Value::Injection(..)
        | Value::Thunk(_)
        | Value::Lift { .. }
        | Value::Quote(_)
        | Value::QuoteComputation(_) => Maybe::Absent(carrying::Absent::DifferentOccurrence),
    }
}

/// A node as its own outcome: the fail-safe reading of an empty results stack,
/// which the engine's own invariant makes unreachable.
///
/// # Specification
/// trivial.
#[inline]
const fn outcome_of(node: AnyNode) -> RewriteOutcome
{
    match node {
        | AnyNode::Value(id) => RewriteOutcome::Value(id),
        | AnyNode::Computation(id) => RewriteOutcome::Computation(id),
        | AnyNode::ValueType(id) => RewriteOutcome::ValueType(id),
        | AnyNode::CompType(id) => RewriteOutcome::CompType(id),
    }
}

/// Schedule `node`'s children, innermost-last, each at the depth its position
/// sits at.
///
/// The tasks stack pops in reverse, so children are pushed in reverse wire
/// order and close in wire order — which is the order [`close_rewrite`] pops
/// their results in.
///
/// **The binding positions are the whole content of this function.** A lambda
/// binds for its body, a bind binds for its body and not for the bound
/// computation, a case binds for each branch and not for the scrutinee, and the
/// dependent arrow binds for its codomain and not for its domain.
///
/// # Specification
/// - requires: `depth` is the number of binders the walk has crossed to reach
///   `node`.
/// - ensures: pushes one open task per child, in reverse wire order so the
///   children close in wire order, and at the depth that child's position sits
///   at: one binder further in for a lambda's body, a bind's body but not its
///   bound computation, each case branch but not the scrutinee, and a dependent
///   arrow's codomain but not its domain. A node with no children, and one that
///   cannot be read, push nothing.
/// - provides: the scheduling half of the engine, and the only statement of
///   where the term language binds.
/// - fails: never.
/// - panics: none.
fn push_rewrite_children(
    arena: &TermArena,
    node: AnyNode,
    depth: BinderDepth,
    tasks: &mut Vec<RewriteTask>,
    rewrite: Rewrite,
)
{
    match node {
        | AnyNode::Value(id) => match arena.value(id) {
            | Some(
                &Value::Variable(_) | &Value::Constant(_) | &Value::Unit | &Value::Literal(_),
            )
            | None => {},
            | Some(&Value::Pair(first, second)) => {
                tasks.push(RewriteTask::Open(AnyNode::Value(second), depth, rewrite));
                tasks.push(RewriteTask::Open(AnyNode::Value(first), depth, rewrite));
            },
            | Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => {
                tasks.push(RewriteTask::Open(AnyNode::Value(body), depth, rewrite));
            },
            | Some(&Value::Thunk(body)) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::Computation(body),
                    depth,
                    rewrite,
                ));
            },
            // The term-to-type edge: a quoted type is rewritten at the depth
            // its quote stands at, the converse of the decoding edge below.
            | Some(&Value::Quote(quoted)) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::ValueType(quoted),
                    depth,
                    rewrite,
                ));
            },
            | Some(&Value::QuoteComputation(quoted)) => {
                tasks.push(RewriteTask::Open(AnyNode::CompType(quoted), depth, rewrite));
            },
        },
        | AnyNode::Computation(id) => match arena.computation(id) {
            | None => {},
            | Some(&Computation::Lambda(body)) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::Computation(body),
                    depth.deeper(),
                    rewrite,
                ));
            },
            | Some(&Computation::Application(head, argument)) => {
                tasks.push(RewriteTask::Open(AnyNode::Value(argument), depth, rewrite));
                tasks.push(RewriteTask::Open(
                    AnyNode::Computation(head),
                    depth,
                    rewrite,
                ));
            },
            | Some(&Computation::Return(value) | &Computation::Force(value)) => {
                tasks.push(RewriteTask::Open(AnyNode::Value(value), depth, rewrite));
            },
            | Some(&Computation::Bind(bound, body)) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::Computation(body),
                    depth.deeper(),
                    rewrite,
                ));
                tasks.push(RewriteTask::Open(
                    AnyNode::Computation(bound),
                    depth,
                    rewrite,
                ));
            },
            | Some(&Computation::Case {
                scrutinee,
                on_left,
                on_right,
            }) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::Computation(on_right),
                    depth.deeper(),
                    rewrite,
                ));
                tasks.push(RewriteTask::Open(
                    AnyNode::Computation(on_left),
                    depth.deeper(),
                    rewrite,
                ));
                tasks.push(RewriteTask::Open(AnyNode::Value(scrutinee), depth, rewrite));
            },
        },
        | AnyNode::ValueType(id) => match arena.value_type(id) {
            | Some(
                &ValueType::Base(_)
                | &ValueType::Unit
                | &ValueType::Universe { .. }
                | &ValueType::Abstract(_),
            )
            | None => {},
            | Some(&ValueType::Product(first, second) | &ValueType::Sum(first, second)) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::ValueType(second),
                    depth,
                    rewrite,
                ));
                tasks.push(RewriteTask::Open(AnyNode::ValueType(first), depth, rewrite));
            },
            | Some(&ValueType::Thunk(body)) => {
                tasks.push(RewriteTask::Open(AnyNode::CompType(body), depth, rewrite));
            },
            | Some(&ValueType::Lift { inner, .. }) => {
                tasks.push(RewriteTask::Open(AnyNode::ValueType(inner), depth, rewrite));
            },
            // The type-to-term edge: a code is rewritten at the depth the type
            // stands at, which is why a rewrite over a type that carries a code
            // is not the identity.
            | Some(&ValueType::Element { code, .. }) => {
                tasks.push(RewriteTask::Open(AnyNode::Value(code), depth, rewrite));
            },
        },
        | AnyNode::CompType(id) => match arena.comp_type(id) {
            | None => {},
            | Some(&CompType::Returner(result)) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::ValueType(result),
                    depth,
                    rewrite,
                ));
            },
            | Some(&CompType::Arrow { domain, codomain }) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::CompType(codomain),
                    depth,
                    rewrite,
                ));
                tasks.push(RewriteTask::Open(
                    AnyNode::ValueType(domain),
                    depth,
                    rewrite,
                ));
            },
            | Some(&CompType::Pi { domain, codomain }) => {
                tasks.push(RewriteTask::Open(
                    AnyNode::CompType(codomain),
                    depth.deeper(),
                    rewrite,
                ));
                tasks.push(RewriteTask::Open(
                    AnyNode::ValueType(domain),
                    depth,
                    rewrite,
                ));
            },
            | Some(&CompType::Element { code, .. }) => {
                tasks.push(RewriteTask::Open(AnyNode::Value(code), depth, rewrite));
            },
        },
    }
}

/// Combine `node`'s children's results into its own, minting only when a child
/// changed.
///
/// # Specification
/// - requires: the results stack holds one outcome per child of `node`, pushed
///   by that child's own close.
/// - ensures: the outcome of `node`, in `node`'s own family, minting a fresh
///   node only where some child changed and answering the original id
///   otherwise, so sharing is preserved rather than re-created.
/// - provides: the combining half of the engine, dispatched to the family's own
///   close.
/// - fails: never.
/// - panics: none.
fn close_rewrite(
    arena: &mut TermArena,
    rewrite: Rewrite,
    node: AnyNode,
    depth: BinderDepth,
    results: &mut Vec<RewriteOutcome>,
) -> RewriteOutcome
{
    match node {
        | AnyNode::Value(id) => {
            RewriteOutcome::Value(close_value(arena, rewrite, id, depth, results))
        },
        | AnyNode::Computation(id) => {
            RewriteOutcome::Computation(close_computation(arena, id, results))
        },
        | AnyNode::ValueType(id) => RewriteOutcome::ValueType(close_value_type(arena, id, results)),
        | AnyNode::CompType(id) => RewriteOutcome::CompType(close_comp_type(arena, id, results)),
    }
}

/// Pop one child result, or fall back to the child itself.
///
/// The fallback is unreachable: an open pushed one result per child before its
/// parent's close ran. Reading it as "unchanged" is the fail-safe direction.
///
/// # Specification
/// - requires: nothing; an empty stack is admissible input and reads as
///   unchanged.
/// - ensures: the top result, and `original` as its own outcome when the stack
///   is empty.
/// - provides: the fail-safe read of a child's result. The empty case is
///   unreachable — an open pushed one result per child before its parent's
///   close ran — and reading it as unchanged cannot fabricate a node.
/// - fails: never.
/// - panics: none.
#[inline]
fn popped(
    results: &mut Vec<RewriteOutcome>,
    original: AnyNode,
) -> RewriteOutcome
{
    results.pop().unwrap_or_else(|| outcome_of(original))
}

/// Combine a value node.
///
/// **The variable arm is where the two rewrites differ, and it is the only arm
/// that differs.** A shift raises a free index and spares a bound one; a
/// substitution replaces the index the walk's depth names, lowers every index
/// outside it, and spares every index inside.
///
/// # Specification
/// - requires: the results stack holds one outcome per child of `id`, and
///   `depth` is the number of binders crossed to reach it.
/// - ensures: the rewritten value id: the variable arm applies the rewrite's
///   own rule, a closed former answers `id`, and every other former mints a
///   node only where a child changed. An unreadable id answers itself.
/// - provides: the value arm of the combining half, and the one arm where the
///   two rewrites differ.
/// - fails: never.
/// - panics: none.
fn close_value(
    arena: &mut TermArena,
    rewrite: Rewrite,
    id: ValueId,
    depth: BinderDepth,
    results: &mut Vec<RewriteOutcome>,
) -> ValueId
{
    let Some(node) = arena.value(id).cloned()
    else {
        return id;
    };
    match node {
        | Value::Variable(index) => rewrite_variable(arena, rewrite, id, index, depth),
        | Value::Constant(_) | Value::Unit | Value::Literal(_) => id,
        | Value::Pair(first, second) => {
            // Results are popped in reverse wire order: children were scheduled
            // so that they close left to right, so the last one to close is the
            // first one on top of the stack.
            let rewritten_second = popped(results, AnyNode::Value(second)).value_or(second);
            let rewritten_first = popped(results, AnyNode::Value(first)).value_or(first);
            if rewritten_first == first && rewritten_second == second {
                id
            }
            else {
                arena.value_pair(rewritten_first, rewritten_second)
            }
        },
        | Value::Injection(side, body) => {
            let rewritten = popped(results, AnyNode::Value(body)).value_or(body);
            if rewritten == body {
                id
            }
            else {
                arena.value_injection(side, rewritten)
            }
        },
        | Value::Lift { target, body } => {
            let rewritten = popped(results, AnyNode::Value(body)).value_or(body);
            if rewritten == body {
                id
            }
            else {
                arena.value_lift(target, rewritten)
            }
        },
        | Value::Thunk(body) => {
            let rewritten = popped(results, AnyNode::Computation(body)).computation_or(body);
            if rewritten == body {
                id
            }
            else {
                arena.value_thunk(rewritten)
            }
        },
        | Value::Quote(quoted) => {
            let rewritten = popped(results, AnyNode::ValueType(quoted)).value_type_or(quoted);
            if rewritten == quoted {
                id
            }
            else {
                arena.value_quote(rewritten)
            }
        },
        | Value::QuoteComputation(quoted) => {
            let rewritten = popped(results, AnyNode::CompType(quoted)).comp_type_or(quoted);
            if rewritten == quoted {
                id
            }
            else {
                arena.value_quote_computation(rewritten)
            }
        },
    }
}

/// The rewritten form of one bound-variable occurrence.
///
/// The three cases of a substitution are the whole rule: an index strictly
/// below the depth is bound inside the walk and stands; an index equal to the
/// depth is the one being replaced, and the replacement is carried in under the
/// binders crossed to reach here; an index above it named a slot outside the
/// binder that is now gone, so it lowers by one.
///
/// # Specification
/// - requires: `depth` is the number of binders crossed to reach this
///   occurrence, and `index` is the occurrence's own de Bruijn index.
/// - ensures: for a shift, the index rises by the amount exactly when it is at
///   or above the cutoff measured from this depth, and stands otherwise; for a
///   substitution, an index below the depth stands, an index equal to it
///   becomes the replacement, and an index above it lowers by one. Shift
///   cutoffs and raised indices clamp at the representable ceiling.
/// - provides: the whole variable rule of both machines, written once.
/// - fails: never.
/// - panics: none.
fn rewrite_variable(
    arena: &mut TermArena,
    rewrite: Rewrite,
    id: ValueId,
    index: DeBruijnIndex,
    depth: BinderDepth,
) -> ValueId
{
    let index = BinderDepth::from(u32::from(index));
    match rewrite {
        | Rewrite::Shift { cutoff, amount } => {
            // reason: a cutoff beyond the index range uses its conservative ceiling.
            let effective = BinderDepth(u32::from(arith::saturating_add(
                arith::Int::from(cutoff.0),
                arith::Int::from(depth.0),
            )));
            if index < effective {
                id
            }
            else {
                // reason: the shift specification clamps an out-of-range raised index.
                let raised = u32::from(arith::saturating_add(
                    arith::Int::from(index.0),
                    arith::Int::from(amount.0),
                ));
                arena.value_variable(DeBruijnIndex::from(raised))
            }
        },
        | Rewrite::Substitute { replacement } => match index.cmp(&depth) {
            | core::cmp::Ordering::Less => id,
            // Reached only at depth zero: every deeper occurrence answers
            // through the scheduled carrying shift, which the engine takes
            // before it ever schedules this close.
            | core::cmp::Ordering::Equal => replacement,
            | core::cmp::Ordering::Greater => {
                // index > depth >= 0, so removing this binder cannot underflow.
                let lowered = u32::from(arith::sub(
                    arith::Int::from(index.0),
                    arith::Int::from(1_u32),
                ));
                arena.value_variable(DeBruijnIndex::from(lowered))
            },
        },
    }
}

/// Combine a computation node.
///
/// # Specification
/// - requires: the results stack holds one outcome per child of `id`.
/// - ensures: the rewritten computation id, minting a fresh node only where
///   some child changed and answering `id` otherwise; an unreadable id answers
///   itself.
/// - provides: the computation arm of the combining half.
/// - fails: never.
/// - panics: none.
fn close_computation(
    arena: &mut TermArena,
    id: ComputationId,
    results: &mut Vec<RewriteOutcome>,
) -> ComputationId
{
    let Some(node) = arena.computation(id).cloned()
    else {
        return id;
    };
    match node {
        | Computation::Lambda(body) => {
            let rewritten = popped(results, AnyNode::Computation(body)).computation_or(body);
            if rewritten == body {
                id
            }
            else {
                arena.computation_lambda(rewritten)
            }
        },
        | Computation::Application(head, argument) => {
            let rewritten_argument = popped(results, AnyNode::Value(argument)).value_or(argument);
            let rewritten_head = popped(results, AnyNode::Computation(head)).computation_or(head);
            if rewritten_head == head && rewritten_argument == argument {
                id
            }
            else {
                arena.computation_application(rewritten_head, rewritten_argument)
            }
        },
        | Computation::Return(value) => {
            let rewritten = popped(results, AnyNode::Value(value)).value_or(value);
            if rewritten == value {
                id
            }
            else {
                arena.computation_return(rewritten)
            }
        },
        | Computation::Force(value) => {
            let rewritten = popped(results, AnyNode::Value(value)).value_or(value);
            if rewritten == value {
                id
            }
            else {
                arena.computation_force(rewritten)
            }
        },
        | Computation::Bind(bound, body) => {
            let rewritten_body = popped(results, AnyNode::Computation(body)).computation_or(body);
            let rewritten_bound =
                popped(results, AnyNode::Computation(bound)).computation_or(bound);
            if rewritten_bound == bound && rewritten_body == body {
                id
            }
            else {
                arena.computation_bind(rewritten_bound, rewritten_body)
            }
        },
        | Computation::Case {
            scrutinee,
            on_left,
            on_right,
        } => {
            let rewritten_right =
                popped(results, AnyNode::Computation(on_right)).computation_or(on_right);
            let rewritten_left =
                popped(results, AnyNode::Computation(on_left)).computation_or(on_left);
            let rewritten_scrutinee =
                popped(results, AnyNode::Value(scrutinee)).value_or(scrutinee);
            if rewritten_scrutinee == scrutinee
                && rewritten_left == on_left
                && rewritten_right == on_right
            {
                id
            }
            else {
                arena.computation_case(rewritten_scrutinee, rewritten_left, rewritten_right)
            }
        },
    }
}

/// Combine a value-type node.
///
/// # Specification
/// - requires: the results stack holds one outcome per child of `id`.
/// - ensures: the rewritten value-type id, minting a fresh node only where some
///   child changed and answering `id` otherwise; an unreadable id answers
///   itself.
/// - provides: the value-type arm of the combining half.
/// - fails: never.
/// - panics: none.
fn close_value_type(
    arena: &mut TermArena,
    id: ValueTypeId,
    results: &mut Vec<RewriteOutcome>,
) -> ValueTypeId
{
    let Some(node) = arena.value_type(id).cloned()
    else {
        return id;
    };
    match node {
        | ValueType::Base(_)
        | ValueType::Unit
        | ValueType::Universe { .. }
        | ValueType::Abstract(_) => id,
        | ValueType::Element { code, target } => {
            let rewritten = popped(results, AnyNode::Value(code)).value_or(code);
            if rewritten == code {
                id
            }
            else {
                arena.value_type_element(rewritten, target)
            }
        },
        | ValueType::Product(first, second) => {
            let rewritten_second =
                popped(results, AnyNode::ValueType(second)).value_type_or(second);
            let rewritten_first = popped(results, AnyNode::ValueType(first)).value_type_or(first);
            if rewritten_first == first && rewritten_second == second {
                id
            }
            else {
                arena.value_type_product(rewritten_first, rewritten_second)
            }
        },
        | ValueType::Sum(first, second) => {
            let rewritten_second =
                popped(results, AnyNode::ValueType(second)).value_type_or(second);
            let rewritten_first = popped(results, AnyNode::ValueType(first)).value_type_or(first);
            if rewritten_first == first && rewritten_second == second {
                id
            }
            else {
                arena.value_type_sum(rewritten_first, rewritten_second)
            }
        },
        | ValueType::Thunk(body) => {
            let rewritten = popped(results, AnyNode::CompType(body)).comp_type_or(body);
            if rewritten == body {
                id
            }
            else {
                arena.value_type_thunk(rewritten)
            }
        },
        | ValueType::Lift { inner, target } => {
            let rewritten = popped(results, AnyNode::ValueType(inner)).value_type_or(inner);
            if rewritten == inner {
                id
            }
            else {
                arena.value_type_lift(rewritten, target)
            }
        },
    }
}

/// Combine a computation-type node.
///
/// # Specification
/// - requires: the results stack holds one outcome per child of `id`.
/// - ensures: the rewritten computation-type id, minting a fresh node only
///   where some child changed and answering `id` otherwise; an unreadable id
///   answers itself.
/// - provides: the computation-type arm of the combining half.
/// - fails: never.
/// - panics: none.
fn close_comp_type(
    arena: &mut TermArena,
    id: CompTypeId,
    results: &mut Vec<RewriteOutcome>,
) -> CompTypeId
{
    let Some(node) = arena.comp_type(id).cloned()
    else {
        return id;
    };
    match node {
        | CompType::Returner(result) => {
            let rewritten = popped(results, AnyNode::ValueType(result)).value_type_or(result);
            if rewritten == result {
                id
            }
            else {
                arena.comp_type_returner(rewritten)
            }
        },
        | CompType::Arrow { domain, codomain } => {
            let rewritten_codomain =
                popped(results, AnyNode::CompType(codomain)).comp_type_or(codomain);
            let rewritten_domain =
                popped(results, AnyNode::ValueType(domain)).value_type_or(domain);
            if rewritten_domain == domain && rewritten_codomain == codomain {
                id
            }
            else {
                arena.comp_type_arrow(rewritten_domain, rewritten_codomain)
            }
        },
        | CompType::Pi { domain, codomain } => {
            let rewritten_codomain =
                popped(results, AnyNode::CompType(codomain)).comp_type_or(codomain);
            let rewritten_domain =
                popped(results, AnyNode::ValueType(domain)).value_type_or(domain);
            if rewritten_domain == domain && rewritten_codomain == codomain {
                id
            }
            else {
                arena.comp_type_pi(rewritten_domain, rewritten_codomain)
            }
        },
        // As at the value decode: a substituted quote fires the decoding rule
        // in the constructor, so the rewrite never leaves the redex behind.
        | CompType::Element { code, target } => {
            let rewritten = popped(results, AnyNode::Value(code)).value_or(code);
            if rewritten == code {
                id
            }
            else {
                arena.comp_type_element(rewritten, target)
            }
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_kernel_check_memo::CheckMemo as _;
    use gandr_kernel_check_memo::ContentAgreement;
    use gandr_kernel_check_memo::MemoEntryCount;
    use gandr_kernel_check_memo::MemoKey as _;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::CompType;
    use gandr_kernel_term::Computation;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueType;
    use quenchant_arith::arith;

    use super::BinderDepth;
    use super::ContentTable;
    use super::RewriteMemo;
    use super::RewritePlane;
    use super::RewriteSupport;
    use super::shift_computation;
    use super::shift_value;
    use super::shift_value_type;
    use super::substitute_comp_type;
    use super::substitute_value;
    use super::substitute_value_type;
    use crate::encoding::RewriteGoal;
    use crate::encoding::content_digest;

    /// A fixture's chain length, as its own quantity rather than a bare count.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct ChainLength(u32);

    /// The de Bruijn index at `depth` binders out.
    ///
    /// # Specification
    /// trivial.
    fn index(depth: BinderDepth) -> DeBruijnIndex
    {
        DeBruijnIndex::from(u32::from(depth))
    }

    #[test]
    fn shifting_raises_free_indices_and_spares_bound_ones()
    {
        let mut arena = TermArena::new();
        let free = arena.value_variable(index(BinderDepth::from(0_u32)));
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let raised = shift_value(
            &mut arena,
            &mut table,
            &mut memo,
            free,
            BinderDepth::NONE,
            BinderDepth::from(2_u32),
        );
        assert_eq!(
            Some(&Value::Variable(index(BinderDepth::from(2_u32)))),
            arena.value(raised),
            "a free index at the cutoff rises by the amount"
        );
        let spared = shift_value(
            &mut arena,
            &mut table,
            &mut memo,
            free,
            BinderDepth::from(1_u32),
            BinderDepth::from(2_u32),
        );
        assert_eq!(
            free, spared,
            "an index below the cutoff is bound outside the rewrite and is returned unchanged"
        );
    }

    #[test]
    fn a_binder_spares_what_it_binds()
    {
        let mut arena = TermArena::new();
        let inner = arena.value_variable(index(BinderDepth::from(0_u32)));
        let outer = arena.value_variable(index(BinderDepth::from(1_u32)));
        let pair = arena.value_pair(inner, outer);
        let body = arena.computation_return(pair);
        let lambda = arena.computation_lambda(body);
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let shifted = shift_computation(
            &mut arena,
            &mut table,
            &mut memo,
            lambda,
            BinderDepth::NONE,
            BinderDepth::from(3_u32),
        );
        let Some(&Computation::Lambda(shifted_body)) = arena.computation(shifted)
        else {
            panic!("a shifted lambda is a lambda");
        };
        let Some(&Computation::Return(shifted_pair)) = arena.computation(shifted_body)
        else {
            panic!("its body is a returner");
        };
        let Some(&Value::Pair(first, second)) = arena.value(shifted_pair)
        else {
            panic!("and the returner carries the pair");
        };
        assert_eq!(
            Some(&Value::Variable(index(BinderDepth::from(0_u32)))),
            arena.value(first),
            "the lambda's own binder is spared"
        );
        assert_eq!(
            Some(&Value::Variable(index(BinderDepth::from(4_u32)))),
            arena.value(second),
            "and the index reaching past it rises by the amount"
        );
    }

    #[test]
    fn substitution_replaces_lowers_and_spares()
    {
        let mut arena = TermArena::new();
        let replacement = arena.value_literal(Literal::Text(StringLiteral::new(String::from("r"))));
        let bound_inside = arena.value_variable(index(BinderDepth::from(0_u32)));
        let substituted = arena.value_variable(index(BinderDepth::from(1_u32)));
        let outside = arena.value_variable(index(BinderDepth::from(2_u32)));
        let inner_pair = arena.value_pair(bound_inside, substituted);
        let pair = arena.value_pair(inner_pair, outside);
        let body = arena.computation_return(pair);
        let lambda = arena.computation_lambda(body);
        let thunk = arena.value_thunk(lambda);
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let result = substitute_value(&mut arena, &mut table, &mut memo, thunk, replacement);

        let Some(&Value::Thunk(result_lambda)) = arena.value(result)
        else {
            panic!("a substituted thunk is a thunk");
        };
        let Some(&Computation::Lambda(result_body)) = arena.computation(result_lambda)
        else {
            panic!("holding a lambda");
        };
        let Some(&Computation::Return(result_pair)) = arena.computation(result_body)
        else {
            panic!("whose body returns");
        };
        let Some(&Value::Pair(result_inner, result_outside)) = arena.value(result_pair)
        else {
            panic!("a pair");
        };
        let Some(&Value::Pair(result_bound, result_substituted)) = arena.value(result_inner)
        else {
            panic!("over a pair");
        };
        assert_eq!(
            Some(&Value::Variable(index(BinderDepth::from(0_u32)))),
            arena.value(result_bound),
            "an index bound inside the walk stands"
        );
        assert_eq!(
            arena.value(replacement).cloned(),
            arena.value(result_substituted).cloned(),
            "the index the walk's depth names becomes the replacement"
        );
        assert_eq!(
            Some(&Value::Variable(index(BinderDepth::from(1_u32)))),
            arena.value(result_outside),
            "and an index outside the vanished binder lowers by one"
        );
    }

    /// A replacement with a free index is carried under the binders the walk
    /// crossed, which is the half of substitution that capture-avoidance is.
    #[test]
    fn a_replacement_is_carried_under_the_binders_it_crosses()
    {
        let mut arena = TermArena::new();
        let replacement = arena.value_variable(index(BinderDepth::from(0_u32)));
        let occurrence = arena.value_variable(index(BinderDepth::from(1_u32)));
        let body = arena.computation_return(occurrence);
        let lambda = arena.computation_lambda(body);
        let thunk = arena.value_thunk(lambda);
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let result = substitute_value(&mut arena, &mut table, &mut memo, thunk, replacement);
        let Some(&Value::Thunk(result_lambda)) = arena.value(result)
        else {
            panic!("a substituted thunk is a thunk");
        };
        let Some(&Computation::Lambda(result_body)) = arena.computation(result_lambda)
        else {
            panic!("holding a lambda");
        };
        let Some(&Computation::Return(carried)) = arena.computation(result_body)
        else {
            panic!("whose body returns");
        };
        assert_eq!(
            Some(&Value::Variable(index(BinderDepth::from(1_u32)))),
            arena.value(carried),
            "the replacement's own free index rises past the binder it was carried under"
        );
    }

    /// Every type is closed at a vocabulary where no former is indexed by a
    /// value term, so both rewrites hand back the node they were given — the
    /// sharing-preserving reuse, exhibited where it is total.
    #[test]
    fn a_closed_type_shifts_to_itself()
    {
        let mut arena = TermArena::new();
        let base = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let product = arena.value_type_product(base, unit);
        let returner = arena.comp_type_returner(product);
        let dependent = arena.comp_type_pi(unit, returner);
        let thunk = arena.value_type_thunk(dependent);
        let before = arena.watermark();
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let shifted = shift_value_type(
            &mut arena,
            &mut table,
            &mut memo,
            thunk,
            BinderDepth::NONE,
            BinderDepth::from(3_u32),
        );
        assert_eq!(thunk, shifted, "a closed type shifts to the very same node");
        assert_eq!(
            before,
            arena.watermark(),
            "and the rewrite mints nothing, so the arena does not grow by a copy"
        );
    }

    #[test]
    fn a_closed_type_instantiates_to_itself()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let dependent = arena.comp_type_pi(unit, returner);
        let replacement = arena.value_unit();
        let before = arena.watermark();
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let instantiated =
            substitute_comp_type(&mut arena, &mut table, &mut memo, dependent, replacement);
        assert_eq!(
            dependent, instantiated,
            "instantiating a closed dependent arrow is the identity on its node"
        );
        let inner = substitute_value_type(&mut arena, &mut table, &mut memo, unit, replacement);
        assert_eq!(unit, inner, "and so is instantiating a closed value type");
        assert_eq!(
            before,
            arena.watermark(),
            "neither mints, so no intermediate outlives the verdict"
        );
    }

    /// A type carrying a code shifts and instantiates like the term it carries,
    /// which is the whole of what "types in the context stop being closed"
    /// means operationally.
    #[test]
    fn a_code_carrying_type_rewrites_through_its_code()
    {
        let mut arena = TermArena::new();
        let zero = Level::zero();
        let code = arena.value_variable(index(BinderDepth::from(0_u32)));
        let element = arena.value_type_element(code, zero);
        let returner = arena.comp_type_returner(element);
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();

        let shifted = shift_value_type(
            &mut arena,
            &mut table,
            &mut memo,
            element,
            BinderDepth::NONE,
            BinderDepth::from(2_u32),
        );
        let Some(&ValueType::Element { code: raised, .. }) = arena.value_type(shifted)
        else {
            panic!("a shifted code-carrying type still carries a code");
        };
        assert_eq!(
            Some(&Value::Variable(index(BinderDepth::from(2_u32)))),
            arena.value(raised),
            "the code's free index rose with the type it sits in"
        );

        // And a dependent codomain instantiates: the returner under the binder
        // reads index zero, so instantiating it at a replacement replaces the
        // code outright.
        let replacement = arena.value_unit();
        let instantiated =
            substitute_comp_type(&mut arena, &mut table, &mut memo, returner, replacement);
        let Some(&CompType::Returner(result)) = arena.comp_type(instantiated)
        else {
            panic!("an instantiated returner is a returner");
        };
        let Some(&ValueType::Element { code: planted, .. }) = arena.value_type(result)
        else {
            panic!("over a code-carrying type");
        };
        assert_eq!(
            replacement, planted,
            "the codomain's code became the argument"
        );
    }

    /// The differential the memo's soundness rests on: the same function at two
    /// type parameters answers alike.
    ///
    /// The workload shares one subterm across many occurrences, so the memoized
    /// run records one entry per distinct `(content, depth)` pair while the
    /// memoless run recomputes each occurrence — and both produce the same
    /// rewritten node.
    #[test]
    fn the_memoized_rewrite_agrees_with_the_memoless_one()
    {
        /// Build a self-similar value whose expansion is exponential in `depth`
        /// and whose distinct-node count is linear in it.
        ///
        /// # Specification
        /// - provides: a shared pair spine with exactly `levels` links.
        /// - panics: none.
        fn shared_composite(
            arena: &mut TermArena,
            levels: ChainLength,
        ) -> ValueId
        {
            let mut node = arena.value_variable(index(BinderDepth::from(0_u32)));
            let mut remaining = levels.0;
            while remaining > 0 {
                node = arena.value_pair(node, node);
                remaining = u32::from(arith::sub(
                    arith::Int::from(remaining),
                    arith::Int::from(1_u32),
                ));
            }
            node
        }

        let mut arena = TermArena::new();
        let root = shared_composite(&mut arena, ChainLength(12));

        let mut memoless_table = ContentTable::new();
        let mut memoless = NullMemo;
        let memoless_result = shift_value(
            &mut arena,
            &mut memoless_table,
            &mut memoless,
            root,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );

        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let memoized_result = shift_value(
            &mut arena,
            &mut table,
            &mut memo,
            root,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );

        // Content, not identity: the two runs answer with the same *term*, and
        // the memoized one answers with a shared spelling of it while the
        // memoless one answers with the expansion. Comparing ids here would
        // assert the opposite of the property under test.
        assert_eq!(
            content_digest(&arena, AnyNode::Value(memoless_result)),
            content_digest(&arena, AnyNode::Value(memoized_result)),
            "the memoized and memoless rewrites produce the same term"
        );
        assert_eq!(
            MemoEntryCount::from(13_usize),
            memo.plane_entry_count(RewritePlane::Shift),
            "one entry per distinct node of the composite, not one per occurrence"
        );
        assert_eq!(
            MemoEntryCount::from(0_usize),
            memo.plane_entry_count(RewritePlane::Substitute),
            "and the substitution plane accounts nothing, so neither plane hides behind the other"
        );

        // The anti-vacuity half, exhibited rather than counted: the memoized
        // answer shares its two children on one node, and the memoless answer
        // does not, so the workload cannot silently stop being shared and keep
        // this case passing.
        let Some(&Value::Pair(memoized_left, memoized_right)) = arena.value(memoized_result)
        else {
            panic!("the composite rewrites to a pair");
        };
        assert_eq!(
            memoized_left, memoized_right,
            "the memoized rewrite answers once for the one distinct subject"
        );
        let Some(&Value::Pair(memoless_left, memoless_right)) = arena.value(memoless_result)
        else {
            panic!("and so does the memoless one");
        };
        assert_ne!(
            memoless_left, memoless_right,
            "while the memoless rewrite answers once per occurrence, which is the cost the memo \
             removes"
        );
    }

    #[test]
    fn two_rewrites_of_one_subject_are_two_supports()
    {
        let mut arena = TermArena::new();
        let subject = arena.value_variable(index(BinderDepth::from(0_u32)));
        let replacement = arena.value_unit();
        let mut table = ContentTable::new();
        let shift = RewriteSupport::build(&mut table, &arena, RewriteGoal::Shift {
            subject: AnyNode::Value(subject),
            depth: BinderDepth::NONE,
            cutoff: BinderDepth::NONE,
            amount: BinderDepth::from(1_u32),
        });
        let substitute = RewriteSupport::build(&mut table, &arena, RewriteGoal::Substitute {
            subject: AnyNode::Value(subject),
            depth: BinderDepth::NONE,
            replacement,
        });
        assert_eq!(RewritePlane::Shift, shift.plane());
        assert_eq!(RewritePlane::Substitute, substitute.plane());
        assert_eq!(
            ContentAgreement::Differ,
            shift.agreement(&substitute),
            "two rewrites of one subject are two questions"
        );
        let deeper = RewriteSupport::build(&mut table, &arena, RewriteGoal::Shift {
            subject: AnyNode::Value(subject),
            depth: BinderDepth::from(1_u32),
            cutoff: BinderDepth::NONE,
            amount: BinderDepth::from(1_u32),
        });
        assert_eq!(
            ContentAgreement::Differ,
            shift.agreement(&deeper),
            "and one subject at two binder depths is two questions"
        );
    }
}
