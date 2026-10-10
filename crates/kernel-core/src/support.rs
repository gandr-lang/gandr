//! The **support of one node check**: everything the checker's answer for a
//! single node depends on, and nothing else.
//!
//! # Why this is the whole soundness argument
//!
//! A memo is sound exactly when equal supports force equal answers. So a
//! support has to be the *complete* input to one goal expansion, and each
//! component below is here because dropping it would let two different
//! questions collide:
//!
//! - **the obligation's content** — not its arena id. Two structurally equal
//!   nodes are one question wherever they sit, which is what lets a re-minted
//!   spine reuse its untouched leaf, and it is what an identity key forfeits.
//! - **the direction, with the expected type** — checking a value against `A`
//!   and against `B` are different questions, and synthesis is a third.
//! - **the binder telescope's content** — variables are de Bruijn indices
//!   resolved against the machine's context, so the same node under two
//!   different contexts means two different things. Only the slice the node can
//!   actually reach is folded in, and it is folded *in telescope order* so
//!   dependency order is part of the content.
//!
//! The key is therefore `(obligation content, telescope content, direction)`,
//! and it is **arena-free**: no arena id, no allocation order, and no context
//! length outside the reached slice reaches it. Content is named by the
//! canonical numbering [`SupportContext`] holds, so two structurally equal
//! nodes key alike however many arena positions spell them.
//!
//! The declaration's level parameters and the environment's admission log are
//! *not* in the key. They are fixed for the whole of one declaration's check,
//! and a memo never outlives that — see
//! [`check_declaration_with_memo`](crate::check::check_declaration_with_memo).
//!
//! # A type reaches binders too
//!
//! The universe-decoding former carries a value, so a type can mention a bound
//! variable and a type-formation goal's answer depends on the same reached
//! telescope a term goal's does. The reach pass therefore runs over all four
//! families rather than over the two term ones, which is what keeps a type
//! formed under two different binders from collapsing onto one entry.
//!
//! # The binder slice is computed, not guessed
//!
//! [`LooseDepths`] computes one more than each node's largest free de Bruijn
//! index, bottom-up over the graph, iteratively, cached per node — so the
//! computation is itself sharing-aware and costs one pass per *distinct* node
//! rather than per occurrence. Where it cannot answer it returns the maximum,
//! which widens the slice to the whole context: **the failure direction is
//! always more context in the key, never less**, so a defect here costs
//! collapse and cannot manufacture a hit.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo as _;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::MemoEntryCount;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_arith::arith;

use crate::encoding::ContentEncoding;
use crate::encoding::ContentTable;
use crate::encoding::SupportGoal;
use crate::encoding::encode_support;
use crate::rewrite::RewriteMemo;
use crate::rewrite::RewritePlane;

/// The state one checking session derives its memo keys against: the canonical
/// content numbering and the per-node binder reach.
///
/// **The session is the memo's lifetime, made structural.** A support is
/// meaningful against the session that built it and against no other, so a
/// caller who wants to hand a memo an entry must build that entry through the
/// same session it then hands to the check. There is no way to mint a key that
/// outlives its call by accident.
#[derive(Clone, Debug, Default)]
pub struct SupportContext
{
    /// The canonical content numbering.
    table: ContentTable,
    /// The per-node binder reach.
    reaches: LooseDepths,
    /// The session's shifting and substitution memo.
    rewrites: RewriteMemo,
}

impl SupportContext
{
    /// A session over nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The two halves a rewrite needs: the content numbering its key is derived
    /// from, and the memo it records into.
    ///
    /// Handed over together because a rewrite borrows both at once and they are
    /// disjoint fields of one session — which is also the statement that a
    /// rewrite's memo lives exactly as long as the check that opened it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn rewrite_parts(&mut self) -> (&mut ContentTable, &mut RewriteMemo)
    {
        (&mut self.table, &mut self.rewrites)
    }

    /// The binder reach of a computation-type node, cached for the session.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn comp_type_reach(
        &mut self,
        arena: &TermArena,
        root: CompTypeId,
    ) -> LooseDepth
    {
        self.reaches.comp_type_reach(arena, root)
    }

    /// How many rewrites of `plane` this session has recorded.
    ///
    /// The two rewrites account separately, so a suite can pin the shifting
    /// machine's reuse without the substitution machine's numbers standing in
    /// for it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret == self.rewrites.plane_entry_count(plane)` — the
    ///   number of entries this session's rewrite memo holds on `plane`, one
    ///   per distinct rewritten `(content, depth)` pair.
    /// - provides: the per-plane accounting an acceptance case pins the two
    ///   wiring sites through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the plane projection, separated by a
    ///   check that reaches both wiring sites and finds both planes non-empty.
    /// - witness: `acceptance::acceptance::the_rewrite_planes_account_separately_through_a_real_check`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.rewrites.plane_entry_count(plane))]
    pub fn rewrite_entry_count(
        &self,
        plane: RewritePlane,
    ) -> MemoEntryCount
    {
        self.rewrites.plane_entry_count(plane)
    }
}

/// One more than the largest free de Bruijn index a node mentions; zero for a
/// closed node.
///
/// This is the number of enclosing binders the node can reach, so it is exactly
/// the length of the context slice its meaning depends on.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LooseDepth(u32);

impl From<u32> for LooseDepth
{
    /// The reach of `value` binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}

impl From<LooseDepth> for u32
{
    /// How many binders `depth` reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: LooseDepth) -> Self
    {
        depth.0
    }
}

impl LooseDepth
{
    /// The saturated maximum — the conservative answer, widening the key's
    /// slice to the whole context.
    const WIDEST: Self = Self(u32::MAX);

    /// The larger of two reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn join(
        self,
        other: Self,
    ) -> Self
    {
        if self.0 >= other.0 { self } else { other }
    }

    /// The reach seen from outside one binder: a body reaching `n` binders
    /// reaches `n - 1` of its parent's, and a closed body stays closed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn under_binder(self) -> Self
    {
        // reason: crossing a binder leaves a closed body's reach at zero.
        Self(u32::from(arith::saturating_sub(
            arith::Int::from(self.0),
            arith::Int::from(1_u32),
        )))
    }

    /// Where the reached slice of `context` starts — the offset of the first
    /// slot this reach can see, saturating to the whole context when the reach
    /// is at or past its length.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the offset of the first slot this reach can see, and zero
    ///   where the reach is at or past the context's length.
    /// - provides: the failure direction of the whole reach computation: an
    ///   over-estimate widens the key's telescope to the entire context, so it
    ///   can split a support and never merge two.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn start_in(
        self,
        context: &[ValueTypeId],
    ) -> ContextOffset
    {
        let wanted = usize::try_from(self.0).unwrap_or(usize::MAX);
        // reason: an overestimated reach widens the slice to the whole context.
        ContextOffset(usize::from(arith::saturating_sub(
            arith::Int::from(context.len()),
            arith::Int::from(wanted),
        )))
    }
}

/// An offset into the machine's typing context.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ContextOffset(usize);

/// Which of the two machines a support belongs to.
///
/// Admitting one declaration runs two iterative machines over the shared graph
/// — the checker's goal loop over the body and the type-formation walk over the
/// declared type. Each gets its own plane so entry counts are asserted
/// separately and neither machine's collapse hides behind the other's numbers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SupportPlane
{
    /// The checker's goal loop, over terms.
    Term,
    /// The type-formation walk, over types.
    Type,
}

/// What one goal expansion produced, as the memo stores it.
///
/// The four variants are the two machines' answers: the checker's produced
/// register, and the type-formation walk's level. They share one memo because
/// they share one lifetime — a declaration's check — and separating them would
/// buy nothing but a second type parameter. **A support carrying the wrong
/// shape is declined and recomputed rather than trusted**, which is what makes
/// sharing the memo safe rather than merely convenient.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NodeOutcome
{
    /// A check succeeded; no type is carried.
    Checked,
    /// A value type was synthesized.
    ValueType(
        /// The synthesized type.
        ValueTypeId,
    ),
    /// A computation type was synthesized.
    CompType(
        /// The synthesized type.
        CompTypeId,
    ),
    /// A type formed at this level.
    Formed(
        /// The universe level.
        Level,
    ),
}

/// The complete support of one goal expansion, as content.
///
/// The support holds no arena id: what it carries is the canonical encoding of
/// the obligation, the expected type, and the reached binder telescope, plus
/// the digest of that encoding. Equality is byte equality of the encoding — the
/// deciding comparison — and the digest is a bucket selector that narrows and
/// never decides.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeSupport
{
    /// Which machine asked.
    plane: SupportPlane,
    /// The canonical content encoding: the deciding comparison's subject.
    encoding: ContentEncoding,
    /// The digest of that encoding: the positive fast path.
    digest: ContentDigest,
}

impl NodeSupport
{
    /// Build the support of `goal` under `context`, taking only the binder
    /// slice the goal's node reaches.
    ///
    /// A type-formation goal reads binders exactly as a term goal does, because
    /// a type can carry a code and a code can be a variable. A type that
    /// carries none reaches nothing and takes the empty telescope, which is
    /// what keeps the closed-type case free.
    ///
    /// # Specification
    /// - requires: `context` is the machine's typing context at the expansion,
    ///   outermost first; `session` is this check's own, and every support a
    ///   memo holds was built against the same one.
    /// - ensures: two supports are equal exactly when the goals ask the same
    ///   question of the same content under the same reached telescope. A wider
    ///   reach yields a longer telescope, so an over-estimate can only split a
    ///   support and never merge two.
    /// - provides: the memo key. Context and session provenance and equality
    ///   across goals remain prose-only: one invocation has neither the history
    ///   nor a second independently interpreted goal.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the plane split, the reach
    ///   lookup, and the slice offset, separated by a closed node under a
    ///   non-empty context (empty telescope), a binder-reading node under two
    ///   differing contexts (two supports), a binder-reading node under two
    ///   contexts agreeing where it looks (one support), and a type goal under
    ///   a non-empty context (empty telescope), each asserted exactly.
    /// - witness: `support::tests::a_closed_node_takes_no_telescope`
    /// - witness: `support::tests::a_binder_reading_node_splits_on_its_slice`
    /// - witness: `support::tests::a_binder_reading_node_collapses_where_its_slice_agrees`
    /// - witness: `support::tests::a_closed_type_goal_reads_no_binder`
    /// - witness: `support::tests::a_code_carrying_type_reads_its_binder`
    #[inline]
    #[must_use]
    pub fn build(
        arena: &TermArena,
        session: &mut SupportContext,
        goal: SupportGoal,
        context: &[ValueTypeId],
    ) -> Self
    {
        let (plane, telescope) = match goal {
            | SupportGoal::ValueTypeLevel(id) => {
                let reach = session.reaches.value_type_reach(arena, id);
                (SupportPlane::Type, reached_slice(context, reach))
            },
            | SupportGoal::CompTypeLevel(id) => {
                let reach = session.reaches.comp_type_reach(arena, id);
                (SupportPlane::Type, reached_slice(context, reach))
            },
            | SupportGoal::SynthValue(id) | SupportGoal::CheckValue(id, _) => {
                let reach = session.reaches.value_reach(arena, id);
                (SupportPlane::Term, reached_slice(context, reach))
            },
            | SupportGoal::SynthComp(id) | SupportGoal::CheckComp(id, _) => {
                let reach = session.reaches.comp_reach(arena, id);
                (SupportPlane::Term, reached_slice(context, reach))
            },
        };
        let encoding = encode_support(&mut session.table, arena, goal, telescope.as_slice());
        let digest = encoding.digest();
        Self {
            plane,
            encoding,
            digest,
        }
    }
}

impl MemoKey for NodeSupport
{
    type Plane = SupportPlane;

    /// The plane this support was built on.
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
    /// The digest is never consulted here, which is the positive-fast-path-only
    /// discipline expressed rather than documented — a collision reaches this
    /// comparison and loses.
    ///
    /// **The plane comparison is redundant and kept deliberately.** Deleting it
    /// is an inert mutation: the encoding's first byte is the goal's direction
    /// tag, and the two type-formation directions draw from a disjoint part of
    /// that alphabet, so the encodings already separate the planes. The
    /// redundancy is defence in depth against a future direction tag that does
    /// not, and the finding is that the plane field is load-bearing for
    /// *accounting* rather than for agreement.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `ContentAgreement::Agree` exactly when the two supports carry
    ///   the same plane and byte-equal canonical encodings; the digest is not
    ///   read, so a collision reaches this comparison and loses.
    /// - provides: the deciding comparison every hit the checker adopts is
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

/// The innermost `reach` entries of `context`, outermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the innermost `reach` slots of `context`, outermost first, and
///   the whole context where the reach is at or past its length.
/// - provides: the telescope a support folds in, in telescope order, so
///   dependency order is part of the content.
/// - fails: never.
/// - panics: none.
#[inline]
fn reached_slice(
    context: &[ValueTypeId],
    reach: LooseDepth,
) -> Vec<ValueTypeId>
{
    let ContextOffset(start) = reach.start_in(context);
    context
        .get(start ..)
        .map_or_else(|| context.to_vec(), <[ValueTypeId]>::to_vec)
}

/// The per-node binder reach, computed once per distinct node and cached.
#[derive(Clone, Debug, Default)]
pub struct LooseDepths
{
    /// Reaches already computed for value nodes.
    values: BTreeMap<ValueId, LooseDepth>,
    /// Reaches already computed for computation nodes.
    computations: BTreeMap<ComputationId, LooseDepth>,
    /// Reaches already computed for value-type nodes.
    value_types: BTreeMap<ValueTypeId, LooseDepth>,
    /// Reaches already computed for computation-type nodes.
    comp_types: BTreeMap<CompTypeId, LooseDepth>,
}

/// One step of the iterative bottom-up reach walk.
#[derive(Clone, Copy, Debug)]
enum ReachTask
{
    /// Ensure this value node's children are computed, then finish it.
    OpenValue(ValueId),
    /// Combine this value node's children's reaches into its own.
    CloseValue(ValueId),
    /// Ensure this computation node's children are computed, then finish it.
    OpenComp(ComputationId),
    /// Combine this computation node's children's reaches into its own.
    CloseComp(ComputationId),
    /// Ensure this value-type node's children are computed, then finish it.
    OpenValueType(ValueTypeId),
    /// Combine this value-type node's children's reaches into its own.
    CloseValueType(ValueTypeId),
    /// Ensure this computation-type node's children are computed, then finish
    /// it.
    OpenCompType(CompTypeId),
    /// Combine this computation-type node's children's reaches into its own.
    CloseCompType(CompTypeId),
}

impl LooseDepths
{
    /// An empty cache.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The binder reach of a value node.
    ///
    /// # Specification
    /// - requires: nothing — an unreadable id is answered conservatively rather
    ///   than refused, since this feeds a key and not a verdict.
    /// - ensures: one more than the node's largest free de Bruijn index, or the
    ///   widest reach where the graph could not be read. The walk is iterative
    ///   over an explicit task stack, so it is total on any depth, and each
    ///   distinct node is combined once however many times it occurs.
    /// - provides: the telescope length of a value goal's support. Exact
    ///   free-index reach, totality, and per-node counts remain prose-only:
    ///   they require an independent binder-aware traversal and its execution
    ///   trace, not the cached answer itself.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the per-former join and the
    ///   binder step, separated by a closed leaf (zero), a bare variable at
    ///   index `i` (`i + 1`), a lambda over a variable (closed from outside),
    ///   and an unreadable id (widest), each asserted exactly.
    /// - witness: `support::tests::a_closed_value_reaches_no_binder`
    /// - witness: `support::tests::a_variable_reaches_one_more_than_its_index`
    /// - witness: `support::tests::a_binder_closes_its_body`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[inline]
    pub fn value_reach(
        &mut self,
        arena: &TermArena,
        root: ValueId,
    ) -> LooseDepth
    {
        self.run(arena, ReachTask::OpenValue(root));
        self.cached_value(root)
    }

    /// The binder reach of a computation node; see [`Self::value_reach`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::value_reach`], over the computation families.
    /// - provides: the telescope length of a computation goal's support. The
    ///   inherited reach and traversal clauses remain prose-only for the same
    ///   reason as [`Self::value_reach`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::value_reach`]; the residues are the three
    ///   binding formers, whose bound positions each step out by one.
    /// - witness: `support::tests::a_binder_closes_its_body`
    /// - witness: `support::tests::a_bind_closes_only_its_body`
    #[inline]
    pub fn comp_reach(
        &mut self,
        arena: &TermArena,
        root: ComputationId,
    ) -> LooseDepth
    {
        self.run(arena, ReachTask::OpenComp(root));
        self.cached_comp(root)
    }

    /// The binder reach of a value-type node; see [`Self::value_reach`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::value_reach`], over the value-type family, where
    ///   the reach comes entirely from the codes the type carries.
    /// - provides: the telescope length of a value-type formation goal's
    ///   support. The inherited reach and traversal clauses remain prose-only
    ///   for the same reason as [`Self::value_reach`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the code edge and the dependent
    ///   arrow's binder step, separated by a closed type (zero), a type over a
    ///   variable code (`i + 1`), and a dependent arrow whose codomain reads
    ///   only its own binder (closed from outside).
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    #[inline]
    pub fn value_type_reach(
        &mut self,
        arena: &TermArena,
        root: ValueTypeId,
    ) -> LooseDepth
    {
        self.run(arena, ReachTask::OpenValueType(root));
        self.cached_value_type(root)
    }

    /// The binder reach of a computation-type node; see
    /// [`Self::value_type_reach`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::value_type_reach`], over the computation-type
    ///   family.
    /// - provides: the telescope length of a computation-type formation goal's
    ///   support. The inherited reach and traversal clauses remain prose-only
    ///   for the same reason as [`Self::value_type_reach`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::value_type_reach`]; the residue is the
    ///   dependent arrow, whose codomain steps out by one and whose domain does
    ///   not.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    #[inline]
    pub fn comp_type_reach(
        &mut self,
        arena: &TermArena,
        root: CompTypeId,
    ) -> LooseDepth
    {
        self.run(arena, ReachTask::OpenCompType(root));
        self.cached_comp_type(root)
    }

    /// Drive the reach walk to completion from one root task.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every node reachable from the root has a cached reach.
    /// - provides: the shared engine of the two reach faces. The executable
    ///   boundary checks root completion; witnesses cover descendant caching
    ///   across binders and code edges.
    /// - fails: never — an unreadable node caches the widest reach.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — code crossings and binder depth close the root cache;
    ///   unreadable nodes conservatively reach the whole telescope.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(ensures: match root {
        ReachTask::OpenValue(id) | ReachTask::CloseValue(id) => self.values.contains_key(&id),
        ReachTask::OpenComp(id) | ReachTask::CloseComp(id) => self.computations.contains_key(&id),
        ReachTask::OpenValueType(id) | ReachTask::CloseValueType(id) => self.value_types.contains_key(&id),
        ReachTask::OpenCompType(id) | ReachTask::CloseCompType(id) => self.comp_types.contains_key(&id),
    })]
    fn run(
        &mut self,
        arena: &TermArena,
        root: ReachTask,
    )
    {
        let mut tasks: Vec<ReachTask> = Vec::new();
        tasks.push(root);
        while let Some(task) = tasks.pop() {
            match task {
                | ReachTask::OpenValue(id) => {
                    if self.values.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.value(id)
                    else {
                        let _prior = self.values.insert(id, LooseDepth::WIDEST);
                        continue;
                    };
                    tasks.push(ReachTask::CloseValue(id));
                    match *node {
                        | Value::Variable(_)
                        | Value::Constant(_)
                        | Value::Unit
                        | Value::Literal(_) => {},
                        | Value::PathEquiv {
                            path_type,
                            forward,
                            backward,
                            ..
                        } => {
                            tasks.push(ReachTask::OpenValueType(path_type));
                            tasks.push(ReachTask::OpenValue(forward));
                            tasks.push(ReachTask::OpenValue(backward));
                        },
                        | Value::SessionPath {
                            path_type,
                            payload_paths,
                            ..
                        } => {
                            tasks.push(ReachTask::OpenValueType(path_type));
                            tasks.push(ReachTask::OpenValue(payload_paths));
                        },
                        | Value::PathRefl(code) => tasks.push(ReachTask::OpenValue(code)),
                        | Value::PathProduct(first, second)
                        | Value::Pair(first, second)
                        | Value::StaticApplication(first, second) => {
                            tasks.push(ReachTask::OpenValue(first));
                            tasks.push(ReachTask::OpenValue(second));
                        },
                        | Value::Injection(_, body) | Value::Lift { body, .. } => {
                            tasks.push(ReachTask::OpenValue(body));
                        },
                        | Value::Thunk(body) => tasks.push(ReachTask::OpenComp(body)),
                        | Value::Quote(quoted) => tasks.push(ReachTask::OpenValueType(quoted)),
                        | Value::QuoteComputation(quoted) => {
                            tasks.push(ReachTask::OpenCompType(quoted));
                        },
                    }
                },
                | ReachTask::CloseValue(id) => {
                    let reach = self.combine_value(arena, id);
                    let _prior = self.values.insert(id, reach);
                },
                | ReachTask::OpenComp(id) => {
                    if self.computations.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.computation(id)
                    else {
                        let _prior = self.computations.insert(id, LooseDepth::WIDEST);
                        continue;
                    };
                    tasks.push(ReachTask::CloseComp(id));
                    match *node {
                        | Computation::Transport(path, value) => {
                            tasks.push(ReachTask::OpenValue(path));
                            tasks.push(ReachTask::OpenValue(value));
                        },
                        | Computation::Lambda(body) => tasks.push(ReachTask::OpenComp(body)),
                        | Computation::Application(head, argument) => {
                            tasks.push(ReachTask::OpenComp(head));
                            tasks.push(ReachTask::OpenValue(argument));
                        },
                        | Computation::Return(value)
                        | Computation::Force(value)
                        | Computation::Absurd(value) => {
                            tasks.push(ReachTask::OpenValue(value));
                        },
                        | Computation::Bind(bound, body) => {
                            tasks.push(ReachTask::OpenComp(bound));
                            tasks.push(ReachTask::OpenComp(body));
                        },
                        | Computation::Case {
                            scrutinee,
                            on_left,
                            on_right,
                        } => {
                            tasks.push(ReachTask::OpenValue(scrutinee));
                            tasks.push(ReachTask::OpenComp(on_left));
                            tasks.push(ReachTask::OpenComp(on_right));
                        },
                    }
                },
                | ReachTask::CloseComp(id) => {
                    let reach = self.combine_comp(arena, id);
                    let _prior = self.computations.insert(id, reach);
                },
                | ReachTask::OpenValueType(id) => {
                    if self.value_types.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.value_type(id)
                    else {
                        let _prior = self.value_types.insert(id, LooseDepth::WIDEST);
                        continue;
                    };
                    tasks.push(ReachTask::CloseValueType(id));
                    match *node {
                        | ValueType::Base(_)
                        | ValueType::Unit
                        | ValueType::Empty
                        | ValueType::Universe { .. }
                        | ValueType::Abstract(_) => {},
                        | ValueType::Product(first, second)
                        | ValueType::Sum(first, second)
                        | ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        } => {
                            tasks.push(ReachTask::OpenValueType(first));
                            tasks.push(ReachTask::OpenValueType(second));
                        },
                        | ValueType::PathUniverse(source, target) => {
                            tasks.push(ReachTask::OpenValue(source));
                            tasks.push(ReachTask::OpenValue(target));
                        },
                        | ValueType::Session {
                            payloads: inner, ..
                        }
                        | ValueType::Lift { inner, .. }
                        | ValueType::List(inner) => {
                            tasks.push(ReachTask::OpenValueType(inner));
                        },
                        | ValueType::Thunk(body) => tasks.push(ReachTask::OpenCompType(body)),
                        | ValueType::Element { code, .. } => {
                            tasks.push(ReachTask::OpenValue(code));
                        },
                    }
                },
                | ReachTask::CloseValueType(id) => {
                    let reach = self.combine_value_type(arena, id);
                    let _prior = self.value_types.insert(id, reach);
                },
                | ReachTask::OpenCompType(id) => {
                    if self.comp_types.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.comp_type(id)
                    else {
                        let _prior = self.comp_types.insert(id, LooseDepth::WIDEST);
                        continue;
                    };
                    tasks.push(ReachTask::CloseCompType(id));
                    match *node {
                        | CompType::Returner(result) => {
                            tasks.push(ReachTask::OpenValueType(result));
                        },
                        | CompType::Arrow { domain, codomain }
                        | CompType::Pi { domain, codomain } => {
                            tasks.push(ReachTask::OpenValueType(domain));
                            tasks.push(ReachTask::OpenCompType(codomain));
                        },
                        | CompType::Element { code, .. } => {
                            tasks.push(ReachTask::OpenValue(code));
                        },
                    }
                },
                | ReachTask::CloseCompType(id) => {
                    let reach = self.combine_comp_type(arena, id);
                    let _prior = self.comp_types.insert(id, reach);
                },
            }
        }
    }

    /// A cached value reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reach already computed for `id`, and the widest reach
    ///   where none is cached.
    /// - provides: the conservative read the combine steps compose, so a gap in
    ///   the cache widens the key's telescope rather than narrowing it.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn cached_value(
        &self,
        id: ValueId,
    ) -> LooseDepth
    {
        self.values.get(&id).copied().unwrap_or(LooseDepth::WIDEST)
    }

    /// A cached computation reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `cached_value`, on the computation plane.
    /// - provides: the conservative read the combine steps compose.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn cached_comp(
        &self,
        id: ComputationId,
    ) -> LooseDepth
    {
        self.computations
            .get(&id)
            .copied()
            .unwrap_or(LooseDepth::WIDEST)
    }

    /// A cached value-type reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `cached_value`, on the value-type plane.
    /// - provides: the conservative read the combine steps compose.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn cached_value_type(
        &self,
        id: ValueTypeId,
    ) -> LooseDepth
    {
        self.value_types
            .get(&id)
            .copied()
            .unwrap_or(LooseDepth::WIDEST)
    }

    /// A cached computation-type reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `cached_value`, on the computation-type plane.
    /// - provides: the conservative read the combine steps compose.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn cached_comp_type(
        &self,
        id: CompTypeId,
    ) -> LooseDepth
    {
        self.comp_types
            .get(&id)
            .copied()
            .unwrap_or(LooseDepth::WIDEST)
    }

    /// Combine one value-type node's children's reaches into its own.
    ///
    /// A type's whole reach comes from the codes it carries: no type former
    /// binds on the positive side, so every arm is the join of its children.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached,
    ///   which the task order establishes.
    /// - ensures: zero for a former carrying no code, the join of the
    ///   children's reaches for a former carrying several, the code's own reach
    ///   for a universe-decoding former, and the widest reach where the node
    ///   could not be read — no positive former binds, so no arm steps out of a
    ///   binder.
    /// - provides: the value-type arm of the bottom-up reach recurrence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed types need no telescope; native universe
    ///   endpoints, list elements and decoded codes retain their greatest loose
    ///   index.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    /// - witness: `support::tests::a_closed_type_goal_reads_no_binder`
    #[spec(ensures: |ret| ret == match arena.value_type(id) {
        None => LooseDepth::WIDEST,
        Some(&ValueType::Base(_) | &ValueType::Unit | &ValueType::Empty | &ValueType::Universe { .. } | &ValueType::Abstract(_)) => LooseDepth(0),
        Some(&ValueType::PathUniverse(a, b)) => self.cached_value(a).join(self.cached_value(b)),
        Some(&ValueType::Product(a, b) | &ValueType::Sum(a, b) | &ValueType::StaticPi { domain: a, codomain: b }) => self.cached_value_type(a).join(self.cached_value_type(b)),
        Some(&ValueType::Session { payloads: inner, .. } | &ValueType::Lift { inner, .. } | &ValueType::List(inner)) => self.cached_value_type(inner),
        Some(&ValueType::Thunk(body)) => self.cached_comp_type(body),
        Some(&ValueType::Element { code, .. }) => self.cached_value(code),
    })]
    fn combine_value_type(
        &self,
        arena: &TermArena,
        id: ValueTypeId,
    ) -> LooseDepth
    {
        let Some(node) = arena.value_type(id)
        else {
            return LooseDepth::WIDEST;
        };
        match *node {
            | ValueType::PathUniverse(source, target) => {
                self.cached_value(source).join(self.cached_value(target))
            },
            | ValueType::Base(_)
            | ValueType::Unit
            | ValueType::Empty
            | ValueType::Universe { .. }
            | ValueType::Abstract(_) => LooseDepth(0),
            | ValueType::Product(first, second)
            | ValueType::Sum(first, second)
            | ValueType::StaticPi {
                domain: first,
                codomain: second,
            } => self
                .cached_value_type(first)
                .join(self.cached_value_type(second)),
            | ValueType::Session {
                payloads: inner, ..
            }
            | ValueType::Lift { inner, .. }
            | ValueType::List(inner) => self.cached_value_type(inner),
            | ValueType::Thunk(body) => self.cached_comp_type(body),
            | ValueType::Element { code, .. } => self.cached_value(code),
        }
    }

    /// Combine one computation-type node's children's reaches into its own.
    ///
    /// The dependent arrow is the one binding former on the negative side: its
    /// codomain is read one binder further out than it computed, and its domain
    /// is not.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached.
    /// - ensures: the join of domain and codomain reaches, with the dependent
    ///   arrow's codomain read one binder further out than it computed, the
    ///   code's own reach for a computation decode, and the widest reach where
    ///   the node could not be read.
    /// - provides: the computation-type arm of the recurrence, and the one
    ///   binding former on the negative side.
    /// - fails: never.
    /// - panics: none.
    fn combine_comp_type(
        &self,
        arena: &TermArena,
        id: CompTypeId,
    ) -> LooseDepth
    {
        let Some(node) = arena.comp_type(id)
        else {
            return LooseDepth::WIDEST;
        };
        match *node {
            | CompType::Returner(result) => self.cached_value_type(result),
            | CompType::Arrow { domain, codomain } => self
                .cached_value_type(domain)
                .join(self.cached_comp_type(codomain)),
            | CompType::Pi { domain, codomain } => self
                .cached_value_type(domain)
                .join(self.cached_comp_type(codomain).under_binder()),
            | CompType::Element { code, .. } => self.cached_value(code),
        }
    }

    /// Combine one value node's children's reaches into its own.
    ///
    /// A variable at index `i` reaches `i + 1` binders — index zero names the
    /// innermost slot. No value former binds, so every other case is the join
    /// of its children.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached.
    /// - ensures: one more than a variable's own index, zero for a closed
    ///   former, the quoted type's reach for a quote, and the join of the
    ///   children's reaches otherwise; the widest reach where the node could
    ///   not be read. No value former binds.
    /// - provides: the value arm of the recurrence, and the base case that
    ///   makes an index a reach.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — free indices set telescope reach; native path
    ///   classifiers and both maps contribute, but evidence has no term
    ///   children.
    /// - witness: `support::tests::a_variable_reaches_one_more_than_its_index`
    /// - witness: `support::tests::a_binder_reading_node_splits_on_its_slice`
    #[spec(ensures: |ret| ret == match arena.value(id) {
        None => LooseDepth::WIDEST,
        Some(&Value::Variable(index)) => LooseDepth(u32::from(index).saturating_add(1)),
        Some(&Value::Constant(_) | &Value::Unit | &Value::Literal(_)) => LooseDepth(0),
        Some(&Value::PathEquiv { path_type, forward, backward, .. }) => self.cached_value_type(path_type).join(self.cached_value(forward)).join(self.cached_value(backward)),
        Some(&Value::SessionPath { path_type, payload_paths, .. }) => self.cached_value_type(path_type).join(self.cached_value(payload_paths)),
        Some(&Value::PathRefl(body) | &Value::Injection(_, body) | &Value::Lift { body, .. }) => self.cached_value(body),
        Some(&Value::PathProduct(a, b) | &Value::Pair(a, b) | &Value::StaticApplication(a, b)) => self.cached_value(a).join(self.cached_value(b)),
        Some(&Value::Thunk(body)) => self.cached_comp(body),
        Some(&Value::Quote(ty)) => self.cached_value_type(ty),
        Some(&Value::QuoteComputation(ty)) => self.cached_comp_type(ty),
    })]
    fn combine_value(
        &self,
        arena: &TermArena,
        id: ValueId,
    ) -> LooseDepth
    {
        let Some(node) = arena.value(id)
        else {
            return LooseDepth::WIDEST;
        };
        match *node {
            | Value::Variable(index) => {
                // reason: an unrepresentable reach conservatively uses the whole context.
                LooseDepth(u32::from(arith::saturating_add(
                    arith::Int::from(u32::from(index)),
                    arith::Int::from(1_u32),
                )))
            },
            | Value::Constant(_) | Value::Unit | Value::Literal(_) => LooseDepth(0),
            | Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => self
                .cached_value_type(path_type)
                .join(self.cached_value(forward))
                .join(self.cached_value(backward)),
            | Value::SessionPath {
                path_type,
                payload_paths,
                ..
            } => self
                .cached_value_type(path_type)
                .join(self.cached_value(payload_paths)),
            | Value::PathRefl(code) => self.cached_value(code),
            | Value::PathProduct(first, second)
            | Value::Pair(first, second)
            | Value::StaticApplication(first, second) => {
                self.cached_value(first).join(self.cached_value(second))
            },
            | Value::Injection(_, body) | Value::Lift { body, .. } => self.cached_value(body),
            | Value::Thunk(body) => self.cached_comp(body),
            | Value::Quote(quoted) => self.cached_value_type(quoted),
            | Value::QuoteComputation(quoted) => self.cached_comp_type(quoted),
        }
    }

    /// Combine one computation node's children's reaches into its own.
    ///
    /// The three binding formers are the whole content: a lambda binds its
    /// argument for the body, a bind binds its payload for the body only (not
    /// for the bound computation), and a case binds each summand for its own
    /// branch only (not for the scrutinee). Each bound position is therefore
    /// read one binder further out than its child computed.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached.
    /// - ensures: the join of the children's reaches, with each bound position
    ///   read one binder further out than its child computed — a lambda's body,
    ///   a bind's body but not its bound computation, and each case branch but
    ///   not the scrutinee; the widest reach where the node could not be read.
    /// - provides: the computation arm of the recurrence, where every binder of
    ///   the term language is accounted for.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bind closes only its body; transport closes neither
    ///   its certificate nor its value, so a free endpoint cannot disappear.
    /// - witness: `support::tests::a_bind_closes_only_its_body`
    /// - witness: `support::tests::a_binder_closes_its_body`
    #[spec(ensures: |ret| ret == match arena.computation(id) {
        None => LooseDepth::WIDEST,
        Some(&Computation::Transport(path, value)) => self.cached_value(path).join(self.cached_value(value)),
        Some(&Computation::Lambda(body)) => self.cached_comp(body).under_binder(),
        Some(&Computation::Application(head, argument)) => self.cached_comp(head).join(self.cached_value(argument)),
        Some(&Computation::Return(value) | &Computation::Force(value) | &Computation::Absurd(value)) => self.cached_value(value),
        Some(&Computation::Bind(bound, body)) => self.cached_comp(bound).join(self.cached_comp(body).under_binder()),
        Some(&Computation::Case { scrutinee, on_left, on_right }) => self.cached_value(scrutinee).join(self.cached_comp(on_left).under_binder()).join(self.cached_comp(on_right).under_binder()),
    })]
    fn combine_comp(
        &self,
        arena: &TermArena,
        id: ComputationId,
    ) -> LooseDepth
    {
        let Some(node) = arena.computation(id)
        else {
            return LooseDepth::WIDEST;
        };
        match *node {
            | Computation::Transport(path, value) => {
                self.cached_value(path).join(self.cached_value(value))
            },
            | Computation::Lambda(body) => self.cached_comp(body).under_binder(),
            | Computation::Application(head, argument) => {
                self.cached_comp(head).join(self.cached_value(argument))
            },
            | Computation::Return(value)
            | Computation::Force(value)
            | Computation::Absurd(value) => self.cached_value(value),
            | Computation::Bind(bound, body) => self
                .cached_comp(bound)
                .join(self.cached_comp(body).under_binder()),
            | Computation::Case {
                scrutinee,
                on_left,
                on_right,
            } => self
                .cached_value(scrutinee)
                .join(self.cached_comp(on_left).under_binder())
                .join(self.cached_comp(on_right).under_binder()),
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_check_memo::ContentAgreement;
    use gandr_kernel_check_memo::MemoKey as _;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::TermArena;

    use super::LooseDepth;
    use super::LooseDepths;
    use super::NodeSupport;
    use super::SupportContext;
    use super::SupportPlane;
    use crate::encoding::SupportGoal;

    #[test]
    fn a_closed_value_reaches_no_binder()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let pair = arena.value_pair(unit, unit);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(0_u32),
            reaches.value_reach(&arena, pair),
            "a closed composite reaches no binder"
        );
    }

    #[test]
    fn a_variable_reaches_one_more_than_its_index()
    {
        let mut arena = TermArena::new();
        let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
        let three = arena.value_variable(DeBruijnIndex::from(3_u32));
        let pair = arena.value_pair(zero, three);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(1_u32),
            reaches.value_reach(&arena, zero),
            "index zero names the innermost slot"
        );
        assert_eq!(
            LooseDepth::from(4_u32),
            reaches.value_reach(&arena, pair),
            "a join takes the wider of the two"
        );
    }

    #[test]
    fn a_binder_closes_its_body()
    {
        let mut arena = TermArena::new();
        let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(zero);
        let lambda = arena.computation_lambda(body);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(1_u32),
            reaches.comp_reach(&arena, body),
            "the body reads its own binder"
        );
        assert_eq!(
            LooseDepth::from(0_u32),
            reaches.comp_reach(&arena, lambda),
            "and from outside the lambda that binder is gone"
        );
    }

    #[test]
    fn a_bind_closes_only_its_body()
    {
        let mut arena = TermArena::new();
        let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.computation_return(zero);
        let body = arena.computation_return(zero);
        let sequence = arena.computation_bind(bound, body);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(1_u32),
            reaches.comp_reach(&arena, sequence),
            "the bound computation keeps its reach while the body loses one, so the join is one"
        );
    }

    #[test]
    fn an_unreadable_node_reaches_widest()
    {
        let mut arena = TermArena::new();
        let floor = arena.watermark();
        let unit = arena.value_unit();
        arena.truncate_to(floor);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(u32::MAX),
            reaches.value_reach(&arena, unit),
            "an unreadable node widens the slice to the whole context rather than narrowing it"
        );
    }

    #[test]
    fn a_closed_node_takes_no_telescope()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let bare = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(unit), &[]);
        let under = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(unit), &[
            unit_type, base,
        ]);
        assert_eq!(
            ContentAgreement::Agree,
            bare.agreement(&under),
            "a closed node means the same thing under every context"
        );
        assert_eq!(SupportPlane::Term, bare.plane(), "and it is a term goal");
    }

    #[test]
    fn a_binder_reading_node_splits_on_its_slice()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let under_unit =
            NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
                unit_type,
            ]);
        let under_base =
            NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
                base,
            ]);
        assert_eq!(
            ContentAgreement::Differ,
            under_unit.agreement(&under_base),
            "the same node under binders of different types is two questions"
        );
    }

    #[test]
    fn a_binder_reading_node_collapses_where_its_slice_agrees()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let shallow =
            NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
                unit_type,
            ]);
        let deep = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
            base, unit_type,
        ]);
        assert_eq!(
            ContentAgreement::Agree,
            shallow.agreement(&deep),
            "only the reached slice is in the key, so contexts agreeing where the node looks are \
             one question"
        );
    }

    /// A type reaches binders exactly through the codes it carries, and the
    /// dependent arrow's codomain steps out by one like every other binder.
    #[test]
    fn a_type_reaches_through_its_codes()
    {
        let mut arena = TermArena::new();
        let zero = Level::zero();
        let closed = arena.value_type_unit();
        let code = arena.value_variable(DeBruijnIndex::from(2_u32));
        let element = arena.value_type_element(code, zero.clone());
        let returner = arena.comp_type_returner(element);
        let universe = arena.value_type_universe(GroundSort::Value, zero);
        let dependent = arena.comp_type_pi(universe, returner);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(0_u32),
            reaches.value_type_reach(&arena, closed),
            "a type carrying no code reaches no binder"
        );
        assert_eq!(
            LooseDepth::from(3_u32),
            reaches.value_type_reach(&arena, element),
            "a type read off a variable code reaches one more than its index"
        );
        assert_eq!(
            LooseDepth::from(2_u32),
            reaches.comp_type_reach(&arena, dependent),
            "and from outside the dependent arrow that binder is gone"
        );
    }

    /// A type-formation goal splits on the binder slice its codes reach, the
    /// same way a term goal does — so one type formed under two different
    /// binders is two entries rather than one.
    #[test]
    fn a_code_carrying_type_reads_its_binder()
    {
        let mut arena = TermArena::new();
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(code, Level::zero());
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let under_unit = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(element),
            &[unit_type],
        );
        let under_base = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(element),
            &[base],
        );
        assert_eq!(
            ContentAgreement::Differ,
            under_unit.agreement(&under_base),
            "the same code-carrying type under binders of different types is two questions"
        );
        assert_eq!(
            SupportPlane::Type,
            under_unit.plane(),
            "and both are accounted to the type-formation plane"
        );
    }

    #[test]
    fn a_closed_type_goal_reads_no_binder()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let bare = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(unit_type),
            &[],
        );
        let under = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(unit_type),
            &[base, unit_type],
        );
        assert_eq!(
            ContentAgreement::Agree,
            bare.agreement(&under),
            "a type carrying no code means the same thing under every context"
        );
        assert_eq!(
            SupportPlane::Type,
            bare.plane(),
            "and the type-formation walk accounts to its own plane"
        );
    }

    #[test]
    fn a_term_support_never_agrees_with_a_type_support()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let mut session = SupportContext::new();
        let term = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(unit), &[]);
        let formation = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(unit_type),
            &[],
        );
        assert_eq!(
            ContentAgreement::Differ,
            term.agreement(&formation),
            "the two machines never answer for one another"
        );
    }
}
