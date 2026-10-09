//! Building a tree: [`TreeBuilder`], the [`StagedId`] it hands out, and the
//! level-order layout it finishes into.
//!
//! # Two id spaces, deliberately different types
//!
//! A parser completes a node once its children are complete, so it mints
//! bottom-up; the arena is laid out top-down. The two orders are different
//! permutations of the same nodes, so a staged identity is not an arena
//! position and the builder never lets one be read as the other. [`StagedId`]
//! is the builder's own currency and stops at [`TreeBuilder::finish`].
//!
//! # A staged identity names its builder
//!
//! A raw position would make two builders' handles interchangeable whenever
//! they had staged the same number of nodes: a handle from one would resolve
//! against the other and lay out an unrelated node, silently. So a [`StagedId`]
//! carries the process-unique identity of the builder that minted it, and every
//! entry point checks it before the position. The counter behind that identity
//! refuses to wrap rather than reissuing a value, because a reissued identity
//! restores exactly the aliasing the stamp removes.
//!
//! # The staged graph is a forest by construction
//!
//! A child must already be staged when its parent is staged, so every edge
//! points at a strictly earlier staged node and no cycle is expressible. A
//! staged node is accepted as a child at most once, so no node has two parents.
//! Together those two make the level-order walk finite without a visited set:
//! it visits each reachable node exactly once.
//!
//! # A refusal leaves the builder at the failure point
//!
//! [`TreeBuilder::node`] attaches children as it validates them, so a call
//! refused partway leaves the children it already accepted attached. The parse
//! that a refusal belongs to has stopped, and unwinding the partial attachment
//! would mean a second traversal whose only consumer is a caller that does not
//! exist. The state is asserted rather than described.

use alloc::vec::Vec;
use core::fmt;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering as AtomicOrdering;

use anodized::spec;

use crate::digest::NodeDigest;
use crate::digest::digest_of;
use crate::error::SyntaxError;
use crate::label::NodeLabel;
use crate::mold::GrammarFingerprint;
use crate::span::ByteSpan;
use crate::span::SourceText;
use crate::tree::ChildCount;
use crate::tree::Node;
use crate::tree::NodeIndex;
use crate::tree::SyntaxTree;

/// The counter every builder draws its identity from.
static NEXT_BUILDER_ID: BuilderIdCounter = BuilderIdCounter(AtomicUsize::new(0_usize));

/// A builder's process-unique identity, stamped into every [`StagedId`] it
/// mints; a handle used against a different builder is rejected.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BuilderId(usize);

/// A counter minting distinct [`BuilderId`]s; exhaustion fails rather than
/// wrapping, so a reissued identity can never alias an extant [`StagedId`].
///
/// The counter is pointer-width so the crate builds on every target with an
/// atomic compare-exchange at all, not only on targets with 64-bit atomics.
#[repr(transparent)]
struct BuilderIdCounter(AtomicUsize);

impl BuilderIdCounter
{
    /// A counter with exactly one distinct identity left to issue.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a counter seeded one below the wrapping point, so its next
    ///   [`BuilderIdCounter::allocate`] succeeds and the one after it refuses.
    /// - provides: the seam that makes the exhaustion refusal reachable from a
    ///   test without issuing `usize::MAX` identities, which is why the
    ///   constructor exists only under `cfg(test)`.
    /// - fails: never.
    /// - panics: none.
    #[cfg(test)]
    #[inline]
    const fn nearly_exhausted() -> Self
    {
        Self(AtomicUsize::new(usize::MAX.wrapping_sub(1_usize)))
    }

    /// Mint the next distinct [`BuilderId`] from this counter.
    ///
    /// # Specification
    /// - requires: nothing; the counter is safe to share across threads.
    /// - ensures: on success the returned identity was never issued by this
    ///   counter before and never will be again.
    /// - provides: the stamp every staged handle carries. The postcondition
    ///   stays prose: it quantifies over every identity this counter has issued
    ///   and will issue, which no predicate over one call states, and any
    ///   per-call reformulation is false under the concurrent sharing the
    ///   precondition admits.
    /// - fails: [`SyntaxError::BuilderIdExhausted`] once the counter would
    ///   wrap, leaving the final identity permanently unissued.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SyntaxError::BuilderIdExhausted`] when no distinct identity remains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the sole decision surface is the `checked_add`
    ///   guard, separated by driving a counter seeded one below the ceiling
    ///   through its last successful issue and then its first refusal, with the
    ///   exact error variant asserted.
    /// - witness: `build::tests::builder_id_exhaustion_is_typed`
    #[inline]
    fn allocate(&self) -> Result<BuilderId, SyntaxError>
    {
        self.0
            .try_update(AtomicOrdering::Relaxed, AtomicOrdering::Relaxed, |next| {
                next.checked_add(1_usize)
            })
            .map(BuilderId)
            .map_err(|_current| SyntaxError::BuilderIdExhausted)
    }
}

/// The identity of a node staged inside one [`TreeBuilder`].
///
/// The identity names its builder as well as the node's staging position, so a
/// handle offered to a different builder is refused rather than resolving
/// against whatever that builder staged at the same position.
///
/// It is not an arena position: the level-order layout permutes the staging
/// order, so reading one as the other would silently name a different node.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StagedId
{
    /// The builder that minted this identity.
    builder: BuilderId,
    /// The node's position in that builder's staging order.
    position: usize,
}

impl fmt::Display for StagedId
{
    /// Write the staged identity as its builder and staging position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the builder's own number, a colon, and the staging
    ///   position, in that order, so two handles from different builders at the
    ///   same position render differently.
    /// - provides: the handle rendering a [`SyntaxError`] carrying a staged
    ///   identity prints.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}:{}", self.builder.0, self.position)
    }
}

/// A resolved position into one builder's staging order.
///
/// Distinct from the raw position inside a [`StagedId`]: a value of this type
/// has already been checked against the builder that is about to read it, which
/// is the whole difference between a handle and an index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct StagingPosition(usize);

/// Whether a staged node has already been accepted as some parent's child.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Attached(bool);

/// One node awaiting layout: everything the arena node needs except its
/// children's arena positions, which layout assigns.
#[derive(Clone, Copy, Debug)]
struct StagedNode
{
    /// What this node is.
    label: NodeLabel,
    /// The bytes of the source this node covers.
    span: ByteSpan,
    /// The content identity, computed when the node was staged.
    digest: NodeDigest,
    /// Where this node's children start in the builder's edge list.
    first_edge: usize,
    /// How many edges follow that position.
    child_count: usize,
    /// Whether some parent has already claimed this node.
    attached: Attached,
}

/// Stages the nodes of one tree and lays them out in level order.
///
/// Deliberately not `Clone`: a clone would carry the original's identity and
/// an equal-length staging vector, so the two would accept each other's
/// handles — reinstating exactly the aliasing the identity removes.
///
/// ```
/// use gandr_surface_syntax::ByteOffset;
/// use gandr_surface_syntax::ByteSpan;
/// use gandr_surface_syntax::GrammarFingerprint;
/// use gandr_surface_syntax::MoldId;
/// use gandr_surface_syntax::NodeLabel;
/// use gandr_surface_syntax::SourceFragment;
/// use gandr_surface_syntax::SourceText;
/// use gandr_surface_syntax::SyntaxError;
/// use gandr_surface_syntax::TreeBuilder;
///
/// fn example() -> Result<(), SyntaxError>
/// {
///     // The mold ids index the table the fingerprint names; these are
///     // illustrative, where a parser reads them from its grammar.
///     let source = SourceText::from("f x");
///     let mut builder = TreeBuilder::new(source, GrammarFingerprint::from(7_u64))?;
///
///     // `?` is a statement, never a subexpression: every fallible step is
///     // bound with `let` before the name is used.
///     let at = |start: usize, end: usize| {
///         ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
///     };
///     let word = NodeLabel::Tile(MoldId::from(4_u32));
///     let head_span = at(0, 1)?;
///     let head = builder.node(word, head_span, &[])?;
///     let gap = at(1, 2)?;
///     let space = builder.node(NodeLabel::Space, gap, &[])?;
///     let argument_span = at(2, 3)?;
///     let argument = builder.node(word, argument_span, &[])?;
///     let whole = at(0, 3)?;
///     let application = builder.node(NodeLabel::Meld(MoldId::from(4_u32)), whole, &[
///         head, space, argument,
///     ])?;
///     let root = builder.node(NodeLabel::Wald, whole, &[application])?;
///     let tree = builder.finish(root)?;
///
///     // A fragment is not a source: it says what a node covers, never what an
///     // offset means.
///     assert_eq!(
///         tree.fragment(tree.root()),
///         Some(SourceFragment::from("f x"))
///     );
///
///     // Level order: every child sits strictly above its parent.
///     for parent in tree.positions() {
///         for child in tree.children(parent) {
///             assert!(usize::from(child) > usize::from(parent));
///         }
///     }
///     Ok(())
/// }
/// example().unwrap();
/// ```
#[derive(Debug)]
pub struct TreeBuilder<'source>
{
    /// This builder's process-unique identity.
    identity: BuilderId,
    /// The text every staged span is validated against.
    source: SourceText<'source>,
    /// The grammar whose mold table the staged labels index.
    grammar: GrammarFingerprint,
    /// The staged nodes, in staging order: children before parents.
    staged: Vec<StagedNode>,
    /// Every staged node's children, in one flat list.
    edges: Vec<StagedId>,
}

impl<'source> TreeBuilder<'source>
{
    /// A builder staging nodes over `source` under `grammar`, with a fresh
    /// identity.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the builder has staged nothing and carries an
    ///   identity no other builder in this process has held or will hold; the
    ///   tree it finishes records `grammar`.
    /// - provides: the only way to obtain a builder, so every staged handle
    ///   carries a stamp. The freshness half is a claim over every builder this
    ///   process has made and will make, which no predicate over one call
    ///   reaches; the empty-staging half alone is the body restated, so the
    ///   line stays prose and the counter's own witness carries it.
    /// - fails: [`SyntaxError::BuilderIdExhausted`] when the process-wide
    ///   identity counter has no distinct value left; construction refuses
    ///   rather than reissuing an identity.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SyntaxError::BuilderIdExhausted`] when no distinct identity remains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the one decision surface is the counter's
    ///   refusal, witnessed on the counter itself where the ceiling is
    ///   reachable; the success arm is exercised by every other witness in this
    ///   module, and the recorded grammar is read back from a finished tree.
    /// - witness: `build::tests::builder_id_exhaustion_is_typed`
    /// - witness: `build::tests::two_builders_take_distinct_identities`
    /// - witness: `build::tests::a_tree_records_its_grammar`
    #[inline]
    pub fn new(
        source: SourceText<'source>,
        grammar: GrammarFingerprint,
    ) -> Result<Self, SyntaxError>
    {
        let identity = NEXT_BUILDER_ID.allocate()?;

        Ok(Self {
            identity,
            source,
            grammar,
            staged: Vec::new(),
            edges: Vec::new(),
        })
    }

    /// Resolve a staged identity against this builder.
    ///
    /// # Specification
    /// - requires: nothing — a foreign or fabricated identity is admissible
    ///   input.
    /// - ensures: the identity's checked staging position when the identity
    ///   carries this builder's stamp and names a node this builder staged.
    /// - provides: the one resolution step every entry point takes, so the
    ///   stamp cannot be checked at one entry point and skipped at another.
    /// - fails: [`SyntaxError::UnknownStagedNode`] when the stamp is another
    ///   builder's or the position names nothing here.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SyntaxError::UnknownStagedNode`] for a foreign stamp or an
    /// out-of-range position.
    #[inline]
    #[spec(ensures: |ret| {
        let resolvable = node.builder == self.identity && node.position < self.staged.len();
        ret.as_ref().ok().map(|position| position.0) == resolvable.then_some(node.position)
    })]
    fn resolve(
        &self,
        node: StagedId,
    ) -> Result<StagingPosition, SyntaxError>
    {
        if node.builder != self.identity || node.position >= self.staged.len() {
            return Err(SyntaxError::UnknownStagedNode { node });
        }

        Ok(StagingPosition(node.position))
    }

    /// Stage a node labelled `label` covering `span` over already-staged
    /// `children`.
    ///
    /// # Specification
    /// - requires: every identity in `children` was minted by this builder and
    ///   has not yet been accepted as a child; `span` lies inside this
    ///   builder's source and does not split a character. Each is checked
    ///   rather than assumed, the builder stamp before the position.
    /// - ensures: on success the node's content digest folds its label, its own
    ///   source fragment when its label carries text, and the digests of its
    ///   significant children in the order given — layout children are kept in
    ///   the tree and left out of the fold — and each child is now attached to
    ///   exactly one parent; the returned identity is fresh.
    /// - provides: the one way to stage a node, so every node in a finished
    ///   tree has a validated span and a digest computed over the same
    ///   preimage. Stating the digest half means rebuilding the child digest
    ///   list this call consumed and hashing the preimage a second time, and
    ///   the exactly-one-parent half is a claim over the whole edge list rather
    ///   than over the flags this call sets; the attachment flags and the
    ///   minted position alone are the body restated, so the line stays prose
    ///   and the pinned digest golden and the witnesses below carry it.
    /// - fails: [`SyntaxError::SpanOutsideSource`] or
    ///   [`SyntaxError::SpanSplitsCharacter`] when the span does not name a
    ///   fragment of the source; [`SyntaxError::UnknownStagedNode`] when a
    ///   child identity carries another builder's stamp or names no node here;
    ///   [`SyntaxError::ChildAlreadyAttached`] when a child already has a
    ///   parent, including a child listed twice in one call. A refusal leaves
    ///   the children accepted before it attached.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SyntaxError::SpanOutsideSource`] and
    /// [`SyntaxError::SpanSplitsCharacter`] from validating `span` against the
    /// source; [`SyntaxError::UnknownStagedNode`] for a child identity stamped
    /// by another builder, or one naming no node here;
    /// [`SyntaxError::ChildAlreadyAttached`] for a child that already has a
    /// parent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — five decision surfaces (the span validation, the
    ///   child lookup, the attachment test, the significance filter, the digest
    ///   fold) separated by a span one byte past the source end, a child
    ///   identity from a second builder, a child offered twice across two calls
    ///   and twice within one call, each asserted as an exact variant with its
    ///   exact payload; a parent over layout and the same parent without it
    ///   asserted one digest; the fold is separated by the digest agreements
    ///   and disagreements the layout witnesses assert.
    /// - witness: `build::tests::a_span_outside_the_source_is_refused_at_mint`
    /// - witness: `build::tests::a_span_splitting_a_character_is_refused_at_mint`
    /// - witness: `build::tests::an_unknown_staged_node_is_refused`
    /// - witness: `build::tests::a_foreign_identity_at_a_live_position_is_refused`
    /// - witness: `build::tests::attaching_a_staged_node_twice_is_refused`
    /// - witness: `build::tests::a_child_listed_twice_in_one_call_is_refused`
    /// - witness: `build::tests::a_refusal_leaves_the_builder_at_the_failure_point`
    /// - witness: `build::tests::layout_never_reaches_a_parent_digest`
    #[inline]
    pub fn node(
        &mut self,
        label: NodeLabel,
        span: ByteSpan,
        children: &[StagedId],
    ) -> Result<StagedId, SyntaxError>
    {
        let fragment = self.source.fragment(span)?;
        let mut digests: Vec<NodeDigest> = Vec::with_capacity(children.len());
        for &child in children {
            let position = self.resolve(child)?;
            let Some(staged) = self.staged.get_mut(position.0)
            else {
                return Err(SyntaxError::UnknownStagedNode { node: child });
            };
            if staged.attached.0 {
                return Err(SyntaxError::ChildAlreadyAttached { node: child });
            }
            staged.attached = Attached(true);
            if bool::from(staged.label.significance()) {
                digests.push(staged.digest);
            }
        }
        let staged = StagedNode {
            label,
            span,
            digest: digest_of(label, fragment, &digests),
            first_edge: self.edges.len(),
            child_count: children.len(),
            attached: Attached(false),
        };
        let minted = StagedId {
            builder: self.identity,
            position: self.staged.len(),
        };
        self.edges.extend_from_slice(children);
        self.staged.push(staged);

        Ok(minted)
    }

    /// Lay the subtree rooted at `root` out in level order.
    ///
    /// # Specification
    /// - requires: `root` was minted by this builder. A staged node that is not
    ///   reachable from `root` is dropped rather than refused, so a parser that
    ///   abandoned a partially built form does not have to unstage it.
    /// - ensures: the tree holds exactly the nodes reachable from `root`, with
    ///   `root` at position zero, every node's children occupying one
    ///   contiguous range of positions strictly above its own, and siblings in
    ///   the order they were given; every node keeps the digest it was staged
    ///   with, so the layout permutes positions and never content.
    /// - provides: the finished tree, and the end of the staged identity space.
    ///   Reachability, `root`'s arrival at position zero, sibling order and
    ///   digest preservation all compare against the staged side, which the
    ///   call consumes, so no predicate over the result reaches them; the
    ///   parent-before-child positions alone are the walk restated, so the line
    ///   stays prose and the layout witnesses carry it.
    /// - fails: [`SyntaxError::UnknownStagedNode`] when `root` carries another
    ///   builder's stamp or names no node here.
    /// - panics: none.
    ///
    /// The walk is a level-order traversal over an explicit queue, so it is
    /// iterative at any tree depth and needs no visited set: the staged graph
    /// is a forest, so each reachable node is enqueued exactly once.
    ///
    /// # Errors
    /// [`SyntaxError::UnknownStagedNode`] when `root` names no staged node of
    /// this builder, whether by a foreign stamp or an out-of-range position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three decision surfaces (the root lookup, the
    ///   first-child cursor, the child-range end) separated by a foreign root
    ///   asserted as an exact variant, by a tree of depth four whose every
    ///   parent-child position pair is asserted, by an exact child position
    ///   list, and by a leaf and an out-of-arena position asserted to yield
    ///   nothing; the digest-preserving half is separated by two builds of one
    ///   source asserted equal digest by digest.
    /// - witness: `build::tests::finishing_from_an_unknown_root_is_refused`
    /// - witness: `build::tests::every_child_sits_above_its_parent`
    /// - witness: `build::tests::children_are_contiguous_and_in_source_order`
    /// - witness: `build::tests::a_leaf_has_no_children`
    /// - witness: `build::tests::a_position_past_the_arena_has_no_children`
    /// - witness: `build::tests::the_root_is_the_first_position`
    /// - witness: `build::tests::two_builds_of_one_source_agree_digest_by_digest`
    /// - witness: `build::tests::an_unreachable_staged_node_is_dropped`
    /// - witness: `build::tests::the_same_subtree_in_two_sources_shares_its_digest`
    /// - witness: `build::tests::an_edit_reaches_exactly_the_edited_node_and_its_ancestors`
    /// - witness: `build::tests::a_tree_records_its_grammar`
    /// - witness: `build::tests::a_foreign_identity_at_a_live_position_is_refused`
    #[inline]
    pub fn finish(
        self,
        root: StagedId,
    ) -> Result<SyntaxTree<'source>, SyntaxError>
    {
        let mut order: Vec<StagedId> = Vec::with_capacity(self.staged.len());
        let mut nodes: Vec<Node> = Vec::with_capacity(self.staged.len());
        order.push(root);
        let mut cursor = 0_usize;
        while let Some(staged_id) = order.get(cursor).copied() {
            let position = self.resolve(staged_id)?;
            let Some(staged) = self.staged.get(position.0)
            else {
                return Err(SyntaxError::UnknownStagedNode { node: staged_id });
            };
            let first_child = NodeIndex::from(order.len());
            let edge_end = staged.first_edge.saturating_add(staged.child_count);
            let edges = self.edges.get(staged.first_edge .. edge_end).unwrap_or(&[]);
            order.extend_from_slice(edges);
            nodes.push(Node::new(
                staged.label,
                staged.span,
                staged.digest,
                first_child,
                ChildCount::from(staged.child_count),
            ));
            cursor = cursor.saturating_add(1_usize);
        }

        Ok(SyntaxTree::from_layout(self.source, self.grammar, nodes))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::vec::Vec;

    use super::TreeBuilder;
    use crate::error::SyntaxError;
    use crate::label::NodeLabel;
    use crate::mold::GrammarFingerprint;
    use crate::mold::MoldId;
    use crate::span::ByteOffset;
    use crate::span::ByteSpan;
    use crate::span::SourceFragment;
    use crate::span::SourceText;
    use crate::tree::ChildCount;
    use crate::tree::Node;
    use crate::tree::NodeCount;
    use crate::tree::NodeIndex;
    use crate::tree::SyntaxTree;

    /// The fixture source: one definition whose body is a lambda over a
    /// returner, which is the shallowest shape reaching depth four.
    const LAMBDA_SOURCE: &str = r#"def f = \x. return x ;"#;

    /// The grammar every fixture tree is built under.
    ///
    /// # Specification
    /// trivial.
    fn grammar() -> GrammarFingerprint
    {
        GrammarFingerprint::from(0x5eed_u64)
    }

    /// The tile every name in the fixtures molds to.
    ///
    /// # Specification
    /// trivial.
    fn word() -> NodeLabel
    {
        NodeLabel::Tile(MoldId::from(1_u32))
    }

    /// A tile of a second mold, distinct from [`word`].
    ///
    /// # Specification
    /// trivial.
    fn literal() -> NodeLabel
    {
        NodeLabel::Tile(MoldId::from(5_u32))
    }

    /// The definition form.
    ///
    /// # Specification
    /// trivial.
    fn definition() -> NodeLabel
    {
        NodeLabel::Meld(MoldId::from(2_u32))
    }

    /// The lambda form.
    ///
    /// # Specification
    /// trivial.
    fn lambda() -> NodeLabel
    {
        NodeLabel::Meld(MoldId::from(3_u32))
    }

    /// The returner form.
    ///
    /// # Specification
    /// trivial.
    fn returner() -> NodeLabel
    {
        NodeLabel::Meld(MoldId::from(4_u32))
    }

    /// Mint a span from two offsets, for a test that is not about minting.
    ///
    /// # Specification
    /// - requires: `start` is at or below `end`; a test about minting offers an
    ///   inverted pair to [`ByteSpan::new`] itself.
    /// - ensures: the span carrying exactly those endpoints.
    /// - provides: the span every fixture below is read against.
    /// - panics: when the endpoints are inverted, so a fixture that violates
    ///   the precondition fails its own test rather than staging a span the
    ///   crate would have refused.
    fn span(
        start: ByteOffset,
        end: ByteOffset,
    ) -> ByteSpan
    {
        ByteSpan::new(start, end).unwrap()
    }

    /// Build the fixture tree over `source`, whose declaration starts `padding`
    /// bytes in.
    ///
    /// The shape is `Wald [ definition [ word, lambda [ word, returner [ word
    /// ] ] ] ]`, whose deepest path is four edges long.
    ///
    /// # Specification
    /// - requires: `source` holds at least `padding + 22` bytes, and every
    ///   shifted span below falls on a character boundary of it.
    /// - ensures: the finished tree of that shape over `source`, with each
    ///   node's span shifted by `padding`.
    /// - provides: the depth-four fixture the layout, walk, and fragment
    ///   assertions below all read.
    /// - panics: when any staged span is refused against `source` or the layout
    ///   fails, so a fixture that no longer matches its source fails loudly
    ///   rather than asserting over a truncated tree.
    fn lambda_tree(
        source: SourceText<'_>,
        padding: ByteOffset,
    ) -> SyntaxTree<'_>
    {
        let mut builder = TreeBuilder::new(source, grammar()).unwrap();
        let shift = usize::from(padding);
        let at = |start: usize, end: usize| {
            span(
                ByteOffset::from(start.saturating_add(shift)),
                ByteOffset::from(end.saturating_add(shift)),
            )
        };
        let name = builder.node(word(), at(4, 5), &[]).unwrap();
        let binder = builder.node(word(), at(9, 10), &[]).unwrap();
        let body = builder.node(word(), at(19, 20), &[]).unwrap();
        let returned = builder.node(returner(), at(12, 20), &[body]).unwrap();
        let abstraction = builder
            .node(lambda(), at(8, 20), &[binder, returned])
            .unwrap();
        let declaration = builder
            .node(definition(), at(0, 22), &[name, abstraction])
            .unwrap();
        let root = builder
            .node(NodeLabel::Wald, at(0, 22), &[declaration])
            .unwrap();

        builder.finish(root).unwrap()
    }

    /// The refusal fixture: two one-byte characters, so every span the refusal
    /// tests need is one of the four named below.
    const REFUSAL_SOURCE: &str = "ab";

    /// A fixture whose first character is two bytes wide, so a span endpoint
    /// can fall inside a character at mint.
    const ACCENTED_SOURCE: &str = "\u{e9}ab";

    /// The span of the refusal fixture's first byte.
    ///
    /// # Specification
    /// trivial.
    fn first_byte() -> ByteSpan
    {
        span(ByteOffset::from(0_usize), ByteOffset::from(1_usize))
    }

    /// The span of the refusal fixture's second byte.
    ///
    /// # Specification
    /// trivial.
    fn second_byte() -> ByteSpan
    {
        span(ByteOffset::from(1_usize), ByteOffset::from(2_usize))
    }

    /// The span of the whole refusal fixture.
    ///
    /// # Specification
    /// trivial.
    fn whole_fixture() -> ByteSpan
    {
        span(ByteOffset::from(0_usize), ByteOffset::from(2_usize))
    }

    /// A span reaching one byte past the refusal fixture's end.
    ///
    /// # Specification
    /// trivial.
    fn past_fixture_end() -> ByteSpan
    {
        span(ByteOffset::from(0_usize), ByteOffset::from(3_usize))
    }

    /// The positions a node's children occupy, as a list.
    ///
    /// # Specification
    /// - requires: nothing — a position the tree does not hold yields the empty
    ///   list, which is what the fail-closed cases below assert.
    /// - ensures: the node's children in the order the walk yields them.
    /// - provides: the comparable form the position assertions below are
    ///   written against.
    /// - panics: none.
    fn children(
        tree: &SyntaxTree<'_>,
        position: NodeIndex,
    ) -> Vec<NodeIndex>
    {
        tree.children(position).collect()
    }

    #[test]
    fn the_root_is_the_first_position()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            tree.root(),
            NodeIndex::from(0_usize),
            "the level-order layout puts the root first"
        );
        assert_eq!(
            tree.node(tree.root()).map(Node::label),
            Some(NodeLabel::Wald),
            "position zero holds the node finish was called with"
        );
        assert_eq!(
            tree.node_count(),
            NodeCount::from(7_usize),
            "the fixture lays out seven nodes"
        );
    }

    #[test]
    fn every_child_sits_above_its_parent()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));
        let mut edges = 0_usize;
        for parent in tree.positions() {
            for child in tree.children(parent) {
                assert!(
                    usize::from(child) > usize::from(parent),
                    "a child position is strictly above its parent's"
                );
                edges = edges.saturating_add(1_usize);
            }
        }

        assert_eq!(
            edges, 6_usize,
            "a seven-node tree has six parent-child edges, so the walk saw them all"
        );
    }

    #[test]
    fn children_are_contiguous_and_in_source_order()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            children(&tree, NodeIndex::from(0_usize)),
            [NodeIndex::from(1_usize)],
            "the root holds one declaration"
        );
        assert_eq!(
            children(&tree, NodeIndex::from(1_usize)),
            [NodeIndex::from(2_usize), NodeIndex::from(3_usize)],
            "the definition's name precedes its body, at adjacent positions"
        );
        assert_eq!(
            children(&tree, NodeIndex::from(3_usize)),
            [NodeIndex::from(4_usize), NodeIndex::from(5_usize)],
            "the lambda's binder precedes its body, at adjacent positions"
        );
        assert_eq!(
            children(&tree, NodeIndex::from(5_usize)),
            [NodeIndex::from(6_usize)],
            "the returner holds one value"
        );
    }

    #[test]
    fn a_leaf_has_no_children()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert!(
            children(&tree, NodeIndex::from(2_usize)).is_empty(),
            "a text leaf yields no child positions"
        );
        assert_eq!(
            tree.node(NodeIndex::from(2_usize)).map(Node::child_count),
            Some(ChildCount::from(0_usize)),
            "and reports a child count of zero"
        );
    }

    #[test]
    fn a_position_past_the_arena_has_no_children()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert!(
            children(&tree, NodeIndex::from(7_usize)).is_empty(),
            "one position past the last node yields nothing rather than panicking"
        );
    }

    #[test]
    fn a_node_names_the_fragment_it_spans()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            tree.fragment(NodeIndex::from(2_usize)),
            Some(SourceFragment::from("f")),
            "the defined name's fragment is its identifier"
        );
        assert_eq!(
            tree.fragment(NodeIndex::from(5_usize)),
            Some(SourceFragment::from("return x")),
            "a structural node's fragment is everything it covers"
        );
    }

    #[test]
    fn the_last_position_holds_a_node()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            tree.node(NodeIndex::from(6_usize)).map(Node::label),
            Some(word()),
            "one below the node count is the last position that resolves"
        );
    }

    #[test]
    fn a_position_past_the_arena_holds_no_node()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            tree.node(NodeIndex::from(7_usize)).map(Node::label),
            None,
            "the node count itself is the first position that does not"
        );
    }

    #[test]
    fn a_span_splitting_a_character_is_refused_at_mint()
    {
        // `REFUSAL_SOURCE` is all one-byte characters, so the boundary fault
        // needs a fixture that actually has a multi-byte character in it.
        let mut builder = TreeBuilder::new(SourceText::from(ACCENTED_SOURCE), grammar()).unwrap();

        assert_eq!(
            builder.node(
                word(),
                span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                &[]
            ),
            Err(SyntaxError::SpanSplitsCharacter {
                offset: ByteOffset::from(1_usize),
            }),
            "a span ending inside the two-byte character is refused at mint"
        );
    }

    #[test]
    fn a_position_past_the_arena_names_no_fragment()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            tree.fragment(NodeIndex::from(7_usize)),
            None,
            "one position past the last node names no fragment"
        );
    }

    #[test]
    fn two_builds_of_one_source_agree_digest_by_digest()
    {
        let first = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));
        let second = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            first.node_count(),
            second.node_count(),
            "two builds of one source lay out the same number of nodes"
        );
        for position in first.positions() {
            assert_eq!(
                first.node(position).map(Node::digest),
                second.node(position).map(Node::digest),
                "a node's identity is a function of its content alone"
            );
        }
    }

    #[test]
    fn the_same_subtree_in_two_sources_shares_its_digest()
    {
        let padded_source = format!("        {LAMBDA_SOURCE}");
        let plain = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));
        let padded = lambda_tree(
            SourceText::from(padded_source.as_str()),
            ByteOffset::from(8_usize),
        );
        let definition = NodeIndex::from(1_usize);

        assert_eq!(
            plain.node(definition).map(Node::digest),
            padded.node(definition).map(Node::digest),
            "the same declaration at two offsets carries one identity"
        );
        assert_ne!(
            plain.node(definition).map(Node::span),
            padded.node(definition).map(Node::span),
            "while its position in its own source differs"
        );
    }

    #[test]
    fn an_edit_reaches_exactly_the_edited_node_and_its_ancestors()
    {
        let renamed_source = LAMBDA_SOURCE.replace("def f", "def g");
        let before = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));
        let after = lambda_tree(
            SourceText::from(renamed_source.as_str()),
            ByteOffset::from(0_usize),
        );
        let changed = [0_usize, 1_usize, 2_usize];
        let unchanged = [3_usize, 4_usize, 5_usize, 6_usize];

        for position in changed {
            assert_ne!(
                before.node(NodeIndex::from(position)).map(Node::digest),
                after.node(NodeIndex::from(position)).map(Node::digest),
                "the renamed leaf and every ancestor of it acquire new identities"
            );
        }
        for position in unchanged {
            assert_eq!(
                before.node(NodeIndex::from(position)).map(Node::digest),
                after.node(NodeIndex::from(position)).map(Node::digest),
                "nothing outside that path moves"
            );
        }
    }

    #[test]
    fn layout_never_reaches_a_parent_digest()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut spaced = TreeBuilder::new(SourceText::from("f  x"), grammar()).unwrap();
        let head = spaced.node(word(), at(0, 1), &[]).unwrap();
        let gap = spaced.node(NodeLabel::Space, at(1, 3), &[]).unwrap();
        let argument = spaced.node(word(), at(3, 4), &[]).unwrap();
        let form = spaced
            .node(definition(), at(0, 4), &[head, gap, argument])
            .unwrap();
        let root = spaced.node(NodeLabel::Wald, at(0, 4), &[form]).unwrap();
        let spaced_tree = spaced.finish(root).unwrap();

        let mut tight = TreeBuilder::new(SourceText::from("fx"), grammar()).unwrap();
        let head = tight.node(word(), at(0, 1), &[]).unwrap();
        let argument = tight.node(word(), at(1, 2), &[]).unwrap();
        let form = tight
            .node(definition(), at(0, 2), &[head, argument])
            .unwrap();
        let root = tight.node(NodeLabel::Wald, at(0, 2), &[form]).unwrap();
        let tight_tree = tight.finish(root).unwrap();

        assert_eq!(
            spaced_tree.node(NodeIndex::from(1_usize)).map(Node::digest),
            tight_tree.node(NodeIndex::from(1_usize)).map(Node::digest),
            "a form over layout has the identity of the same form without it"
        );
        assert_eq!(
            spaced_tree.node(spaced_tree.root()).map(Node::digest),
            tight_tree.node(tight_tree.root()).map(Node::digest),
            "and so does every ancestor"
        );
        assert_eq!(
            spaced_tree.node(NodeIndex::from(3_usize)).map(Node::label),
            Some(NodeLabel::Space),
            "while the layout stays in the tree, between the tiles it separates"
        );
        assert_eq!(
            spaced_tree.fragment(NodeIndex::from(3_usize)),
            Some(SourceFragment::from("  ")),
            "covering exactly the bytes it was staged over"
        );
    }

    #[test]
    fn a_tree_records_its_grammar()
    {
        let tree = lambda_tree(SourceText::from(LAMBDA_SOURCE), ByteOffset::from(0_usize));

        assert_eq!(
            tree.grammar(),
            grammar(),
            "the finished tree names the grammar its builder was opened under"
        );
    }

    #[test]
    fn a_span_outside_the_source_is_refused_at_mint()
    {
        let mut builder = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();

        assert_eq!(
            builder.node(word(), past_fixture_end(), &[]),
            Err(SyntaxError::SpanOutsideSource {
                span: past_fixture_end(),
                source_end: ByteOffset::from(2_usize),
            }),
            "a span one byte past the source end is refused at mint"
        );
    }

    #[test]
    fn an_unknown_staged_node_is_refused()
    {
        let mut first = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let foreign = first.node(word(), first_byte(), &[]).unwrap();
        let mut second = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();

        assert_eq!(
            second.node(NodeLabel::Wald, whole_fixture(), &[foreign]),
            Err(SyntaxError::UnknownStagedNode { node: foreign }),
            "an identity from another builder resolves to nothing here"
        );
    }

    #[test]
    fn a_foreign_identity_at_a_live_position_is_refused()
    {
        // The boundary the stamp exists for: both builders have staged one
        // node, so the foreign identity's raw position is in range here. With a
        // bare position this call would silently adopt the local node.
        let mut first = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let foreign = first.node(word(), first_byte(), &[]).unwrap();
        let mut second = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let local = second.node(literal(), first_byte(), &[]).unwrap();

        assert_ne!(
            foreign, local,
            "two builders' handles at one position are distinct values"
        );
        assert_eq!(
            second.node(NodeLabel::Wald, whole_fixture(), &[foreign]),
            Err(SyntaxError::UnknownStagedNode { node: foreign }),
            "a foreign identity is refused even where the position resolves"
        );
        assert_eq!(
            second.finish(foreign).err(),
            Some(SyntaxError::UnknownStagedNode { node: foreign }),
            "and refused as a root on the same ground"
        );
    }

    #[test]
    fn two_builders_take_distinct_identities()
    {
        let mut first = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let mut second = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let from_first = first.node(word(), first_byte(), &[]).unwrap();
        let from_second = second.node(word(), first_byte(), &[]).unwrap();

        assert_ne!(
            from_first, from_second,
            "a fresh builder never reuses a live builder's identity"
        );
    }

    #[test]
    fn builder_id_exhaustion_is_typed()
    {
        let counter = super::BuilderIdCounter::nearly_exhausted();

        assert!(
            counter.allocate().is_ok(),
            "the last distinct identity is issued"
        );
        assert_eq!(
            counter.allocate(),
            Err(SyntaxError::BuilderIdExhausted),
            "the counter refuses rather than wrapping into a reissued identity"
        );
    }

    #[test]
    fn attaching_a_staged_node_twice_is_refused()
    {
        let mut builder = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let leaf = builder.node(word(), first_byte(), &[]).unwrap();
        let _first = builder
            .node(NodeLabel::Wald, whole_fixture(), &[leaf])
            .unwrap();

        assert_eq!(
            builder.node(NodeLabel::Wald, whole_fixture(), &[leaf]),
            Err(SyntaxError::ChildAlreadyAttached { node: leaf }),
            "a staged node has at most one parent"
        );
    }

    #[test]
    fn a_child_listed_twice_in_one_call_is_refused()
    {
        let mut builder = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let leaf = builder.node(word(), first_byte(), &[]).unwrap();

        assert_eq!(
            builder.node(NodeLabel::Wald, whole_fixture(), &[leaf, leaf]),
            Err(SyntaxError::ChildAlreadyAttached { node: leaf }),
            "the attachment is recorded as each child is accepted, so a repeat \
             inside one call is caught as well"
        );
    }

    #[test]
    fn a_refusal_leaves_the_builder_at_the_failure_point()
    {
        let mut builder = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let first = builder.node(word(), first_byte(), &[]).unwrap();
        let second = builder.node(word(), second_byte(), &[]).unwrap();
        let refused = builder.node(NodeLabel::Wald, whole_fixture(), &[first, second, second]);

        assert_eq!(
            refused,
            Err(SyntaxError::ChildAlreadyAttached { node: second }),
            "the third child repeats the second"
        );
        assert_eq!(
            builder.node(NodeLabel::Wald, whole_fixture(), &[first]),
            Err(SyntaxError::ChildAlreadyAttached { node: first }),
            "the children accepted before the refusal stay attached"
        );
    }

    #[test]
    fn finishing_from_an_unknown_root_is_refused()
    {
        let mut first = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let foreign = first.node(word(), first_byte(), &[]).unwrap();
        let second = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();

        assert_eq!(
            second.finish(foreign).err(),
            Some(SyntaxError::UnknownStagedNode { node: foreign }),
            "a root from another builder lays out nothing"
        );
    }

    #[test]
    fn an_unreachable_staged_node_is_dropped()
    {
        let mut builder = TreeBuilder::new(SourceText::from(REFUSAL_SOURCE), grammar()).unwrap();
        let kept = builder.node(word(), first_byte(), &[]).unwrap();
        let _abandoned = builder.node(word(), second_byte(), &[]).unwrap();
        let root = builder
            .node(NodeLabel::Wald, whole_fixture(), &[kept])
            .unwrap();
        let tree = builder.finish(root).unwrap();

        assert_eq!(
            tree.node_count(),
            NodeCount::from(2_usize),
            "a staged node no parent claimed does not reach the arena"
        );
    }
}
