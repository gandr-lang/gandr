//! The null/ordered differential: **memoless and memoized are one function at
//! two type parameters**, not two implementations.
//!
//! The workload is a flat, id-addressed arena of shared nodes and one
//! defunctionalized walk over it. The walk is generic in the memo, guards every
//! memo interaction — support construction included — on the compile-time
//! activity constant, and is instantiated twice. Nothing about it is a second
//! implementation of anything: the memoless side is the same `evaluate` at
//! [`NullMemo`].
//!
//! Three properties are asserted, and the third is what stops the first two
//! from being vacuous.
//!
//! - **Zero drift.** The two instantiations agree outcome for outcome, on the
//!   shared composite and on its fully unshared spelling, at every depth.
//! - **The collapse, as a closed form.** The memoless walk makes `2^(d+1) - 1`
//!   goal expansions per plane; the memoized walk makes `d + 1`. Asserted at
//!   three depths rather than sampled, per plane, and the memo's own entry
//!   count is compared against the expansion count from the other direction.
//! - **Anti-vacuity.** A workload that quietly lost its sharing would report a
//!   memoless count equal to its memoized count. So the occurrence count is
//!   pinned twice over — once by the tally and once by the machine's own
//!   weight-plane answer — the hit counts are asserted exactly rather than
//!   reported, and a separate case pins that the shared composite and its fully
//!   unshared spelling cost the **memoless** walk identically, which is the
//!   statement that sharing buys this walk nothing without the memo.
//!
//! The support is content-derived, so the unshared spelling collapses under the
//! memo exactly as the shared one does — which is the content key's payoff
//! stated as a number rather than as an argument.

extern crate alloc;
use alloc::collections::BTreeMap;

use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::MemoEntryCount;
use gandr_kernel_check_memo::MemoError;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_check_memo::OrderedMemo;

/// A failure of the harness, as distinct from a disagreement between the two
/// instantiations.
///
/// A disagreement is an assertion, because that is the property under test. The
/// variants here are the ways the harness can fail to do what it intended —
/// none of which a well-formed arena should be able to produce, so each one
/// surfacing is itself a finding rather than a panic buried in a helper.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WorkloadError
{
    /// A node identifier did not resolve in the arena.
    NodeOutOfRange,
    /// A node's content encoding had not been computed when it was demanded.
    MissingEncoding,
    /// A content encoding exceeded the length its prefix can express.
    EncodingTooLong,
    /// The machine popped an operand that was never pushed.
    ResultStackUnderflow,
    /// The machine finished with operands left over.
    ResultStackResidue,
    /// A weight exceeded the range its counter can express.
    WeightOverflow,
    /// A tally exceeded the range its counter can express.
    TallyOverflow,
    /// A depth exceeded the range its closed forms can express.
    DepthOverflow,
    /// The unshared builder was handed a level with an odd number of nodes.
    OddLevel,
    /// The memo served an entry whose support does not agree with the demanded
    /// one — the pointwise adoption check a hit's carried support exists for.
    ServedSupportDisagrees,
    /// The memo declined to record.
    Memo(MemoError),
}

/// A zero-based index into an [`Arena`]'s node vector.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NodeId(usize);

/// The payload of a leaf.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LeafTag(u8);

/// The depth of a composite: the number of pair levels above its leaves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Depth(u32);

/// An answer the walk produces for one node on one plane.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Outcome(u64);

/// A count of goal expansions or of memo hits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct WalkCount(u64);

impl WalkCount
{
    /// The next count up.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count one greater than `self` when representable.
    /// - provides: the only way this harness increments a tally, so no bare
    ///   overflowing arithmetic runs on a number an assertion reads.
    /// - fails: `WorkloadError::TallyOverflow` at the ceiling, rather than
    ///   wrapping to zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — any u64 count is admitted; zero and MAX - 1 have
    ///   exact successors, while MAX must return `TallyOverflow`. Exact values
    ///   separate a missing increment, an early ceiling and wrapping.
    /// - witness: `differential::tests::counter_arithmetic_boundaries`
    #[anodized::spec(ensures: |ret| ret.map(|count| count.0) == self.0.checked_add(1).ok_or(WorkloadError::TallyOverflow))]
    fn successor(self) -> Result<Self, WorkloadError>
    {
        self.0
            .checked_add(1)
            .map_or(Err(WorkloadError::TallyOverflow), |next| Ok(Self(next)))
    }
}

/// The canonical content encoding of a node: tagged, length-prefixed, and
/// prefix-free, so it is injective and mirrors the node relation exactly.
///
/// # Specification
/// - requires: bytes were produced from the tagged, length-framed node grammar.
/// - ensures: equal encodings denote equal ordered trees, without arena
///   indices.
/// - provides: the deciding content carried by the workload support.
/// - panics: none.
/// - executable: none — the original tree is external to these bytes, and
///   data-item construction does not invoke the predicate expansion.
///
/// # Adequacy
/// - hypothesis: L3 — leaf tags and ordered pairs have exact framed bytes;
///   reversing unequal children must change the encoding. L1 the unshared
///   spelling collapses by content despite distinct arena positions.
/// - witness: `differential::tests::arena_and_framing_boundaries`
/// - witness: `differential::tests::a_content_key_collapses_the_unshared_spelling_too`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct ContentEncoding(Vec<u8>);

/// The byte that distinguishes one plane from another inside an encoding.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlaneTag(u8);

/// The accounting partition an expansion is charged to.
///
/// Two planes, because a memo covering one plane of a two-machine walk buys a
/// small constant against an exponential capability. Both consult one memo and
/// each is asserted separately.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Plane
{
    /// An order-sensitive fold, standing in for a term-checking machine.
    Value,
    /// The size of the node's tree expansion, standing in for a type-formation
    /// walk — and, incidentally, the occurrence count the tally must match.
    Weight,
}

impl Plane
{
    /// The byte a plane contributes to a support's encoding, so the same node
    /// on two planes is two different questions.
    ///
    /// # Specification
    /// trivial.
    const fn tag(self) -> PlaneTag
    {
        match self {
            | Self::Value => PlaneTag(0x10),
            | Self::Weight => PlaneTag(0x11),
        }
    }

    /// The answer for a leaf.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value plane answers the leaf's own tag and the weight
    ///   plane answers one, so the weight plane's total over a term is that
    ///   term's occurrence count.
    /// - provides: the base case of both machines.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and a nonzero leaf tag on both planes separate
    ///   payload-dependent value from constant unit weight by exact outcomes.
    /// - witness: `differential::tests::plane_fold_boundaries`
    #[anodized::spec(ensures: |ret| ret == match self { Plane::Value => Outcome(u64::from(tag.0)), Plane::Weight => Outcome(1) })]
    fn leaf_outcome(
        self,
        tag: LeafTag,
    ) -> Outcome
    {
        match self {
            | Self::Value => Outcome(u64::from(tag.0)),
            | Self::Weight => Outcome(1),
        }
    }

    /// The answer for a pair, from its two operands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value plane answers an order-sensitive bitwise fold; the
    ///   weight plane answers one more than the sum of its operands, counting
    ///   the pair node itself.
    /// - provides: the inductive case of both machines.
    /// - fails: `WorkloadError::WeightOverflow` when a weight sum leaves the
    ///   range its counter can express.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — for arbitrary operand words, the weight result is the
    ///   u128 sum plus one, narrowed only at the end. L3 asymmetric operands
    ///   separate the value-plane order; zero, MAX - 1 and MAX separate
    ///   ordinary weight, final-step overflow and operand-sum overflow.
    /// - witness: `differential::tests::plane_fold_boundaries`
    #[anodized::spec(ensures: |ret| match self {
        Plane::Value => ret == Ok(Outcome(left.0.rotate_left(1) ^ right.0.rotate_left(3) ^ 0x9e37_79b9)),
        Plane::Weight => ret.map(|outcome| u128::from(outcome.0))
            == u128::from(left.0).checked_add(u128::from(right.0)).and_then(|sum| sum.checked_add(1))
                .filter(|sum| *sum <= u128::from(u64::MAX)).ok_or(WorkloadError::WeightOverflow),
    })]
    fn combine(
        self,
        left: Outcome,
        right: Outcome,
    ) -> Result<Outcome, WorkloadError>
    {
        match self {
            // Bitwise and total; the two rotations give the operands different roles.
            | Self::Value => Ok(Outcome(
                left.0.rotate_left(1) ^ right.0.rotate_left(3) ^ 0x9e37_79b9,
            )),
            | Self::Weight => {
                let operands = left
                    .0
                    .checked_add(right.0)
                    .ok_or(WorkloadError::WeightOverflow)?;
                let total = operands
                    .checked_add(1)
                    .ok_or(WorkloadError::WeightOverflow)?;
                Ok(Outcome(total))
            },
        }
    }
}

/// A node of the workload arena.
///
/// Children are named by identifier and are always strictly earlier than their
/// parent, so the structure is flat, acyclic, and id-addressed, and content
/// encodings can be computed in one forward pass.
///
/// # Specification
/// - requires: pair operands name earlier nodes in the enclosing arena.
/// - ensures: a node contributes a leaf or an ordered pair, never an arena
///   cycle.
/// - provides: finite bottom-up content construction and stack-based
///   evaluation.
/// - panics: none.
/// - executable: none — the enclosing arena and the node's position are not
///   retained in one node value; builders check the boundary instead.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf and an ordered pair over earlier children
///   distinguish the two cases and operand order by exact nodes and encodings.
///   The first and last minted indices are resolved; an index at the length is
///   refused.
/// - witness: `differential::tests::arena_and_framing_boundaries`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Node
{
    /// A leaf carrying a tag.
    Leaf(LeafTag),
    /// A pair of strictly-earlier children.
    Pair
    {
        /// The left child.
        left: NodeId,
        /// The right child.
        right: NodeId,
    },
}

/// The workload arena: nodes, and the content encoding of each.
///
/// # Specification
/// - requires: the nodes are topological and each stored encoding denotes the
///   node at the same index; a complete arena has one encoding per node.
/// - ensures: identifiers select the same ordered tree through both views.
/// - provides: shared and unshared spellings of one finite workload.
/// - panics: none.
/// - executable: none — data-item predicates do not run at construction; lookup
///   and builder operations check their individual boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — empty and populated arenas separate absent indices from
///   minted leaves and ordered pairs by exact values and encodings. L1 the
///   depth-zero and depth-one spellings separate identity from sharing, while
///   closed-form counts at three larger depths detect topology mistakes.
/// - witness: `differential::tests::arena_and_framing_boundaries`
/// - witness: `differential::tests::workload_shape_boundaries`
/// - witness: `differential::tests::the_collapse_is_a_closed_form_at_three_depths`
#[derive(Clone, Debug)]
struct Arena
{
    /// The nodes, children before parents.
    nodes: Vec<Node>,
    /// The canonical content encoding of each node, at the same index.
    encodings: Vec<ContentEncoding>,
}

impl Arena
{
    /// An arena holding nothing.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        Self {
            nodes: Vec::new(),
            encodings: Vec::new(),
        }
    }

    /// The node at `id`.
    ///
    /// # Specification
    /// - requires: nothing; an identifier the arena never minted is admissible
    ///   input and is refused.
    /// - ensures: the node minted at `id`.
    /// - provides: the node lookup the walk expands through.
    /// - fails: `WorkloadError::NodeOutOfRange` for an identifier past the
    ///   arena's own nodes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, first, last and one-past-end lookups
    ///   distinguish index shifts and false success by exact `Node` values or
    ///   `NodeOutOfRange`.
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(ensures: |ret| ret == self.nodes.get(id.0).copied().ok_or(WorkloadError::NodeOutOfRange))]
    fn node(
        &self,
        id: NodeId,
    ) -> Result<Node, WorkloadError>
    {
        self.nodes
            .get(id.0)
            .map_or(Err(WorkloadError::NodeOutOfRange), |node| Ok(*node))
    }

    /// The content encoding of the node at `id`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the encoding recorded for the node at `id` when the arena
    ///   holds one.
    /// - provides: the deciding datum a support carries.
    /// - fails: `WorkloadError::MissingEncoding` when no encoding is recorded
    ///   at that index, which covers an out-of-range identifier as well as a
    ///   node whose encoding was never computed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf and pair encodings at minted indices, and empty
    ///   or one-past-end lookup, distinguish mismatched indices and a
    ///   fabricated encoding by exact bytes or `MissingEncoding`.
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(ensures: |ret| ret == self.encodings.get(id.0).ok_or(WorkloadError::MissingEncoding))]
    fn encoding(
        &self,
        id: NodeId,
    ) -> Result<&ContentEncoding, WorkloadError>
    {
        self.encodings
            .get(id.0)
            .ok_or(WorkloadError::MissingEncoding)
    }

    /// The last node minted, which every builder here leaves as the root.
    ///
    /// # Specification
    /// - requires: nothing; an empty arena is admissible input and is refused.
    /// - ensures: the identifier of the last node minted.
    /// - provides: the goal every walk starts from.
    /// - fails: `WorkloadError::NodeOutOfRange` for an arena holding no nodes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, singleton and multi-node arenas separate
    ///   absence from the last minted identifier, catching an off-by-one root.
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(ensures: |ret| ret.map(|id| id.0) == self.nodes.len().checked_sub(1).ok_or(WorkloadError::NodeOutOfRange))]
    fn root(&self) -> Result<NodeId, WorkloadError>
    {
        self.nodes
            .len()
            .checked_sub(1)
            .map_or(Err(WorkloadError::NodeOutOfRange), |last| Ok(NodeId(last)))
    }

    /// The support for one goal: a plane and the node's content encoding.
    ///
    /// Content-derived and arena-free by construction — the identifier is used
    /// to *find* the encoding and never enters the key, so two structurally
    /// identical nodes at different indices take one key.
    ///
    /// # Specification
    /// - requires: `id` names a node this arena minted.
    /// - ensures: a support carrying `plane` and the node's content encoding,
    ///   and nothing else — no identifier and no allocation order — so two
    ///   structurally identical nodes at different indices take one key.
    /// - provides: the memo key the walk consults on.
    /// - fails: `WorkloadError::MissingEncoding` when the node's encoding was
    ///   never computed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two equal leaves at different indices must agree on
    ///   one plane and differ across planes; a minted node whose encoding is
    ///   missing must refuse. This separates arena identity, plane omission and
    ///   fabricated content from the required support.
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(requires: id.0 < self.nodes.len(),
        ensures: |ret| ret.as_ref().ok().is_none_or(|support| support.plane == plane
            && self.encodings.get(id.0) == Some(&support.content)))]
    fn support(
        &self,
        plane: Plane,
        id: NodeId,
    ) -> Result<Support, WorkloadError>
    {
        let encoding = self.encoding(id)?;
        Ok(Support {
            plane,
            content: encoding.clone(),
        })
    }

    /// Mints a leaf and records its encoding.
    ///
    /// # Specification
    /// - requires: the arena has one encoding per node.
    /// - ensures: appends a leaf and its tagged encoding at one fresh index.
    /// - provides: the base case of topological arena construction.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — from an empty or populated complete arena, distinct
    ///   leaf tags produce exact nodes and encodings at consecutive fresh
    ///   indices. Repeated equal tags still mint distinct indices without
    ///   changing content.
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(requires: self.nodes.len() == self.encodings.len(),
        captures: [previous = self.nodes.len()],
        ensures: |ret| ret.0 == previous && previous.checked_add(1) == Some(self.nodes.len())
            && self.encodings.len() == self.nodes.len()
            && self.nodes.get(ret.0) == Some(&Node::Leaf(tag))
            && self.encodings.get(ret.0).is_some_and(|encoding| encoding.0 == [0x00, tag.0]))]
    fn leaf(
        &mut self,
        tag: LeafTag,
    ) -> NodeId
    {
        let id = NodeId(self.nodes.len());
        self.nodes.push(Node::Leaf(tag));
        self.encodings.push(ContentEncoding(vec![0x00, tag.0]));
        id
    }

    /// Mints a pair over already-minted children and records its encoding.
    ///
    /// # Specification
    /// - requires: `left` and `right` name nodes this arena already minted,
    ///   which keeps every child strictly earlier than its parent.
    /// - ensures: a fresh identifier for a pair node whose recorded encoding is
    ///   the pair marker followed by both children's encodings, each
    ///   length-prefixed.
    /// - provides: the inductive builder both workload shapes are written with.
    /// - fails: `WorkloadError::MissingEncoding` when a child carries no
    ///   encoding; `WorkloadError::EncodingTooLong` when a child's encoding
    ///   exceeds the length its prefix can express.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — earlier unequal leaves produce an exact ordered pair
    ///   and framed encoding; reversing them changes the content. A missing
    ///   child encoding must refuse before either arena vector grows. The
    ///   encoding-size ceiling belongs to the framing operation, not node-index
    ///   arithmetic.
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(requires: left.0 < self.nodes.len() && right.0 < self.nodes.len(),
        captures: [nodes_before = self.nodes.len(), encodings_before = self.encodings.len()],
        ensures: |ret| match ret {
            Ok(id) => id.0 == nodes_before && nodes_before.checked_add(1) == Some(self.nodes.len())
                && encodings_before.checked_add(1) == Some(self.encodings.len())
                && self.nodes.get(id.0) == Some(&Node::Pair { left, right }),
            Err(_) => self.nodes.len() == nodes_before && self.encodings.len() == encodings_before,
        })]
    fn pair(
        &mut self,
        left: NodeId,
        right: NodeId,
    ) -> Result<NodeId, WorkloadError>
    {
        let encoding = {
            let left = self.encoding(left)?;
            let right = self.encoding(right)?;
            let mut bytes = ContentEncoding(vec![0x01]);
            push_framed(&mut bytes, left)?;
            push_framed(&mut bytes, right)?;
            bytes
        };
        let id = NodeId(self.nodes.len());
        self.nodes.push(Node::Pair { left, right });
        self.encodings.push(encoding);
        Ok(id)
    }
}

/// Appends a length-prefixed encoding, which is what makes the encoding
/// prefix-free and therefore injective.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the little-endian length of `encoding` and then its
///   bytes, so no encoding is a prefix of another and the node relation is
///   mirrored injectively.
/// - provides: the framing that makes the content key decide.
/// - fails: `WorkloadError::EncodingTooLong` when the length exceeds what its
///   prefix can express.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero-length and nonempty byte strings append exact
///   little-endian prefixes and payloads after an existing prefix, separating
///   omitted framing, byte-order and replacement mutations. The u32 conversion
///   sets the size ceiling; allocating a larger-than-u32 payload is outside
///   these bounded witnesses.
/// - witness: `differential::tests::arena_and_framing_boundaries`
#[anodized::spec(captures: [prefix_len = bytes.0.len()],
    ensures: |ret| match u32::try_from(encoding.0.len()) {
        Ok(length) => ret.is_ok() && prefix_len.checked_add(4).and_then(|len| len.checked_add(encoding.0.len())) == Some(bytes.0.len())
            && bytes.0.get(prefix_len ..).is_some_and(|suffix| suffix.starts_with(&length.to_le_bytes()) && suffix.get(4 ..) == Some(encoding.0.as_slice())),
        Err(_) => ret == Err(WorkloadError::EncodingTooLong) && bytes.0.len() == prefix_len,
    })]
fn push_framed(
    bytes: &mut ContentEncoding,
    encoding: &ContentEncoding,
) -> Result<(), WorkloadError>
{
    let length =
        u32::try_from(encoding.0.len()).map_err(|_error| WorkloadError::EncodingTooLong)?;
    bytes.0.extend_from_slice(&length.to_le_bytes());
    bytes.0.extend_from_slice(&encoding.0);
    Ok(())
}

/// The tag every leaf in this harness carries, so the shared composite and its
/// unshared spelling denote the same term.
const LEAF: LeafTag = LeafTag(7);

/// The self-similar composite: `n(0)` is a leaf and `n(i+1)` is the pair of
/// `n(i)` with itself, so the arena holds `d + 1` nodes and the term they
/// denote has `2^(d+1) - 1` occurrences.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an arena of `depth + 1` nodes whose root denotes a term with
///   `2^(depth + 1) - 1` occurrences, every level being the pair of the level
///   below with itself.
/// - provides: the shared side of the collapse claim, whose sharing the memo
///   must not need to be told about.
/// - fails: `WorkloadError::MissingEncoding` or
///   `WorkloadError::EncodingTooLong`, propagated from the pair builder.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — at depth zero and one, node identities and exact shared
///   operands distinguish a leaf from one pair layer; at depths four, six and
///   eight, closed-form expansion counts separate missing or extra levels.
///   Successful results must be a predecessor chain, not merely the right size.
/// - witness: `differential::tests::workload_shape_boundaries`
/// - witness: `differential::tests::the_collapse_is_a_closed_form_at_three_depths`
#[anodized::spec(ensures: |ret| ret.as_ref().ok().is_none_or(|arena|
        u64::try_from(arena.nodes.len()).ok() == u64::from(depth.0).checked_add(1)
        && arena.nodes.iter().enumerate().all(|(index, node)| match *node {
            Node::Leaf(tag) => index == 0 && tag == LEAF,
            Node::Pair { left, right } => index.checked_sub(1) == Some(left.0) && left == right,
        })))]
fn shared_composite(depth: Depth) -> Result<Arena, WorkloadError>
{
    let mut arena = Arena::new();
    let mut current = arena.leaf(LEAF);
    for _level in 0 .. depth.0 {
        current = arena.pair(current, current)?;
    }
    Ok(arena)
}

/// The same term written out with no sharing at all: a full binary tree of
/// `2^(d+1) - 1` distinct nodes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an arena of `2^(depth + 1) - 1` distinct nodes whose root denotes
///   the same term the shared composite's root denotes.
/// - provides: the unshared side of the collapse claim, so the content key's
///   payoff is stated as a number rather than as an argument.
/// - fails: `WorkloadError::DepthOverflow` when the leaf count leaves the
///   representable range; `WorkloadError::OddLevel` when a level holds an odd
///   number of nodes; `WorkloadError::MissingEncoding` or
///   `WorkloadError::EncodingTooLong`, propagated from the pair builder.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — depths zero and one produce exact tree shapes and match
///   the shared spelling by content; larger finite depths match the closed-form
///   occurrence count. L3 a shift at the machine width must refuse before
///   allocation. The enormous adjacent valid tree is not built by this bounded
///   witness.
/// - witness: `differential::tests::workload_shape_boundaries`
/// - witness: `differential::tests::the_unshared_spelling_costs_the_memoless_walk_identically`
#[anodized::spec(ensures: |ret| ret.as_ref().ok().is_none_or(|arena|
        occurrence_count(depth).ok().map(|count| count.0) == u64::try_from(arena.nodes.len()).ok())
        && (depth.0 < usize::BITS || matches!(ret, Err(WorkloadError::DepthOverflow))))]
fn unshared_spelling(depth: Depth) -> Result<Arena, WorkloadError>
{
    let mut arena = Arena::new();
    let leaf_count = 1_usize
        .checked_shl(depth.0)
        .ok_or(WorkloadError::DepthOverflow)?;
    let mut level = Vec::new();
    for _leaf in 0 .. leaf_count {
        level.push(arena.leaf(LEAF));
    }
    while level.len() > 1 {
        let mut next = Vec::new();
        let mut operands = level.into_iter();
        while let Some(left) = operands.next() {
            let Some(right) = operands.next()
            else {
                return Err(WorkloadError::OddLevel);
            };
            let node = arena.pair(left, right)?;
            next.push(node);
        }
        level = next;
    }
    Ok(arena)
}

/// The support the walk keys on: the plane, and the node's content encoding.
///
/// # Specification
/// - requires: the content encodes the complete ordered tree for one goal.
/// - ensures: the plane and content, not the arena position, determine the key.
/// - provides: the complete input of one workload fold.
/// - panics: none.
/// - executable: none — completeness relates this value to an external arena
///   goal; the data-item expansion does not check construction.
///
/// # Adequacy
/// - hypothesis: L3 — equal leaves at distinct indices agree, but identical
///   content on the other plane differs. L2 the two memo instantiations agree
///   on outcomes; L1 the unshared spelling retains content-based collapse.
/// - witness: `differential::tests::arena_and_framing_boundaries`
/// - witness: `differential::tests::memoized_and_memoless_agree_answer_for_answer`
/// - witness: `differential::tests::a_content_key_collapses_the_unshared_spelling_too`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Support
{
    /// The accounting partition.
    plane: Plane,
    /// The node's canonical content encoding — the deciding datum.
    content: ContentEncoding,
}

/// The FNV-1a basis for the low digest word.
const LOW_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
/// A second basis, so the two digest words are not the same function.
const HIGH_BASIS: u64 = 0x8422_2325_cbf2_9ce4;
/// The FNV-1a prime.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// A deterministic FNV-1a fold over a support's encoding.
///
/// Wrapping multiplication is the hash's own definition, not overflowing
/// arithmetic on a quantity anything reads as a number.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a deterministic function of `basis`, the plane's own byte and the
///   encoding's bytes in order, so equal supports fold to equal words and the
///   plane is part of what is folded.
/// - provides: one word of the support's digest, derived from content alone.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — on arbitrary bytes and bases the u128 recurrence reduces
///   modulo 2^64 after each step, independently of wrapping u64 multiplication.
///   L3 empty and nonempty encodings, two planes and two bases have exact
///   independently calculated words, catching omitted plane bytes, reordered
///   bytes and a reused basis.
/// - witness: `differential::tests::digest_and_agreement_boundaries`
#[anodized::spec(ensures: |ret| u128::from(u64::from(ret))
    == core::iter::once(plane.tag().0).chain(encoding.0.iter().copied())
        .fold(u128::from(u64::from(basis)), |state, byte|
            (state ^ u128::from(byte)).wrapping_mul(u128::from(FNV_PRIME)) & u128::from(u64::MAX)))]
fn fold(
    plane: Plane,
    encoding: &ContentEncoding,
    basis: DigestWord,
) -> DigestWord
{
    let mut hash = u64::from(basis);
    for byte in core::iter::once(plane.tag().0).chain(encoding.0.iter().copied()) {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    DigestWord::from(hash)
}

impl MemoKey for Support
{
    type Plane = Plane;

    /// The plane this support is accounted to.
    ///
    /// # Specification
    /// trivial.
    fn plane(&self) -> Self::Plane
    {
        self.plane
    }

    /// The two-word fold of the support's plane and content.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: both words are folded from the support's content and its
    ///   plane alone, under two different bases, so agreeing supports digest
    ///   alike.
    /// - provides: the bucket selector, never a decision.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact words for both bases distinguish swapped or
    ///   reused bases, while equal content at different positions agrees and
    ///   changing plane separates the fixture keys. This certifies this fixture
    ///   digest, not collision freedom for arbitrary inputs.
    /// - witness: `differential::tests::digest_and_agreement_boundaries`
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(ensures: |ret| ret.high() == fold(self.plane, &self.content, DigestWord::from(HIGH_BASIS))
        && ret.low() == fold(self.plane, &self.content, DigestWord::from(LOW_BASIS)))]
    fn digest(&self) -> ContentDigest
    {
        ContentDigest::new(
            fold(self.plane, &self.content, DigestWord::from(HIGH_BASIS)),
            fold(self.plane, &self.content, DigestWord::from(LOW_BASIS)),
        )
    }

    /// Agrees exactly when plane and content both match.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `ContentAgreement::Agree` exactly when `self` and `other`
    ///   carry the same plane and byte-equal encodings, so the comparison
    ///   decides rather than narrows.
    /// - provides: the deciding comparison every hit in this harness is served
    ///   on.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal encodings, differing bytes and differing planes
    ///   separate agreement from both byte-blind and plane-blind comparisons.
    ///   Relocation leaves the relation unchanged because indices are absent.
    /// - witness: `differential::tests::digest_and_agreement_boundaries`
    /// - witness: `differential::tests::arena_and_framing_boundaries`
    #[anodized::spec(ensures: |ret| matches!(ret, ContentAgreement::Agree)
        == (self.plane == other.plane && self.content == other.content))]
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement
    {
        if self.plane == other.plane && self.content == other.content {
            ContentAgreement::Agree
        }
        else {
            ContentAgreement::Differ
        }
    }
}

/// The exercised-path counters: expansions and hits, per plane.
///
/// Asserted rather than reported, because a differential can be green while
/// never reaching the code it tests.
///
/// # Specification
/// - requires: counts record events from the same run, on their own planes.
/// - ensures: expansions and served hits remain separately observable.
/// - provides: a check against vacuous memoized/fresh comparisons.
/// - panics: none.
/// - executable: none — event history is external to these maps, and data-item
///   predicates are not invoked at construction; recording checks increments.
///
/// # Adequacy
/// - hypothesis: L3 — from zero and the representable ceiling, recording each
///   event kind on each plane must change only its own counter or refuse
///   unchanged. L1 the workload observes exact expansion and hit totals, rather
///   than accepting any nonzero activity.
/// - witness: `differential::tests::tally_boundaries`
/// - witness: `differential::tests::the_exercised_paths_are_asserted_rather_than_reported`
#[derive(Clone, Debug, Default)]
struct Tally
{
    /// Goal expansions performed, per plane.
    expansions: BTreeMap<Plane, WalkCount>,
    /// Memo entries served, per plane.
    hits: BTreeMap<Plane, WalkCount>,
}

impl Tally
{
    /// A tally over nothing.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        Self::default()
    }

    /// Charges one goal expansion to `plane`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the plane's expansion count is one greater and no other
    ///   plane's moves.
    /// - provides: half of the exercised-path observation the differential
    ///   asserts on rather than reports.
    /// - fails: `WorkloadError::TallyOverflow` at the counter's ceiling,
    ///   leaving the tally where it was.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for any representable expansions count, zero and MAX
    ///   - 1 advance exactly while MAX refuses without changing either map.
    ///   Both planes and both event kinds are observed, separating crossed
    ///   counters, an absent-plane default, early guards and partial mutation.
    /// - witness: `differential::tests::tally_boundaries`
    #[anodized::spec(captures: [before = self.expansions(plane)],
        ensures: |ret| ret.map(|()| self.expansions(plane).0)
            == before.0.checked_add(1).ok_or(WorkloadError::TallyOverflow)
            && (ret.is_ok() || self.expansions(plane) == before))]
    fn record_expansion(
        &mut self,
        plane: Plane,
    ) -> Result<(), WorkloadError>
    {
        let bumped = self.expansions(plane).successor()?;
        let _prior = self.expansions.insert(plane, bumped);
        Ok(())
    }

    /// Charges one served entry to `plane`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the plane's hit count is one greater and no other plane's
    ///   moves.
    /// - provides: the other half of the exercised-path observation, so a green
    ///   run cannot have been served nothing.
    /// - fails: `WorkloadError::TallyOverflow` at the counter's ceiling,
    ///   leaving the tally where it was.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for any representable hits count, zero and MAX - 1
    ///   advance exactly while MAX refuses without changing either map. Both
    ///   planes and both event kinds are observed, separating crossed counters,
    ///   an absent-plane default, early guards and partial mutation.
    /// - witness: `differential::tests::tally_boundaries`
    #[anodized::spec(captures: [before = self.hits(plane)],
        ensures: |ret| ret.map(|()| self.hits(plane).0)
            == before.0.checked_add(1).ok_or(WorkloadError::TallyOverflow)
            && (ret.is_ok() || self.hits(plane) == before))]
    fn record_hit(
        &mut self,
        plane: Plane,
    ) -> Result<(), WorkloadError>
    {
        let bumped = self.hits(plane).successor()?;
        let _prior = self.hits.insert(plane, bumped);
        Ok(())
    }

    /// Goal expansions performed on `plane`.
    ///
    /// # Specification
    /// - requires: nothing, including an unrecorded plane.
    /// - ensures: returns that plane's expansions count, or zero if absent.
    /// - provides: an exact per-plane event observer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent planes and distinct populated counters
    ///   distinguish zero defaults, a crossed event map and the wrong plane.
    /// - witness: `differential::tests::tally_boundaries`
    #[anodized::spec(ensures: |ret| ret == self.expansions.get(&plane).copied().unwrap_or(WalkCount(0)))]
    fn expansions(
        &self,
        plane: Plane,
    ) -> WalkCount
    {
        self.expansions.get(&plane).copied().unwrap_or_default()
    }

    /// Entries served on `plane`.
    ///
    /// # Specification
    /// - requires: nothing, including an unrecorded plane.
    /// - ensures: returns that plane's hits count, or zero if absent.
    /// - provides: an exact per-plane event observer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent planes and distinct populated counters
    ///   distinguish zero defaults, a crossed event map and the wrong plane.
    /// - witness: `differential::tests::tally_boundaries`
    #[anodized::spec(ensures: |ret| ret == self.hits.get(&plane).copied().unwrap_or(WalkCount(0)))]
    fn hits(
        &self,
        plane: Plane,
    ) -> WalkCount
    {
        self.hits.get(&plane).copied().unwrap_or_default()
    }
}

/// One frame of the walk's explicit stack. No recursion, and no frame owns a
/// pointer to another.
///
/// # Specification
/// - requires: node identifiers belong to the current arena; a combine frame is
///   pushed before its operand goals, so it executes after both operands.
/// - ensures: the frame identifies the next goal or completed pair reduction.
/// - provides: a finite stack machine without recursive calls.
/// - panics: none.
/// - executable: none — the arena and stack ordering are external to one frame.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf, an asymmetric pair and an already memoized root
///   have exact outcomes and expansion/hit counts. They separate operand
///   reversal, combining too soon and re-expanding a served root.
/// - witness: `differential::tests::workload_shape_boundaries`
/// - witness: `differential::tests::a_served_root_skips_expansion_on_both_planes`
#[derive(Clone, Copy, Debug)]
enum Frame
{
    /// Answer this goal, from the memo if it can.
    Expand
    {
        /// The plane the goal is on.
        plane: Plane,
        /// The node the goal is about.
        node: NodeId,
    },
    /// Combine two already-computed operands into this node's answer, then
    /// record it. Pushed *before* the operand goals so it pops after them,
    /// which is what makes the recorded answer final rather than intermediate.
    Combine
    {
        /// The plane the goal is on.
        plane: Plane,
        /// The node the goal is about.
        node: NodeId,
    },
}

/// Walks the arena on one plane, consulting `memo`.
///
/// This is the function the differential compares against itself. Every memo
/// interaction — the support construction included — is guarded on
/// `Memo::ACTIVITY`, so the [`NullMemo`] instantiation monomorphizes to the
/// walk this would be with no seam at all.
///
/// # Specification
/// - requires: `arena` holds a root, and `memo` and `tally` belong to this run.
/// - ensures: answers the plane's fold of the arena's root, charging one
///   expansion per goal whose rule ran and one hit per goal the memo answered;
///   a served entry is adopted only after its carried support is compared
///   pointwise against the demanded one. The frame stack is explicit and the
///   combine frame is pushed before its operands, so the recorded answer for a
///   pair is final rather than intermediate, and the walk is total on depth the
///   arena can express.
/// - provides: the one walk both instantiations run, so the differential
///   compares a function against itself rather than against a second
///   implementation.
/// - fails: `WorkloadError::ServedSupportDisagrees` when a hit's support does
///   not agree with the demanded one; `WorkloadError::ResultStackUnderflow` or
///   `WorkloadError::ResultStackResidue` when the operand stack does not
///   balance; `WorkloadError::Memo` when the memo declines to record; and the
///   arena, tally and combine failures those steps propagate.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — on nonempty topological arenas with complete supports,
///   fresh and memoized folds agree on both planes. L1 closed-form counts
///   separate skipped or repeated work. L3 a leaf, asymmetric pair and served
///   root distinguish missing root charges, operand reversal and an unused hit
///   path; a ceiling tally refuses instead of wrapping.
/// - witness: `differential::tests::memoized_and_memoless_agree_answer_for_answer`
/// - witness: `differential::tests::the_collapse_is_a_closed_form_at_three_depths`
/// - witness: `differential::tests::workload_shape_boundaries`
/// - witness: `differential::tests::a_served_root_skips_expansion_on_both_planes`
/// - witness: `differential::tests::tally_boundaries`
#[anodized::spec(requires: !arena.nodes.is_empty(),
    captures: [expansions_before = tally.expansions(plane), hits_before = tally.hits(plane)],
    ensures: |ret| ret.is_err() || (tally.expansions(plane) >= expansions_before
        && tally.hits(plane) >= hits_before
        && u128::from(tally.expansions(plane).0).checked_add(u128::from(tally.hits(plane).0))
            > u128::from(expansions_before.0).checked_add(u128::from(hits_before.0))))]
fn evaluate<Memo>(
    arena: &Arena,
    plane: Plane,
    memo: &mut Memo,
    tally: &mut Tally,
) -> Result<Outcome, WorkloadError>
where
    Memo: CheckMemo<Support, Outcome>,
{
    let root = arena.root()?;
    let mut frames = vec![Frame::Expand { plane, node: root }];
    let mut operands: Vec<Outcome> = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            | Frame::Expand { plane, node } => {
                if matches!(Memo::ACTIVITY, MemoActivity::Active) {
                    let support = arena.support(plane, node)?;
                    let served = match memo.recall(&support) {
                        | Some(hit) => {
                            // A hit carries its support, so adoption is a
                            // pointwise comparison of demanded against
                            // supplied rather than an assertion.
                            if !matches!(hit.support().agreement(&support), ContentAgreement::Agree)
                            {
                                return Err(WorkloadError::ServedSupportDisagrees);
                            }
                            Some(*hit.outcome())
                        },
                        | None => None,
                    };
                    if let Some(outcome) = served {
                        tally.record_hit(plane)?;
                        operands.push(outcome);
                        continue;
                    }
                }
                tally.record_expansion(plane)?;
                let node_at = arena.node(node)?;
                match node_at {
                    | Node::Leaf(tag) => {
                        let outcome = plane.leaf_outcome(tag);
                        operands.push(outcome);
                        remember(arena, plane, node, outcome, memo)?;
                    },
                    | Node::Pair { left, right } => {
                        frames.push(Frame::Combine { plane, node });
                        frames.push(Frame::Expand { plane, node: right });
                        frames.push(Frame::Expand { plane, node: left });
                    },
                }
            },
            | Frame::Combine { plane, node } => {
                let right = operands.pop().ok_or(WorkloadError::ResultStackUnderflow)?;
                let left = operands.pop().ok_or(WorkloadError::ResultStackUnderflow)?;
                let outcome = plane.combine(left, right)?;
                operands.push(outcome);
                remember(arena, plane, node, outcome, memo)?;
            },
        }
    }
    let outcome = operands.pop().ok_or(WorkloadError::ResultStackUnderflow)?;
    if !operands.is_empty() {
        return Err(WorkloadError::ResultStackResidue);
    }
    Ok(outcome)
}

/// Records one answer, building the support only when the memo is live.
///
/// # Specification
/// - requires: `node` names a node of `arena`, and `outcome` is the answer this
///   walk computed for it on `plane`.
/// - ensures: records the answer under the node's content-derived support
///   exactly when `Memo::ACTIVITY` is `MemoActivity::Active`, and builds no
///   support at all otherwise, so the memoless instantiation pays for no seam.
/// - provides: the guarded record every answering site in the walk goes
///   through.
/// - fails: `WorkloadError::MissingEncoding` when the node carries no encoding;
///   `WorkloadError::Memo` when the memo declines to record.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — for a minted node, inactive recording succeeds even when
///   its encoding is absent, while active recording reports the missing
///   encoding. This catches eager support construction. Valid active records
///   are then recalled through their content key with the exact outcome.
/// - witness: `differential::tests::recording_liveness_boundary`
/// - witness: `differential::tests::a_served_root_skips_expansion_on_both_planes`
#[anodized::spec(requires: node.0 < arena.nodes.len(),
    ensures: |ret| !matches!(Memo::ACTIVITY, MemoActivity::Inactive) || ret.is_ok())]
fn remember<Memo>(
    arena: &Arena,
    plane: Plane,
    node: NodeId,
    outcome: Outcome,
    memo: &mut Memo,
) -> Result<(), WorkloadError>
where
    Memo: CheckMemo<Support, Outcome>,
{
    if matches!(Memo::ACTIVITY, MemoActivity::Inactive) {
        return Ok(());
    }
    let support = arena.support(plane, node)?;
    let _record = memo
        .remember(support, outcome)
        .map_err(WorkloadError::Memo)?;
    Ok(())
}

/// The answers and the exercised-path counts of one walk of both planes,
/// through one memo.
///
/// # Specification
/// - requires: observations come from one arena, memo and two-plane walk.
/// - ensures: both answers accompany their event counts and memo census.
/// - provides: the two independently observed sides of the collapse claim.
/// - panics: none.
/// - executable: none — the producing arena and memo are external to the
///   snapshot; the run operation checks the census at its return boundary.
///
/// # Adequacy
/// - hypothesis: L2 — shared and unshared spellings have equal outcomes on both
///   planes. L1 exact expansion, hit and entry counts distinguish crossed
///   planes or observations from different runs; a served-root run separates
///   zero expansion from zero activity.
/// - witness: `differential::tests::memoized_and_memoless_agree_answer_for_answer`
/// - witness: `differential::tests::the_exercised_paths_are_asserted_rather_than_reported`
/// - witness: `differential::tests::a_served_root_skips_expansion_on_both_planes`
#[derive(Clone, Debug)]
struct Run
{
    /// The value plane's answer.
    value: Outcome,
    /// The weight plane's answer, which is the term's occurrence count.
    weight: Outcome,
    /// The exercised-path counts.
    tally: Tally,
    /// The memo's own entry count, read from the other direction.
    entries: MemoEntryCount,
    /// The memo's entry count on the value plane.
    value_entries: MemoEntryCount,
    /// The memo's entry count on the weight plane.
    weight_entries: MemoEntryCount,
}

/// Runs both planes over one arena through one memo.
///
/// One memo, two machines: that is the shape the per-plane accounting exists
/// for.
///
/// # Specification
/// - requires: `arena` holds a root, and `memo` is this run's own.
/// - ensures: walks the value plane and then the weight plane through one memo
///   and one tally, and answers both planes' outcomes beside the exercised-path
///   counts and the memo's own entry counts, total and per plane.
/// - provides: the observation the zero-drift, collapse and anti-vacuity claims
///   are all stated over, with the memo's count read from the other direction
///   than the tally's.
/// - fails: whatever the two walks propagate.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — for nonempty topological arenas, the two instantiations
///   must agree answer-for-answer. L1 each plane has its own closed-form event
///   and entry counts. L3 a leaf, asymmetric pair and second run over a served
///   root separate plane swaps, operand order and fresh-versus-reused work.
/// - witness: `differential::tests::memoized_and_memoless_agree_answer_for_answer`
/// - witness: `differential::tests::the_collapse_is_a_closed_form_at_three_depths`
/// - witness: `differential::tests::workload_shape_boundaries`
/// - witness: `differential::tests::a_served_root_skips_expansion_on_both_planes`
#[anodized::spec(requires: !arena.nodes.is_empty(),
    ensures: |ret| ret.as_ref().ok().is_none_or(|run|
        run.entries == memo.entry_count() && run.value_entries == memo.plane_entry_count(Plane::Value)
        && run.weight_entries == memo.plane_entry_count(Plane::Weight)
        && usize::from(run.value_entries).checked_add(usize::from(run.weight_entries)) == Some(usize::from(run.entries))))]
fn run<Memo>(
    arena: &Arena,
    memo: &mut Memo,
) -> Result<Run, WorkloadError>
where
    Memo: CheckMemo<Support, Outcome>,
{
    let mut tally = Tally::new();
    let value = evaluate(arena, Plane::Value, memo, &mut tally)?;
    let weight = evaluate(arena, Plane::Weight, memo, &mut tally)?;
    Ok(Run {
        value,
        weight,
        tally,
        entries: memo.entry_count(),
        value_entries: memo.plane_entry_count(Plane::Value),
        weight_entries: memo.plane_entry_count(Plane::Weight),
    })
}

/// `2^(d+1) - 1`: the number of goal expansions per plane the memoless walk
/// makes, which is the term's occurrence count.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `2^(depth + 1) - 1`, which is the occurrence count of the term
///   both workload shapes denote and the number of goal expansions the memoless
///   walk makes per plane.
/// - provides: the closed form the memoless side is asserted against.
/// - fails: `WorkloadError::DepthOverflow` when the form leaves the
///   representable range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — for every representable depth, the wide-integer closed
///   form is independent of the leaf-plus-branch calculation. L3 depths zero,
///   one, 62 and 63 must return exact counts; 64 and the u32 ceiling must
///   refuse. These distinguish the intermediate-shift overflow from a genuinely
///   unrepresentable result and catch off-by-one guards.
/// - witness: `differential::tests::occurrence_count_ceiling_is_representable`
/// - witness: `differential::tests::the_collapse_is_a_closed_form_at_three_depths`
#[anodized::spec(ensures: |ret| ret.map(|count| count.0)
    == depth.0.checked_add(1).and_then(|power| 1_u128.checked_shl(power))
        .and_then(|value| value.checked_sub(1))
        .and_then(|value| u64::try_from(value).ok()).ok_or(WorkloadError::DepthOverflow))]
fn occurrence_count(depth: Depth) -> Result<WalkCount, WorkloadError>
{
    let leaves = 1_u64
        .checked_shl(depth.0)
        .ok_or(WorkloadError::DepthOverflow)?;
    let branches = leaves.checked_sub(1).ok_or(WorkloadError::DepthOverflow)?;
    let count = leaves
        .checked_add(branches)
        .ok_or(WorkloadError::DepthOverflow)?;
    Ok(WalkCount(count))
}

/// `d + 1`: the number of distinct contents, and so the number of goal
/// expansions per plane the memoized walk makes under a content-derived key.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `depth + 1`, the number of distinct contents in the workload and
///   so the number of goal expansions the memoized walk makes per plane under a
///   content-derived key.
/// - provides: the closed form the memoized side is asserted against.
/// - fails: `WorkloadError::DepthOverflow` when the sum leaves the
///   representable range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L0 — u32 depth plus one always fits the u64 result domain. L3
///   zero and the u32 ceiling have exact results, separating a forgotten
///   increment from an unnecessary narrowing or overflow refusal.
/// - witness: `differential::tests::counter_arithmetic_boundaries`
#[anodized::spec(ensures: |ret| ret.map(|count| count.0) == u64::from(depth.0).checked_add(1).ok_or(WorkloadError::DepthOverflow))]
fn distinct_content_count(depth: Depth) -> Result<WalkCount, WorkloadError>
{
    let count = u64::from(depth.0)
        .checked_add(1)
        .ok_or(WorkloadError::DepthOverflow)?;
    Ok(WalkCount(count))
}

/// `d`: the number of entries the memoized walk is served per plane. A hit at
/// an interior node prunes its subtree, so one entry is served per pair level
/// and none at the leaf.
///
/// # Specification
/// trivial.
fn served_count(depth: Depth) -> WalkCount
{
    WalkCount(u64::from(depth.0))
}

/// `2d + 1`: the number of goals the memoized walk issues per plane — the root,
/// plus two per pair expansion.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `2 * depth + 1`, the number of goals the memoized walk issues per
///   plane — the root, plus two per pair expansion.
/// - provides: the closed form that pins goals against expansions plus hits,
///   which is what makes the hit count non-vacuous.
/// - fails: `WorkloadError::DepthOverflow` when the form leaves the
///   representable range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L0 — twice any u32 depth plus one fits u64. L3 zero, one and
///   the u32 ceiling distinguish missing root goals, wrong factors and
///   premature narrowing by exact answers.
/// - witness: `differential::tests::counter_arithmetic_boundaries`
#[anodized::spec(ensures: |ret| ret.map(|count| count.0) == u64::from(depth.0).checked_mul(2).and_then(|count| count.checked_add(1)).ok_or(WorkloadError::DepthOverflow))]
fn goal_count(depth: Depth) -> Result<WalkCount, WorkloadError>
{
    let pairs = u64::from(depth.0)
        .checked_mul(2)
        .ok_or(WorkloadError::DepthOverflow)?;
    let goals = pairs.checked_add(1).ok_or(WorkloadError::DepthOverflow)?;
    Ok(WalkCount(goals))
}

/// The sum of two walk counts.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the sum of the two counts when representable.
/// - provides: the one addition the closed-form assertions go through.
/// - fails: `WorkloadError::TallyOverflow` when the sum leaves the
///   representable range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — arbitrary u64 operands are added in u128 before checking
///   the target ceiling. L3 zero, an exact MAX sum and MAX plus one distinguish
///   omitted operands, premature refusal and wrapping.
/// - witness: `differential::tests::counter_arithmetic_boundaries`
#[anodized::spec(ensures: |ret| ret.map(|count| u128::from(count.0))
    == u128::from(first.0).checked_add(u128::from(second.0)).filter(|count| *count <= u128::from(u64::MAX)).ok_or(WorkloadError::TallyOverflow))]
fn sum_counts(
    first: WalkCount,
    second: WalkCount,
) -> Result<WalkCount, WorkloadError>
{
    let sum = first
        .0
        .checked_add(second.0)
        .ok_or(WorkloadError::TallyOverflow)?;
    Ok(WalkCount(sum))
}

/// The same count read as a memo entry count, so the tally and the memo's own
/// accounting can be compared directly.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the same quantity as a memo entry count, so the tally and the
///   memo's own accounting are compared in one unit.
/// - provides: the bridge between the two directions the collapse claim is read
///   from.
/// - fails: `WorkloadError::TallyOverflow` when the count does not fit a memo
///   entry count.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero and the largest input are compared with checked
///   usize conversion, exercising success or refusal according to the target
///   width. Exact counts separate truncation from an identity conversion.
/// - witness: `differential::tests::counter_arithmetic_boundaries`
#[anodized::spec(ensures: |ret| ret.map(usize::from) == usize::try_from(count.0).map_err(|_error| WorkloadError::TallyOverflow))]
fn as_entries(count: WalkCount) -> Result<MemoEntryCount, WorkloadError>
{
    let count = usize::try_from(count.0).map_err(|_error| WorkloadError::TallyOverflow)?;
    Ok(MemoEntryCount::from(count))
}

/// Two planes' worth of the same per-plane count.
///
/// # Specification
/// - requires: nothing.
/// - ensures: twice the per-plane count, as a memo entry count.
/// - provides: the two-plane total a single-plane closed form is compared
///   against, since one memo serves both machines.
/// - fails: `WorkloadError::TallyOverflow` when the doubled count leaves the
///   representable range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — doubling is calculated in u128 and then checked against
///   both u64 and usize ceilings. L3 zero, one, the largest fitting half and
///   one above it distinguish an omitted factor, early refusal and wrapping
///   before the representation conversion.
/// - witness: `differential::tests::counter_arithmetic_boundaries`
#[anodized::spec(ensures: |ret| ret.map(usize::from)
    == u128::from(count.0).checked_mul(2).filter(|count| *count <= u128::from(u64::MAX))
        .and_then(|count| usize::try_from(count).ok()).ok_or(WorkloadError::TallyOverflow))]
fn both_planes(count: WalkCount) -> Result<MemoEntryCount, WorkloadError>
{
    let doubled = count.0.checked_mul(2).ok_or(WorkloadError::TallyOverflow)?;
    as_entries(WalkCount(doubled))
}

#[cfg(test)]
mod tests
{
    use super::*;

    /// The depths the closed forms are asserted at.
    const DEPTHS: [Depth; 3] = [Depth(4), Depth(6), Depth(8)];

    #[test]
    fn memoized_and_memoless_agree_answer_for_answer() -> Result<(), WorkloadError>
    {
        for depth in DEPTHS {
            let shared = shared_composite(depth)?;
            let unshared = unshared_spelling(depth)?;
            for arena in [shared, unshared] {
                let fresh = run(&arena, &mut NullMemo)?;
                let mut memo: OrderedMemo<Support, Outcome> = OrderedMemo::new();
                let memoized = run(&arena, &mut memo)?;
                assert_eq!(
                    fresh.value, memoized.value,
                    "the value plane's answer is the same function's answer at either type parameter"
                );
                assert_eq!(
                    fresh.weight, memoized.weight,
                    "and so is the weight plane's"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn the_collapse_is_a_closed_form_at_three_depths() -> Result<(), WorkloadError>
    {
        for depth in DEPTHS {
            let arena = shared_composite(depth)?;
            let occurrences = occurrence_count(depth)?;
            let distinct = distinct_content_count(depth)?;

            let fresh = run(&arena, &mut NullMemo)?;
            assert_eq!(
                occurrences,
                fresh.tally.expansions(Plane::Value),
                "memoless, the value plane expands one goal per occurrence: 2^(d+1) - 1"
            );
            assert_eq!(
                occurrences,
                fresh.tally.expansions(Plane::Weight),
                "and so does the weight plane, per plane rather than in aggregate"
            );
            assert_eq!(
                Outcome(occurrences.0),
                fresh.weight,
                "and the machine's own weight answer is that same occurrence count, so the workload \
             cannot silently stop being shared without this disagreeing with the tally"
            );

            let mut memo: OrderedMemo<Support, Outcome> = OrderedMemo::new();
            let memoized = run(&arena, &mut memo)?;
            assert_eq!(
                distinct,
                memoized.tally.expansions(Plane::Value),
                "memoized, the value plane expands one goal per distinct content: d + 1"
            );
            assert_eq!(
                distinct,
                memoized.tally.expansions(Plane::Weight),
                "and so does the weight plane"
            );
            let per_plane = as_entries(distinct)?;
            let total = both_planes(distinct)?;
            assert_eq!(
                per_plane, memoized.value_entries,
                "the memo's own value-plane entry count agrees with the expansion count read from the \
             other direction"
            );
            assert_eq!(
                per_plane, memoized.weight_entries,
                "and so does the weight plane's, so neither machine's collapse hides behind the \
             other's numbers"
            );
            assert_eq!(
                total, memoized.entries,
                "and the total is the sum of the two planes"
            );
        }
        Ok(())
    }

    #[test]
    fn the_exercised_paths_are_asserted_rather_than_reported() -> Result<(), WorkloadError>
    {
        for depth in DEPTHS {
            let arena = shared_composite(depth)?;
            let occurrences = occurrence_count(depth)?;
            let distinct = distinct_content_count(depth)?;
            // The memoized walk issues `2d + 1` goals per plane — the root plus two
            // per pair expansion — of which `d + 1` miss and `d` are served. A hit
            // at an interior node prunes that node's whole subtree, which is why
            // the served count is linear in the depth rather than in the
            // occurrence count.
            let served = served_count(depth);
            let goals = goal_count(depth)?;

            let fresh = run(&arena, &mut NullMemo)?;
            assert_eq!(
                WalkCount(0),
                fresh.tally.hits(Plane::Value),
                "the null instantiation serves nothing, on either plane"
            );
            assert_eq!(WalkCount(0), fresh.tally.hits(Plane::Weight));
            assert_eq!(
                MemoEntryCount::zero(),
                fresh.entries,
                "and it accounts nothing, so the memoless side is genuinely memoless"
            );

            let mut memo: OrderedMemo<Support, Outcome> = OrderedMemo::new();
            let memoized = run(&arena, &mut memo)?;
            assert_eq!(
                served,
                memoized.tally.hits(Plane::Value),
                "the memoized instantiation serves exactly `d` entries on the value plane — asserted, \
             so a green differential cannot have skipped the hit path"
            );
            assert_eq!(
                served,
                memoized.tally.hits(Plane::Weight),
                "and exactly `d` on the weight plane, so neither plane's hit path is unreached"
            );
            assert_eq!(
                distinct,
                memoized.tally.expansions(Plane::Value),
                "the misses are the distinct contents"
            );
            let value_goals = sum_counts(memoized.tally.expansions(Plane::Value), served)?;
            let weight_goals = sum_counts(memoized.tally.expansions(Plane::Weight), served)?;
            assert_eq!(
                goals, value_goals,
                "and every goal the walk issued was either expanded or served, on the value plane"
            );
            assert_eq!(goals, weight_goals, "and on the weight plane");
            assert!(
                occurrences > goals,
                "while the memoless walk issued one goal per occurrence, which is what the collapse is"
            );
        }
        Ok(())
    }

    #[test]
    fn the_unshared_spelling_costs_the_memoless_walk_identically() -> Result<(), WorkloadError>
    {
        for depth in DEPTHS {
            let shared = shared_composite(depth)?;
            let shared = run(&shared, &mut NullMemo)?;
            let unshared = unshared_spelling(depth)?;
            let unshared = run(&unshared, &mut NullMemo)?;
            assert_eq!(
                shared.tally.expansions(Plane::Value),
                unshared.tally.expansions(Plane::Value),
                "the shared composite and its fully unshared spelling cost the memoless walk the same, \
             which is the statement that sharing bought this walk nothing before the memo existed"
            );
            assert_eq!(
                shared.tally.expansions(Plane::Weight),
                unshared.tally.expansions(Plane::Weight)
            );
            assert_eq!(
                shared.value, unshared.value,
                "and the two spellings denote the same term, so their answers agree"
            );
            assert_eq!(shared.weight, unshared.weight);
        }
        Ok(())
    }

    #[test]
    fn a_content_key_collapses_the_unshared_spelling_too() -> Result<(), WorkloadError>
    {
        for depth in DEPTHS {
            let arena = unshared_spelling(depth)?;
            let distinct = distinct_content_count(depth)?;
            let mut memo: OrderedMemo<Support, Outcome> = OrderedMemo::new();
            let memoized = run(&arena, &mut memo)?;
            assert_eq!(
                distinct,
                memoized.tally.expansions(Plane::Value),
                "a content-derived key collapses structurally identical nodes at different indices, so \
             the unshared spelling costs what the shared one costs — which an arena-relative key \
             would not do"
            );
            assert_eq!(distinct, memoized.tally.expansions(Plane::Weight));
            let entries = as_entries(distinct)?;
            assert_eq!(entries, memoized.value_entries);
        }
        Ok(())
    }

    #[test]
    fn occurrence_count_ceiling_is_representable()
    {
        assert_eq!(Ok(WalkCount(1)), occurrence_count(Depth(0)));
        assert_eq!(Ok(WalkCount(3)), occurrence_count(Depth(1)));
        assert_eq!(
            Ok(WalkCount(0x7fff_ffff_ffff_ffff)),
            occurrence_count(Depth(62))
        );
        assert_eq!(Ok(WalkCount(u64::MAX)), occurrence_count(Depth(63)));
        assert_eq!(
            Err(WorkloadError::DepthOverflow),
            occurrence_count(Depth(64))
        );
        assert_eq!(
            Err(WorkloadError::DepthOverflow),
            occurrence_count(Depth(u32::MAX))
        );
    }

    #[test]
    fn counter_arithmetic_boundaries()
    {
        assert_eq!(Ok(WalkCount(1)), WalkCount(0).successor());
        assert_eq!(Ok(WalkCount(u64::MAX)), WalkCount(u64::MAX - 1).successor());
        assert_eq!(
            Err(WorkloadError::TallyOverflow),
            WalkCount(u64::MAX).successor()
        );
        assert_eq!(Ok(WalkCount(0)), sum_counts(WalkCount(0), WalkCount(0)));
        assert_eq!(
            Ok(WalkCount(u64::MAX)),
            sum_counts(WalkCount(u64::MAX - 1), WalkCount(1))
        );
        assert_eq!(
            Err(WorkloadError::TallyOverflow),
            sum_counts(WalkCount(u64::MAX), WalkCount(1))
        );
        assert_eq!(Ok(WalkCount(1)), distinct_content_count(Depth(0)));
        assert_eq!(
            Ok(WalkCount(0x1_0000_0000)),
            distinct_content_count(Depth(u32::MAX))
        );
        assert_eq!(Ok(WalkCount(1)), goal_count(Depth(0)));
        assert_eq!(Ok(WalkCount(3)), goal_count(Depth(1)));
        assert_eq!(Ok(WalkCount(0x1_ffff_ffff)), goal_count(Depth(u32::MAX)));
        assert_eq!(Ok(MemoEntryCount::zero()), as_entries(WalkCount(0)));
        match usize::try_from(u64::MAX) {
            | Ok(maximum) => assert_eq!(
                Ok(MemoEntryCount::from(maximum)),
                as_entries(WalkCount(u64::MAX))
            ),
            | Err(_error) => assert_eq!(
                Err(WorkloadError::TallyOverflow),
                as_entries(WalkCount(u64::MAX))
            ),
        }
        assert_eq!(Ok(MemoEntryCount::zero()), both_planes(WalkCount(0)));
        assert_eq!(Ok(MemoEntryCount::from(2)), both_planes(WalkCount(1)));
        let maximum = u64::try_from(usize::MAX).unwrap_or(u64::MAX);
        let half = maximum.checked_div(2).expect("nonzero divisor");
        let last = usize::try_from(maximum & !1).expect("bounded even count");
        assert_eq!(Ok(MemoEntryCount::from(last)), both_planes(WalkCount(half)));
        assert_eq!(
            Err(WorkloadError::TallyOverflow),
            both_planes(WalkCount(
                half.checked_add(1).expect("half is below the ceiling")
            ))
        );
    }

    #[test]
    fn plane_fold_boundaries()
    {
        assert_eq!(Outcome(0), Plane::Value.leaf_outcome(LeafTag(0)));
        assert_eq!(Outcome(7), Plane::Value.leaf_outcome(LeafTag(7)));
        assert_eq!(Outcome(1), Plane::Weight.leaf_outcome(LeafTag(7)));
        assert_eq!(
            Ok(Outcome(0x9e37_79ab)),
            Plane::Value.combine(Outcome(1), Outcome(2))
        );
        assert_eq!(
            Ok(Outcome(0x9e37_79b5)),
            Plane::Value.combine(Outcome(2), Outcome(1))
        );
        assert_eq!(
            Ok(Outcome(1)),
            Plane::Weight.combine(Outcome(0), Outcome(0))
        );
        assert_eq!(
            Ok(Outcome(u64::MAX)),
            Plane::Weight.combine(Outcome(u64::MAX - 1), Outcome(0))
        );
        assert_eq!(
            Err(WorkloadError::WeightOverflow),
            Plane::Weight.combine(Outcome(u64::MAX), Outcome(0))
        );
        assert_eq!(
            Err(WorkloadError::WeightOverflow),
            Plane::Weight.combine(Outcome(u64::MAX), Outcome(1))
        );
    }

    #[test]
    fn arena_and_framing_boundaries() -> Result<(), WorkloadError>
    {
        let mut arena = Arena::new();
        assert_eq!(Err(WorkloadError::NodeOutOfRange), arena.root());
        assert_eq!(Err(WorkloadError::NodeOutOfRange), arena.node(NodeId(0)));
        assert_eq!(
            Err(WorkloadError::MissingEncoding),
            arena.encoding(NodeId(0))
        );
        let left = arena.leaf(LeafTag(1));
        assert_eq!(NodeId(0), left);
        assert_eq!(Ok(left), arena.root());
        let right = arena.leaf(LeafTag(2));
        let same = arena.leaf(LeafTag(1));
        let pair = arena.pair(left, right)?;
        assert_eq!(NodeId(3), pair);
        assert_eq!(Ok(pair), arena.root());
        assert_eq!(Ok(Node::Leaf(LeafTag(1))), arena.node(left));
        assert_eq!(Ok(Node::Pair { left, right }), arena.node(pair));
        assert_eq!(&[0, 1], arena.encoding(left)?.0.as_slice());
        assert_eq!(
            &[1, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2],
            arena.encoding(pair)?.0.as_slice()
        );
        let reversed = arena.pair(right, left)?;
        assert_ne!(arena.encoding(pair)?, arena.encoding(reversed)?);
        assert_eq!(
            Err(WorkloadError::NodeOutOfRange),
            arena.node(NodeId(arena.nodes.len()))
        );
        assert_eq!(
            Err(WorkloadError::MissingEncoding),
            arena.encoding(NodeId(arena.encodings.len()))
        );
        let first_support = arena.support(Plane::Value, left)?;
        let same_support = arena.support(Plane::Value, same)?;
        assert_eq!(
            ContentAgreement::Agree,
            first_support.agreement(&same_support)
        );
        assert_eq!(first_support.digest(), same_support.digest());
        assert_eq!(
            ContentAgreement::Differ,
            first_support.agreement(&arena.support(Plane::Weight, same)?)
        );
        let mut framed = ContentEncoding(vec![0xaa]);
        push_framed(&mut framed, &ContentEncoding(vec![]))?;
        push_framed(&mut framed, &ContentEncoding(vec![0, 7]))?;
        assert_eq!(vec![0xaa, 0, 0, 0, 0, 2, 0, 0, 0, 0, 7], framed.0);
        arena.encodings.clear();
        assert_eq!(
            Err(WorkloadError::MissingEncoding),
            arena.support(Plane::Value, left)
        );
        let nodes_before = arena.nodes.clone();
        assert_eq!(Err(WorkloadError::MissingEncoding), arena.pair(left, right));
        assert_eq!(nodes_before, arena.nodes);
        assert!(
            arena.encodings.is_empty(),
            "refusal must not append an encoding"
        );
        Ok(())
    }

    #[test]
    fn workload_shape_boundaries() -> Result<(), WorkloadError>
    {
        let shared_leaf = shared_composite(Depth(0))?;
        let unshared_leaf = unshared_spelling(Depth(0))?;
        assert_eq!(vec![Node::Leaf(LEAF)], shared_leaf.nodes);
        assert_eq!(shared_leaf.nodes, unshared_leaf.nodes);
        let shared = shared_composite(Depth(1))?;
        let unshared = unshared_spelling(Depth(1))?;
        assert_eq!(
            vec![Node::Leaf(LEAF), Node::Pair {
                left: NodeId(0),
                right: NodeId(0)
            }],
            shared.nodes
        );
        assert_eq!(
            vec![Node::Leaf(LEAF), Node::Leaf(LEAF), Node::Pair {
                left: NodeId(0),
                right: NodeId(1)
            }],
            unshared.nodes
        );
        assert_eq!(
            shared.encoding(shared.root()?)?,
            unshared.encoding(unshared.root()?)?
        );
        assert!(matches!(
            unshared_spelling(Depth(usize::BITS)),
            Err(WorkloadError::DepthOverflow)
        ));
        let mut asymmetric = Arena::new();
        let left = asymmetric.leaf(LeafTag(1));
        let right = asymmetric.leaf(LeafTag(2));
        let _root = asymmetric.pair(left, right)?;
        let observed = run(&asymmetric, &mut NullMemo)?;
        assert_eq!(Outcome(0x9e37_79ab), observed.value);
        assert_eq!(Outcome(3), observed.weight);
        assert_eq!(WalkCount(3), observed.tally.expansions(Plane::Value));
        assert_eq!(WalkCount(3), observed.tally.expansions(Plane::Weight));
        Ok(())
    }

    #[test]
    fn digest_and_agreement_boundaries()
    {
        let empty = ContentEncoding(vec![]);
        assert_eq!(
            DigestWord::from(0xaf63_cd4c_8601_d30f),
            fold(Plane::Value, &empty, DigestWord::from(LOW_BASIS))
        );
        assert_eq!(
            DigestWord::from(0x789e_ae39_8d40_b44f),
            fold(Plane::Weight, &empty, DigestWord::from(HIGH_BASIS))
        );
        let support = Support {
            plane: Plane::Value,
            content: ContentEncoding(vec![0, 7]),
        };
        assert_eq!(
            ContentDigest::new(
                DigestWord::from(0x3e75_07f9_62f4_ed49),
                DigestWord::from(0x63e4_bf18_ba8f_154e)
            ),
            support.digest()
        );
        assert_eq!(ContentAgreement::Agree, support.agreement(&support));
        let other_content = Support {
            plane: Plane::Value,
            content: ContentEncoding(vec![0, 8]),
        };
        let other_plane = Support {
            plane: Plane::Weight,
            content: ContentEncoding(vec![0, 7]),
        };
        assert_eq!(ContentAgreement::Differ, support.agreement(&other_content));
        assert_eq!(ContentAgreement::Differ, support.agreement(&other_plane));
    }

    #[test]
    fn tally_boundaries() -> Result<(), WorkloadError>
    {
        let mut tally = Tally::new();
        assert_eq!(WalkCount(0), tally.expansions(Plane::Weight));
        assert_eq!(WalkCount(0), tally.hits(Plane::Value));
        tally.record_expansion(Plane::Value)?;
        tally.record_hit(Plane::Weight)?;
        assert_eq!(
            BTreeMap::from([(Plane::Value, WalkCount(1))]),
            tally.expansions
        );
        assert_eq!(BTreeMap::from([(Plane::Weight, WalkCount(1))]), tally.hits);
        let _prior = tally
            .expansions
            .insert(Plane::Value, WalkCount(u64::MAX - 1));
        tally.record_expansion(Plane::Value)?;
        assert_eq!(WalkCount(u64::MAX), tally.expansions(Plane::Value));
        let before = (tally.expansions.clone(), tally.hits.clone());
        assert_eq!(
            Err(WorkloadError::TallyOverflow),
            tally.record_expansion(Plane::Value)
        );
        assert_eq!((&before.0, &before.1), (&tally.expansions, &tally.hits));
        let _prior = tally.hits.insert(Plane::Weight, WalkCount(u64::MAX - 1));
        tally.record_hit(Plane::Weight)?;
        assert_eq!(WalkCount(u64::MAX), tally.hits(Plane::Weight));
        let before = (tally.expansions.clone(), tally.hits.clone());
        assert_eq!(
            Err(WorkloadError::TallyOverflow),
            tally.record_hit(Plane::Weight)
        );
        assert_eq!((&before.0, &before.1), (&tally.expansions, &tally.hits));
        let arena = shared_composite(Depth(0))?;
        assert_eq!(
            Err(WorkloadError::TallyOverflow),
            evaluate(&arena, Plane::Value, &mut NullMemo, &mut tally)
        );
        assert_eq!((&before.0, &before.1), (&tally.expansions, &tally.hits));
        Ok(())
    }

    #[test]
    fn a_served_root_skips_expansion_on_both_planes() -> Result<(), WorkloadError>
    {
        let arena = shared_composite(Depth(2))?;
        let mut memo: OrderedMemo<Support, Outcome> = OrderedMemo::new();
        let first = run(&arena, &mut memo)?;
        let second = run(&arena, &mut memo)?;
        assert_eq!(first.value, second.value);
        assert_eq!(Outcome(7), second.weight);
        for plane in [Plane::Value, Plane::Weight] {
            assert_eq!(WalkCount(0), second.tally.expansions(plane));
            assert_eq!(WalkCount(1), second.tally.hits(plane));
        }
        assert_eq!(MemoEntryCount::from(6), second.entries);
        assert_eq!(MemoEntryCount::from(3), second.value_entries);
        assert_eq!(MemoEntryCount::from(3), second.weight_entries);
        Ok(())
    }

    #[test]
    fn recording_liveness_boundary() -> Result<(), WorkloadError>
    {
        let mut arena = Arena::new();
        let node = arena.leaf(LeafTag(7));
        let mut memo: OrderedMemo<Support, Outcome> = OrderedMemo::new();
        remember(&arena, Plane::Value, node, Outcome(7), &mut memo)?;
        assert_eq!(
            &Outcome(7),
            memo.recall(&arena.support(Plane::Value, node)?)
                .expect("recorded support")
                .outcome()
        );
        arena.encodings.clear();
        assert_eq!(
            Ok(()),
            remember(&arena, Plane::Value, node, Outcome(7), &mut NullMemo)
        );
        assert_eq!(
            Err(WorkloadError::MissingEncoding),
            remember(&arena, Plane::Value, node, Outcome(7), &mut memo)
        );
        Ok(())
    }
}
