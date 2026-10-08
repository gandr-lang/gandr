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
//!   statement that sharing bought this walk nothing before the memo existed.
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
    fn successor(self) -> Result<Self, WorkloadError>
    {
        self.0
            .checked_add(1)
            .map_or(Err(WorkloadError::TallyOverflow), |next| Ok(Self(next)))
    }
}

/// The canonical content encoding of a node: tagged, length-prefixed, and
/// prefix-free, so it is injective and mirrors the node relation exactly.
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
    /// - ensures: the value plane answers a bitwise, order-sensitive
    ///   combination that distinguishes a pair from its mirror image; the
    ///   weight plane answers one more than the sum of its operands, which
    ///   counts the pair node itself.
    /// - provides: the inductive case of both machines.
    /// - fails: `WorkloadError::WeightOverflow` when a weight sum leaves the
    ///   range its counter can express.
    /// - panics: none.
    fn combine(
        self,
        left: Outcome,
        right: Outcome,
    ) -> Result<Outcome, WorkloadError>
    {
        match self {
            // Bitwise and order-sensitive: total, and it distinguishes a pair
            // from its mirror image.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
/// `M::ACTIVITY`, so the [`NullMemo`] instantiation monomorphizes to the walk
/// this would be with no seam at all.
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
fn occurrence_count(depth: Depth) -> Result<WalkCount, WorkloadError>
{
    let levels = depth.0.checked_add(1).ok_or(WorkloadError::DepthOverflow)?;
    let leaves_and_more = 1_u64
        .checked_shl(levels)
        .ok_or(WorkloadError::DepthOverflow)?;
    let count = leaves_and_more
        .checked_sub(1)
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
}
