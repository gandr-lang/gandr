//! The document builder: the only insertion path into an arena.
//!
//! Construction is explicit. There is no infallible constructor and no
//! `Default`, because both would have to conceal either a key-minting failure
//! or a capacity failure, and concealing those is how a resource bound stops
//! being a bound. Every constructor takes handles, checks them, charges the
//! meter, and returns a handle or a typed error.
//!
//! Handles are shareable: naming the same handle twice builds a shared
//! subdocument rather than a copy, and the second edge is charged as an edge
//! rather than as a new node.
//!
//! # The construction surface
//!
//! [`DocBuilder::try_new`] mints the arena key and inserts the singleton empty,
//! line, and hard-line nodes. Those three count against the node ceiling, so a
//! ceiling below three refuses immediately rather than pretending to succeed.
//!
//! [`DocBuilder::concat_all`] builds a balanced concatenation and preserves
//! input order.
//!
//! `group(d)` is exactly `choice(d, flatten(d))`, in that order. The
//! unflattened form is deliberately on the left: when both branches end up
//! width-tainted the merge keeps the left promise unforced, so the vertical
//! form is what a document too wide to lay out falls back to. At ordinary
//! widths the cost order still selects the flattened form when it is better,
//! so the left bias costs nothing where it does not matter.
//!
//! # Finalization
//!
//! [`DocBuilder::finish`] runs one iterative, memoized flatten pass under the
//! same build limits. It visits each node once, consults a structural
//! interner, appends at most one distinct flattened image per node, keeps the
//! original identity when flattening changes nothing, and records the result.
//! It receives no render options: flattening is a property of the document, not
//! of a page width. Existing identities never move, and a limit or allocation
//! failure returns without producing a partial arena.
//!
//! Finalization moves its fallibly grown stores straight into the arena and
//! keeps their capacity. It does not shrink them or convert them through a
//! boxed slice, because that step can allocate and an allocation on the way out
//! of a fallible builder is exactly the failure the fallible growth was for.
//!
//! # Accounting
//!
//! - One build step per checked input edge and per interner probe.
//! - A newly stored node, text identity, verbatim identity, byte, or physical
//!   fragment is charged exactly once to its own ceiling.
//! - A second edge to an existing handle is charged as an edge, never as a new
//!   node.
//! - Each visit, flatten edge, and interner probe during finalization charges a
//!   build step, and each distinct flattened image charges a node before it is
//!   inserted.
//! - Exceeding a build ceiling leaves the builder unfinalized, and a build
//!   failure can never consume a render counter.
//!
//! The interner is an ordered map, so the same document interns to the same
//! arena on every run with no hash seed in play. Its growth is bounded by the
//! node ceiling, charged before every insertion; `alloc` offers no fallible
//! reservation for an ordered map, so it is the one build store whose
//! allocation is not a typed error.
//!
//! # Recursion
//!
//! Nothing here recurses over caller-supplied structure. Finalization is one
//! forward pass over the node store — every edge names an earlier node, whose
//! image is therefore already computed — and balanced concatenation runs on
//! explicit levels, because a deep document is ordinary input and a native
//! stack is not a resource this crate is allowed to exhaust.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::num::NonZeroU32;
use core::sync::atomic::AtomicU32;
use core::sync::atomic::Ordering;

use quenchant_shape::shape::Maybe;

use crate::arena::ArenaKey;
use crate::arena::CheckedText;
use crate::arena::DocArena;
use crate::arena::DocId;
use crate::arena::DocNode;
use crate::arena::NodeId;
use crate::arena::TextId;
use crate::arena::TextOwned;
use crate::arena::TextSource;
use crate::arena::VerbatimId;
use crate::arena::VerbatimOwned;
use crate::arena::VerbatimSource;
use crate::arena::VerbatimText;
use crate::error::BuildAllocationSite;
use crate::error::BuildArithmetic;
use crate::error::BuildError;
use crate::limits::BuildMeter;
use crate::units::NestAmount;

quenchant_shape::reason_enum! {
    /// Why the interner holds no image for a candidate.
    pub(crate) mod interned {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// No structurally equal image was stored before.
            Unseen,
        }
    }
}

/// The next process-local arena key, with zero reserved as the exhausted state.
///
/// # Specification
/// - requires: updates use the checked atomic minting operation without resets.
/// - ensures: each nonzero key is consumed once and zero remains exhausted.
/// - provides: the shared namespace authority for every builder.
/// - panics: none.
/// - executable: none — the static is shared state, not a callable boundary;
///   atomic minting carries the executable ordering predicate.
///
/// # Adequacy
/// - hypothesis: L3 — local transitions at one, u32 maximum and exhausted zero
///   expose exact token/next-state pairs; concurrent minting exposes duplicate
///   arena keys without assuming a global starting value. Wraparound, token
///   reuse, skipped advancement and a non-atomic update change these
///   observations.
/// - witness: `build::tests::an_exhausted_arena_key_counter_is_reported_rather_than_reused`
/// - witness: `build::tests::concurrent_minting_never_reuses_an_arena_namespace`
static NEXT_ARENA_KEY: AtomicU32 = AtomicU32::new(1u32);

/// The value of the process-local arena-key counter: the token the next
/// builder takes, or zero once every token has been taken.
///
/// # Specification
/// - requires: the counter contains the next nonzero token or exhausted zero.
/// - ensures: exhaustion is terminal and a successful transition consumes one
///   token.
/// - provides: the pure transition applied by the atomic arena-key allocator.
/// - panics: none.
/// - executable: none — this counter record has no invocation boundary; `mint`
///   carries the executable transition predicate.
///
/// # Adequacy
/// - hypothesis: L3 — local transitions at one, u32 maximum and exhausted zero
///   expose exact token/next-state pairs; concurrent minting exposes duplicate
///   arena keys without assuming a global starting value. Wraparound, token
///   reuse, skipped advancement and a non-atomic update change these
///   observations.
/// - witness: `build::tests::an_exhausted_arena_key_counter_is_reported_rather_than_reused`
/// - witness: `build::tests::concurrent_minting_never_reuses_an_arena_namespace`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct KeyCounter
{
    /// The next token, or zero when exhausted.
    next: u32,
}

/// The mutable side of a document under construction.
///
/// The builder holds the arena key it will seal into the finished arena and
/// exclusively borrows the meter every charge is recorded against, so a
/// document and its accounting cannot come apart.
///
/// # Specification
/// - requires: the builder exclusively borrows one build meter for its life.
/// - ensures: every stored edge names an earlier node in this builder.
/// - provides: the only insertion path into a document arena.
/// - fails: every constructor returns a build error rather than panicking.
/// - panics: none.
/// - executable: none — the builder is a state carrier; constructors, edge
///   checks, storage transitions and finalization are its executable
///   boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — distinct ordered children, foreign handles, the next
///   ordinal and an exhausted step budget expose exact graph edges, rendered
///   order and usage snapshots. Reversing edges, accepting another namespace,
///   charging before validation and changing an unrelated counter alter those
///   observations.
/// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
/// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
/// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
#[derive(Debug)]
pub struct DocBuilder<'meter>
{
    /// The key sealed into the finished arena.
    arena: ArenaKey,
    /// The exclusively borrowed build meter every charge lands on.
    meter: &'meter mut BuildMeter,
    /// The grow-only document node store.
    nodes: Vec<DocNode>,
    /// The grow-only text store.
    texts: Vec<CheckedText>,
    /// The grow-only verbatim store.
    verbatim: Vec<VerbatimText>,
    /// The singleton empty node identity.
    empty: NodeId,
    /// The singleton soft-line node identity.
    line: NodeId,
    /// The singleton hard-line node identity.
    hard_line: NodeId,
    /// Flattened images for original nodes in insertion order.
    flattened: Vec<NodeId>,
    /// The structural interner for flattened images.
    flatten_memo: BTreeMap<DocNode, NodeId>,
    /// The shared text identity used by flattened soft lines.
    space_text: Option<TextId>,
}

impl<'meter> DocBuilder<'meter>
{
    /// Creates a builder and inserts the three algebraic singleton nodes.
    ///
    /// # Specification
    /// - requires: `meter` is unused by another builder for this lifetime.
    /// - ensures: the builder owns distinct `Empty`, `Line`, and `HardLine`
    ///   identities before any client node is accepted.
    /// - provides: the only constructor for a mutable document build.
    /// - fails: reports arena-key exhaustion, allocation failure, or a node
    ///   ceiling below three without returning a partial builder.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the exact build failure that prevents key minting or singleton
    /// insertion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact two/three-node ceiling distinguishes
    ///   refusal from the complete singleton basis; an existing shared meter
    ///   distinguishes incrementing its node usage from resetting it. Missing
    ///   or aliased singleton nodes and a shifted admission boundary change
    ///   graph identity, usage or refusal.
    /// - witness: `algebra::tests::a_builder_with_a_node_ceiling_below_three_refuses_immediately`
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    #[anodized::spec(
        captures: before = meter.usage(),
        ensures: |ret| ret.as_ref().map_or(true,
            |builder| { let usage = builder.meter.usage();
            builder.nodes.as_slice() == [DocNode::Empty, DocNode::Line, DocNode::HardLine].as_slice()
                && u32::from(builder.empty) == 0
                && u32::from(builder.line) == 1
                && u32::from(builder.hard_line) == 2
                && builder.texts.is_empty()
                && builder.verbatim.is_empty()
                && builder.flattened.is_empty()
                && builder.flatten_memo.is_empty()
                && builder.space_text.is_none()
                && u64::from(before.doc_nodes).checked_add(3) == Some(u64::from(usage.doc_nodes))
                && usage == crate::limits::BuildUsage { doc_nodes: usage.doc_nodes, ..before } })
    )]
    #[inline]
    #[must_use = "the builder owns the document under construction"]
    pub fn try_new(meter: &'meter mut BuildMeter) -> Result<Self, BuildError>
    {
        let arena = mint_arena_key()?;
        let mut builder = Self {
            arena,
            meter,
            nodes: Vec::new(),
            texts: Vec::new(),
            verbatim: Vec::new(),
            empty: NodeId::from(0u32),
            line: NodeId::from(0u32),
            hard_line: NodeId::from(0u32),
            flattened: Vec::new(),
            flatten_memo: BTreeMap::new(),
            space_text: None,
        };
        let empty = builder.insert_node(DocNode::Empty)?;
        let line = builder.insert_node(DocNode::Line)?;
        let hard_line = builder.insert_node(DocNode::HardLine)?;
        builder.empty = empty.node_id();
        builder.line = line.node_id();
        builder.hard_line = hard_line.node_id();
        Ok(builder)
    }

    /// Returns the shared empty document handle.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn empty(&self) -> DocId
    {
        self.handle(self.empty)
    }

    /// Stores newline-free borrowed text as a document node.
    ///
    /// # Specification
    /// - requires: `text` is complete UTF-8; forbidden scalars remain in the
    ///   domain.
    /// - ensures: one text identity and one document node are stored on
    ///   success.
    /// - provides: a checked text leaf for the document algebra.
    /// - fails: rejects invalid text, allocation failure, or a build ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidText`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multibyte text, physical fragments, shared
    ///   handles and exact byte/node ceilings expose stored payloads, nominal
    ///   counts and complete usage snapshots. Duplicate storage, wrong identity
    ///   assignment, byte/scalar confusion and mutation before refusal change
    ///   those observations; allocation failure is not deterministically
    ///   injected.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.meter.usage()),
        ensures: |ret| ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && self.texts.len() == before.1
                && self.meter.usage() == before.2,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.texts.len() == before.1.saturating_add(1)
                && self.nodes.last().is_some_and(|node| matches!(*node, DocNode::Text(identity) if usize::try_from(u32::from(identity)) == Ok(before.1))))
    )]
    #[inline]
    #[must_use = "the text handle is the stored document leaf"]
    pub fn text(
        &mut self,
        text: TextSource<'_>,
    ) -> Result<DocId, BuildError>
    {
        self.store_text(CheckedText::try_from(text)?)
    }

    /// Stores newline-free owned text as a document node.
    ///
    /// # Specification
    /// - requires: `text` is complete UTF-8; forbidden scalars remain in the
    ///   domain.
    /// - ensures: the supplied allocation is moved into one text identity.
    /// - provides: an owned checked text leaf for the document algebra.
    /// - fails: rejects invalid text, allocation failure, or a build ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidText`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multibyte text, physical fragments, shared
    ///   handles and exact byte/node ceilings expose stored payloads, nominal
    ///   counts and complete usage snapshots. Duplicate storage, wrong identity
    ///   assignment, byte/scalar confusion and mutation before refusal change
    ///   those observations; allocation failure is not deterministically
    ///   injected.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.meter.usage()),
        ensures: |ret| ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && self.texts.len() == before.1
                && self.meter.usage() == before.2,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.texts.len() == before.1.saturating_add(1)
                && self.nodes.last().is_some_and(|node| matches!(*node, DocNode::Text(identity) if usize::try_from(u32::from(identity)) == Ok(before.1))))
    )]
    #[inline]
    #[must_use = "the text handle is the stored document leaf"]
    pub fn text_owned(
        &mut self,
        text: TextOwned,
    ) -> Result<DocId, BuildError>
    {
        self.store_text(CheckedText::try_from(text)?)
    }

    /// Stores borrowed verbatim text with its physical fragment metrics.
    ///
    /// # Specification
    /// - requires: `text` is complete UTF-8; bare CR remains in the domain.
    /// - ensures: bytes and one record per physical fragment are stored
    ///   together.
    /// - provides: the opaque byte-identical document leaf.
    /// - fails: rejects bare carriage returns, allocation failure, or a build
    ///   ceiling before the node becomes reachable.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidVerbatimLineEnding`, `AllocationFailed`,
    /// `ArithmeticOverflow`, or `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multibyte text, physical fragments, shared
    ///   handles and exact byte/node ceilings expose stored payloads, nominal
    ///   counts and complete usage snapshots. Duplicate storage, wrong identity
    ///   assignment, byte/scalar confusion and mutation before refusal change
    ///   those observations; allocation failure is not deterministically
    ///   injected.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.verbatim.len(), self.meter.usage()),
        ensures: |ret| ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && self.verbatim.len() == before.1
                && self.meter.usage() == before.2,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.verbatim.len() == before.1.saturating_add(1)
                && self.nodes.last().is_some_and(|node| matches!(*node, DocNode::Verbatim(identity) if usize::try_from(u32::from(identity)) == Ok(before.1))))
    )]
    #[inline]
    #[must_use = "the verbatim handle is the stored document leaf"]
    pub fn verbatim(
        &mut self,
        text: VerbatimSource<'_>,
    ) -> Result<DocId, BuildError>
    {
        self.store_verbatim(VerbatimText::try_from(text)?)
    }

    /// Stores owned verbatim text with its physical fragment metrics.
    ///
    /// # Specification
    /// - requires: `text` is complete UTF-8; bare CR remains in the domain.
    /// - ensures: the supplied bytes and their scan records move into one node.
    /// - provides: the owned opaque byte-identical document leaf.
    /// - fails: rejects bare carriage returns, allocation failure, or a build
    ///   ceiling before the node becomes reachable.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidVerbatimLineEnding`, `AllocationFailed`,
    /// `ArithmeticOverflow`, or `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multibyte text, physical fragments, shared
    ///   handles and exact byte/node ceilings expose stored payloads, nominal
    ///   counts and complete usage snapshots. Duplicate storage, wrong identity
    ///   assignment, byte/scalar confusion and mutation before refusal change
    ///   those observations; allocation failure is not deterministically
    ///   injected.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.verbatim.len(), self.meter.usage()),
        ensures: |ret| ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && self.verbatim.len() == before.1
                && self.meter.usage() == before.2,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.verbatim.len() == before.1.saturating_add(1)
                && self.nodes.last().is_some_and(|node| matches!(*node, DocNode::Verbatim(identity) if usize::try_from(u32::from(identity)) == Ok(before.1))))
    )]
    #[inline]
    #[must_use = "the verbatim handle is the stored document leaf"]
    pub fn verbatim_owned(
        &mut self,
        text: VerbatimOwned,
    ) -> Result<DocId, BuildError>
    {
        self.store_verbatim(VerbatimText::try_from(text)?)
    }

    /// Returns the shared soft-line document handle.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn line(&self) -> DocId
    {
        self.handle(self.line)
    }

    /// Returns the shared hard-line document handle.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn hard_line(&self) -> DocId
    {
        self.handle(self.hard_line)
    }

    /// Stores an unaligned concatenation of two existing documents.
    ///
    /// # Specification
    /// - requires: both arguments are candidate handles; foreign and
    ///   out-of-range handles remain in the domain.
    /// - ensures: the left edge is visited before the right edge and both point
    ///   at earlier identities.
    /// - provides: one concatenation node preserving source order.
    /// - fails: rejects foreign handles, allocation failure, or a build
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len()),
        ensures: |ret| self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.nodes.last() == Some(&DocNode::Concat { left: left.node_id(), right: right.node_id() }))
    )]
    #[inline]
    #[must_use = "the concatenation handle is the new document node"]
    pub fn concat(
        &mut self,
        left: DocId,
        right: DocId,
    ) -> Result<DocId, BuildError>
    {
        let left = self.checked_edge(left)?;
        let right = self.checked_edge(right)?;
        self.meter.check_doc_node()?;
        self.nodes
            .try_reserve(1usize)
            .map_err(|_error| BuildError::AllocationFailed {
                site: BuildAllocationSite::NodeArena,
            })?;
        self.meter.charge_doc_node()?;
        self.nodes.push(DocNode::Concat { left, right });
        let Ok(index) = u32::try_from(self.nodes.len().saturating_sub(1usize))
        else {
            return Err(BuildError::NodeIdExhausted);
        };
        Ok(self.handle(NodeId::from(index)))
    }

    /// Builds a balanced concatenation while preserving iterator order.
    ///
    /// # Specification
    /// - requires: the iterator yields candidate handles once; invalid handles
    ///   remain in the domain.
    /// - ensures: the empty input is `empty`, one item is returned unchanged,
    ///   and larger inputs form a balanced left-to-right tree.
    /// - provides: bounded-depth concatenation construction for long inputs.
    /// - fails: propagates handle, allocation, arithmetic, and build-limit
    ///   errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first typed failure raised while validating or combining the
    /// supplied handles.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, singleton, odd-length and shared input
    ///   sequences expose exact rendered order and bounded construction depth.
    ///   Dropping, duplicating or reversing an item and building a spine change
    ///   those observations. The predicate checks newly stored topology without
    ///   consuming the one-shot iterator a second time; order is witnessed
    ///   through rendering.
    /// - witness: `algebra::tests::parenthesizations_preserve_unicode_output_and_cost`
    /// - witness: `algebra::tests::empty_operands_preserve_complete_rendered_output`
    /// - witness: `algebra::tests::balanced_concatenation_preserves_odd_and_even_leaf_order`
    /// - witness: `algebra::tests::a_wide_shared_graph_finalizes_without_native_stack_growth`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len()),
        ensures: |ret| self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && ret.as_ref().map_or(true,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())).is_ok_and(|index| index < self.nodes.len())
                && self.nodes.get(before.0 ..).is_some_and(|nodes| nodes.iter().enumerate().all(|(offset, node)| matches!(*node, DocNode::Concat { left, right } if usize::try_from(u32::from(left)).is_ok_and(|index| index < before.0.saturating_add(offset))
                && usize::try_from(u32::from(right)).is_ok_and(|index| index < before.0.saturating_add(offset))))))
    )]
    #[inline]
    #[must_use = "the balanced concatenation handle is the new document"]
    pub fn concat_all<Docs>(
        &mut self,
        docs: Docs,
    ) -> Result<DocId, BuildError>
    where
        Docs: IntoIterator<Item = DocId>,
    {
        let mut current = Vec::new();
        for doc in docs {
            self.validate_doc(doc)?;
            if current.try_reserve(1usize).is_err() {
                return Err(BuildError::AllocationFailed {
                    site: BuildAllocationSite::FinalizeStack,
                });
            }
            current.push(doc);
        }
        if current.is_empty() {
            return Ok(self.empty());
        }
        loop {
            if current.len() <= 1usize {
                break;
            }
            let mut next = Vec::new();
            let mut iter = current.into_iter();
            while let Some(left) = iter.next() {
                let Some(right) = iter.next()
                else {
                    if next.try_reserve(1usize).is_err() {
                        return Err(BuildError::AllocationFailed {
                            site: BuildAllocationSite::FinalizeStack,
                        });
                    }
                    next.push(left);
                    break;
                };
                let pair = self.concat(left, right)?;
                if next.try_reserve(1usize).is_err() {
                    return Err(BuildError::AllocationFailed {
                        site: BuildAllocationSite::FinalizeStack,
                    });
                }
                next.push(pair);
            }
            current = next;
        }
        current
            .into_iter()
            .next()
            .map_or_else(|| Ok(self.empty()), Ok)
    }

    /// Stores a checked nesting node.
    ///
    /// # Specification
    /// - requires: `amount` is the requested increment and `doc` is any
    ///   candidate handle.
    /// - ensures: the amount and child identity are retained without wrapping.
    /// - provides: a nesting node for later checked indentation resolution.
    /// - fails: rejects foreign handles, allocation failure, or a build
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len()),
        ensures: |ret| self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.nodes.last() == Some(&DocNode::Nest { amount: u32::from(amount), doc: doc.node_id() }))
    )]
    #[inline]
    #[must_use = "the nesting handle is the new document node"]
    pub fn nest(
        &mut self,
        amount: NestAmount,
        doc: DocId,
    ) -> Result<DocId, BuildError>
    {
        let doc = self.checked_edge(doc)?;
        self.insert_node(DocNode::Nest {
            amount: u32::from(amount),
            doc,
        })
    }

    /// Stores an alignment node.
    ///
    /// # Specification
    /// - requires: `doc` is any candidate handle, including a foreign or
    ///   out-of-range handle.
    /// - ensures: the child is retained under an alignment boundary.
    /// - provides: an alignment node for later resolution.
    /// - fails: rejects foreign handles, allocation failure, or a build
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len()),
        ensures: |ret| self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.nodes.last() == Some(&DocNode::Align { doc: doc.node_id() }))
    )]
    #[inline]
    #[must_use = "the alignment handle is the new document node"]
    pub fn align(
        &mut self,
        doc: DocId,
    ) -> Result<DocId, BuildError>
    {
        let doc = self.checked_edge(doc)?;
        self.insert_node(DocNode::Align { doc })
    }

    /// Stores an arbitrary choice between two existing documents.
    ///
    /// # Specification
    /// - requires: both arguments are candidate handles; foreign and
    ///   out-of-range handles remain in the domain.
    /// - ensures: the left branch precedes the right branch and ties retain
    ///   that order for later resolution.
    /// - provides: a choice node with both alternatives intact.
    /// - fails: rejects foreign handles, allocation failure, or a build
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len()),
        ensures: |ret| self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.nodes.last() == Some(&DocNode::Choice { left: left.node_id(), right: right.node_id() }))
    )]
    #[inline]
    #[must_use = "the choice handle is the new document node"]
    pub fn choice(
        &mut self,
        left: DocId,
        right: DocId,
    ) -> Result<DocId, BuildError>
    {
        let left = self.checked_edge(left)?;
        let right = self.checked_edge(right)?;
        self.insert_node(DocNode::Choice { left, right })
    }

    /// Stores a flatten node over an existing document.
    ///
    /// # Specification
    /// - requires: `doc` is any candidate handle, including a foreign or
    ///   out-of-range handle.
    /// - ensures: the flatten request is retained until finalization.
    /// - provides: a node whose finalized image softens layout-owned lines.
    /// - fails: rejects foreign handles, allocation failure, or a build
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len()),
        ensures: |ret| self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.nodes.last() == Some(&DocNode::Flatten { doc: doc.node_id() }))
    )]
    #[inline]
    #[must_use = "the flatten handle is the new document node"]
    pub fn flatten(
        &mut self,
        doc: DocId,
    ) -> Result<DocId, BuildError>
    {
        let doc = self.checked_edge(doc)?;
        self.insert_node(DocNode::Flatten { doc })
    }

    /// Stores `choice(doc, flatten(doc))` in that order.
    ///
    /// # Specification
    /// - requires: `doc` is any candidate handle, including a foreign or
    ///   out-of-range handle.
    /// - ensures: the unflattened branch is the left alternative and the
    ///   flattened branch is the right alternative.
    /// - provides: the standard source-preserving grouping operation.
    /// - fails: propagates the typed failures of flattening and choice.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded` as applicable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        captures: before = self.nodes.len(),
        ensures: |ret| ret.as_ref().map_or(true,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.saturating_add(1))
                && self.nodes.len() == before.saturating_add(2)
                && self.nodes.get(before) == Some(&DocNode::Flatten { doc: doc.node_id() })
                && self.nodes.last().is_some_and(|node| matches!(*node, DocNode::Choice { left, right } if left == doc.node_id()
                && usize::try_from(u32::from(right)) == Ok(before))))
    )]
    #[inline]
    #[must_use = "the grouped handle is the new document node"]
    pub fn group(
        &mut self,
        doc: DocId,
    ) -> Result<DocId, BuildError>
    {
        let flattened = self.flatten(doc)?;
        self.choice(doc, flattened)
    }

    /// Seals the document and computes all flattened images iteratively.
    ///
    /// # Specification
    /// - requires: every builder edge already names an earlier node.
    /// - ensures: the returned arena is immutable, deterministic, and has one
    ///   flattened-image entry for every stored node.
    /// - provides: the sealed document every resolution reads.
    /// - fails: returns a typed limit, allocation, arithmetic, or identity
    ///   error without returning a partial arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns a build error when finalization cannot complete its bounded
    /// iterative pass.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged leaves, soft and hard lines, shared
    ///   subgraphs and a reached ceiling expose flat-image identity, rendered
    ///   bytes, node growth and step usage. Losing reuse, changing child order,
    ///   retaining a soft line or omitting an edge/probe charge changes those
    ///   observations; deep spines additionally witness heap rather than
    ///   native-stack traversal.
    /// - witness: `algebra::tests::flattening_is_idempotent`
    /// - witness: `algebra::tests::finalization_reuses_the_original_identity_when_nothing_changes`
    /// - witness: `algebra::tests::every_finalization_visit_edge_and_probe_charges_a_build_step`
    /// - witness: `algebra::tests::deep_left_spine_construction_uses_a_heap_work_stack`
    #[anodized::spec(
        captures: before = (self.arena, self.nodes.len()),
        ensures: |ret| ret.as_ref().map_or(true,
            |arena| { let count = u64::from(arena.node_count());
            usize::try_from(count).is_ok_and(|count| count >= before.1
                && count <= before.1.saturating_mul(2))
                && (0 .. count).all(|index| u32::try_from(index).is_ok_and(|index| { let node = NodeId::from(index);
            matches!(arena.contains(DocId::from_parts(before.0, node)), crate::arena::DocHandleStatus::Present)
                && match arena.flattened_node(node) { Maybe::Present(image) => arena.flattened_node(image) == Maybe::Present(image)
                && matches!(arena.node(image), Maybe::Present(candidate) if !matches!(candidate, DocNode::Line | DocNode::Flatten { .. })), Maybe::Absent(_) => false } })) })
    )]
    #[inline]
    #[must_use = "the sealed arena is the document's immutable result"]
    pub fn finish(mut self) -> Result<DocArena, BuildError>
    {
        let original_count = self.nodes.len();
        if self.flattened.try_reserve(original_count).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::FlattenImages,
            });
        }
        let mut index = 0usize;
        while index < original_count {
            self.meter.charge_step()?;
            let Some(node) = self.nodes.get(index).copied()
            else {
                return Err(BuildError::NodeIdExhausted);
            };
            let current = match u32::try_from(index) {
                | Ok(index) => NodeId::from(index),
                | Err(_) => return Err(BuildError::NodeIdExhausted),
            };
            let candidate = match node {
                | DocNode::Empty => DocNode::Empty,
                | DocNode::Text(text) => DocNode::Text(text),
                | DocNode::Verbatim(verbatim) => DocNode::Verbatim(verbatim),
                | DocNode::Line => {
                    let text = self.space_text_id()?;
                    DocNode::Text(text)
                },
                | DocNode::HardLine => DocNode::HardLine,
                | DocNode::Concat { left, right } => DocNode::Concat {
                    left: self.flattened_edge(left)?,
                    right: self.flattened_edge(right)?,
                },
                | DocNode::Nest { amount, doc } => DocNode::Nest {
                    amount,
                    doc: self.flattened_edge(doc)?,
                },
                | DocNode::Align { doc } => DocNode::Align {
                    doc: self.flattened_edge(doc)?,
                },
                | DocNode::Choice { left, right } => DocNode::Choice {
                    left: self.flattened_edge(left)?,
                    right: self.flattened_edge(right)?,
                },
                | DocNode::Flatten { doc } => {
                    let doc = self.flattened_edge(doc)?;
                    let Ok(index) = usize::try_from(u32::from(doc))
                    else {
                        return Err(BuildError::NodeIdExhausted);
                    };
                    let Some(image) = self.nodes.get(index).copied()
                    else {
                        return Err(BuildError::UnknownDoc);
                    };
                    image
                },
            };
            let image = if candidate == node {
                current
            }
            else {
                match self.find_flattened(candidate)? {
                    | Maybe::Present(image) => image,
                    | Maybe::Absent(interned::Absent::Unseen) => {
                        self.insert_flattened(candidate)?
                    },
                }
            };
            if self.flattened.try_reserve(1usize).is_err() {
                return Err(BuildError::AllocationFailed {
                    site: BuildAllocationSite::FlattenImages,
                });
            }
            self.flattened.push(image);
            index = index.saturating_add(1usize);
        }
        while self.flattened.len() < self.nodes.len() {
            let index = self.flattened.len();
            let Ok(index) = u32::try_from(index)
            else {
                return Err(BuildError::NodeIdExhausted);
            };
            let node = NodeId::from(index);
            if self.flattened.try_reserve(1usize).is_err() {
                return Err(BuildError::AllocationFailed {
                    site: BuildAllocationSite::FlattenImages,
                });
            }
            self.flattened.push(node);
        }
        Ok(DocArena::from_parts(
            self.arena,
            self.nodes,
            self.texts,
            self.verbatim,
            self.flattened,
        ))
    }

    /// Returns a client handle for an internal node identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn handle(
        &self,
        node: NodeId,
    ) -> DocId
    {
        DocId::from_parts(self.arena, node)
    }

    /// Validates a client handle before any store lookup.
    ///
    /// # Specification
    /// - requires: `doc` may be foreign or out of range.
    /// - ensures: success returns only a node identity present in this builder.
    /// - provides: the identity guard shared by every edge constructor.
    /// - fails: returns `UnknownDoc` before any meter charge or lookup.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc` for a foreign or out-of-range handle.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        ensures: |ret| ret == if doc.arena_key() == self.arena
                && usize::try_from(u32::from(doc.node_id())).is_ok_and(|index| index < self.nodes.len()) { Ok(doc.node_id()) }
            else { Err(BuildError::UnknownDoc) }
    )]
    #[inline]
    fn validate_doc(
        &self,
        doc: DocId,
    ) -> Result<NodeId, BuildError>
    {
        if self.arena != doc.arena_key() {
            return Err(BuildError::UnknownDoc);
        }
        let node = doc.node_id();
        let Ok(index) = usize::try_from(u32::from(node))
        else {
            return Err(BuildError::UnknownDoc);
        };
        if self.nodes.get(index).is_none() {
            return Err(BuildError::UnknownDoc);
        }
        Ok(node)
    }

    /// Validates one edge and charges its checked traversal step.
    ///
    /// # Specification
    /// - requires: `doc` is a candidate edge handle.
    /// - ensures: the edge is validated before its step is charged.
    /// - provides: the common constructor edge path.
    /// - fails: returns `UnknownDoc` or a step-limit error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `ArithmeticOverflow`, or `LimitExceeded`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct ordered children, foreign handles, the next
    ///   ordinal and an exhausted step budget expose exact graph edges,
    ///   rendered order and usage snapshots. Reversing edges, accepting another
    ///   namespace, charging before validation and changing an unrelated
    ///   counter alter those observations.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `algebra::tests::concat_resolves_the_right_at_the_left_ending_column`
    /// - witness: `algebra::tests::group_is_choice_of_the_unflattened_form_then_the_flattened_form`
    #[anodized::spec(
        captures: before = self.meter.usage(),
        ensures: |ret| { let usage = self.meter.usage();
            if doc.arena_key() == self.arena
                && usize::try_from(u32::from(doc.node_id())).is_ok_and(|index| index < self.nodes.len()) { ret.as_ref().map_or_else(|error| usage == before
                && matches!(*error, BuildError::ArithmeticOverflow { operation: BuildArithmetic::BuildSteps } | BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::BuildSteps, .. }),
            |node| *node == doc.node_id()
                && u64::from(before.build_steps).checked_add(1) == Some(u64::from(usage.build_steps))
                && usage == crate::limits::BuildUsage { build_steps: usage.build_steps, ..before }) }
            else { ret == Err(BuildError::UnknownDoc)
                && usage == before } }
    )]
    #[inline]
    fn checked_edge(
        &mut self,
        doc: DocId,
    ) -> Result<NodeId, BuildError>
    {
        let doc = self.validate_doc(doc)?;
        self.meter.check_step()?;
        self.meter.charge_step()?;
        Ok(doc)
    }

    /// Inserts one node after preflighting its node ceiling and capacity.
    ///
    /// # Specification
    /// - requires: every identity in `node` names an earlier stored node.
    /// - ensures: the node is appended exactly once and receives the next id.
    /// - provides: the common single-node insertion path.
    /// - fails: reports identity, allocation, arithmetic, or limit failure.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `NodeIdExhausted`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multibyte text, physical fragments, shared
    ///   handles and exact byte/node ceilings expose stored payloads, nominal
    ///   counts and complete usage snapshots. Duplicate storage, wrong identity
    ///   assignment, byte/scalar confusion and mutation before refusal change
    ///   those observations; allocation failure is not deterministically
    ///   injected.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.meter.usage()),
        ensures: |ret| { let usage = self.meter.usage();
            ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && usage == before.1,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.nodes.last() == Some(&node)
                && u64::from(before.1.doc_nodes).checked_add(1) == Some(u64::from(usage.doc_nodes))
                && usage == crate::limits::BuildUsage { doc_nodes: usage.doc_nodes, ..before.1 }) }
    )]
    #[inline]
    fn insert_node(
        &mut self,
        node: DocNode,
    ) -> Result<DocId, BuildError>
    {
        let Ok(index) = u32::try_from(self.nodes.len())
        else {
            return Err(BuildError::NodeIdExhausted);
        };
        self.meter.check_doc_node()?;
        if self.nodes.try_reserve(1usize).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::NodeArena,
            });
        }
        self.meter.charge_doc_node()?;
        self.nodes.push(node);
        Ok(self.handle(NodeId::from(index)))
    }

    /// Stores one text identity and its document node atomically.
    ///
    /// # Specification
    /// - requires: `text` has already passed the newline-free validation.
    /// - ensures: bytes and node usage are charged before either store grows.
    /// - provides: the shared text insertion path.
    /// - fails: returns typed identity, allocation, arithmetic, or limit
    ///   errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first typed failure found during preflight or insertion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multibyte text, physical fragments, shared
    ///   handles and exact byte/node ceilings expose stored payloads, nominal
    ///   counts and complete usage snapshots. Duplicate storage, wrong identity
    ///   assignment, byte/scalar confusion and mutation before refusal change
    ///   those observations; allocation failure is not deterministically
    ///   injected.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len(), self.meter.usage(), text.as_ref().as_ptr(), text.as_ref().len(), text.width()),
        ensures: |ret| { let usage = self.meter.usage();
            ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && usage == before.3,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.texts.len() == before.1.saturating_add(1)
                && self.verbatim.len() == before.2
                && self.nodes.last().is_some_and(|node| matches!(*node, DocNode::Text(identity) if usize::try_from(u32::from(identity)) == Ok(before.1)))
                && self.texts.last().is_some_and(|stored| stored.as_ref().as_ptr() == before.4
                && stored.as_ref().len() == before.5
                && stored.width() == before.6)
                && u64::from(before.3.doc_nodes).checked_add(1) == Some(u64::from(usage.doc_nodes))
                && u64::try_from(before.5).ok().and_then(|amount| u64::from(before.3.text_bytes).checked_add(amount)) == Some(u64::from(usage.text_bytes))
                && usage == crate::limits::BuildUsage { doc_nodes: usage.doc_nodes, text_bytes: usage.text_bytes, ..before.3 }) }
    )]
    #[inline]
    fn store_text(
        &mut self,
        text: CheckedText,
    ) -> Result<DocId, BuildError>
    {
        let Ok(text_index) = u32::try_from(self.texts.len())
        else {
            return Err(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            });
        };
        let amount = text.bytes_used()?;
        self.meter.check_text_bytes(amount)?;
        self.meter.check_doc_node()?;
        if self.texts.try_reserve(1usize).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::TextArena,
            });
        }
        if self.nodes.try_reserve(1usize).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::NodeArena,
            });
        }
        self.meter.charge_text_bytes(amount)?;
        self.meter.charge_doc_node()?;
        self.texts.push(text);
        self.nodes.push(DocNode::Text(TextId::from(text_index)));
        let Ok(node_index) = u32::try_from(self.nodes.len().saturating_sub(1usize))
        else {
            return Err(BuildError::NodeIdExhausted);
        };
        Ok(self.handle(NodeId::from(node_index)))
    }

    /// Stores one verbatim identity and its document node atomically.
    ///
    /// # Specification
    /// - requires: `text` has coherent bytes and scan records, including its
    ///   final fragment.
    /// - ensures: bytes, fragments, and node usage are charged before stores
    ///   grow.
    /// - provides: the shared verbatim insertion path.
    /// - fails: returns typed identity, allocation, arithmetic, or limit
    ///   errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first typed failure found during preflight or insertion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multibyte text, physical fragments, shared
    ///   handles and exact byte/node ceilings expose stored payloads, nominal
    ///   counts and complete usage snapshots. Duplicate storage, wrong identity
    ///   assignment, byte/scalar confusion and mutation before refusal change
    ///   those observations; allocation failure is not deterministically
    ///   injected.
    /// - witness: `build::tests::failed_builder_operations_preserve_stores_and_charge_only_valid_edges`
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[anodized::spec(
        captures: before = (self.nodes.len(), self.texts.len(), self.verbatim.len(), self.meter.usage(), text.as_ref().as_ptr(), text.as_ref().len(), text.lines().as_ptr(), text.lines().len()),
        ensures: |ret| { let usage = self.meter.usage();
            ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && self.texts.len() == before.1
                && self.verbatim.len() == before.2
                && usage == before.3,
            |handle| handle.arena_key() == self.arena
                && usize::try_from(u32::from(handle.node_id())) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.texts.len() == before.1
                && self.verbatim.len() == before.2.saturating_add(1)
                && self.nodes.last().is_some_and(|node| matches!(*node, DocNode::Verbatim(identity) if usize::try_from(u32::from(identity)) == Ok(before.2)))
                && self.verbatim.last().is_some_and(|stored| stored.as_ref().as_ptr() == before.4
                && stored.as_ref().len() == before.5
                && stored.lines().as_ptr() == before.6
                && stored.lines().len() == before.7)
                && u64::from(before.3.doc_nodes).checked_add(1) == Some(u64::from(usage.doc_nodes))
                && u64::try_from(before.5).ok().and_then(|amount| u64::from(before.3.text_bytes).checked_add(amount)) == Some(u64::from(usage.text_bytes))
                && u64::try_from(before.7).ok().and_then(|amount| u64::from(before.3.verbatim_lines).checked_add(amount)) == Some(u64::from(usage.verbatim_lines))
                && usage == crate::limits::BuildUsage { doc_nodes: usage.doc_nodes, text_bytes: usage.text_bytes, verbatim_lines: usage.verbatim_lines, ..before.3 }) }
    )]
    #[inline]
    fn store_verbatim(
        &mut self,
        text: VerbatimText,
    ) -> Result<DocId, BuildError>
    {
        let Ok(verbatim_index) = u32::try_from(self.verbatim.len())
        else {
            return Err(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            });
        };
        let bytes_used = text.bytes_used()?;
        let lines_used = text.lines_used()?;
        self.meter.check_text_bytes(bytes_used)?;
        self.meter.check_verbatim_lines(lines_used)?;
        self.meter.check_doc_node()?;
        if self.verbatim.try_reserve(1usize).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::VerbatimArena,
            });
        }
        if self.nodes.try_reserve(1usize).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::NodeArena,
            });
        }
        self.meter.charge_text_bytes(bytes_used)?;
        self.meter.charge_verbatim_lines(lines_used)?;
        self.meter.charge_doc_node()?;
        self.verbatim.push(text);
        self.nodes
            .push(DocNode::Verbatim(VerbatimId::from(verbatim_index)));
        let Ok(node_index) = u32::try_from(self.nodes.len().saturating_sub(1usize))
        else {
            return Err(BuildError::NodeIdExhausted);
        };
        Ok(self.handle(NodeId::from(node_index)))
    }
    /// # Specification
    /// - requires: `doc` is an earlier original node already visited by finish.
    /// - ensures: one edge charge precedes its flattened-image lookup.
    /// - provides: the child image used to build a parent image.
    /// - fails: reports edge-limit or identity errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc`, `ArithmeticOverflow`, or `LimitExceeded`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged leaves, soft and hard lines, shared
    ///   subgraphs and a reached ceiling expose flat-image identity, rendered
    ///   bytes, node growth and step usage. Losing reuse, changing child order,
    ///   retaining a soft line or omitting an edge/probe charge changes those
    ///   observations; deep spines additionally witness heap rather than
    ///   native-stack traversal.
    /// - witness: `algebra::tests::flattening_is_idempotent`
    /// - witness: `algebra::tests::finalization_reuses_the_original_identity_when_nothing_changes`
    /// - witness: `algebra::tests::every_finalization_visit_edge_and_probe_charges_a_build_step`
    /// - witness: `algebra::tests::deep_left_spine_construction_uses_a_heap_work_stack`
    #[anodized::spec(
        captures: before = (self.meter.usage(), usize::try_from(u32::from(doc)).ok().and_then(|index| self.flattened.get(index)).copied()),
        ensures: |ret| { let usage = self.meter.usage();
            ret.as_ref().map_or_else(|error| usage == before.0
                && (matches!(*error, BuildError::ArithmeticOverflow { operation: BuildArithmetic::BuildSteps } | BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::BuildSteps, .. }) || (*error == BuildError::UnknownDoc
                && before.1.is_none())),
            |image| before.1 == Some(*image)
                && u64::from(before.0.build_steps).checked_add(1) == Some(u64::from(usage.build_steps))
                && usage == crate::limits::BuildUsage { build_steps: usage.build_steps, ..before.0 }) }
    )]
    #[inline]
    fn flattened_edge(
        &mut self,
        doc: NodeId,
    ) -> Result<NodeId, BuildError>
    {
        self.meter.check_step()?;
        let Ok(index) = usize::try_from(u32::from(doc))
        else {
            return Err(BuildError::UnknownDoc);
        };
        let Some(image) = self.flattened.get(index).copied()
        else {
            return Err(BuildError::UnknownDoc);
        };
        self.meter.charge_step()?;
        Ok(image)
    }

    /// Finds an existing structurally equal flattened image.
    ///
    /// # Specification
    /// - requires: `candidate` is a fully mapped flattened node.
    /// - ensures: the image is the one stored for a structurally equal node, if
    ///   any; the ordered map makes the answer the same on every run.
    /// - provides: image reuse; [`interned::Absent::Unseen`] when no equal
    ///   image was stored before.
    /// - fails: reports a build-step limit or arithmetic overflow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` when a probe cannot be
    /// charged.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged leaves, soft and hard lines, shared
    ///   subgraphs and a reached ceiling expose flat-image identity, rendered
    ///   bytes, node growth and step usage. Losing reuse, changing child order,
    ///   retaining a soft line or omitting an edge/probe charge changes those
    ///   observations; deep spines additionally witness heap rather than
    ///   native-stack traversal.
    /// - witness: `algebra::tests::flattening_is_idempotent`
    /// - witness: `algebra::tests::finalization_reuses_the_original_identity_when_nothing_changes`
    /// - witness: `algebra::tests::every_finalization_visit_edge_and_probe_charges_a_build_step`
    /// - witness: `algebra::tests::deep_left_spine_construction_uses_a_heap_work_stack`
    #[anodized::spec(
        captures: before = (self.meter.usage(), self.flatten_memo.get(&candidate).copied(), self.flatten_memo.len(), self.nodes.len()),
        ensures: |ret| { let usage = self.meter.usage();
            self.flatten_memo.len() == before.2
                && self.nodes.len() == before.3
                && ret.as_ref().map_or_else(|_error| usage == before.0,
            |image| *image == before.1.map_or(Maybe::Absent(interned::Absent::Unseen), Maybe::Present)
                && u64::from(before.0.build_steps).checked_add(1) == Some(u64::from(usage.build_steps))
                && usage == crate::limits::BuildUsage { build_steps: usage.build_steps, ..before.0 }) }
    )]
    #[inline]
    fn find_flattened(
        &mut self,
        candidate: DocNode,
    ) -> Result<Maybe<NodeId, interned::Absent>, BuildError>
    {
        self.meter.check_step()?;
        let image = match self.flatten_memo.get(&candidate) {
            | Some(&image) => Maybe::Present(image),
            | None => Maybe::Absent(interned::Absent::Unseen),
        };
        self.meter.charge_step()?;
        Ok(image)
    }

    /// Inserts one distinct flattened image into the node and memo stores.
    ///
    /// # Specification
    /// - requires: `candidate` is not already in the deterministic interner.
    /// - ensures: the image is appended once and its identity is stable.
    /// - provides: a newly stored flattened node identity.
    /// - fails: reports identity, allocation, arithmetic, or node-limit errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `NodeIdExhausted`, `AllocationFailed`, `ArithmeticOverflow`, or
    /// `LimitExceeded`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged leaves, soft and hard lines, shared
    ///   subgraphs and a reached ceiling expose flat-image identity, rendered
    ///   bytes, node growth and step usage. Losing reuse, changing child order,
    ///   retaining a soft line or omitting an edge/probe charge changes those
    ///   observations; deep spines additionally witness heap rather than
    ///   native-stack traversal.
    /// - witness: `algebra::tests::flattening_is_idempotent`
    /// - witness: `algebra::tests::finalization_reuses_the_original_identity_when_nothing_changes`
    /// - witness: `algebra::tests::every_finalization_visit_edge_and_probe_charges_a_build_step`
    /// - witness: `algebra::tests::deep_left_spine_construction_uses_a_heap_work_stack`
    #[anodized::spec(
        requires: !self.flatten_memo.contains_key(&candidate), captures: before = (self.nodes.len(), self.flatten_memo.len(), self.meter.usage()),
        ensures: |ret| { let usage = self.meter.usage();
            ret.as_ref().map_or_else(|_error| self.nodes.len() == before.0
                && self.flatten_memo.len() == before.1
                && usage == before.2,
            |node| usize::try_from(u32::from(*node)) == Ok(before.0)
                && self.nodes.len() == before.0.saturating_add(1)
                && self.nodes.last() == Some(&candidate)
                && self.flatten_memo.len() == before.1.saturating_add(1)
                && self.flatten_memo.get(&candidate) == Some(node)
                && u64::from(before.2.doc_nodes).checked_add(1) == Some(u64::from(usage.doc_nodes))
                && usage == crate::limits::BuildUsage { doc_nodes: usage.doc_nodes, ..before.2 }) }
    )]
    #[inline]
    fn insert_flattened(
        &mut self,
        candidate: DocNode,
    ) -> Result<NodeId, BuildError>
    {
        let Ok(index) = u32::try_from(self.nodes.len())
        else {
            return Err(BuildError::NodeIdExhausted);
        };
        self.meter.check_doc_node()?;
        if self.nodes.try_reserve(1usize).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::NodeArena,
            });
        }
        self.meter.charge_doc_node()?;
        let node = NodeId::from(index);
        self.nodes.push(candidate);
        let _unseen = self.flatten_memo.insert(candidate, node);
        Ok(node)
    }

    /// Returns or creates the text identity used to flatten a soft line.
    ///
    /// # Specification
    /// - requires: finalization needs a flattened soft-line image.
    /// - ensures: one shared single-space text identity exists.
    /// - provides: the flattened representation of `Line`.
    /// - fails: reports allocation, arithmetic, or text-limit failure.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `AllocationFailed`, `ArithmeticOverflow`, or `LimitExceeded`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged leaves, soft and hard lines, shared
    ///   subgraphs and a reached ceiling expose flat-image identity, rendered
    ///   bytes, node growth and step usage. Losing reuse, changing child order,
    ///   retaining a soft line or omitting an edge/probe charge changes those
    ///   observations; deep spines additionally witness heap rather than
    ///   native-stack traversal.
    /// - witness: `algebra::tests::flattening_is_idempotent`
    /// - witness: `algebra::tests::finalization_reuses_the_original_identity_when_nothing_changes`
    /// - witness: `algebra::tests::every_finalization_visit_edge_and_probe_charges_a_build_step`
    /// - witness: `algebra::tests::deep_left_spine_construction_uses_a_heap_work_stack`
    #[anodized::spec(
        captures: before = (self.space_text, self.texts.len(), self.nodes.len(), self.meter.usage()),
        ensures: |ret| { let usage = self.meter.usage();
            self.nodes.len() == before.2
                && ret.as_ref().map_or_else(|_error| self.space_text == before.0
                && self.texts.len() == before.1
                && usage == before.3,
            |identity| self.space_text == Some(*identity)
                && usize::try_from(u32::from(*identity)).ok().and_then(|index| self.texts.get(index)).is_some_and(|text| text.as_ref() == " "
                && u32::from(text.width()) == 1)
                && before.0.map_or_else(|| self.texts.len() == before.1.saturating_add(1)
                && usize::try_from(u32::from(*identity)) == Ok(before.1)
                && u64::from(before.3.text_bytes).checked_add(1) == Some(u64::from(usage.text_bytes))
                && usage == crate::limits::BuildUsage { text_bytes: usage.text_bytes, ..before.3 },
            |existing| *identity == existing
                && self.texts.len() == before.1
                && usage == before.3)) }
    )]
    #[inline]
    fn space_text_id(&mut self) -> Result<TextId, BuildError>
    {
        if let Some(text) = self.space_text {
            return Ok(text);
        }
        let Ok(index) = u32::try_from(self.texts.len())
        else {
            return Err(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            });
        };
        let text = CheckedText::try_from(TextSource::from(" "))?;
        let amount = text.bytes_used()?;
        self.meter.check_text_bytes(amount)?;
        if self.texts.try_reserve(1usize).is_err() {
            return Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::TextArena,
            });
        }
        self.meter.charge_text_bytes(amount)?;
        self.texts.push(text);
        let id = TextId::from(index);
        self.space_text = Some(id);
        Ok(id)
    }
}

impl KeyCounter
{
    /// The key this counter value mints and the value the counter takes next.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a non-zero value mints its own token and advances by one, the
    ///   largest token advancing to the exhausted zero; zero mints nothing and
    ///   stays zero.
    /// - provides: the one transition every arena key is minted through.
    /// - fails: [`BuildError::ArenaKeyExhausted`] at zero.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`BuildError::ArenaKeyExhausted`] once every token is taken.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — local transitions at one, u32 maximum and exhausted
    ///   zero expose exact token/next-state pairs; concurrent minting exposes
    ///   duplicate arena keys without assuming a global starting value.
    ///   Wraparound, token reuse, skipped advancement and a non-atomic update
    ///   change these observations.
    /// - witness: `build::tests::an_exhausted_arena_key_counter_is_reported_rather_than_reused`
    /// - witness: `build::tests::concurrent_minting_never_reuses_an_arena_namespace`
    #[anodized::spec(
        ensures: |ret| NonZeroU32::new(self.next).map_or_else(|| ret == Err(BuildError::ArenaKeyExhausted),
            |token| ret.is_ok_and(|(key, next)| key == ArenaKey::from(token)
                && next.next == self.next.checked_add(1).unwrap_or(0)))
    )]
    fn mint(self) -> Result<(ArenaKey, Self), BuildError>
    {
        let Some(token) = NonZeroU32::new(self.next)
        else {
            return Err(BuildError::ArenaKeyExhausted);
        };
        let next = self.next.checked_add(1u32).unwrap_or(0u32);
        Ok((ArenaKey::from(token), Self { next }))
    }
}

/// Mints one non-zero process-local arena key.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every successful call returns a distinct non-zero token.
/// - provides: the arena identity used to reject foreign handles.
/// - fails: returns `ArenaKeyExhausted` once the counter is exhausted.
/// - panics: none.
///
/// # Errors
/// Returns `ArenaKeyExhausted` when no non-zero token remains.
///
/// # Adequacy
/// - hypothesis: L3 — local transitions at one, u32 maximum and exhausted zero
///   expose exact token/next-state pairs; concurrent minting exposes duplicate
///   arena keys without assuming a global starting value. Wraparound, token
///   reuse, skipped advancement and a non-atomic update change these
///   observations.
/// - witness: `build::tests::an_exhausted_arena_key_counter_is_reported_rather_than_reused`
/// - witness: `build::tests::concurrent_minting_never_reuses_an_arena_namespace`
#[anodized::spec(
    captures: before = NonZeroU32::new(NEXT_ARENA_KEY.load(Ordering::Relaxed)).map(ArenaKey::from),
    ensures: |ret| { let after = NonZeroU32::new(NEXT_ARENA_KEY.load(Ordering::Relaxed)).map(ArenaKey::from);
        ret.as_ref().map_or_else(|error| *error == BuildError::ArenaKeyExhausted
            && after.is_none(),
        |key| before.is_some_and(|before| *key >= before)
            && after.is_none_or(|after| *key < after)) }
)]
#[inline]
fn mint_arena_key() -> Result<ArenaKey, BuildError>
{
    let previous = NEXT_ARENA_KEY
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
            KeyCounter { next }
                .mint()
                .ok()
                .map(|(_key, counter)| counter.next)
        })
        .map_err(|_exhausted| BuildError::ArenaKeyExhausted)?;
    KeyCounter { next: previous }
        .mint()
        .map(|(key, _counter)| key)
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroU32;

    use super::KeyCounter;
    use crate::arena::ArenaKey;
    use crate::error::BuildError;

    /// The largest token is minted once and leaves the counter exhausted; the
    /// exhausted counter refuses rather than wrapping to a token already used.
    #[test]
    fn an_exhausted_arena_key_counter_is_reported_rather_than_reused()
    {
        let first = KeyCounter { next: 1u32 }.mint().unwrap();
        assert_eq!(first.0, ArenaKey::from(NonZeroU32::MIN));
        assert_eq!(first.1, KeyCounter { next: 2u32 });
        let last = KeyCounter { next: u32::MAX }.mint().unwrap();
        assert_eq!(last.0, ArenaKey::from(NonZeroU32::MAX));
        assert_eq!(
            last.1,
            KeyCounter { next: 0u32 },
            "the counter is exhausted, not wrapped"
        );
        assert_eq!(last.1.mint(), Err(BuildError::ArenaKeyExhausted));
    }

    /// Failed insertion leaves stores intact, while only previously validated
    /// edges consume steps.
    #[test]
    fn failed_builder_operations_preserve_stores_and_charge_only_valid_edges()
    {
        use super::DocBuilder;
        use crate::arena::TextOwned;
        use crate::arena::TextSource;
        use crate::arena::VerbatimSource;
        use crate::error::BuildLimitKind;
        use crate::limits::BuildLimits;
        use crate::limits::BuildMeter;
        use crate::units::LimitBound;
        use crate::units::MaxBuildSteps;
        use crate::units::MaxDocNodes;
        use crate::units::MaxTextBytes;
        use crate::units::MaxVerbatimLines;
        let foreign = {
            let mut meter = BuildMeter::new(BuildLimits::default());
            DocBuilder::try_new(&mut meter)
                .expect("foreign builder")
                .empty()
        };
        let mut meter = BuildMeter::new(BuildLimits {
            max_doc_nodes: MaxDocNodes::from(3_u32),
            max_text_bytes: MaxTextBytes::from(0_usize),
            max_verbatim_lines: MaxVerbatimLines::from(1_u32),
            max_build_steps: MaxBuildSteps::from(1_u64),
        });
        {
            let mut builder = DocBuilder::try_new(&mut meter).expect("singleton basis fits");
            let before = builder.meter.usage();
            // workflow-gates: allow-escaped-newline
            assert_eq!(
                builder.text(TextSource::from("\n")),
                Err(BuildError::InvalidText)
            );
            assert_eq!(
                builder.text_owned(TextOwned::from(alloc::string::String::from("\t"))),
                Err(BuildError::InvalidText)
            );
            assert_eq!(
                builder.verbatim(VerbatimSource::from("\r")),
                Err(BuildError::InvalidVerbatimLineEnding)
            );
            assert_eq!(
                builder.text(TextSource::from("a")),
                Err(BuildError::LimitExceeded {
                    kind: BuildLimitKind::TextBytes,
                    limit: LimitBound::from(0_u64)
                })
            );
            assert_eq!(
                builder.verbatim(VerbatimSource::from("")),
                Err(BuildError::LimitExceeded {
                    kind: BuildLimitKind::DocNodes,
                    limit: LimitBound::from(3_u64)
                })
            );
            assert_eq!(builder.meter.usage(), before);
            assert_eq!(
                (
                    builder.nodes.len(),
                    builder.texts.len(),
                    builder.verbatim.len()
                ),
                (3, 0, 0)
            );
            let empty = builder.empty();
            assert_eq!(builder.concat(empty, foreign), Err(BuildError::UnknownDoc));
            let after_edge = builder.meter.usage();
            assert_eq!(u64::from(after_edge.build_steps), 1);
            assert_eq!(after_edge, crate::limits::BuildUsage {
                build_steps: after_edge.build_steps,
                ..before
            });
            assert_eq!(builder.concat(foreign, empty), Err(BuildError::UnknownDoc));
            assert_eq!(
                builder.concat(empty, empty),
                Err(BuildError::LimitExceeded {
                    kind: BuildLimitKind::BuildSteps,
                    limit: LimitBound::from(1_u64)
                })
            );
            assert_eq!(
                builder.space_text_id(),
                Err(BuildError::LimitExceeded {
                    kind: BuildLimitKind::TextBytes,
                    limit: LimitBound::from(0_u64)
                })
            );
            assert_eq!(builder.meter.usage(), after_edge);
            assert_eq!(
                (
                    builder.nodes.len(),
                    builder.texts.len(),
                    builder.verbatim.len()
                ),
                (3, 0, 0)
            );
            assert_eq!(builder.space_text, None);
        }
        let spent = meter.usage();
        assert!(matches!(
            DocBuilder::try_new(&mut meter),
            Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::DocNodes,
                ..
            })
        ));
        assert_eq!(meter.usage(), spent);
        let mut shared_meter = BuildMeter::new(BuildLimits::default());
        drop(DocBuilder::try_new(&mut shared_meter).expect("first builder"));
        let spent = shared_meter.usage();
        let next = DocBuilder::try_new(&mut shared_meter).expect("second builder");
        assert_eq!(
            u64::from(next.meter.usage().doc_nodes),
            u64::from(spent.doc_nodes).saturating_add(3)
        );
    }

    /// Concurrent calls mint disjoint namespaces without resetting the shared
    /// counter.
    #[test]
    fn concurrent_minting_never_reuses_an_arena_namespace()
    {
        let barrier = std::sync::Barrier::new(4);
        let keys = std::thread::scope(|scope| {
            let workers = core::iter::repeat_with(|| {
                scope.spawn(|| {
                    barrier.wait();
                    core::iter::repeat_with(|| {
                        super::mint_arena_key().expect("bounded key minting")
                    })
                    .take(32)
                    .collect::<alloc::vec::Vec<_>>()
                })
            })
            .take(4)
            .collect::<alloc::vec::Vec<_>>();
            workers
                .into_iter()
                .flat_map(|worker| worker.join().expect("minting worker"))
                .collect::<alloc::vec::Vec<_>>()
        });
        let mut seen = alloc::collections::BTreeSet::new();
        for key in keys {
            assert!(seen.insert(key), "every key owns a distinct namespace");
        }
    }
}
