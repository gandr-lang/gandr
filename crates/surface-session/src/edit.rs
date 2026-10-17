//! Edit-action reconstruction: a localized structured diff of the lowered
//! core, and the localizer that maps a source range to the smallest core term
//! enclosing it.
//!
//! # Soundness is total; localization is partial
//!
//! [`diff`] aligns two revisions' items and descends each kept pair's bodies
//! together: where the two nodes have one former and one payload it goes on
//! into their children, where a leaf differs it emits one in-place action,
//! and where the formers differ it replaces the subtree wholesale. [`apply`]
//! of a diff to the old items reproduces the new items exactly, so the worst
//! a diff can be is coarse, never wrong.
//!
//! # Trees are read out of the arena, free of ids
//!
//! A [`Tree`] is one core term as a table of the incremental checker's
//! [`ContentNode`]s, numbered breadth-first from the root, with each constant
//! read as the [`Reference`] its admission position resolves to. Two
//! structurally equal terms are equal trees whatever ids their arenas gave
//! them, which is what lets two revisions, lowered into two arenas, be
//! compared at all.
//!
//! # Paths
//!
//! A [`CorePath`] names an item and the child slots from its body's root. An
//! action anchored in the old revision — a deletion, a signature change, a
//! hole filled or erased, a subtree replaced or a leaf set — carries the
//! item's old ordinal; an insertion has no old anchor and carries the new
//! ordinal.
//!
//! # Edits are a diff of the lowered core
//!
//! Each accepted submission carries the `EditScript` from the latest accepted
//! revision: the `diff` of their `Snapshot`s. A snapshot retains each item's
//! `DeclarationTree`: value signature and body roots, or a complete native data
//! signature. Each root reads out of the arena as a `Tree` of the incremental
//! checker's `ContentNode`s, numbered breadth-first, each constant read as the
//! `Reference` it resolves to, so two revisions lowered into two arenas compare
//! node by node. Items align by reference — key and occurrence — keeping the
//! largest set whose order both revisions share; each kept pair's bodies are
//! walked together, a changed literal, variable or constant becoming one
//! in-place action and any other change one `Replace` of the old subtree.
//! `apply` of a diff to the old items reproduces the new ones exactly:
//! soundness is total, localization is partial. A path names an item and the
//! child slots from its body's root; an action anchored in the old revision
//! carries the old ordinal, an insertion the new one.
//!
//! Over a named surface core the contract would carry actions for grades,
//! injection sides, binder names and annotations, and align items by a longest
//! common subsequence of their names in an `n·m` table. The core here carries
//! none of those payloads — binders are de Bruijn indices, so renaming one
//! reconstructs to no action — and its actions are the core's own leaves.
//! Because references are unique within a revision, the longest common
//! subsequence is the longest increasing run of matched old ordinals, which
//! patience sorting finds in `n log n`. The alternatives were a text diff,
//! which names bytes rather than terms, and a diff of content-addressed tables,
//! which numbers nodes and loses the path a face surfaces. The choice reverses
//! when the lowering emits structured edits itself; the session would then
//! forward them.
//!
//! Effect and control edits use the portable child ordering of
//! `gandr-core-incremental`'s `content` module. Interface and operation names,
//! clause order, frame kind and projection side participate in payload
//! agreement; operation types and binder-local bodies remain child content. A
//! metadata-only change therefore replaces its node rather than disappearing
//! from the edit script. Witness:
//! `edit::tests::control_edits_preserve_names_scopes_and_frame_order`.
//!
//! # Native declaration snapshots
//!
//! `DeclarationTree::Value`, `DeclarationTree::Data`,
//! `DeclarationTree::Abstract` and `DeclarationTree::World` preserve distinct
//! declaration categories. Data snapshots retain their kind, parameter
//! telescope and every constructor field; an abstract type its kind, its
//! representation, the extent of its seal, its minting site and the mobility
//! its signature marks; a world declaration has no roots. A schema or
//! category change replaces the item through delete/insert; native term
//! children still receive localized edits.
//! Record labels, constructor tags, nominal identities and all variadic
//! children participate in agreement. The child reader is an unbounded borrowed
//! iterator, not a fixed three-child buffer.
//!
//! `edit::native_snapshots_preserve_schema_and_fourth_children` checks literal
//! edits beneath fourth nominal arguments, constructor fields, case branches
//! and record fields, plus schema and category replacements; applying each diff
//! reconstructs the exact new snapshot. Native declarations have no runtime
//! body: evaluation returns `UnrunnableData`. No source notation or command-IL
//! implementation is inferred from retaining this programmatic content.
//!
//! **Choice.** Extend the snapshot and diff contract rather than maintain a
//! second nominal identity table. **Reversal.** A source reader or runtime
//! consumer must add its own syntax and execution rules before these native
//! items become runnable from the session.
//!
//! # Native universe-path content
//!
//! Edit snapshots retain native `Path_U` classifiers, reflexivity, equivalence
//! maps and evidence, product paths, and transport operands as the incremental
//! layer’s content nodes. Their child ordering is the ordinary constructor
//! ordering. Both ordered dialogue lists participate in non-child payload
//! agreement: an evidence-only change produces a replacement even when every
//! child is unchanged. The witness
//! `edit::tests::path_evidence_changes_are_reconstructed` observes source- and
//! target-dialogue changes separately, exact reader child order, and replay of
//! the new content. Evidence-insensitive certificate conversion is not content
//! equality. No session revision becomes a certificate admission receipt by
//! retaining this content.
//!
//! **Choice.** Extend the structural edit vocabulary rather than maintain a
//! second path identity table. These forms are programmatic core content;
//! source-level identity operations, bridge-mode observations, higher fields,
//! funext, `Flow_U` and guarded List values are not introduced by this adapter.
//! **Reversal.** An interactive identity consumer must define its own
//! application and persistence boundary over the kernel APIs.
//!
//! # Localization descends extents
//!
//! `Snapshot::localize` returns the body node whose span encloses a range with
//! the fewest bytes, the outermost of a shared span and the leftmost at one
//! depth, so a contiguous edit's locus is the common ancestor of the changes it
//! induces. Descending the nesting of the origin map does not work here, since
//! a node's recorded origin need not enclose its children: a function's lambda
//! records its parameter. A snapshot therefore spans each node by its extent,
//! the hull of its own origin and its children's extents, which nests by
//! construction. The descent examines the children of the enclosing nodes
//! alone, level by level, so its work follows the locus's depth; it keeps every
//! enclosing sibling rather than the first, which keeps it exact where a point
//! touches two siblings. A linear scan of every node is its oracle. The extent
//! step retires if the lowering's origins come to nest, when each extent equals
//! its origin.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use core::mem;

use anodized::spec;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::NodeIndex;
use gandr_core_incremental::Program;
use gandr_core_incremental::Reference;
use gandr_core_incremental::Sort;
use gandr_core_incremental::map_children;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::SplitMotive;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_surface_lowering::OriginTable;
use gandr_surface_syntax::ByteLength;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a path of a revision's core has no source span.
    pub mod spanned {
        /// The reason no span is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The path names no node of the revision.
            Unaddressed,
            /// The lowering recorded no origin for the node, nor for any node
            /// beneath it.
            Unrecorded,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a path names no node of a revision's core.
    pub mod addressed {
        /// The reason no node is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The revision holds no item at the path's ordinal.
            NoItem,
            /// The item owes its body.
            NoBody,
            /// A slot of the path names no child of the node it is read at.
            NoChild,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a source range localizes to no core term.
    pub mod located {
        /// The reason no term is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No item's body encloses the range: it falls in a signature,
            /// between declarations, or outside the source.
            Outside,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an action carries no body path.
    pub mod body_path {
        /// The reason no path is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The action edits the item list or an item's halves, not a node
            /// within a body.
            ItemLevel,
        }
    }
}

/// The position of a child among its parent's children, in the parent
/// former's order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChildSlot(usize);

impl From<usize> for ChildSlot
{
    /// The slot at position `slot`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(slot: usize) -> Self
    {
        Self(slot)
    }
}

impl From<ChildSlot> for usize
{
    /// The position `slot` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(slot: ChildSlot) -> Self
    {
        slot.0
    }
}

/// A position in a revision's lowered core: an item, and the child slots
/// from its body's root to the node.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: An item ordinal and ordered child slots identify a proposed body
///   locus; the empty slot sequence names the body root. A snapshot decides
///   whether that locus exists.
/// - executable: none — A path does not carry its snapshot or expose a callable
///   validation boundary; `Snapshot::node`, `Snapshot::span` and `path_of`
///   check its interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
/// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CorePath
{
    /// The item.
    item: ItemOrdinal,
    /// The slots from the body's root; empty for the root itself.
    slots: Vec<ChildSlot>,
}

impl CorePath
{
    /// The path from `item`'s body root through `slots`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        item: ItemOrdinal,
        slots: Vec<ChildSlot>,
    ) -> Self
    {
        Self { item, slots }
    }

    /// The item.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn item(&self) -> ItemOrdinal
    {
        self.item
    }

    /// The slots from the body's root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn slots(&self) -> &[ChildSlot]
    {
        &self.slots
    }
}

/// One core term read out of its arena: content nodes numbered breadth-first
/// from the root, the root first, each child an index into the same table.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: A body or signature is represented root-first with canonical
///   breadth-first child indices; each occurrence has its own node.
/// - executable: none — The aggregate has no callable boundary; read, subtree
///   and graft check canonical numbering, and `diff/apply` witnesses check the
///   represented term.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Tree
{
    /// The nodes, the root first.
    nodes: Vec<ContentNode>,
}

impl Tree
{
    /// The nodes, the root first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[ContentNode]
    {
        &self.nodes
    }

    /// The node `slots` reach from the root.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns root index zero for an empty path, otherwise follows
    ///   each child slot in order; the first missing step yields `NoChild`. The
    ///   caller checks whether the resulting index names a node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every child slot of hand-built multi-child body
    ///   formers and absent item/body/child paths. Exact node payloads and
    ///   distinct absence reasons distinguish slot reversal and premature or
    ///   delayed absence.
    /// - witness: `tests::edit::apply_of_diff_reproduces_new`
    /// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
    /// - witness: `tests::edit::constructor_change_is_one_replace`
    /// - witness: `edit::tests::missing_paths_and_unrecorded_origins_stay_distinct`
    #[spec(
        ensures: |ret| {
    let expected = slots
        .iter()
        .try_fold(
            NodeIndex::from(0_usize),
            |at, &slot| {
                let node = self.nodes.get(usize::from(at))?;
                children(node).nth(slot.0)
            },
        );
    match (ret, expected) {
        (Maybe::Present(found), Some(expected)) => found == expected,
        (Maybe::Absent(addressed::Absent::NoChild), None) => true,
        _ => false,
    }
},
    )]
    fn resolve(
        &self,
        slots: &[ChildSlot],
    ) -> Maybe<NodeIndex, addressed::Absent>
    {
        let mut at = NodeIndex::from(0_usize);
        for &slot in slots {
            let next = self
                .nodes
                .get(usize::from(at))
                .and_then(|node| children(node).nth(slot.0));
            match next {
                Some(child) => at = child,
                None => return Maybe::Absent(addressed::Absent::NoChild),
            }
        }
        Maybe::Present(at)
    }

    /// The subtree rooted at `root`, renumbered breadth-first from it.
    ///
    /// # Specification
    /// - requires: the reachable child graph is finite and every present child
    ///   names a node.
    /// - ensures: copies the subtree rooted at `root`, preserving formers and
    ///   payloads while renumbering every child breadth-first; an absent root
    ///   gives an empty tree.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor change at a nested node and every
    ///   multi-child body former, replayed to the independently lowered target
    ///   snapshot. Root/payload preservation and canonical child numbering are
    ///   executable; full descendant correspondence is observed by replay.
    /// - witness: `tests::edit::apply_of_diff_reproduces_new`
    /// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
    /// - witness: `tests::edit::constructor_change_is_one_replace`
    #[spec(
        ensures: |ret| match self.nodes.get(usize::from(root)) {
    Some(original) => {
        ret
            .nodes
            .first()
            .is_some_and(|node| agreement(original, node) == Agreement::Same)
            && (ret.nodes.is_empty()
                || {
                    let mut expected = 1_usize;
                    ret
                        .nodes
                        .iter()
                        .all(|node| {
                            children(node)
                                .all(|child| {
                                    let correct = usize::from(child) == expected;
                                    expected = expected.saturating_add(1_usize);
                                    correct
                                })
                        }) && expected == ret.nodes.len()
                })
    }
    None => ret.nodes.is_empty(),
},
    )]
    fn subtree(
        &self,
        root: NodeIndex,
    ) -> Self
    {
        let mut nodes = Vec::new();
        let mut queue = VecDeque::from([root]);
        let mut numbered = 1_usize;
        while let Some(index) = queue.pop_front() {
            let Some(node) = self.nodes.get(usize::from(index))
            else {
                continue;
            };
            nodes.push(map_children(node, &mut |child| {
                queue.push_back(child);
                let renumbered = NodeIndex::from(numbered);
                numbered = numbered.saturating_add(1_usize);
                renumbered
            }));
        }
        Self { nodes }
    }
}

/// Arena-independent declaration content, retaining native signatures
/// separately.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DeclarationTree
{
    /// An ordinary value declaration's independent halves.
    Value
    {
        /// Its optional classifier.
        signature: Maybe<Tree, signature::Absent>,
        /// Its body or a genuine value obligation.
        body: Maybe<Tree, body::Absent>,
    },
    /// A nominal signature; none of these roots is a value obligation.
    Data
    {
        /// The parameter telescope, in order.
        parameters: Vec<Tree>,
        /// Constructor field classifiers, in tag and field order.
        constructors: Vec<Vec<Tree>>,
        /// The declared universe.
        kind: Tree,
    },
    /// A sealed abstract type; neither root is a value obligation.
    Abstract
    {
        /// The declared universe.
        kind: Tree,
        /// The type the atom is sealed over.
        representation: Tree,
        /// How many declarations after it the seal reaches.
        extent: gandr_kernel_term::SealExtent,
        /// The site that mints the atom.
        site: gandr_core_checker::SealSite,
        /// Whether its signature marks it mobile.
        mobility: gandr_core_checker::worlds::Mobility,
    },
    /// A world declaration; it has no roots.
    World,
}

/// One item of a revision: its identity, its signature and its body, each
/// read out of the arena.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: The reference identifies the declaration; signature and body
///   images independently preserve present or owed halves.
/// - executable: none — The data declaration has no runtime invocation;
///   `Snapshot::of` checks reference and half correspondence, while
///   `diff/apply` observe their transitions.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::hole_fill_and_erase`
/// - witness: `tests::edit::item_ascription_change_is_one_set_item_ascription`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ItemTree
{
    /// The item's identity across revisions: its key and occurrence.
    reference: Reference,
    /// The declaration content, with native signatures distinct from value
    /// halves.
    declaration: DeclarationTree,
}

impl ItemTree
{
    /// The item's identity across revisions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reference(&self) -> &Reference
    {
        &self.reference
    }

    /// The complete value or nominal declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declaration(&self) -> &DeclarationTree
    {
        &self.declaration
    }

    /// The present classifier of a value declaration; native signatures are
    /// separate.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a signed and an unsigned value declaration.
    /// - witness: `edit::tests::a_value_declaration_reports_its_signature_and_an_unsigned_one_none`
    #[inline]
    #[must_use]
    pub const fn signature(&self) -> Option<&Tree>
    {
        match self.declaration {
            DeclarationTree::Value {
                signature: Maybe::Present(ref tree),
                ..
            } => Some(tree),
            DeclarationTree::Value {
                signature: Maybe::Absent(_),
                ..
            }
            | DeclarationTree::Data { .. }
            | DeclarationTree::Abstract { .. }
            | DeclarationTree::World => None,
        }
    }

    /// The present body of a value declaration. A native declaration has no
    /// body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> Option<&Tree>
    {
        match self.declaration {
            DeclarationTree::Value {
                body: Maybe::Present(ref tree),
                ..
            } => Some(tree),
            DeclarationTree::Value {
                body: Maybe::Absent(_),
                ..
            }
            | DeclarationTree::Data { .. }
            | DeclarationTree::Abstract { .. }
            | DeclarationTree::World => None,
        }
    }
}

/// How many nodes a localization examined.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Visited(usize);

/// A revision's lowered core as items of trees, with the source extent of
/// every body node.
///
/// A node's extent is the hull of its own origin and its children's extents.
/// The lowering records where each node came from, which for a function's
/// lambda is its parameter, not its body; the extent restores the nesting a
/// localizer descends by, every node enclosing everything beneath it.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: The item order agrees with the source program, body span tables
///   parallel body nodes, and indexed body extents ascend by start position.
/// - executable: none — The aggregate has no runtime invocation or source
///   program of its own; `Snapshot::of` checks its image and the localizer
///   checks source containment.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
/// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Snapshot
{
    /// The items, in source order.
    items: Vec<ItemTree>,
    /// Per item, the extent of each body node, by table index.
    spans: Vec<Vec<Maybe<ByteSpan, spanned::Absent>>>,
    /// Each body root's span beside its item, ascending by start; the bodies
    /// of distinct declarations do not overlap.
    bodies: Vec<(ByteSpan, ItemOrdinal)>,
}

impl Snapshot
{
    /// The snapshot of `program`, its nodes located through `origins`.
    ///
    /// # Specification
    /// - requires: `origins` is the origin table of the lowering `program` was
    ///   offered from.
    /// - ensures: one item per program item, in order, carrying the item's
    ///   reference and its signature and body read out of the arena, children
    ///   in each former's order; each body node spans its extent, the hull of
    ///   its recorded origin and its children's extents.
    /// - provides: the id-free image [`diff`] compares and [`Self::localize`]
    ///   descends.
    /// - panics: none.
    /// - economy: an arena node shared by two parents is read once per parent,
    ///   so a tree is as large as the term written out; the lowering shares no
    ///   body nodes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every multi-child body former in a hand-built arena,
    ///   source-localized nested terms, holes and missing origins. Exact leaf
    ///   paths and spans distinguish child permutations and lost origins;
    ///   predicates additionally check item identities, body/signature
    ///   presence, canonical numbering and sorted body extents.
    /// - witness: `tests::edit::apply_of_diff_reproduces_new`
    /// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
    /// - witness: `tests::edit::constructor_change_is_one_replace`
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
    /// - witness: `edit::tests::missing_paths_and_unrecorded_origins_stay_distinct`
    #[spec(
        ensures: |ret| {
    ret.items.len() == program.items().len() && ret.spans.len() == ret.items.len()
        && ret
            .items
            .iter()
            .zip(&ret.spans)
            .zip(program.items().iter().zip(program.references()))
            .all(|((item, spans), (original, reference))| {
                item.reference == *reference
                    && {
                        let ordered = |tree:&Tree| {
                            let mut expected = 1_usize;
                            tree.nodes.is_empty() || (tree.nodes.iter().all(|node| children(node).all(|child| {
                                let correct = usize::from(child) == expected;
                                expected = expected.saturating_add(1);correct
                            })) && expected == tree.nodes.len())
                        };
                        { let (matched_left_value, matched_right_value) = (&item.declaration,original.declaration().content());
if let DeclarationTree::Value {ref signature,ref body} = *matched_left_value && let gandr_core_checker::DeclarationContent::Value {signature:ref source_signature,body:ref source_body} = *matched_right_value { {
                                ({ let (matched_left_value, matched_right_value) = (signature,source_signature);
if let Maybe::Present(ref tree) = *matched_left_value && matches!(*matched_right_value, Maybe::Present(_)) { ordered(tree) }
 else if let Maybe::Absent(left) = *matched_left_value && let Maybe::Absent(right) = *matched_right_value { left == right }
 else { false }
}) && { let (matched_left_value, matched_right_value) = (body,source_body);
if let Maybe::Present(ref tree) = *matched_left_value && matches!(*matched_right_value, Maybe::Present(_)) { ordered(tree) && spans.len() == tree.nodes.len() }
 else if let Maybe::Absent(left) = *matched_left_value && let Maybe::Absent(right) = *matched_right_value { left == right && spans.is_empty() }
 else { false }
}
                            } }
 else if let DeclarationTree::Data {ref parameters,ref constructors,ref kind} = *matched_left_value && let gandr_core_checker::DeclarationContent::Data(ref signature) = *matched_right_value { {
                                parameters.len() == signature.parameters().len()
                                    && constructors.iter().map(Vec::len).eq(signature.constructors().iter().map(Vec::len))
                                    && parameters.iter().chain(constructors.iter().flatten()).chain(core::iter::once(kind)).all(ordered)
                                    && spans.is_empty()
                            } }
 else if let DeclarationTree::Abstract {ref kind,ref representation,extent,site,mobility} = *matched_left_value && let gandr_core_checker::DeclarationContent::Abstract(sealed) = *matched_right_value { ordered(kind) && ordered(representation) && extent == sealed.extent() && site == sealed.site() && mobility == sealed.mobility() && spans.is_empty() }
 else if matches!(*matched_left_value, DeclarationTree::World) && matches!(*matched_right_value, gandr_core_checker::DeclarationContent::World) { spans.is_empty() }
 else { false }
}
                    }
            })
        && ret
            .bodies
            .windows(2)
            .all(|pair| {
                matches!(pair, [(left, _), (right, _)] if left.start() <= right.start())
            })
        && ret.bodies.len()
            == ret
                .spans
                .iter()
                .filter(|spans| matches!(spans.first(), Some(Maybe::Present(_))))
                .count()
        && ret
            .bodies
            .iter()
            .all(|&(span, item)| {
                ret.spans
                    .get(usize::from(item))
                    .and_then(|spans| spans.first())
                    .is_some_and(|found| *found == Maybe::Present(span))
            })
},
    )]
    #[inline]
    #[must_use]
    pub fn of(
        program: &Program,
        origins: &OriginTable,
    ) -> Self
    {
        let mut items = Vec::with_capacity(program.items().len());
        let mut spans = Vec::with_capacity(program.items().len());
        let mut bodies = Vec::new();
        for (ordinal, (item, reference)) in
            program.items().iter().zip(program.references()).enumerate()
        {
            let (declaration, located) = match *(item.declaration().content()) {
                gandr_core_checker::DeclarationContent::Value {
                    ref signature,
                    ref body,
                } => {
                    let signature =
                        signature.map(|root| read(program, origins, Root::ValueType(root)).0);
                    let (body, located) = match *body {
                        Maybe::Present(root) => {
                            let (tree, located) = read(program, origins, Root::Value(root));
                            (Maybe::Present(tree), located)
                        },
                        Maybe::Absent(reason) => (Maybe::Absent(reason), Vec::new()),
                    };
                    (DeclarationTree::Value { signature, body }, located)
                },
                gandr_core_checker::DeclarationContent::Data(ref signature) => {
                    let parameters = signature
                        .parameters()
                        .iter()
                        .map(|&root| read(program, origins, Root::ValueType(root)).0)
                        .collect();
                    let constructors = signature
                        .constructors()
                        .iter()
                        .map(|fields| {
                            fields
                                .iter()
                                .map(|&root| read(program, origins, Root::ValueType(root)).0)
                                .collect()
                        })
                        .collect();
                    let kind = read(program, origins, Root::ValueType(signature.kind())).0;
                    (
                        DeclarationTree::Data {
                            parameters,
                            constructors,
                            kind,
                        },
                        Vec::new(),
                    )
                },
                gandr_core_checker::DeclarationContent::Abstract(sealed) => (
                    DeclarationTree::Abstract {
                        kind: read(program, origins, Root::ValueType(sealed.kind())).0,
                        representation: read(
                            program,
                            origins,
                            Root::ValueType(sealed.representation()),
                        )
                        .0,
                        extent: sealed.extent(),
                        site: sealed.site(),
                        mobility: sealed.mobility(),
                    },
                    Vec::new(),
                ),
                gandr_core_checker::DeclarationContent::World => {
                    (DeclarationTree::World, Vec::new())
                },
            };
            if let Some(&Maybe::Present(span)) = located.first() {
                bodies.push((span, ItemOrdinal::from(ordinal)));
            }
            items.push(ItemTree {
                reference: reference.clone(),
                declaration,
            });
            spans.push(located);
        }
        bodies.sort_by_key(|&(span, _)| span.start());
        Self {
            items,
            spans,
            bodies,
        }
    }

    /// The items, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn items(&self) -> &[ItemTree]
    {
        &self.items
    }

    /// The body node `path` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node reached from the body root of the item at
    ///   `path.item()` by taking each slot's child in turn.
    /// - fails: never; [`addressed::Absent`] names the first step that has no
    ///   node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independently named leaves of multi-child formers and
    ///   separate absent-item, absent-body and absent-child paths. Exact
    ///   payloads, borrow identity and absence tags distinguish wrong traversal
    ///   and collapsed failure causes.
    /// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
    /// - witness: `edit::tests::missing_paths_and_unrecorded_origins_stay_distinct`
    #[spec(
        ensures: |ret| {
    self.items
        .get(usize::from(path.item))
        .map_or(
            matches!(ret, Maybe::Absent(addressed::Absent::NoItem)),
            |item| item.body().map_or(matches!(ret, Maybe::Absent(addressed::Absent::NoBody)), |tree| match tree.resolve(&path.slots) {
                        Maybe::Present(index) => {
                            tree.nodes
                                .get(usize::from(index))
                                .map_or(
                                    matches!(ret, Maybe::Absent(addressed::Absent::NoChild)),
                                    |node| {
                                        matches!(
                                            ret, Maybe::Present(found) if
                                            core::ptr::eq(core::ptr::from_ref(found),
                                            core::ptr::from_ref(node))
                                        )
                                    },
                                )
                        }
                        Maybe::Absent(_) => {
                            matches!(ret, Maybe::Absent(addressed::Absent::NoChild))
                        }
                    }),
        )
},
    )]
    #[inline]
    pub fn node(
        &self,
        path: &CorePath,
    ) -> Maybe<&ContentNode, addressed::Absent>
    {
        let Some(item) = self.items.get(usize::from(path.item))
        else {
            return Maybe::Absent(addressed::Absent::NoItem);
        };
        let Some(tree) = item.body()
        else {
            return Maybe::Absent(addressed::Absent::NoBody);
        };
        tree.resolve(&path.slots).and_then(|at| {
            tree.nodes
                .get(usize::from(at))
                .map_or(Maybe::Absent(addressed::Absent::NoChild), Maybe::Present)
        })
    }

    /// The source span of the body node `path` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the extent of the node [`Self::node`] reaches: the hull of
    ///   its recorded origin and every span beneath it.
    /// - fails: never; [`spanned::Absent::Unaddressed`] when the path names no
    ///   node, [`spanned::Absent::Unrecorded`] when neither the node nor any
    ///   node beneath it has an origin.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a literal and its enclosing body, missing
    ///   item/body/child paths, and a valid node with no recorded origin. Exact
    ///   spans and distinct Unaddressed/Unrecorded reasons distinguish lost
    ///   provenance from absent nodes.
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
    /// - witness: `edit::tests::missing_paths_and_unrecorded_origins_stay_distinct`
    #[spec(
        ensures: |ret| {
    ret
        == match (
            self.items.get(usize::from(path.item)),
            self.spans.get(usize::from(path.item)),
        ) {
            (Some(item), Some(spans)) => {
                item.body().map_or(Maybe::Absent(spanned::Absent::Unaddressed), |tree| match tree.resolve(&path.slots) {
                            Maybe::Present(index) => {
                                spans
                                    .get(usize::from(index))
                                    .copied()
                                    .unwrap_or(Maybe::Absent(spanned::Absent::Unaddressed))
                            }
                            Maybe::Absent(_) => {
                                Maybe::Absent(spanned::Absent::Unaddressed)
                            }
                        })
            }
            _ => Maybe::Absent(spanned::Absent::Unaddressed),
        }
},
    )]
    #[inline]
    pub fn span(
        &self,
        path: &CorePath,
    ) -> Maybe<ByteSpan, spanned::Absent>
    {
        let (
            Some(&ItemTree {
                declaration:
                    DeclarationTree::Value {
                        body: Maybe::Present(ref tree),
                        ..
                    },
                ..
            }),
            Some(spans),
        ) = (
            self.items.get(usize::from(path.item)),
            self.spans.get(usize::from(path.item)),
        )
        else {
            return Maybe::Absent(spanned::Absent::Unaddressed);
        };
        match tree.resolve(&path.slots) {
            Maybe::Present(at) => spans
                .get(usize::from(at))
                .copied()
                .unwrap_or(Maybe::Absent(spanned::Absent::Unaddressed)),
            Maybe::Absent(_) => Maybe::Absent(spanned::Absent::Unaddressed),
        }
    }

    /// The one body that can enclose `range`: the last whose span starts at or
    /// before the range's start. Bodies ascend by start and do not overlap, so
    /// no other body can enclose it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the last body whose span starts at or before `range`'s start;
    ///   [`located::Absent::Outside`] when every body starts after it.
    /// - provides: the root [`Self::descend`] starts from, and the reading the
    ///   locus clauses state absence through.
    /// - panics: none.
    ///
    /// # Clause cost
    /// - bound: one binary search over the bodies and one read beside it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the descent built on it agrees with an independent
    ///   linear scan over five source shapes, which a candidate one body off or
    ///   past the range would break.
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(&(span, _)) => span.start() <= range.start(),
        Maybe::Absent(_) => self.bodies.first().is_none_or(|&(span, _)| range.start() < span.start()),
    })]
    fn candidate(
        &self,
        range: ByteSpan,
    ) -> Maybe<&(ByteSpan, ItemOrdinal), located::Absent>
    {
        self.bodies
            .partition_point(|&(span, _)| span.start() <= range.start())
            .checked_sub(1_usize)
            .and_then(|at| self.bodies.get(at))
            .map_or(Maybe::Absent(located::Absent::Outside), Maybe::Present)
    }

    /// The smallest body term enclosing `range`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the path of the body node whose span encloses `range` with
    ///   the fewest bytes; among nodes sharing that span the outermost, and
    ///   among those at one depth the leftmost.
    /// - provides: the core term a source range is about. Nodes the lowering
    ///   synthesised share their source's span, so the outermost of a shared
    ///   span is the common ancestor of every change an edit there induces, not
    ///   one of several overlapping descendants.
    /// - fails: never; [`located::Absent::Outside`] when no item's body
    ///   encloses the range.
    /// - panics: none.
    /// - intension: one binary search over the bodies, then a descent that
    ///   examines the children of the nodes enclosing the range and no other:
    ///   the work grows with the depth of the locus, not with the snapshot.
    ///
    /// # Adequacy
    /// - hypothesis: L2 over the node spans and endpoints of five named source
    ///   shapes: an independent linear scan orders candidates by extent, depth
    ///   and left-to-right position. L3 for traversal cost: the same nested
    ///   locus with eight and forty unrelated declarations has equal visited
    ///   counts. The predicate checks containment, and checks Outside through
    ///   [`Self::candidate`], the one body that could enclose the range,
    ///   without replaying the allocating localizer.
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
    /// - witness: `edit::tests::localize_descends_in_depth_not_map_size`
    /// - witness: `tests::edit::multi_point_edit_localizes_to_the_common_ancestor`
    #[spec(
        ensures: |ret| match ret {
    Maybe::Present(ref path) => {
        matches!(
            self.span(path), Maybe::Present(span) if span.start() <= range.start() &&
            range.end() <= span.end()
        )
    }
    Maybe::Absent(located::Absent::Outside) => {
        !matches!(self.candidate(range), Maybe::Present(&(span, _)) if range.end() <= span.end())
    }
},
    )]
    #[inline]
    pub fn localize(
        &self,
        range: ByteSpan,
    ) -> Maybe<CorePath, located::Absent>
    {
        self.descend(range).0
    }

    /// The smallest body term enclosing the bytes `edit` replaced.
    ///
    /// # Specification
    /// - requires: `edit` is measured against this snapshot's revision.
    /// - ensures: [`Self::localize`] of the edit's old extent.
    /// - provides: the term an incoming source edit touches, before the edited
    ///   revision is lowered.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a literal replacement and generated source edits,
    ///   observed at the old-span locus and reconstructed action paths. Using
    ///   new coordinates or an unrelated body changes containment or the
    ///   independent path witness. Outside is checked through
    ///   [`Self::candidate`] of the old extent.
    /// - witness: `edit::tests::edit_locus_maps_a_source_edit_to_its_old_span_locus`
    /// - witness: `tests::edit::edit_locus_contains_the_diff`
    #[spec(
        ensures: |ret| match ret {
    Maybe::Present(ref path) => {
        matches!(
            self.span(path), Maybe::Present(span) if span.start() <= edit.old.start() &&
            edit.old.end() <= span.end()
        )
    }
    Maybe::Absent(located::Absent::Outside) => {
        !matches!(self.candidate(edit.old), Maybe::Present(&(span, _)) if edit.old.end() <= span.end())
    }
},
    )]
    #[inline]
    pub fn edit_locus(
        &self,
        edit: SourceEdit,
    ) -> Maybe<CorePath, located::Absent>
    {
        self.localize(edit.old)
    }

    /// The locus of `range`, and how many nodes the descent examined.
    ///
    /// # Specification
    /// - requires: the body extents and child trees are the snapshot’s
    ///   canonical source image.
    /// - ensures: returns the smallest enclosing body term, preferring
    ///   shallower then leftmost ties, and counts the body root plus each
    ///   inspected child; Outside inspects no nodes.
    /// - panics: none.
    /// - intension: binary-searches body starts, then visits only children of
    ///   enclosing nodes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for five source shapes and their node-span endpoints
    ///   against an independent linear scan; L3 for a fixed deep locus with
    ///   increasing unrelated declarations. Exact paths and visited counts
    ///   distinguish wrong ties, skipped nodes and a whole-map traversal.
    ///   Outside is checked through [`Self::candidate`].
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
    /// - witness: `edit::tests::localize_descends_in_depth_not_map_size`
    #[spec(
        ensures: |ret| {
    (match ret.0 {
        Maybe::Present(ref path) => {
            matches!(
                self.span(path), Maybe::Present(span) if span.start() <= range.start() &&
                range.end() <= span.end()
            )
        }
        Maybe::Absent(located::Absent::Outside) => {
            !matches!(self.candidate(range), Maybe::Present(&(span, _)) if range.end() <= span.end())
        }
    })
        && match ret.0 {
            Maybe::Present(ref path) => {
                self.items
                    .get(usize::from(path.item))
                    .is_some_and(|item| match item.body() {
                        Some(tree) => {
                            ret.1.0 > 0_usize && ret.1.0 <= tree.nodes.len()
                        }
                        None => false,
                    })
            }
            Maybe::Absent(_) => ret.1.0 == 0_usize,
        }
},
    )]
    fn descend(
        &self,
        range: ByteSpan,
    ) -> (Maybe<CorePath, located::Absent>, Visited)
    {
        let outside = (Maybe::Absent(located::Absent::Outside), Visited::default());
        let encloses = |span: ByteSpan| span.start() <= range.start() && range.end() <= span.end();
        let Maybe::Present(&(root_span, item)) = self.candidate(range)
        else {
            return outside;
        };
        let (
            true,
            Some(&ItemTree {
                declaration:
                    DeclarationTree::Value {
                        body: Maybe::Present(ref tree),
                        ..
                    },
                ..
            }),
            Some(spans),
        ) = (
            encloses(root_span),
            self.items.get(usize::from(item)),
            self.spans.get(usize::from(item)),
        )
        else {
            return outside;
        };
        // Level by level, left to right, over the nodes enclosing the range:
        // a strictly smaller span displaces the best, so a tie keeps the
        // shallower node, and at one depth the leftmost.
        let mut frames = vec![Frame {
            nodes: NodeIndex::from(0_usize),
            parent: None,
            slot: ChildSlot(0_usize),
        }];
        let mut best: (ByteLength, FrameIndex) = (root_span.length(), FrameIndex(0_usize));
        let mut frontier = vec![FrameIndex(0_usize)];
        let mut visited = 1_usize;
        while !frontier.is_empty() {
            let mut next = Vec::new();
            for &at in &frontier {
                let Some(node) = frames
                    .get(at.0)
                    .and_then(|frame| tree.nodes.get(usize::from(frame.nodes)))
                else {
                    continue;
                };
                for (slot, child) in children(node).enumerate() {
                    visited = visited.saturating_add(1_usize);
                    let Some(&Maybe::Present(span)) = spans.get(usize::from(child))
                    else {
                        continue;
                    };
                    if !encloses(span) {
                        continue;
                    }
                    let reached = FrameIndex(frames.len());
                    frames.push(Frame {
                        nodes: child,
                        parent: Some(at),
                        slot: ChildSlot(slot),
                    });
                    next.push(reached);
                    if span.length() < best.0 {
                        best = (span.length(), reached);
                    }
                }
            }
            frontier = next;
        }
        (
            Maybe::Present(path_of(&frames, best.1, item)),
            Visited(visited),
        )
    }
}

/// A source edit: the bytes it replaced in the old revision, and where the
/// replacement ends in the new one.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: The old span names the replaced source extent; `new_end` names
///   the replacement end in the new revision. Localization uses old
///   coordinates.
/// - executable: none — The two source revisions needed to validate an edit are
///   not stored in this data record; `edit_locus` checks containment in the old
///   snapshot.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `edit::tests::edit_locus_maps_a_source_edit_to_its_old_span_locus`
/// - witness: `tests::edit::edit_locus_contains_the_diff`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SourceEdit
{
    /// The bytes of the old revision the edit replaced.
    old: ByteSpan,
    /// The offset in the new revision where the replacement ends.
    new_end: ByteOffset,
}

impl SourceEdit
{
    /// The edit replacing `old` with text ending at `new_end`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        old: ByteSpan,
        new_end: ByteOffset,
    ) -> Self
    {
        Self { old, new_end }
    }

    /// The bytes of the old revision the edit replaced.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn old(&self) -> ByteSpan
    {
        self.old
    }

    /// The offset in the new revision where the replacement ends.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new_end(&self) -> ByteOffset
    {
        self.new_end
    }
}

/// One localized structured edit action.
///
/// The item actions edit the list of declarations or an item's halves; the
/// path-addressed ones edit one body. [`Self::Replace`], [`Self::FillHole`]
/// and [`Self::EraseToHole`] all install or remove a whole tree, and stay
/// distinct because the distinction is what a consumer reports: a hole
/// filled, a body erased to a hole, a former replaced.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: Deletion and body/signature edits use old ordinals and paths;
///   insertion uses its new ordinal. Leaf actions retain before and after
///   payloads.
/// - executable: none — An action alone does not contain the two revisions that
///   give its anchors meaning and has no callable boundary; diff checks anchors
///   and apply witnesses check replay.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Action
{
    /// A new item, at its ordinal in the new revision.
    InsertItem
    {
        /// The item's ordinal in the new revision.
        at: ItemOrdinal,
        /// The item.
        item: ItemTree,
    },
    /// An item removed, at its ordinal in the old revision.
    DeleteItem
    {
        /// The item's ordinal in the old revision.
        at: ItemOrdinal,
    },
    /// A kept item's declared type changed, wholesale.
    SetSignature
    {
        /// The item's ordinal in the old revision.
        at: ItemOrdinal,
        /// The old declared type.
        from: Maybe<Tree, signature::Absent>,
        /// The new declared type.
        to: Maybe<Tree, signature::Absent>,
    },
    /// A kept item owed its body, and now has one.
    FillHole
    {
        /// The item's ordinal in the old revision.
        at: ItemOrdinal,
        /// The body.
        to: Tree,
    },
    /// A kept item had a body, and now owes it.
    EraseToHole
    {
        /// The item's ordinal in the old revision.
        at: ItemOrdinal,
    },
    /// A body node whose former or payload changed, replaced wholesale.
    Replace
    {
        /// The node's path in the old revision.
        path: CorePath,
        /// The new subtree.
        to: Tree,
    },
    /// A literal changed in place.
    SetLiteral
    {
        /// The literal's path in the old revision.
        path: CorePath,
        /// The old literal.
        from: Literal,
        /// The new literal.
        to: Literal,
    },
    /// A bound variable occurrence changed in place.
    SetVariable
    {
        /// The occurrence's path in the old revision.
        path: CorePath,
        /// The old zone and index.
        from: (Zone, DeBruijnIndex),
        /// The new zone and index.
        to: (Zone, DeBruijnIndex),
    },
    /// A constant changed in place to name another declaration.
    SetConstant
    {
        /// The constant's path in the old revision.
        path: CorePath,
        /// The declaration it named.
        from: Reference,
        /// The declaration it names.
        to: Reference,
    },
}

impl Action
{
    /// The body node a path-addressed action edits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: borrows the old-body path for a subtree or leaf action;
    ///   item-list and item-half actions report `ItemLevel`. The const
    ///   predicate checks the path’s own child-slot scalars; exact item and
    ///   path values are observed by witnesses.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — named leaf, constructor, insertion, deletion,
    ///   signature and hole transitions. Exact action paths and item-level
    ///   absence distinguish confusing old and new ordinals or inventing a path
    ///   for an item edit; no const equality of a foreign ordinal is assumed.
    /// - witness: `tests::edit::literal_edit_is_one_set_int`
    /// - witness: `tests::edit::item_insertion_leaves_neighbours_untouched`
    /// - witness: `tests::edit::hole_fill_and_erase`
    /// - witness: `tests::edit::constructor_change_is_one_replace`
    /// - witness: `edit::tests::missing_paths_and_unrecorded_origins_stay_distinct`
    #[spec(
        ensures: |ret| match *self {
    Self::Replace { ref path, .. }
    | Self::SetLiteral { ref path, .. }
    | Self::SetVariable { ref path, .. }
    | Self::SetConstant { ref path, .. } => {
        match ret {
            Maybe::Present(found) => {
                let mut left = found.slots.as_slice();
                let mut right = path.slots.as_slice();
                let mut equal = left.len() == right.len();
                while let (&[first, ref rest @ ..], &[second, ref tail @ ..]) = (
                    left,
                    right,
                ) {
                    if first.0 != second.0 {
                        equal = false;
                        break;
                    }
                    left = rest;
                    right = tail;
                }
                equal
            }
            Maybe::Absent(_) => false,
        }
    }
    Self::InsertItem { .. }
    | Self::DeleteItem { .. }
    | Self::SetSignature { .. }
    | Self::FillHole { .. }
    | Self::EraseToHole { .. } => {
        matches!(ret, Maybe::Absent(body_path::Absent::ItemLevel))
    }
},
    )]
    #[inline]
    pub const fn path(&self) -> Maybe<&CorePath, body_path::Absent>
    {
        match *self {
            Self::Replace { ref path, .. }
            | Self::SetLiteral { ref path, .. }
            | Self::SetVariable { ref path, .. }
            | Self::SetConstant { ref path, .. } => Maybe::Present(path),
            Self::InsertItem { .. }
            | Self::DeleteItem { .. }
            | Self::SetSignature { .. }
            | Self::FillHole { .. }
            | Self::EraseToHole { .. } => Maybe::Absent(body_path::Absent::ItemLevel),
        }
    }
}

/// The actions transforming one revision into the next.
///
/// They are kept in the order the diff emitted them: deletions by old
/// ordinal, insertions by new ordinal, then each kept item's signature, hole
/// and body actions, items in old order and body actions in pre-order.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: Actions are emitted in deletion, insertion and aligned-item
///   order, with body edits in preorder; replay produces the next item image.
/// - executable: none — A script does not own its source and target snapshots
///   or a runtime validation boundary; diff checks the emitted anchors and
///   apply/replay supplies the relational witness.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EditScript(Vec<Action>);

impl EditScript
{
    /// The actions, in emission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn actions(&self) -> &[Action]
    {
        &self.0
    }
}

/// The edit script transforming `old` into `new`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`apply`] of the script to `old`'s items equals `new`'s items.
///   Items are aligned by reference — key and occurrence — keeping the largest
///   set whose order both revisions share; an item outside it is deleted and
///   reinserted. A kept pair's differing signatures are one
///   [`Action::SetSignature`]; a body gained or lost is one
///   [`Action::FillHole`] or [`Action::EraseToHole`]; two bodies are descended
///   together, slot by slot through nodes of one former, payload and arity, a
///   differing literal, variable or constant leaf becoming one in-place action
///   and any other difference — a tuple gaining or losing a component among
///   them — one [`Action::Replace`] of the old subtree. The script is empty
///   exactly when the revisions are equal.
/// - provides: the localized edit a consumer reads instead of a text diff.
/// - panics: none.
/// - intension: alignment in time `n log n` over items by patience sorting;
///   each body pair is walked once, and a path is built only for an action.
///
/// # Adequacy
/// - hypothesis: L2 over generated revision pairs: replay is compared with the
///   independently lowered target snapshot. L3 over each named edit kind: exact
///   old paths and before/after payloads distinguish coarse, misanchored and
///   wrong-kind scripts. Predicates check identity, anchors and source payloads
///   without allocating a replay.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `tests::edit::self_diff_is_identity`
/// - witness: `tests::edit::literal_edit_is_one_set_int`
/// - witness: `tests::edit::item_insertion_leaves_neighbours_untouched`
/// - witness: `tests::edit::hole_fill_and_erase`
/// - witness: `edit::tests::a_changed_nominal_declaration_is_replaced_and_an_unchanged_one_kept`
/// - witness: `tests::edit::item_ascription_change_is_one_set_item_ascription`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `tests::edit::comp_constructor_change_is_one_replace`
/// - witness: `tests::edit::item_deletion_is_one_delete`
/// - witness: `tests::edit::multi_point_edit_localizes_to_the_common_ancestor`
/// - witness: `tests::edit::growing_a_tuple_replaces_it_325`
#[spec(
    ensures: |ret| {
    ret.0.is_empty() == (old.items == new.items)
        && ret
            .0
            .iter()
            .all(|action| match *action {
                Action::InsertItem { .. } => true,
                Action::DeleteItem { at }
                | Action::SetSignature { at, .. }
                | Action::FillHole { at, .. }
                | Action::EraseToHole { at } => usize::from(at) < old.items.len(),
                Action::Replace { ref path, .. }
                | Action::SetLiteral { ref path, .. }
                | Action::SetVariable { ref path, .. }
                | Action::SetConstant { ref path, .. } => {
                    old.items
                        .get(usize::from(path.item))
                        .is_some_and(|item| item.body().is_some_and(|tree| matches!(
                                    tree.resolve(& path.slots), Maybe::Present(index) if
                                    usize::from(index) < tree.nodes.len()
                                )))
                }
            })
        && ret
            .0
            .iter()
            .all(|action| match *action {
                Action::InsertItem { at, ref item } => {
                    new.items.get(usize::from(at)) == Some(item)
                }
                Action::SetSignature { at, ref from, .. } => {
                    old.items
                        .get(usize::from(at))
                        .is_some_and(|item| matches!(item.declaration,DeclarationTree::Value {ref signature,..} if signature == from))
                }
                Action::FillHole { at, .. } => {
                    old.items
                        .get(usize::from(at))
                        .is_some_and(|item| matches!(item.declaration,DeclarationTree::Value {body:Maybe::Absent(_),..}))
                }
                Action::EraseToHole { at } => {
                    old.items
                        .get(usize::from(at))
                        .is_some_and(|item| item.body().is_some())
                }
                Action::SetLiteral { ref path, ref from, .. } => {
                    match old.node(path) {
                        Maybe::Present(node) => {
                            matches!(
                                * node, ContentNode::Literal(ref literal) if literal == from
                            )
                        }
                        Maybe::Absent(_) => false,
                    }
                }
                Action::SetVariable { ref path, from, .. } => {
                    matches!(
                        old.node(path), Maybe::Present(& ContentNode::Variable { zone,
                        index }) if (zone, index) == from
                    )
                }
                Action::SetConstant { ref path, ref from, .. } => {
                    match old.node(path) {
                        Maybe::Present(node) => {
                            matches!(
                                * node, ContentNode::Constant(ref reference) if reference ==
                                from
                            )
                        }
                        Maybe::Absent(_) => false,
                    }
                }
                Action::DeleteItem { .. } | Action::Replace { .. } => true,
            })
},
)]
#[inline]
#[must_use]
pub fn diff(
    old: &Snapshot,
    new: &Snapshot,
) -> EditScript
{
    let kept = align(&old.items, &new.items);
    let mut actions = Vec::new();
    let mut kept_old = vec![false; old.items.len()];
    let mut kept_new = vec![false; new.items.len()];
    for &(old_at, new_at) in &kept {
        if let Some(slot) = kept_old.get_mut(usize::from(old_at)) {
            *slot = true;
        }
        if let Some(slot) = kept_new.get_mut(usize::from(new_at)) {
            *slot = true;
        }
    }
    for (at, &is_kept) in kept_old.iter().enumerate() {
        if !is_kept {
            actions.push(Action::DeleteItem {
                at: ItemOrdinal::from(at),
            });
        }
    }
    for ((at, &is_kept), item) in kept_new.iter().enumerate().zip(&new.items) {
        if !is_kept {
            actions.push(Action::InsertItem {
                at: ItemOrdinal::from(at),
                item: item.clone(),
            });
        }
    }
    for (at, new_at) in kept {
        let (Some(before), Some(after)) = (
            old.items.get(usize::from(at)),
            new.items.get(usize::from(new_at)),
        )
        else {
            continue;
        };
        let DeclarationTree::Value {
            signature: ref before_signature,
            body: ref before_body,
        } = before.declaration
        else {
            if before.declaration != after.declaration {
                actions.push(Action::DeleteItem { at });
                actions.push(Action::InsertItem {
                    at: new_at,
                    item: after.clone(),
                });
            }
            continue;
        };
        let DeclarationTree::Value {
            signature: ref after_signature,
            body: ref after_body,
        } = after.declaration
        else {
            if before.declaration != after.declaration {
                actions.push(Action::DeleteItem { at });
                actions.push(Action::InsertItem {
                    at: new_at,
                    item: after.clone(),
                });
            }
            continue;
        };
        if before_signature != after_signature {
            actions.push(Action::SetSignature {
                at,
                from: before_signature.clone(),
                to: after_signature.clone(),
            });
        }
        match (before_body, after_body) {
            (&Maybe::Absent(_), &Maybe::Absent(_)) => {},
            (&Maybe::Absent(_), &Maybe::Present(ref body)) => {
                actions.push(Action::FillHole {
                    at,
                    to: body.clone(),
                });
            },
            (&Maybe::Present(_), &Maybe::Absent(_)) => actions.push(Action::EraseToHole { at }),
            (&Maybe::Present(ref from), &Maybe::Present(ref to)) => {
                diff_trees(from, to, at, &mut actions);
            },
        }
    }
    EditScript(actions)
}

/// `old` with `script` applied.
///
/// # Specification
/// - requires: `script` was reconstructed by [`diff`] from a snapshot whose
///   items are `old`.
/// - ensures: the items of the snapshot the script was reconstructed towards.
///   An action whose anchor `old` does not hold is not applied.
/// - provides: the adjoint of [`diff`], the oracle its soundness is stated
///   against.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 over generated revision pairs: applying a diff equals the
///   independently lowered target. L3 for every action kind, each multi-child
///   slot and root replacement. The predicate checks item conservation,
///   insertion positions and the empty-script identity without rebuilding a
///   second result.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `tests::edit::self_diff_is_empty_and_apply_is_identity`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `tests::edit::hole_fill_and_erase`
/// - witness: `tests::edit::item_insertion_leaves_neighbours_untouched`
#[spec(
    ensures: |ret| {
    ret.len()
        == old
            .len()
            .saturating_sub(
                script
                    .0
                    .iter()
                    .filter(|action| matches!(action, Action::DeleteItem { .. }))
                    .count(),
            )
            .saturating_add(
                script
                    .0
                    .iter()
                    .filter(|action| matches!(action, Action::InsertItem { .. }))
                    .count(),
            ) && (!script.0.is_empty() || ret == old)
        && script
            .0
            .iter()
            .all(|action| match *action {
                Action::InsertItem { at, ref item } => {
                    ret.get(usize::from(at)) == Some(item)
                }
                Action::DeleteItem { .. } | Action::SetSignature { .. } | Action::FillHole { .. } | Action::EraseToHole { .. } | Action::Replace { .. } | Action::SetLiteral { .. } | Action::SetVariable { .. } | Action::SetConstant { .. } => true,
            })
},
)]
#[inline]
#[must_use]
pub fn apply(
    old: &[ItemTree],
    script: &EditScript,
) -> Vec<ItemTree>
{
    let mut items: Vec<Option<ItemTree>> = old.iter().cloned().map(Some).collect();
    let mut grafts: BTreeMap<ItemOrdinal, Vec<(&CorePath, Graft<'_>)>> = BTreeMap::new();
    let mut inserted: Vec<(ItemOrdinal, &ItemTree)> = Vec::new();
    for action in script.actions() {
        match *action {
            Action::InsertItem { at, ref item } => inserted.push((at, item)),
            Action::DeleteItem { at } => {
                if let Some(slot) = items.get_mut(usize::from(at)) {
                    *slot = None;
                }
            },
            Action::SetSignature { at, ref to, .. } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at))
                    && let DeclarationTree::Value {
                        ref mut signature, ..
                    } = item.declaration
                {
                    signature.clone_from(to);
                }
            },
            Action::FillHole { at, ref to } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at))
                    && let DeclarationTree::Value { ref mut body, .. } = item.declaration
                {
                    *body = Maybe::Present(to.clone());
                }
            },
            Action::EraseToHole { at } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at))
                    && let DeclarationTree::Value { ref mut body, .. } = item.declaration
                {
                    *body = Maybe::Absent(body::Absent::Hole);
                }
            },
            Action::Replace { ref path, ref to } => {
                grafts
                    .entry(path.item)
                    .or_default()
                    .push((path, Graft::Subtree(to)));
            },
            Action::SetLiteral {
                ref path, ref to, ..
            } => {
                grafts
                    .entry(path.item)
                    .or_default()
                    .push((path, Graft::Leaf(ContentNode::Literal(to.clone()))));
            },
            Action::SetVariable {
                ref path,
                to: (zone, index),
                ..
            } => {
                grafts
                    .entry(path.item)
                    .or_default()
                    .push((path, Graft::Leaf(ContentNode::Variable { zone, index })));
            },
            Action::SetConstant {
                ref path, ref to, ..
            } => {
                grafts
                    .entry(path.item)
                    .or_default()
                    .push((path, Graft::Leaf(ContentNode::Constant(to.clone()))));
            },
        }
    }
    for (at, edits) in grafts {
        if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at))
            && let DeclarationTree::Value {
                body: Maybe::Present(ref mut body),
                ..
            } = item.declaration
        {
            *body = graft(body, &edits);
        }
    }
    let mut result: Vec<ItemTree> = items.into_iter().flatten().collect();
    inserted.sort_by_key(|&(at, _)| at);
    for (at, item) in inserted {
        let position = usize::from(at).min(result.len());
        result.insert(position, item.clone());
    }
    result
}

/// What a path-addressed action installs at its node.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: A replacement is either an entire borrowed subtree or an owned
///   leaf; descendants of a replaced subtree are not edited again.
/// - executable: none — The replacement lacks the old tree and its anchor, and
///   the enum has no invocation; graft checks its installed root and canonical
///   numbering.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[derive(Clone, Debug)]
enum Graft<'script>
{
    /// A whole subtree.
    Subtree(&'script Tree),
    /// A leaf node.
    Leaf(ContentNode),
}

/// Where a rebuilt node is copied from.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: Queued nodes are read from either the original tree or the
///   particular grafted subtree that owns their index.
/// - executable: none — An original-node variant lacks its original tree;
///   interpretation is checked at graft, not at this inert queue element.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[derive(Clone, Copy, Debug)]
enum Source<'script>
{
    /// A node of the tree being rebuilt.
    Old(NodeIndex),
    /// A node of a grafted subtree.
    Grafted(&'script Tree, NodeIndex),
}

/// `tree` with each of `edits` installed at its path, renumbered
/// breadth-first.
///
/// # Specification
/// - requires: the tree and grafted subtrees have canonical breadth-first
///   numbering and finite child graphs; edits are the non-overlapping old paths
///   a diff emits.
/// - ensures: installs each addressed leaf or subtree, retains unaffected nodes
///   and renumbers the result breadth-first; an unresolved path changes
///   nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 over generated diff/replay pairs and L3 over leaf
///   replacements at every multi-child slot and a whole-body constructor
///   change. Exact target snapshots distinguish lost siblings, wrong anchors
///   and renumbering mistakes; root replacement and numbering are executable
///   without a second graft.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[spec(
    ensures: |ret| {
    (ret.nodes.is_empty()
        || {
            let mut expected = 1_usize;
            ret
                .nodes
                .iter()
                .all(|node| {
                    children(node)
                        .all(|child| {
                            let correct = usize::from(child) == expected;
                            expected = expected.saturating_add(1_usize);
                            correct
                        })
                }) && expected == ret.nodes.len()
        })
        && match edits.iter().rev().find(|edit| edit.0.slots.is_empty()) {
            Some(&(_, Graft::Subtree(subtree))) => ret == *subtree,
            Some(&(_, Graft::Leaf(ref leaf))) => {
                ret.nodes.as_slice() == core::slice::from_ref(leaf)
            }
            None => {
                match tree.nodes.first() {
                    Some(root) => {
                        ret.nodes
                            .first()
                            .is_some_and(|found| {
                                agreement(root, found) == Agreement::Same
                            })
                    }
                    None => ret.nodes.is_empty(),
                }
            }
        }
},
)]
fn graft(
    tree: &Tree,
    edits: &[(&CorePath, Graft<'_>)],
) -> Tree
{
    let mut at_node: BTreeMap<NodeIndex, &Graft<'_>> = BTreeMap::new();
    for &(path, ref edit) in edits {
        if let Maybe::Present(index) = tree.resolve(&path.slots) {
            at_node.insert(index, edit);
        }
    }
    let mut nodes = Vec::with_capacity(tree.nodes.len());
    let mut queue = VecDeque::from([Source::Old(NodeIndex::from(0_usize))]);
    let mut numbered = 1_usize;
    while let Some(source) = queue.pop_front() {
        let source = match source {
            Source::Old(index) => match at_node.get(&index) {
                Some(&&Graft::Subtree(subtree)) => {
                    Source::Grafted(subtree, NodeIndex::from(0_usize))
                },
                Some(&&Graft::Leaf(ref leaf)) => {
                    nodes.push(leaf.clone());
                    continue;
                },
                None => source,
            },
            Source::Grafted(..) => source,
        };
        let node = match source {
            Source::Old(index) => tree.nodes.get(usize::from(index)),
            Source::Grafted(subtree, index) => subtree.nodes.get(usize::from(index)),
        };
        let Some(node) = node
        else {
            continue;
        };
        nodes.push(map_children(node, &mut |child| {
            queue.push_back(match source {
                Source::Old(_) => Source::Old(child),
                Source::Grafted(subtree, _) => Source::Grafted(subtree, child),
            });
            let renumbered = NodeIndex::from(numbered);
            numbered = numbered.saturating_add(1_usize);
            renumbered
        }));
    }
    Tree { nodes }
}

/// The kept pairs of old and new ordinals: the largest set of items present
/// in both revisions by reference whose order the two share, ascending.
///
/// # Specification
/// - requires: item references are unique within each revision, as the
///   program’s key-and-occurrence scheme establishes.
/// - ensures: returns an order-preserving set of equal-reference pairs of
///   maximum cardinality; both ordinal projections strictly ascend.
/// - panics: none.
/// - intension: uses patience sorting in n log n time rather than a quadratic
///   alignment table.
///
/// # Adequacy
/// - hypothesis: L2 over all subsets and permutations of three distinct
///   references: exhaustive old subsequences independently determine the
///   maximum cardinality. Exact matched references and ascending ordinals
///   distinguish mismatched identities and order violations; replay witnesses
///   observe the resulting edits.
/// - witness: `edit::tests::alignment_matches_exhaustive_reference_subsequences`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[spec(
    ensures: |ret| {
    ret.len() <= old.len().min(new.len())
        && ret
            .iter()
            .all(|&(before, after)| {
                matches!(
                    (old.get(usize::from(before)), new.get(usize::from(after))),
                    (Some(left), Some(right)) if left.reference == right.reference
                )
            })
        && ret
            .windows(2)
            .all(|pair| {
                matches!(
                    pair, [(left_old, left_new), (right_old, right_new)] if left_old <
                    right_old && left_new < right_new
                )
            }) && (old != new || ret.len() == old.len())
},
)]
fn align(
    old: &[ItemTree],
    new: &[ItemTree],
) -> Vec<(ItemOrdinal, ItemOrdinal)>
{
    let by_reference: BTreeMap<&Reference, usize> = old
        .iter()
        .enumerate()
        .map(|(at, item)| (&item.reference, at))
        .collect();
    let candidates: Vec<(usize, usize)> = new
        .iter()
        .enumerate()
        .filter_map(|(new_at, item)| {
            by_reference
                .get(&item.reference)
                .map(|&old_at| (old_at, new_at))
        })
        .collect();
    // Patience sorting: `tails[k]` is the candidate ending the increasing run
    // of length `k + 1` with the smallest old ordinal found so far.
    let mut tails: Vec<usize> = Vec::new();
    let mut previous: Vec<Option<usize>> = Vec::with_capacity(candidates.len());
    for (index, &(old_at, _)) in candidates.iter().enumerate() {
        let length = tails.partition_point(|&tail| {
            candidates
                .get(tail)
                .is_some_and(|&(tail_old, _)| tail_old < old_at)
        });
        previous.push(
            length
                .checked_sub(1_usize)
                .and_then(|before| tails.get(before).copied()),
        );
        if let Some(slot) = tails.get_mut(length) {
            *slot = index;
        }
        else {
            tails.push(index);
        }
    }
    let mut kept = Vec::with_capacity(tails.len());
    let mut cursor = tails.last().copied();
    while let Some(index) = cursor {
        if let Some(&(old_at, new_at)) = candidates.get(index) {
            kept.push((ItemOrdinal::from(old_at), ItemOrdinal::from(new_at)));
        }
        cursor = previous.get(index).copied().flatten();
    }
    kept.reverse();
    kept
}

/// The position of a frame in a walk's frame table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct FrameIndex(usize);

/// One node, or pair of nodes, a walk reached, and how it was reached.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: A frame records its nodes, parent and child slot; parent links
///   used for paths point to earlier frames.
/// - executable: none — The frame does not know its position or enclosing frame
///   table; `path_of` checks parent indices where the complete table is
///   available.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
/// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
#[derive(Clone, Copy, Debug)]
struct Frame<Nodes>
{
    /// The node or nodes reached.
    nodes: Nodes,
    /// The frame of the parent, absent at the root.
    parent: Option<FrameIndex>,
    /// The slot the frame was reached through from its parent.
    slot: ChildSlot,
}

/// The path of the frame `at`, walking its parents.
///
/// # Specification
/// - requires: each parent points to an earlier frame, so the parent chain
///   terminates.
/// - ensures: retains `item` and returns the non-root frame slots in
///   root-to-leaf order; a missing frame terminates the chain.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — nested localized terms and each multi-child body slot,
///   with exact independently named root-to-leaf paths. Reversed slots, a
///   spurious root slot or wrong item ordinal change those paths; the
///   precondition checks parent-chain well-foundedness.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
/// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
#[spec(
    requires: frames
    .iter()
    .enumerate()
    .all(|(index, frame)| frame.parent.is_none_or(|parent| parent.0 < index)),
    ensures: |ret| {
    ret.item == item
        && {
            let mut cursor = Some(at);
            let mut slots = ret.slots.iter().rev();
            let mut exact = true;
            while let Some(index) = cursor {
                let Some(frame) = frames.get(index.0) else { break };
                if frame.parent.is_some() && slots.next() != Some(&frame.slot) {
                    exact = false;
                    break;
                }
                cursor = frame.parent;
            }
            exact && slots.next().is_none()
        }
},
)]
fn path_of<Nodes>(
    frames: &[Frame<Nodes>],
    at: FrameIndex,
    item: ItemOrdinal,
) -> CorePath
{
    let mut slots = Vec::new();
    let mut cursor = Some(at);
    while let Some(index) = cursor {
        let Some(frame) = frames.get(index.0)
        else {
            break;
        };
        if frame.parent.is_some() {
            slots.push(frame.slot);
        }
        cursor = frame.parent;
    }
    slots.reverse();
    CorePath { item, slots }
}

/// Push the actions turning the body `old` into `new`, of the item at old
/// ordinal `item`, in pre-order.
///
/// # Specification
/// - requires: both trees are finite canonical images of bodies; existing
///   actions belong to earlier items.
/// - ensures: appends only old-body paths for `item`, in preorder; equal
///   formers descend, unequal leaves become leaf actions and other differences
///   become subtree replacements. Equal trees append nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 over generated replay pairs and L3 over exact leaf and
///   constructor edits in nested and multi-child bodies. Wrong item anchors,
///   skipped changes or destructive prefix handling alter the final action
///   sequence or reconstructed target.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[spec(
    captures: before = actions.len(),
    ensures: |_| {
    actions.len() >= before
        && actions
            .get(before..)
            .is_some_and(|added| {
                added
                    .iter()
                    .all(|action| match *action {
                        Action::Replace { ref path, .. }
                        | Action::SetLiteral { ref path, .. }
                        | Action::SetVariable { ref path, .. }
                        | Action::SetConstant { ref path, .. } => {
                            path.item == item
                                && matches!(
                                    old.resolve(& path.slots), Maybe::Present(index) if
                                    usize::from(index) < old.nodes.len()
                                )
                                && matches!(
                                    new.resolve(& path.slots), Maybe::Present(index) if
                                    usize::from(index) < new.nodes.len()
                                )
                        }
                        Action::InsertItem { .. } | Action::DeleteItem { .. } | Action::SetSignature { .. } | Action::FillHole { .. } | Action::EraseToHole { .. } => false,
                    })
            }) && (old != new || actions.len() == before)
},
)]
fn diff_trees(
    old: &Tree,
    new: &Tree,
    item: ItemOrdinal,
    actions: &mut Vec<Action>,
)
{
    let root = NodeIndex::from(0_usize);
    let mut frames = vec![Frame {
        nodes: (root, root),
        parent: None,
        slot: ChildSlot(0_usize),
    }];
    let mut pending = vec![FrameIndex(0_usize)];
    while let Some(at) = pending.pop() {
        let Some(&Frame {
            nodes: (old_at, new_at),
            ..
        }) = frames.get(at.0)
        else {
            continue;
        };
        let (Some(before), Some(after)) = (
            old.nodes.get(usize::from(old_at)),
            new.nodes.get(usize::from(new_at)),
        )
        else {
            continue;
        };
        if agreement(before, after) == Agreement::Same {
            let first = frames.len();
            let (old_children, new_children) = (children(before), children(after));
            for (slot, nodes) in old_children.zip(new_children).enumerate() {
                frames.push(Frame {
                    nodes,
                    parent: Some(at),
                    slot: ChildSlot(slot),
                });
            }
            pending.extend((first .. frames.len()).rev().map(FrameIndex));
            continue;
        }
        let path = path_of(&frames, at, item);
        actions.push(match (before, after) {
            (&ContentNode::Literal(ref from), &ContentNode::Literal(ref to)) => {
                Action::SetLiteral {
                    path,
                    from: from.clone(),
                    to: to.clone(),
                }
            },
            (
                &ContentNode::Variable {
                    zone: from_zone,
                    index: from_index,
                },
                &ContentNode::Variable {
                    zone: to_zone,
                    index: to_index,
                },
            ) => Action::SetVariable {
                path,
                from: (from_zone, from_index),
                to: (to_zone, to_index),
            },
            (&ContentNode::Constant(ref from), &ContentNode::Constant(ref to)) => {
                Action::SetConstant {
                    path,
                    from: from.clone(),
                    to: to.clone(),
                }
            },
            _ => Action::Replace {
                path,
                to: new.subtree(new_at),
            },
        });
    }
}

/// Whether two nodes share their former, payload and arity.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: Same means equal former, non-child payload and child count, not
///   equal descendants; A difference requires replacing a leaf or subtree.
/// - executable: none — The comparison operands are absent from this result
///   enum; agreement carries the executable equivalence and diff/replay
///   observes its consequences.
///
/// # Adequacy
/// - hypothesis: L3 — the cited independently constructed revision images,
///   paths and edit transitions distinguish wrong identities, ordering or
///   source interpretation. The predicates live on the operations that possess
///   the necessary context.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Agreement
{
    /// One former, one payload, one arity: the walk descends into the
    /// children, pairing them slot by slot.
    Same,
    /// The former, the payload or the arity differs: the walk emits an
    /// action.
    Differs,
}

/// Whether `old` and `new` share their former, payload and arity, children
/// aside.
///
/// # Specification
/// - requires: nothing.
/// - ensures: agrees exactly on the former, the non-child payload and the
///   number of children: leaf values, injection side, classifier targets, path
///   evidence, a memory form's kind and slot, and a tuple's or product's
///   component count matter; child indices do not. The walk pairs children by
///   slot, so two nodes it descends into have every child paired.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — literal, variable, constant and constructor edits, a
///   tuple gaining a component, plus payload-bearing node pairs whose children
///   alone differ. Distinct actions and exact payloads distinguish ignoring
///   semantic data, ignoring a component the pairing would drop, or treating
///   renumbered children as a change. Independent source- and target-dialogue
///   edits retain their evidence even when every child is unchanged.
/// - witness: `tests::edit::growing_a_tuple_replaces_it_325`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `edit::tests::effect_row_edits_preserve_names_and_rebuild_operation_types`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::child_mapping_preserves_payloads_without_replaying_the_callback`
/// - witness: `edit::tests::a_memory_form_agrees_on_its_kind_and_slot`
/// - witness: `edit::tests::every_node_family_agrees_exactly_on_its_payload`
#[spec(
    ensures: |ret| {
    (ret == Agreement::Same)
        == (mem::discriminant(old) == mem::discriminant(new)
            && children(old).count() == children(new).count()
            && match *old {
                ContentNode::Data {declaration:ref left,ref arguments} => matches!(*new,ContentNode::Data {declaration:ref right,arguments:ref other} if left == right && arguments.len() == other.len()),
                ContentNode::Constructor {tag,ref fields,..} => matches!(*new,ContentNode::Constructor {tag:other,fields:ref theirs,..} if tag == other && fields.len() == theirs.len()),
                ContentNode::Record(ref fields) => matches!(*new,ContentNode::Record(ref other) if fields.keys().eq(other.keys())),
                ContentNode::RecordType(ref fields) => matches!(*new,ContentNode::RecordType(ref other) if fields.keys().eq(other.keys())),
                ContentNode::DataCase {ref branches,..} => matches!(*new,ContentNode::DataCase {branches:ref other,..} if branches.len() == other.len()),
                ContentNode::RecordProjection(_,ref label) => matches!(*new,ContentNode::RecordProjection(_,ref other) if label == other),
                ContentNode::TupleProjection(_,component) => matches!(*new,ContentNode::TupleProjection(_,other) if component == other),
                ContentNode::Reify(ref left) => matches!(*new, ContentNode::Reify(ref right) if left.iter().zip(right.iter()).all(|(left, right)| match (*left, *right) { (gandr_core_term::control::StackFrame::Apply(_), gandr_core_term::control::StackFrame::Apply(_)) | (gandr_core_term::control::StackFrame::Bind(_), gandr_core_term::control::StackFrame::Bind(_)) => true, (gandr_core_term::control::StackFrame::Project(left), gandr_core_term::control::StackFrame::Project(right)) => left == right, _ => false }) && left.len() == right.len()),
                ContentNode::Project(left, _) => matches!(*new, ContentNode::Project(right, _) if left == right),
                ContentNode::Perform { signature: ref left, operation: ref first, .. } => matches!(*new, ContentNode::Perform { signature: ref right, operation: ref second, .. } if first == second && left.name() == right.name() && left.operations().map(|op| &op.name).eq(right.operations().map(|op| &op.name))),
                ContentNode::Handle { signature: ref left, clauses: ref first, .. } => matches!(*new, ContentNode::Handle { signature: ref right, clauses: ref second, .. } if first.iter().map(|clause| &clause.operation).eq(second.iter().map(|clause| &clause.operation)) && left.name() == right.name() && left.operations().map(|op| &op.name).eq(right.operations().map(|op| &op.name))),
                ContentNode::Returner { effects: ref left, .. } => matches!(*new, ContentNode::Returner { effects: ref right, .. } if left.signatures().len() == right.signatures().len() && left.signatures().zip(right.signatures()).all(|(left, right)| left.name() == right.name() && left.operations().len() == right.operations().len() && left.operations().zip(right.operations()).all(|(left, right)| left.name == right.name))),
                ContentNode::Exercise { signature: ref left, operation: ref first, .. } => matches!(*new, ContentNode::Exercise { signature: ref right, operation: ref second, .. } if first == second && left.name() == right.name() && left.operations().map(|op| &op.name).eq(right.operations().map(|op| &op.name))),
                ContentNode::Scope { signature: ref left, clauses: ref first, .. } => matches!(*new, ContentNode::Scope { signature: ref right, clauses: ref second, .. } if first.iter().map(|clause| &clause.operation).eq(second.iter().map(|clause| &clause.operation)) && left.name() == right.name() && left.operations().map(|op| &op.name).eq(right.operations().map(|op| &op.name))),
                ContentNode::Capability { authority: ref left, grade, region } => matches!(*new, ContentNode::Capability { authority: ref right, grade: other_grade, region: other_region } if grade == other_grade && region == other_region && left.signatures().len() == right.signatures().len() && left.signatures().zip(right.signatures()).all(|(left, right)| left.name() == right.name() && left.operations().len() == right.operations().len() && left.operations().zip(right.operations()).all(|(left, right)| left.name == right.name))),
                ContentNode::PathEquiv { evidence: ref left, .. } => {
                    matches!(
                        * new, ContentNode::PathEquiv { evidence : ref right, .. } if
                        left == right
                    )
                }
                ContentNode::Injection(left, _) => {
                    matches!(* new, ContentNode::Injection(right, _) if left == right)
                }
                ContentNode::ValueLift { target: ref left, .. } => {
                    matches!(
                        * new, ContentNode::ValueLift { target : ref right, .. } if left
                        == right
                    )
                }
                ContentNode::TypeLift { target: ref left, .. } => {
                    matches!(
                        * new, ContentNode::TypeLift { target : ref right, .. } if left
                        == right
                    )
                }
                ContentNode::Element { target: ref left, .. } => {
                    matches!(
                        * new, ContentNode::Element { target : ref right, .. } if left ==
                        right
                    )
                }
                ContentNode::ComputationElement { target: ref left, .. } => {
                    matches!(
                        * new, ContentNode::ComputationElement { target : ref right, .. }
                        if left == right
                    )
                }
                ContentNode::Memory(ref left) => matches!(*new, ContentNode::Memory(ref right) if left.shape() == right.shape()),
                _ if children(old).next().is_none() => old == new,
                ContentNode::Stack { .. } | ContentNode::WithType(..) | ContentNode::Resume(..) | ContentNode::Split(..) | ContentNode::DependentSplit { .. } | ContentNode::Reset(_) | ContentNode::Shift(_) | ContentNode::With(..) | ContentNode::Ascribe { .. } | ContentNode::PrimitiveValue(_) | ContentNode::Primitive(..) | ContentNode::PathUniverse(..) | ContentNode::PathRefl(_) | ContentNode::PathProduct(..) | ContentNode::Funext(..) | ContentNode::Equiv(..) | ContentNode::Ua { .. } | ContentNode::Transport(..) | ContentNode::PathType { .. } | ContentNode::Here(_) | ContentNode::Returned(_) | ContentNode::Nested(_) | ContentNode::Run(_) | ContentNode::ElementTransport { .. } | ContentNode::TelescopeTransport { .. } | ContentNode::SessionRelated { .. } | ContentNode::Stay(_) | ContentNode::Then(..) | ContentNode::Forward(_) | ContentNode::FunctionFlow(..) | ContentNode::FlowProduct(..) | ContentNode::Recorded(_) | ContentNode::Ride { .. } | ContentNode::FlowType { .. } | ContentNode::RunType(_) | ContentNode::Variable { .. } | ContentNode::Constant(_) | ContentNode::Literal(_) | ContentNode::Tuple(_) | ContentNode::ListNil | ContentNode::ListCons(..) | ContentNode::Thunk(_) | ContentNode::Quote(_) | ContentNode::QuoteComputation(_) | ContentNode::StaticLambda(_) | ContentNode::StaticApplication(..) | ContentNode::Hole(_) | ContentNode::ValueMark { .. } | ContentNode::Lambda(_) | ContentNode::Application(..) | ContentNode::Return(_) | ContentNode::Bind(..) | ContentNode::Force(_) | ContentNode::Case { .. } | ContentNode::ComputationHole(_) | ContentNode::ComputationMark { .. } | ContentNode::Fixpoint { .. } | ContentNode::ListFold { .. } | ContentNode::Session(_) | ContentNode::Base(_) | ContentNode::Product(_) | ContentNode::Sum(_) | ContentNode::List(_) | ContentNode::ThunkType(_) | ContentNode::Universe { .. } | ContentNode::StaticPi { .. } | ContentNode::Sigma { .. } | ContentNode::SessionType(_) | ContentNode::Abstract(_) | ContentNode::UnknownType | ContentNode::Arrow { .. } | ContentNode::Pi { .. } | ContentNode::UnknownComputationType | ContentNode::Unresolved(_) => true,
            })
},
)]
fn agreement(
    old: &ContentNode,
    new: &ContentNode,
) -> Agreement
{
    let same = match (old, new) {
        (&ContentNode::Reify(ref left), &ContentNode::Reify(ref right)) => {
            left.iter()
                .zip(right.iter())
                .all(|(left, right)| match (*left, *right) {
                    (
                        gandr_core_term::control::StackFrame::Apply(_),
                        gandr_core_term::control::StackFrame::Apply(_),
                    )
                    | (
                        gandr_core_term::control::StackFrame::Bind(_),
                        gandr_core_term::control::StackFrame::Bind(_),
                    ) => true,
                    (
                        gandr_core_term::control::StackFrame::Project(left),
                        gandr_core_term::control::StackFrame::Project(right),
                    ) => left == right,
                    _ => false,
                })
                && left.len() == right.len()
        },
        (&ContentNode::Project(left, _), &ContentNode::Project(right, _)) => left == right,
        (&ContentNode::Injection(left, _), &ContentNode::Injection(right, _)) => left == right,
        (
            &ContentNode::Perform {
                signature: ref left,
                operation: ref first,
                ..
            },
            &ContentNode::Perform {
                signature: ref right,
                operation: ref second,
                ..
            },
        ) => {
            first == second
                && left.name() == right.name()
                && left
                    .operations()
                    .map(|op| &op.name)
                    .eq(right.operations().map(|op| &op.name))
        },
        (
            &ContentNode::Handle {
                signature: ref left,
                clauses: ref first,
                ..
            },
            &ContentNode::Handle {
                signature: ref right,
                clauses: ref second,
                ..
            },
        ) => {
            first
                .iter()
                .map(|clause| &clause.operation)
                .eq(second.iter().map(|clause| &clause.operation))
                && left.name() == right.name()
                && left
                    .operations()
                    .map(|op| &op.name)
                    .eq(right.operations().map(|op| &op.name))
        },
        (
            &ContentNode::Returner {
                effects: ref left, ..
            },
            &ContentNode::Returner {
                effects: ref right, ..
            },
        ) => {
            left.signatures().len() == right.signatures().len()
                && left
                    .signatures()
                    .zip(right.signatures())
                    .all(|(left, right)| {
                        left.name() == right.name()
                            && left.operations().len() == right.operations().len()
                            && left
                                .operations()
                                .zip(right.operations())
                                .all(|(left, right)| left.name == right.name)
                    })
        },
        (
            &ContentNode::Exercise {
                signature: ref left,
                operation: ref first,
                ..
            },
            &ContentNode::Exercise {
                signature: ref right,
                operation: ref second,
                ..
            },
        ) => {
            first == second
                && left.name() == right.name()
                && left
                    .operations()
                    .map(|op| &op.name)
                    .eq(right.operations().map(|op| &op.name))
        },
        (
            &ContentNode::Scope {
                signature: ref left,
                clauses: ref first,
                ..
            },
            &ContentNode::Scope {
                signature: ref right,
                clauses: ref second,
                ..
            },
        ) => {
            first
                .iter()
                .map(|clause| &clause.operation)
                .eq(second.iter().map(|clause| &clause.operation))
                && left.name() == right.name()
                && left
                    .operations()
                    .map(|op| &op.name)
                    .eq(right.operations().map(|op| &op.name))
        },
        (
            &ContentNode::Capability {
                authority: ref left,
                grade: first_grade,
                region: first_region,
            },
            &ContentNode::Capability {
                authority: ref right,
                grade: second_grade,
                region: second_region,
            },
        ) => {
            first_grade == second_grade
                && first_region == second_region
                && left.signatures().len() == right.signatures().len()
                && left
                    .signatures()
                    .zip(right.signatures())
                    .all(|(left, right)| {
                        left.name() == right.name()
                            && left.operations().len() == right.operations().len()
                            && left
                                .operations()
                                .zip(right.operations())
                                .all(|(left, right)| left.name == right.name)
                    })
        },
        (
            &ContentNode::Data {
                declaration: ref left,
                arguments: ref a,
            },
            &ContentNode::Data {
                declaration: ref right,
                arguments: ref b,
            },
        ) => left == right && a.len() == b.len(),
        (
            &ContentNode::Constructor {
                tag: a,
                fields: ref left,
                ..
            },
            &ContentNode::Constructor {
                tag: b,
                fields: ref right,
                ..
            },
        ) => a == b && left.len() == right.len(),
        (&ContentNode::Record(ref left), &ContentNode::Record(ref right))
        | (&ContentNode::RecordType(ref left), &ContentNode::RecordType(ref right)) => {
            left.keys().eq(right.keys())
        },
        (
            &ContentNode::DataCase {
                branches: ref left, ..
            },
            &ContentNode::DataCase {
                branches: ref right,
                ..
            },
        ) => left.len() == right.len(),
        (
            &ContentNode::RecordProjection(_, ref left),
            &ContentNode::RecordProjection(_, ref right),
        ) => left == right,
        (&ContentNode::TupleProjection(_, left), &ContentNode::TupleProjection(_, right)) => {
            left == right
        },
        (
            &ContentNode::PathEquiv {
                evidence: ref left, ..
            },
            &ContentNode::PathEquiv {
                evidence: ref right,
                ..
            },
        ) => left == right,
        (
            &ContentNode::ValueLift {
                target: ref left, ..
            },
            &ContentNode::ValueLift {
                target: ref right, ..
            },
        )
        | (
            &ContentNode::TypeLift {
                target: ref left, ..
            },
            &ContentNode::TypeLift {
                target: ref right, ..
            },
        )
        | (
            &ContentNode::Element {
                target: ref left, ..
            },
            &ContentNode::Element {
                target: ref right, ..
            },
        )
        | (
            &ContentNode::ComputationElement {
                target: ref left, ..
            },
            &ContentNode::ComputationElement {
                target: ref right, ..
            },
        ) => left == right,
        (&ContentNode::Memory(ref left), &ContentNode::Memory(ref right)) => {
            left.shape() == right.shape()
        },
        _ if children(old).next().is_none() => old == new,
        _ => mem::discriminant(old) == mem::discriminant(new),
    };
    if same && children(old).count() == children(new).count() {
        Agreement::Same
    }
    else {
        Agreement::Differs
    }
}

/// The canonical children of a node, with sort annotations omitted.
///
/// # Specification
/// trivial.
fn children(node: &ContentNode) -> impl DoubleEndedIterator<Item = NodeIndex> + Clone + '_
{
    node.child_indices().map(|(child, _)| child)
}

/// The root a tree is read from.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: Each arena identifier retains the sort in which it must be read;
///   a missing entry yields Unresolved of that sort.
/// - executable: none — The enum does not hold the arena that gives an
///   identifier meaning; read and the four sort-specific readers check the
///   interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — missing roots of all four arena sorts and independently
///   named child paths. Exact sort tags and replay images distinguish
///   misinterpretation.
/// - witness: `edit::tests::absent_arena_roots_keep_their_sorts`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
#[derive(Clone, Copy, Debug)]
enum Root
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// The tree rooted at `root` in `program`'s arena, and each node's span.
///
/// # Specification
/// - requires: the reachable arena graph is finite, and origins refer to the
///   same arena.
/// - ensures: returns the root-first breadth-first content image with one span
///   entry per node; missing entries retain their arena sort, and recorded
///   extents enclose every recorded descendant.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — multi-child body terms, nested source extents and absent
///   roots of all four sorts. Exact node paths, source slices and
///   unresolved-sort tags distinguish shape, numbering and provenance errors; a
///   direct span-hull witness separates absent origins from recorded
///   descendants.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
/// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
/// - witness: `edit::tests::absent_arena_roots_keep_their_sorts`
/// - witness: `edit::tests::hulls_cover_descendants_without_inventing_origins`
#[spec(
    ensures: |ret| {
    ret.0.nodes.len() == ret.1.len() && !ret.0.nodes.is_empty()
        && (ret.0.nodes.is_empty()
            || {
                let mut expected = 1_usize;
                ret
                    .0
                    .nodes
                    .iter()
                    .all(|node| {
                        children(node)
                            .all(|child| {
                                let correct = usize::from(child) == expected;
                                expected = expected.saturating_add(1_usize);
                                correct
                            })
                    }) && expected == ret.0.nodes.len()
            })
        && ret
            .0
            .nodes
            .iter()
            .enumerate()
            .all(|(index, node)| {
                children(node)
                    .all(|child| match ret.1.get(usize::from(child)) {
                        Some(&Maybe::Present(child_span)) => {
                            matches!(
                                ret.1.get(index), Some(& Maybe::Present(parent)) if parent
                                .start() <= child_span.start() && child_span.end() <= parent
                                .end()
                            )
                        }
                        _ => true,
                    })
            })
},
)]
fn read(
    program: &Program,
    origins: &OriginTable,
    root: Root,
) -> (Tree, Vec<Maybe<ByteSpan, spanned::Absent>>)
{
    let mut nodes = Vec::new();
    let mut spans = Vec::new();
    let mut queue = VecDeque::from([root]);
    let mut numbered = 1_usize;
    while let Some(at) = queue.pop_front() {
        let mut child = |next: Root| {
            queue.push_back(next);
            let index = NodeIndex::from(numbered);
            numbered = numbered.saturating_add(1_usize);
            index
        };
        let (node, origin) = match at {
            Root::Value(id) => (read_value(program, id, &mut child), origins.value(id)),
            Root::Computation(id) => (
                read_computation(program, id, &mut child),
                origins.computation(id),
            ),
            Root::ValueType(id) => (
                read_value_type(program, id, &mut child),
                origins.value_type(id),
            ),
            Root::CompType(id) => (
                read_comp_type(program, id, &mut child),
                origins.comp_type(id),
            ),
        };
        nodes.push(node);
        spans.push(match origin {
            Maybe::Present(origin) => Maybe::Present(origin.span()),
            Maybe::Absent(_) => Maybe::Absent(spanned::Absent::Unrecorded),
        });
    }
    let tree = Tree { nodes };
    hull(&tree, &mut spans);
    (tree, spans)
}

/// The content node of the value `id`, each child numbered by `child`.
///
/// # Specification
/// - requires: `child` numbers the supplied child roots.
/// - ensures: preserves the arena node’s former and non-child payload, resolves
///   constants by program identity, and invokes `child` in former order with
///   each child’s sort. An absent arena entry is Unresolved at the requested
///   sort.
/// - panics: only if `child` panics.
///
/// # Adequacy
/// - hypothesis: L3 — hand-built multi-child body formers, generated typed
///   source revisions and absent roots in each of the four arena sorts. Exact
///   leaf paths, replayed target snapshots and sort-specific unresolved results
///   distinguish swapped child sorts, metadata loss and conflated missing
///   entries; the predicate does not replay the callback.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::absent_arena_roots_keep_their_sorts`
#[spec(
    ensures: |ret| {
    program
        .arena()
        .value(id)
        .map_or(
            matches!(ret, ContentNode::Unresolved(Sort::Value)),
            |node| match *node {
                Value::Constructor {tag,ref fields,..} => matches!(ret,ContentNode::Constructor {tag:found,fields:ref other,..} if tag == found && fields.len() == other.len()),
                Value::Record(ref fields) => matches!(ret,ContentNode::Record(ref other) if fields.keys().eq(other.keys())),
                Value::Reify(_) => matches!(ret, ContentNode::Reify(_)),
                Value::Primitive { primitive, .. } => ret == ContentNode::PrimitiveValue(primitive),
                Value::PathRefl(_) => matches!(ret, ContentNode::PathRefl(_)),
                Value::Here(_) => matches!(ret, ContentNode::Here(_)),
                Value::Returned(_) => matches!(ret, ContentNode::Returned(_)),
                Value::Nested(_) => matches!(ret, ContentNode::Nested(_)),
                Value::Run(_) => matches!(ret, ContentNode::Run(_)),
                Value::PathProduct(..) => matches!(ret, ContentNode::PathProduct(..)),
                Value::Funext(..) => matches!(ret, ContentNode::Funext(..)),
                Value::Equiv(..) => matches!(ret, ContentNode::Equiv(..)),
                Value::SessionRelated { relation, .. } => {
                    matches!(ret, ContentNode::SessionRelated { relation: found, .. } if found == relation)
                }
                Value::Stay(_) => matches!(ret, ContentNode::Stay(_)),
                Value::Then(..) => matches!(ret, ContentNode::Then(..)),
                Value::FlowProduct(..) => matches!(ret, ContentNode::FlowProduct(..)),
                Value::Forward(_) => matches!(ret, ContentNode::Forward(_)),
                Value::FunctionFlow(..) => matches!(ret, ContentNode::FunctionFlow(..)),
                Value::Recorded(ref moves) => {
                    matches!(ret, ContentNode::Recorded(ref found) if found.len() == moves.len()
                        && found.iter().zip(moves.iter()).all(|(left, right)| left.carrying(()) == right.carrying(())))
                }
                Value::Ua { stratum, ref sides, .. } => {
                    matches!(
                        ret, ContentNode::Ua { stratum: found, sides: ref other, .. } if found
                        == stratum && other == sides
                    )
                }
                Value::PathEquiv { ref evidence, .. } => {
                    matches!(
                        ret, ContentNode::PathEquiv { evidence : ref found, .. } if found
                        == evidence
                    )
                }
                Value::Variable { zone, index } => {
                    matches!(
                        ret, ContentNode::Variable { zone : found_zone, index :
                        found_index } if found_zone == zone && found_index == index
                    )
                }
                Value::Constant(position) => {
                    matches!(
                        ret, ContentNode::Constant(ref found) if program.items().iter()
                        .position(| item | item.declaration().constant() == position)
                        .and_then(| ordinal | program.references().get(ordinal))
                        .map_or(matches!(found, Reference::Unoccupied), | expected |
                        found == expected)
                    )
                }
                Value::Tuple(ref components) => {
                    matches!(ret, ContentNode::Tuple(ref found) if found.len() == components.len())
                }
                Value::ListNil => matches!(ret, ContentNode::ListNil),
                Value::ListCons(..) => matches!(ret, ContentNode::ListCons(..)),
                Value::Literal(ref expected) => {
                    matches!(ret, ContentNode::Literal(ref found) if found == expected)
                }
                Value::Injection(side, _) => {
                    matches!(ret, ContentNode::Injection(found, _) if found == side)
                }
                Value::Lift { ref target, .. } => {
                    matches!(
                        ret, ContentNode::ValueLift { target : ref found, .. } if found
                        == target
                    )
                }
                Value::Thunk(..) => matches!(ret, ContentNode::Thunk(..)),
                Value::Quote(..) => matches!(ret, ContentNode::Quote(..)),
                Value::QuoteComputation(..) => {
                    matches!(ret, ContentNode::QuoteComputation(..))
                }
                Value::StaticLambda(..) => matches!(ret, ContentNode::StaticLambda(..)),
                Value::StaticApplication(..) => {
                    matches!(ret, ContentNode::StaticApplication(..))
                }
                Value::Hole(hole) => ret == ContentNode::Hole(hole),
                Value::Mark { mark, .. } => {
                    matches!(ret, ContentNode::ValueMark { mark: found, .. } if found == mark)
                }
            },
        )
},
)]
fn read_value<Child>(
    program: &Program,
    id: ValueId,
    child: &mut Child,
) -> ContentNode
where
    Child: FnMut(Root) -> NodeIndex,
{
    match program.arena().value(id) {
        Some(&Value::Constructor {
            datatype,
            tag,
            ref fields,
        }) => ContentNode::Constructor {
            datatype: child(Root::ValueType(datatype)),
            tag,
            fields: fields
                .iter()
                .map(|&field| child(Root::Value(field)))
                .collect(),
        },
        Some(&Value::Record(ref fields)) => ContentNode::Record(
            fields
                .iter()
                .map(|(label, &field)| (label.clone(), child(Root::Value(field))))
                .collect(),
        ),
        Some(&Value::Reify(ref frames)) => ContentNode::Reify(
            frames
                .iter()
                .map(|frame| match *frame {
                    gandr_core_term::control::StackFrame::Apply(value) => {
                        gandr_core_term::control::StackFrame::Apply(child(Root::Value(value)))
                    },
                    gandr_core_term::control::StackFrame::Bind(body) => {
                        gandr_core_term::control::StackFrame::Bind(child(Root::Computation(body)))
                    },
                    gandr_core_term::control::StackFrame::Project(side) => {
                        gandr_core_term::control::StackFrame::Project(side)
                    },
                })
                .collect(),
        ),
        Some(&Value::Primitive { primitive, .. }) => ContentNode::PrimitiveValue(primitive),
        Some(&Value::PathRefl(code)) => ContentNode::PathRefl(child(Root::Value(code))),
        Some(&Value::Here(point)) => ContentNode::Here(child(Root::Value(point))),
        Some(&Value::Returned(computation)) => {
            ContentNode::Returned(child(Root::Computation(computation)))
        },
        Some(&Value::Nested(computation)) => {
            ContentNode::Nested(child(Root::Computation(computation)))
        },
        Some(&Value::Run(computation)) => ContentNode::Run(child(Root::Computation(computation))),
        Some(&Value::PathProduct(first, second)) => {
            let first = child(Root::Value(first));
            ContentNode::PathProduct(first, child(Root::Value(second)))
        },
        Some(&Value::Funext(left, right)) => {
            let left = child(Root::Value(left));
            ContentNode::Funext(left, child(Root::Value(right)))
        },
        Some(&Value::Equiv(forward, backward)) => {
            let forward = child(Root::Value(forward));
            ContentNode::Equiv(forward, child(Root::Value(backward)))
        },
        Some(&Value::SessionRelated {
            relation,
            source,
            target,
        }) => {
            let source = child(Root::Value(source));
            ContentNode::SessionRelated {
                relation,
                source,
                target: child(Root::Value(target)),
            }
        },
        Some(&Value::Stay(point)) => ContentNode::Stay(child(Root::Value(point))),
        Some(&Value::Then(first, second)) => {
            let first = child(Root::Value(first));
            ContentNode::Then(first, child(Root::Value(second)))
        },
        Some(&Value::FlowProduct(first, second)) => {
            let first = child(Root::Value(first));
            ContentNode::FlowProduct(first, child(Root::Value(second)))
        },
        Some(&Value::Forward(translator)) => ContentNode::Forward(child(Root::Value(translator))),
        Some(&Value::FunctionFlow(domain, codomain)) => {
            let domain = child(Root::Value(domain));
            ContentNode::FunctionFlow(domain, child(Root::Value(codomain)))
        },
        Some(&Value::Recorded(ref moves)) => ContentNode::Recorded(
            moves
                .iter()
                .map(|step| {
                    step.try_map(|payload| {
                        Ok::<_, core::convert::Infallible>(child(Root::Value(payload)))
                    })
                    .unwrap_or_else(|never| match never {})
                })
                .collect(),
        ),
        Some(&Value::Ua {
            stratum,
            ref sides,
            forward,
            backward,
        }) => {
            let forward = child(Root::Value(forward));
            ContentNode::Ua {
                stratum,
                sides: alloc::sync::Arc::clone(sides),
                forward,
                backward: child(Root::Value(backward)),
            }
        },
        Some(&Value::PathEquiv {
            path_type,
            forward,
            backward,
            ref evidence,
        }) => ContentNode::PathEquiv {
            path_type: child(Root::ValueType(path_type)),
            forward: child(Root::Value(forward)),
            backward: child(Root::Value(backward)),
            evidence: alloc::sync::Arc::clone(evidence),
        },
        Some(&Value::Variable { zone, index }) => ContentNode::Variable { zone, index },
        Some(&Value::Constant(position)) => ContentNode::Constant(program.resolve(position)),
        Some(&Value::ListNil) => ContentNode::ListNil,
        Some(&Value::ListCons(head, tail)) => {
            ContentNode::ListCons(child(Root::Value(head)), child(Root::Value(tail)))
        },
        Some(&Value::Literal(ref literal)) => ContentNode::Literal(literal.clone()),
        Some(&Value::Tuple(ref components)) => ContentNode::Tuple(
            components
                .iter()
                .map(|&component| child(Root::Value(component)))
                .collect(),
        ),
        Some(&Value::Injection(side, body)) => {
            ContentNode::Injection(side, child(Root::Value(body)))
        },
        Some(&Value::Thunk(body)) => ContentNode::Thunk(child(Root::Computation(body))),
        Some(&Value::Lift { ref target, body }) => ContentNode::ValueLift {
            target: target.clone(),
            body: child(Root::Value(body)),
        },
        Some(&Value::Quote(quoted)) => ContentNode::Quote(child(Root::ValueType(quoted))),
        Some(&Value::QuoteComputation(quoted)) => {
            ContentNode::QuoteComputation(child(Root::CompType(quoted)))
        },
        Some(&Value::StaticLambda(body)) => ContentNode::StaticLambda(child(Root::Value(body))),
        Some(&Value::StaticApplication(head, argument)) => {
            let head = child(Root::Value(head));
            ContentNode::StaticApplication(head, child(Root::Value(argument)))
        },
        Some(&Value::Hole(hole)) => ContentNode::Hole(hole),
        Some(&Value::Mark { mark, body }) => ContentNode::ValueMark {
            mark,
            body: child(Root::Value(body)),
        },
        None => ContentNode::Unresolved(Sort::Value),
    }
}

/// The content node of the computation `id`, each child numbered by `child`.
///
/// # Specification
/// - requires: `child` numbers the supplied child roots.
/// - ensures: preserves the arena node’s former and non-child payload, resolves
///   constants by program identity, and invokes `child` in former order with
///   each child’s sort. An absent arena entry is Unresolved at the requested
///   sort, and so is a world form, as incremental content lists it.
/// - panics: only if `child` panics.
///
/// # Adequacy
/// - hypothesis: L3 — hand-built multi-child body formers, generated typed
///   source revisions and absent roots in each of the four arena sorts. Exact
///   leaf paths, replayed target snapshots and sort-specific unresolved results
///   distinguish swapped child sorts, metadata loss and conflated missing
///   entries; the predicate does not replay the callback.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::absent_arena_roots_keep_their_sorts`
#[spec(
    ensures: |ret| {
    program
        .arena()
        .computation(id)
        .map_or(
            matches!(ret, ContentNode::Unresolved(Sort::Computation)),
            |node| match *node {
                Computation::DataCase {ref branches,..} => matches!(ret,ContentNode::DataCase {branches:ref other,..} if branches.len() == other.len()),
                Computation::RecordProjection(_,ref label) => matches!(ret,ContentNode::RecordProjection(_,ref other) if label == other),
                Computation::TupleProjection(_,component) => matches!(ret,ContentNode::TupleProjection(_,other) if component == other),
                Computation::Perform { ref operation, ref signature, .. } => matches!(ret, ContentNode::Perform { operation: ref actual, signature: ref mapped, .. } if operation == actual && signature.name() == mapped.name()),
                Computation::Handle { ref signature, .. } => matches!(ret, ContentNode::Handle { signature: ref mapped, .. } if signature.name() == mapped.name()),
                Computation::Scope { ref signature, .. } => matches!(ret, ContentNode::Scope { signature: ref mapped, .. } if signature.name() == mapped.name()),
                Computation::Exercise { ref operation, ref signature, .. } => matches!(ret, ContentNode::Exercise { operation: ref actual, signature: ref mapped, .. } if operation == actual && signature.name() == mapped.name()),
                Computation::Resume(..) => matches!(ret, ContentNode::Resume(..)),
                Computation::Split { arity, motive: SplitMotive::Ambient, .. } => matches!(ret, ContentNode::Split(_, actual, _) if actual == arity),
                Computation::Split { arity, motive: SplitMotive::Scrutinee(_), .. } => matches!(ret, ContentNode::DependentSplit { arity: actual, .. } if actual == arity),
                Computation::Reset(_) => matches!(ret, ContentNode::Reset(_)),
                Computation::Shift(_) => matches!(ret, ContentNode::Shift(_)),
                Computation::With(..) => matches!(ret, ContentNode::With(..)),
                Computation::Ascribe { .. } => matches!(ret, ContentNode::Ascribe { .. }),
                Computation::Project(side, _) => matches!(ret, ContentNode::Project(actual, _) if actual == side),
                Computation::Primitive { primitive, .. } => matches!(ret, ContentNode::Primitive(actual, _) if actual == primitive),
                Computation::Transport(..) => matches!(ret, ContentNode::Transport(..)),
                Computation::PathTransport { .. } => matches!(ret, ContentNode::ElementTransport { .. }),
                Computation::TelescopeTransport { .. } => matches!(ret, ContentNode::TelescopeTransport { .. }),
                Computation::Ride { .. } => matches!(ret, ContentNode::Ride { .. }),
                Computation::Lambda(..) => matches!(ret, ContentNode::Lambda(..)),
                Computation::Application(..) => {
                    matches!(ret, ContentNode::Application(..))
                }
                Computation::Return(..) => matches!(ret, ContentNode::Return(..)),
                Computation::Bind(..) => matches!(ret, ContentNode::Bind(..)),
                Computation::Force(..) => matches!(ret, ContentNode::Force(..)),
                Computation::Case { .. } => matches!(ret, ContentNode::Case { .. }),
                Computation::Hole(hole) => ret == ContentNode::ComputationHole(hole),
                Computation::Mark { mark, .. } => {
                    matches!(ret, ContentNode::ComputationMark { mark: found, .. } if found == mark)
                }
                Computation::Fixpoint { evidence, .. } => {
                    matches!(ret, ContentNode::Fixpoint { evidence: found, .. } if found == evidence)
                }
                Computation::ListFold { .. } => matches!(ret, ContentNode::ListFold { .. }),
                Computation::Session(ref action) => matches!(ret, ContentNode::Session(ref found) if found.shape() == action.shape()),
                Computation::Memory(ref form) => matches!(ret, ContentNode::Memory(ref found) if found.shape() == form.shape()),
                Computation::World(_) => ret == ContentNode::Unresolved(Sort::Computation),
            },
        )
},
)]
fn read_computation<Child>(
    program: &Program,
    id: ComputationId,
    child: &mut Child,
) -> ContentNode
where
    Child: FnMut(Root) -> NodeIndex,
{
    match program.arena().computation(id) {
        Some(&Computation::DataCase {
            scrutinee,
            motive,
            ref branches,
        }) => ContentNode::DataCase {
            scrutinee: child(Root::Value(scrutinee)),
            motive: child(Root::CompType(motive)),
            branches: branches
                .iter()
                .map(|&branch| child(Root::Computation(branch)))
                .collect(),
        },
        Some(&Computation::RecordProjection(record, ref label)) => {
            ContentNode::RecordProjection(child(Root::Value(record)), label.clone())
        },
        Some(&Computation::TupleProjection(tuple, component)) => {
            ContentNode::TupleProjection(child(Root::Value(tuple)), component)
        },
        Some(&Computation::Ride {
            motive,
            flow,
            value,
        }) => {
            let motive = child(Root::ValueType(motive));
            let flow = child(Root::Value(flow));
            ContentNode::Ride {
                motive,
                flow,
                value: child(Root::Value(value)),
            }
        },
        Some(&Computation::Perform {
            ref signature,
            ref operation,
            payload,
        }) => {
            let payload = child(Root::Value(payload));
            let signature = signature
                .try_relocate(|ty| Ok::<_, core::convert::Infallible>(child(Root::ValueType(ty))))
                .unwrap_or_else(|never| match never {});
            ContentNode::Perform {
                signature,
                operation: operation.clone(),
                payload,
            }
        },
        Some(
            computation @ &(Computation::Handle {
                ref signature,
                subject,
                on_return,
                ref clauses,
            }
            | Computation::Scope {
                ref signature,
                subject,
                on_return,
                ref clauses,
            }),
        ) => {
            let subject = child(Root::Computation(subject));
            let on_return = child(Root::Computation(on_return));
            let signature = signature
                .try_relocate(|ty| Ok::<_, core::convert::Infallible>(child(Root::ValueType(ty))))
                .unwrap_or_else(|never| match never {});
            let clauses = clauses
                .iter()
                .map(|clause| gandr_core_term::control::EffectClause {
                    operation: clause.operation.clone(),
                    body: child(Root::Computation(clause.body)),
                })
                .collect();
            if matches!(*computation, Computation::Scope { .. }) {
                ContentNode::Scope {
                    signature,
                    subject,
                    on_return,
                    clauses,
                }
            }
            else {
                ContentNode::Handle {
                    signature,
                    subject,
                    on_return,
                    clauses,
                }
            }
        },
        Some(&Computation::Exercise {
            capability,
            ref signature,
            ref operation,
            payload,
        }) => {
            let capability = child(Root::Value(capability));
            let payload = child(Root::Value(payload));
            let signature = signature
                .try_relocate(|ty| Ok::<_, core::convert::Infallible>(child(Root::ValueType(ty))))
                .unwrap_or_else(|never| match never {});
            ContentNode::Exercise {
                capability,
                signature,
                operation: operation.clone(),
                payload,
            }
        },
        Some(&Computation::Resume(stack, body)) => {
            ContentNode::Resume(child(Root::Value(stack)), child(Root::Computation(body)))
        },
        Some(&Computation::Split {
            scrutinee,
            arity,
            motive: SplitMotive::Ambient,
            body,
        }) => ContentNode::Split(
            child(Root::Value(scrutinee)),
            arity,
            child(Root::Computation(body)),
        ),
        Some(&Computation::Split {
            scrutinee,
            arity,
            motive: SplitMotive::Scrutinee(motive),
            body,
        }) => {
            let scrutinee = child(Root::Value(scrutinee));
            let motive = child(Root::CompType(motive));
            ContentNode::DependentSplit {
                scrutinee,
                arity,
                motive,
                body: child(Root::Computation(body)),
            }
        },
        Some(&Computation::Reset(body)) => ContentNode::Reset(child(Root::Computation(body))),
        Some(&Computation::Shift(body)) => ContentNode::Shift(child(Root::Computation(body))),
        Some(&Computation::With(first, second)) => ContentNode::With(
            child(Root::Computation(first)),
            child(Root::Computation(second)),
        ),
        Some(&Computation::Ascribe { body, ty }) => {
            let body = child(Root::Computation(body));
            ContentNode::Ascribe {
                body,
                ty: child(Root::CompType(ty)),
            }
        },
        Some(&Computation::Project(side, body)) => {
            ContentNode::Project(side, child(Root::Computation(body)))
        },
        Some(&Computation::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        }) => ContentNode::ListFold {
            element: child(Root::ValueType(element)),
            result: child(Root::ValueType(result)),
            list: child(Root::Value(list)),
            on_nil: child(Root::Computation(on_nil)),
            on_cons: child(Root::Computation(on_cons)),
        },
        Some(&Computation::Primitive {
            primitive,
            arguments,
        }) => {
            use gandr_core_term::primitive::Arguments;
            let arguments = match arguments {
                Arguments::Unary(argument) => Arguments::Unary(child(Root::Value(argument))),
                Arguments::Binary([first, second]) => {
                    Arguments::Binary([child(Root::Value(first)), child(Root::Value(second))])
                },
            };
            ContentNode::Primitive(primitive, arguments)
        },
        Some(&Computation::Transport(path, value)) => {
            let path = child(Root::Value(path));
            ContentNode::Transport(path, child(Root::Value(value)))
        },
        Some(&Computation::PathTransport {
            motive,
            path,
            value,
        }) => {
            let motive = child(Root::ValueType(motive));
            let path = child(Root::Value(path));
            ContentNode::ElementTransport {
                motive,
                path,
                value: child(Root::Value(value)),
            }
        },
        Some(&Computation::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value,
        }) => {
            let motive = child(Root::CompType(motive));
            let path = child(Root::Value(path));
            let start = child(Root::Value(start));
            let over = child(Root::Value(over));
            ContentNode::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value: child(Root::Value(value)),
            }
        },
        Some(&Computation::Lambda(body)) => ContentNode::Lambda(child(Root::Computation(body))),
        Some(&Computation::Application(head, argument)) => {
            let head = child(Root::Computation(head));
            ContentNode::Application(head, child(Root::Value(argument)))
        },
        Some(&Computation::Return(value)) => ContentNode::Return(child(Root::Value(value))),
        Some(&Computation::Bind(bound, rest)) => {
            let bound = child(Root::Computation(bound));
            ContentNode::Bind(bound, child(Root::Computation(rest)))
        },
        Some(&Computation::Force(value)) => ContentNode::Force(child(Root::Value(value))),
        Some(&Computation::Case {
            scrutinee,
            ref branches,
        }) => {
            let scrutinee = child(Root::Value(scrutinee));
            ContentNode::Case {
                scrutinee,
                branches: branches
                    .iter()
                    .map(|&branch| child(Root::Computation(branch)))
                    .collect(),
            }
        },
        Some(&Computation::Hole(hole)) => ContentNode::ComputationHole(hole),
        Some(&Computation::Mark { mark, body }) => ContentNode::ComputationMark {
            mark,
            body: child(Root::Computation(body)),
        },
        Some(&Computation::Fixpoint { body, evidence }) => ContentNode::Fixpoint {
            body: child(Root::Computation(body)),
            evidence,
        },
        Some(&Computation::Session(ref action)) => ContentNode::Session(
            action
                .try_map(
                    gandr_core_term::session::ChildOrder::Forward,
                    child,
                    |child, value| Ok::<_, core::convert::Infallible>(child(Root::Value(value))),
                    |child, body| Ok(child(Root::Computation(body))),
                    |child, ty| Ok(child(Root::ValueType(ty))),
                )
                .unwrap_or_else(|never| match never {}),
        ),
        Some(&Computation::Memory(ref form)) => ContentNode::Memory(
            form.try_map(
                gandr_core_term::session::ChildOrder::Forward,
                child,
                |child, value| Ok::<_, core::convert::Infallible>(child(Root::Value(value))),
                |child, body| Ok(child(Root::Computation(body))),
            )
            .unwrap_or_else(|never| match never {}),
        ),
        // A located program is judged whole, never edited by node: its world
        // forms, as incremental content lists them, stand by their sort.
        Some(&Computation::World(_)) | None => ContentNode::Unresolved(Sort::Computation),
    }
}

/// The content node of the value type `id`, each child numbered by `child`.
///
/// # Specification
/// - requires: `child` numbers the supplied child roots.
/// - ensures: preserves the arena node’s former and non-child payload, resolves
///   constants by program identity, and invokes `child` in former order with
///   sort, and so is a staged type: a stage is one judgement's own and names
///   nothing a program's content could hold. A world type is Unresolved too, as
///   incremental content lists it.
/// - panics: only if `child` panics.
///
/// # Adequacy
/// - hypothesis: L3 — hand-built multi-child body formers, generated typed
///   source revisions and absent roots in each of the four arena sorts. Exact
///   leaf paths, replayed target snapshots and sort-specific unresolved results
///   distinguish swapped child sorts, metadata loss and conflated missing
///   entries; the predicate does not replay the callback.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::absent_arena_roots_keep_their_sorts`
#[spec(
    ensures: |ret| {
    program
        .arena()
        .value_type(id)
        .map_or(
            matches!(ret, ContentNode::Unresolved(Sort::ValueType)),
            |node| match *node {
                ValueType::Data {declaration,ref arguments} => matches!(ret,ContentNode::Data {declaration:ref found,arguments:ref other} if *found == program.resolve(declaration) && arguments.len() == other.len()),
                ValueType::Record(ref fields) => matches!(ret,ContentNode::RecordType(ref other) if fields.keys().eq(other.keys())),
                ValueType::Stack { .. } => matches!(ret, ContentNode::Stack { .. }),
                ValueType::Capability { grade, region, .. } => matches!(ret, ContentNode::Capability { grade: found_grade, region: found_region, .. } if found_grade == grade && found_region == region),
                ValueType::PathUniverse(..) => {
                    matches!(ret, ContentNode::PathUniverse(..))
                }
                ValueType::Path { .. } => matches!(ret, ContentNode::PathType { .. }),
                ValueType::Flow { .. } => matches!(ret, ContentNode::FlowType { .. }),
                ValueType::Run(_) => matches!(ret, ContentNode::RunType(_)),
                ValueType::Base(base) => {
                    matches!(ret, ContentNode::Base(found) if found == base)
                }
                ValueType::Product(ref parts) => matches!(ret, ContentNode::Product(ref found) if found.len() == parts.len()),
                ValueType::Sum(ref parts) => matches!(ret, ContentNode::Sum(ref found) if found.len() == parts.len()),
                ValueType::List(_) => matches!(ret, ContentNode::List(_)),
                ValueType::Thunk(_) => matches!(ret, ContentNode::ThunkType(_)),
                ValueType::Universe { sort, ref level } => {
                    matches!(
                        ret, ContentNode::Universe { sort : found_sort, level : ref
                        found_level } if found_sort == sort && found_level == level
                    )
                }
                ValueType::Lift { ref target, .. } => {
                    matches!(
                        ret, ContentNode::TypeLift { target : ref found, .. } if found ==
                        target
                    )
                }
                ValueType::Element { ref target, .. } => {
                    matches!(
                        ret, ContentNode::Element { target : ref found, .. } if found ==
                        target
                    )
                }
                ValueType::Abstract(position) => {
                    matches!(
                        ret, ContentNode::Abstract(ref found) if program.items().iter()
                        .position(| item | item.declaration().constant() == position)
                        .and_then(| ordinal | program.references().get(ordinal))
                        .map_or(matches!(found, Reference::Unoccupied), | expected |
                        found == expected)
                    )
                }
                ValueType::StaticPi { .. } => matches!(ret, ContentNode::StaticPi { .. }),
                ValueType::Sigma { .. } => matches!(ret, ContentNode::Sigma { .. }),
                ValueType::Session(ref session) => matches!(ret, ContentNode::SessionType(ref found)
                    if found.protocol() == session.protocol() && found.state() == session.state()
                        && found.payloads().len() == session.payloads().len()),
                ValueType::Unknown => ret == ContentNode::UnknownType,
                ValueType::Staged { .. } | ValueType::World(_) => ret == ContentNode::Unresolved(Sort::ValueType),
            },
        )
},
)]
fn read_value_type<Child>(
    program: &Program,
    id: ValueTypeId,
    child: &mut Child,
) -> ContentNode
where
    Child: FnMut(Root) -> NodeIndex,
{
    match program.arena().value_type(id) {
        Some(&ValueType::Data {
            declaration,
            ref arguments,
        }) => ContentNode::Data {
            declaration: program.resolve(declaration),
            arguments: arguments
                .iter()
                .map(|&argument| child(Root::Value(argument)))
                .collect(),
        },
        Some(&ValueType::Record(ref fields)) => ContentNode::RecordType(
            fields
                .iter()
                .map(|(label, &field)| (label.clone(), child(Root::ValueType(field))))
                .collect(),
        ),
        Some(&ValueType::Stack { input, output }) => ContentNode::Stack {
            input: child(Root::CompType(input)),
            output: child(Root::CompType(output)),
        },
        Some(&ValueType::Capability {
            ref authority,
            grade,
            region,
        }) => ContentNode::Capability {
            authority: authority
                .try_relocate(|ty| Ok::<_, core::convert::Infallible>(child(Root::ValueType(ty))))
                .unwrap_or_else(|never| match never {}),
            grade,
            region,
        },
        Some(&ValueType::PathUniverse(source, target)) => {
            let source = child(Root::Value(source));
            ContentNode::PathUniverse(source, child(Root::Value(target)))
        },
        Some(&ValueType::Path {
            carrier,
            left,
            right,
        }) => {
            let carrier = child(Root::ValueType(carrier));
            let left = child(Root::Value(left));
            ContentNode::PathType {
                carrier,
                left,
                right: child(Root::Value(right)),
            }
        },
        Some(&ValueType::Flow {
            carrier,
            source,
            target,
        }) => {
            let carrier = child(Root::ValueType(carrier));
            let source = child(Root::Value(source));
            ContentNode::FlowType {
                carrier,
                source,
                target: child(Root::Value(target)),
            }
        },
        Some(&ValueType::Run(code)) => ContentNode::RunType(child(Root::Value(code))),
        Some(&ValueType::Base(base)) => ContentNode::Base(base),
        Some(&ValueType::Product(ref parts)) => ContentNode::Product(
            parts
                .iter()
                .map(|&part| child(Root::ValueType(part)))
                .collect(),
        ),
        Some(&ValueType::Sum(ref parts)) => ContentNode::Sum(
            parts
                .iter()
                .map(|&part| child(Root::ValueType(part)))
                .collect(),
        ),
        Some(&ValueType::List(element)) => ContentNode::List(child(Root::ValueType(element))),
        Some(&ValueType::Thunk(body)) => ContentNode::ThunkType(child(Root::CompType(body))),
        Some(&ValueType::Universe { sort, ref level }) => ContentNode::Universe {
            sort,
            level: level.clone(),
        },
        Some(&ValueType::Lift { inner, ref target }) => ContentNode::TypeLift {
            inner: child(Root::ValueType(inner)),
            target: target.clone(),
        },
        Some(&ValueType::Element { code, ref target }) => ContentNode::Element {
            code: child(Root::Value(code)),
            target: target.clone(),
        },
        Some(&ValueType::Abstract(position)) => ContentNode::Abstract(program.resolve(position)),
        Some(&ValueType::StaticPi { domain, codomain }) => {
            let domain = child(Root::ValueType(domain));
            ContentNode::StaticPi {
                domain,
                codomain: child(Root::ValueType(codomain)),
            }
        },
        Some(&ValueType::Sigma { first, second }) => {
            let first = child(Root::ValueType(first));
            ContentNode::Sigma {
                first,
                second: child(Root::ValueType(second)),
            }
        },
        Some(&ValueType::Session(ref session)) => ContentNode::SessionType(
            session
                .try_relocate(|ty| Ok::<_, core::convert::Infallible>(child(Root::ValueType(ty))))
                .unwrap_or_else(|never| match never {}),
        ),
        Some(&ValueType::Unknown) => ContentNode::UnknownType,
        Some(&(ValueType::Staged { .. } | ValueType::World(_))) | None => {
            ContentNode::Unresolved(Sort::ValueType)
        },
    }
}

/// The content node of the computation type `id`, each child numbered by
/// `child`.
///
/// # Specification
/// - requires: `child` numbers the supplied child roots.
/// - ensures: preserves the arena node’s former and non-child payload, resolves
///   constants by program identity, and invokes `child` in former order with
///   each child’s sort. An absent arena entry is Unresolved at the requested
///   sort.
/// - panics: only if `child` panics.
///
/// # Adequacy
/// - hypothesis: L3 — hand-built multi-child body formers, generated typed
///   source revisions and absent roots in each of the four arena sorts. Exact
///   leaf paths, replayed target snapshots and sort-specific unresolved results
///   distinguish swapped child sorts, metadata loss and conflated missing
///   entries; the predicate does not replay the callback.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::absent_arena_roots_keep_their_sorts`
#[spec(
    ensures: |ret| {
    program
        .arena()
        .comp_type(id)
        .map_or(
            matches!(ret, ContentNode::Unresolved(Sort::CompType)),
            |node| match *node {
                CompType::With(..) => matches!(ret, ContentNode::WithType(..)),
                CompType::Returner { .. } => matches!(ret, ContentNode::Returner { .. }),
                CompType::Arrow { .. } => matches!(ret, ContentNode::Arrow { .. }),
                CompType::Pi { .. } => matches!(ret, ContentNode::Pi { .. }),
                CompType::Element { ref target, .. } => {
                    matches!(
                        ret, ContentNode::ComputationElement { target : ref found, .. }
                        if found == target
                    )
                }
                CompType::Unknown => ret == ContentNode::UnknownComputationType,
            },
        )
},
)]
fn read_comp_type<Child>(
    program: &Program,
    id: CompTypeId,
    child: &mut Child,
) -> ContentNode
where
    Child: FnMut(Root) -> NodeIndex,
{
    match program.arena().comp_type(id) {
        Some(&CompType::With(first, second)) => {
            ContentNode::WithType(child(Root::CompType(first)), child(Root::CompType(second)))
        },
        Some(&CompType::Returner {
            result,
            ref effects,
        }) => {
            let result = child(Root::ValueType(result));
            let effects = effects
                .try_relocate(|ty| Ok::<_, core::convert::Infallible>(child(Root::ValueType(ty))))
                .unwrap_or_else(|never| match never {});
            ContentNode::Returner { result, effects }
        },
        Some(&CompType::Arrow { domain, codomain }) => {
            let domain = child(Root::ValueType(domain));
            ContentNode::Arrow {
                domain,
                codomain: child(Root::CompType(codomain)),
            }
        },
        Some(&CompType::Pi { domain, codomain }) => {
            let domain = child(Root::ValueType(domain));
            ContentNode::Pi {
                domain,
                codomain: child(Root::CompType(codomain)),
            }
        },
        Some(&CompType::Element { code, ref target }) => ContentNode::ComputationElement {
            code: child(Root::Value(code)),
            target: target.clone(),
        },
        Some(&CompType::Unknown) => ContentNode::UnknownComputationType,
        None => ContentNode::Unresolved(Sort::CompType),
    }
}

/// Widen every node's span of `tree` to its extent: the hull of its own
/// origin and its children's extents.
///
/// # Specification
/// - requires: the tree is numbered breadth-first and the span table has one
///   entry per node.
/// - ensures: widens each recorded extent to the hull of itself and every
///   recorded descendant; an unknown parent inherits recorded descendants,
///   while a wholly unrecorded subtree remains unrecorded.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an unrecorded branching root with disjoint recorded
///   children and an unknown leaf, plus source-localized nested terms. Exact
///   union endpoints and retained absence distinguish overwriting a span,
///   dropping descendants or inventing source provenance.
/// - witness: `edit::tests::hulls_cover_descendants_without_inventing_origins`
/// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
/// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the body visits every node and each of its children once; the check visits each once and counts the recorded spans twice"
    )
)]
#[spec(
    requires: spans.len() == tree.nodes.len()
    && (tree.nodes.is_empty()
        || {
            let mut expected = 1_usize;
            tree
                .nodes
                .iter()
                .all(|node| {
                    children(node)
                        .all(|child| {
                            let correct = usize::from(child) == expected;
                            expected = expected.saturating_add(1_usize);
                            correct
                        })
                }) && expected == tree.nodes.len()
        }),
    captures: recorded = spans
    .iter()
    .filter(|span| matches!(span, Maybe::Present(_)))
    .count(),
    ensures: |_| {
    spans.iter().filter(|span| matches!(span, Maybe::Present(_))).count() >= recorded
        && tree
            .nodes
            .iter()
            .enumerate()
            .all(|(index, node)| {
                children(node)
                    .all(|child| match spans.get(usize::from(child)) {
                        Some(&Maybe::Present(child_span)) => {
                            matches!(
                                spans.get(index), Some(& Maybe::Present(parent)) if parent
                                .start() <= child_span.start() && child_span.end() <= parent
                                .end()
                            )
                        }
                        _ => true,
                    })
            })
},
)]
fn hull(
    tree: &Tree,
    spans: &mut [Maybe<ByteSpan, spanned::Absent>],
)
{
    // Breadth-first numbering puts every child after its parent, so one pass
    // from the last node back settles each child before its parent.
    for (index, node) in tree.nodes.iter().enumerate().rev() {
        let mut covered = match spans.get(index) {
            Some(&Maybe::Present(span)) => Some(span),
            Some(&Maybe::Absent(_)) | None => None,
        };
        for child in children(node) {
            if let Some(&Maybe::Present(span)) = spans.get(usize::from(child)) {
                covered = Some(covered.map_or(span, |held| held.join(span)));
            }
        }
        if let (Some(span), Some(slot)) = (covered, spans.get_mut(index)) {
            *slot = Maybe::Present(span);
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::fmt::Write as _;

    use anodized::spec;
    use gandr_core_incremental::ItemOrdinal;
    use gandr_surface_dispatcher::Lowered;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::lower_source;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::ChildSlot;
    use super::CorePath;
    use super::ItemTree;
    use super::Snapshot;
    use super::SourceEdit;
    use super::children;
    use super::located;
    use crate::item_source::program;

    /// The snapshot of `text`, which the lowering must read as a module.
    ///
    /// # Specification
    /// - requires: the fixture text parses and lowers to an ordered module.
    /// - ensures: returns its source-provenanced body and signature image.
    /// - panics: if the fixture grammar, lowering or module ordering is
    ///   invalid.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independently located nested literals, holes and
    ///   adjacent declarations; exact node paths and source slices distinguish
    ///   an incorrectly adapted fixture.
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
    #[spec(
        ensures: |ret| {
    ret.spans
        .iter()
        .flatten()
        .all(|span| match *span {
            Maybe::Present(span) => span.end() <= text.end(),
            Maybe::Absent(_) => true,
        })
},
    )]
    fn snapshot_of(text: SourceText<'_>) -> Snapshot
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        let lowering = lower_source(&grammar, text, &mut lowerings).expect("the revision lowers");
        let Lowered::Module { module, arena } = lowering.into_lowered()
        else {
            panic!("the lowering reads a module: {text:?}");
        };
        let program = program(&module, arena).expect("positions ascend");
        Snapshot::of(&program, module.origins())
    }

    /// The reference localizer: every body node of every item scanned, the
    /// enclosing one with the fewest bytes kept, then the shallowest, then
    /// the first in item and breadth-first order.
    ///
    /// # Specification
    /// - requires: the snapshot is a canonical source image.
    /// - ensures: chooses the enclosing span with least extent, then least
    ///   depth, then first item and breadth-first position; reports Outside
    ///   exactly when no body contains the range.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 over the spans and endpoints of five source shapes
    ///   against the independently implemented indexed descent. The two
    ///   algorithms share span containment, not candidate enumeration or
    ///   ranking.
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    #[spec(
        ensures: |ret| match ret {
    Maybe::Present(ref path) => {
        matches!(
            snapshot.span(path), Maybe::Present(span) if span.start() <= range.start() &&
            range.end() <= span.end()
        )
    }
    Maybe::Absent(located::Absent::Outside) => {
        snapshot
            .bodies
            .iter()
            .all(|&(span, _)| {
                !(span.start() <= range.start() && range.end() <= span.end())
            })
    }
},
    )]
    fn stab(
        snapshot: &Snapshot,
        range: ByteSpan,
    ) -> Maybe<CorePath, located::Absent>
    {
        let mut best: Option<(ByteSpan, usize, CorePath)> = None;
        for (ordinal, (item, spans)) in snapshot.items.iter().zip(&snapshot.spans).enumerate() {
            let &ItemTree {
                declaration:
                    super::DeclarationTree::Value {
                        body: Maybe::Present(ref tree),
                        ..
                    },
                ..
            } = item
            else {
                continue;
            };
            // Breadth-first numbering lists every parent before its children.
            let mut reached: Vec<Option<(usize, ChildSlot)>> = vec![None; tree.nodes.len()];
            let mut depth = vec![0_usize; tree.nodes.len()];
            for (index, node) in tree.nodes.iter().enumerate() {
                let below = depth
                    .get(index)
                    .copied()
                    .unwrap_or_default()
                    .saturating_add(1);
                for (slot, child) in children(node).enumerate() {
                    if let (Some(parent), Some(level)) = (
                        reached.get_mut(usize::from(child)),
                        depth.get_mut(usize::from(child)),
                    ) {
                        *parent = Some((index, ChildSlot(slot)));
                        *level = below;
                    }
                }
            }
            for (index, span) in spans.iter().enumerate() {
                let &Maybe::Present(span) = span
                else {
                    continue;
                };
                if !(span.start() <= range.start() && range.end() <= span.end()) {
                    continue;
                }
                let level = depth.get(index).copied().unwrap_or_default();
                if best.as_ref().is_some_and(|&(held, held_level, _)| {
                    (held.length(), held_level) <= (span.length(), level)
                }) {
                    continue;
                }
                let mut slots = Vec::new();
                let mut cursor = index;
                while let Some(&Some((parent, slot))) = reached.get(cursor) {
                    slots.push(slot);
                    cursor = parent;
                }
                slots.reverse();
                best = Some((span, level, CorePath {
                    item: ItemOrdinal::from(ordinal),
                    slots,
                }));
            }
        }
        match best {
            Some((_, _, path)) => Maybe::Present(path),
            None => Maybe::Absent(located::Absent::Outside),
        }
    }

    #[test]
    fn descent_agrees_with_the_linear_stab_oracle()
    {
        let sources = [
            "def deep = thunk { return thunk { return thunk { return 1 } } } ;\n",
            "def target(x: Integer) -> -F Integer {\n  return 1\n}\ndef shown : +U (-F Integer) ;\ndef shown = thunk { become (force target)(0) } ;\n",
            "def a = 1 ;\ndef b = 2 ;\ndef c = 3 ;\n",
            "def owed : Integer ;\ndef reads = owed ;\n",
            "def f(x: Integer) -> -F Integer { return x }\ndef twice = thunk { become (force f)(\"text\") } ;\n",
            // The tail return the lowering inserts spans the value it returns:
            // a tie the descent breaks by depth.
            "def g(x: Integer) -> -F Integer { x }\n",
        ];
        for source in sources {
            let snapshot = snapshot_of(SourceText::from(source));

            for spans in &snapshot.spans {
                for &span in spans {
                    let Maybe::Present(span) = span
                    else {
                        continue;
                    };
                    let start = ByteSpan::new(span.start(), span.start()).expect("a point");
                    let end = ByteSpan::new(span.end(), span.end()).expect("a point");
                    for probe in [span, start, end] {
                        assert_eq!(
                            snapshot.localize(probe),
                            stab(&snapshot, probe),
                            "{source:?}: the descent and the linear stab disagree at {probe:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn missing_paths_and_unrecorded_origins_stay_distinct()
    {
        use super::addressed;
        use super::spanned;
        let snapshot = snapshot_of(SourceText::from(
            r#"def owed : Integer ;
def body = 1 ;
"#,
        ));
        let missing_item = CorePath::new(ItemOrdinal::from(2_usize), Vec::new());
        let missing_body = CorePath::new(ItemOrdinal::from(0_usize), Vec::new());
        let missing_child =
            CorePath::new(ItemOrdinal::from(1_usize), vec![ChildSlot::from(0_usize)]);
        assert_eq!(
            snapshot.node(&missing_item),
            Maybe::Absent(addressed::Absent::NoItem)
        );
        assert_eq!(
            snapshot.node(&missing_body),
            Maybe::Absent(addressed::Absent::NoBody)
        );
        assert_eq!(
            snapshot.node(&missing_child),
            Maybe::Absent(addressed::Absent::NoChild)
        );
        for path in [&missing_item, &missing_body, &missing_child] {
            assert_eq!(
                snapshot.span(path),
                Maybe::Absent(spanned::Absent::Unaddressed)
            );
        }
        let body = CorePath::new(ItemOrdinal::from(1_usize), Vec::new());
        let mut unrecorded = snapshot.clone();
        for span in unrecorded.spans.iter_mut().flatten() {
            *span = Maybe::Absent(spanned::Absent::Unrecorded);
        }
        unrecorded.bodies.clear();
        assert_eq!(unrecorded.node(&body), snapshot.node(&body));
        assert_eq!(
            unrecorded.span(&body),
            Maybe::Absent(spanned::Absent::Unrecorded)
        );
        let range = ByteSpan::new(
            super::ByteOffset::from(0_usize),
            super::ByteOffset::from(0_usize),
        )
        .expect("a point");
        assert_eq!(
            unrecorded.localize(range),
            Maybe::Absent(located::Absent::Outside)
        );
        assert_eq!(
            children(&super::ContentNode::Tuple(Vec::new())).next(),
            None
        );
    }

    #[test]
    fn child_mapping_preserves_payloads_without_replaying_the_callback()
    {
        use gandr_kernel_term::Side;

        use super::ContentNode;
        use super::NodeIndex;
        let original = ContentNode::Case {
            scrutinee: NodeIndex::from(7_usize),
            branches: vec![NodeIndex::from(3_usize), NodeIndex::from(11_usize)],
        };
        let mut seen = Vec::new();
        let mapped = super::map_children(&original, &mut |index| {
            seen.push(index);
            NodeIndex::from(19_usize.saturating_add(seen.len()))
        });
        assert_eq!(seen, vec![
            NodeIndex::from(7_usize),
            NodeIndex::from(3_usize),
            NodeIndex::from(11_usize)
        ]);
        assert_eq!(mapped, ContentNode::Case {
            scrutinee: NodeIndex::from(20_usize),
            branches: vec![NodeIndex::from(21_usize), NodeIndex::from(22_usize)],
        });
        assert_eq!(children(&mapped).nth(3), None);
        let left = ContentNode::Injection(Side::Left.into(), NodeIndex::from(7_usize));
        let changed = super::map_children(&left, &mut |_| NodeIndex::from(8_usize));
        assert_eq!(
            changed,
            ContentNode::Injection(Side::Left.into(), NodeIndex::from(8_usize))
        );
        assert_eq!(super::agreement(&left, &changed), super::Agreement::Same);
        assert_ne!(
            super::agreement(
                &left,
                &ContentNode::Injection(Side::Right.into(), NodeIndex::from(7_usize))
            ),
            super::Agreement::Same
        );
        assert_eq!(
            super::map_children(&ContentNode::Tuple(Vec::new()), &mut |_| panic!(
                "a leaf has no child"
            )),
            ContentNode::Tuple(Vec::new())
        );
    }

    #[test]
    fn a_memory_form_agrees_on_its_kind_and_slot()
    {
        use gandr_core_term::memory::MemoryForm;
        use gandr_kernel_term::DeBruijnIndex;

        use super::Agreement;
        use super::ContentNode;
        use super::NodeIndex;
        let (first, second) = (NodeIndex::from(3_usize), NodeIndex::from(5_usize));
        let access = |held| {
            ContentNode::Memory(MemoryForm::Access {
                held,
                body: first,
                unwind: second,
            })
        };
        let hold = ContentNode::Memory(MemoryForm::Hold {
            value: first,
            body: second,
        });
        let slot = DeBruijnIndex::from(0_u32);
        assert_eq!(
            super::agreement(&access(slot), &access(slot)),
            Agreement::Same,
            "one access over one slot agrees"
        );
        assert_eq!(
            super::agreement(&access(slot), &hold),
            Agreement::Differs,
            "an access and a hold of one arity are two formers"
        );
        assert_eq!(
            super::agreement(&access(slot), &access(DeBruijnIndex::from(1_u32))),
            Agreement::Differs,
            "an access over another slot is another payload"
        );
    }

    #[test]
    fn every_node_family_agrees_exactly_on_its_payload()
    {
        use alloc::collections::BTreeMap;
        use alloc::sync::Arc;

        use gandr_core_incremental::ItemKey;
        use gandr_core_incremental::Occurrence;
        use gandr_core_incremental::Reference;
        use gandr_core_term::Component;
        use gandr_core_term::ConstructorTag;
        use gandr_core_term::FieldLabel;
        use gandr_core_term::control::EffectClause;
        use gandr_core_term::control::StackFrame;
        use gandr_core_term::effect::EffectName;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        use gandr_core_term::effect::capability::CapabilityGrade;
        use gandr_core_term::effect::capability::Region;
        use gandr_core_term::effect::capability::RegionDepth;
        use gandr_kernel_strata::Level;
        use gandr_kernel_term::Side;

        use super::Agreement;
        use super::Agreement::Differs;
        use super::Agreement::Same;
        use super::ContentNode;
        use super::NodeIndex;

        let node = |index: usize| NodeIndex::from(index);
        let interface = |name: &str, operations: &[&str]| {
            EffectSig::new(
                EffectName::from(name),
                operations.iter().map(|&operation| EffectOp {
                    name: OperationName::from(operation),
                    payload: node(1_usize),
                    reply: node(2_usize),
                }),
            )
            .expect("distinct operations")
        };
        let state = || interface("State", &["get", "put"]);
        let perform = |signature, operation: &str, payload| ContentNode::Perform {
            signature,
            operation: OperationName::from(operation),
            payload: node(payload),
        };
        let exercise = |signature, operation: &str, payload| ContentNode::Exercise {
            capability: node(5_usize),
            signature,
            operation: OperationName::from(operation),
            payload: node(payload),
        };
        let scope = |signature, operation: &str, body| ContentNode::Scope {
            signature,
            subject: node(3_usize),
            on_return: node(4_usize),
            clauses: Arc::from([EffectClause {
                operation: OperationName::from(operation),
                body: node(body),
            }]),
        };
        let capability =
            |signatures: Vec<EffectSig<NodeIndex>>, grade, region| ContentNode::Capability {
                authority: EffectRow::from_signatures(signatures).expect("distinct interfaces"),
                grade,
                region,
            };
        let held = Region::Held;
        let durable = CapabilityGrade::Durable;
        let item = |key: &str| Reference::Item {
            key: ItemKey::from(key),
            occurrence: Occurrence::from(0_usize),
        };
        let data = |key: &str, argument| ContentNode::Data {
            declaration: item(key),
            arguments: vec![node(argument)],
        };
        let constructor = |tag: usize, field| ContentNode::Constructor {
            datatype: node(1_usize),
            tag: ConstructorTag::from(tag),
            fields: vec![node(field)],
        };
        let label = |text: &str| FieldLabel::from(String::from(text));
        let record =
            |key: &str, field| ContentNode::Record(BTreeMap::from([(label(key), node(field))]));
        let reify =
            |frames: &[StackFrame<NodeIndex, NodeIndex>]| ContentNode::Reify(Arc::from(frames));
        let zero = Level::zero();
        let one = zero.succ().expect("level one");
        let lift = |target: &Level, body| ContentNode::ValueLift {
            target: target.clone(),
            body: node(body),
        };
        let element = |target: &Level, code| ContentNode::Element {
            target: target.clone(),
            code: node(code),
        };
        let cases: [(&str, ContentNode, ContentNode, Agreement); 28] = [
            (
                "a perform over other children",
                perform(state(), "get", 3),
                perform(state(), "get", 4),
                Same,
            ),
            (
                "a perform of another operation",
                perform(state(), "get", 3),
                perform(state(), "put", 3),
                Differs,
            ),
            (
                "a perform of another interface",
                perform(state(), "get", 3),
                perform(interface("Store", &["get", "put"]), "get", 3),
                Differs,
            ),
            (
                "a perform naming other operations",
                perform(state(), "get", 3),
                perform(interface("State", &["get", "set"]), "get", 3),
                Differs,
            ),
            (
                "an exercise over other children",
                exercise(state(), "get", 3),
                exercise(state(), "get", 4),
                Same,
            ),
            (
                "an exercise of another operation",
                exercise(state(), "get", 3),
                exercise(state(), "put", 3),
                Differs,
            ),
            (
                "an exercise of another interface",
                exercise(state(), "get", 3),
                exercise(interface("Store", &["get", "put"]), "get", 3),
                Differs,
            ),
            (
                "an exercise naming other operations",
                exercise(state(), "get", 3),
                exercise(interface("State", &["get", "set"]), "get", 3),
                Differs,
            ),
            (
                "a scope over other children",
                scope(state(), "get", 6),
                scope(state(), "get", 7),
                Same,
            ),
            (
                "a scope handling another operation",
                scope(state(), "get", 6),
                scope(state(), "put", 6),
                Differs,
            ),
            (
                "a scope of another interface",
                scope(state(), "get", 6),
                scope(interface("Store", &["get", "put"]), "get", 6),
                Differs,
            ),
            (
                "a scope naming other operations",
                scope(state(), "get", 6),
                scope(interface("State", &["get", "set"]), "get", 6),
                Differs,
            ),
            (
                "one capability",
                capability(vec![state()], durable, held),
                capability(vec![state()], durable, held),
                Same,
            ),
            (
                "a capability of another grade",
                capability(vec![state()], durable, held),
                capability(vec![state()], CapabilityGrade::Consumable, held),
                Differs,
            ),
            (
                "a capability of another region",
                capability(vec![state()], durable, held),
                capability(
                    vec![state()],
                    durable,
                    Region::Scoped(RegionDepth::from(0_u32)),
                ),
                Differs,
            ),
            (
                "a capability of another interface",
                capability(vec![state()], durable, held),
                capability(vec![interface("Store", &["get", "put"])], durable, held),
                Differs,
            ),
            (
                "a capability of fewer operations",
                capability(vec![state()], durable, held),
                capability(vec![interface("State", &["get"])], durable, held),
                Differs,
            ),
            (
                "a capability naming other operations",
                capability(vec![state()], durable, held),
                capability(vec![interface("State", &["get", "set"])], durable, held),
                Differs,
            ),
            (
                "a family over another argument",
                data("List", 1),
                data("List", 2),
                Same,
            ),
            ("another family", data("List", 1), data("Tree", 1), Differs),
            (
                "a constructor over another field",
                constructor(0, 1),
                constructor(0, 2),
                Same,
            ),
            (
                "another constructor",
                constructor(0, 1),
                constructor(1, 1),
                Differs,
            ),
            (
                "a record of another label",
                record("x", 1),
                record("y", 1),
                Differs,
            ),
            (
                "a record projection of another label",
                ContentNode::RecordProjection(node(1_usize), label("x")),
                ContentNode::RecordProjection(node(1_usize), label("y")),
                Differs,
            ),
            (
                "a tuple projection of another component",
                ContentNode::TupleProjection(node(1_usize), Component::from(0_usize)),
                ContentNode::TupleProjection(node(1_usize), Component::from(1_usize)),
                Differs,
            ),
            (
                "a lift over another body",
                lift(&zero, 1),
                lift(&zero, 2),
                Same,
            ),
            (
                "a lift to another level",
                lift(&zero, 1),
                lift(&one, 1),
                Differs,
            ),
            (
                "an element at another level",
                element(&zero, 1),
                element(&one, 1),
                Differs,
            ),
        ];
        for (what, old, new, expected) in cases {
            assert_eq!(super::agreement(&old, &new), expected, "{what}");
        }
        let frames = [
            StackFrame::Apply(node(1_usize)),
            StackFrame::Bind(node(2_usize)),
        ];
        let renumbered = [
            StackFrame::Apply(node(3_usize)),
            StackFrame::Bind(node(4_usize)),
        ];
        for (what, old, new, expected) in [
            (
                "a stack over other frames' children",
                reify(&frames),
                reify(&renumbered),
                Same,
            ),
            (
                "a stack projecting one side",
                reify(&[StackFrame::Project(Side::Left)]),
                reify(&[StackFrame::Project(Side::Left)]),
                Same,
            ),
            (
                "a stack projecting the other side",
                reify(&[StackFrame::Project(Side::Left)]),
                reify(&[StackFrame::Project(Side::Right)]),
                Differs,
            ),
            (
                "a tuple over other children",
                ContentNode::Tuple(vec![node(1_usize), node(2_usize)]),
                ContentNode::Tuple(vec![node(3_usize), node(4_usize)]),
                Same,
            ),
        ] {
            assert_eq!(super::agreement(&old, &new), expected, "{what}");
        }
    }

    /// A data declaration whose constructors change is deleted and inserted
    /// afresh, and an unchanged one is kept: the script is empty.
    #[test]
    fn a_changed_nominal_declaration_is_replaced_and_an_unchanged_one_kept()
    {
        let two = snapshot_of(SourceText::from(
            "data Color : Type { Red : Color; Green : Color; }\ndef a = 1 ;\n",
        ));
        let three = snapshot_of(SourceText::from(
            "data Color : Type { Red : Color; Green : Color; Blue : Color; }\ndef a = 1 ;\n",
        ));
        assert!(
            super::diff(&two, &two).actions().is_empty(),
            "an unchanged data declaration is kept"
        );
        for (old, new, what) in [
            (&two, &three, "a data declaration gaining a constructor"),
            (&three, &two, "a data declaration losing a constructor"),
        ] {
            let script = super::diff(old, new);
            assert!(
                script.actions().iter().any(|action| matches!(
                    *action,
                    super::Action::DeleteItem { at } if at == ItemOrdinal::from(0_usize)
                )),
                "{what} is replaced: {:?}",
                script.actions()
            );
            assert_eq!(super::apply(old.items(), &script), new.items(), "{what}");
        }
    }

    #[test]
    fn a_value_declaration_reports_its_signature_and_an_unsigned_one_none()
    {
        use gandr_core_incremental::ItemKey;
        use gandr_core_incremental::Occurrence;
        use gandr_core_incremental::Program;
        use gandr_core_incremental::Reference;
        use gandr_core_term::CoreArena;
        use gandr_surface_lowering::OriginTable;

        let mut arena = CoreArena::new();
        let value = arena.value_unit();
        let program = Program::new(arena, Vec::new()).expect("empty declaration order");
        let (tree, _spans) =
            super::read(&program, &OriginTable::default(), super::Root::Value(value));
        let item = |signature| ItemTree {
            reference: Reference::Item {
                key: ItemKey::from("f"),
                occurrence: Occurrence::from(0_usize),
            },
            declaration: super::DeclarationTree::Value {
                signature,
                body: Maybe::Present(tree.clone()),
            },
        };
        assert_eq!(item(Maybe::Present(tree.clone())).signature(), Some(&tree));
        assert_eq!(
            item(Maybe::Absent(super::signature::Absent::Unsigned)).signature(),
            None
        );
    }

    #[test]
    fn effect_row_edits_preserve_names_and_rebuild_operation_types()
    {
        use gandr_core_incremental::ItemKey;
        use gandr_core_incremental::Occurrence;
        use gandr_core_incremental::Program;
        use gandr_core_incremental::Reference;
        use gandr_core_term::CoreArena;
        use gandr_core_term::effect::EffectName;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        use gandr_kernel_term::BaseType;
        use gandr_surface_lowering::OriginTable;
        let snapshot = |name: &str, reply| {
            let mut arena = CoreArena::new();
            let unit = arena.value_type_unit();
            let reply = arena.value_type_base(reply);
            let signature = EffectSig::new(EffectName::from(name), [EffectOp {
                name: OperationName::from("get"),
                payload: unit,
                reply,
            }])
            .expect("one operation");
            let returner =
                arena.comp_type_returner_with_effects(unit, EffectRow::singleton(signature));
            let code = arena.value_quote_computation(returner);
            let program = Program::new(arena, Vec::new()).expect("empty declaration order");
            let (body, spans) =
                super::read(&program, &OriginTable::default(), super::Root::Value(code));
            Snapshot {
                items: vec![ItemTree {
                    reference: Reference::Item {
                        key: ItemKey::from("row"),
                        occurrence: Occurrence::from(0_usize),
                    },
                    declaration: super::DeclarationTree::Value {
                        signature: Maybe::Absent(super::signature::Absent::Unsigned),
                        body: Maybe::Present(body),
                    },
                }],
                spans: vec![spans],
                bodies: Vec::new(),
            }
        };
        let old = snapshot("State", BaseType::Integer);
        for (new, slots) in [
            (snapshot("State", BaseType::String), vec![
                ChildSlot::from(0_usize),
                ChildSlot::from(2_usize),
            ]),
            (snapshot("Other", BaseType::Integer), vec![ChildSlot::from(
                0_usize,
            )]),
        ] {
            let expected = CorePath::new(ItemOrdinal::from(0_usize), slots);
            let script = super::diff(&old, &new);
            assert!(
                matches!(script.actions(), [super::Action::Replace { path, .. }] if path == &expected)
            );
            assert_eq!(super::apply(old.items(), &script), new.items());
        }
    }

    #[test]
    fn control_edits_preserve_names_scopes_and_frame_order()
    {
        use gandr_core_incremental::ItemKey;
        use gandr_core_incremental::Occurrence;
        use gandr_core_incremental::Program;
        use gandr_core_incremental::Reference;
        use gandr_core_term::CoreArena;
        use gandr_core_term::Zone;
        use gandr_core_term::control::EffectClause;
        use gandr_core_term::control::StackFrame;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectSig;
        use gandr_kernel_term::BaseType;
        use gandr_kernel_term::Side;
        use gandr_surface_lowering::OriginTable;
        let snapshot =
            |interface: &str, operation: &str, reply, bound: u32, side, reverse: bool| {
                let mut arena = CoreArena::new();
                let unit = arena.value_unit();
                let variable = arena.value_variable(Zone::Intuitionistic, bound.into());
                let unit_type = arena.value_type_unit();
                let reply = arena.value_type_base(reply);
                let signature = EffectSig::new(interface.into(), [EffectOp {
                    name: operation.into(),
                    payload: unit_type,
                    reply,
                }])
                .expect("one operation");
                let returned = arena.computation_return(variable);
                let mut frames = [
                    StackFrame::Apply(unit),
                    StackFrame::Bind(returned),
                    StackFrame::Project(side),
                ];
                if reverse {
                    frames.reverse();
                }
                let stack = arena.value_reify(alloc::sync::Arc::from(frames));
                let performed =
                    arena.computation_perform(signature.clone(), operation.into(), stack);
                let resumed = arena.computation_resume(variable, performed);
                let shifted = arena.computation_shift(resumed);
                let reset = arena.computation_reset(shifted);
                let pair = arena.computation_with(reset, returned);
                let projected = arena.computation_project(side, pair);
                let handled = arena.computation_handle(
                    signature,
                    projected,
                    returned,
                    alloc::sync::Arc::from([EffectClause {
                        operation: operation.into(),
                        body: returned,
                    }]),
                );
                let value = arena.value_thunk(handled);
                let program = Program::new(arena, Vec::new()).expect("empty declaration order");
                let (body, spans) =
                    super::read(&program, &OriginTable::default(), super::Root::Value(value));
                Snapshot {
                    items: vec![ItemTree {
                        reference: Reference::Item {
                            key: ItemKey::from("control"),
                            occurrence: Occurrence::from(0_usize),
                        },
                        declaration: super::DeclarationTree::Value {
                            signature: Maybe::Absent(super::signature::Absent::Unsigned),
                            body: Maybe::Present(body),
                        },
                    }],
                    spans: vec![spans],
                    bodies: Vec::new(),
                }
            };
        let old = snapshot("E", "op", BaseType::Integer, 0, Side::Left, false);
        for new in [
            snapshot("Other", "op", BaseType::Integer, 0, Side::Left, false),
            snapshot("E", "other", BaseType::Integer, 0, Side::Left, false),
            snapshot("E", "op", BaseType::String, 0, Side::Left, false),
            snapshot("E", "op", BaseType::Integer, 1, Side::Left, false),
            snapshot("E", "op", BaseType::Integer, 0, Side::Right, false),
            snapshot("E", "op", BaseType::Integer, 0, Side::Left, true),
        ] {
            assert_ne!(
                old.items(),
                new.items(),
                "each revision changes a semantic field"
            );
            let script = super::diff(&old, &new);
            assert_eq!(
                super::apply(old.items(), &script),
                new.items(),
                "annotations, names, frame order and branch-local indices survive reconstruction"
            );
        }
    }

    #[test]
    fn path_evidence_changes_are_reconstructed()
    {
        use alloc::sync::Arc;

        use gandr_core_incremental::ContentNode;
        use gandr_core_incremental::ItemKey;
        use gandr_core_incremental::NodeIndex;
        use gandr_core_incremental::Occurrence;
        use gandr_core_incremental::Program;
        use gandr_core_incremental::Reference;
        use gandr_core_term::CoreArena;
        use gandr_kernel_term::BaseType;
        use gandr_kernel_term::PathEvidence;
        use gandr_surface_lowering::OriginTable;

        use super::Action;
        use super::Root;
        use super::Tree;
        use super::apply;
        use super::diff;
        use super::read;
        use super::spanned;

        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let source = arena.value_quote(unit_type);
        let target = arena.value_quote(integer_type);
        let classifier = arena.value_type_path_universe(source, target);
        let forward = arena.value_path_refl(source);
        let backward = arena.value_path_refl(target);
        let evidence = Arc::new(PathEvidence::default());
        let equivalence =
            arena.value_path_equiv(classifier, forward, backward, Arc::clone(&evidence));
        let product = arena.value_path_product(forward, backward);
        let unit = arena.value_unit();
        let transport = arena.computation_transport(product, unit);
        let program = Program::new(arena, Vec::new()).expect("empty item order");
        let origins = OriginTable::default();
        let (signature, _) = read(&program, &origins, Root::ValueType(classifier));
        assert_eq!(signature.nodes(), &[
            ContentNode::PathUniverse(NodeIndex::from(1_usize), NodeIndex::from(2_usize)),
            ContentNode::Quote(NodeIndex::from(3_usize)),
            ContentNode::Quote(NodeIndex::from(4_usize)),
            ContentNode::Product(Vec::new()),
            ContentNode::Base(BaseType::Integer),
        ]);
        let (body, spans) = read(&program, &origins, Root::Value(equivalence));
        assert_eq!(
            body.nodes().get(.. 4_usize),
            Some(
                [
                    ContentNode::PathEquiv {
                        path_type: NodeIndex::from(1_usize),
                        forward: NodeIndex::from(2_usize),
                        backward: NodeIndex::from(3_usize),
                        evidence: Arc::clone(&evidence),
                    },
                    ContentNode::PathUniverse(NodeIndex::from(4_usize), NodeIndex::from(5_usize)),
                    ContentNode::PathRefl(NodeIndex::from(6_usize)),
                    ContentNode::PathRefl(NodeIndex::from(7_usize)),
                ]
                .as_slice()
            )
        );
        assert!(
            spans
                .iter()
                .all(|span| *span == Maybe::Absent(spanned::Absent::Unrecorded))
        );
        let (transported, _) = read(&program, &origins, Root::Computation(transport));
        assert_eq!(
            transported.nodes().get(.. 5_usize),
            Some(
                [
                    ContentNode::Transport(NodeIndex::from(1_usize), NodeIndex::from(2_usize)),
                    ContentNode::PathProduct(NodeIndex::from(3_usize), NodeIndex::from(4_usize)),
                    ContentNode::Tuple(Vec::new()),
                    ContentNode::PathRefl(NodeIndex::from(5_usize)),
                    ContentNode::PathRefl(NodeIndex::from(6_usize)),
                ]
                .as_slice()
            )
        );

        let old = Snapshot {
            items: vec![ItemTree {
                reference: Reference::Item {
                    key: ItemKey::from("equivalence"),
                    occurrence: Occurrence::from(0_usize),
                },
                declaration: super::DeclarationTree::Value {
                    signature: Maybe::Present(signature),
                    body: Maybe::Present(body),
                },
            }],
            spans: vec![spans],
            bodies: Vec::new(),
        };
        for replacement in [
            PathEvidence {
                source: vec![Vec::new()],
                target: Vec::new(),
            },
            PathEvidence {
                source: Vec::new(),
                target: vec![Vec::new()],
            },
        ] {
            let mut new = old.clone();
            let item = new.items.first_mut().expect("one item");
            let super::DeclarationTree::Value {
                body: Maybe::Present(Tree { ref mut nodes }),
                ..
            } = item.declaration
            else {
                panic!("the equivalence body");
            };
            let root = nodes.first_mut().expect("the equivalence root");
            let ContentNode::PathEquiv {
                ref mut evidence, ..
            } = *root
            else {
                panic!("the equivalence former");
            };
            *evidence = Arc::new(replacement);
            let script = diff(&old, &new);
            assert!(matches!(script.actions(), [Action::Replace { path, .. }]
                if path == &CorePath::new(ItemOrdinal::from(0_usize), Vec::new())));
            assert_eq!(apply(old.items(), &script), new.items());
        }
    }

    #[test]
    fn alignment_matches_exhaustive_reference_subsequences()
    {
        let snapshot = snapshot_of(SourceText::from(
            r#"def a = 1 ;
def b = 2 ;
def c = 3 ;
"#,
        ));
        let old = snapshot.items();
        let permutations = [
            [0_usize, 1_usize, 2_usize],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        for permutation in permutations {
            for selected in 0_u8 .. 8_u8 {
                let new: Vec<_> = permutation
                    .into_iter()
                    .filter(|&index| selected & (1_u8 << index) != 0_u8)
                    .map(|index| old.get(index).expect("three fixture items").clone())
                    .collect();
                let pairs = super::align(old, &new);
                let maximum = (0_u8 .. 8_u8)
                    .filter_map(|mask| {
                        let wanted: Vec<_> = old
                            .iter()
                            .enumerate()
                            .filter(|&(index, _)| mask & (1_u8 << index) != 0_u8)
                            .map(|(_, item)| &item.reference)
                            .collect();
                        let mut remaining = new.iter();
                        wanted
                            .iter()
                            .all(|reference| remaining.any(|item| &item.reference == *reference))
                            .then_some(wanted.len())
                    })
                    .max()
                    .expect("the empty subsequence is valid");
                assert_eq!(
                    pairs.len(),
                    maximum,
                    "permutation {permutation:?}, subset {selected}"
                );
                assert!(pairs.iter().all(|&(left, right)| {
                    old.get(usize::from(left))
                        .zip(new.get(usize::from(right)))
                        .is_some_and(|(before, after)| before.reference == after.reference)
                }));
                assert!(pairs.windows(2).all(|pair| matches!(pair, [(left_old, left_new), (right_old, right_new)] if left_old < right_old && left_new < right_new)));
            }
        }
    }

    #[test]
    fn hulls_cover_descendants_without_inventing_origins()
    {
        use super::ContentNode;
        use super::NodeIndex;
        use super::spanned;
        let tree = super::Tree {
            nodes: vec![
                ContentNode::Case {
                    scrutinee: NodeIndex::from(1_usize),
                    branches: vec![NodeIndex::from(2_usize), NodeIndex::from(3_usize)],
                },
                ContentNode::Tuple(Vec::new()),
                ContentNode::Tuple(Vec::new()),
                ContentNode::Tuple(Vec::new()),
            ],
        };
        let left = ByteSpan::new(
            super::ByteOffset::from(17_usize),
            super::ByteOffset::from(20_usize),
        )
        .expect("ordered extent");
        let right = ByteSpan::new(
            super::ByteOffset::from(4_usize),
            super::ByteOffset::from(9_usize),
        )
        .expect("ordered extent");
        let unknown = Maybe::Absent(spanned::Absent::Unrecorded);
        let mut spans = vec![
            unknown,
            Maybe::Present(left),
            unknown,
            Maybe::Present(right),
        ];
        super::hull(&tree, &mut spans);
        assert_eq!(spans, vec![
            Maybe::Present(
                ByteSpan::new(
                    super::ByteOffset::from(4_usize),
                    super::ByteOffset::from(20_usize)
                )
                .expect("union")
            ),
            Maybe::Present(left),
            unknown,
            Maybe::Present(right)
        ]);
    }

    #[test]
    fn absent_arena_roots_keep_their_sorts()
    {
        use gandr_core_term::CoreArena;
        let program =
            super::Program::new(CoreArena::new(), Vec::new()).expect("empty positions ascend");
        let mut foreign = CoreArena::new();
        let value = foreign.value_unit();
        let computation = foreign.computation_return(value);
        let value_type = foreign.value_type_unit();
        let comp_type = foreign.comp_type_returner(value_type);
        let roots = [
            (super::Root::Value(value), super::Sort::Value),
            (
                super::Root::Computation(computation),
                super::Sort::Computation,
            ),
            (super::Root::ValueType(value_type), super::Sort::ValueType),
            (super::Root::CompType(comp_type), super::Sort::CompType),
        ];
        for (root, sort) in roots {
            let (tree, spans) = super::read(&program, &super::OriginTable::default(), root);
            assert_eq!(tree.nodes, vec![super::ContentNode::Unresolved(sort)]);
            assert_eq!(spans, vec![Maybe::Absent(
                super::spanned::Absent::Unrecorded
            )]);
        }
    }

    /// How deeply the first declaration nests its literal.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Depth(usize);

    /// How many shallow declarations follow the deep one.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Breadth(usize);

    /// A deeply nested first declaration followed by `breadth` shallow ones:
    /// the first's bytes are the same whatever the breadth.
    ///
    /// # Specification
    /// - requires: the fixture size fits memory.
    /// - ensures: the first declaration nests one literal at the requested
    ///   depth, followed by exactly the requested number of independent shallow
    ///   declarations.
    /// - panics: none; writing to a String cannot refuse formatting.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — depth eight with eight and forty following
    ///   declarations. The same independently located literal path and equal
    ///   visit counts distinguish breadth leaking into the first declaration.
    /// - witness: `edit::tests::localize_descends_in_depth_not_map_size`
    #[spec(
        ensures: |ret| {
    ret.lines().count() == breadth.0.saturating_add(1_usize)
        && ret.matches("thunk { return ").count() == depth.0
        && ret.starts_with("def deep = ") && ret.ends_with(" ;\n")
},
    )]
    fn deep_then_shallow(
        depth: Depth,
        breadth: Breadth,
    ) -> String
    {
        let mut nested = String::from("1");
        for _ in 0 .. depth.0 {
            nested = format!("thunk {{ return {nested} }}");
        }
        let mut text = format!("def deep = {nested} ;\n");
        for index in 0 .. breadth.0 {
            writeln!(text, "def d{index} = {index} ;").expect("a string takes every write");
        }
        text
    }

    #[test]
    fn localize_descends_in_depth_not_map_size()
    {
        let depth = Depth(8_usize);
        let narrow_text = deep_then_shallow(depth, Breadth(8_usize));
        let wide_text = deep_then_shallow(depth, Breadth(40_usize));
        let narrow = snapshot_of(SourceText::from(narrow_text.as_str()));
        let wide = snapshot_of(SourceText::from(wide_text.as_str()));
        let nodes = |snapshot: &Snapshot| snapshot.spans.iter().map(Vec::len).sum::<usize>();
        assert!(
            nodes(&wide) > nodes(&narrow),
            "the wide snapshot holds more nodes: {} against {}",
            nodes(&wide),
            nodes(&narrow)
        );

        // The literal: under a thunk and a return per level.
        let literal = CorePath {
            item: ItemOrdinal::from(0_usize),
            slots: vec![ChildSlot(0_usize); depth.0.saturating_mul(2)],
        };
        let Maybe::Present(span) = narrow.span(&literal)
        else {
            panic!("the literal has a span");
        };
        let (narrow_locus, narrow_visited) = narrow.descend(span);
        let (wide_locus, wide_visited) = wide.descend(span);
        assert_eq!(
            narrow_locus,
            Maybe::Present(literal.clone()),
            "the literal localizes to itself"
        );
        assert_eq!(
            narrow_locus, wide_locus,
            "the same span localizes alike in both"
        );
        assert_eq!(
            narrow_visited, wide_visited,
            "the descent examines as many nodes whatever follows the declaration"
        );
        let bound = literal.slots.len().saturating_mul(3).saturating_add(1);
        assert!(
            narrow_visited.0 <= bound,
            "{narrow_visited:?} examined, at most three children for each of {} levels",
            literal.slots.len()
        );
        assert!(
            narrow_visited.0 < nodes(&wide),
            "the descent is no scan: {narrow_visited:?} of {} nodes",
            nodes(&wide)
        );
    }

    #[test]
    fn edit_locus_maps_a_source_edit_to_its_old_span_locus()
    {
        let snapshot = snapshot_of(SourceText::from("def v = thunk { return 1 } ;\n"));
        let literal = CorePath {
            item: ItemOrdinal::from(0_usize),
            slots: vec![ChildSlot(0_usize), ChildSlot(0_usize)],
        };
        let Maybe::Present(span) = snapshot.span(&literal)
        else {
            panic!("the literal has a span");
        };
        let edit = SourceEdit::new(span, span.end());
        assert_eq!(
            snapshot.edit_locus(edit),
            snapshot.localize(span),
            "the edit's locus is its old extent's"
        );
        assert_eq!(
            snapshot.edit_locus(edit),
            Maybe::Present(literal),
            "which is the literal"
        );
    }
}
