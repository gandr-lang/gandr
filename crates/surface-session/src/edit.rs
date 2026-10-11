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
                | Some(child) => at = child,
                | None => return Maybe::Absent(addressed::Absent::NoChild),
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
    #[inline]
    #[must_use]
    pub const fn signature(&self) -> Option<&Tree>
    {
        match self.declaration {
            | DeclarationTree::Value {
                signature: Maybe::Present(ref tree),
                ..
            } => Some(tree),
            | DeclarationTree::Value {
                signature: Maybe::Absent(_),
                ..
            }
            | DeclarationTree::Data { .. } => None,
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
            | DeclarationTree::Value {
                body: Maybe::Present(ref tree),
                ..
            } => Some(tree),
            | DeclarationTree::Value {
                body: Maybe::Absent(_),
                ..
            }
            | DeclarationTree::Data { .. } => None,
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
                | gandr_core_checker::DeclarationContent::Value {
                    ref signature,
                    ref body,
                } => {
                    let signature =
                        signature.map(|root| read(program, origins, Root::ValueType(root)).0);
                    let (body, located) = match *body {
                        | Maybe::Present(root) => {
                            let (tree, located) = read(program, origins, Root::Value(root));
                            (Maybe::Present(tree), located)
                        },
                        | Maybe::Absent(reason) => (Maybe::Absent(reason), Vec::new()),
                    };
                    (DeclarationTree::Value { signature, body }, located)
                },
                | gandr_core_checker::DeclarationContent::Data(ref signature) => {
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
        tree.resolve(&path.slots)
            .and_then(|at| match tree.nodes.get(usize::from(at)) {
                | Some(node) => Maybe::Present(node),
                | None => Maybe::Absent(addressed::Absent::NoChild),
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
            | Maybe::Present(at) => spans
                .get(usize::from(at))
                .copied()
                .unwrap_or(Maybe::Absent(spanned::Absent::Unaddressed)),
            | Maybe::Absent(_) => Maybe::Absent(spanned::Absent::Unaddressed),
        }
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
    ///   counts. The predicate checks containment and Outside without replaying
    ///   the allocating localizer.
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
        self.bodies
            .iter()
            .all(|&(span, _)| {
                !(span.start() <= range.start() && range.end() <= span.end())
            })
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
    ///   independent path witness.
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
        self.bodies
            .iter()
            .all(|&(span, _)| {
                !(span.start() <= edit.old.start() && edit.old.end() <= span.end())
            })
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
            self.bodies
                .iter()
                .all(|&(span, _)| {
                    !(span.start() <= range.start() && range.end() <= span.end())
                })
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
        let after = self
            .bodies
            .partition_point(|&(span, _)| span.start() <= range.start());
        let Some(&(root_span, item)) = after
            .checked_sub(1_usize)
            .and_then(|at| self.bodies.get(at))
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
            | Self::Replace { ref path, .. }
            | Self::SetLiteral { ref path, .. }
            | Self::SetVariable { ref path, .. }
            | Self::SetConstant { ref path, .. } => Maybe::Present(path),
            | Self::InsertItem { .. }
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
///   together, a differing literal, variable or constant leaf becoming one
///   in-place action and any other difference one [`Action::Replace`] of the
///   old subtree. Equal revisions give the empty script.
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
/// - witness: `tests::edit::item_ascription_change_is_one_set_item_ascription`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `tests::edit::comp_constructor_change_is_one_replace`
/// - witness: `tests::edit::item_deletion_is_one_delete`
/// - witness: `tests::edit::multi_point_edit_localizes_to_the_common_ancestor`
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
            | (&Maybe::Absent(_), &Maybe::Absent(_)) => {},
            | (&Maybe::Absent(_), &Maybe::Present(ref body)) => {
                actions.push(Action::FillHole {
                    at,
                    to: body.clone(),
                });
            },
            | (&Maybe::Present(_), &Maybe::Absent(_)) => actions.push(Action::EraseToHole { at }),
            | (&Maybe::Present(ref from), &Maybe::Present(ref to)) => {
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
                _ => true,
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
            | Action::InsertItem { at, ref item } => inserted.push((at, item)),
            | Action::DeleteItem { at } => {
                if let Some(slot) = items.get_mut(usize::from(at)) {
                    *slot = None;
                }
            },
            | Action::SetSignature { at, ref to, .. } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at))
                    && let DeclarationTree::Value {
                        ref mut signature, ..
                    } = item.declaration
                {
                    signature.clone_from(to);
                }
            },
            | Action::FillHole { at, ref to } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at))
                    && let DeclarationTree::Value { ref mut body, .. } = item.declaration
                {
                    *body = Maybe::Present(to.clone());
                }
            },
            | Action::EraseToHole { at } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at))
                    && let DeclarationTree::Value { ref mut body, .. } = item.declaration
                {
                    *body = Maybe::Absent(body::Absent::Hole);
                }
            },
            | Action::Replace { ref path, ref to } => {
                grafts
                    .entry(path.item)
                    .or_default()
                    .push((path, Graft::Subtree(to)));
            },
            | Action::SetLiteral {
                ref path, ref to, ..
            } => {
                grafts
                    .entry(path.item)
                    .or_default()
                    .push((path, Graft::Leaf(ContentNode::Literal(to.clone()))));
            },
            | Action::SetVariable {
                ref path,
                to: (zone, index),
                ..
            } => {
                grafts
                    .entry(path.item)
                    .or_default()
                    .push((path, Graft::Leaf(ContentNode::Variable { zone, index })));
            },
            | Action::SetConstant {
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
            | Source::Old(index) => match at_node.get(&index) {
                | Some(&&Graft::Subtree(subtree)) => {
                    Source::Grafted(subtree, NodeIndex::from(0_usize))
                },
                | Some(&&Graft::Leaf(ref leaf)) => {
                    nodes.push(leaf.clone());
                    continue;
                },
                | None => source,
            },
            | Source::Grafted(..) => source,
        };
        let node = match source {
            | Source::Old(index) => tree.nodes.get(usize::from(index)),
            | Source::Grafted(subtree, index) => subtree.nodes.get(usize::from(index)),
        };
        let Some(node) = node
        else {
            continue;
        };
        nodes.push(map_children(node, &mut |child| {
            queue.push_back(match source {
                | Source::Old(_) => Source::Old(child),
                | Source::Grafted(subtree, _) => Source::Grafted(subtree, child),
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
                        _ => false,
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
            | (&ContentNode::Literal(ref from), &ContentNode::Literal(ref to)) => {
                Action::SetLiteral {
                    path,
                    from: from.clone(),
                    to: to.clone(),
                }
            },
            | (
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
            | (&ContentNode::Constant(ref from), &ContentNode::Constant(ref to)) => {
                Action::SetConstant {
                    path,
                    from: from.clone(),
                    to: to.clone(),
                }
            },
            | _ => Action::Replace {
                path,
                to: new.subtree(new_at),
            },
        });
    }
}

/// Whether two nodes share their former and payload.
///
/// # Specification
/// - requires: nothing beyond the documented producer and consumer contracts.
/// - ensures: Same means equal former and non-child payload, not equal
///   descendants; A difference requires replacing a leaf or subtree.
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
    /// One former, one payload: the walk descends into the children.
    Same,
    /// The former or the payload differs: the walk emits an action.
    Differs,
}

/// Whether `old` and `new` share their former and payload, children aside.
///
/// # Specification
/// - requires: nothing.
/// - ensures: agrees exactly on the former and non-child payload: leaf values,
///   injection side, classifier targets, and path evidence matter; child
///   indices do not.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — literal, variable, constant and constructor edits, plus
///   payload-bearing node pairs whose children alone differ. Distinct actions
///   and exact payloads distinguish ignoring semantic data or treating
///   renumbered children as a change. Independent source- and target-dialogue
///   edits retain their evidence even when every child is unchanged.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `edit::tests::path_evidence_changes_are_reconstructed`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `edit::tests::child_mapping_preserves_payloads_without_replaying_the_callback`
#[spec(
    ensures: |ret| {
    (ret == Agreement::Same)
        == (mem::discriminant(old) == mem::discriminant(new)
            && match *old {
                ContentNode::Data {declaration:ref left,ref arguments} => matches!(*new,ContentNode::Data {declaration:ref right,arguments:ref other} if left == right && arguments.len() == other.len()),
                ContentNode::Constructor {tag,ref fields,..} => matches!(*new,ContentNode::Constructor {tag:other,fields:ref theirs,..} if tag == other && fields.len() == theirs.len()),
                ContentNode::Record(ref fields) => matches!(*new,ContentNode::Record(ref other) if fields.keys().eq(other.keys())),
                ContentNode::RecordType(ref fields) => matches!(*new,ContentNode::RecordType(ref other) if fields.keys().eq(other.keys())),
                ContentNode::DataCase {ref branches,..} => matches!(*new,ContentNode::DataCase {branches:ref other,..} if branches.len() == other.len()),
                ContentNode::RecordProjection(_,ref label) => matches!(*new,ContentNode::RecordProjection(_,ref other) if label == other),
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
                _ if children(old).next().is_none() => old == new,
                _ => true,
            })
},
)]
fn agreement(
    old: &ContentNode,
    new: &ContentNode,
) -> Agreement
{
    let same = match (old, new) {
        | (
            &ContentNode::Data {
                declaration: ref left,
                arguments: ref a,
            },
            &ContentNode::Data {
                declaration: ref right,
                arguments: ref b,
            },
        ) => left == right && a.len() == b.len(),
        | (
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
        | (&ContentNode::Record(ref left), &ContentNode::Record(ref right))
        | (&ContentNode::RecordType(ref left), &ContentNode::RecordType(ref right)) => {
            left.keys().eq(right.keys())
        },
        | (
            &ContentNode::DataCase {
                branches: ref left, ..
            },
            &ContentNode::DataCase {
                branches: ref right,
                ..
            },
        ) => left.len() == right.len(),
        | (
            &ContentNode::RecordProjection(_, ref left),
            &ContentNode::RecordProjection(_, ref right),
        ) => left == right,
        | (
            &ContentNode::PathEquiv {
                evidence: ref left, ..
            },
            &ContentNode::PathEquiv {
                evidence: ref right,
                ..
            },
        ) => left == right,
        | (&ContentNode::Injection(left, _), &ContentNode::Injection(right, _)) => left == right,
        | (
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
        | _ if children(old).next().is_none() => old == new,
        | _ => mem::discriminant(old) == mem::discriminant(new),
    };
    if same {
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
            | Root::Value(id) => (read_value(program, id, &mut child), origins.value(id)),
            | Root::Computation(id) => (
                read_computation(program, id, &mut child),
                origins.computation(id),
            ),
            | Root::ValueType(id) => (
                read_value_type(program, id, &mut child),
                origins.value_type(id),
            ),
            | Root::CompType(id) => (
                read_comp_type(program, id, &mut child),
                origins.comp_type(id),
            ),
        };
        nodes.push(node);
        spans.push(match origin {
            | Maybe::Present(origin) => Maybe::Present(origin.span()),
            | Maybe::Absent(_) => Maybe::Absent(spanned::Absent::Unrecorded),
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
                Value::Primitive { primitive, .. } => ret == ContentNode::PrimitiveValue(primitive),
                Value::PathRefl(_) => matches!(ret, ContentNode::PathRefl(_)),
                Value::PathProduct(..) => matches!(ret, ContentNode::PathProduct(..)),
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
                Value::Unit => matches!(ret, ContentNode::Unit),
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
                Value::Pair(..) => matches!(ret, ContentNode::Pair(..)),
                Value::Thunk(..) => matches!(ret, ContentNode::Thunk(..)),
                Value::Quote(..) => matches!(ret, ContentNode::Quote(..)),
                Value::QuoteComputation(..) => {
                    matches!(ret, ContentNode::QuoteComputation(..))
                }
                Value::StaticLambda(..) => matches!(ret, ContentNode::StaticLambda(..)),
                Value::StaticApplication(..) => {
                    matches!(ret, ContentNode::StaticApplication(..))
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
        | Some(&Value::Constructor {
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
        | Some(&Value::Record(ref fields)) => ContentNode::Record(
            fields
                .iter()
                .map(|(label, &field)| (label.clone(), child(Root::Value(field))))
                .collect(),
        ),
        | Some(&Value::Primitive { primitive, .. }) => ContentNode::PrimitiveValue(primitive),
        | Some(&Value::PathRefl(code)) => ContentNode::PathRefl(child(Root::Value(code))),
        | Some(&Value::PathProduct(first, second)) => {
            let first = child(Root::Value(first));
            ContentNode::PathProduct(first, child(Root::Value(second)))
        },
        | Some(&Value::PathEquiv {
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
        | Some(&Value::Variable { zone, index }) => ContentNode::Variable { zone, index },
        | Some(&Value::Constant(position)) => ContentNode::Constant(program.resolve(position)),
        | Some(&Value::Unit) => ContentNode::Unit,
        | Some(&Value::Literal(ref literal)) => ContentNode::Literal(literal.clone()),
        | Some(&Value::Pair(first, second)) => {
            let first = child(Root::Value(first));
            ContentNode::Pair(first, child(Root::Value(second)))
        },
        | Some(&Value::Injection(side, body)) => {
            ContentNode::Injection(side, child(Root::Value(body)))
        },
        | Some(&Value::Thunk(body)) => ContentNode::Thunk(child(Root::Computation(body))),
        | Some(&Value::Lift { ref target, body }) => ContentNode::ValueLift {
            target: target.clone(),
            body: child(Root::Value(body)),
        },
        | Some(&Value::Quote(quoted)) => ContentNode::Quote(child(Root::ValueType(quoted))),
        | Some(&Value::QuoteComputation(quoted)) => {
            ContentNode::QuoteComputation(child(Root::CompType(quoted)))
        },
        | Some(&Value::StaticLambda(body)) => ContentNode::StaticLambda(child(Root::Value(body))),
        | Some(&Value::StaticApplication(head, argument)) => {
            let head = child(Root::Value(head));
            ContentNode::StaticApplication(head, child(Root::Value(argument)))
        },
        | None => ContentNode::Unresolved(Sort::Value),
    }
}

/// The content node of the computation `id`, each child numbered by `child`.
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
        .computation(id)
        .map_or(
            matches!(ret, ContentNode::Unresolved(Sort::Computation)),
            |node| match *node {
                Computation::DataCase {ref branches,..} => matches!(ret,ContentNode::DataCase {branches:ref other,..} if branches.len() == other.len()),
                Computation::RecordProjection(_,ref label) => matches!(ret,ContentNode::RecordProjection(_,ref other) if label == other),
                Computation::Primitive { primitive, .. } => matches!(ret, ContentNode::Primitive(actual, _) if actual == primitive),
                Computation::Transport(..) => matches!(ret, ContentNode::Transport(..)),
                Computation::Lambda(..) => matches!(ret, ContentNode::Lambda(..)),
                Computation::Application(..) => {
                    matches!(ret, ContentNode::Application(..))
                }
                Computation::Return(..) => matches!(ret, ContentNode::Return(..)),
                Computation::Bind(..) => matches!(ret, ContentNode::Bind(..)),
                Computation::Force(..) => matches!(ret, ContentNode::Force(..)),
                Computation::Case { .. } => matches!(ret, ContentNode::Case { .. }),
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
        | Some(&Computation::DataCase {
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
        | Some(&Computation::RecordProjection(record, ref label)) => {
            ContentNode::RecordProjection(child(Root::Value(record)), label.clone())
        },
        | Some(&Computation::Primitive {
            primitive,
            arguments,
        }) => {
            use gandr_core_term::primitive::Arguments;
            let arguments = match arguments {
                | Arguments::Unary(argument) => Arguments::Unary(child(Root::Value(argument))),
                | Arguments::Binary([first, second]) => {
                    Arguments::Binary([child(Root::Value(first)), child(Root::Value(second))])
                },
            };
            ContentNode::Primitive(primitive, arguments)
        },
        | Some(&Computation::Transport(path, value)) => {
            let path = child(Root::Value(path));
            ContentNode::Transport(path, child(Root::Value(value)))
        },
        | Some(&Computation::Lambda(body)) => ContentNode::Lambda(child(Root::Computation(body))),
        | Some(&Computation::Application(head, argument)) => {
            let head = child(Root::Computation(head));
            ContentNode::Application(head, child(Root::Value(argument)))
        },
        | Some(&Computation::Return(value)) => ContentNode::Return(child(Root::Value(value))),
        | Some(&Computation::Bind(bound, rest)) => {
            let bound = child(Root::Computation(bound));
            ContentNode::Bind(bound, child(Root::Computation(rest)))
        },
        | Some(&Computation::Force(value)) => ContentNode::Force(child(Root::Value(value))),
        | Some(&Computation::Case {
            scrutinee,
            on_left,
            on_right,
        }) => {
            let scrutinee = child(Root::Value(scrutinee));
            let on_left = child(Root::Computation(on_left));
            ContentNode::Case {
                scrutinee,
                on_left,
                on_right: child(Root::Computation(on_right)),
            }
        },
        | None => ContentNode::Unresolved(Sort::Computation),
    }
}

/// The content node of the value type `id`, each child numbered by `child`.
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
        .value_type(id)
        .map_or(
            matches!(ret, ContentNode::Unresolved(Sort::ValueType)),
            |node| match *node {
                ValueType::Data {declaration,ref arguments} => matches!(ret,ContentNode::Data {declaration:ref found,arguments:ref other} if *found == program.resolve(declaration) && arguments.len() == other.len()),
                ValueType::Record(ref fields) => matches!(ret,ContentNode::RecordType(ref other) if fields.keys().eq(other.keys())),
                ValueType::PathUniverse(..) => {
                    matches!(ret, ContentNode::PathUniverse(..))
                }
                ValueType::Base(base) => {
                    matches!(ret, ContentNode::Base(found) if found == base)
                }
                ValueType::Unit => matches!(ret, ContentNode::UnitType),
                ValueType::Product(..) => matches!(ret, ContentNode::Product(..)),
                ValueType::Sum(..) => matches!(ret, ContentNode::Sum(..)),
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
        | Some(&ValueType::Data {
            declaration,
            ref arguments,
        }) => ContentNode::Data {
            declaration: program.resolve(declaration),
            arguments: arguments
                .iter()
                .map(|&argument| child(Root::Value(argument)))
                .collect(),
        },
        | Some(&ValueType::Record(ref fields)) => ContentNode::RecordType(
            fields
                .iter()
                .map(|(label, &field)| (label.clone(), child(Root::ValueType(field))))
                .collect(),
        ),
        | Some(&ValueType::PathUniverse(source, target)) => {
            let source = child(Root::Value(source));
            ContentNode::PathUniverse(source, child(Root::Value(target)))
        },
        | Some(&ValueType::Base(base)) => ContentNode::Base(base),
        | Some(&ValueType::Unit) => ContentNode::UnitType,
        | Some(&ValueType::Product(first, second)) => {
            let first = child(Root::ValueType(first));
            ContentNode::Product(first, child(Root::ValueType(second)))
        },
        | Some(&ValueType::Sum(first, second)) => {
            let first = child(Root::ValueType(first));
            ContentNode::Sum(first, child(Root::ValueType(second)))
        },
        | Some(&ValueType::Thunk(body)) => ContentNode::ThunkType(child(Root::CompType(body))),
        | Some(&ValueType::Universe { sort, ref level }) => ContentNode::Universe {
            sort,
            level: level.clone(),
        },
        | Some(&ValueType::Lift { inner, ref target }) => ContentNode::TypeLift {
            inner: child(Root::ValueType(inner)),
            target: target.clone(),
        },
        | Some(&ValueType::Element { code, ref target }) => ContentNode::Element {
            code: child(Root::Value(code)),
            target: target.clone(),
        },
        | Some(&ValueType::Abstract(position)) => ContentNode::Abstract(program.resolve(position)),
        | Some(&ValueType::StaticPi { domain, codomain }) => {
            let domain = child(Root::ValueType(domain));
            ContentNode::StaticPi {
                domain,
                codomain: child(Root::ValueType(codomain)),
            }
        },
        | None => ContentNode::Unresolved(Sort::ValueType),
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
                CompType::Returner(_) => matches!(ret, ContentNode::Returner(_)),
                CompType::Arrow { .. } => matches!(ret, ContentNode::Arrow { .. }),
                CompType::Pi { .. } => matches!(ret, ContentNode::Pi { .. }),
                CompType::Element { ref target, .. } => {
                    matches!(
                        ret, ContentNode::ComputationElement { target : ref found, .. }
                        if found == target
                    )
                }
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
        | Some(&CompType::Returner(result)) => {
            ContentNode::Returner(child(Root::ValueType(result)))
        },
        | Some(&CompType::Arrow { domain, codomain }) => {
            let domain = child(Root::ValueType(domain));
            ContentNode::Arrow {
                domain,
                codomain: child(Root::CompType(codomain)),
            }
        },
        | Some(&CompType::Pi { domain, codomain }) => {
            let domain = child(Root::ValueType(domain));
            ContentNode::Pi {
                domain,
                codomain: child(Root::CompType(codomain)),
            }
        },
        | Some(&CompType::Element { code, ref target }) => ContentNode::ComputationElement {
            code: child(Root::Value(code)),
            target: target.clone(),
        },
        | None => ContentNode::Unresolved(Sort::CompType),
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
            | Some(&Maybe::Present(span)) => Some(span),
            | Some(&Maybe::Absent(_)) | None => None,
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
            | Some((_, _, path)) => Maybe::Present(path),
            | None => Maybe::Absent(located::Absent::Outside),
        }
    }

    #[test]
    fn descent_agrees_with_the_linear_stab_oracle()
    {
        let sources = [
            "def deep = thunk { ret thunk { ret thunk { ret 1 } } } ;\n",
            "def target(x: Integer) -> -F Integer {\n  ret 1\n}\ndef shown : +U (-F Integer) ;\ndef shown = thunk { (force target)(0) } ;\n",
            "def a = 1 ;\ndef b = 2 ;\ndef c = 3 ;\n",
            "def owed : Integer ;\ndef reads = owed ;\n",
            "def f(x: Integer) -> -F Integer { ret x }\ndef twice = thunk { (force f)(\"text\") } ;\n",
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
        assert_eq!(children(&super::ContentNode::Unit).next(), None);
    }

    #[test]
    fn child_mapping_preserves_payloads_without_replaying_the_callback()
    {
        use gandr_kernel_term::Side;

        use super::ContentNode;
        use super::NodeIndex;
        let original = ContentNode::Case {
            scrutinee: NodeIndex::from(7_usize),
            on_left: NodeIndex::from(3_usize),
            on_right: NodeIndex::from(11_usize),
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
            on_left: NodeIndex::from(21_usize),
            on_right: NodeIndex::from(22_usize)
        });
        assert_eq!(children(&mapped).nth(3), None);
        let left = ContentNode::Injection(Side::Left, NodeIndex::from(7_usize));
        let changed = super::map_children(&left, &mut |_| NodeIndex::from(8_usize));
        assert_eq!(
            changed,
            ContentNode::Injection(Side::Left, NodeIndex::from(8_usize))
        );
        assert_eq!(super::agreement(&left, &changed), super::Agreement::Same);
        assert_ne!(
            super::agreement(
                &left,
                &ContentNode::Injection(Side::Right, NodeIndex::from(7_usize))
            ),
            super::Agreement::Same
        );
        assert_eq!(
            super::map_children(&ContentNode::Unit, &mut |_| panic!("a leaf has no child")),
            ContentNode::Unit
        );
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
            ContentNode::UnitType,
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
                    ContentNode::Unit,
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
                    on_left: NodeIndex::from(2_usize),
                    on_right: NodeIndex::from(3_usize),
                },
                ContentNode::Unit,
                ContentNode::Unit,
                ContentNode::Unit,
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
        && ret.matches("thunk { ret ").count() == depth.0
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
            nested = format!("thunk {{ ret {nested} }}");
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
        let snapshot = snapshot_of(SourceText::from("def v = thunk { ret 1 } ;\n"));
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
