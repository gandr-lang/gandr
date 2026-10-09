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

use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::NodeIndex;
use gandr_core_incremental::Program;
use gandr_core_incremental::Reference;
use gandr_core_incremental::Sort;
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
    /// trivial.
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
                .and_then(|node| children(node).get(slot));
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
    /// trivial.
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

/// One item of a revision: its identity, its signature and its body, each
/// read out of the arena.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ItemTree
{
    /// The item's identity across revisions: its key and occurrence.
    reference: Reference,
    /// The declared type.
    signature: Maybe<Tree, signature::Absent>,
    /// The body.
    body: Maybe<Tree, body::Absent>,
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

    /// The declared type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn signature(&self) -> Maybe<&Tree, signature::Absent>
    {
        match self.signature {
            | Maybe::Present(ref tree) => Maybe::Present(tree),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn body(&self) -> Maybe<&Tree, body::Absent>
    {
        match self.body {
            | Maybe::Present(ref tree) => Maybe::Present(tree),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
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
    /// - hypothesis: L3 — the child order is pinned by a hand-built arena
    ///   holding every multi-child former of the body sorts, each leaf's path
    ///   written out by hand and checked against the path its change is diffed
    ///   at; the spans by the localization suite over lowered sources.
    /// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
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
            let declaration = item.declaration();
            let signature = declaration
                .signature()
                .map(|root| read(program, origins, Root::ValueType(root)).0);
            let (body, located) = match declaration.body() {
                | Maybe::Present(root) => {
                    let (tree, located) = read(program, origins, Root::Value(root));
                    (Maybe::Present(tree), located)
                },
                | Maybe::Absent(reason) => (Maybe::Absent(reason), Vec::new()),
            };
            if let Some(&Maybe::Present(span)) = located.first() {
                bodies.push((span, ItemOrdinal::from(ordinal)));
            }
            items.push(ItemTree {
                reference: reference.clone(),
                signature,
                body,
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
    /// - hypothesis: L3 — every leaf of a hand-built tree read at the path
    ///   written out for it.
    /// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
    #[inline]
    pub fn node(
        &self,
        path: &CorePath,
    ) -> Maybe<&ContentNode, addressed::Absent>
    {
        let tree = match self.items.get(usize::from(path.item)) {
            | None => return Maybe::Absent(addressed::Absent::NoItem),
            | Some(&ItemTree {
                body: Maybe::Absent(_),
                ..
            }) => return Maybe::Absent(addressed::Absent::NoBody),
            | Some(&ItemTree {
                body: Maybe::Present(ref tree),
                ..
            }) => tree,
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
    /// - hypothesis: L3 — a literal's span and a body root's span read and
    ///   localized back to their own paths.
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
    #[inline]
    pub fn span(
        &self,
        path: &CorePath,
    ) -> Maybe<ByteSpan, spanned::Absent>
    {
        let (
            Some(&ItemTree {
                body: Maybe::Present(ref tree),
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
    /// - hypothesis: L2 — every node span of several sources, and each of its
    ///   endpoints as a point, is localized and compared with a linear scan of
    ///   every node as the external oracle; L3 for the cost — the nodes the
    ///   descent examines stay fixed as the snapshot grows fivefold.
    /// - witness: `edit::tests::descent_agrees_with_the_linear_stab_oracle`
    /// - witness: `edit::tests::localize_descends_in_depth_not_map_size`
    /// - witness: `tests::edit::localize_finds_smallest_enclosing_term`
    /// - witness: `tests::edit::multi_point_edit_localizes_to_the_common_ancestor`
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
    /// - hypothesis: L3 — a one-literal edit maps to the literal's path, and
    ///   every path the reconstructed diff of the same edit names sits under
    ///   it.
    /// - witness: `edit::tests::edit_locus_maps_a_source_edit_to_its_old_span_locus`
    /// - witness: `tests::edit::edit_locus_contains_the_diff`
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
    /// trivial.
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
                body: Maybe::Present(ref tree),
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
                for (slot, child) in children(node).iter().enumerate() {
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
    /// trivial.
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
/// - hypothesis: L2 for soundness — over generated revision pairs `apply` of
///   the diff reproduces the new revision's own snapshot, the external oracle,
///   and a self-diff is empty; L3 for localization — each action kind is
///   reached by a named edit and asserted at its exact path and payload.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
/// - witness: `tests::edit::literal_edit_is_one_set_int`
/// - witness: `tests::edit::item_insertion_leaves_neighbours_untouched`
/// - witness: `tests::edit::hole_fill_and_erase`
/// - witness: `tests::edit::item_ascription_change_is_one_set_item_ascription`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `tests::edit::comp_constructor_change_is_one_replace`
/// - witness: `tests::edit::item_deletion_is_one_delete`
/// - witness: `tests::edit::multi_point_edit_localizes_to_the_common_ancestor`
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
        if before.signature != after.signature {
            actions.push(Action::SetSignature {
                at,
                from: before.signature.clone(),
                to: after.signature.clone(),
            });
        }
        match (&before.body, &after.body) {
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
/// - hypothesis: L2 — over generated revision pairs the applied diff equals the
///   new revision's own snapshot; L3 — each action kind applied once, a leaf
///   grafted at every child slot of every multi-child former and a subtree at a
///   body root, and the result compared with the edited revision's snapshot.
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_empty_and_apply_is_identity`
/// - witness: `tests::edit::step_comp_child_order_matches_diff_and_rebuild`
/// - witness: `tests::edit::constructor_change_is_one_replace`
/// - witness: `tests::edit::hole_fill_and_erase`
/// - witness: `tests::edit::item_insertion_leaves_neighbours_untouched`
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
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at)) {
                    item.signature.clone_from(to);
                }
            },
            | Action::FillHole { at, ref to } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at)) {
                    item.body = Maybe::Present(to.clone());
                }
            },
            | Action::EraseToHole { at } => {
                if let Some(&mut Some(ref mut item)) = items.get_mut(usize::from(at)) {
                    item.body = Maybe::Absent(body::Absent::Hole);
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
            && let Maybe::Present(ref body) = item.body
        {
            item.body = Maybe::Present(graft(body, &edits));
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
#[derive(Clone, Debug)]
enum Graft<'script>
{
    /// A whole subtree.
    Subtree(&'script Tree),
    /// A leaf node.
    Leaf(ContentNode),
}

/// Where a rebuilt node is copied from.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
            for (slot, nodes) in old_children.iter().zip(new_children.iter()).enumerate() {
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
/// trivial.
fn agreement(
    old: &ContentNode,
    new: &ContentNode,
) -> Agreement
{
    let same = match (old, new) {
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
        | _ if children(old).count == 0_usize => old == new,
        | _ => mem::discriminant(old) == mem::discriminant(new),
    };
    if same {
        Agreement::Same
    }
    else {
        Agreement::Differs
    }
}

/// The children of one content node, in its former's order.
#[derive(Clone, Copy, Debug, Default)]
struct Children
{
    /// The children; slots from `count` on are unused.
    slots: [NodeIndex; 3],
    /// How many slots are used.
    count: usize,
}

impl Children
{
    /// The child at `slot`.
    ///
    /// # Specification
    /// trivial.
    fn get(
        &self,
        slot: ChildSlot,
    ) -> Option<NodeIndex>
    {
        if slot.0 < self.count {
            self.slots.get(slot.0).copied()
        }
        else {
            None
        }
    }

    /// The children, in order.
    ///
    /// # Specification
    /// trivial.
    fn iter(&self) -> impl Iterator<Item = NodeIndex>
    {
        self.slots.iter().take(self.count).copied()
    }
}

/// The children of `node`, in its former's order.
///
/// # Specification
/// trivial.
fn children(node: &ContentNode) -> Children
{
    let unused = NodeIndex::default();
    let (slots, count) = match *node {
        | ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::Unit
        | ContentNode::Literal(_)
        | ContentNode::Base(_)
        | ContentNode::UnitType
        | ContentNode::Universe { .. }
        | ContentNode::Abstract(_)
        | ContentNode::Unresolved(_) => ([unused; 3], 0_usize),
        | ContentNode::Injection(_, only)
        | ContentNode::Thunk(only)
        | ContentNode::ValueLift { body: only, .. }
        | ContentNode::Quote(only)
        | ContentNode::QuoteComputation(only)
        | ContentNode::Lambda(only)
        | ContentNode::Return(only)
        | ContentNode::Force(only)
        | ContentNode::ThunkType(only)
        | ContentNode::TypeLift { inner: only, .. }
        | ContentNode::Element { code: only, .. }
        | ContentNode::ComputationElement { code: only, .. }
        | ContentNode::Returner(only) => ([only, unused, unused], 1_usize),
        | ContentNode::Pair(first, second)
        | ContentNode::Application(first, second)
        | ContentNode::Bind(first, second)
        | ContentNode::Product(first, second)
        | ContentNode::Sum(first, second)
        | ContentNode::Arrow {
            domain: first,
            codomain: second,
        }
        | ContentNode::Pi {
            domain: first,
            codomain: second,
        } => ([first, second, unused], 2_usize),
        | ContentNode::Case {
            scrutinee,
            on_left,
            on_right,
        } => ([scrutinee, on_left, on_right], 3_usize),
    };
    Children { slots, count }
}

/// `node` with each child replaced by its image under `image`, children
/// visited in the former's order.
///
/// # Specification
/// trivial.
fn map_children<Image>(
    node: &ContentNode,
    image: &mut Image,
) -> ContentNode
where
    Image: FnMut(NodeIndex) -> NodeIndex,
{
    match *node {
        | ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::Unit
        | ContentNode::Literal(_)
        | ContentNode::Base(_)
        | ContentNode::UnitType
        | ContentNode::Universe { .. }
        | ContentNode::Abstract(_)
        | ContentNode::Unresolved(_) => node.clone(),
        | ContentNode::Pair(first, second) => {
            let first = image(first);
            ContentNode::Pair(first, image(second))
        },
        | ContentNode::Injection(side, body) => ContentNode::Injection(side, image(body)),
        | ContentNode::Thunk(body) => ContentNode::Thunk(image(body)),
        | ContentNode::ValueLift { ref target, body } => ContentNode::ValueLift {
            target: target.clone(),
            body: image(body),
        },
        | ContentNode::Quote(quoted) => ContentNode::Quote(image(quoted)),
        | ContentNode::QuoteComputation(quoted) => ContentNode::QuoteComputation(image(quoted)),
        | ContentNode::Lambda(body) => ContentNode::Lambda(image(body)),
        | ContentNode::Application(head, argument) => {
            let head = image(head);
            ContentNode::Application(head, image(argument))
        },
        | ContentNode::Return(value) => ContentNode::Return(image(value)),
        | ContentNode::Bind(bound, rest) => {
            let bound = image(bound);
            ContentNode::Bind(bound, image(rest))
        },
        | ContentNode::Force(value) => ContentNode::Force(image(value)),
        | ContentNode::Case {
            scrutinee,
            on_left,
            on_right,
        } => {
            let scrutinee = image(scrutinee);
            let on_left = image(on_left);
            ContentNode::Case {
                scrutinee,
                on_left,
                on_right: image(on_right),
            }
        },
        | ContentNode::Product(first, second) => {
            let first = image(first);
            ContentNode::Product(first, image(second))
        },
        | ContentNode::Sum(first, second) => {
            let first = image(first);
            ContentNode::Sum(first, image(second))
        },
        | ContentNode::ThunkType(body) => ContentNode::ThunkType(image(body)),
        | ContentNode::TypeLift { inner, ref target } => ContentNode::TypeLift {
            inner: image(inner),
            target: target.clone(),
        },
        | ContentNode::Element { code, ref target } => ContentNode::Element {
            code: image(code),
            target: target.clone(),
        },
        | ContentNode::ComputationElement { code, ref target } => ContentNode::ComputationElement {
            code: image(code),
            target: target.clone(),
        },
        | ContentNode::Returner(result) => ContentNode::Returner(image(result)),
        | ContentNode::Arrow { domain, codomain } => {
            let domain = image(domain);
            ContentNode::Arrow {
                domain,
                codomain: image(codomain),
            }
        },
        | ContentNode::Pi { domain, codomain } => {
            let domain = image(domain);
            ContentNode::Pi {
                domain,
                codomain: image(codomain),
            }
        },
    }
}

/// The root a tree is read from.
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
/// trivial.
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
/// trivial.
fn read_value<Child>(
    program: &Program,
    id: ValueId,
    child: &mut Child,
) -> ContentNode
where
    Child: FnMut(Root) -> NodeIndex,
{
    match program.arena().value(id) {
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
        | None => ContentNode::Unresolved(Sort::Value),
    }
}

/// The content node of the computation `id`, each child numbered by `child`.
///
/// # Specification
/// trivial.
fn read_computation<Child>(
    program: &Program,
    id: ComputationId,
    child: &mut Child,
) -> ContentNode
where
    Child: FnMut(Root) -> NodeIndex,
{
    match program.arena().computation(id) {
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
/// trivial.
fn read_value_type<Child>(
    program: &Program,
    id: ValueTypeId,
    child: &mut Child,
) -> ContentNode
where
    Child: FnMut(Root) -> NodeIndex,
{
    match program.arena().value_type(id) {
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
        | None => ContentNode::Unresolved(Sort::ValueType),
    }
}

/// The content node of the computation type `id`, each child numbered by
/// `child`.
///
/// # Specification
/// trivial.
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
/// trivial.
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
        for child in children(node).iter() {
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
    /// trivial.
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
    /// trivial.
    fn stab(
        snapshot: &Snapshot,
        range: ByteSpan,
    ) -> Maybe<CorePath, located::Absent>
    {
        let mut best: Option<(ByteSpan, usize, CorePath)> = None;
        for (ordinal, (item, spans)) in snapshot.items.iter().zip(&snapshot.spans).enumerate() {
            let &ItemTree {
                body: Maybe::Present(ref tree),
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
                for (slot, child) in children(node).iter().enumerate() {
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
            let mut probes = 0_usize;
            for spans in &snapshot.spans {
                for &span in spans {
                    let Maybe::Present(span) = span
                    else {
                        continue;
                    };
                    let start = ByteSpan::new(span.start(), span.start()).expect("a point");
                    let end = ByteSpan::new(span.end(), span.end()).expect("a point");
                    for probe in [span, start, end] {
                        probes = probes.saturating_add(1);
                        assert_eq!(
                            snapshot.localize(probe),
                            stab(&snapshot, probe),
                            "{source:?}: the descent and the linear stab disagree at {probe:?}"
                        );
                    }
                }
            }
            assert!(probes > 0_usize, "{source:?} has spanned nodes to probe");
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
    /// trivial.
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
