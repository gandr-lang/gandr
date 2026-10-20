//! Co-de Bruijn content: every table node a former over its own minimal
//! scope, carrying the references beneath it.
//!
//! # A node is its own scope
//!
//! A content table node is a [`SupportedNode`]: a [`ContentNode`] former
//! whose variable occurrences are ranks in the node's own scope, the cover
//! — one [`Thinning`] edge per child, from `gandr_core_term::support` —
//! placing each child's scope in that scope past the binders the former opens
//! over it, the scope's widths, and the references beneath the node, in value
//! and in type positions. A former names at most one occurrence itself: a
//! variable's index, a session action's endpoint, a memory form's slot or
//! view. Every other index of the subterm lives in the covers, so a variable
//! is a bare leaf — `x₀` in a scope of one — and one subterm under
//! different unused binders is one node.
//!
//! [`factor`] turns a de Bruijn table, as the encoder reads it off an arena,
//! into this form bottom-up and hash-conses it: two subterms whose formers,
//! covers and widths agree are the same node wherever they stand, whatever
//! their arena sharing. [`number`] renumbers the reachable nodes breadth-first
//! from the roots, so equal content is an equal table. [`expand`] is the de
//! Bruijn projection: from a root and its support in the ambient scope it
//! places every node and recovers the de Bruijn table, refusing an index past
//! `u32` rather than saturating it. [`assemble`] is the reader's check: it
//! rebuilds every node's references from a decoded table and refuses a
//! cycle, a cover that is not the exact minimal cover of its node, and two
//! entries that are the same node.
//!
//! A node's references are its own reference, if it names one, and every
//! child's, a child's value reads promoted to type reads beneath a type
//! former. They are what the footprint reads off the roots, so no walk of the
//! table recovers them. A set is shared, not copied, by every ancestor that
//! adds nothing to it, so a spine of nodes above one reference holds one set.
//!
//! The interner searches a table's first few nodes in order, which costs
//! less than hashing them, and indexes a larger table in a `hashbrown`
//! table under `foldhash`'s fixed-seed state, the pair the grammar's label
//! index measured and chose: factoring probes it once per de Bruijn entry,
//! and the standard map's `SipHash` and a bucket list per hash cost more
//! than the rest of the probe. The keys are syntax the encoder built from a
//! checked arena, not input a seeded hasher would defend against.
//! **Reversal.** As the grammar's: the hasher unmaintained or dropped from
//! the graph.
//!
//! **Choice.** The table keeps the core vocabulary's own former type, with
//! each index the former carries — its own occurrence — rewritten to its
//! rank in the node's scope, so the vocabulary, its walks and its consumers
//! stay one type. **Alternatives.** A former generic in its index type, unit
//! for a compact variable, which cannot express the linear indices session
//! and memory payloads carry as plain de Bruijn indices; a parallel compact
//! vocabulary, a second copy of a hundred formers. **Reversal.** A former
//! that names two occurrences of its own.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::hash::BuildHasher as _;
use core::hash::Hash;
use core::hash::Hasher;
use std::collections::HashSet;

use anodized::spec;
use foldhash::fast::FixedState;
use gandr_core_term::support::Cover;
use gandr_core_term::support::CoverError;
use gandr_core_term::support::Crossing;
use gandr_core_term::support::PlacementError;
use gandr_core_term::support::Scope;
use gandr_core_term::support::Thinning;
use gandr_core_term::support::check_cover;
use hashbrown::HashTable;
use quenchant_shape::shape::Maybe;

use crate::boundary::NodeIndex;
use crate::content::ContentNode;
use crate::content::Opacity;
use crate::content::Sort;
use crate::content::map_children;
use crate::region::Reference;

/// One compact former, its cover and scope, and the references beneath it.
///
/// # Specification
/// - executable: none — a data declaration; [`factor`] and [`assemble`]
///   establish that the cover is the exact minimal cover of the node, the
///   former's own occurrence a rank in its scope, and the references those of
///   its subterm.
///
/// # Adequacy
/// - hypothesis: L2 — an independent arena walk observes the references; L3 —
///   relocation under unused binders and forged covers separate the support
///   from cached indices.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SupportedNode
{
    /// The former, its own occurrence a rank in `scope`.
    former: ContentNode,
    /// One edge per child, in child order.
    cover: Vec<Thinning>,
    /// The node's minimal scope.
    scope: Scope,
    /// References outside every type former.
    value_reads: Reads,
    /// References beneath a type former, or a type former's own.
    type_reads: Reads,
    /// Whether the subterm holds an unresolved node.
    opacity: Opacity,
}

impl Hash for SupportedNode
{
    /// Hash the node's identity: its former, cover and scope. The references
    /// and opacity are functions of them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<State>(
        &self,
        state: &mut State,
    ) where
        State: Hasher,
    {
        self.former.hash(state);
        self.cover.hash(state);
        self.scope.hash(state);
    }
}

impl SupportedNode
{
    /// The former, its own occurrence a rank in its scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn former(&self) -> &ContentNode
    {
        &self.former
    }

    /// The edges, one per child in child order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cover(&self) -> &[Thinning]
    {
        &self.cover
    }

    /// The node's minimal scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> Scope
    {
        self.scope
    }

    /// References outside every type former, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value_reads(&self) -> impl ExactSizeIterator<Item = &Reference>
    {
        self.value_reads.as_slice().iter()
    }

    /// References in type positions, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn type_reads(&self) -> impl ExactSizeIterator<Item = &Reference>
    {
        self.type_reads.as_slice().iter()
    }

    /// Whether the subterm resolves completely.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn opacity(&self) -> Opacity
    {
        self.opacity
    }

    /// The node's sort.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sort(&self) -> Sort
    {
        self.former.sort()
    }

    /// The unresolved leaf of `sort`: an id no arena resolves, opaque.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn unresolved(sort: Sort) -> Self
    {
        Self {
            former: ContentNode::Unresolved(sort),
            cover: Vec::new(),
            scope: Scope::default(),
            value_reads: Reads::default(),
            type_reads: Reads::default(),
            opacity: Opacity::Opaque,
        }
    }
}

/// A set of references, ascending and duplicate-free, shared between a node
/// and the ancestors that repeat it.
///
/// # Specification
/// - executable: none — a data declaration; [`Union::finish`] keeps the slice
///   strictly ascending.
///
/// # Adequacy
/// - hypothesis: L2 — an independent arena walk observes the union at every
///   root.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Reads(Option<Arc<[Reference]>>);

impl Reads
{
    /// The references, ascending.
    ///
    /// # Specification
    /// trivial.
    fn as_slice(&self) -> &[Reference]
    {
        self.0.as_deref().unwrap_or_default()
    }
}

/// A union of reference sets in progress: the one set every part so far
/// equals, until a part differs and the union is copied out.
///
/// # Specification
/// - executable: none — a data declaration; [`Union::add`] keeps `shared` the
///   union while `merged` is absent, and `merged` every reference added once it
///   is present.
///
/// # Adequacy
/// - hypothesis: L2 — the arena walk observes every root's union.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
#[derive(Default)]
struct Union<'part>
{
    /// The set every part added so far equals.
    shared: Option<&'part Arc<[Reference]>>,
    /// Every reference added, once two parts differ or a lone reference
    /// joined.
    merged: Option<Vec<Reference>>,
}

impl<'part> Union<'part>
{
    /// The union holding `own` alone, or nothing.
    ///
    /// # Specification
    /// trivial.
    fn of(own: Option<&Reference>) -> Self
    {
        Self {
            shared: None,
            merged: own.map(|reference| alloc::vec![reference.clone()]),
        }
    }

    /// Join `part`: shared while it equals the set held, copied out once
    /// it differs.
    ///
    /// # Specification
    /// - requires: `part` ascends strictly.
    /// - ensures: the union holds every reference it held and every one of
    ///   `part`; no reference is copied while every part equals the first.
    /// - panics: none.
    /// - executable: none — the union is observed through [`Union::finish`],
    ///   whose predicate checks the set it yields.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the arena walk observes every root's union.
    /// - witness: `tests::supports::carried_footprint_matches_reference_walk`
    fn add(
        &mut self,
        part: &'part Reads,
    )
    {
        let Some(ref held) = part.0
        else {
            return;
        };
        if let Some(ref mut merged) = self.merged {
            merged.extend(held.iter().cloned());
            return;
        }
        match self.shared {
            None => self.shared = Some(held),
            Some(first) if Arc::ptr_eq(first, held) || first == held => {},
            Some(first) => {
                let mut merged = Vec::with_capacity(first.len().saturating_add(held.len()));
                merged.extend(first.iter().cloned());
                merged.extend(held.iter().cloned());
                self.merged = Some(merged);
            },
        }
    }

    /// The set the union holds: the shared part itself, or the copied
    /// references sorted and deduplicated.
    ///
    /// # Specification
    /// - ensures: strictly ascending.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the arena walk observes every root's union.
    /// - witness: `tests::supports::carried_footprint_matches_reference_walk`
    #[spec(ensures: |ret| ret.as_slice().windows(2).all(|pair| pair.first() < pair.last()))]
    fn finish(self) -> Reads
    {
        match self.merged {
            Some(mut merged) => {
                merged.sort_unstable();
                merged.dedup();
                Reads(Some(Arc::from(merged)))
            },
            None => Reads(self.shared.cloned()),
        }
    }
}

/// The references and opacity of `former`, its `children` read through
/// `lookup`.
///
/// # Specification
/// - requires: `children` are the former's children in order, and `lookup`
///   yields every one of them; a child it does not yield contributes nothing.
/// - ensures: the former's own reference, in a type position exactly when the
///   former is a type; every child's type reads; every child's value reads,
///   promoted to type reads beneath a type former. Opaque exactly when the
///   former is unresolved or a child is opaque.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the independent arena walk distinguishes omitted reads
///   and false promotion through quotes, element types and signatures; L3 —
///   forged reference sets cannot be persisted, since a reader rebuilds them.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
/// - witness: `footprint::tests::type_support_holds_only_type_positions`
#[spec(ensures: |ret| (!matches!(former.sort(), Sort::ValueType | Sort::CompType) || ret.0.as_slice().is_empty())
    && former.children().iter().all(|(child, _)| lookup(child).is_none_or(|child|
        child.type_reads.as_slice().iter().all(|read| ret.1.as_slice().binary_search(read).is_ok())
        && child.value_reads.as_slice().iter().all(|read|
            if matches!(former.sort(), Sort::ValueType | Sort::CompType) { &ret.1 } else { &ret.0 }
                .as_slice().binary_search(read).is_ok())
        && (child.opacity == Opacity::Transparent || ret.2 == Opacity::Opaque))))]
fn reads_of<'table, Children, Lookup>(
    former: &ContentNode,
    children: Children,
    lookup: Lookup,
) -> (Reads, Reads, Opacity)
where
    Children: Iterator<Item = NodeIndex>,
    Lookup: Fn(NodeIndex) -> Option<&'table SupportedNode>,
{
    let mut opacity = if matches!(*former, ContentNode::Unresolved(_)) {
        Opacity::Opaque
    }
    else {
        Opacity::Transparent
    };
    let in_type = matches!(former.sort(), Sort::ValueType | Sort::CompType);
    let own = match former.reference() {
        Maybe::Present(reference) => Some(reference),
        Maybe::Absent(_) => None,
    };
    let (mut value_reads, mut type_reads) = if in_type {
        (Union::default(), Union::of(own))
    }
    else {
        (Union::of(own), Union::default())
    };
    for child in children {
        let Some(child) = lookup(child)
        else {
            continue;
        };
        if child.opacity == Opacity::Opaque {
            opacity = Opacity::Opaque;
        }
        type_reads.add(&child.type_reads);
        if in_type {
            type_reads.add(&child.value_reads);
        }
        else {
            value_reads.add(&child.value_reads);
        }
    }
    (value_reads.finish(), type_reads.finish(), opacity)
}

/// The hash-consed nodes of a table under construction.
///
/// # Specification
/// - executable: none — a data declaration; [`Interner::intern`] keeps one
///   entry per distinct former, cover and scope.
///
/// # Adequacy
/// - hypothesis: L3 — a subterm under unused binder interleavings is interned
///   once, and distinct wiring stays distinct.
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
#[derive(Default)]
struct Interner
{
    /// The interned nodes, children before parents.
    nodes: Vec<SupportedNode>,
    /// Each index of `nodes` beside the hash of its identity, built once the
    /// table outgrows [`LINEAR`].
    index: HashTable<(u64, NodeIndex)>,
    /// The fixed-seed state identities hash under.
    state: FixedState,
}

/// The table size up to which the interner searches its nodes in order
/// rather than hashing: most tables are an item's or a type's few nodes,
/// where comparing formers is cheaper than hashing them and allocating an
/// index.
const LINEAR: usize = 16;

impl Interner
{
    /// The index of the node `former`, `cover` and `scope` name, interning it
    /// on first sight with its references computed over the interned nodes
    /// it has as `children`.
    ///
    /// # Specification
    /// - requires: `children` are the former's children in order, every one
    ///   interned.
    /// - ensures: the index of the one node equal to the three in identity, of
    ///   the former's sort, the cover's arity and the scope; the table grows by
    ///   one exactly when none was interned.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same pair under two unused-binder interleavings
    ///   interns once, in a table below [`LINEAR`] and in one past it; altered
    ///   wiring interns twice.
    /// - witness: `content::tests::unused_binder_interleavings_share_one_node`
    #[spec(
        captures: [entry = self.nodes.len(), sort = former.sort(), arity = cover.len()],
        ensures: |ret| self.nodes.get(usize::from(ret)).is_some_and(|node|
                node.former.sort() == sort && node.cover.len() == arity && node.scope == scope)
            && (self.nodes.len() == entry || self.nodes.len() == entry.saturating_add(1)),
    )]
    fn intern<Children>(
        &mut self,
        former: ContentNode,
        cover: Vec<Thinning>,
        scope: Scope,
        children: Children,
    ) -> NodeIndex
    where
        Children: Iterator<Item = NodeIndex>,
    {
        let hash =
            (self.nodes.len() >= LINEAR).then(|| self.state.hash_one((&former, &cover, &scope)));
        if hash.is_some() && self.index.is_empty() {
            // The table has just outgrown the linear search: index it.
            for (position, held) in self.nodes.iter().enumerate() {
                let held_hash = self
                    .state
                    .hash_one((&held.former, &held.cover, &held.scope));
                let _entry = self.index.insert_unique(
                    held_hash,
                    (held_hash, NodeIndex::from(position)),
                    |&(stored, _)| stored,
                );
            }
        }
        let nodes = &self.nodes;
        let same = |held: &SupportedNode| {
            held.scope == scope && held.former == former && held.cover == cover
        };
        let found = match hash {
            None => nodes.iter().position(same).map(NodeIndex::from),
            Some(hash) => self
                .index
                .find(hash, |&(held_hash, index)| {
                    held_hash == hash && nodes.get(usize::from(index)).is_some_and(same)
                })
                .map(|&(_, index)| index),
        };
        if let Some(index) = found {
            return index;
        }
        let (value_reads, type_reads, opacity) =
            reads_of(&former, children, |child| nodes.get(usize::from(child)));
        let index = NodeIndex::from(self.nodes.len());
        self.nodes.push(SupportedNode {
            former,
            cover,
            scope,
            value_reads,
            type_reads,
            opacity,
        });
        if let Some(hash) = hash {
            let _entry = self
                .index
                .insert_unique(hash, (hash, index), |&(held_hash, _)| held_hash);
        }
        index
    }
}

/// Where a de Bruijn node landed in a factored table: the compact node it is
/// and its support in its own ambient scope.
///
/// # Specification
/// - executable: none — a data declaration; [`factor`] establishes that the
///   support's widths are the node's scope.
///
/// # Adequacy
/// - hypothesis: L3 — expanding a placement recovers the de Bruijn node.
/// - witness: `content::tests::covers_preserve_every_binding_former`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Placement
{
    /// The compact node.
    pub node: NodeIndex,
    /// The ambient indices it selects.
    pub support: Thinning,
}

/// A factored table and the placement of each de Bruijn node in it.
///
/// # Specification
/// - executable: none — a data declaration; [`factor`] establishes it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`factor`].
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
pub struct Factored
{
    /// The hash-consed nodes, children before parents.
    pub nodes: Vec<SupportedNode>,
    /// One placement per de Bruijn node, in its table's order.
    pub placements: Vec<Placement>,
}

/// How far a post-order walk has taken a de Bruijn node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mark
{
    /// Not reached.
    Unvisited,
    /// Reached, its children not yet all factored.
    Open,
    /// Factored.
    Closed,
}

/// A step of a post-order walk, an exit carrying what the walk keeps for it.
#[derive(Clone, Copy, Debug)]
enum Visit<Kept>
{
    /// Schedule the node's children.
    Enter(NodeIndex),
    /// Finish the node, its children finished.
    Exit(NodeIndex, Kept),
}

/// Factor the de Bruijn table `raw` into compact nodes with covers.
///
/// # Specification
/// - requires: nothing — a child out of range, or one that closes a cycle, is
///   factored as one unresolved leaf of the sort its node's first slot naming
///   it requires, so the table is opaque.
/// - ensures: one placement per entry of `raw`, its support the entry's free
///   indices in each zone, its node the entry's former over its own minimal
///   scope; nodes equal in former, cover and scope are one entry. Expanding a
///   placement recovers its entry up to sharing.
/// - provides: an iterative, stack-independent encoding.
/// - panics: none.
/// - intension: visits each entry once; one cover and one hash per entry.
///
/// # Adequacy
/// - hypothesis: L2 — reference support agrees with an independent arena walk;
///   L3 — relocation under unused binders, altered wiring and the de Bruijn
///   projection separate false sharing from failure to share; an unresolved id
///   stays opaque.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
/// - witness: `content::tests::covers_preserve_every_binding_former`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
#[spec(ensures: |ret| ret.placements.len() == raw.len()
    && ret.placements.iter().zip(raw).all(|(placed, node)|
        ret.nodes.get(usize::from(placed.node)).is_some_and(|compact|
            compact.scope == placed.support.scope() && compact.sort() == node.sort())))]
pub fn factor(raw: &[ContentNode]) -> Factored
{
    let mut interner = Interner::default();
    let mut placements = alloc::vec![Placement::default(); raw.len()];
    let mut marks = alloc::vec![Mark::Unvisited; raw.len()];
    let mut work = Vec::new();
    let empty = Thinning::empty();
    // The children of every open entry, one segment per entry, deepest last:
    // a segment is pushed on entry and popped once the entry is factored.
    let mut pending: Vec<(NodeIndex, Sort, Crossing)> = Vec::new();
    // Scratch reused across entries: each entry's stray leaves.
    let mut strays: BTreeMap<NodeIndex, NodeIndex> = BTreeMap::new();
    for start in 0 .. raw.len() {
        work.push(Visit::Enter(NodeIndex::from(start)));
        while let Some(visit) = work.pop() {
            match visit {
                Visit::Enter(index) => {
                    let (Some(mark), Some(node)) = (
                        marks.get_mut(usize::from(index)),
                        raw.get(usize::from(index)),
                    )
                    else {
                        continue;
                    };
                    if *mark != Mark::Unvisited {
                        continue;
                    }
                    *mark = Mark::Open;
                    let segment = pending.len();
                    pending.extend(node.children().crossed());
                    work.push(Visit::Exit(index, segment));
                    work.extend(
                        pending
                            .get(segment ..)
                            .unwrap_or_default()
                            .iter()
                            .rev()
                            .map(|&(child, ..)| Visit::Enter(child)),
                    );
                },
                Visit::Exit(index, segment) => {
                    let Some(node) = raw.get(usize::from(index))
                    else {
                        pending.truncate(segment);
                        continue;
                    };
                    let children = pending.get(segment ..).unwrap_or_default();
                    strays.clear();
                    for &(child, sort, _) in children {
                        if marks.get(usize::from(child)) != Some(&Mark::Closed)
                            && !strays.contains_key(&child)
                        {
                            let leaf = interner.intern(
                                ContentNode::Unresolved(sort),
                                Vec::new(),
                                Scope::default(),
                                core::iter::empty(),
                            );
                            let _first = strays.insert(child, leaf);
                        }
                    }
                    let support_of = |child: NodeIndex| match marks.get(usize::from(child)) {
                        Some(&Mark::Closed) => placements
                            .get(usize::from(child))
                            .map_or(&empty, |placed| &placed.support),
                        Some(&(Mark::Open | Mark::Unvisited)) | None => &empty,
                    };
                    let own = match node.occurrence() {
                        Maybe::Present(occurrence) => Some(occurrence),
                        Maybe::Absent(_) => None,
                    };
                    let cover = Cover::of(
                        own,
                        &children
                            .iter()
                            .map(|&(child, _, crossing)| (support_of(child), crossing)),
                    );
                    let (support, edges) = cover.into_parts();
                    let image = |child: NodeIndex| match strays.get(&child) {
                        Some(&leaf) => leaf,
                        None => placements
                            .get(usize::from(child))
                            .map_or(child, |placed| placed.node),
                    };
                    let mut former = map_children(node, &mut |child| image(child));
                    if let Some((zone, occurrence)) = own
                        && let Maybe::Present(rank) = support.rank(zone, occurrence)
                    {
                        former = former.relocated(rank);
                    }
                    let scope = support.scope();
                    let compact = interner.intern(
                        former,
                        edges,
                        scope,
                        children.iter().map(|&(child, ..)| image(child)),
                    );
                    if let Some(placed) = placements.get_mut(usize::from(index)) {
                        *placed = Placement {
                            node: compact,
                            support,
                        };
                    }
                    if let Some(mark) = marks.get_mut(usize::from(index)) {
                        *mark = Mark::Closed;
                    }
                    pending.truncate(segment);
                },
            }
        }
    }
    Factored {
        nodes: interner.nodes,
        placements,
    }
}

/// A table renumbered breadth-first from its roots, with the old-to-new map.
///
/// # Specification
/// - executable: none — a data declaration; [`number`] establishes it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`number`].
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
pub struct Numbered
{
    /// The reached nodes, numbered by discovery.
    pub nodes: Vec<SupportedNode>,
    /// The new index of each old index the walk reached.
    pub numbers: Vec<Option<NodeIndex>>,
}

/// Renumber the nodes of the table below `end` reachable from `roots`,
/// breadth-first, children left to right; `take` yields each old entry once.
///
/// # Specification
/// - requires: `take` yields the entry at each index of the table; every root
///   and child is an index of it.
/// - ensures: every reachable entry appears once, in discovery order, its cover
///   and scope unchanged and every child renumbered; `numbers` maps exactly the
///   reached old indices. An entry `take` cannot yield is listed as an
///   unresolved value, so the numbering stays dense.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a signature interleaved with a body renumbers to the
///   table its type encodes to on its own, covers and root support included.
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
#[spec(ensures: |ret| ret.numbers.len() == usize::from(end)
    && ret.numbers.iter().flatten().all(|index| usize::from(*index) < ret.nodes.len())
    && ret.numbers.iter().flatten().count() == ret.nodes.len())]
pub fn number<Roots, Take>(
    end: NodeIndex,
    roots: Roots,
    mut take: Take,
) -> Numbered
where
    Roots: IntoIterator<Item = NodeIndex>,
    Take: FnMut(NodeIndex) -> Option<SupportedNode>,
{
    let mut discovery = Discovery {
        numbers: alloc::vec![None; usize::from(end)],
        nodes: Vec::with_capacity(usize::from(end)),
    };
    for root in roots {
        let _number = discovery.discover(root, &mut take);
    }
    // The table is its own queue: entries are written as they are
    // discovered, and the walk renumbers each one's children in turn.
    let mut written = 0_usize;
    while let Some(node) = discovery.nodes.get_mut(written) {
        let pending = core::mem::replace(&mut node.former, ContentNode::Unresolved(Sort::Value));
        // `map_children` calls its image once per child, left to right, so
        // it discovers the children in the order the walk numbers them.
        let former = map_children(&pending, &mut |child| discovery.discover(child, &mut take));
        if let Some(node) = discovery.nodes.get_mut(written) {
            node.former = former;
        }
        written = written.saturating_add(1);
    }
    Numbered {
        nodes: discovery.nodes,
        numbers: discovery.numbers,
    }
}

/// A breadth-first numbering in progress.
///
/// # Specification
/// - executable: none — a data declaration; [`Discovery::discover`] keeps
///   `nodes` the numbered entries in number order.
///
/// # Adequacy
/// - hypothesis: L3 — as [`number`].
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
struct Discovery
{
    /// The new index of each old index numbered so far.
    numbers: Vec<Option<NodeIndex>>,
    /// The numbered entries, in number order; those past the walk's cursor
    /// still name their children by old index.
    nodes: Vec<SupportedNode>,
}

impl Discovery
{
    /// The new index of `old`, numbering it and writing the entry `take`
    /// yields for it on first sight.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the number `old` took when first discovered; a first
    ///   discovery takes the next number and appends its entry, an unresolved
    ///   value when `take` yields none. An index past the table is returned
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`number`]: a shared node keeps one number.
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(
        captures: [held = self.numbers.get(usize::from(old)).copied().flatten(), written = self.nodes.len()],
        ensures: |ret| match held {
            Some(number) => ret == number && self.nodes.len() == written,
            None => self.numbers.get(usize::from(old)).is_none_or(|slot| *slot == Some(ret))
                && self.nodes.len() <= written.saturating_add(1),
        },
    )]
    fn discover<Take>(
        &mut self,
        old: NodeIndex,
        take: &mut Take,
    ) -> NodeIndex
    where
        Take: FnMut(NodeIndex) -> Option<SupportedNode>,
    {
        match self.numbers.get_mut(usize::from(old)) {
            Some(&mut Some(number)) => number,
            Some(slot @ &mut None) => {
                let number = NodeIndex::from(self.nodes.len());
                *slot = Some(number);
                self.nodes
                    .push(take(old).unwrap_or_else(|| SupportedNode::unresolved(Sort::Value)));
                number
            },
            None => old,
        }
    }
}

/// The de Bruijn table of the node `root` of `nodes` whose support in the
/// ambient scope is `placement`, numbered by discovery, the root first.
///
/// # Specification
/// - requires: `nodes` is a supported table, as [`factor`] builds it or
///   [`assemble`] admits it, and `placement` has the root's widths.
/// - ensures: every own occurrence becomes the ambient index its rank selects,
///   and every child is placed by its edge and names an entry of the table; one
///   entry per distinct node and placement, so a node placed under two supports
///   expands twice. An ill-sorted input stays ill-sorted: the projection keeps
///   every former and does not re-check the sorts.
/// - fails: [`PlacementError::IndexOverflow`] when a binder raises an ambient
///   index past `u32`; [`PlacementError::OutOfScope`] for an edge or occurrence
///   past its node's support. No saturated index escapes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the same pair under two unused-binder interleavings and
///   every binding former of both zones expand to their original indices; a
///   placement at the index ceiling under a binder overflows.
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
/// - witness: `content::tests::covers_preserve_every_binding_former`
/// - witness: `content::tests::debruijn_projection_reports_index_overflow`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |table| table.iter().all(|node|
    node.children().iter().all(|(child, _)| table.get(usize::from(child)).is_some()))))]
pub fn expand(
    nodes: &[SupportedNode],
    root: NodeIndex,
    placement: &Thinning,
) -> Result<Vec<ContentNode>, PlacementError>
{
    let mut numbered: BTreeMap<(NodeIndex, Thinning), NodeIndex> = BTreeMap::new();
    let mut queue = VecDeque::new();
    let _root = numbered.insert((root, placement.clone()), NodeIndex::from(0_usize));
    queue.push_back((root, placement.clone()));
    let mut output = Vec::new();
    // One slot buffer for every node's children, refilled per node.
    let mut slots: Vec<(NodeIndex, NodeIndex, bool)> = Vec::new();
    while let Some((index, ambient)) = queue.pop_front() {
        let Some(node) = nodes.get(usize::from(index))
        else {
            output.push(ContentNode::Unresolved(Sort::Value));
            continue;
        };
        slots.clear();
        slots.reserve(node.cover.len());
        for ((child, _, crossing), edge) in node.former.children().crossed().zip(&node.cover) {
            let placed = ambient.place(edge, crossing)?;
            let next = NodeIndex::from(numbered.len());
            let number = *numbered.entry((child, placed)).or_insert_with_key(|key| {
                queue.push_back(key.clone());
                next
            });
            slots.push((child, number, false));
        }
        // Each child takes the expansion of the first unclaimed slot that
        // names it, so slots naming one node under different edges keep
        // their own placements in child order.
        let mut former = map_children(&node.former, &mut |child| match slots
            .iter_mut()
            .find(|slot| slot.0 == child && !slot.2)
        {
            Some(slot) => {
                slot.2 = true;
                slot.1
            },
            None => child,
        });
        if let Maybe::Present((zone, rank)) = former.occurrence() {
            let ambient_index = ambient.select(zone, rank)?;
            former = former.relocated(ambient_index);
        }
        output.push(former);
    }
    Ok(output)
}

/// A decoded node before its references are rebuilt.
///
/// # Specification
/// - executable: none — a data declaration; [`assemble`] validates it.
///
/// # Adequacy
/// - hypothesis: L3 — forged covers, scopes and duplicates are refused.
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeParts
{
    /// The compact former.
    pub former: ContentNode,
    /// The edges.
    pub cover: Vec<Thinning>,
    /// The scope.
    pub scope: Scope,
}

/// Why a decoded table is no supported table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TableFault
{
    /// A child is out of range or of the wrong sort.
    Child,
    /// A node is its own descendant.
    Cycle,
    /// A cover is not the exact minimal cover of its node.
    Cover(CoverError),
    /// Two entries are the same node.
    Duplicate,
}

/// Rebuild a decoded table, checking every cover and computing every node's
/// references.
///
/// # Specification
/// - requires: nothing — this is the reader's check of a table it did not
///   build.
/// - ensures: on success, the table with each node's references and opacity
///   rebuilt from its children, so no persisted reference set is trusted.
/// - fails: [`TableFault::Child`] for a child out of range or of the wrong
///   sort; [`TableFault::Cycle`] for a node that is its own descendant;
///   [`TableFault::Cover`] for a cover that is not the exact minimal cover of
///   its node over its children's scopes and crossings, its own occurrence
///   included; [`TableFault::Duplicate`] for two equal entries, which a
///   factored table never holds.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a factored table round-trips; a widened scope, an edge
///   past its node's scope, an unused slot, a cycle and a duplicated node are
///   each refused.
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[spec(
    captures: [count = parts.len()],
    ensures: |ret| ret.as_ref().map_or(true, |table| table.len() == count),
)]
pub fn assemble(parts: Vec<NodeParts>) -> Result<Vec<SupportedNode>, TableFault>
{
    for part in &parts {
        for (child, sort) in part.former.children().iter() {
            match parts.get(usize::from(child)) {
                Some(found) if found.former.sort() == sort => {},
                Some(_) | None => return Err(TableFault::Child),
            }
        }
    }
    let mut marks = alloc::vec![Mark::Unvisited; parts.len()];
    let mut order = Vec::with_capacity(parts.len());
    let mut work = Vec::new();
    for start in 0 .. parts.len() {
        work.push(Visit::Enter(NodeIndex::from(start)));
        while let Some(visit) = work.pop() {
            match visit {
                Visit::Enter(index) => {
                    let (Some(mark), Some(part)) = (
                        marks.get_mut(usize::from(index)),
                        parts.get(usize::from(index)),
                    )
                    else {
                        continue;
                    };
                    match *mark {
                        Mark::Closed => continue,
                        Mark::Open => return Err(TableFault::Cycle),
                        Mark::Unvisited => {},
                    }
                    *mark = Mark::Open;
                    work.push(Visit::Exit(index, ()));
                    for (child, _) in part.former.children().iter() {
                        match marks.get(usize::from(child)) {
                            Some(&Mark::Open) => return Err(TableFault::Cycle),
                            Some(&Mark::Unvisited) => work.push(Visit::Enter(child)),
                            Some(&Mark::Closed) | None => {},
                        }
                    }
                },
                Visit::Exit(index, ()) => {
                    if let Some(mark) = marks.get_mut(usize::from(index))
                        && *mark == Mark::Open
                    {
                        *mark = Mark::Closed;
                        order.push(index);
                    }
                },
            }
        }
    }
    let mut identities = HashSet::with_capacity(parts.len());
    for part in &parts {
        if !identities.insert((&part.former, &part.cover)) {
            return Err(TableFault::Duplicate);
        }
    }
    let mut parts: Vec<Option<NodeParts>> = parts.into_iter().map(Some).collect();
    let mut built: Vec<Option<SupportedNode>> = alloc::vec![None; parts.len()];
    for index in order {
        let Some(part) = parts.get_mut(usize::from(index)).and_then(Option::take)
        else {
            continue;
        };
        let own = match part.former.occurrence() {
            Maybe::Present(occurrence) => Some(occurrence),
            Maybe::Absent(_) => None,
        };
        // Post-order: every child is built before its parent, so its scope is
        // read from the built table.
        let children = part
            .former
            .children()
            .crossed()
            .map(|(child, _, crossing)| {
                (
                    built
                        .get(usize::from(child))
                        .and_then(Option::as_ref)
                        .map_or_else(Scope::default, |found| found.scope),
                    crossing,
                )
            });
        check_cover(part.scope, own, &part.cover, children).map_err(TableFault::Cover)?;
        let (value_reads, type_reads, opacity) = reads_of(
            &part.former,
            part.former.children().iter().map(|(child, _)| child),
            |child| built.get(usize::from(child)).and_then(Option::as_ref),
        );
        if let Some(slot) = built.get_mut(usize::from(index)) {
            *slot = Some(SupportedNode {
                former: part.former,
                cover: part.cover,
                scope: part.scope,
                value_reads,
                type_reads,
                opacity,
            });
        }
    }
    built
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(TableFault::Cycle)
}
