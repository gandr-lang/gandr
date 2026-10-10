//! The carrier: a finite trie from hierarchical names to bindings, held in one
//! arena.
//!
//! A namespace is a finite map from [`NamePath`] to a [`Binding`]. Namespaces
//! are implicit: `nat` names nothing on its own — it is exactly the bindings
//! whose path starts with `nat` — and `nat` and `nat.plus` are independent
//! bindings that coexist.
//!
//! # One arena, ids for edges
//!
//! The trie is a node per path prefix, every node in one [`Vec`] and every
//! edge an index into it, never a box: the type is not recursive, so no
//! derived trait, drop or walk over it recurs at a depth the author controls.
//! Each node keeps its children sorted by segment, so a subtree is reached by
//! one descent of binary searches and moved by one pass over its own nodes;
//! the rest of the namespace is never touched.
//!
//! Two invariants hold between operations: every node but the root is bound
//! or has a bound descendant, so a namespace has exactly one shape and two
//! namespaces with the same bindings compare equal node for node; and every
//! edge names a live node, freed nodes going to a vacancy list for reuse.
//!
//! # Union is pointwise
//!
//! Two bindings collide only when their whole paths are equal: the union walks
//! the later namespace's nodes beside the earlier one's, so subtrees merge
//! rather than shadow wholesale.

use alloc::vec::Vec;
use core::fmt;
use core::mem;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::namespace::path::NamePath;
use crate::namespace::path::Segment;
use crate::namespace::path::SegmentCount;

quenchant_shape::reason_enum! {
    /// Why a namespace answers no binding at a path.
    pub mod binding {
        /// Nothing is bound at the path.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The path is unbound, whatever is bound below it.
            Unbound,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an insert displaced no binding.
    pub mod displaced {
        /// The path was unbound before the insert.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The insert bound a fresh path.
            Fresh,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node has no incoming edge.
    mod edge {
        /// The node is the root.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The root is reached by no segment.
            Root,
        }
    }
}

/// One binding: the payload a path reaches, and the tag that travels with it.
///
/// Binding operations relocate and merge the opaque tag without interpreting
/// it. Equality and debugging use its corresponding traits. A consumer may
/// carry a source span, a provenance marker, or `()`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Binding<Data, Tag>
{
    /// The payload the path resolves to.
    pub data: Data,
    /// The metadata retained beside the payload.
    pub tag: Tag,
}

impl<Data, Tag> Binding<Data, Tag>
{
    /// The binding of `data` tagged `tag`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn new(
        data: Data,
        tag: Tag,
    ) -> Self
    {
        Self { data, tag }
    }
}

/// The two bindings a union found at one path.
///
/// `former` is the binding already present; `latter` arrives from the
/// namespace being merged in. Which survives belongs to the caller, so both
/// are handed over intact.
///
/// # Specification
/// - requires: the producer supplies the earlier and arriving bindings of one
///   collision.
/// - ensures: the two roles remain distinct until the resolver chooses a
///   survivor.
/// - provides: collision policy without a carrier-imposed winner.
/// - executable: none — the pair holds no namespace run establishing which
///   binding was earlier.
///
/// # Adequacy
/// - hypothesis: L3 — either side can survive a collision; non-unit tags travel
///   with the binding passed to the resolver.
/// - witness: `namespace::trie::tests::union_consults_the_resolver_on_a_collision`
/// - witness: `namespace::trie::tests::relocation_and_collision_keep_payloads_with_their_tags`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Collision<Data, Tag>
{
    /// The binding already present at the colliding path.
    pub former: Binding<Data, Tag>,
    /// The binding arriving at the colliding path.
    pub latter: Binding<Data, Tag>,
}

/// Whether a namespace holds any binding.
///
/// The emptiness check is a constructor of the modifier language, so its
/// answer is a named value.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Emptiness(pub bool);

impl Emptiness
{
    /// The namespace holds no binding.
    pub const EMPTY: Self = Self(true);
    /// The namespace holds at least one binding.
    pub const OCCUPIED: Self = Self(false);
}

/// A number of bindings.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BindingCount(usize);

impl From<usize> for BindingCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<BindingCount> for usize
{
    /// The number `count` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: BindingCount) -> Self
    {
        count.0
    }
}

/// A node's position in its trie's arena.
///
/// # Specification
/// - requires: the owning arena accompanies an index.
/// - ensures: the value names a position only in that arena; zero is its root.
/// - provides: non-recursive edges, not globally authenticated node identities.
/// - executable: none — an index alone does not hold its arena or live-node
///   set.
///
/// # Adequacy
/// - hypothesis: L3 — moved and reused slots retain the same public map; L2 — a
///   deep chain uses an arena rather than recursive ownership.
/// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
/// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct NodeId(usize);

impl NodeId
{
    /// The root, at the arena's first position in every trie.
    const ROOT: Self = Self(0);
}

/// One edge: the segment that reaches a child, and the child.
///
/// # Specification
/// - requires: the owning arena accompanies the edge.
/// - ensures: its segment reaches its node in that arena.
/// - provides: a labelled child reference.
/// - executable: none — a detached edge holds no arena establishing target
///   liveness.
///
/// # Adequacy
/// - hypothesis: L3 — nested paths, sibling preservation and slot reuse retain
///   exact reachable bindings.
/// - witness: `namespace::trie::tests::a_path_and_its_extension_are_independent_bindings`
/// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
#[derive(Clone, Debug)]
struct Child
{
    /// The segment the edge spells.
    segment: Segment,
    /// The child it reaches.
    node: NodeId,
}

/// One arena node: the binding at its path, and its children in ascending
/// segment order.
///
/// # Specification
/// - requires: child targets belong to the owning trie.
/// - ensures: children have distinct segments in ascending order; the optional
///   binding is independent of descendants.
/// - provides: one node of an ordered finite map.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; descent predicates check edges at operation boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — a path and its extension coexist, and out-of-order inputs
///   iterate in path order.
/// - witness: `namespace::trie::tests::a_path_and_its_extension_are_independent_bindings`
/// - witness: `namespace::trie::tests::borrowing_a_namespace_iterates_every_binding_in_order`
#[derive(Clone, Debug)]
struct Node<Data, Tag>
{
    /// The binding at this node's path.
    binding: Maybe<Binding<Data, Tag>, binding::Absent>,
    /// The edges to the node's children, sorted by segment.
    children: Vec<Child>,
}

impl<Data, Tag> Node<Data, Tag>
{
    /// A node with no binding and no children.
    ///
    /// # Specification
    /// trivial.
    const fn vacant() -> Self
    {
        Self {
            binding: Maybe::Absent(binding::Absent::Unbound),
            children: Vec::new(),
        }
    }
}

/// A namespace: the finite trie from hierarchical names to bindings.
///
/// # Specification
/// - requires: externally observed states are completed operation boundaries.
/// - ensures: the live root remains, edges target live nodes, freed slots are
///   vacant, and the cached count equals bound nodes; non-root live nodes lead
///   to a binding.
/// - provides: a finite map independent of arena layout, with iterative walks.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; operation predicates check counts, edges and allocation
///   transitions.
///
/// # Adequacy
/// - hypothesis: L3 — inserts, moves, refused merges and slot reuse retain
///   exact maps; L2 — every walk handles the fixed deep-chain witness
///   iteratively.
/// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
/// - witness: `namespace::trie::tests::a_declined_collision_keeps_the_binding_it_found`
/// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
#[derive(Clone)]
pub struct Trie<Data, Tag>
{
    /// The nodes; the root is the first.
    nodes: Vec<Node<Data, Tag>>,
    /// Freed positions, reused before the arena grows.
    vacant: Vec<NodeId>,
    /// The number of bound nodes.
    count: BindingCount,
}

impl<Data, Tag> Default for Trie<Data, Tag>
{
    /// The namespace with no bindings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::empty()
    }
}

impl<Data, Tag> Trie<Data, Tag>
{
    /// The namespace with no bindings.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a single vacant root, no free slots and no bindings.
    /// - provides: the empty carrier from which mutation starts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty namespace and a one-binding namespace, each
    ///   asserted as the exact emptiness.
    /// - witness: `namespace::trie::tests::the_empty_namespace_is_empty`
    #[spec(
        ensures: |ret| {
            ret.nodes.len() == 1
                && ret.vacant.is_empty()
                && ret.count.0 == 0
                && ret.nodes.first().is_some_and(|root| {
                    matches!(root.binding, Maybe::Absent(_)) && root.children.is_empty()
                })
        },
    )]
    #[inline]
    #[must_use]
    pub fn empty() -> Self
    {
        let nodes = Vec::from([Node::vacant()]);
        Self {
            nodes,
            vacant: Vec::new(),
            count: BindingCount(0_usize),
        }
    }

    /// Bind `path` to `binding`, returning the binding it displaced.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `path` is bound to `binding`; a repeat insert hands back the
    ///   binding it replaced, a fresh one reports the path fresh; no
    ///   [`Collision`] is reported, because an insert is not a union.
    /// - provides: the primitive every namespace is built from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh path and a repeated path, each asserted as
    ///   the exact answer and the exact listing after.
    /// - witness: `namespace::trie::tests::inserting_returns_the_binding_it_displaced`
    #[spec(
        captures: before = (self.count.0, matches!(self.get(path), Maybe::Present(_))),
        ensures: |ret| {
            matches!(self.get(path), Maybe::Present(_))
                && matches!(ret, Maybe::Present(_)) == before.1
                && self.count.0 == before.0.saturating_add(usize::from(!before.1))
        },
    )]
    #[inline]
    pub fn insert(
        &mut self,
        path: &NamePath,
        binding: Binding<Data, Tag>,
    ) -> Maybe<Binding<Data, Tag>, displaced::Absent>
    {
        let target = self.reach(path.segments());
        let Some(node) = self.nodes.get_mut(target.0)
        else {
            return Maybe::Absent(displaced::Absent::Fresh);
        };
        match mem::replace(&mut node.binding, Maybe::Present(binding)) {
            | Maybe::Present(former) => Maybe::Present(former),
            | Maybe::Absent(_) => {
                self.count.0 = self.count.0.saturating_add(1_usize);
                Maybe::Absent(displaced::Absent::Fresh)
            },
        }
    }

    /// The binding at `path`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the lookup is exact on the whole path: a path bound only
    ///   below it answers nothing, because a namespace is not an object a path
    ///   reaches.
    /// - provides: resolution, and the reason `nat` and `nat.plus` are
    ///   independent bindings.
    /// - fails: never; an unbound path is an absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path bound at itself and a path bound only below
    ///   it, each asserted as the exact answer.
    /// - witness: `namespace::trie::tests::a_path_bound_only_below_it_resolves_to_nothing`
    /// - witness: `namespace::trie::tests::a_path_and_its_extension_are_independent_bindings`
    #[spec(
        ensures: |ret| {
            let expected = path
                .segments()
                .iter()
                .try_fold(NodeId::ROOT, |parent, segment| {
                    let node = self.nodes.get(parent.0)?;
                    let position = node
                        .children
                        .binary_search_by(|edge| edge.segment.cmp(segment))
                        .ok()?;
                    node.children.get(position).map(|edge| edge.node)
                })
                .and_then(|target| self.nodes.get(target.0))
                .and_then(|node| match node.binding {
                    | Maybe::Present(ref binding) => Some(binding),
                    | Maybe::Absent(_) => None,
                });
            match (ret, expected) {
                | (Maybe::Present(actual), Some(expected)) => {
                    core::ptr::eq(&raw const *actual, &raw const *expected)
                },
                | (Maybe::Absent(_), None) => true,
                | (Maybe::Present(_), None) | (Maybe::Absent(_), Some(_)) => false,
            }
        },
    )]
    #[inline]
    pub fn get(
        &self,
        path: &NamePath,
    ) -> Maybe<&Binding<Data, Tag>, binding::Absent>
    {
        let mut current = NodeId::ROOT;
        for segment in path.segments() {
            match self.child(current, segment) {
                | Maybe::Present(child) => current = child,
                | Maybe::Absent(_) => return Maybe::Absent(binding::Absent::Unbound),
            }
        }
        match self.nodes.get(current.0) {
            | Some(&Node {
                binding: Maybe::Present(ref binding),
                ..
            }) => Maybe::Present(binding),
            | Some(_) | None => Maybe::Absent(binding::Absent::Unbound),
        }
    }

    /// The binding at the longest prefix of `path` reached by bound prefixes
    /// only, with that prefix's depth.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present with depth `n` and binding `b` exactly when the first
    ///   `n` segments of `path` are bound to `b`, every shorter non-empty
    ///   prefix is bound, and either `n` is the whole path or the next prefix
    ///   is unbound; absent when `path` is the root or its first segment is
    ///   unbound. The walk stops at the first unbound prefix, so a binding
    ///   beyond a gap is not reached.
    /// - provides: the one descent a governed resolution reads.
    /// - fails: never; an unbound first segment is an absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a whole path bound, an absent member under a
    ///   governing namespace at depths one and two, a value component's field
    ///   and an unbound root, each asserted as the exact resolution the
    ///   outermost scope builds on it.
    /// - witness: `recognition::recognition::a_path_is_governed_by_its_deepest_resolved_prefix`
    /// - witness: `namespace::trie::tests::a_bound_root_does_not_bridge_a_gap_in_governed_resolution`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present((depth, _)) => {
                usize::from(depth) > 0
                    && usize::from(depth) <= path.segments().len()
                    && self.count.0 > 0
            },
            | Maybe::Absent(_) => path.segments().first().is_none_or(|segment| {
                match self.child(NodeId::ROOT, segment) {
                    | Maybe::Present(node) => self
                        .nodes
                        .get(node.0)
                        .is_none_or(|node| matches!(node.binding, Maybe::Absent(_))),
                    | Maybe::Absent(_) => true,
                }
            }),
        },
    )]
    #[inline]
    pub fn resolved_prefix(
        &self,
        path: &NamePath,
    ) -> Maybe<(SegmentCount, &Binding<Data, Tag>), binding::Absent>
    {
        let mut resolved = Maybe::Absent(binding::Absent::Unbound);
        let mut current = NodeId::ROOT;
        let mut depth = 0_usize;
        for segment in path.segments() {
            let Maybe::Present(child) = self.child(current, segment)
            else {
                return resolved;
            };
            let Some(&Node {
                binding: Maybe::Present(ref binding),
                ..
            }) = self.nodes.get(child.0)
            else {
                return resolved;
            };
            depth = depth.saturating_add(1_usize);
            resolved = Maybe::Present((SegmentCount::from(depth), binding));
            current = child;
        }
        resolved
    }

    /// The first binding in path order at `prefix` or below it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the binding at `prefix` when it is bound; otherwise the
    ///   binding of least path among those extending `prefix`; absent when
    ///   nothing at or below `prefix` is bound.
    /// - provides: the binding a declaration taking over `prefix` displaces,
    ///   seen even when only members below it are bound.
    /// - fails: never; an empty subtree is an absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration over a seeded namespace, over a fresh
    ///   name and over a source declaration, each asserted as the exact
    ///   shadowing record.
    /// - witness: `recognition::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
    /// - witness: `recognition::recognition::redeclaring_a_source_name_is_not_a_shadow_event`
    /// - witness: `namespace::trie::tests::first_binding_prefers_a_bound_prefix_then_its_least_descendant`
    #[spec(
        ensures: |ret| match self.get(prefix) {
            | Maybe::Present(expected) => {
                matches!(ret, Maybe::Present(actual) if core::ptr::eq(&raw const *actual, &raw const *expected))
            },
            | Maybe::Absent(_) => self.count.0 > 0 || matches!(ret, Maybe::Absent(_)),
        },
    )]
    #[inline]
    pub fn first_at_or_below(
        &self,
        prefix: &NamePath,
    ) -> Maybe<&Binding<Data, Tag>, binding::Absent>
    {
        let mut current = NodeId::ROOT;
        for segment in prefix.segments() {
            match self.child(current, segment) {
                | Maybe::Present(child) => current = child,
                | Maybe::Absent(_) => return Maybe::Absent(binding::Absent::Unbound),
            }
        }
        let mut stack = Vec::new();
        stack.push(current);
        while let Some(visited) = stack.pop() {
            let Some(node) = self.nodes.get(visited.0)
            else {
                continue;
            };
            if let Maybe::Present(ref binding) = node.binding {
                return Maybe::Present(binding);
            }
            stack.extend(node.children.iter().rev().map(|edge| edge.node));
        }
        Maybe::Absent(binding::Absent::Unbound)
    }

    /// Every binding, in ascending path order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frontier starts at the root, with an empty path and this
    ///   trie borrowed.
    /// - provides: the initial state of the ordered binding walk.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an out-of-order input yields its exact ordered
    ///   bindings.
    /// - witness: `namespace::trie::tests::borrowing_a_namespace_iterates_every_binding_in_order`
    #[spec(
        ensures: |ret| {
            core::ptr::eq(&raw const *ret.trie, &raw const *self)
                && ret.path.is_empty()
                && ret.stack.len() == 1
                && ret.stack.first().is_some_and(|visit| {
                    visit.node == NodeId::ROOT
                        && visit.depth == 0
                        && matches!(visit.segment, Maybe::Absent(edge::Absent::Root))
                })
        },
    )]
    #[inline]
    #[must_use]
    pub fn iter(&self) -> Bindings<'_, Data, Tag>
    {
        let stack = Vec::from([Visit {
            node: NodeId::ROOT,
            depth: 0_usize,
            segment: Maybe::Absent(edge::Absent::Root),
        }]);
        Bindings {
            trie: self,
            stack,
            path: Vec::new(),
        }
    }

    /// The number of bindings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn binding_count(&self) -> BindingCount
    {
        self.count
    }

    /// Whether the namespace holds no binding: the check the modifier
    /// language's `all` performs on.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: EMPTY exactly when the cached binding census is zero.
    /// - provides: the modifier emptiness observation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty carrier and a carrier holding one binding.
    /// - witness: `namespace::trie::tests::the_empty_namespace_is_empty`
    #[spec(
        ensures: |ret| ret.0 == (self.count.0 == 0),
    )]
    #[inline]
    #[must_use]
    pub const fn emptiness(&self) -> Emptiness
    {
        Emptiness(self.count.0 == 0_usize)
    }

    /// Remove the subtree at `prefix` and return it, rebased to the root.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned namespace holds exactly the bindings whose path
    ///   extended `prefix`, each at its remainder after `prefix`; this
    ///   namespace keeps exactly the rest. Detaching at the root takes
    ///   everything; detaching an absent prefix takes nothing.
    /// - provides: the source half of a renaming and the working namespace of
    ///   `in`.
    /// - fails: never.
    /// - panics: none.
    /// - intension: the descent and the moved subtree's own nodes, nothing else
    ///   of this namespace.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the root, an absent prefix and a prefix with bound
    ///   siblings, each asserted as the exact two listings; L2 — a chain of one
    ///   hundred thousand segments detached inside a small stack.
    /// - witness: `namespace::trie::tests::detaching_at_the_root_takes_everything`
    /// - witness: `namespace::trie::tests::detaching_rebases_and_leaves_the_rest`
    /// - witness: `namespace::trie::tests::detaching_an_absent_prefix_yields_the_empty_namespace`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        captures: before = self.count.0,
        ensures: |ret| {
            self.count.0 <= before
                && ret.count.0 == before.saturating_sub(self.count.0)
                && (!prefix.segments().is_empty() || self.count.0 == 0)
        },
    )]
    #[inline]
    #[must_use]
    pub fn detach_subtree(
        &mut self,
        prefix: &NamePath,
    ) -> Self
    {
        if prefix.segments().is_empty() {
            return mem::take(self);
        }
        let mut chain = Vec::with_capacity(prefix.segments().len().saturating_add(1_usize));
        chain.push(NodeId::ROOT);
        let mut current = NodeId::ROOT;
        for segment in prefix.segments() {
            match self.child(current, segment) {
                | Maybe::Present(child) => current = child,
                | Maybe::Absent(_) => return Self::empty(),
            }
            chain.push(current);
        }
        let _target = chain.pop();
        if let (Some(&parent), Some(segment)) = (chain.last(), prefix.segments().last()) {
            self.unlink(parent, segment);
        }
        let mut detached = Self::empty();
        detached.transplant(self, current, NodeId::ROOT);
        self.prune(&chain, prefix);
        detached
    }

    /// Graft `subtree` at `prefix`, dropping whatever was there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every binding under `prefix` is gone and each binding of
    ///   `subtree` is bound at its path prefixed by `prefix`; grafting at the
    ///   root replaces this namespace with `subtree`.
    /// - provides: the target half of a renaming, and the way `in` puts a
    ///   modified subtree back.
    /// - fails: never.
    /// - panics: none.
    /// - intension: the descent, the dropped subtree and the grafted one,
    ///   nothing else of this namespace.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the root, an occupied target and a target beside a
    ///   bound sibling, each asserted as the exact listing; L2 — a chain of one
    ///   hundred thousand segments grafted inside a small stack.
    /// - witness: `namespace::trie::tests::grafting_at_the_root_replaces_everything`
    /// - witness: `namespace::trie::tests::grafting_drops_whatever_was_at_the_target`
    /// - witness: `namespace::trie::tests::grafting_keeps_bindings_outside_the_target`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        captures: before = (self.count.0, subtree.count.0),
        ensures: self.count.0 >= before.1
            && self.count.0 <= before.0.saturating_add(before.1)
            && (!prefix.segments().is_empty() || self.count.0 == before.1),
    )]
    #[inline]
    pub fn graft_subtree(
        &mut self,
        prefix: &NamePath,
        subtree: Self,
    )
    {
        if prefix.segments().is_empty() {
            *self = subtree;
            return;
        }
        let mut subtree = subtree;
        let mut chain = self.reach_chain(prefix.segments());
        let Some(&target) = chain.last()
        else {
            return;
        };
        self.clear(target);
        self.transplant(&mut subtree, NodeId::ROOT, target);
        let _target = chain.pop();
        if let Some(&Node {
            binding: Maybe::Absent(_),
            ref children,
        }) = self.nodes.get(target.0)
            && children.is_empty()
        {
            if let (Some(&parent), Some(segment)) = (chain.last(), prefix.segments().last()) {
                self.unlink(parent, segment);
            }
            self.free(target);
            self.prune(&chain, prefix);
        }
    }

    /// This namespace with every path moved under `prefix`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each binding is bound at its path prefixed by `prefix`, and
    ///   nothing else is bound.
    /// - provides: the relocation a section's export undergoes at close.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two bindings at different depths, asserted as the
    ///   exact listing.
    /// - witness: `namespace::trie::tests::prefixing_moves_every_path`
    #[spec(
        captures: before = self.count.0,
        ensures: |ret| ret.count.0 == before,
    )]
    #[inline]
    #[must_use]
    pub fn into_prefixed(
        self,
        prefix: &NamePath,
    ) -> Self
    {
        let mut prefixed = Self::empty();
        prefixed.graft_subtree(prefix, self);
        prefixed
    }

    /// Merge `later` into this namespace, asking `resolve` to settle each
    /// collision.
    ///
    /// # Specification
    /// - requires: `resolve` returns the binding that survives at the path it
    ///   is handed; the carrier imposes no default.
    /// - ensures: the merge is pointwise on whole paths, so two bindings
    ///   collide only when their paths are equal and no namespace shadows
    ///   another wholesale; collisions are handed over in ascending path order.
    /// - provides: the union of the modifier language and of a scope's imports.
    /// - fails: propagates `resolve`'s failure unchanged. The merge is not
    ///   atomic — every binding of `later` ordered before the refused path
    ///   stays merged — but it is never destructive: the binding this namespace
    ///   held at the refused path survives.
    /// - panics: none.
    ///
    /// # Errors
    /// The failure `resolve` returns on the first collision it declines.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — disjoint namespaces, one collision settled each way,
    ///   two collisions inserted out of order, a declining resolver and a
    ///   declining resolver reached after a merged sibling, each asserted as
    ///   the exact listing, collision order or failure; L2 — a chain of one
    ///   hundred thousand segments merged inside a small stack.
    /// - witness: `namespace::trie::tests::union_of_disjoint_namespaces_merges_pointwise`
    /// - witness: `namespace::trie::tests::union_consults_the_resolver_on_a_collision`
    /// - witness: `namespace::trie::tests::union_reports_collisions_in_path_order`
    /// - witness: `namespace::trie::tests::union_propagates_a_declining_resolver`
    /// - witness: `namespace::trie::tests::a_declined_collision_keeps_the_binding_it_found`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        captures: before = (self.count.0, later.count.0),
        ensures: |ret| {
            self.count.0 >= before.0
                && self.count.0 <= before.0.saturating_add(before.1)
                && (ret.is_err() || self.count.0 >= before.1)
        },
    )]
    #[inline]
    pub fn union_resolving<Resolve, Failure>(
        &mut self,
        later: Self,
        resolve: &mut Resolve,
    ) -> Result<(), Failure>
    where
        Data: Clone,
        Tag: Clone,
        Resolve: FnMut(&NamePath, Collision<Data, Tag>) -> Result<Binding<Data, Tag>, Failure>,
    {
        let mut later = later;
        let mut chain = Vec::new();
        chain.push(NodeId::ROOT);
        let mut stack: Vec<Merge> = Vec::new();
        let root = later.take(NodeId::ROOT);
        self.merge_binding(&chain, root.binding, resolve)?;
        push_merges(
            &mut stack,
            root.children,
            NodeId::ROOT,
            SegmentCount::from(1_usize),
        );
        while let Some(frame) = stack.pop() {
            chain.truncate(usize::from(frame.depth));
            let node = self.child_or_new(frame.parent, frame.segment);
            chain.push(node);
            let arriving = later.take(frame.later);
            self.merge_binding(&chain, arriving.binding, resolve)?;
            push_merges(
                &mut stack,
                arriving.children,
                node,
                SegmentCount::from(usize::from(frame.depth).saturating_add(1_usize)),
            );
        }
        Ok(())
    }

    /// Bind `arriving` at the node ending `chain`, consulting `resolve` on a
    /// collision.
    ///
    /// # Specification
    /// - requires: `chain` runs from the root to a live node, each a child of
    ///   the one before.
    /// - ensures: an absent arrival changes nothing; an arrival at an unbound
    ///   node binds it; an arrival at a bound node binds what `resolve` returns
    ///   for the node's path and the two bindings.
    /// - provides: one step of [`Self::union_resolving`].
    /// - fails: propagates `resolve`'s failure, leaving the node's binding as
    ///   it was.
    /// - panics: none.
    ///
    /// # Errors
    /// The failure `resolve` returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh and colliding arrivals, including refusal after
    ///   a merged sibling, retain the exact surviving bindings.
    /// - witness: `namespace::trie::tests::union_of_disjoint_namespaces_merges_pointwise`
    /// - witness: `namespace::trie::tests::union_consults_the_resolver_on_a_collision`
    /// - witness: `namespace::trie::tests::a_declined_collision_keeps_the_binding_it_found`
    #[spec(
        requires: chain.first() == Some(&NodeId::ROOT)
            && chain.last().is_some_and(|node| node.0 < self.nodes.len()),
        captures: before = (
            self.count.0,
            matches!(arriving, Maybe::Present(_)),
            chain
                .last()
                .and_then(|node| self.nodes.get(node.0))
                .is_some_and(|node| matches!(node.binding, Maybe::Present(_))),
        ),
        ensures: |ret| {
            self.count.0
                == before
                    .0
                    .saturating_add(usize::from(ret.is_ok() && before.1 && !before.2))
                && (ret.is_err()
                    || !before.1
                    || chain
                        .last()
                        .and_then(|node| self.nodes.get(node.0))
                        .is_some_and(|node| matches!(node.binding, Maybe::Present(_))))
        },
    )]
    fn merge_binding<Resolve, Failure>(
        &mut self,
        chain: &[NodeId],
        arriving: Maybe<Binding<Data, Tag>, binding::Absent>,
        resolve: &mut Resolve,
    ) -> Result<(), Failure>
    where
        Data: Clone,
        Tag: Clone,
        Resolve: FnMut(&NamePath, Collision<Data, Tag>) -> Result<Binding<Data, Tag>, Failure>,
    {
        let Maybe::Present(latter) = arriving
        else {
            return Ok(());
        };
        let Some(&target) = chain.last()
        else {
            return Ok(());
        };
        let former = match self.nodes.get(target.0) {
            | Some(&Node {
                binding: Maybe::Present(ref former),
                ..
            }) => Maybe::Present(former.clone()),
            | Some(_) | None => Maybe::Absent(binding::Absent::Unbound),
        };
        let mut survivor = latter;
        if let Maybe::Present(former) = former {
            let path = self.path_of(chain);
            let resolved = resolve(&path, Collision {
                former,
                latter: survivor,
            })?;
            survivor = resolved;
        }
        else {
            self.count.0 = self.count.0.saturating_add(1_usize);
        }
        if let Some(node) = self.nodes.get_mut(target.0) {
            node.binding = Maybe::Present(survivor);
        }
        Ok(())
    }

    /// The path `chain` spells.
    ///
    /// # Specification
    /// - requires: `chain` runs from the root, each node a child of the one
    ///   before.
    /// - ensures: the segments of the edges between consecutive nodes, in
    ///   order.
    /// - provides: the path a collision is reported at, built only when one
    ///   occurs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — collisions inserted out of order are reported at
    ///   their exact whole paths in lexicographic order.
    /// - witness: `namespace::trie::tests::union_reports_collisions_in_path_order`
    /// - witness: `namespace::namespace::a_nested_shadow_reports_the_accumulated_prefix`
    #[spec(
        requires: chain.first() == Some(&NodeId::ROOT),
        ensures: |ret| {
            ret.segments().len() == chain.len().saturating_sub(1)
                && chain
                    .iter()
                    .zip(chain.iter().skip(1))
                    .zip(ret.segments())
                    .all(|((parent, child), segment)| {
                        self.nodes.get(parent.0).is_some_and(|node| {
                            node.children
                                .iter()
                                .any(|edge| edge.node == *child && edge.segment == *segment)
                        })
                    })
        },
    )]
    fn path_of(
        &self,
        chain: &[NodeId],
    ) -> NamePath
    {
        let mut segments = Vec::with_capacity(chain.len().saturating_sub(1_usize));
        for pair in chain.windows(2_usize) {
            let (Some(&parent), Some(&child)) = (pair.first(), pair.get(1_usize))
            else {
                continue;
            };
            let edge = self.nodes.get(parent.0).and_then(|node| {
                node.children
                    .iter()
                    .find(|candidate| candidate.node == child)
            });
            if let Some(edge) = edge {
                segments.push(edge.segment.clone());
            }
        }
        NamePath::from(segments)
    }

    /// The child of `parent` reached by `segment`.
    ///
    /// # Specification
    /// - requires: the parent belongs to this arena when present.
    /// - ensures: returns the edge selected by the segment, or absence when the
    ///   parent or edge is missing.
    /// - provides: one binary-search step of a path descent.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact bound paths and absent prefixes traverse
    ///   present and missing edges; whole-path queries do not accept
    ///   descendants.
    /// - witness: `namespace::trie::tests::a_path_bound_only_below_it_resolves_to_nothing`
    /// - witness: `namespace::trie::tests::a_path_and_its_extension_are_independent_bindings`
    #[spec(
        ensures: |ret| {
            ret == self
                .nodes
                .get(parent.0)
                .and_then(|node| {
                    let position = node
                        .children
                        .binary_search_by(|edge| edge.segment.cmp(segment))
                        .ok()?;
                    node.children.get(position)
                })
                .map_or(Maybe::Absent(binding::Absent::Unbound), |edge| {
                    Maybe::Present(edge.node)
                })
        },
    )]
    fn child(
        &self,
        parent: NodeId,
        segment: &Segment,
    ) -> Maybe<NodeId, binding::Absent>
    {
        let Some(node) = self.nodes.get(parent.0)
        else {
            return Maybe::Absent(binding::Absent::Unbound);
        };
        match node
            .children
            .binary_search_by(|candidate| candidate.segment.cmp(segment))
        {
            | Ok(found) => node
                .children
                .get(found)
                .map_or(Maybe::Absent(binding::Absent::Unbound), |edge| {
                    Maybe::Present(edge.node)
                }),
            | Err(_) => Maybe::Absent(binding::Absent::Unbound),
        }
    }

    /// The child of `parent` reached by `segment`, created when absent.
    ///
    /// # Specification
    /// - requires: `parent` is live.
    /// - ensures: the child reached by `segment`; a new child is a vacant node
    ///   inserted at its sorted position.
    /// - provides: the descent every binding operation shares.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated insertion and a detach followed by new paths
    ///   cover existing edges, new edges and vacant-slot reuse.
    /// - witness: `namespace::trie::tests::inserting_returns_the_binding_it_displaced`
    /// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
    #[spec(
        requires: parent.0 < self.nodes.len(),
        captures: before = (
            self.count.0,
            self.nodes.len(),
            self.vacant.len(),
            self.nodes.get(parent.0).map(|node| {
                node.children
                    .binary_search_by(|edge| edge.segment.cmp(&segment))
            }),
        ),
        ensures: |ret| {
            ret.0 < self.nodes.len()
                && self.count.0 == before.0
                && match before.3 {
                    | Some(Ok(position)) => {
                        self.nodes.len() == before.1
                            && self.vacant.len() == before.2
                            && self
                                .nodes
                                .get(parent.0)
                                .and_then(|node| node.children.get(position))
                                .is_some_and(|edge| edge.node == ret)
                    },
                    | Some(Err(position)) => {
                        self.nodes.len() == before.1.saturating_add(usize::from(before.2 == 0))
                            && self.vacant.len() == before.2.saturating_sub(1)
                            && self
                                .nodes
                                .get(parent.0)
                                .and_then(|node| node.children.get(position))
                                .is_some_and(|edge| edge.node == ret)
                    },
                    | None => false,
                }
        },
    )]
    fn child_or_new(
        &mut self,
        parent: NodeId,
        segment: Segment,
    ) -> NodeId
    {
        let position = match self.nodes.get(parent.0).map(|node| {
            node.children
                .binary_search_by(|candidate| candidate.segment.cmp(&segment))
        }) {
            | Some(Ok(found)) => {
                return self
                    .nodes
                    .get(parent.0)
                    .and_then(|node| node.children.get(found))
                    .map_or(parent, |edge| edge.node);
            },
            | Some(Err(position)) => position,
            | None => return parent,
        };
        let child = self.allocate();
        if let Some(node) = self.nodes.get_mut(parent.0) {
            node.children.insert(position, Child {
                segment,
                node: child,
            });
        }
        child
    }

    /// The node at `segments` below the root, created along the way.
    ///
    /// # Specification
    /// - requires: the arena has its live root.
    /// - ensures: returns the node reached by all segments, creating missing
    ///   edges without binding nodes.
    /// - provides: the insertion descent.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, repeated and nested paths resolve
    ///   independently.
    /// - witness: `namespace::trie::tests::inserting_returns_the_binding_it_displaced`
    /// - witness: `namespace::trie::tests::a_path_and_its_extension_are_independent_bindings`
    #[spec(
        requires: !self.nodes.is_empty(),
        captures: before = self.count.0,
        ensures: |ret| {
            self.count.0 == before
                && segments.iter().try_fold(NodeId::ROOT, |parent, segment| {
                    match self.child(parent, segment) {
                        | Maybe::Present(child) => Some(child),
                        | Maybe::Absent(_) => None,
                    }
                }) == Some(ret)
        },
    )]
    fn reach(
        &mut self,
        segments: &[Segment],
    ) -> NodeId
    {
        let mut current = NodeId::ROOT;
        for segment in segments {
            current = self.child_or_new(current, segment.clone());
        }
        current
    }

    /// The nodes from the root to `segments`, created along the way.
    ///
    /// # Specification
    /// - requires: the arena has its live root.
    /// - ensures: returns the root followed by one node per segment, each
    ///   reached from its predecessor; no binding is added.
    /// - provides: the chain needed to graft and prune.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — grafts at the root, an occupied target and beside a
    ///   bound sibling preserve the exact outside bindings; L2 — the deep walk
    ///   is iterative.
    /// - witness: `namespace::trie::tests::grafting_drops_whatever_was_at_the_target`
    /// - witness: `namespace::trie::tests::grafting_keeps_bindings_outside_the_target`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        requires: !self.nodes.is_empty(),
        captures: before = self.count.0,
        ensures: |ret| {
            self.count.0 == before
                && ret.len() == segments.len().saturating_add(1)
                && ret.first() == Some(&NodeId::ROOT)
                && ret.iter().zip(ret.iter().skip(1)).zip(segments).all(
                    |((parent, child), segment)| {
                        self.child(*parent, segment) == Maybe::Present(*child)
                    },
                )
        },
    )]
    fn reach_chain(
        &mut self,
        segments: &[Segment],
    ) -> Vec<NodeId>
    {
        let mut chain = Vec::with_capacity(segments.len().saturating_add(1_usize));
        chain.push(NodeId::ROOT);
        let mut current = NodeId::ROOT;
        for segment in segments {
            current = self.child_or_new(current, segment.clone());
            chain.push(current);
        }
        chain
    }

    /// A vacant node's position, reusing a freed one first.
    ///
    /// # Specification
    /// - requires: the arena has a live root and its free list contains vacant
    ///   non-root positions.
    /// - ensures: consumes the last free position before growing the arena; the
    ///   returned slot is vacant and the binding census is unchanged.
    /// - provides: reusable arena storage.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — public detach, graft and later insertion preserve
    ///   exact bindings when abandoned slots can be reused.
    /// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
    #[spec(
        requires: !self.nodes.is_empty(),
        captures: before = (
            self.nodes.len(),
            self.vacant.len(),
            self.vacant.last().copied(),
            self.count.0,
        ),
        ensures: |ret| {
            self.count.0 == before.3
                && ret.0 > 0
                && self.nodes.get(ret.0).is_some_and(|node| {
                    matches!(node.binding, Maybe::Absent(_)) && node.children.is_empty()
                })
                && match before.2 {
                    | Some(reused) => {
                        ret == reused
                            && self.nodes.len() == before.0
                            && self.vacant.len() == before.1.saturating_sub(1)
                    },
                    | None => {
                        ret.0 == before.0
                            && self.nodes.len() == before.0.saturating_add(1)
                            && self.vacant.is_empty()
                    },
                }
        },
    )]
    fn allocate(&mut self) -> NodeId
    {
        if let Some(reused) = self.vacant.pop() {
            return reused;
        }
        let fresh = NodeId(self.nodes.len());
        self.nodes.push(Node::vacant());
        fresh
    }

    /// Return `node`'s position to the vacancy list, emptied.
    ///
    /// # Specification
    /// - requires: a detached, vacant non-root node not already on the free
    ///   list.
    /// - ensures: appends its position to the free list, leaves the slot vacant
    ///   and changes no binding census.
    /// - provides: reuse after pruning.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — detached branches can be replaced without leaking
    ///   their old bindings into subsequent paths.
    /// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
    /// - witness: `namespace::trie::tests::detaching_rebases_and_leaves_the_rest`
    #[spec(
        requires: node.0 > 0
            && self.nodes.get(node.0).is_some_and(|slot| {
                matches!(slot.binding, Maybe::Absent(_)) && slot.children.is_empty()
            }),
        captures: before = (self.count.0, self.nodes.len(), self.vacant.len()),
        ensures: self.count.0 == before.0
            && self.nodes.len() == before.1
            && self.vacant.len() == before.2.saturating_add(1)
            && self.vacant.last() == Some(&node)
            && self.nodes.get(node.0).is_some_and(|slot| {
                matches!(slot.binding, Maybe::Absent(_)) && slot.children.is_empty()
            }),
    )]
    fn free(
        &mut self,
        node: NodeId,
    )
    {
        if let Some(slot) = self.nodes.get_mut(node.0) {
            *slot = Node::vacant();
            self.vacant.push(node);
        }
    }

    /// Take `node`'s binding and children, leaving it vacant.
    ///
    /// # Specification
    /// - requires: the node is in this arena.
    /// - ensures: moves its binding and children out, leaving a vacant slot;
    ///   the caller updates the binding census when its larger move finishes.
    /// - provides: destructive node extraction without cloning payloads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — detach, graft and union retain moved bindings and
    ///   discard only the selected target bindings.
    /// - witness: `namespace::trie::tests::detaching_rebases_and_leaves_the_rest`
    /// - witness: `namespace::trie::tests::grafting_drops_whatever_was_at_the_target`
    /// - witness: `namespace::trie::tests::relocation_and_collision_keep_payloads_with_their_tags`
    #[spec(
        requires: node.0 < self.nodes.len(),
        captures: before = (
            self.count.0,
            self.nodes.get(node.0).map(|slot| {
                (
                    matches!(slot.binding, Maybe::Present(_)),
                    slot.children.len(),
                )
            }),
        ),
        ensures: |ret| {
            self.count.0 == before.0
                && self.nodes.get(node.0).is_some_and(|slot| {
                    matches!(slot.binding, Maybe::Absent(_)) && slot.children.is_empty()
                })
                && before.1.is_some_and(|old| {
                    matches!(ret.binding, Maybe::Present(_)) == old.0 && ret.children.len() == old.1
                })
        },
    )]
    fn take(
        &mut self,
        node: NodeId,
    ) -> Node<Data, Tag>
    {
        self.nodes
            .get_mut(node.0)
            .map_or(Node::vacant(), |slot| mem::replace(slot, Node::vacant()))
    }

    /// Remove the edge from `parent` spelled `segment`.
    ///
    /// # Specification
    /// - requires: the parent is in this arena.
    /// - ensures: removes exactly the matching edge when present; no binding
    ///   census is adjusted by unlinking alone.
    /// - provides: detachment before reclaiming a branch.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — detaching one prefix leaves its siblings reachable
    ///   and the detached paths absent.
    /// - witness: `namespace::trie::tests::detaching_rebases_and_leaves_the_rest`
    /// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
    #[spec(
        requires: parent.0 < self.nodes.len(),
        captures: before = (
            self.count.0,
            self.nodes.get(parent.0).map(|node| {
                (
                    node.children.len(),
                    node.children
                        .binary_search_by(|edge| edge.segment.cmp(segment))
                        .is_ok(),
                )
            }),
        ),
        ensures: self.count.0 == before.0
            && matches!(self.child(parent, segment), Maybe::Absent(_))
            && before.1.is_some_and(|old| {
                self.nodes.get(parent.0).is_some_and(|node| {
                    node.children.len() == old.0.saturating_sub(usize::from(old.1))
                })
            }),
    )]
    fn unlink(
        &mut self,
        parent: NodeId,
        segment: &Segment,
    )
    {
        if let Some(node) = self.nodes.get_mut(parent.0)
            && let Ok(found) = node
                .children
                .binary_search_by(|candidate| candidate.segment.cmp(segment))
        {
            let _edge = node.children.remove(found);
        }
    }

    /// Drop `node`'s binding and every node below it, keeping `node` itself.
    ///
    /// # Specification
    /// - requires: `node` is live.
    /// - ensures: `node` is vacant, every descendant is freed and the binding
    ///   count falls by the bindings dropped.
    /// - provides: the drop half of a graft.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — replacing an occupied target drops its bindings but
    ///   retains outside siblings; the moved branch can reuse the released
    ///   slots.
    /// - witness: `namespace::trie::tests::grafting_drops_whatever_was_at_the_target`
    /// - witness: `namespace::trie::tests::grafting_keeps_bindings_outside_the_target`
    /// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
    #[spec(
        requires: node.0 < self.nodes.len(),
        captures: before = (self.count.0, self.nodes.len(), self.vacant.len()),
        ensures: self.count.0 <= before.0
            && self.nodes.len() == before.1
            && self.vacant.len() >= before.2
            && self.nodes.get(node.0).is_some_and(|slot| {
                matches!(slot.binding, Maybe::Absent(_)) && slot.children.is_empty()
            }),
    )]
    fn clear(
        &mut self,
        node: NodeId,
    )
    {
        let cleared = self.take(node);
        let mut dropped = usize::from(matches!(cleared.binding, Maybe::Present(_)));
        let mut stack: Vec<NodeId> = cleared.children.iter().map(|edge| edge.node).collect();
        while let Some(below) = stack.pop() {
            let freed = self.take(below);
            if let Maybe::Present(_) = freed.binding {
                dropped = dropped.saturating_add(1_usize);
            }
            stack.extend(freed.children.iter().map(|edge| edge.node));
            self.vacant.push(below);
        }
        self.count.0 = self.count.0.saturating_sub(dropped);
    }

    /// Move the subtree at `from` in `source` into the vacant node `into` of
    /// this trie.
    ///
    /// # Specification
    /// - requires: `from` is live in `source` and unlinked from its parent
    ///   unless it is the root; `into` is live and vacant here.
    /// - ensures: `into` holds `from`'s binding and a copy of its descendants
    ///   in the same order; `source` frees every moved node but the root and
    ///   loses the moved bindings from its count, which this trie gains.
    /// - provides: the move shared by detaching and grafting.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root and nested moves conserve exact bindings,
    ///   including non-unit tags; L2 — a deep chain moves without recursive
    ///   calls.
    /// - witness: `namespace::trie::tests::detaching_at_the_root_takes_everything`
    /// - witness: `namespace::trie::tests::detaching_rebases_and_leaves_the_rest`
    /// - witness: `namespace::trie::tests::relocation_and_collision_keep_payloads_with_their_tags`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        requires: from.0 < source.nodes.len()
            && self.nodes.get(into.0).is_some_and(|node| {
                matches!(node.binding, Maybe::Absent(_)) && node.children.is_empty()
            }),
        captures: before = (self.count.0, source.count.0),
        ensures: source.count.0 <= before.1
            && self.count.0
                == before
                    .0
                    .saturating_add(before.1.saturating_sub(source.count.0))
            && source.nodes.get(from.0).is_some_and(|node| {
                matches!(node.binding, Maybe::Absent(_)) && node.children.is_empty()
            }),
    )]
    fn transplant(
        &mut self,
        source: &mut Self,
        from: NodeId,
        into: NodeId,
    )
    {
        let mut moved = 0_usize;
        let mut stack = Vec::new();
        stack.push((from, into));
        while let Some((old, new)) = stack.pop() {
            let mut taken = source.take(old);
            if old != NodeId::ROOT {
                source.vacant.push(old);
            }
            if let Maybe::Present(_) = taken.binding {
                moved = moved.saturating_add(1_usize);
            }
            for edge in &mut taken.children {
                let fresh = self.allocate();
                stack.push((edge.node, fresh));
                edge.node = fresh;
            }
            if let Some(slot) = self.nodes.get_mut(new.0) {
                *slot = taken;
            }
        }
        source.count.0 = source.count.0.saturating_sub(moved);
        self.count.0 = self.count.0.saturating_add(moved);
    }

    /// Free each node of `chain` that holds nothing, innermost first, up to
    /// the first that holds something; the root always stays.
    ///
    /// # Specification
    /// - requires: `chain` runs from the root along `path`, each node the child
    ///   of the one before by the matching segment.
    /// - ensures: no node of `chain` but the root is left unbound and
    ///   childless.
    /// - provides: the shape invariant after a detach or an empty graft.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — detachment preserves its sibling and later reuse has
    ///   no old bindings; L2 — a long now-empty chain is reclaimed iteratively.
    /// - witness: `namespace::trie::tests::detaching_rebases_and_leaves_the_rest`
    /// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        requires: chain.first() == Some(&NodeId::ROOT)
            && chain.len() <= path.segments().len().saturating_add(1)
            && chain.iter().all(|node| node.0 < self.nodes.len()),
        captures: before = (self.count.0, self.nodes.len(), self.vacant.len()),
        ensures: self.count.0 == before.0
            && self.nodes.len() == before.1
            && self.vacant.len() >= before.2
            && !self.nodes.is_empty(),
    )]
    fn prune(
        &mut self,
        chain: &[NodeId],
        path: &NamePath,
    )
    {
        let mut depth = chain.len();
        while depth > 1_usize {
            depth = depth.saturating_sub(1_usize);
            let (Some(&node), Some(&parent), Some(segment)) = (
                chain.get(depth),
                chain.get(depth.saturating_sub(1_usize)),
                path.segments().get(depth.saturating_sub(1_usize)),
            )
            else {
                return;
            };
            match self.nodes.get(node.0) {
                | Some(&Node {
                    binding: Maybe::Absent(_),
                    ref children,
                }) if children.is_empty() => {},
                | Some(_) | None => return,
            }
            self.unlink(parent, segment);
            self.free(node);
        }
    }
}

/// Queue the children `edges` of a merged node, smallest segment on top.
///
/// # Specification
/// - requires: edges arrive in strictly ascending segment order.
/// - ensures: appends one frame per edge in reverse order, retaining the parent
///   and depth, so the smallest segment is popped first.
/// - provides: the ordered union frontier.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two collisions inserted out of order are visited in path
///   order, with the resolver choosing each surviving binding.
/// - witness: `namespace::trie::tests::union_reports_collisions_in_path_order`
#[spec(
    requires: edges
        .iter()
        .zip(edges.iter().skip(1))
        .all(|(left, right)| left.segment < right.segment),
    captures: before = (stack.len(), edges.len()),
    ensures: stack.len() == before.0.saturating_add(before.1)
        && stack.get(before.0 ..).is_some_and(|added| {
            added
                .iter()
                .all(|frame| frame.parent == parent && frame.depth == depth)
                && added
                    .iter()
                    .zip(added.iter().skip(1))
                    .all(|(left, right)| left.segment > right.segment)
        }),
)]
fn push_merges(
    stack: &mut Vec<Merge>,
    edges: Vec<Child>,
    parent: NodeId,
    depth: SegmentCount,
)
{
    for edge in edges.into_iter().rev() {
        stack.push(Merge {
            later: edge.node,
            parent,
            segment: edge.segment,
            depth,
        });
    }
}

/// One pending node of a union: a node of the later namespace and where it
/// lands in this one.
///
/// # Specification
/// - requires: the earlier and later arenas accompany a pending merge.
/// - ensures: the arriving node is attached under the named parent and segment
///   at the recorded depth.
/// - provides: an explicit union worklist rather than recursive calls.
/// - executable: none — a frame does not hold either arena or the current
///   descent chain.
///
/// # Adequacy
/// - hypothesis: L3 — collisions occur at full paths in order; L2 — a deep
///   union uses the explicit frontier.
/// - witness: `namespace::trie::tests::union_reports_collisions_in_path_order`
/// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
#[derive(Debug)]
struct Merge
{
    /// The node in the later namespace.
    later: NodeId,
    /// The node of this namespace the arriving node lands under.
    parent: NodeId,
    /// The segment from `parent` to the landing node.
    segment: Segment,
    /// The landing node's depth, which is the length of the chain above it.
    depth: SegmentCount,
}

impl<Data, Tag> PartialEq for Trie<Data, Tag>
where
    Data: PartialEq,
    Tag: PartialEq,
{
    /// Whether the two namespaces hold the same bindings at the same paths.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: equal exactly when every path is bound in both or neither, to
    ///   equal bindings; the arena layout and the vacancy list are not
    ///   compared.
    /// - provides: namespace equality as the bindings it holds, which the shape
    ///   invariant makes a node-for-node walk.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused import preserves namespace equality, while
    ///   detach, reuse and insertion produce an equal namespace through a
    ///   different arena layout; tags participate in equality.
    /// - witness: `namespace::namespace::a_refused_multi_entry_import_leaves_the_visible_namespace_as_it_was`
    /// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
    /// - witness: `namespace::trie::tests::relocation_and_collision_keep_payloads_with_their_tags`
    #[spec(
        ensures: |ret| {
            (!ret || self.count == other.count) && (self.count.0 != 0 || other.count.0 != 0 || ret)
        },
    )]
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        if self.count != other.count {
            return false;
        }
        let mut stack = Vec::new();
        stack.push((NodeId::ROOT, NodeId::ROOT));
        while let Some((left, right)) = stack.pop() {
            let (Some(left), Some(right)) = (self.nodes.get(left.0), other.nodes.get(right.0))
            else {
                return false;
            };
            if left.binding != right.binding || left.children.len() != right.children.len() {
                return false;
            }
            for (left, right) in left.children.iter().zip(right.children.iter()) {
                if left.segment != right.segment {
                    return false;
                }
                stack.push((left.node, right.node));
            }
        }
        true
    }
}

impl<Data, Tag> Eq for Trie<Data, Tag>
where
    Data: Eq,
    Tag: Eq,
{
}

impl<Data, Tag> fmt::Debug for Trie<Data, Tag>
where
    Data: fmt::Debug,
    Tag: fmt::Debug,
{
    /// Writes the bindings as a map from path to binding, in path order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'trie, Data, Tag> IntoIterator for &'trie Trie<Data, Tag>
{
    type IntoIter = Bindings<'trie, Data, Tag>;
    type Item = (NamePath, &'trie Binding<Data, Tag>);

    /// Every binding, in ascending path order.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two bindings inserted out of order, iterated by
    ///   borrowing, asserted as the exact ordered listing.
    /// - witness: `namespace::trie::tests::borrowing_a_namespace_iterates_every_binding_in_order`
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.iter()
    }
}

impl<Data, Tag> FromIterator<(NamePath, Binding<Data, Tag>)> for Trie<Data, Tag>
{
    /// The namespace binding each path to its binding, a later repeat
    /// displacing an earlier.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: binds each input path, a later repeated path replacing the
    ///   earlier binding; the cached count matches the bound nodes.
    /// - provides: namespace construction from ordered inputs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a repeated path retains the last payload beside an
    ///   independent path; empty and nested inputs exercise the carrier
    ///   boundaries.
    /// - witness: `namespace::trie::tests::collecting_repeats_keeps_the_last_binding`
    /// - witness: `namespace::trie::tests::a_path_and_its_extension_are_independent_bindings`
    #[spec(
        ensures: |ret| {
            !ret.nodes.is_empty()
                && ret.vacant.is_empty()
                && ret.count.0
                    == ret
                        .nodes
                        .iter()
                        .filter(|node| matches!(node.binding, Maybe::Present(_)))
                        .count()
        },
    )]
    #[inline]
    fn from_iter<Source>(iter: Source) -> Self
    where
        Source: IntoIterator<Item = (NamePath, Binding<Data, Tag>)>,
    {
        let mut trie = Self::empty();
        for (path, binding) in iter {
            let _displaced = trie.insert(&path, binding);
        }
        trie
    }
}

/// One pending node of an iteration.
///
/// # Specification
/// - requires: the walked trie and current path accompany the visit.
/// - ensures: the root visit has no incoming segment; descendants carry the
///   edge segment and resulting path depth.
/// - provides: one pending step of the ordered iterator.
/// - executable: none — a visit holds neither the owning trie nor the path it
///   extends.
///
/// # Adequacy
/// - hypothesis: L3 — exact listings cover root-relative nested paths and
///   out-of-order insertion.
/// - witness: `namespace::trie::tests::borrowing_a_namespace_iterates_every_binding_in_order`
/// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
#[derive(Clone, Copy, Debug)]
struct Visit<'trie>
{
    /// The node.
    node: NodeId,
    /// The node's depth.
    depth: usize,
    /// The segment that reaches it.
    segment: Maybe<&'trie Segment, edge::Absent>,
}

/// The bindings of a namespace, in ascending path order.
///
/// # Specification
/// - requires: construction starts through the trie's iterator entry point.
/// - ensures: the frontier walks the borrowed trie in path order, yielding each
///   binding with its owned path.
/// - provides: ordered observation without exposing arena positions.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; iterator predicates check the initial frontier and each
///   yielded binding.
///
/// # Adequacy
/// - hypothesis: L3 — exact iteration after out-of-order insertion and arena
///   reuse fixes the finite ordering and binding correspondence.
/// - witness: `namespace::trie::tests::borrowing_a_namespace_iterates_every_binding_in_order`
/// - witness: `namespace::trie::tests::vacant_slots_do_not_change_namespace_equality_or_iteration`
#[derive(Clone, Debug)]
pub struct Bindings<'trie, Data, Tag>
{
    /// The namespace walked.
    trie: &'trie Trie<Data, Tag>,
    /// The nodes still to visit, the next on top.
    stack: Vec<Visit<'trie>>,
    /// The segments from the root to the last node visited.
    path: Vec<&'trie Segment>,
}

impl<'trie, Data, Tag> Iterator for Bindings<'trie, Data, Tag>
{
    type Item = (NamePath, &'trie Binding<Data, Tag>);

    /// The next binding in ascending path order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the bindings in preorder over children sorted by segment,
    ///   which is ascending path order, each with its owned path.
    /// - provides: listing and debugging a namespace.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two bindings inserted out of order, and every carrier
    ///   listing, asserted as the exact ordered listing.
    /// - witness: `namespace::trie::tests::borrowing_a_namespace_iterates_every_binding_in_order`
    /// - witness: `namespace::trie::tests::union_reports_collisions_in_path_order`
    #[spec(
        ensures: |ret| match ret.as_ref() {
            | Some(pair) => {
                pair.0.segments().iter().eq(self.path.iter().copied())
                    && matches!(self.trie.get(&pair.0), Maybe::Present(binding) if core::ptr::eq(&raw const *binding, &raw const *pair.1))
            },
            | None => self.stack.is_empty(),
        },
    )]
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        while let Some(visit) = self.stack.pop() {
            if let Maybe::Present(segment) = visit.segment {
                self.path.truncate(visit.depth.saturating_sub(1_usize));
                self.path.push(segment);
            }
            let Some(node) = self.trie.nodes.get(visit.node.0)
            else {
                continue;
            };
            for edge in node.children.iter().rev() {
                self.stack.push(Visit {
                    node: edge.node,
                    depth: visit.depth.saturating_add(1_usize),
                    segment: Maybe::Present(&edge.segment),
                });
            }
            if let Maybe::Present(ref binding) = node.binding {
                let segments: Vec<Segment> =
                    self.path.iter().map(|&segment| segment.clone()).collect();
                return Some((NamePath::from(segments), binding));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;
    use alloc::vec::Vec;

    use quenchant_shape::shape::Maybe;

    use super::Binding;
    use super::BindingCount;
    use super::Collision;
    use super::Emptiness;
    use super::Trie;
    use super::binding;
    use super::displaced;
    use crate::namespace::path::DottedName;
    use crate::namespace::path::NamePath;

    /// The payload a carrier test binds.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Payload(u32);

    /// One entry of a test namespace: a dotted path and its payload.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Entry
    {
        /// The dotted rendering of the bound path.
        path: DottedName<'static>,
        /// The payload bound there.
        payload: Payload,
    }

    /// The path `text` renders.
    ///
    /// # Specification
    /// trivial.
    fn path<Text>(text: Text) -> NamePath
    where
        Text: Into<DottedName<'static>>,
    {
        NamePath::from(text.into())
    }

    /// The entry binding `text` to `payload`.
    ///
    /// # Specification
    /// trivial.
    fn entry<Text>(
        text: Text,
        payload: Payload,
    ) -> Entry
    where
        Text: Into<DottedName<'static>>,
    {
        Entry {
            path: text.into(),
            payload,
        }
    }

    /// The namespace of `entries`.
    ///
    /// # Specification
    /// trivial.
    fn namespace(entries: &[Entry]) -> Trie<Payload, ()>
    {
        entries
            .iter()
            .map(|item| (path(item.path), Binding::new(item.payload, ())))
            .collect()
    }

    /// The namespace's dotted paths with their payloads, in ascending order.
    ///
    /// # Specification
    /// trivial.
    fn listing(subject: &Trie<Payload, ()>) -> Vec<(String, Payload)>
    {
        subject
            .iter()
            .map(|(path, binding)| (format!("{path}"), binding.data))
            .collect()
    }

    /// The expected listing of `entries`.
    ///
    /// # Specification
    /// trivial.
    fn expected(entries: &[Entry]) -> Vec<(String, Payload)>
    {
        entries
            .iter()
            .map(|item| (String::from(item.path.as_ref()), item.payload))
            .collect()
    }

    #[test]
    fn vacant_slots_do_not_change_namespace_equality_or_iteration()
    {
        let mut subject = namespace(&[entry("a.deep", Payload(1)), entry("b", Payload(2))]);
        let moved = subject.detach_subtree(&path("a"));
        subject.graft_subtree(&path("c"), moved);
        let _fresh = subject.insert(&path("a"), Binding::new(Payload(5), ()));
        let wanted = [
            entry("a", Payload(5)),
            entry("b", Payload(2)),
            entry("c.deep", Payload(1)),
        ];
        assert_eq!(subject, namespace(&wanted));
        assert_eq!(listing(&subject), expected(&wanted));
        assert_eq!(subject.binding_count(), BindingCount::from(3_usize));
        assert_eq!(
            subject.get(&path("a.deep")),
            Maybe::Absent(binding::Absent::Unbound)
        );
    }

    #[test]
    fn a_bound_root_does_not_bridge_a_gap_in_governed_resolution()
    {
        let mut subject = namespace(&[entry("", Payload(7)), entry("a.b", Payload(2))]);
        assert_eq!(
            subject.resolved_prefix(&NamePath::root()),
            Maybe::Absent(binding::Absent::Unbound)
        );
        assert_eq!(
            subject.resolved_prefix(&path("a.b")),
            Maybe::Absent(binding::Absent::Unbound)
        );
        assert_eq!(
            subject.get(&path("a.b")).map(|binding| binding.data),
            Maybe::Present(Payload(2))
        );
        let _fresh = subject.insert(&path("a"), Binding::new(Payload(3), ()));
        assert_eq!(
            subject
                .resolved_prefix(&path("a.b.c"))
                .map(|(depth, binding)| (usize::from(depth), binding.data)),
            Maybe::Present((2_usize, Payload(2)))
        );
    }

    #[test]
    fn first_binding_prefers_a_bound_prefix_then_its_least_descendant()
    {
        let mut subject = namespace(&[
            entry("a.z", Payload(2)),
            entry("a.a", Payload(1)),
            entry("b", Payload(3)),
        ]);
        assert_eq!(
            subject
                .first_at_or_below(&path("a"))
                .map(|binding| binding.data),
            Maybe::Present(Payload(1))
        );
        let _fresh = subject.insert(&path("a"), Binding::new(Payload(9), ()));
        assert_eq!(
            subject
                .first_at_or_below(&path("a"))
                .map(|binding| binding.data),
            Maybe::Present(Payload(9))
        );
        assert_eq!(
            subject.first_at_or_below(&path("missing")),
            Maybe::Absent(binding::Absent::Unbound)
        );
        let _root = subject.insert(&NamePath::root(), Binding::new(Payload(7), ()));
        assert_eq!(
            subject
                .first_at_or_below(&NamePath::root())
                .map(|binding| binding.data),
            Maybe::Present(Payload(7))
        );
    }

    #[test]
    fn collecting_repeats_keeps_the_last_binding()
    {
        let subject = namespace(&[
            entry("x", Payload(1)),
            entry("y", Payload(2)),
            entry("x", Payload(3)),
        ]);
        assert_eq!(subject.binding_count(), BindingCount::from(2_usize));
        assert_eq!(
            listing(&subject),
            expected(&[entry("x", Payload(3)), entry("y", Payload(2))])
        );
    }

    #[test]
    fn relocation_and_collision_keep_payloads_with_their_tags()
    {
        let original: Trie<Payload, Payload> =
            core::iter::once((path("a"), Binding::new(Payload(1), Payload(10)))).collect();
        let mut relocated = original.into_prefixed(&path("pkg"));
        let arriving: Trie<Payload, Payload> =
            core::iter::once((path("pkg.a"), Binding::new(Payload(2), Payload(20)))).collect();
        relocated
            .union_resolving(arriving, &mut |at, collision| {
                assert_eq!(at, &path("pkg.a"));
                assert_eq!(collision.former, Binding::new(Payload(1), Payload(10)));
                assert_eq!(collision.latter, Binding::new(Payload(2), Payload(20)));
                Ok::<_, core::convert::Infallible>(collision.latter)
            })
            .expect("this resolver keeps the arriving binding");
        assert_eq!(
            relocated.get(&path("pkg.a")),
            Maybe::Present(&Binding::new(Payload(2), Payload(20)))
        );
        let different_tag: Trie<Payload, Payload> =
            core::iter::once((path("pkg.a"), Binding::new(Payload(2), Payload(99)))).collect();
        assert_ne!(relocated, different_tag);
    }
    #[test]
    fn the_empty_namespace_is_empty()
    {
        assert_eq!(
            Trie::<Payload, ()>::empty().emptiness(),
            Emptiness::EMPTY,
            "a fresh namespace holds nothing"
        );
        assert_eq!(
            namespace(&[entry("nat", Payload(1))]).emptiness(),
            Emptiness::OCCUPIED,
            "one binding is enough to occupy a namespace"
        );
    }

    #[test]
    fn a_path_and_its_extension_are_independent_bindings()
    {
        let subject = namespace(&[entry("nat", Payload(1)), entry("nat.plus", Payload(2))]);
        assert_eq!(
            subject.binding_count(),
            BindingCount::from(2_usize),
            "namespaces are implicit, so `nat` and `nat.plus` coexist"
        );
        assert_eq!(
            subject.get(&path("nat")).map(|binding| binding.data),
            Maybe::Present(Payload(1)),
            "the shorter path resolves on its own"
        );
    }

    #[test]
    fn a_path_bound_only_below_it_resolves_to_nothing()
    {
        let subject = namespace(&[entry("nat.plus", Payload(1))]);
        assert_eq!(
            subject.get(&path("nat")),
            Maybe::Absent(binding::Absent::Unbound),
            "`nat` is not an object, so it reaches a binding only when something is bound at it"
        );
        assert_eq!(
            subject.get(&path("nat.plus")).map(|binding| binding.data),
            Maybe::Present(Payload(1)),
            "while the whole path that is bound resolves exactly"
        );
    }

    #[test]
    fn borrowing_a_namespace_iterates_every_binding_in_order()
    {
        let subject = namespace(&[entry("b", Payload(2)), entry("a", Payload(1))]);
        let mut visited: Vec<(String, Payload)> = Vec::new();
        for (path, binding) in &subject {
            visited.push((format!("{path}"), binding.data));
        }
        assert_eq!(
            visited,
            expected(&[entry("a", Payload(1)), entry("b", Payload(2))]),
            "borrowing a namespace iterates it in ascending path order"
        );
    }

    #[test]
    fn inserting_returns_the_binding_it_displaced()
    {
        let mut subject = namespace(&[entry("nat", Payload(1))]);
        assert_eq!(
            subject.insert(&path("nat.plus"), Binding::new(Payload(2), ())),
            Maybe::Absent(displaced::Absent::Fresh),
            "a fresh path displaces nothing"
        );
        assert_eq!(
            subject.insert(&path("nat"), Binding::new(Payload(3), ())),
            Maybe::Present(Binding::new(Payload(1), ())),
            "a repeat insert hands back exactly what it replaced"
        );
        assert_eq!(
            listing(&subject),
            expected(&[entry("nat", Payload(3)), entry("nat.plus", Payload(2))]),
            "and the later binding is what the path now reaches"
        );
    }

    #[test]
    fn detaching_at_the_root_takes_everything()
    {
        let mut subject = namespace(&[entry("a.x", Payload(1)), entry("b.y", Payload(2))]);
        let detached = subject.detach_subtree(&NamePath::root());
        assert_eq!(
            subject.emptiness(),
            Emptiness::EMPTY,
            "the root prefixes every path, so nothing is retained"
        );
        assert_eq!(
            listing(&detached),
            expected(&[entry("a.x", Payload(1)), entry("b.y", Payload(2))]),
            "detaching at the root rebases nothing"
        );
    }

    #[test]
    fn detaching_rebases_and_leaves_the_rest()
    {
        let mut subject = namespace(&[
            entry("nat.plus", Payload(1)),
            entry("nat.times", Payload(2)),
            entry("int.plus", Payload(3)),
        ]);
        let detached = subject.detach_subtree(&path("nat"));
        assert_eq!(
            listing(&detached),
            expected(&[entry("plus", Payload(1)), entry("times", Payload(2))]),
            "the detached subtree is rebased to the root"
        );
        assert_eq!(
            subject,
            namespace(&[entry("int.plus", Payload(3))]),
            "bindings outside the prefix are retained in place, and the emptied `nat` is pruned"
        );
    }

    #[test]
    fn detaching_an_absent_prefix_yields_the_empty_namespace()
    {
        let mut subject = namespace(&[entry("nat.plus", Payload(1))]);
        let detached = subject.detach_subtree(&path("rational"));
        assert_eq!(
            detached.emptiness(),
            Emptiness::EMPTY,
            "an absent prefix detaches nothing"
        );
        assert_eq!(
            listing(&subject),
            expected(&[entry("nat.plus", Payload(1))]),
            "and leaves the namespace untouched"
        );
    }

    #[test]
    fn grafting_at_the_root_replaces_everything()
    {
        let mut subject = namespace(&[entry("a.x", Payload(1)), entry("b.y", Payload(2))]);
        subject.graft_subtree(&NamePath::root(), namespace(&[entry("c.z", Payload(3))]));
        assert_eq!(
            listing(&subject),
            expected(&[entry("c.z", Payload(3))]),
            "grafting at the root drops the whole target namespace"
        );
    }

    #[test]
    fn grafting_drops_whatever_was_at_the_target()
    {
        let mut subject = namespace(&[entry("lib.old", Payload(1)), entry("lib.kept", Payload(2))]);
        subject.graft_subtree(&path("lib"), namespace(&[entry("new", Payload(3))]));
        assert_eq!(
            listing(&subject),
            expected(&[entry("lib.new", Payload(3))]),
            "the target subtree is replaced, not merged"
        );
        subject.graft_subtree(&path("lib"), Trie::empty());
        assert_eq!(
            subject,
            Trie::empty(),
            "grafting nothing over the only subtree empties the namespace and prunes the target"
        );
    }

    #[test]
    fn grafting_keeps_bindings_outside_the_target()
    {
        let mut subject = namespace(&[entry("lib.old", Payload(1)), entry("app.main", Payload(2))]);
        subject.graft_subtree(&path("lib"), namespace(&[entry("new", Payload(3))]));
        assert_eq!(
            listing(&subject),
            expected(&[entry("app.main", Payload(2)), entry("lib.new", Payload(3))]),
            "only the target subtree is affected"
        );
    }

    #[test]
    fn prefixing_moves_every_path()
    {
        let subject = namespace(&[entry("x", Payload(1)), entry("y.z", Payload(2))]);
        assert_eq!(
            listing(&subject.into_prefixed(&path("section"))),
            expected(&[
                entry("section.x", Payload(1)),
                entry("section.y.z", Payload(2)),
            ]),
            "prefixing is what a section's export undergoes at close"
        );
    }

    #[test]
    fn union_of_disjoint_namespaces_merges_pointwise()
    {
        let mut subject = namespace(&[entry("a.x", Payload(1))]);
        let mut collisions: Vec<String> = Vec::new();
        let outcome: Result<(), ()> = subject.union_resolving(
            namespace(&[entry("a.y", Payload(2))]),
            &mut |path, collision| {
                collisions.push(format!("{path}"));
                Ok(collision.latter)
            },
        );
        assert_eq!(outcome, Ok(()), "a disjoint union cannot fail");
        assert!(
            collisions.is_empty(),
            "sharing the prefix `a` is not a collision: only equal whole paths collide"
        );
        assert_eq!(
            listing(&subject),
            expected(&[entry("a.x", Payload(1)), entry("a.y", Payload(2))]),
            "the implicit namespace `a` is merged, not shadowed"
        );
    }

    #[test]
    fn union_consults_the_resolver_on_a_collision()
    {
        for (keep_latter, survivor) in [(true, Payload(2)), (false, Payload(1))] {
            let mut subject = namespace(&[entry("a.x", Payload(1))]);
            let outcome: Result<(), ()> = subject.union_resolving(
                namespace(&[entry("a.x", Payload(2))]),
                &mut |_, collision| {
                    Ok(if keep_latter {
                        collision.latter
                    }
                    else {
                        collision.former
                    })
                },
            );
            assert_eq!(outcome, Ok(()), "an accepted collision cannot fail");
            assert_eq!(
                listing(&subject),
                expected(&[entry("a.x", survivor)]),
                "the resolver, not the carrier, chooses the survivor"
            );
        }
    }

    #[test]
    fn union_reports_collisions_in_path_order()
    {
        let mut subject = namespace(&[entry("b", Payload(1)), entry("a", Payload(2))]);
        let mut collisions: Vec<String> = Vec::new();
        let outcome: Result<(), ()> = subject.union_resolving(
            namespace(&[entry("b", Payload(3)), entry("a", Payload(4))]),
            &mut |path, collision| {
                collisions.push(format!("{path}"));
                Ok(collision.latter)
            },
        );
        assert_eq!(outcome, Ok(()), "both collisions are accepted");
        assert_eq!(
            collisions,
            Vec::from([String::from("a"), String::from("b")]),
            "collisions arrive in ascending path order, not insertion order"
        );
    }

    #[test]
    fn union_propagates_a_declining_resolver()
    {
        let mut subject = namespace(&[entry("a.x", Payload(1))]);
        let outcome: Result<(), Collision<Payload, ()>> = subject.union_resolving(
            namespace(&[entry("a.x", Payload(2))]),
            &mut |_, collision| Err(collision),
        );
        assert_eq!(
            outcome,
            Err(Collision {
                former: Binding::new(Payload(1), ()),
                latter: Binding::new(Payload(2), ()),
            }),
            "the declining resolver's exact value reaches the caller"
        );
    }

    #[test]
    fn a_declined_collision_keeps_the_binding_it_found()
    {
        let mut subject = namespace(&[entry("m.b", Payload(1))]);
        let outcome: Result<(), Collision<Payload, ()>> = subject.union_resolving(
            namespace(&[entry("m.a", Payload(2)), entry("m.b", Payload(3))]),
            &mut |_, collision| Err(collision),
        );
        assert_eq!(
            outcome,
            Err(Collision {
                former: Binding::new(Payload(1), ()),
                latter: Binding::new(Payload(3), ()),
            }),
            "the resolver declines the collision at `m.b`, and only that one"
        );
        assert_eq!(
            subject,
            namespace(&[entry("m.a", Payload(2)), entry("m.b", Payload(1))]),
            "the merge stops where it was refused, keeping what it merged and never dropping the \
             binding whose collision was refused"
        );
    }
}
