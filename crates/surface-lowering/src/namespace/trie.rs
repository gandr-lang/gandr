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
/// The tag is opaque to every operation here — the carrier relocates and
/// merges it but never reads it — so a consumer chooses what it carries: a
/// source span, a provenance marker, `()`.
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct NodeId(usize);

impl NodeId
{
    /// The root, at the arena's first position in every trie.
    const ROOT: Self = Self(0);
}

/// One edge: the segment that reaches a child, and the child.
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
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty namespace and a one-binding namespace, each
    ///   asserted as the exact emptiness.
    /// - witness: `namespace::trie::tests::the_empty_namespace_is_empty`
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
/// trivial.
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
    /// - hypothesis: L3 — every listing assertion in the carrier and modifier
    ///   witnesses compares through it, and the refused-scope witnesses assert
    ///   equality of namespaces whose arenas were reshaped by an aborted union.
    /// - witness: `namespace::namespace::a_refused_multi_entry_import_leaves_the_visible_namespace_as_it_was`
    /// - witness: `namespace::namespace::a_nested_modifier_survives_a_round_trip`
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
    /// trivial.
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
