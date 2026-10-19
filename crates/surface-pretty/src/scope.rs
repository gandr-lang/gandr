//! The binders each node of a term stands under.
//!
//! A type the checker keeps for a term inside a body mentions the binders
//! around that term by de Bruijn index, and the printer names them from the
//! context it is given ([`Source::context`]). [`Scopes`] reads that context
//! off the term itself: one walk from each root over the printer's own child
//! table — the binders each child stands under are the ones the printer opens
//! when it spells the same former — records every binder with the binder
//! around it and the node that opens it, and every node with the innermost
//! binder it stands under.
//!
//! A node reached twice keeps the scope it was first reached in, so the walk
//! visits each node once and ends over any source, a cyclic one included.
//!
//! The node index is a `hashbrown` map under `foldhash`'s fixed-seed state,
//! the grammar's label-index pair: the table build probes it once per node
//! reached and once per typed term, and an ordered map's probes there cost a
//! tenth of the build. The map is never iterated, so its order is never
//! observed. Reversal: a caller that needs the nodes in order.

use alloc::vec::Vec;
use core::hash::Hash;

use anodized::spec;
use foldhash::fast::FixedState;
use gandr_core_term::Zone;
use hashbrown::HashMap;
use hashbrown::hash_map::Entry;

use crate::Source;
use crate::walk::Admits;
use crate::walk::Bodies;
use crate::walk::children;

/// The position of one binder among a [`Scopes`]'s binders.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderIndex(usize);

impl From<BinderIndex> for usize
{
    /// The position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: BinderIndex) -> Self
    {
        index.0
    }
}

/// The position of one child slot among its node's children, in the
/// printer's order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChildSlot(usize);

impl ChildSlot
{
    /// The first child slot: a capability scope's subject.
    pub const FIRST: Self = Self(0);
}

impl From<usize> for ChildSlot
{
    /// The slot at the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

/// One binder: the binder it stands under, the node that opens it, the child
/// slot of that node it opens over and the zone it opens in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Binder<Node>
{
    /// The binder around this one; none at a root.
    parent: Option<BinderIndex>,
    /// The former that opens it: a lambda, a bind, a dependent arrow, a case.
    opener: Node,
    /// The position of the child slot it opens over, among the opener's
    /// children in the printer's order.
    slot: ChildSlot,
    /// The zone it opens in.
    zone: Zone,
}

impl<Node: Copy> Binder<Node>
{
    /// The binder around this one; none at a root.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each binder of a chain names the next one out, the
    ///   outermost none.
    /// - witness: `scope::tests::a_variable_finds_the_binder_it_counts_out_to`
    #[inline]
    #[must_use]
    pub const fn parent(&self) -> Option<BinderIndex>
    {
        self.parent
    }

    /// The former that opens the binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn opener(&self) -> Node
    {
        self.opener
    }

    /// The position of the child slot the binder opens over, among its
    /// opener's children in the printer's order: a capability scope's
    /// subject is its first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn slot(&self) -> ChildSlot
    {
        self.slot
    }

    /// The zone the binder opens in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn zone(&self) -> Zone
    {
        self.zone
    }
}

/// The binders the nodes reachable from some roots stand under.
#[derive(Clone, Debug, Default)]
pub struct Scopes<Node>
{
    /// Every binder met, each after the binder around it.
    binders: Vec<Binder<Node>>,
    /// Each node reached, with the innermost binder it stands under.
    standing: HashMap<Node, Option<BinderIndex>, FixedState>,
}

impl<Node: Copy + Eq + Hash> Scopes<Node>
{
    /// The binders of every node reachable from `roots` in `source`, each
    /// root standing under none.
    ///
    /// # Specification
    /// - requires: nothing; a malformed source is admissible.
    /// - ensures: every node reachable from a root through the printer's child
    ///   table is recorded once, with the innermost binder of the scope it was
    ///   first reached in; each child's binders are recorded in the order the
    ///   printer opens them, the first outermost, each under the one before.
    /// - provides: the context of a typed node, which its type mentions.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each node is expanded at most once, and a source names finitely many
    /// nodes from finitely many roots.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda around a split of two components resolves
    ///   the split body's variables to the split's two binders, the last
    ///   component innermost, then the lambda's; a binder opened in the wrong
    ///   order, chained to the wrong parent, or counted in the wrong zone fails
    ///   the witness.
    /// - witness: `scope::tests::a_variable_finds_the_binder_it_counts_out_to`
    #[spec(ensures: |ret| ret.binders.iter().enumerate().all(|(at, binder)|
        binder.parent.is_none_or(|parent| parent.0 < at)))]
    #[inline]
    pub fn of<S, Roots>(
        source: &S,
        roots: Roots,
    ) -> Self
    where
        S: Source<Node = Node> + ?Sized,
        Roots: IntoIterator<Item = Node>,
    {
        let mut scopes = Self {
            binders: Vec::new(),
            standing: HashMap::with_hasher(FixedState::default()),
        };
        let mut pending: Vec<(Node, Option<BinderIndex>)> =
            roots.into_iter().map(|root| (root, None)).collect();
        while let Some((node, scope)) = pending.pop() {
            match scopes.standing.entry(node) {
                Entry::Occupied(_) => continue,
                Entry::Vacant(vacant) => {
                    let _fresh = vacant.insert(scope);
                },
            }
            let former = source.read(node);
            for (position, slot) in children(source, node, &former, Admits::Type, Bodies::Spelled)
                .into_iter()
                .enumerate()
            {
                let mut inner = scope;
                for _ in 0_usize .. slot.binds.count {
                    let index = BinderIndex(scopes.binders.len());
                    scopes.binders.push(Binder {
                        parent: inner,
                        opener: node,
                        slot: ChildSlot::from(position),
                        zone: slot.binds.zone,
                    });
                    inner = Some(index);
                }
                if let Some(child) = slot.node {
                    pending.push((child, inner));
                }
            }
        }
        scopes
    }

    /// Every binder, each after the binder around it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn binders(&self) -> impl ExactSizeIterator<Item = (BinderIndex, &Binder<Node>)>
    {
        self.binders
            .iter()
            .enumerate()
            .map(|(at, binder)| (BinderIndex(at), binder))
    }

    /// Every node reached from the roots, in no fixed order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn reached(&self) -> impl Iterator<Item = Node> + '_
    {
        self.standing.keys().copied()
    }

    /// The innermost binder `node` stands under: none outside every binder,
    /// absent for a node no root reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn innermost(
        &self,
        node: Node,
    ) -> Option<Option<BinderIndex>>
    {
        self.standing.get(&node).copied()
    }

    /// The binder at `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn binder(
        &self,
        index: BinderIndex,
    ) -> Option<&Binder<Node>>
    {
        self.binders.get(index.0)
    }

    /// The binders of `zone` around the scope whose innermost binder is
    /// `innermost`, innermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each binder of the chain from `innermost` outward whose zone
    ///   is `zone`, in that order; a variable of `zone` at de Bruijn index `i`
    ///   names the `i`-th of them.
    /// - provides: the context a variable counts out through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each binder's parent precedes it, so the chain strictly descends.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::of`].
    /// - witness: `scope::tests::a_variable_finds_the_binder_it_counts_out_to`
    #[spec(ensures: |ret| ret.iter().all(|&index| self.binders.get(index.0).is_some_and(|binder| binder.zone == zone)))]
    #[inline]
    #[must_use]
    pub fn around(
        &self,
        innermost: Option<BinderIndex>,
        zone: Zone,
    ) -> Vec<BinderIndex>
    {
        let mut chain = Vec::new();
        let mut at = innermost;
        while let Some(index) = at {
            let Some(binder) = self.binders.get(index.0)
            else {
                break;
            };
            if binder.zone == zone {
                chain.push(index);
            }
            at = binder.parent.filter(|parent| parent.0 < index.0);
        }
        chain
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;

    use super::Scopes;
    use crate::CoreNode;
    use crate::CoreSource;

    /// A lambda around a split of two components resolves each variable of
    /// the split's body to the binder it counts out to: the split's two, the
    /// last component innermost, then the lambda's.
    #[test]
    fn a_variable_finds_the_binder_it_counts_out_to()
    {
        let mut core = CoreArena::new();
        let first = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = core.computation_return(first);
        let split = core.computation_split(
            first,
            gandr_core_term::ComponentCount::from(2_usize),
            returned,
        );
        let lambda = core.computation_lambda(split);
        let source = CoreSource::new(&core, &[]);
        let scopes = Scopes::of(&source, [CoreNode::Computation(lambda)]);
        let body = scopes
            .innermost(CoreNode::Computation(returned))
            .expect("the split's body is reached");
        let chain = scopes.around(body, Zone::Intuitionistic);
        assert_eq!(chain.len(), 3_usize, "a lambda and two components");
        let openers: Vec<CoreNode> = chain
            .iter()
            .map(|&index| scopes.binder(index).expect("a recorded binder").opener())
            .collect();
        assert_eq!(openers, [
            CoreNode::Computation(split),
            CoreNode::Computation(split),
            CoreNode::Computation(lambda),
        ]);
        let parents: Vec<_> = chain
            .iter()
            .map(|&index| scopes.binder(index).expect("a recorded binder").parent())
            .collect();
        assert_eq!(
            parents,
            [chain.get(1).copied(), chain.get(2).copied(), None],
            "each binder stands under the next one out, the lambda under none"
        );
        assert_eq!(
            scopes.innermost(CoreNode::Computation(split)),
            Some(chain.last().copied()),
            "the split stands under the lambda alone"
        );
        assert!(scopes.around(body, Zone::Linear).is_empty());
    }
}
