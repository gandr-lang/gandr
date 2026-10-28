//! The scope every IL node carries, as two slots beside the node.
//!
//! A node's scope is built once at mint as the union of what it names, the
//! annotations it carries and its children's scopes past the binders it opens
//! over each, and kept in its family's scope table at the node's own offset:
//! one slot per binding space, the code itself when it is one word and a
//! handle into the arena's word arena otherwise. A read is an index, and
//! minting is the only writer.

use gandr_core_term::support::Slot;
use gandr_core_term::support::ThinningRef;
use gandr_core_term::support::WordArena;
use quenchant_shape::shape::Maybe;

use super::CommandArena;
use super::CommandNode;
use super::ConsumerNode;
use super::MintRefusal;
use super::NodeAddress;
use super::NodeScope;
use super::Opens;
use super::ProducerNode;
use super::Scoping;
use super::command_annotations;
use super::command_children;
use super::command_named;
use super::consumer_annotations;
use super::consumer_children;
use super::consumer_named;
use super::producer_children;
use super::producer_named;
use crate::boundary::FamilyAddress as _;

/// A node's two slots: its producer support's and its covariable support's.
pub type Slots = [Slot; 2];

impl Scoping
{
    /// Keep the scope built: one slot per space, wide codes in `words`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) fn store(
        self,
        words: &mut WordArena,
    ) -> Slots
    {
        [
            words.store_union(self.producers),
            words.store_union(self.covariables),
        ]
    }
}

impl CommandArena
{
    /// Add a child's scope past `opens` to `scoping`.
    ///
    /// # Specification
    /// - requires: nothing; a dangling child is refused.
    /// - ensures: on success `scoping` holds the child's supports past `opens`,
    ///   read where the node stands.
    /// - fails: [`MintRefusal::DanglingProducer`],
    ///   [`MintRefusal::DanglingConsumer`] or [`MintRefusal::DanglingCommand`]
    ///   for a child whose scope the arena does not hold.
    /// - panics: none.
    /// - executable: none — this runs once per child on the mint path; the
    ///   instrumented body is a closure the test profile does not inline, and
    ///   the witnesses read every minted support back.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — binders in each zone whose bodies read and ignore the
    ///   bound name separate a kept index from a lowered one and the zones from
    ///   each other; L2 — every command of every generated focused term carries
    ///   the support an independent walk computes.
    /// - witness: `il::tests::an_unused_binder_thins_to_zero`
    /// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
    #[inline]
    fn gather_child(
        &self,
        scoping: &mut Scoping,
        child: NodeAddress,
        opens: Opens,
    ) -> Result<(), MintRefusal>
    {
        let slots = self.slots(child).ok_or(match child {
            NodeAddress::Producer(id) => MintRefusal::DanglingProducer(id),
            NodeAddress::Consumer(id) => MintRefusal::DanglingConsumer(id),
            NodeAddress::Command(id) => MintRefusal::DanglingCommand(id),
        })?;
        scoping.child(slots, &self.words, opens);
        Ok(())
    }

    /// Add the supports of `annotations` to `scoping`.
    ///
    /// # Specification
    /// - ensures: on success `scoping` holds every annotation's intuitionistic
    ///   indices.
    /// - fails: [`MintRefusal::DanglingAnnotation`] for the first annotation
    ///   the annotation arena does not hold.
    /// - panics: none.
    /// - executable: none — the scoping is read only once the node is stored;
    ///   the witness reads the support back off the minted node.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold whose element type names a variable no term of
    ///   the fold names separates a counted annotation from an ignored one.
    /// - witness: `il::tests::an_annotation_counts_in_its_nodes_support`
    #[inline]
    fn gather_annotations(
        &self,
        scoping: &mut Scoping,
        annotations: impl Iterator<Item = gandr_core_term::ValueTypeId>,
    ) -> Result<(), MintRefusal>
    {
        for annotation in annotations {
            let support = self
                .annotations
                .value_type_support(annotation)
                .ok_or(MintRefusal::DanglingAnnotation(annotation))?;
            scoping.annotation(support);
        }
        Ok(())
    }

    /// The scope minting keeps for a producer: the variable it names and each
    /// child's scope past the binders it opens.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when every child of `node` resolves, holding the
    ///   summary's scope.
    /// - fails: as [`Self::gather_child`], the first dangling child in edge
    ///   order.
    /// - panics: none.
    /// - executable: none — the mint that calls it states that every child of
    ///   the node it minted resolves; a predicate here would move the scoping
    ///   through one more closure per node.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::gather_child`]; each producer form is
    ///   supplied live children and one dangling child per referenced family,
    ///   and several dangling children expose a changed failure precedence.
    /// - witness: `il::tests::an_unused_binder_thins_to_zero`
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[inline]
    pub(super) fn producer_scoping(
        &self,
        node: &ProducerNode,
    ) -> Result<Scoping, MintRefusal>
    {
        let mut scoping = Scoping::new();
        scoping.name(producer_named(node), core::iter::empty());
        producer_children(node, |child, opens| {
            self.gather_child(&mut scoping, child, opens)
        })?;
        Ok(scoping)
    }

    /// The scope minting keeps for a consumer: the covariable it names, its
    /// annotations' supports and each child's scope past the binders it
    /// opens.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when every child and annotation of `node`
    ///   resolves, holding the summary's scope.
    /// - fails: as [`Self::gather_annotations`] and [`Self::gather_child`], the
    ///   annotations first, then the first dangling child in edge order.
    /// - panics: none.
    /// - executable: none — as [`Self::producer_scoping`].
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::gather_annotations`]; each consumer form
    ///   is supplied live children and one dangling child per referenced
    ///   family, and several dangling children expose a changed failure
    ///   precedence.
    /// - witness: `il::tests::an_annotation_counts_in_its_nodes_support`
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[inline]
    pub(super) fn consumer_scoping(
        &self,
        node: &ConsumerNode,
    ) -> Result<Scoping, MintRefusal>
    {
        let mut scoping = Scoping::new();
        scoping.name(core::iter::empty(), consumer_named(node));
        self.gather_annotations(&mut scoping, consumer_annotations(node))?;
        consumer_children(node, |child, opens| {
            self.gather_child(&mut scoping, child, opens)
        })?;
        Ok(scoping)
    }

    /// The scope minting keeps for a command: the linear slot it names, its
    /// annotations' supports and each child's scope past the binders it
    /// opens.
    ///
    /// # Specification
    /// - ensures: on success, as the summary states, and every payload and
    ///   reply type of the interface the command carries resolves.
    /// - fails: as [`Self::gather_annotations`] and [`Self::gather_child`], the
    ///   interface first, in canonical operation order.
    /// - panics: none.
    /// - executable: none — as [`Self::producer_scoping`].
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::gather_annotations`]; imported host
    ///   interfaces keep distinct payload and reply types.
    /// - witness: `il::tests::an_annotation_counts_in_its_nodes_support`
    /// - witness: `il::tests::minting_refuses_a_dangling_child`
    /// - witness: `tests::run::hand_built_effect_cases_agree`
    #[inline]
    pub(super) fn command_scoping(
        &self,
        node: &CommandNode,
    ) -> Result<Scoping, MintRefusal>
    {
        let mut scoping = Scoping::new();
        scoping.name(command_named(node), core::iter::empty());
        self.gather_annotations(&mut scoping, command_annotations(node))?;
        command_children(node, |child, opens| {
            self.gather_child(&mut scoping, child, opens)
        })?;
        Ok(scoping)
    }

    /// The slots holding `node`'s scope, or `None` when its address dangles.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn slots(
        &self,
        node: NodeAddress,
    ) -> Option<Slots>
    {
        match node {
            NodeAddress::Producer(id) => id.read_in(&self.producers).map(|row| row.scope),
            NodeAddress::Consumer(id) => id.read_in(&self.consumers).map(|row| row.scope),
            NodeAddress::Command(id) => id.read_in(&self.commands).map(|row| row.scope),
        }
    }

    /// The scope `slots` keep, read in place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn scope_at(
        &self,
        slots: Slots,
    ) -> NodeScope<'_>
    {
        let [producers, covariables] = slots;
        let read = |slot| match self.words.read(slot) {
            Maybe::Present(support) => support,
            // reason: every handle a table holds names words the arena wrote
            // and a truncation drops the row with them.
            Maybe::Absent(_) => ThinningRef::empty(),
        };
        NodeScope {
            producers: read(producers),
            covariables: read(covariables),
        }
    }

    /// The scope a node has, or `None` when its address dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some` exactly when the arena holds the node, holding the
    ///   scope minting kept for it.
    /// - provides: the read side of the scopes, for the crate's own readers and
    ///   for a runtime that closes a suspension over exactly what it names.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    /// - executable: none — read once at a check's root and once per capture;
    ///   the node reads whose own predicates state presence are projections of
    ///   the same families.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope read at a minted node of each family and a
    ///   dangling address separate the three families and the absent case.
    /// - witness: `il::tests::an_unused_binder_thins_to_zero`
    #[inline]
    #[must_use]
    pub fn node_scope(
        &self,
        node: NodeAddress,
    ) -> Option<NodeScope<'_>>
    {
        self.slots(node).map(|slots| self.scope_at(slots))
    }
}
