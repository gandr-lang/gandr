//! Allocation-only nominal tree handles and arena-resident name-bearing terms.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;

use crate::handle::Allocation;
use crate::handle::Arity;
use crate::handle::AutomatonError;
use crate::handle::Configuration;
use crate::handle::Control;
use crate::handle::Degree;
use crate::handle::Register;
use crate::handle::Transfer;
use crate::handle::arity_at;
use crate::handle::validate_initial;
use crate::handle::validate_transfer;

/// A node index in one term arena; child references must point backward.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermId(usize);
impl From<usize> for TermId
{
    /// Wrap an index; arena methods validate it before use.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

/// Whether a term node uses or binds its name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NameKind<A>
{
    /// A free occurrence at this node.
    Free(A),
    /// A binder whose scope covers the node's children.
    Bound(A),
}

/// A flat term node whose children are arena indices.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermNode<A, F>
{
    /// The name occurrence or binder.
    name: NameKind<A>,
    /// The signature symbol.
    symbol: F,
    /// Ordered child indices.
    children: Vec<TermId>,
}
impl<A, F> TermNode<A, F>
{
    /// Construct a free-name node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn free(
        name: A,
        symbol: F,
        children: Vec<TermId>,
    ) -> Self
    {
        Self {
            name: NameKind::Free(name),
            symbol,
            children,
        }
    }
    /// Construct a binder over its child terms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn bound(
        name: A,
        symbol: F,
        children: Vec<TermId>,
    ) -> Self
    {
        Self {
            name: NameKind::Bound(name),
            symbol,
            children,
        }
    }
    /// The node name and its binding role.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn name(&self) -> &NameKind<A>
    {
        &self.name
    }

    /// The signature symbol.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn symbol(&self) -> &F
    {
        &self.symbol
    }

    /// The ordered child indices.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn children(&self) -> &[TermId]
    {
        &self.children
    }
}

/// An absent or forward term reference.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TermError
{
    /// The invalid reference.
    pub node: TermId,
}
impl core::fmt::Display for TermError
{
    /// Render the unknown term index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(f, "unknown term node {}", self.node.0)
    }
}
impl core::error::Error for TermError
{
}

/// A flat arena of acyclic name-bearing terms, with sharing by child index.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term<A, F>
{
    /// Nodes in child-before-parent order.
    nodes: Vec<TermNode<A, F>>,
}
impl<A, F> Default for Term<A, F>
{
    /// An empty arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self { nodes: Vec::new() }
    }
}
impl<A, F> Term<A, F>
{
    /// Append a node whose children already exist.
    ///
    /// # Specification
    /// - ensures: success retains child-before-parent order; failure leaves the
    ///   arena unchanged.
    /// - fails: the first child index outside the current arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `TermError` for an absent or forward child.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a forward child is refused without consuming an index;
    ///   a deep unary term can be traversed and destroyed without recursion.
    /// - witness: `tests::validation::flat_terms_refuse_forward_children_and_handle_deep_scope`
    #[inline]
    #[spec(captures: [length = self.nodes.len()], ensures: |result| match result { Ok(id) => id.0 == length && self.nodes.len() == length.saturating_add(1), Err(_) => self.nodes.len() == length })]
    pub fn push(
        &mut self,
        node: TermNode<A, F>,
    ) -> Result<TermId, TermError>
    {
        for child in &node.children {
            if child.0 >= self.nodes.len() {
                return Err(TermError { node: *child });
            }
        }
        let id = TermId(self.nodes.len());
        self.nodes.push(node);
        Ok(id)
    }

    /// Read a node by index.
    ///
    /// # Specification
    /// - ensures: returns exactly the node at the supplied index.
    /// - fails: an unknown index is reported without mutation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `TermError` outside the arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a refused child and valid leaf separate lookup
    ///   boundaries.
    /// - witness: `tests::validation::flat_terms_refuse_forward_children_and_handle_deep_scope`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == (id.0 < self.nodes.len()))]
    pub fn node(
        &self,
        id: TermId,
    ) -> Result<&TermNode<A, F>, TermError>
    {
        self.nodes.get(id.0).ok_or(TermError { node: id })
    }
}

/// One iterative scope-walk instruction.
#[derive(Clone, Copy)]
enum Walk<A>
{
    /// Visit a node under the active binders.
    Enter(TermId),
    /// Leave one occurrence of a binder.
    Leave(A),
}
impl<A: Copy + Ord, F> Term<A, F>
{
    /// Compute free names under lexical binder scope.
    ///
    /// # Specification
    /// - ensures: a name is returned exactly when a free occurrence under
    ///   `root` has no ancestor binder of the same name; sibling scopes are
    ///   independent.
    /// - fails: an unknown root is reported before traversal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `TermError` for an unknown root.
    ///
    /// # Adequacy
    /// - hypothesis: L3 nested equal binders, free siblings and a shared node
    ///   in two scopes distinguish shadowing from global name removal.
    /// - witness: `tests::rnta::free_names_respects_binder_shadowing`
    /// - witness: `tests::validation::flat_terms_refuse_forward_children_and_handle_deep_scope`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == (root.0 < self.nodes.len()))]
    pub fn free_names(
        &self,
        root: TermId,
    ) -> Result<BTreeSet<A>, TermError>
    {
        self.node(root)?;
        let mut work = alloc::vec![Walk::Enter(root)];
        let mut bound: BTreeMap<A, usize> = BTreeMap::new();
        let mut free = BTreeSet::new();
        while let Some(step) = work.pop() {
            match step {
                | Walk::Leave(name) => {
                    if let Some(count) = bound.get_mut(&name) {
                        *count = count.saturating_sub(1);
                        if *count == 0 {
                            bound.remove(&name);
                        }
                    }
                },
                | Walk::Enter(id) => {
                    let node = self.node(id)?;
                    match node.name {
                        | NameKind::Free(name) => {
                            if !bound.contains_key(&name) {
                                free.insert(name);
                            }
                        },
                        | NameKind::Bound(name) => {
                            let count = bound.entry(name).or_default();
                            *count = count.saturating_add(1);
                            work.push(Walk::Leave(name));
                        },
                    }
                    work.extend(node.children.iter().rev().map(|id| Walk::Enter(*id)));
                },
            }
        }
        Ok(free)
    }
}

/// The name constraint on a tree rewrite rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeKind
{
    /// Read a remembered name.
    FreeName
    {
        /// The source register.
        register: Register,
    },
    /// Allocate a fresh binder name.
    Allocate,
}
/// A child control and the transfer preparing its store.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChildTarget
{
    /// The child control.
    control: Control,
    /// The child store assignment.
    transfer: Vec<Transfer>,
}
impl ChildTarget
{
    /// Pair a child control with its transfer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        control: Control,
        transfer: Vec<Transfer>,
    ) -> Self
    {
        Self { control, transfer }
    }
    /// The child control.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn control(&self) -> Control
    {
        self.control
    }

    /// The child assignment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn transfer(&self) -> &[Transfer]
    {
        &self.transfer
    }
}
/// A symbolic tree rewrite with one target for each ordered child.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RntaRule<F>
{
    /// The source control.
    source: Control,
    /// The matched signature symbol.
    symbol: F,
    /// The name constraint.
    kind: NodeKind,
    /// Ordered child targets; their count gives this rule's rank.
    children: Vec<ChildTarget>,
}
impl<F> RntaRule<F>
{
    /// Construct a symbolic tree rewrite.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        source: Control,
        symbol: F,
        kind: NodeKind,
        children: Vec<ChildTarget>,
    ) -> Self
    {
        Self {
            source,
            symbol,
            kind,
            children,
        }
    }
    /// The source control.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn source(&self) -> Control
    {
        self.source
    }

    /// The matched symbol.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn symbol(&self) -> &F
    {
        &self.symbol
    }

    /// The name constraint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn kind(&self) -> NodeKind
    {
        self.kind
    }

    /// The ordered child targets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn children(&self) -> &[ChildTarget]
    {
        &self.children
    }
}
/// A validated finite handle for an allocation-only nominal tree automaton.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rnta<A, F>
{
    /// The control arities.
    arities: Vec<Arity>,
    /// The initial configuration.
    initial: Configuration<A>,
    /// The symbolic rewrite rules.
    rules: Vec<RntaRule<F>>,
}
impl<A: Copy + Ord, F> Rnta<A, F>
{
    /// Validate a tree handle and each child transfer independently.
    ///
    /// # Specification
    /// - ensures: controls, reads and child arities are valid; each child
    ///   transfer is injective and may store an allocated name only on a binder
    ///   rule.
    /// - fails: returns the first structural automaton error.
    /// - panics: none.
    ///
    /// # Errors
    /// Invalid controls, arities, reads, repeated registers or misplaced
    /// allocations.
    ///
    /// # Adequacy
    /// - hypothesis: L3 two children may each retain the allocated name;
    ///   invalid reads and free-rule allocations fail independently.
    /// - witness: `tests::rnta::construction_accepts_a_well_formed_rnta`
    /// - witness: `tests::rnta::construction_rejects_unknown_register`
    /// - witness: `tests::rnta::construction_rejects_misplaced_allocated_name`
    /// - witness: `tests::validation::transfers_preserve_partial_injections`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |automaton| automaton.arities.get(usize::from(automaton.initial.control())) == Some(&automaton.initial.store().arity())))]
    pub fn new(
        arities: Vec<Arity>,
        initial: Configuration<A>,
        rules: Vec<RntaRule<F>>,
    ) -> Result<Self, AutomatonError>
    {
        validate_initial(&arities, &initial)?;
        for rule in &rules {
            let source_arity = arity_at(&arities, rule.source)?;
            let allocation = match rule.kind {
                | NodeKind::FreeName { register } => {
                    if usize::from(register) >= usize::from(source_arity) {
                        return Err(AutomatonError::UnknownRegister {
                            control: rule.source,
                            register,
                        });
                    }
                    Allocation::Forbidden
                },
                | NodeKind::Allocate => Allocation::Allowed,
            };
            for child in &rule.children {
                validate_transfer(
                    &arities,
                    rule.source,
                    child.control,
                    &child.transfer,
                    allocation,
                )?;
            }
        }
        Ok(Self {
            arities,
            initial,
            rules,
        })
    }
    /// The control arities.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arities(&self) -> &[Arity]
    {
        &self.arities
    }

    /// The initial configuration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn initial(&self) -> &Configuration<A>
    {
        &self.initial
    }

    /// The rewrite rules.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[RntaRule<F>]
    {
        &self.rules
    }

    /// The maximum declared register arity.
    ///
    /// # Specification
    /// - ensures: returns the maximum arity across controls.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 the empty initial and occupied children distinguish
    ///   maximum from initial arity.
    /// - witness: `tests::rnta::construction_accepts_a_well_formed_rnta`
    #[inline]
    #[must_use]
    #[spec(ensures: |result| self.arities.iter().all(|arity| usize::from(*arity) <= usize::from(result)) && self.arities.iter().any(|arity| usize::from(*arity) == usize::from(result)))]
    pub fn degree(&self) -> Degree
    {
        Degree::from(
            self.arities
                .iter()
                .map(|arity| usize::from(*arity))
                .max()
                .unwrap_or(0),
        )
    }
}
