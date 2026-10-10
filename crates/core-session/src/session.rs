//! Closed, contractive syntax in a flat arena.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

/// A position in one session's syntax arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct NodeId(pub usize);

/// An opaque payload-type identity assigned by the protocol's owner.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ValueTypeId(pub [u8; 32]);

/// A protocol branch name, compared by exact spelling.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Label(pub String);

impl From<&str> for Label
{
    /// Own a branch name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &str) -> Self
    {
        Self(String::from(value))
    }
}

/// One node of finite session syntax; only variables form recursive edges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Node
{
    /// Send a payload, then follow the continuation.
    Send(ValueTypeId, NodeId),
    /// Receive a payload, then follow the continuation.
    Receive(ValueTypeId, NodeId),
    /// Choose one label.
    Select(BTreeMap<Label, NodeId>),
    /// Accept one label chosen by the peer.
    Offer(BTreeMap<Label, NodeId>),
    /// Close the endpoint.
    End,
    /// Bind recursion over the body.
    Mu(NodeId),
    /// Refer to an enclosing `Mu` node by its arena identity.
    Var(NodeId),
}

/// The observable action at an unfolded session state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Action
{
    /// A send with the expected payload type.
    Send(ValueTypeId),
    /// A receive with the expected payload type.
    Receive(ValueTypeId),
    /// A local label selection.
    Select,
    /// A peer label selection.
    Offer,
    /// Endpoint closure.
    End,
}

/// A malformed syntax arena or a broken arena reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeError
{
    /// An edge or root names no node.
    MissingNode(NodeId),
    /// A structural edge revisits syntax; use a variable for recursion.
    RepeatedNode(NodeId),
    /// A variable does not name an enclosing recursion binder.
    UnboundVariable(NodeId),
    /// A recursion body starts with `Mu` or `Var`.
    NonContractive(NodeId),
    /// Some arena node is outside the rooted syntax tree.
    UnreachableNode(NodeId),
}

impl core::fmt::Display for TypeError
{
    /// Describe the failed construction rule and node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::MissingNode(NodeId(id)) => write!(f, "missing session node {id}"),
            | Self::RepeatedNode(NodeId(id)) => write!(f, "repeated structural node {id}"),
            | Self::UnboundVariable(NodeId(id)) => write!(f, "unbound session variable {id}"),
            | Self::NonContractive(NodeId(id)) => write!(f, "non-contractive recursion {id}"),
            | Self::UnreachableNode(NodeId(id)) => write!(f, "unreachable session node {id}"),
        }
    }
}

impl core::error::Error for TypeError
{
}

/// A closed session type whose recursion is guarded by observable actions.
///
/// # Specification
/// - provides: an immutable syntax tree with in-scope recursive back edges;
///   every `Mu` body is an action or `End`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 malformed arenas distinguish closure, tree, and guard
///   checks; recursive relation witnesses observe the accepted semantics.
/// - witness: `tests::construction::malformed_arenas_are_refused`
/// - witness: `tests::relations::unfolded_recursive_types_are_equivalent`
#[derive(Clone, Debug)]
pub struct Session
{
    /// The exclusively owned syntax tree, including variable leaves.
    nodes: Vec<Node>,
    /// The root of the syntax tree.
    root: NodeId,
}

/// Construction obligations; leaving a binder restores lexical scope.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// Visit a structural node.
    Enter(NodeId),
    /// Remove a binder after its entire body has been visited.
    Leave(NodeId),
}

impl Session
{
    /// The root identity of this validated syntax tree.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn root(&self) -> NodeId
    {
        self.root
    }

    /// Validate and own a closed, contractive session syntax tree.
    ///
    /// # Specification
    /// - ensures: every structural node occurs once and every variable names an
    ///   enclosing `Mu`; bodies of `Mu` start with an action or `End`.
    /// - fails: missing roots/edges, repeated structural nodes, unbound
    ///   variables, unguarded recursion, and unreachable nodes are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the corresponding [`TypeError`] with the offending node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exact refusals distinguish malformed edges, sibling
    ///   scope escape, structural cycles/sharing, and both unguarded heads.
    /// - witness: `tests::construction::malformed_arenas_are_refused`
    /// - witness: `tests::construction::nested_binders_preserve_scope`
    #[inline]
    pub fn new(
        nodes: Vec<Node>,
        root: NodeId,
    ) -> Result<Self, TypeError>
    {
        let session = Self { nodes, root };
        let mut seen = BTreeSet::new();
        let mut binders = BTreeSet::new();
        let mut pending = alloc::vec![Visit::Enter(root)];
        while let Some(visit) = pending.pop() {
            let id = match visit {
                | Visit::Leave(id) => {
                    binders.remove(&id);
                    continue;
                },
                | Visit::Enter(id) => id,
            };
            let node = session.node(id)?;
            if !seen.insert(id) {
                return Err(TypeError::RepeatedNode(id));
            }
            match node {
                | &Node::Send(_, next) | &Node::Receive(_, next) => {
                    pending.push(Visit::Enter(next));
                },
                | &Node::Select(ref branches) | &Node::Offer(ref branches) => {
                    pending.extend(branches.values().copied().map(Visit::Enter));
                },
                | &Node::Mu(body) => {
                    let body_node = session.node(body)?;
                    if matches!(*body_node, Node::Mu(_) | Node::Var(_)) {
                        return Err(TypeError::NonContractive(id));
                    }
                    binders.insert(id);
                    pending.push(Visit::Leave(id));
                    pending.push(Visit::Enter(body));
                },
                | &Node::Var(binder) => {
                    if !binders.contains(&binder) {
                        return Err(TypeError::UnboundVariable(id));
                    }
                },
                | &Node::End => {},
            }
        }
        for (index, _) in session.nodes.iter().enumerate() {
            let id = NodeId(index);
            if !seen.contains(&id) {
                return Err(TypeError::UnreachableNode(id));
            }
        }
        Ok(session)
    }

    /// Transform every action into its peer action, preserving binding.
    ///
    /// # Specification
    /// - ensures: send/receive and select/offer swap; payload identities,
    ///   labels, continuations, recursion binding, and end are preserved.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 explicit independent protocol duals and L3 all former
    ///   pairs distinguish missed swaps and changed payloads or bindings.
    /// - witness: `tests::protocols::generator_duality_and_two_yields`
    /// - witness: `tests::protocols::seat_duality_report_and_handoff`
    /// - witness: `tests::relations::generated_relations_match_finite_oracle`
    #[inline]
    #[must_use]
    pub fn dual(&self) -> Self
    {
        let nodes = self
            .nodes
            .iter()
            .map(|node| match node {
                | &Node::Send(payload, next) => Node::Receive(payload, next),
                | &Node::Receive(payload, next) => Node::Send(payload, next),
                | &Node::Select(ref branches) => Node::Offer(branches.clone()),
                | &Node::Offer(ref branches) => Node::Select(branches.clone()),
                | &Node::End => Node::End,
                | &Node::Mu(body) => Node::Mu(body),
                | &Node::Var(binder) => Node::Var(binder),
            })
            .collect();
        Self {
            nodes,
            root: self.root,
        }
    }

    /// Look up a syntax node without partial indexing.
    ///
    /// # Specification
    /// - ensures: returns exactly the node at `id`.
    /// - fails: `MissingNode(id)` if the position is outside the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`TypeError::MissingNode`] for an out-of-arena identity.
    ///
    /// # Adequacy
    /// - hypothesis: L3 invalid root and continuation distinguish lookup
    ///   bounds.
    /// - witness: `tests::construction::malformed_arenas_are_refused`
    pub(crate) fn node(
        &self,
        id: NodeId,
    ) -> Result<&Node, TypeError>
    {
        // Arena indexing has no domain trait; the primitive stays local.
        self.nodes.get(id.0).ok_or(TypeError::MissingNode(id))
    }

    /// Expose the action reached by administrative unfolding.
    ///
    /// # Specification
    /// - ensures: returns the first action and its syntax identity; unfolding
    ///   preserves the binding of every recursive occurrence.
    /// - fails: malformed internal edges retain their construction refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`TypeError`] only for a broken internal arena invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 nested binders and one-unfold comparisons distinguish
    ///   binder confusion and syntactic rather than coinductive comparison.
    /// - witness: `tests::construction::nested_binders_preserve_scope`
    /// - witness: `tests::relations::unfolded_recursive_types_are_equivalent`
    pub(crate) fn head(
        &self,
        mut id: NodeId,
    ) -> Result<(NodeId, &Node), TypeError>
    {
        // At most Var -> Mu -> action; construction rejects administrative cycles.
        for _step in 0 .. 3_u8 {
            let node = self.node(id)?;
            match node {
                | &Node::Mu(body) | &Node::Var(body) => id = body,
                | node => return Ok((id, node)),
            }
        }
        Err(TypeError::NonContractive(id))
    }
}

impl Node
{
    /// Classify an observable node without unfolding.
    ///
    /// # Specification
    /// - ensures: returns the node's endpoint action and payload identity.
    /// - fails: administrative nodes are refused as non-contractive heads.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`TypeError::NonContractive`] when given `Mu` or `Var`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 every action and wrong-direction twin distinguishes the
    ///   observable classifications used by replay.
    /// - witness: `tests::monitor::refusals_preserve_the_accepted_prefix`
    pub(crate) fn action(
        &self,
        id: NodeId,
    ) -> Result<Action, TypeError>
    {
        match *self {
            | Self::Send(payload, _) => Ok(Action::Send(payload)),
            | Self::Receive(payload, _) => Ok(Action::Receive(payload)),
            | Self::Select(_) => Ok(Action::Select),
            | Self::Offer(_) => Ok(Action::Offer),
            | Self::End => Ok(Action::End),
            | Self::Mu(_) | Self::Var(_) => Err(TypeError::NonContractive(id)),
        }
    }
}
