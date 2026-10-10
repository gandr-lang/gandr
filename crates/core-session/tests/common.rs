//! Protocol fixtures with independent producer and peer spellings.

use anodized::spec;
use gandr_core_session::Node;
use gandr_core_session::NodeId;
use gandr_core_session::Payload;
use gandr_core_session::PayloadDigest;
use gandr_core_session::Session;
use gandr_core_session::ValueTypeId;

/// Generator yield identity.
pub const YIELD: ValueTypeId = ValueTypeId([1; 32]);
/// Dispatch identity.
pub const DISPATCH: ValueTypeId = ValueTypeId([2; 32]);
/// Report identity.
pub const REPORT: ValueTypeId = ValueTypeId([3; 32]);
/// Handoff identity.
pub const HANDOFF: ValueTypeId = ValueTypeId([4; 32]);

/// Validate a fixture rooted at zero.
///
/// # Specification
/// - requires: nodes form a closed, contractive fixture rooted at zero.
/// - ensures: returns the validated fixture.
/// - panics: an invalid fixture fails construction.
///
/// # Adequacy
/// - hypothesis: L3 finite, recursive, and nested fixtures exercise the valid
///   domain; exact equivalence decisions distinguish discarded continuations.
/// - witness: `tests::construction::nested_binders_preserve_scope`
#[spec(requires: !nodes.is_empty())]
pub fn session(nodes: alloc::vec::Vec<Node>) -> Session
{
    Session::new(nodes, NodeId(0)).expect("fixture is closed and contractive")
}

/// Attach an opaque body digest to its abstract type.
///
/// # Specification
/// trivial.
pub fn payload(identity: ValueTypeId) -> Payload
{
    Payload {
        identity,
        digest: PayloadDigest([0; 32]),
    }
}

/// The generator endpoint, `mu t. &{next: !Y.t, stop: end}`.
///
/// # Specification
/// trivial.
pub fn generator() -> Session
{
    session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Offer([("next".into(), NodeId(2)), ("stop".into(), NodeId(4))].into()),
        Node::Send(YIELD, NodeId(3)),
        Node::Var(NodeId(0)),
        Node::End,
    ])
}

/// The independently stated loop endpoint, `mu t. +{next: ?Y.t, stop: end}`.
///
/// # Specification
/// trivial.
pub fn consumer() -> Session
{
    session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Select([("next".into(), NodeId(2)), ("stop".into(), NodeId(4))].into()),
        Node::Receive(YIELD, NodeId(3)),
        Node::Var(NodeId(0)),
        Node::End,
    ])
}

/// The seat endpoint including report/next/retire and handoff branches.
///
/// # Specification
/// trivial.
pub fn seat() -> Session
{
    session(alloc::vec![
        Node::Receive(DISPATCH, NodeId(1)),
        Node::Mu(NodeId(2)),
        Node::Select([("report".into(), NodeId(3)), ("handoff".into(), NodeId(7))].into()),
        Node::Send(REPORT, NodeId(4)),
        Node::Offer([("next".into(), NodeId(5)), ("retire".into(), NodeId(6))].into()),
        Node::Var(NodeId(1)),
        Node::End,
        Node::Send(HANDOFF, NodeId(8)),
        Node::End,
    ])
}

/// The operator endpoint, stated without calling the dual transformation.
///
/// # Specification
/// trivial.
pub fn operator() -> Session
{
    session(alloc::vec![
        Node::Send(DISPATCH, NodeId(1)),
        Node::Mu(NodeId(2)),
        Node::Offer([("report".into(), NodeId(3)), ("handoff".into(), NodeId(7))].into()),
        Node::Receive(REPORT, NodeId(4)),
        Node::Select([("next".into(), NodeId(5)), ("retire".into(), NodeId(6))].into()),
        Node::Var(NodeId(1)),
        Node::End,
        Node::Receive(HANDOFF, NodeId(8)),
        Node::End,
    ])
}
