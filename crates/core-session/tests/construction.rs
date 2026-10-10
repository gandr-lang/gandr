//! Syntax validation and lexical recursion witnesses.

use gandr_core_session::Decision;
use gandr_core_session::Node;
use gandr_core_session::NodeId;
use gandr_core_session::Relation;
use gandr_core_session::Session;
use gandr_core_session::TypeError;
use gandr_core_session::decide;

use crate::common::REPORT;
use crate::common::YIELD;
use crate::common::session;

#[test]
fn malformed_arenas_are_refused()
{
    let cases = [
        (alloc::vec![], TypeError::MissingNode(NodeId(0))),
        (
            alloc::vec![Node::Send(YIELD, NodeId(1))],
            TypeError::MissingNode(NodeId(1)),
        ),
        (
            alloc::vec![Node::Send(YIELD, NodeId(0))],
            TypeError::RepeatedNode(NodeId(0)),
        ),
        (
            alloc::vec![Node::Var(NodeId(0))],
            TypeError::UnboundVariable(NodeId(0)),
        ),
        (
            alloc::vec![Node::Mu(NodeId(1)), Node::Var(NodeId(0))],
            TypeError::NonContractive(NodeId(0)),
        ),
        (
            alloc::vec![Node::Mu(NodeId(1)), Node::Mu(NodeId(2)), Node::End],
            TypeError::NonContractive(NodeId(0)),
        ),
        (
            alloc::vec![Node::End, Node::End],
            TypeError::UnreachableNode(NodeId(1)),
        ),
        (
            alloc::vec![
                Node::Offer([("a".into(), NodeId(1)), ("b".into(), NodeId(1))].into()),
                Node::End
            ],
            TypeError::RepeatedNode(NodeId(1)),
        ),
        (
            alloc::vec![
                Node::Offer([("a".into(), NodeId(1)), ("b".into(), NodeId(4))].into()),
                Node::Var(NodeId(4)),
                Node::End,
                Node::End,
                Node::Mu(NodeId(5)),
                Node::Send(YIELD, NodeId(6)),
                Node::Var(NodeId(4)),
            ],
            TypeError::UnboundVariable(NodeId(1)),
        ),
    ];
    for (nodes, error) in cases {
        assert_eq!(Session::new(nodes, NodeId(0)).err(), Some(error));
    }
    assert_eq!(
        Session::new(alloc::vec![Node::End], NodeId(9)).err(),
        Some(TypeError::MissingNode(NodeId(9)))
    );
}

#[test]
fn nested_binders_preserve_scope()
{
    let nested = session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Send(YIELD, NodeId(2)),
        Node::Mu(NodeId(3)),
        Node::Send(REPORT, NodeId(4)),
        Node::Var(NodeId(0)),
    ]);
    let flat = session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Send(YIELD, NodeId(2)),
        Node::Send(REPORT, NodeId(3)),
        Node::Var(NodeId(0)),
    ]);
    let inner = session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Send(YIELD, NodeId(2)),
        Node::Mu(NodeId(3)),
        Node::Send(REPORT, NodeId(4)),
        Node::Var(NodeId(2)),
    ]);
    assert_eq!(
        decide(&nested, &flat, Relation::Equivalent),
        Ok(Decision::Related)
    );
    assert_eq!(
        decide(&nested, &inner, Relation::Equivalent),
        Ok(Decision::Unrelated)
    );
    let vacuous = session(alloc::vec![Node::Mu(NodeId(1)), Node::End]);
    assert_eq!(
        decide(
            &vacuous,
            &session(alloc::vec![Node::End]),
            Relation::Equivalent
        ),
        Ok(Decision::Related)
    );
}
