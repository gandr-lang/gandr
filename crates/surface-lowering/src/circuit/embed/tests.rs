//! The source-body boundary into actual diagram matching.

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::MatchCount;
use gandr_theory_levitation::CircuitFrame;
use gandr_theory_levitation::CircuitRedex;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::*;

/// One operation with one named input and one named output.
///
/// # Specification
/// trivial.
fn operation(
    head: impl Into<Name>,
    input: impl Into<Name>,
    output: impl Into<Name>,
) -> CircuitNode
{
    CircuitNode::Frame(CircuitFrame::new(
        FrameHead::Op(head.into()),
        [FreeTerm::var(input)],
        output,
    ))
}

/// A nonzero matching allowance for these finite diagrams.
///
/// # Specification
/// trivial.
fn budget() -> MatchBudget
{
    MatchBudget::from(4096_usize)
}

#[test]
fn a_two_line_body_reads_as_a_diagram_with_one_internal_wire()
{
    let body = CircuitBody::new(
        [
            operation("f", "input", "middle"),
            operation("g", "middle", "result"),
        ],
        "result",
    );
    let wiring = circuit_wiring(&body).expect("a two-step chain");
    assert_eq!(wiring.wire_count(), WireCount::from(3_usize));
    assert_eq!(wiring.boundary().inputs(), [Wire::from(0_usize)]);
    assert_eq!(wiring.boundary().outputs(), [Wire::from(2_usize)]);
    assert_eq!(
        wiring.producer_of(Wire::from(1_usize)),
        Maybe::Present(Edge::from(0_usize))
    );
    assert_eq!(
        wiring.consumer_of(Wire::from(1_usize)),
        Maybe::Present(Edge::from(1_usize))
    );
    assert_eq!(wiring.generators()[0].sources(), [Wire::from(0_usize)]);
    assert_eq!(wiring.generators()[1].targets(), [Wire::from(2_usize)]);
}

#[test]
fn a_ground_argument_names_no_wire()
{
    let body = CircuitBody::new(
        [CircuitNode::Frame(CircuitFrame::new(
            FrameHead::Op("f".into()),
            [FreeTerm::ctor("Zero", [])],
            "out",
        ))],
        "out",
    );
    assert_eq!(
        circuit_wiring(&body),
        Err(CircuitWiringError::ArgumentIsNotAPort("Zero".into()))
    );
}

#[test]
fn a_body_binding_one_port_twice_is_not_a_wiring()
{
    let body = CircuitBody::new(
        [
            operation("f", "left", "shared"),
            operation("g", "right", "shared"),
        ],
        "shared",
    );
    assert_eq!(
        circuit_wiring(&body),
        Err(CircuitWiringError::NotAWiring(WiringObstruction::FanIn {
            wire: Wire::from(1_usize),
            first: Edge::from(0_usize),
            second: Edge::from(1_usize),
        }))
    );
}

#[test]
fn a_rule_body_embeds_in_a_body_that_contains_it()
{
    let pattern = CircuitBody::new([operation("f", "x", "y")], "y");
    let target = CircuitBody::new([operation("g", "a", "b"), operation("f", "b", "c")], "c");
    let matching = embed_circuit_rule(&pattern, &target, budget()).expect("bounded match");
    assert_eq!(matching.admitted_count(), MatchCount::from(1_usize));
    let [ref embedding] = *matching.admitted()
    else {
        panic!("one matching occurrence")
    };
    assert_eq!(
        embedding.wires().image_of(Wire::from(0_usize)),
        Maybe::Present(Wire::from(1_usize))
    );
    assert_eq!(
        embedding.wires().image_of(Wire::from(1_usize)),
        Maybe::Present(Wire::from(2_usize))
    );
}

#[test]
fn a_body_that_does_not_contain_the_pattern_admits_no_embedding()
{
    let pattern = CircuitBody::new([operation("f", "x", "y")], "y");
    let target = CircuitBody::new([operation("g", "a", "b")], "b");
    let matching = embed_circuit_rule(&pattern, &target, budget()).expect("completed search");
    assert_eq!(matching.admitted_count(), MatchCount::from(0_usize));
}

#[test]
fn one_spelling_in_two_roles_is_two_boxes()
{
    let operation_body = CircuitBody::new([operation("same", "a", "b")], "b");
    let constructor = CircuitNode::Frame(CircuitFrame::new(
        FrameHead::Ctor("same".into()),
        [FreeTerm::var("x")],
        "y",
    ));
    let rewrite = CircuitNode::Redex(CircuitRedex::new(
        "same",
        FreeTerm::var("x"),
        FreeTerm::var("y"),
        "y",
    ));
    for node in [constructor, rewrite] {
        let pattern = CircuitBody::new([node], "y");
        let matching =
            embed_circuit_rule(&pattern, &operation_body, budget()).expect("completed search");
        assert_eq!(matching.admitted_count(), MatchCount::from(0_usize));
    }
}

#[test]
fn an_exhausted_budget_declines_rather_than_reporting_no_match()
{
    let pattern = CircuitBody::new([operation("f", "x", "y")], "y");
    assert!(matches!(
        embed_circuit_rule(&pattern, &pattern, MatchBudget::from(0_usize)),
        Err(CircuitEmbedError::Matching(_))
    ));
}
