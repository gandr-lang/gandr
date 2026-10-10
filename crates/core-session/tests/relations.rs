//! Coinductive relations against an independent finite elimination oracle.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_session::Decision;
use gandr_core_session::Node;
use gandr_core_session::NodeId;
use gandr_core_session::Relation;
use gandr_core_session::Session;
use gandr_core_session::decide;
use gandr_core_session::duality;

use crate::common::REPORT;
use crate::common::YIELD;
use crate::common::session;

#[test]
fn unfolded_recursive_types_are_equivalent()
{
    let folded = session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Send(YIELD, NodeId(2)),
        Node::Var(NodeId(0))
    ]);
    let unfolded = session(alloc::vec![
        Node::Send(YIELD, NodeId(1)),
        Node::Mu(NodeId(2)),
        Node::Send(YIELD, NodeId(3)),
        Node::Var(NodeId(1))
    ]);
    let different = session(alloc::vec![
        Node::Send(REPORT, NodeId(1)),
        Node::Mu(NodeId(2)),
        Node::Send(YIELD, NodeId(3)),
        Node::Var(NodeId(1))
    ]);
    for relation in [Relation::Equivalent, Relation::Subtype] {
        assert_eq!(decide(&folded, &unfolded, relation), Ok(Decision::Related));
        assert_eq!(decide(&unfolded, &folded, relation), Ok(Decision::Related));
        assert_eq!(
            decide(&folded, &different, relation),
            Ok(Decision::Unrelated)
        );
        assert_eq!(
            decide(&different, &folded, relation),
            Ok(Decision::Unrelated)
        );
    }
    assert_eq!(duality(&folded, &unfolded.dual()), Ok(Decision::Related));
}

#[test]
fn choice_width_and_continuations_are_directional()
{
    let narrow = session(alloc::vec![
        Node::Select([("a".into(), NodeId(1))].into()),
        Node::End
    ]);
    let wide = session(alloc::vec![
        Node::Select([("a".into(), NodeId(1)), ("b".into(), NodeId(2))].into()),
        Node::End,
        Node::End
    ]);
    assert_eq!(
        decide(&narrow, &wide, Relation::Subtype),
        Ok(Decision::Related)
    );
    assert_eq!(
        decide(&wide, &narrow, Relation::Subtype),
        Ok(Decision::Unrelated)
    );
    assert_eq!(
        decide(&wide.dual(), &narrow.dual(), Relation::Subtype),
        Ok(Decision::Related)
    );
    assert_eq!(
        decide(&narrow.dual(), &wide.dual(), Relation::Subtype),
        Ok(Decision::Unrelated)
    );
    for (left, right) in [
        (&narrow, &wide),
        (&wide, &narrow),
        (&narrow.dual(), &wide.dual()),
    ] {
        assert_eq!(
            decide(left, right, Relation::Equivalent),
            Ok(Decision::Unrelated)
        );
    }
    // Reversing offer-width inclusion must not reverse continuation subtyping.
    let offer_narrow = session(alloc::vec![
        Node::Offer([("x".into(), NodeId(1))].into()),
        Node::Select([("a".into(), NodeId(2))].into()),
        Node::End,
    ]);
    let offer_wide = session(alloc::vec![
        Node::Offer([("x".into(), NodeId(1))].into()),
        Node::Select([("a".into(), NodeId(2)), ("b".into(), NodeId(3))].into()),
        Node::End,
        Node::End,
    ]);
    assert_eq!(
        decide(&offer_narrow, &offer_wide, Relation::Subtype),
        Ok(Decision::Related)
    );
    assert_eq!(
        decide(&offer_wide, &offer_narrow, Relation::Subtype),
        Ok(Decision::Unrelated)
    );
    // A successful recursive branch cannot hide a different terminal branch.
    let good = session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Offer([("loop".into(), NodeId(2)), ("stop".into(), NodeId(3))].into()),
        Node::Var(NodeId(0)),
        Node::End
    ]);
    let bad = session(alloc::vec![
        Node::Mu(NodeId(1)),
        Node::Offer([("loop".into(), NodeId(2)), ("stop".into(), NodeId(3))].into()),
        Node::Var(NodeId(0)),
        Node::Send(YIELD, NodeId(4)),
        Node::End
    ]);
    assert_eq!(
        decide(&good, &bad, Relation::Equivalent),
        Ok(Decision::Unrelated)
    );
    assert_eq!(
        decide(&good, &bad, Relation::Subtype),
        Ok(Decision::Unrelated)
    );
}

/// Whether reference comparison observes matching or peer actions.
#[derive(Clone, Copy)]
enum Polarity
{
    /// Actions have the same endpoint direction.
    Same,
    /// Actions have opposite endpoint directions.
    Opposite,
}

/// A generated syntax tree paired with its separately indexed finite machine.
struct Sample
{
    /// Validated production input.
    syntax: Session,
    /// Observable states only, rooted at zero; no `Mu` or `Var` nodes.
    machine: Vec<Node>,
}

/// Interpret one finite-machine pair using the current candidate relation.
///
/// # Specification
/// - requires: both nodes are observable states, not recursion syntax.
/// - ensures: returns membership in the one-step simulation/bisimulation
///   operator; opposite polarity swaps peer directions without a type
///   transform.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 this oracle removes invalid pairs from the full product,
///   independently of the production root-driven visited-set algorithm.
/// - witness: `tests::relations::generated_relations_match_finite_oracle`
fn compatible(
    left: &Node,
    right: &Node,
    relation: Relation,
    polarity: Polarity,
    candidates: &BTreeSet<(NodeId, NodeId)>,
) -> Decision
{
    let compatible = match (left, right, polarity) {
        | (&Node::End, &Node::End, _) => true,
        | (&Node::Send(a, x), &Node::Send(b, y), Polarity::Same)
        | (&Node::Receive(a, x), &Node::Receive(b, y), Polarity::Same)
        | (&Node::Send(a, x), &Node::Receive(b, y), Polarity::Opposite)
        | (&Node::Receive(a, x), &Node::Send(b, y), Polarity::Opposite) => {
            a == b && candidates.contains(&(x, y))
        },
        | (&Node::Select(ref a), &Node::Select(ref b), Polarity::Same)
        | (&Node::Select(ref a), &Node::Offer(ref b), Polarity::Opposite) => {
            a.iter()
                .all(|(label, x)| b.get(label).is_some_and(|y| candidates.contains(&(*x, *y))))
                && (relation == Relation::Subtype || b.keys().all(|label| a.contains_key(label)))
        },
        | (&Node::Offer(ref a), &Node::Offer(ref b), Polarity::Same)
        | (&Node::Offer(ref a), &Node::Select(ref b), Polarity::Opposite) => {
            b.iter()
                .all(|(label, y)| a.get(label).is_some_and(|x| candidates.contains(&(*x, *y))))
                && (relation == Relation::Subtype || a.keys().all(|label| b.contains_key(label)))
        },
        | _ => false,
    };
    if compatible {
        Decision::Related
    }
    else {
        Decision::Unrelated
    }
}

/// Eliminate invalid pairs from the full finite state product to convergence.
///
/// # Specification
/// - requires: all machine edges address observable states in their own vector.
/// - ensures: returns root membership in the greatest fixed point of the
///   independently applied one-step relation operator.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 finite elimination supplies a second algorithm rather than
///   a mirror of production worklist scheduling or unfolding.
/// - witness: `tests::relations::generated_relations_match_finite_oracle`
fn reference(
    left: &[Node],
    right: &[Node],
    relation: Relation,
    polarity: Polarity,
) -> Decision
{
    let mut candidates: BTreeSet<_> = left
        .iter()
        .enumerate()
        .flat_map(|(a, _)| {
            right
                .iter()
                .enumerate()
                .map(move |(b, _)| (NodeId(a), NodeId(b)))
        })
        .collect();
    // Each changing pass removes at least one pair; the finite product bounds it.
    for _pass in 0 ..= candidates.len() {
        let before = candidates.clone();
        candidates.retain(|&(NodeId(a), NodeId(b))| {
            compatible(&left[a], &right[b], relation, polarity, &before) == Decision::Related
        });
        if candidates == before {
            break;
        }
    }
    if candidates.contains(&(NodeId(0), NodeId(0))) {
        Decision::Related
    }
    else {
        Decision::Unrelated
    }
}

/// An action alphabet covering both payload identities and both directions.
#[derive(Clone, Copy)]
enum Symbol
{
    /// Send the first identity.
    SendYield,
    /// Receive the first identity.
    ReceiveYield,
    /// Send a distinct identity.
    SendReport,
    /// Receive a distinct identity.
    ReceiveReport,
}

/// Termination or a back edge after a generated word.
#[derive(Clone, Copy)]
enum Tail
{
    /// Close after the word.
    End,
    /// Repeat the entire nonempty word.
    Repeat,
}

/// Assemble independent syntax and finite-state indexes for a word.
///
/// # Specification
/// trivial.
fn word_sample(
    word: &[Symbol],
    tail: Tail,
) -> Sample
{
    let mut nodes = Vec::new();
    let mut machine = Vec::new();
    if matches!(tail, Tail::Repeat) {
        nodes.push(Node::Mu(NodeId(1)));
    }
    for (index, symbol) in word.iter().enumerate() {
        let next = index.saturating_add(1);
        let model_next = if next == word.len() && matches!(tail, Tail::Repeat) {
            NodeId(0)
        }
        else {
            NodeId(next)
        };
        let syntax_next = NodeId(nodes.len().saturating_add(1));
        let (syntax, model) = match *symbol {
            | Symbol::SendYield => (
                Node::Send(YIELD, syntax_next),
                Node::Send(YIELD, model_next),
            ),
            | Symbol::ReceiveYield => (
                Node::Receive(YIELD, syntax_next),
                Node::Receive(YIELD, model_next),
            ),
            | Symbol::SendReport => (
                Node::Send(REPORT, syntax_next),
                Node::Send(REPORT, model_next),
            ),
            | Symbol::ReceiveReport => (
                Node::Receive(REPORT, syntax_next),
                Node::Receive(REPORT, model_next),
            ),
        };
        nodes.push(syntax);
        machine.push(model);
    }
    match tail {
        | Tail::End => {
            nodes.push(Node::End);
            machine.push(Node::End);
        },
        | Tail::Repeat => nodes.push(Node::Var(NodeId(0))),
    }
    Sample {
        syntax: session(nodes),
        machine,
    }
}

/// Enumerate words through length three and recursive choices over two labels.
///
/// # Specification
/// trivial.
fn samples() -> Vec<Sample>
{
    let mut samples = alloc::vec![word_sample(&[], Tail::End)];
    let mut words = alloc::vec![Vec::new()];
    for _depth in 0 .. 3_u8 {
        let mut next = Vec::new();
        for word in words {
            for symbol in [
                Symbol::SendYield,
                Symbol::ReceiveYield,
                Symbol::SendReport,
                Symbol::ReceiveReport,
            ] {
                let mut extended = word.clone();
                extended.push(symbol);
                samples.push(word_sample(&extended, Tail::End));
                samples.push(word_sample(&extended, Tail::Repeat));
                next.push(extended);
            }
        }
        words = next;
    }
    for mask in 0 .. 4_u8 {
        for polarity in [Polarity::Same, Polarity::Opposite] {
            let mut branches = BTreeMap::new();
            let mut model = BTreeMap::new();
            let mut nodes = alloc::vec![Node::Mu(NodeId(1)), Node::End];
            let mut machine = alloc::vec![Node::End];
            if mask & 1 != 0 {
                branches.insert("again".into(), NodeId(nodes.len()));
                nodes.push(Node::Var(NodeId(0)));
                model.insert("again".into(), NodeId(0));
            }
            if mask & 2 != 0 {
                branches.insert("stop".into(), NodeId(nodes.len()));
                nodes.push(Node::End);
                model.insert("stop".into(), NodeId(1));
                machine.push(Node::End);
            }
            nodes[1] = match polarity {
                | Polarity::Same => Node::Select(branches),
                | Polarity::Opposite => Node::Offer(branches),
            };
            machine[0] = match polarity {
                | Polarity::Same => Node::Select(model),
                | Polarity::Opposite => Node::Offer(model),
            };
            samples.push(Sample {
                syntax: session(nodes),
                machine,
            });
        }
    }
    samples
}

#[test]
fn generated_relations_match_finite_oracle()
{
    let samples = samples();
    assert_eq!(samples.len(), 177, "finite domain: 169 words and 8 choices");
    for left in &samples {
        for right in &samples {
            for relation in [Relation::Equivalent, Relation::Subtype] {
                assert_eq!(
                    decide(&left.syntax, &right.syntax, relation),
                    Ok(reference(
                        &left.machine,
                        &right.machine,
                        relation,
                        Polarity::Same
                    ))
                );
            }
            assert_eq!(
                duality(&left.syntax, &right.syntax),
                Ok(reference(
                    &left.machine,
                    &right.machine,
                    Relation::Equivalent,
                    Polarity::Opposite
                ))
            );
        }
        assert_eq!(
            decide(
                &left.syntax,
                &left.syntax.dual().dual(),
                Relation::Equivalent
            ),
            Ok(Decision::Related)
        );
    }
}
