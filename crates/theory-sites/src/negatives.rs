//! Why the site's objects are stick-free: one test per alternative the
//! crate root's decisions reject, each asserting the one fact that rules it
//! out.
//!
//! The data are raw carrier wirings read as graphs before admission, so a
//! bare wire, which no shape holds, can be validated by the same clauses as
//! the site's maps.

use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::WiringObstruction;

use crate::catalogue::Catalogue;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::map::homs;
use crate::shape::Graph;
use crate::shape::Shape;
use crate::shape::ShapeKey;
use crate::shape::ShapeObstruction;
use crate::shape::ShapeSize;
use crate::shape::WireKind;
use crate::shape::presented;

/// The raw wiring of `count` bare wires side by side: no generator, each
/// wire both an input and an output port.
///
/// # Specification
/// trivial.
fn bare_wires(count: WireCount) -> Wiring
{
    let wires: Vec<Wire> = (0 .. usize::from(count)).map(Wire::from).collect();
    Wiring::assemble(count, vec![], Interface::new(wires.clone(), wires))
        .expect("the carrier admits bare wires")
}

/// One generator label for every fixture.
///
/// # Specification
/// trivial.
fn label() -> GeneratorLabel
{
    GeneratorLabel::new("g", GeneratorSort::Value)
}

/// The raw wiring of the corolla `C(1,1)`: one generator consuming the input
/// wire 0 and producing the output wire 1.
///
/// # Specification
/// trivial.
fn corolla() -> Wiring
{
    Wiring::assemble(
        WireCount::from(2),
        vec![Generator::new(label(), vec![Wire::from(0)], vec![
            Wire::from(1),
        ])],
        Interface::new(vec![Wire::from(0)], vec![Wire::from(1)]),
    )
    .expect("the carrier admits the corolla")
}

/// The raw wiring of the closed chain `p→q`: `p` produces wire 0 and `q`
/// consumes it.
///
/// # Specification
/// trivial.
fn closed_chain() -> Wiring
{
    Wiring::assemble(
        WireCount::from(1),
        vec![
            Generator::new(label(), vec![], vec![Wire::from(0)]),
            Generator::new(label(), vec![Wire::from(0)], vec![]),
        ],
        Interface::default(),
    )
    .expect("the carrier admits the closed chain")
}

/// Keeping sticks as objects leaves no degree: the inclusion `↑ → ↑↑` is a
/// non-invertible raising map, the fusion `↑↑ → ↑` a raising map back, and
/// their composite is the identity of `↑`, so a degree would need
/// `d(↑) < d(↑↑) ≤ d(↑)`. Admission refuses both graphs at their first
/// stick.
#[test]
fn sticks_as_objects_admit_no_degree()
{
    let one = bare_wires(WireCount::from(1));
    let two = bare_wires(WireCount::from(2));
    assert_eq!(
        Shape::read(&one),
        Err(ShapeObstruction::Stick {
            wire: Wire::from(0)
        })
    );
    assert_eq!(
        Shape::read(&two),
        Err(ShapeObstruction::Stick {
            wire: Wire::from(0)
        })
    );
    let one_ends = presented(&one).expect("the bare wire reads");
    let two_ends = presented(&two).expect("the bare wires read");
    assert!(one_ends.iter().all(|ends| ends.kind() == WireKind::Stick));
    let stick = Graph::new(EdgeCount::from(0), &one_ends);
    let sticks = Graph::new(EdgeCount::from(0), &two_ends);
    let inclusion = SiteMap::new(vec![], vec![Wire::from(0)]);
    let fusion = SiteMap::new(vec![], vec![Wire::from(0), Wire::from(0)]);
    assert_eq!(inclusion.check(stick, sticks), Ok(()), "↑ → ↑↑ is a map");
    assert_eq!(fusion.check(sticks, stick), Ok(()), "↑↑ → ↑ is a map");
    assert_eq!(inclusion.raising(), Membership::Inside);
    assert_eq!(fusion.raising(), Membership::Inside);
    assert!(
        !inclusion.wires().contains(&Wire::from(1)),
        "the inclusion misses the second stick, so it is not invertible"
    );
    assert_eq!(
        inclusion.then(&fusion),
        Ok(SiteMap::new(vec![], vec![Wire::from(0)])),
        "the round trip is the identity of ↑"
    );
}

/// Connected objects lose the point's deletion: the endomorphism `ε` of `•`
/// that deletes the point and includes `∅` back factors as a lowering map
/// then a raising map only through `∅`, which has no vertex and no wire and
/// so no component.
#[test]
fn connected_objects_lose_the_point_deletion()
{
    let point = Shape::from_ends(EdgeCount::from(1), vec![]).expect("the point is a shape");
    let empty = Shape::default();
    let epsilon = SiteMap::new(vec![VertexSet::EMPTY], vec![]);
    assert_eq!(epsilon.validate(&point, &point), Ok(()));
    let catalogue = Catalogue::build(ShapeSize::from(3)).expect("the catalogue builds");
    let mut middles: Vec<ShapeKey> = Vec::new();
    for middle in catalogue.shapes() {
        for lower in homs(&point, middle)
            .into_iter()
            .filter(|map| map.lowering(middle) == Membership::Inside)
        {
            for raise in homs(middle, &point)
                .into_iter()
                .filter(|map| map.raising() == Membership::Inside)
            {
                if lower.then(&raise).as_ref() == Ok(&epsilon) {
                    middles.push(middle.key());
                }
            }
        }
    }
    assert_eq!(middles, vec![empty.key()], "ε factors through ∅ alone");
    assert_eq!(usize::from(empty.vertex_count()), 0);
    assert_eq!(usize::from(empty.wire_count()), 0);
}

/// Fusions restricted to an output leg joined to an input leg are not
/// closed: the sticks of `↑↑` sent to the legs of `C(1,1)`, then the
/// corolla substituted by `p→q` with its legs fused, compose to a map of the
/// class that fuses two sticks.
#[test]
fn vertex_end_fusions_are_not_closed()
{
    let two = bare_wires(WireCount::from(2));
    let corolla = corolla();
    let chain = closed_chain();
    let stick_ends = presented(&two).expect("the bare wires read");
    let corolla_ends = presented(&corolla).expect("the corolla reads");
    let chain_ends = presented(&chain).expect("the chain reads");
    let sticks = Graph::new(EdgeCount::from(0), &stick_ends);
    let legs = Graph::new(corolla.edge_count(), &corolla_ends);
    let joined = Graph::new(chain.edge_count(), &chain_ends);
    let onto_legs = SiteMap::new(vec![], vec![Wire::from(0), Wire::from(1)]);
    let contraction = SiteMap::new(
        vec![VertexSet::single(Edge::from(0)).union(VertexSet::single(Edge::from(1)))],
        vec![Wire::from(0), Wire::from(0)],
    );
    assert_eq!(onto_legs.check(sticks, legs), Ok(()), "no fusion");
    assert_eq!(contraction.check(legs, joined), Ok(()));
    let mut fused: Vec<WireKind> = corolla_ends.iter().map(|ends| ends.kind()).collect();
    fused.sort_unstable();
    assert_eq!(
        fused,
        vec![WireKind::InputLeg, WireKind::OutputLeg],
        "the contraction fuses an output leg with an input leg"
    );
    let composite = onto_legs.then(&contraction).expect("they compose");
    assert_eq!(
        composite.check(sticks, joined),
        Ok(()),
        "a map of the class"
    );
    assert_eq!(composite.wires(), &[Wire::from(0), Wire::from(0)]);
    assert!(
        stick_ends.iter().all(|ends| ends.kind() == WireKind::Stick),
        "the composite's fused preimages are two sticks"
    );
}

/// Contraction placed in the lowering class loses the factorization of
/// `C(1,1) → p→q`: a raising half has an injective wire function, so the
/// lowering half would fuse the corolla's legs onto one wire of a one-vertex
/// middle, a generator consuming its own output, which the carrier refuses.
#[test]
fn contraction_lowering_loses_the_factorization()
{
    let corolla = Shape::read(&corolla()).expect("the corolla is a shape");
    let chain = Shape::read(&closed_chain()).expect("the chain is a shape");
    let contraction = SiteMap::new(
        vec![VertexSet::single(Edge::from(0)).union(VertexSet::single(Edge::from(1)))],
        vec![Wire::from(0), Wire::from(0)],
    );
    assert_eq!(
        homs(&corolla, &chain),
        vec![contraction],
        "the one map fuses both legs"
    );
    let loop_middle = Wiring::assemble(
        WireCount::from(1),
        vec![Generator::new(label(), vec![Wire::from(0)], vec![
            Wire::from(0),
        ])],
        Interface::default(),
    );
    assert_eq!(
        loop_middle,
        Err(WiringObstruction::DirectedCycle {
            through: Edge::from(0)
        })
    );
}
