//! The validator's clauses and composition on raw graphs, sticks admitted,
//! the form the clauses are stated on.

use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Leg;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;

use super::CompositionMismatch;
use super::MapObstruction;
use super::SiteMap;
use super::VertexSet;
use crate::shape::End;
use crate::shape::Ends;
use crate::shape::Graph;

/// One wire end: `o` for open, a vertex number otherwise.
macro_rules! end {
    (o) => {
        End::Open
    };
    ($vertex:literal) => {
        End::Vertex(Edge::from($vertex))
    };
}

/// The wire ends of a raw graph, producer first: `ends![o > 0, 0 > o]`.
macro_rules! ends {
    ($($producer:tt > $consumer:tt),*) => {
        vec![$(Ends::new(end!($producer), end!($consumer))),*]
    };
}

/// The candidate map with the given vertex and wire images:
/// `site_map!([{0, 1}], [0, 0])`.
macro_rules! site_map {
    ([$({$($member:literal),*}),*], [$($wire:literal),*]) => {
        SiteMap::new(
            vec![$(
                [$(Edge::from($member)),*]
                    .into_iter()
                    .fold(VertexSet::EMPTY, |set, vertex| set.union(VertexSet::single(vertex)))
            ),*],
            vec![$(Wire::from($wire)),*],
        )
    };
}

/// Each clause of the validator refuses a hand-built candidate that breaks
/// it, by its variant and payload; the fusion clause, which the boundary
/// clause implies on shapes, is reached through a stick fused with an inner
/// wire, and two sticks fused onto one pass it.
#[test]
fn each_clause_refuses_by_variant()
{
    let empty: Vec<Ends> = Vec::new();
    let corolla_ends = ends![o > 0, 0 > o];
    let chain_ends = ends![0 > 1];
    let chain_and_stick_ends = ends![0 > 1, o > o];
    let stick_ends = ends![o > o];
    let two_stick_ends = ends![o > o, o > o];
    let point = Graph::new(EdgeCount::from(1), &empty);
    let two_points = Graph::new(EdgeCount::from(2), &empty);
    let corolla = Graph::new(EdgeCount::from(1), &corolla_ends);
    let chain = Graph::new(EdgeCount::from(2), &chain_ends);
    let chain_and_stick = Graph::new(EdgeCount::from(2), &chain_and_stick_ends);
    let stick = Graph::new(EdgeCount::from(0), &stick_ends);
    let two_sticks = Graph::new(EdgeCount::from(0), &two_stick_ends);
    assert_eq!(
        site_map!([], []).check(point, point),
        Err(MapObstruction::ImageCount {
            expected: EdgeCount::from(1),
            found: EdgeCount::from(0)
        })
    );
    assert_eq!(
        site_map!([{ 0 }], []).check(corolla, corolla),
        Err(MapObstruction::WireImageCount {
            expected: WireCount::from(2),
            found: WireCount::from(0)
        })
    );
    assert_eq!(
        site_map!([{ 1 }], []).check(point, point),
        Err(MapObstruction::ImageOutOfRange {
            vertex: Edge::from(0)
        })
    );
    assert_eq!(
        site_map!([{ 0 }], [0, 2]).check(corolla, corolla),
        Err(MapObstruction::WireOutOfRange {
            wire: Wire::from(1)
        })
    );
    assert_eq!(
        site_map!([{0}, {0, 1}], []).check(two_points, two_points),
        Err(MapObstruction::Overlap {
            first: Edge::from(0),
            second: Edge::from(1)
        })
    );
    assert_eq!(
        site_map!([{ 0 }], [1, 0]).check(corolla, corolla),
        Err(MapObstruction::Boundary {
            vertex: Edge::from(0),
            leg: Leg::Input
        }),
        "the input leg sent to the output leg"
    );
    assert_eq!(
        site_map!([{ 0 }, { 1 }], [0, 0]).check(chain_and_stick, chain),
        Err(MapObstruction::Fusion {
            wire: Wire::from(0)
        }),
        "an inner wire among a fused wire's preimages"
    );
    assert_eq!(
        site_map!([], [0, 0]).check(two_sticks, stick),
        Ok(()),
        "two sticks fused onto one"
    );
}

/// A composite refuses an image member and a wire image the second map has
/// no image for, naming each.
#[test]
fn composition_refuses_a_missing_image()
{
    assert_eq!(
        site_map!([{ 1 }], []).then(&site_map!([{ 0 }], [])),
        Err(CompositionMismatch::Vertex {
            vertex: Edge::from(1)
        })
    );
    assert_eq!(
        site_map!([], [2]).then(&site_map!([], [0])),
        Err(CompositionMismatch::Wire {
            wire: Wire::from(2)
        })
    );
}
