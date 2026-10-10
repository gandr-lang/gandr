//! Shapes: the enumeration against an independent count, the constructors'
//! refusals, the stick among them, reading a wiring back, and the statistics
//! the suites use.

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
use gandr_theory_sites::Degree;
use gandr_theory_sites::End;
use gandr_theory_sites::Ends;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::VertexKind;
use gandr_theory_sites::WireKind;
use gandr_theory_sites::shapes_up_to;

/// The wiring with one wire of each admitted kind and a point: `w0` enters
/// `g0`, `w1` runs from `g0` to `g1`, `g2` has no port, and `w2` leaves `g3`.
///
/// # Specification
/// trivial.
fn mixed_wiring() -> Wiring
{
    let label = GeneratorLabel::new("g", GeneratorSort::Value);
    let wire = Wire::from;
    Wiring::assemble(
        WireCount::from(3),
        vec![
            Generator::new(label.clone(), vec![wire(0)], vec![wire(1)]),
            Generator::new(label.clone(), vec![wire(1)], vec![]),
            Generator::new(label.clone(), vec![], vec![]),
            Generator::new(label, vec![], vec![wire(2)]),
        ],
        Interface::new(vec![wire(0)], vec![wire(2)]),
    )
    .expect("the fixture is admitted")
}

/// The bare identity wire: one wire, both a boundary input and a boundary
/// output, no generator.
///
/// # Specification
/// trivial.
fn identity_wire() -> Wiring
{
    let wire = Wire::from(0);
    Wiring::assemble(
        WireCount::from(1),
        vec![],
        Interface::new(vec![wire], vec![wire]),
    )
    .expect("the carrier admits the identity wire")
}

/// Every size bound up to six has the stick-free class count an enumerator
/// written outside this crate implies.
///
/// That enumerator counts the classes with sticks allowed, 1, 3, 8, 20, 51,
/// 132 and 355 up to sizes zero to six. Removing the sticks of a class of size
/// exactly `n` leaves a stick-free class of size at most `n`, and every
/// stick-free class is reached once, so the stick-free counts are the
/// differences: 1, 2, 5, 12, 31, 81 and 223. A lost or doubled class, or an
/// admitted stick, changes a count.
#[test]
fn the_enumeration_counts_match_an_independent_count()
{
    let expected: [usize; 7] = [1, 2, 5, 12, 31, 81, 223];
    for (bound, count) in expected.into_iter().enumerate() {
        let shapes = shapes_up_to(ShapeSize::from(bound)).expect("the enumeration runs");
        assert_eq!(shapes.len(), count, "classes of size at most {bound}");
        assert!(
            shapes.is_sorted_by_key(Shape::size),
            "the classes come least size first"
        );
        assert!(
            shapes
                .iter()
                .all(|shape| usize::from(shape.count_of(WireKind::Stick)) == 0),
            "no class holds a stick"
        );
    }
}

/// Each refusal of the constructors other than the stick is observed by its
/// variant.
#[test]
fn the_constructor_refuses_by_variant()
{
    assert_eq!(
        Shape::from_ends(EdgeCount::from(65), vec![]),
        Err(ShapeObstruction::TooManyVertices {
            vertices: EdgeCount::from(65)
        })
    );
    assert_eq!(
        Shape::from_ends(EdgeCount::from(1), vec![Ends::new(end!(0), end!(1))]),
        Err(ShapeObstruction::UnknownVertex {
            wire: Wire::from(0),
            vertex: Edge::from(1)
        })
    );
    assert_eq!(
        Shape::from_ends(EdgeCount::from(1), vec![Ends::new(end!(0), end!(0))]),
        Err(ShapeObstruction::Carrier(
            WiringObstruction::DirectedCycle {
                through: Edge::from(0)
            }
        )),
        "a self-loop is the carrier's cycle refusal"
    );
    assert!(
        matches!(
            Shape::from_ends(EdgeCount::from(2), vec![
                Ends::new(end!(0), end!(1)),
                Ends::new(end!(1), end!(0))
            ]),
            Err(ShapeObstruction::Carrier(
                WiringObstruction::DirectedCycle { .. }
            ))
        ),
        "a two-cycle is refused"
    );
    let label = GeneratorLabel::new("g", GeneratorSort::Value);
    let crowded = Wiring::assemble(
        WireCount::from(0),
        vec![Generator::new(label, vec![], vec![]); 65],
        Interface::default(),
    )
    .expect("port-free generators are admitted");
    assert_eq!(
        Shape::read(&crowded),
        Err(ShapeObstruction::TooManyVertices {
            vertices: EdgeCount::from(65)
        })
    );
}

/// A stick is refused by naming its wire, from a list of ends and from a
/// wiring, alone or beside a corolla; wires are checked in order, and the
/// vertex count before any wire.
#[test]
fn a_stick_is_refused_by_name()
{
    let stick = Ends::new(End::Open, End::Open);
    assert_eq!(
        Shape::from_ends(EdgeCount::from(1), vec![
            Ends::new(End::Open, end!(0)),
            stick
        ]),
        Err(ShapeObstruction::Stick {
            wire: Wire::from(1)
        })
    );
    assert_eq!(
        Shape::from_ends(EdgeCount::from(1), vec![stick, Ends::new(end!(0), end!(1))]),
        Err(ShapeObstruction::Stick {
            wire: Wire::from(0)
        }),
        "the stick comes first"
    );
    assert_eq!(
        Shape::from_ends(EdgeCount::from(1), vec![Ends::new(end!(0), end!(1)), stick]),
        Err(ShapeObstruction::UnknownVertex {
            wire: Wire::from(0),
            vertex: Edge::from(1)
        }),
        "the absent vertex comes first"
    );
    assert_eq!(
        Shape::from_ends(EdgeCount::from(65), vec![stick]),
        Err(ShapeObstruction::TooManyVertices {
            vertices: EdgeCount::from(65)
        }),
        "the vertex count is checked before any wire"
    );
    assert_eq!(
        Shape::read(&identity_wire()),
        Err(ShapeObstruction::Stick {
            wire: Wire::from(0)
        }),
        "the identity wire is not a shape"
    );
    let corolla = shape!(1; o > 0, 0 > o)
        .to_wiring()
        .expect("the carrier admits the corolla");
    let beside =
        gandr_theory_sites::merge(&corolla, &identity_wire()).expect("the carrier admits the pair");
    assert_eq!(
        Shape::read(&beside),
        Err(ShapeObstruction::Stick {
            wire: Wire::from(2)
        }),
        "a stick beside a corolla is refused"
    );
    assert_eq!(
        ShapeObstruction::Stick {
            wire: Wire::from(2)
        }
        .to_string(),
        "wire 2 is a stick component"
    );
}

/// A wiring reads to the ends written by hand, and the wiring the shape
/// presents reads back to the same shape.
#[test]
fn a_wiring_reads_back_as_its_shape()
{
    let shape = Shape::read(&mixed_wiring()).expect("the fixture reads");
    assert_eq!(shape, shape!(4; o > 0, 0 > 1, 3 > o));
    let presented = shape.to_wiring().expect("the carrier admits it");
    assert_eq!(Shape::read(&presented), Ok(shape.clone()));
    assert_eq!(shape.to_string(), "[4v; ·→0, 0→1, 3→·]");
}

/// Each admitted kind of wire is counted once in a shape holding one of
/// each, and the kinds follow which ends are open.
#[test]
fn wire_kinds_follow_the_open_ends()
{
    let shape = Shape::read(&mixed_wiring()).expect("the fixture reads");
    for kind in [WireKind::InputLeg, WireKind::OutputLeg, WireKind::Inner] {
        assert_eq!(
            usize::from(shape.count_of(kind)),
            1,
            "one wire of each kind"
        );
    }
    assert_eq!(usize::from(shape.count_of(WireKind::Stick)), 0);
    assert_eq!(Ends::new(End::Open, End::Open).kind(), WireKind::Stick);
    assert_eq!(Ends::new(End::Open, end!(0)).kind(), WireKind::InputLeg);
    assert_eq!(Ends::new(end!(0), End::Open).kind(), WireKind::OutputLeg);
    assert_eq!(Ends::new(end!(0), end!(1)).kind(), WireKind::Inner);
}

/// The points are the vertices no end names; a vertex touched by an output
/// alone is ported.
#[test]
fn points_are_the_vertices_no_wire_touches()
{
    let shape = Shape::read(&mixed_wiring()).expect("the fixture reads");
    assert_eq!(shape.points(), vec![Edge::from(2)]);
    assert_eq!(usize::from(shape.point_count()), 1);
    assert_eq!(shape.vertex_kind(Edge::from(3)), VertexKind::Ported);
    assert_eq!(usize::from(shape!(3).point_count()), 3);
    assert_eq!(usize::from(shape!(1; o > 0).point_count()), 0);
}

/// Relabelling the vertices keeps the key; moving a leg changes it.
#[test]
fn a_relabelled_shape_keys_alike()
{
    let chain = shape!(2; o > 0, 0 > 1);
    let renumbered = shape!(2; 1 > 0, o > 1);
    let moved = shape!(2; o > 1, 0 > 1);
    assert_eq!(chain.key(), renumbered.key());
    assert_ne!(chain.key(), moved.key());
}

/// The degree counts vertices and inner wires and nothing else: a leg, a
/// lost point or a lost inner wire each changes one of the three values.
#[test]
fn the_degree_counts_vertices_and_inner_wires()
{
    let mixed = Shape::read(&mixed_wiring()).expect("the fixture reads");
    assert_eq!(Degree::of(&mixed).to_string(), "5");
    assert_eq!(Degree::of(&shape!(1; o > 0, 0 > o)).to_string(), "1");
    assert_eq!(Degree::of(&shape!(2; 0 > 1)).to_string(), "3");
    assert!(
        Degree::of(&shape!(1; o > 0, 0 > o)) < Degree::of(&shape!(2; 0 > 1)),
        "degrees compare as counts"
    );
}
