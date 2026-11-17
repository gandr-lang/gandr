//! The chains suite: the chain of `n` vertices, the family of chains, the
//! catalogue of that family as a sub-site, its stratum, and diagrams that
//! fill a chain.

use alloc::sync::Arc;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_sites::Boundary;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Corolla;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::Membership;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeBudget;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Uncertified;
use gandr_theory_sites::Unfilled;
use gandr_theory_sites::fills;
use gandr_theory_sites::shape_class;
use quenchant_shape::shape::Maybe;

/// A chain's vertex count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Length(usize);

/// An object a 1-cell runs between.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Object(char);

/// The objects the cells below run between.
const A: Object = Object('a');
/// The second object.
const B: Object = Object('b');
/// The third object.
const C: Object = Object('c');
/// The fourth object.
const D: Object = Object('d');
/// An object no composable neighbour shares.
const X: Object = Object('x');
/// The graft's target.
const Y: Object = Object('y');

/// The chain of `length` vertices.
///
/// # Specification
/// trivial.
fn chain(Length(length): Length) -> Shape
{
    Shape::chain(EdgeCount::from(length)).expect("the chain is admitted")
}

/// The cell from `source` to `target`.
///
/// # Specification
/// trivial.
fn cell(
    source: Object,
    target: Object,
) -> Boundary<Object>
{
    Boundary::new(vec![source], vec![target])
}

/// The 3-chain is the three composable vertices between its two open ends,
/// the chain of no vertex is the stick, and 65 vertices are more than a
/// vertex set holds.
#[test]
fn a_chain_runs_from_its_open_input_to_its_open_output()
{
    assert_eq!(
        chain(Length(3)),
        shape!(3; o > 0, 0 > 1, 1 > 2, 2 > o),
        "wire i feeds vertex i, and the last wire opens out"
    );
    assert_eq!(
        Shape::chain(EdgeCount::from(0)),
        Err(ShapeObstruction::Stick {
            wire: Wire::from(0)
        }),
        "the chain of no vertex is the stick"
    );
    assert_eq!(
        Shape::chain(EdgeCount::from(65)),
        Err(ShapeObstruction::TooManyVertices {
            vertices: EdgeCount::from(65)
        }),
        "a chain past the vertex set is refused by its count"
    );
}

/// The chains hold the 3-chain under any vertex order, the empty shape and
/// the point. They refuse `C(2,1)`, the closed chain, a vertex the chain does
/// not reach, and two chains side by side. A catalogue of chains names a
/// refused class as outside the family, and a longer chain as past the bound.
#[test]
fn the_chains_hold_the_chain_and_refuse_the_rest()
{
    let held = [
        chain(Length(3)),
        shape!(3; 2 > 0, o > 1, 1 > 2, 0 > o),
        Shape::default(),
        shape!(1),
    ];
    for shape in &held {
        assert_eq!(
            Family::Chains.holds(shape),
            Membership::Inside,
            "{shape} is a chain"
        );
    }
    let refused = [
        shape!(1; o > 0, o > 0, 0 > o),
        shape!(2; 0 > 1),
        shape!(2; o > 0, 0 > o, o > 1, 1 > o),
        shape!(2; o > 0, 0 > 1),
        shape!(2; o > 0, 0 > o),
        shape!(2),
    ];
    for shape in &refused {
        assert_eq!(
            Family::Chains.holds(shape),
            Membership::Outside,
            "{shape} is no chain"
        );
        assert_eq!(
            Family::Wirings.holds(shape),
            Membership::Inside,
            "{shape} is a wiring"
        );
    }
    let catalogue = Catalogue::chains(ShapeSize::from(7)).expect("the catalogue builds");
    assert_eq!(catalogue.family(), &Family::Chains);
    assert!(
        matches!(catalogue.find(&held[1]), Maybe::Present(_)),
        "a relabelled 3-chain is found at its class"
    );
    assert_eq!(
        catalogue.find(&refused[0]),
        Maybe::Absent(shape_class::Absent::OutsideTheFamily),
        "C(2,1) lies outside the chains"
    );
    assert_eq!(
        catalogue.find(&chain(Length(4))),
        Maybe::Absent(shape_class::Absent::PastTheBound),
        "the 4-chain is past size seven"
    );
}

/// At size five the chain catalogue's shapes are the wiring catalogue's
/// classes the family holds, in its order, and each hom set between two of
/// them is the wiring catalogue's. At size seven the 1-chain includes into
/// the 3-chain six ways and the 2-chain four ways.
#[test]
fn the_chain_catalogue_is_the_full_sub_site_on_the_chains()
{
    let bound = ShapeSize::from(5);
    let chains = Catalogue::chains(bound).expect("the catalogue builds");
    let wirings = Catalogue::build(bound).expect("the catalogue builds");
    let held: Vec<(ShapeIndex, &Shape)> = wirings
        .entries()
        .filter(|entry| Family::Chains.holds(entry.1) == Membership::Inside)
        .collect();
    assert_eq!(
        chains.shapes(),
        held.iter().map(|entry| entry.1.clone()).collect::<Vec<_>>(),
        "the empty shape, the point, the 1-chain and the 2-chain"
    );
    for (source, &(wide_source, _)) in held.iter().enumerate() {
        for (target, &(wide_target, _)) in held.iter().enumerate() {
            assert_eq!(
                chains.maps(ShapeIndex::from(source), ShapeIndex::from(target)),
                wirings.maps(wide_source, wide_target),
                "the hom set from chain class {source} to chain class {target}"
            );
        }
    }
    let longer = Catalogue::chains(ShapeSize::from(7)).expect("the catalogue builds");
    let index = |shape: &Shape| match longer.find(shape) {
        Maybe::Present(index) => index,
        Maybe::Absent(reason) => panic!("{shape} is absent: {reason:?}"),
    };
    let homs = |source: usize, target: usize| match longer
        .maps(index(&chain(Length(source))), index(&chain(Length(target))))
    {
        Maybe::Present(maps) => maps.len(),
        Maybe::Absent(reason) => panic!("no hom set: {reason:?}"),
    };
    assert_eq!(
        homs(1, 3),
        6,
        "a 1-cell goes to each sub-chain of the 3-chain"
    );
    assert_eq!(homs(2, 3), 4, "a 2-chain goes to the 3-chain four ways");
}

/// The chain budget counts the empty shape, the point and each chain: size
/// seven holds five shapes, so a budget of five admits them and one of four
/// stops at the fifth, before any hom set is built. A budget of nothing stops
/// at the empty shape.
#[test]
fn the_chain_budget_counts_the_empty_shape_the_point_and_each_chain()
{
    let bound = ShapeSize::from(7_usize);
    let within =
        Catalogue::chains_within(bound, ShapeBudget::from(5_usize)).expect("five shapes fit");
    assert_eq!(
        within.shapes(),
        Catalogue::chains(bound)
            .expect("the catalogue builds")
            .shapes(),
        "the budget at the count admits every shape the unbudgeted catalogue holds"
    );
    assert!(
        matches!(
            Catalogue::chains_within(bound, ShapeBudget::from(4_usize)),
            Err(ShapeObstruction::PastTheBudget { counted }) if usize::from(counted) == 5
        ),
        "one shape under the count stops at the fifth"
    );
    assert!(
        matches!(
            Catalogue::chains_within(bound, ShapeBudget::from(0_usize)),
            Err(ShapeObstruction::PastTheBudget { counted }) if usize::from(counted) == 1
        ),
        "a budget of nothing stops at the empty shape"
    );
}

/// At size seven the chain stratum is certified at degree four with the point
/// and the 1-chain as its corollas and the 2-chain's cocone, and at degree five
/// with the 3-chain's cocone too. Degree six lies above every chain.
#[test]
fn the_chain_stratum_is_certified_through_the_three_chain()
{
    let catalogue = Arc::new(Catalogue::chains(ShapeSize::from(7)).expect("the catalogue builds"));
    let shapes_of = |stratum: &SegalStratum| -> Vec<Shape> {
        stratum
            .cocones()
            .iter()
            .filter_map(|cocone| match catalogue.shape(cocone.shape()) {
                Maybe::Present(shape) => Some(shape.clone()),
                Maybe::Absent(_) => None,
            })
            .collect()
    };
    let four = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(4))
        .expect("degree four is certified");
    assert_eq!(
        four.corollas()
            .iter()
            .map(Corolla::profile)
            .collect::<Vec<_>>(),
        [Profile::default(), Profile {
            inputs: PortCount::from(1),
            outputs: PortCount::from(1)
        }],
        "the point and the 1-chain"
    );
    assert_eq!(shapes_of(&four), [chain(Length(2))], "the 2-chain alone");
    let five = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(5))
        .expect("degree five is certified");
    assert_eq!(
        shapes_of(&five),
        [chain(Length(2)), chain(Length(3))],
        "the 2-chain and the 3-chain"
    );
    assert!(
        matches!(
            SegalStratum::certify(Arc::clone(&catalogue), Degree::from(6)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(6)
        ),
        "no chain at size seven has degree six"
    );
}

/// Three composable cells fill the 3-chain and answer its outer objects. On
/// the graft of a binary vertex after a unary one, the inner wire meets the
/// binary vertex's first input.
#[test]
fn a_composable_diagram_fills_its_chain()
{
    let cells = [cell(A, B), cell(B, C), cell(C, D)];
    let filled = fills(&chain(Length(3)), &cells, PartialEq::eq).expect("the cells compose");
    assert_eq!(filled.inputs(), [&A], "the composite's source");
    assert_eq!(filled.outputs(), [&D], "the composite's target");
    let graft = shape!(2; o > 0, 0 > 1, o > 1, 1 > o);
    let cells = [cell(A, B), Boundary::new(vec![B, X], vec![Y])];
    let filled = fills(&graft, &cells, PartialEq::eq).expect("the cells meet");
    assert_eq!(filled.inputs(), [&A, &X], "the open inputs in wire order");
    assert_eq!(filled.outputs(), [&Y], "the one open output");
}

/// A cell short, a cell with another profile and a middle object that
/// disagrees are each refused with their payload, in that order of precedence.
#[test]
fn a_diagram_that_does_not_fill_its_chain_is_named()
{
    let three = chain(Length(3));
    assert_eq!(
        fills(&three, &[cell(A, B), cell(B, C)], PartialEq::eq),
        Err(Unfilled::Cells {
            vertices: EdgeCount::from(3),
            cells: EdgeCount::from(2)
        }),
        "a cell short"
    );
    assert_eq!(
        fills(
            &three,
            &[cell(A, B), Boundary::new(vec![B, B], vec![C]), cell(X, D)],
            PartialEq::eq
        ),
        Err(Unfilled::Profile {
            vertex: Edge::from(1),
            found: Profile {
                inputs: PortCount::from(2),
                outputs: PortCount::from(1)
            }
        }),
        "a binary cell at a unary vertex, before the later wire's mismatch"
    );
    assert_eq!(
        fills(&three, &[cell(A, B), cell(B, C), cell(X, D)], PartialEq::eq),
        Err(Unfilled::Wire {
            wire: Wire::from(2)
        }),
        "the second cell ends at c and the third starts at x"
    );
}
