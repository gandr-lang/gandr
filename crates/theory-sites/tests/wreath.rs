//! The wreath of the wiring site over itself, `W ≀ W`: its objects one per
//! class, its raising class read jointly per column, and the generalized
//! Reedy conditions at the bound.
//!
//! Single maps run over the objects of total size at most four, composable
//! pairs and spans over total size at most three. Every case count is pinned:
//! a lost object, map or case changes one.

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_sites::CaseCount;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Chain;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Outcome;
use gandr_theory_sites::Part;
use gandr_theory_sites::Scope;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Verdict;
use gandr_theory_sites::VertexSet;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathMap;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::closure;
use gandr_theory_sites::degree_order;
use gandr_theory_sites::dual_rigidity;
use gandr_theory_sites::factorization;
use gandr_theory_sites::identities;
use gandr_theory_sites::intersection;
use gandr_theory_sites::invertibility;
use gandr_theory_sites::pushouts;
use gandr_theory_sites::rigidity;
use gandr_theory_sites::split_lowering;
use quenchant_shape::shape::Maybe;

/// `W ≀ W` with every object of total size at most `bound`, over the wiring
/// catalogue at the same bound.
///
/// # Specification
/// trivial.
fn wreath(bound: ShapeSize) -> Wreath<Catalogue>
{
    let catalogue = Catalogue::build(bound).expect("the catalogue builds");
    Wreath::build(&catalogue, &catalogue, bound)
}

/// How many maps the wreath holds.
///
/// # Specification
/// trivial.
fn map_count(wreath: &Wreath<Catalogue>) -> CaseCount
{
    let count = wreath.objects().len();
    CaseCount::from(
        (0 .. count)
            .flat_map(|source| (0 .. count).map(move |target| (source, target)))
            .map(|(source, target)| {
                wreath
                    .hom(ShapeIndex::from(source), ShapeIndex::from(target))
                    .len()
            })
            .sum::<usize>(),
    )
}

/// The index of the object whose outer shape is `outer` and whose columns
/// are `columns`, in some order.
///
/// # Specification
/// trivial.
fn position(
    wreath: &Wreath<Catalogue>,
    outer: &Shape,
    columns: &[Shape],
) -> ShapeIndex
{
    let mut wanted: Vec<&Shape> = columns.iter().collect();
    wanted.sort();
    let mut held: Vec<&Shape> = Vec::with_capacity(columns.len());
    let found = wreath
        .objects()
        .iter()
        .position(|object: &WreathShape<Shape>| {
            held.clear();
            held.extend(object.columns());
            held.sort();
            object.outer() == outer && held == wanted
        })
        .expect("the wreath holds the object");
    ShapeIndex::from(found)
}

/// The probe's counts: 19 objects with 537 maps at total size three, and 65
/// with 6707 at four. The two orders of the columns over a pair of points are
/// one object, carried onto each other by the swap of the points.
#[test]
fn the_wreath_holds_one_object_per_class()
{
    let small = wreath(ShapeSize::from(3));
    assert_eq!(small.objects().len(), 19);
    assert_eq!(usize::from(map_count(&small)), 537);
    let large = wreath(ShapeSize::from(4));
    assert_eq!(large.objects().len(), 65);
    assert_eq!(usize::from(map_count(&large)), 6707);
    let pair = shape!(2);
    let over_the_pair = small
        .objects()
        .iter()
        .filter(|object| *object.outer() == pair)
        .count();
    assert_eq!(
        over_the_pair, 2,
        "(∅, ∅), and one class for (•, ∅) and (∅, •)"
    );
}

/// A point carrying a point, sent onto a pair of points carrying the empty
/// shape and a point: the inner map to the empty column deletes the point,
/// and alone it does not raise. Beside the identity onto the point's column
/// the column raises, so the wreath map raises and its degree rises from two
/// to three. Beside the deletion and re-inclusion of the point it does not.
#[test]
fn a_column_raises_when_one_inner_map_keeps_it()
{
    let small = wreath(ShapeSize::from(3));
    let point = shape!(1);
    let source = position(&small, &point, core::slice::from_ref(&point));
    let target = position(&small, &shape!(2), &[shape!(0), point]);
    let both = VertexSet::single(Edge::from(0)).union(VertexSet::single(Edge::from(1)));
    let onto_both: Vec<_> = small
        .hom(source, target)
        .iter()
        .filter(|map| map.outer().image(Edge::from(0)) == both)
        .collect();
    assert_eq!(
        onto_both.len(),
        2,
        "the identity or ε onto the point's column"
    );
    let raising: Vec<_> = onto_both
        .iter()
        .filter(|map| Wreath::<Catalogue>::raising(map) == Membership::Inside)
        .collect();
    assert_eq!(raising.len(), 1);
    let column = raising[0].column(Edge::from(0));
    assert_eq!(column.len(), 2, "one inner map per image vertex");
    let kept = column
        .iter()
        .filter(|entry| Catalogue::raising(&entry.1) == Membership::Inside)
        .count();
    assert_eq!(
        kept, 1,
        "the deletion into the empty column does not raise alone"
    );
    let objects = small.objects();
    let degree =
        |index: ShapeIndex| usize::from(Wreath::<Catalogue>::degree(&objects[usize::from(index)]));
    assert_eq!((degree(source), degree(target)), (2, 3));
}

/// Every generalized Reedy condition holds over `W ≀ W` with the degree the
/// sum over the levels: identities, the two classes meeting in the
/// isomorphisms, invertibility, the degree order, factorization unique up to
/// a unique isomorphism, both rigidity axioms, split lowering, and each class
/// closed under composition.
#[test]
fn the_wreath_is_a_generalized_reedy_category()
{
    let large = wreath(ShapeSize::from(4));
    let site = Site::new(&large);
    let maps = map_count(&large);
    assert_eq!(identities(&site), Outcome::Holds { cases: 6772.into() });
    assert_eq!(intersection(&site), Outcome::Holds { cases: maps });
    assert_eq!(invertibility(&site), Outcome::Holds { cases: maps });
    assert_eq!(degree_order(&site, Scope::Both), Outcome::Holds {
        cases: 814.into()
    });
    assert_eq!(factorization(&site), Outcome::Holds { cases: maps });
    assert_eq!(rigidity(&site), Outcome::Holds { cases: 1214.into() });
    assert_eq!(dual_rigidity(&site), Outcome::Holds { cases: 1828.into() });
    assert_eq!(split_lowering(&site), Outcome::Holds { cases: 302.into() });
    let small = wreath(ShapeSize::from(3));
    let narrow = Site::new(&small);
    for (part, cases) in [
        (Part::Whole, 33615_usize),
        (Part::Raising, 418),
        (Part::Lowering, 234),
    ] {
        assert_eq!(
            closure(&narrow, part),
            Outcome::Holds {
                cases: cases.into()
            },
            "{part:?}"
        );
    }
}

/// The outer shapes and columns a failing chain's maps run into, in order.
///
/// # Specification
/// trivial.
fn targets(
    outcome: &Outcome<Chain<WreathShape<Shape>, WreathMap<SiteMap>>>
) -> Vec<(Shape, Vec<Shape>)>
{
    match outcome.witness() {
        Maybe::Present(chain) => chain
            .links()
            .iter()
            .map(|link| {
                (
                    link.target().outer().clone(),
                    link.target().columns().to_vec(),
                )
            })
            .collect(),
        Maybe::Absent(_) => panic!("the condition fails"),
    }
}

/// Level one has no pushout of the point substituted by the closed chain
/// beside the point's deletion; the wreath carries that span on empty
/// columns, the fourteenth span examined at total size three. Inside a
/// column the same span has a pushout: every cocone deletes the outer vertex,
/// so the empty object is the pushout, and the pushed-out map lowers rather
/// than raises. The columns run over a point alone, the outer catalogue at
/// size one beside the inner at three.
#[test]
fn a_column_pushes_out_only_by_deleting_its_vertex()
{
    let (empty, point, closed) = (shape!(0), shape!(1), shape!(2; 0 > 1));
    let small = wreath(ShapeSize::from(3));
    let outcomes = pushouts(&Site::new(&small));
    assert_eq!(outcomes.existence.verdict(), Verdict::Fails);
    assert_eq!(usize::from(outcomes.existence.cases()), 14);
    assert_eq!(targets(&outcomes.existence), [
        (closed.clone(), vec![empty.clone(), empty.clone()]),
        (empty.clone(), vec![]),
    ]);
    assert_eq!(outcomes.stability, Outcome::Holds { cases: 160.into() });
    let points = Catalogue::build(ShapeSize::from(1)).expect("the catalogue builds");
    let inner = Catalogue::build(ShapeSize::from(3)).expect("the catalogue builds");
    let columns = Wreath::build(&points, &inner, ShapeSize::from(4));
    let outcomes = pushouts(&Site::new(&columns));
    assert_eq!(outcomes.existence, Outcome::Holds { cases: 181.into() });
    assert_eq!(outcomes.stability.verdict(), Verdict::Fails);
    assert_eq!(usize::from(outcomes.stability.cases()), 37);
    assert_eq!(targets(&outcomes.stability), [
        (point.clone(), vec![closed]),
        (point, vec![empty.clone()]),
        (empty, vec![]),
    ]);
}
