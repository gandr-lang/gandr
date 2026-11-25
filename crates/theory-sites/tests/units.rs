//! The units suite: the point and its inclusions, the external product, and
//! the finite check that the empty diagram is its one unit.

use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::GeneratorBound;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Part;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Verdict;
use gandr_theory_sites::closure;
use gandr_theory_sites::corolla;
use gandr_theory_sites::homs;
use gandr_theory_sites::merge;
use gandr_theory_sites::scalars;
use gandr_theory_sites::unit_property;

/// The raising maps are a subcategory at size three; the point has its
/// identity as its only raising endomorphism and reaches each point of
/// every shape at size four once.
#[test]
fn the_point_reaches_each_point_once()
{
    let triples = Catalogue::build(ShapeSize::from(3)).expect("the catalogue builds");
    let catalogue = Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds");
    assert_eq!(
        closure(&Site::new(&triples), Part::Raising).verdict(),
        Verdict::Holds
    );
    let outcome = corolla(&Site::new(&catalogue));
    assert_eq!(outcome.verdict(), Verdict::Holds);
    let point = shape!(1);
    let raising: Vec<SiteMap> = homs(&point, &point)
        .into_iter()
        .filter(|map| map.raising() == Membership::Inside)
        .collect();
    assert_eq!(
        raising,
        vec![SiteMap::identity(&point)],
        "ε deletes the point"
    );
}

/// The external product sets two wirings side by side, a bare wire among
/// them, and the empty wiring is a unit for it on both sides.
#[test]
fn the_external_product_sets_wirings_side_by_side()
{
    let label = GeneratorLabel::new("f", GeneratorSort::Value);
    let wire = Wire::from;
    let corolla = Wiring::assemble(
        WireCount::from(2),
        vec![Generator::new(label.clone(), vec![wire(0)], vec![wire(1)])],
        Interface::new(vec![wire(0)], vec![wire(1)]),
    )
    .expect("the corolla is admitted");
    let bare = Wiring::assemble(
        WireCount::from(1),
        vec![],
        Interface::new(vec![wire(0)], vec![wire(0)]),
    )
    .expect("the carrier admits a bare wire");
    let expected = Wiring::assemble(
        WireCount::from(3),
        vec![Generator::new(label, vec![wire(0)], vec![wire(1)])],
        Interface::new(vec![wire(0), wire(2)], vec![wire(1), wire(2)]),
    )
    .expect("the product is admitted");
    assert_eq!(merge(&corolla, &bare), Ok(expected));
    let empty = Wiring::assemble(WireCount::from(0), vec![], Interface::default())
        .expect("the empty wiring");
    assert_eq!(merge(&empty, &corolla), Ok(corolla.clone()));
    assert_eq!(merge(&corolla, &empty), Ok(corolla));
}

/// The scalars of at most four generators over `c`, `d`, `u` and `k` are
/// twenty-two classes, and the closed chain carries `u` then `k`.
#[test]
fn scalars_are_counted_and_labelled()
{
    let universe = scalars(GeneratorBound::from(4)).expect("the scalars are admitted");
    assert_eq!(universe.len(), 22);
    let chain = universe
        .iter()
        .find(|wiring| {
            usize::from(wiring.edge_count()) == 2 && usize::from(wiring.wire_count()) == 1
        })
        .expect("the closed chain is a scalar");
    let names: Vec<String> = chain
        .generators()
        .iter()
        .map(|generator| generator.label().name().to_string())
        .collect();
    assert_eq!(names, vec!["u".to_owned(), "k".to_owned()]);
}

/// Among the scalars of at most four generators exactly one is a
/// cancellable pseudo-idempotent, the empty diagram; it is a two-sided unit
/// on every shape at size three labelled by arity, and without it no scalar
/// is one.
#[test]
fn the_empty_diagram_is_the_only_unit()
{
    let catalogue = Catalogue::build(ShapeSize::from(3)).expect("the catalogue builds");
    let outcomes = unit_property(GeneratorBound::from(4), &catalogue).expect("the property runs");
    assert_eq!(usize::from(outcomes.scalars), 22);
    assert_eq!(outcomes.units, vec![shape!(0)]);
    assert_eq!(outcomes.two_sided.verdict(), Verdict::Holds);
    assert_eq!(outcomes.content.verdict(), Verdict::Holds);
}
