//! The generalized Reedy structure at the bound: the category and its two
//! classes, the degree, the direct point-free core, finite latching, the
//! factorization through a point deletion, both rigidity axioms, and the one
//! span without a pushout.
//!
//! Single maps run over the shapes of size at most four, composable pairs
//! and spans over size at most three. Every case count is pinned: a lost
//! shape, map or case changes one.

use gandr_theory_sites::CaseCount;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Chain;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Invertibility;
use gandr_theory_sites::MapCase;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Outcome;
use gandr_theory_sites::Part;
use gandr_theory_sites::Scope;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeKey;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Verdict;
use gandr_theory_sites::WireKind;
use gandr_theory_sites::closure;
use gandr_theory_sites::degree_order;
use gandr_theory_sites::direct_core;
use gandr_theory_sites::dual_rigidity;
use gandr_theory_sites::factorization;
use gandr_theory_sites::homs;
use gandr_theory_sites::identities;
use gandr_theory_sites::intersection;
use gandr_theory_sites::latching;
use gandr_theory_sites::pushouts;
use gandr_theory_sites::rigidity;
use quenchant_shape::shape::Maybe;

/// The classes of a case's source and target.
///
/// # Specification
/// trivial.
fn classes(case: &MapCase) -> (ShapeKey, ShapeKey)
{
    (case.source().key(), case.target().key())
}

/// The links of a failing chain outcome.
///
/// # Specification
/// trivial.
fn links(outcome: &Outcome<Chain>) -> &[MapCase]
{
    match outcome.witness() {
        | Maybe::Present(chain) => chain.links(),
        | Maybe::Absent(_) => panic!("the condition fails"),
    }
}

/// How many maps of the catalogue `keep` admits, given each with its source
/// and target.
///
/// # Specification
/// trivial.
fn maps_where(
    catalogue: &Catalogue,
    keep: impl Fn(&Shape, &Shape, &SiteMap) -> bool,
) -> CaseCount
{
    let mut count = 0_usize;
    for (source_index, source) in catalogue.entries() {
        for (target_index, target) in catalogue.entries() {
            let Maybe::Present(maps) = catalogue.maps(source_index, target_index)
            else {
                panic!("every pair has a hom set");
            };
            count =
                count.saturating_add(maps.iter().filter(|map| keep(source, target, map)).count());
        }
    }
    CaseCount::from(count)
}

/// The catalogue for single maps.
///
/// # Specification
/// trivial.
fn single() -> Catalogue
{
    Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds")
}

/// The catalogue for composable pairs and spans.
///
/// # Specification
/// trivial.
fn paired() -> Catalogue
{
    Catalogue::build(ShapeSize::from(3)).expect("the catalogue builds")
}

/// Identities are units in both classes, every part is closed under
/// composition, and the maps in both classes are exactly the isomorphisms:
/// one case per shape and per map for the identities, one per map for the
/// intersection, one per composable pair for each closure.
#[test]
fn the_class_is_a_category_with_two_classes()
{
    let catalogue = single();
    let site = Site::new(&catalogue);
    let maps = maps_where(&catalogue, |_, _, _| true);
    assert_eq!(catalogue.shapes().len(), 31);
    assert_eq!(usize::from(maps), 1901);
    assert_eq!(identities(&site), Outcome::Holds { cases: 1932.into() });
    assert_eq!(intersection(&site), Outcome::Holds { cases: maps });
    let pairs = paired();
    let narrow = Site::new(&pairs);
    for (part, cases) in [
        (Part::Whole, 12376_usize),
        (Part::Raising, 328),
        (Part::Lowering, 170),
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

/// The degree, vertices plus inner wires, preserves every isomorphism,
/// strictly raises every other raising map and strictly lowers every other
/// lowering map. The contraction `C(1,1) → p→q` raises it from one to three
/// while keeping vertices plus wires at three, so that count is no degree.
#[test]
fn the_degree_orders_both_classes()
{
    let catalogue = single();
    let site = Site::new(&catalogue);
    let raising = maps_where(&catalogue, |_, target, map| {
        map.invertibility(target) == Invertibility::Invertible
            || map.raising() == Membership::Inside
    });
    assert_eq!(degree_order(&site, Scope::Raising), Outcome::Holds {
        cases: raising
    });
    let either = maps_where(&catalogue, |_, target, map| {
        map.raising() == Membership::Inside || map.lowering(target) == Membership::Inside
    });
    assert_eq!(degree_order(&site, Scope::Both), Outcome::Holds {
        cases: either
    });
    assert_eq!((usize::from(raising), usize::from(either)), (370, 439));
    let corolla = shape!(1; o > 0, 0 > o);
    let chain = shape!(2; 0 > 1);
    assert_eq!(Degree::of(&corolla), Degree::from(1));
    assert_eq!(Degree::of(&chain), Degree::from(3));
    let parts = |shape: &Shape| {
        usize::from(shape.vertex_count()).saturating_add(usize::from(shape.wire_count()))
    };
    assert_eq!(parts(&corolla), parts(&chain));
    assert_eq!(homs(&corolla, &chain).len(), 1, "the contraction");
    assert!(
        Degree::of(&shape!(0)) < Degree::of(&shape!(1)),
        "the deletion of the point lowers it"
    );
}

/// Between shapes without points every map is raising, and strictly raises
/// the degree unless it is an isomorphism: the point-free core is a direct
/// category.
#[test]
fn the_point_free_core_is_direct()
{
    let catalogue = single();
    let site = Site::new(&catalogue);
    let point_free = maps_where(&catalogue, |source, target, _| {
        usize::from(source.point_count()) == 0 && usize::from(target.point_count()) == 0
    });
    assert_eq!(usize::from(point_free), 97);
    assert_eq!(direct_core(&site), Outcome::Holds { cases: point_free });
    let contraction = &homs(&shape!(1; o > 0, 0 > o), &shape!(2; 0 > 1))[0];
    assert_eq!(contraction.raising(), Membership::Inside);
}

/// Every non-invertible raising map `G → K` has at most `K`'s vertices and
/// at most `K`'s wires plus inner wires, so the latching category at `K` lies
/// among finitely many shapes. `p ⊔ q → p→q`, two legs fused into the inner
/// wire, meets the wire bound with equality.
#[test]
fn the_latching_category_is_finite()
{
    let catalogue = single();
    let site = Site::new(&catalogue);
    let raising = maps_where(&catalogue, |_, target, map| {
        map.raising() == Membership::Inside
            && map.invertibility(target) == Invertibility::NotInvertible
    });
    assert_eq!(usize::from(raising), 289);
    assert_eq!(latching(&site), Outcome::Holds { cases: raising });
    let pair = shape!(2; 0 > o, o > 1);
    let chain = shape!(2; 0 > 1);
    let joined = homs(&pair, &chain);
    assert_eq!(joined.len(), 1, "the contraction");
    assert_eq!(
        joined[0].invertibility(&chain),
        Invertibility::NotInvertible
    );
    assert_eq!(pair.vertex_count(), chain.vertex_count());
    assert_eq!(
        usize::from(pair.wire_count()),
        usize::from(chain.wire_count())
            .saturating_add(usize::from(chain.count_of(WireKind::Inner))),
        "the wire bound is met with equality"
    );
}

/// Every map is a point deletion followed by a raising map, unique up to a
/// unique isomorphism of the middle; ε, the endomorphism of `•` deleting
/// and re-including its point, factors through `∅` and not through `•`.
#[test]
fn every_map_factors_through_a_point_deletion()
{
    let catalogue = single();
    let site = Site::new(&catalogue);
    let maps = maps_where(&catalogue, |_, _, _| true);
    assert_eq!(factorization(&site), Outcome::Holds { cases: maps });
    let point = shape!(1);
    let epsilon = site_map!([{}], []);
    epsilon.validate(&point, &point).expect("ε is a map");
    let through = |middle: &Shape| {
        homs(&point, middle)
            .into_iter()
            .filter(|lower| lower.lowering(middle) == Membership::Inside)
            .flat_map(|lower| {
                homs(middle, &point)
                    .into_iter()
                    .filter(|raise| raise.raising() == Membership::Inside)
                    .filter_map(move |raise| lower.then(&raise).ok())
            })
            .filter(|composite| *composite == epsilon)
            .count()
    };
    assert_eq!(through(&shape!(0)), 1, "through ∅");
    assert_eq!(through(&point), 0, "not through •");
}

/// An automorphism fixing a lowering map, or absorbed by a raising map, is
/// the identity: axiom (iv) and its dual, one case per lowering or raising
/// map and automorphism.
#[test]
fn both_rigidity_axioms_hold()
{
    let catalogue = single();
    let site = Site::new(&catalogue);
    assert_eq!(rigidity(&site), Outcome::Holds { cases: 958.into() });
    assert_eq!(dual_rigidity(&site), Outcome::Holds { cases: 1432.into() });
}

/// The point sent to the closed chain has no pushout with its deletion,
/// the seventh span examined; every pushout that exists pushes a raising
/// map to a raising map.
#[test]
fn a_closed_substitution_has_no_pushout_with_a_deletion()
{
    let catalogue = paired();
    let outcomes = pushouts(&Site::new(&catalogue));
    assert_eq!(usize::from(outcomes.existence.cases()), 7);
    let span = links(&outcomes.existence);
    assert_eq!(span.len(), 2, "a span");
    let (substitution, deletion) = (&span[0], &span[1]);
    assert_eq!(
        classes(substitution),
        (shape!(1).key(), shape!(2; 0 > 1).key())
    );
    assert_eq!(*substitution.map(), site_map!([{0, 1}], []));
    assert_eq!(classes(deletion), (shape!(1).key(), shape!(0).key()));
    assert_eq!(outcomes.stability, Outcome::Holds { cases: 117.into() });
    assert_eq!(outcomes.existence.verdict(), Verdict::Fails);
}
