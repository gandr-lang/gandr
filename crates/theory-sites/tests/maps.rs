//! Maps: the vertex sets, the enumerator against hand counts and a
//! brute-force enumeration, composition, the two classes and the catalogue.

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::ImageForm;
use gandr_theory_sites::Invertibility;
use gandr_theory_sites::MapForm;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Part;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Verdict;
use gandr_theory_sites::VertexSet;
use gandr_theory_sites::WireForm;
use gandr_theory_sites::closure;
use gandr_theory_sites::hom_lookup;
use gandr_theory_sites::homs;
use gandr_theory_sites::identities;
use gandr_theory_sites::invertibility;
use gandr_theory_sites::shape_class;
use gandr_theory_sites::shape_lookup;
use gandr_theory_sites::shapes_up_to;
use quenchant_shape::shape::Maybe;

/// Every pair `(S, φ)` from `source` to `target` the validator accepts,
/// found by trying every assignment of a vertex subset to each source vertex
/// and a target wire to each source wire.
///
/// # Specification
/// trivial.
fn brute_force(
    source: &Shape,
    target: &Shape,
) -> Vec<SiteMap>
{
    // Every reading of a mixed-radix counter, least position fastest; one
    // empty reading for no positions, none when a base is zero.
    let readings = |bases: &[usize]| -> Vec<Vec<usize>> {
        if bases.contains(&0) {
            return Vec::new();
        }
        let mut digits = vec![0_usize; bases.len()];
        let mut all = vec![digits.clone()];
        loop {
            let Some(position) = digits
                .iter()
                .zip(bases)
                .position(|(digit, base)| digit.saturating_add(1) < *base)
            else {
                return all;
            };
            digits[position] = digits[position].saturating_add(1);
            for digit in &mut digits[.. position] {
                *digit = 0;
            }
            all.push(digits.clone());
        }
    };
    let vertices = u32::try_from(usize::from(target.vertex_count())).unwrap();
    let subsets = 2_usize.checked_pow(vertices).unwrap();
    let vertex_digits = vec![subsets; usize::from(source.vertex_count())];
    let wire_digits = vec![usize::from(target.wire_count()); usize::from(source.wire_count())];
    let mut found = Vec::new();
    for images in readings(&vertex_digits) {
        let images: Vec<VertexSet> = images
            .into_iter()
            .map(|subset| {
                (0 .. vertices)
                    .filter(|vertex| subset.checked_shr(*vertex).unwrap() & 1 == 1)
                    .fold(VertexSet::EMPTY, |set, vertex| {
                        set.union(VertexSet::single(Edge::from(
                            usize::try_from(vertex).unwrap(),
                        )))
                    })
            })
            .collect();
        for wires in readings(&wire_digits) {
            let candidate =
                SiteMap::new(images.clone(), wires.into_iter().map(Wire::from).collect());
            if candidate.validate(source, target).is_ok() {
                found.push(candidate);
            }
        }
    }
    found.sort();
    found
}

/// The first and last representable vertex are members, a later one is
/// not, and the members come least first.
#[test]
fn vertex_sets_hold_the_first_and_last_vertex()
{
    let first = VertexSet::single(Edge::from(0));
    let last = VertexSet::single(Edge::from(63));
    assert_eq!(VertexSet::single(Edge::from(64)), VertexSet::EMPTY);
    let both = first.union(last);
    assert_eq!(both.members().collect::<Vec<_>>(), vec![
        Edge::from(0),
        Edge::from(63)
    ]);
    assert_eq!(usize::from(both.count()), 2);
    assert_eq!(both.contains(Edge::from(63)), Membership::Inside);
    assert_eq!(both.contains(Edge::from(1)), Membership::Outside);
    assert_eq!(both.without(first), last);
    assert_eq!(
        usize::from(VertexSet::below(EdgeCount::from(64)).count()),
        64
    );
    assert_eq!(both.to_string(), "{0,63}");
}

/// The hom counts worked by hand from the class's clauses, and a grounded
/// source whose two maps share their wire image.
#[test]
fn hom_counts_match_hand_counts()
{
    let point = shape!(1);
    let empty = shape!(0);
    let two_points = shape!(2);
    let identity_corolla = shape!(1; o > 0, 0 > o);
    let merge_corolla = shape!(1; o > 0, o > 0, 0 > o);
    let sink_corolla = shape!(1; o > 0);
    let closed_chain = shape!(2; 0 > 1);
    let source_beside_sink = shape!(2; 0 > o, o > 1);
    let count = |source: &Shape, target: &Shape| homs(source, target).len();
    assert_eq!(count(&point, &empty), 1, "• → ∅");
    assert_eq!(count(&empty, &closed_chain), 1, "∅ → p→q");
    assert_eq!(count(&point, &point), 2, "• → •: the identity and ε");
    assert_eq!(
        count(&point, &two_points),
        4,
        "• → •⊔•: ∅, either point, or both"
    );
    assert_eq!(
        count(&point, &closed_chain),
        2,
        "• → p→q: the deletion and the closed chain substituted"
    );
    assert_eq!(count(&merge_corolla, &merge_corolla), 2, "C(2,1) → C(2,1)");
    assert_eq!(count(&identity_corolla, &closed_chain), 1, "C(1,1) → p→q");
    assert_eq!(
        count(&source_beside_sink, &closed_chain),
        1,
        "p ⊔ q → p→q: the contraction"
    );
    assert_eq!(
        count(&sink_corolla, &identity_corolla),
        0,
        "C(1,0) → C(1,1)"
    );
    assert_eq!(count(&identity_corolla, &empty), 0, "C(1,1) → ∅");
    let source_corolla = shape!(1; 0 > o);
    let beside_point = shape!(2; 0 > o);
    let maps = homs(&source_corolla, &beside_point);
    assert_eq!(
        maps.len(),
        2,
        "C(0,1) → C(0,1)⊔•: the image with or without the point"
    );
    assert_eq!(
        maps[0].wires(),
        maps[1].wires(),
        "the edge action does not fix the map"
    );
}

/// The enumerator returns exactly what a brute-force filter over every
/// pair `(S, φ)` returns, for every pair of shapes of size at most four
/// whose sizes sum to at most six.
#[test]
fn the_enumerator_agrees_with_brute_force()
{
    let shapes = shapes_up_to(ShapeSize::from(4)).expect("the enumeration runs");
    let mut pairs = 0_usize;
    for source in &shapes {
        for target in &shapes {
            if usize::from(source.size()).saturating_add(usize::from(target.size())) > 6 {
                continue;
            }
            pairs = pairs.saturating_add(1);
            assert_eq!(
                homs(source, target),
                brute_force(source, target),
                "{source} → {target}"
            );
        }
    }
    assert_eq!(
        pairs, PAIRS_COMPARED,
        "the comparison covers the small pairs"
    );
}

/// How many ordered pairs of stick-free shapes of size at most four have
/// sizes summing to at most six: with 1, 1, 3, 7 and 19 classes of size
/// exactly zero to four, `Σ n_a n_b` over `a + b ≤ 6` is 334.
const PAIRS_COMPARED: usize = 334;

/// Identities are maps and units, composites of maps are maps, and
/// composition is associative, over every shape and composable triple at
/// size three.
#[test]
fn the_class_is_a_category_at_the_bound()
{
    let catalogue = Catalogue::build(ShapeSize::from(3)).expect("the catalogue builds");
    let site = Site::new(&catalogue);
    assert_eq!(identities(&site).verdict(), Verdict::Holds);
    assert_eq!(closure(&site, Part::Whole).verdict(), Verdict::Holds);
    let count = catalogue.shapes().len();
    let maps = |source: usize, target: usize| match catalogue
        .maps(ShapeIndex::from(source), ShapeIndex::from(target))
    {
        | Maybe::Present(maps) => maps.to_vec(),
        | Maybe::Absent(_) => panic!("every pair has a hom set"),
    };
    for first in 0 .. count {
        for second in 0 .. count {
            for third in 0 .. count {
                for fourth in 0 .. count {
                    for left in maps(first, second) {
                        for middle in maps(second, third) {
                            for right in maps(third, fourth) {
                                let grouped_left =
                                    left.then(&middle).and_then(|map| map.then(&right));
                                let grouped_right =
                                    middle.then(&right).and_then(|map| left.then(&map));
                                assert_eq!(grouped_left, grouped_right, "associativity");
                            }
                        }
                    }
                }
            }
        }
    }
}

/// The composite of a substitution of a corolla beside a point and the
/// deletion of that point, worked by hand.
#[test]
fn a_contraction_composes_with_a_deletion()
{
    let source = shape!(2; o > 0, 0 > o);
    let middle = shape!(3; 0 > 1);
    let target = shape!(2; 0 > 1);
    let contraction = site_map!([{0, 1}, {2}], [0, 0]);
    let deletion = site_map!([{ 0 }, { 1 }, {}], [0]);
    contraction
        .validate(&source, &middle)
        .expect("the contraction is a map");
    deletion
        .validate(&middle, &target)
        .expect("the deletion is a map");
    let composite = contraction.then(&deletion).expect("they compose");
    assert_eq!(composite, site_map!([{0, 1}, {}], [0, 0]));
    assert_eq!(composite.validate(&source, &target), Ok(()));
    assert_eq!(composite.kernel(), VertexSet::single(Edge::from(1)));
}

/// A map is an isomorphism of the class exactly when some map composes
/// with it to both identities, over every pair at size four.
#[test]
fn invertibility_matches_two_sided_inverses()
{
    let catalogue = Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds");
    let site = Site::new(&catalogue);
    let outcome = invertibility(&site);
    assert_eq!(outcome.verdict(), Verdict::Holds);
}

/// The forms of an identity, a deletion, a contraction, an inclusion of the
/// empty shape, a substitution, a contraction missing a wire and an
/// inclusion beside a point.
#[test]
fn map_forms_read_back()
{
    let form = |images, cover, wires| MapForm {
        images,
        cover,
        wires,
    };
    let corolla = shape!(1; o > 0, 0 > o);
    let closed_chain = shape!(2; 0 > 1);
    assert_eq!(
        SiteMap::identity(&corolla).form(&corolla),
        form(
            ImageForm::Singletons,
            Membership::Inside,
            WireForm::Bijective
        )
    );
    assert_eq!(
        site_map!([{}], []).form(&shape!(0)),
        form(
            ImageForm::AtMostOne,
            Membership::Inside,
            WireForm::Bijective
        )
    );
    assert_eq!(
        site_map!([{ 0 }, { 1 }], [0, 0]).form(&closed_chain),
        form(
            ImageForm::Singletons,
            Membership::Inside,
            WireForm::Surjective
        )
    );
    assert_eq!(
        site_map!([], []).form(&corolla),
        form(
            ImageForm::Singletons,
            Membership::Outside,
            WireForm::Injective
        )
    );
    assert_eq!(
        site_map!([{0, 1}], [0, 0]).form(&closed_chain),
        form(ImageForm::Larger, Membership::Inside, WireForm::Surjective)
    );
    assert_eq!(
        site_map!([{ 0 }, { 1 }], [0, 0]).form(&shape!(3; 0 > 1, 2 > o)),
        form(
            ImageForm::Singletons,
            Membership::Outside,
            WireForm::Neither
        )
    );
    assert_eq!(
        site_map!([{ 0 }], []).form(&shape!(2)),
        form(
            ImageForm::Singletons,
            Membership::Outside,
            WireForm::Bijective
        )
    );
}

/// The raising class is the maps that delete nothing and the lowering class
/// the deletions followed by an isomorphism; the identity is in both, and ε,
/// a point deleted and re-included, in neither.
#[test]
fn the_two_classes_sort_the_fixtures()
{
    let point = shape!(1);
    let corolla = shape!(1; o > 0, 0 > o);
    let closed_chain = shape!(2; 0 > 1);
    let fixtures = [
        (
            "the identity of C(1,1)",
            SiteMap::identity(&corolla),
            &corolla,
            Membership::Inside,
            Membership::Inside,
        ),
        (
            "• → ∅",
            site_map!([{}], []),
            &shape!(0),
            Membership::Outside,
            Membership::Inside,
        ),
        (
            "C(1,1) ⊔ • → C(1,1)",
            site_map!([{ 0 }, {}], [0, 1]),
            &corolla,
            Membership::Outside,
            Membership::Inside,
        ),
        (
            "p ⊔ q → p→q",
            site_map!([{ 0 }, { 1 }], [0, 0]),
            &closed_chain,
            Membership::Inside,
            Membership::Outside,
        ),
        (
            "C(1,1) → p→q",
            site_map!([{0, 1}], [0, 0]),
            &closed_chain,
            Membership::Inside,
            Membership::Outside,
        ),
        (
            "∅ → C(1,1)",
            site_map!([], []),
            &corolla,
            Membership::Inside,
            Membership::Outside,
        ),
        (
            "ε : • → •",
            site_map!([{}], []),
            &point,
            Membership::Outside,
            Membership::Outside,
        ),
    ];
    for (name, map, target, raising, lowering) in fixtures {
        assert_eq!(map.raising(), raising, "{name} raising");
        assert_eq!(map.lowering(target), lowering, "{name} lowering");
        let invertible = if raising == Membership::Inside && lowering == Membership::Inside {
            Invertibility::Invertible
        }
        else {
            Invertibility::NotInvertible
        };
        assert_eq!(
            map.invertibility(target),
            invertible,
            "{name} invertibility"
        );
    }
}

/// The catalogue serves a pinned hom set by class, finds a relabelled
/// shape, and refuses lookups past its range or bound.
#[test]
fn the_catalogue_serves_pinned_hom_sets()
{
    let catalogue = Catalogue::build(ShapeSize::from(3)).expect("the catalogue builds");
    let find = |shape: &Shape| match catalogue.find(shape) {
        | Maybe::Present(index) => index,
        | Maybe::Absent(reason) => panic!("the class is within the bound: {reason:?}"),
    };
    let point = find(&shape!(1));
    let closed_chain = find(&shape!(2; 1 > 0));
    match catalogue.maps(point, closed_chain) {
        | Maybe::Present(maps) => assert_eq!(maps.len(), 2, "• → p→q"),
        | Maybe::Absent(reason) => panic!("the pair is in range: {reason:?}"),
    }
    let past = ShapeIndex::from(catalogue.shapes().len());
    assert_eq!(
        catalogue.shape(past),
        Maybe::Absent(shape_lookup::Absent::OutOfRange)
    );
    assert_eq!(
        catalogue.maps(point, past),
        Maybe::Absent(hom_lookup::Absent::OutOfRange)
    );
    assert_eq!(
        catalogue.find(&shape!(2; o > 0, 0 > 1)),
        Maybe::Absent(shape_class::Absent::PastTheBound)
    );
}
