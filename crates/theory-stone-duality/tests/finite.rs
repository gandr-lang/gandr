//! Finite posets against a naive closure, Birkhoff duality in both
//! directions, and monotone maps against their preimages.
//!
//! The reference readings here are written apart from the crate: a relation
//! closes by repeating unions until nothing changes, a set is a down-set when
//! it holds the closure of each of its elements, and a lattice of sets closes
//! by repeating unions and intersections until nothing changes.

use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::FinitePoset;
use gandr_theory_stone_duality::GeneratorCount;
use gandr_theory_stone_duality::Membership;
use gandr_theory_stone_duality::MonotoneMap;
use gandr_theory_stone_duality::SetRing;

/// The Dedekind numbers: the down-sets of the cubes on up to four axes.
const DEDEKIND: [usize; 5] = [2, 3, 6, 20, 168];

/// Whether a naive closure holds a cycle, and its least pair when it does.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Outcome
{
    /// No two distinct elements lie each below the other.
    Acyclic,
    /// These two elements lie each below the other.
    Cycle(Element, Element),
}

/// A finite poset beside the naive closure of its relation.
struct Small
{
    /// The poset the crate builds.
    poset: FinitePoset,
    /// The principal down-set of each element, by the naive closure.
    closure: Vec<ElementSet>,
}

/// The set of one element, read from its bit.
///
/// # Specification
/// trivial.
fn single(element: Element) -> ElementSet
{
    let shift = u32::try_from(usize::from(element)).expect("a small element");
    ElementSet::from(1_u64.checked_shl(shift).expect("an element below a word"))
}

/// Whether a set holds an element, read from its bit.
///
/// # Specification
/// trivial.
fn holds(
    set: ElementSet,
    element: Element,
) -> Membership
{
    if u64::from(set) & u64::from(single(element)) == 0 {
        Membership::Outside
    }
    else {
        Membership::Inside
    }
}

/// Whether one set is included in another, read from their bits.
///
/// # Specification
/// trivial.
fn included(
    lower: ElementSet,
    upper: ElementSet,
) -> Comparison
{
    if u64::from(lower) & u64::from(upper) == u64::from(lower) {
        Comparison::Below
    }
    else {
        Comparison::NotBelow
    }
}

/// The union of two sets, read from their bits.
///
/// # Specification
/// trivial.
fn union(
    left: ElementSet,
    right: ElementSet,
) -> ElementSet
{
    ElementSet::from(u64::from(left) | u64::from(right))
}

/// The intersection of two sets, read from their bits.
///
/// # Specification
/// trivial.
fn meet(
    left: ElementSet,
    right: ElementSet,
) -> ElementSet
{
    ElementSet::from(u64::from(left) & u64::from(right))
}

/// The elements of a carrier of `count` points.
///
/// # Specification
/// trivial.
fn elements(count: ElementCount) -> impl Iterator<Item = Element>
{
    (0 .. usize::from(count)).map(Element::from)
}

/// The whole carrier of `count` points.
///
/// # Specification
/// trivial.
fn whole(count: ElementCount) -> ElementSet
{
    elements(count).fold(ElementSet::EMPTY, |set, element| {
        union(set, single(element))
    })
}

/// The subsets of a carrier of `count` points, in mask order.
///
/// # Specification
/// trivial.
fn subsets(count: ElementCount) -> impl Iterator<Item = ElementSet>
{
    (0 ..= u64::from(whole(count))).map(ElementSet::from)
}

/// The pairs of distinct elements of a carrier of `count` points.
///
/// # Specification
/// trivial.
fn pairs(count: ElementCount) -> Vec<(Element, Element)>
{
    elements(count)
        .flat_map(|lower| elements(count).map(move |upper| (lower, upper)))
        .filter(|&(lower, upper)| lower != upper)
        .collect()
}

/// The pairs whose positions `choice` holds, written into `relation`.
///
/// # Specification
/// trivial.
fn pick(
    relation: &mut Vec<(Element, Element)>,
    pairs: &[(Element, Element)],
    choice: ElementSet,
)
{
    relation.clear();
    relation.extend(
        pairs
            .iter()
            .enumerate()
            .filter(|&(index, _)| holds(choice, Element::from(index)) == Membership::Inside)
            .map(|(_, pair)| *pair),
    );
}

/// The reflexive and transitive closure of a relation, by repeated unions
/// until nothing changes.
///
/// # Specification
/// trivial.
fn naive_closure(
    count: ElementCount,
    relation: &[(Element, Element)],
) -> Vec<ElementSet>
{
    let mut below: Vec<ElementSet> = elements(count).map(single).collect();
    for &(lower, upper) in relation {
        let slot = &mut below[usize::from(upper)];
        *slot = union(*slot, single(lower));
    }
    loop {
        let mut changed = Membership::Outside;
        for index in 0 .. below.len() {
            let current = below[index];
            let grown = elements(count)
                .filter(|element| holds(current, *element) == Membership::Inside)
                .fold(current, |set, element| {
                    union(set, below[usize::from(element)])
                });
            if grown != current {
                below[index] = grown;
                changed = Membership::Inside;
            }
        }
        if changed == Membership::Outside {
            return below;
        }
    }
}

/// The least pair of a closure that lies each below the other.
///
/// # Specification
/// trivial.
fn naive_cycle(closure: &[ElementSet]) -> Outcome
{
    for (upper, upper_set) in closure.iter().enumerate() {
        for (lower, lower_set) in closure.iter().enumerate().take(upper) {
            if holds(*upper_set, Element::from(lower)) == Membership::Inside
                && holds(*lower_set, Element::from(upper)) == Membership::Inside
            {
                return Outcome::Cycle(Element::from(lower), Element::from(upper));
            }
        }
    }
    Outcome::Acyclic
}

/// Every poset on up to three elements, with its naive closure.
///
/// # Specification
/// trivial.
fn small_posets() -> Vec<Small>
{
    let mut all = Vec::new();
    let mut relation = Vec::new();
    for size in 0 ..= 3_usize {
        let count = ElementCount::from(size);
        let pairs = pairs(count);
        for choice in subsets(ElementCount::from(pairs.len())) {
            pick(&mut relation, &pairs, choice);
            let closure = naive_closure(count, &relation);
            if naive_cycle(&closure) == Outcome::Acyclic {
                let poset = FinitePoset::new(count, &relation).expect("an acyclic relation");
                all.push(Small { poset, closure });
            }
        }
    }
    all
}

/// Inserts `set` into the sorted `members` unless it is already there, and
/// says whether it was new.
///
/// # Specification
/// trivial.
fn insert(
    members: &mut Vec<ElementSet>,
    set: ElementSet,
) -> Membership
{
    match members.binary_search(&set) {
        Ok(_) => Membership::Inside,
        Err(position) => {
            members.insert(position, set);
            Membership::Outside
        },
    }
}

/// The closure of a family of sets under union and intersection with the
/// empty set and the whole carrier, by repeated passes until nothing changes.
///
/// # Specification
/// trivial.
fn naive_ring(
    carrier: ElementCount,
    generators: &[ElementSet],
) -> Vec<ElementSet>
{
    let mut members = Vec::new();
    for &set in generators
        .iter()
        .chain(&[ElementSet::EMPTY, whole(carrier)])
    {
        let _new = insert(&mut members, set);
    }
    loop {
        let mut changed = Membership::Outside;
        for left in 0 .. members.len() {
            for right in 0 .. members.len() {
                let (first, second) = (members[left], members[right]);
                for made in [union(first, second), meet(first, second)] {
                    if insert(&mut members, made) == Membership::Outside {
                        changed = Membership::Inside;
                    }
                }
            }
        }
        if changed == Membership::Outside {
            return members;
        }
    }
}

/// Checks Birkhoff duality on one poset: its down-sets are the subsets that
/// hold the closure of each element, and their spectrum is the poset again.
///
/// # Specification
/// trivial.
fn check_birkhoff(small: &Small)
{
    let poset = &small.poset;
    let closure = &small.closure;
    let count = poset.count();
    let lattice = poset.down_sets(Budget::from(64)).expect("a small lattice");
    let naive: Vec<ElementSet> = subsets(count)
        .filter(|set| {
            elements(count).all(|element| {
                holds(*set, element) == Membership::Outside
                    || included(closure[usize::from(element)], *set) == Comparison::Below
            })
        })
        .collect();
    assert_eq!(lattice.members(), naive.as_slice());
    for set in subsets(count) {
        let expected = elements(count)
            .filter(|element| holds(set, *element) == Membership::Inside)
            .fold(ElementSet::EMPTY, |down, element| {
                union(down, closure[usize::from(element)])
            });
        assert_eq!(poset.down_closure(set), Ok(expected));
    }
    let spectrum = lattice.spectrum().expect("a spectrum");
    let mut principal = closure.clone();
    principal.sort_unstable();
    assert_eq!(spectrum.points(), principal.as_slice());
    let points = spectrum.points();
    for lower in elements(count) {
        let lower_point = points
            .binary_search(&closure[usize::from(lower)])
            .expect("a point");
        for upper in elements(count) {
            let upper_point = points
                .binary_search(&closure[usize::from(upper)])
                .expect("a point");
            assert_eq!(
                spectrum
                    .poset()
                    .compare(Element::from(lower_point), Element::from(upper_point)),
                poset.compare(lower, upper)
            );
        }
    }
}

/// Checks one family of sets: the lattice it generates is the naive one, its
/// spectrum is its join-irreducible members, and the down-sets of the
/// spectrum read back to the lattice one to one.
///
/// # Specification
/// trivial.
fn check_ring(
    carrier: ElementCount,
    generators: &[ElementSet],
)
{
    let ring = SetRing::generated(carrier, generators, Budget::from(64)).expect("a small lattice");
    let naive = naive_ring(carrier, generators);
    assert_eq!(ring.members(), naive.as_slice(), "{generators:?}");
    for point in elements(carrier) {
        let least = naive
            .iter()
            .filter(|member| holds(**member, point) == Membership::Inside)
            .fold(whole(carrier), |set, member| meet(set, *member));
        assert_eq!(ring.least_member(point), Ok(least));
    }
    let irreducible: Vec<ElementSet> = naive
        .iter()
        .copied()
        .filter(|member| {
            let below = naive
                .iter()
                .filter(|other| *other != member && included(**other, *member) == Comparison::Below)
                .fold(ElementSet::EMPTY, |set, other| union(set, *other));
            *member != ElementSet::EMPTY && below != *member
        })
        .collect();
    let spectrum = ring.spectrum().expect("a spectrum");
    assert_eq!(spectrum.points(), irreducible.as_slice());
    for member in ring.members() {
        assert_eq!(spectrum.member(spectrum.below(*member)), Ok(*member));
    }
    let downs = spectrum
        .poset()
        .down_sets(Budget::from(64))
        .expect("a small lattice");
    let mut read: Vec<ElementSet> = downs
        .members()
        .iter()
        .map(|down| spectrum.member(*down).expect("a member"))
        .collect();
    read.sort_unstable();
    assert_eq!(read.as_slice(), ring.members());
    let past = Element::from(usize::from(carrier));
    assert_eq!(
        ring.least_member(past),
        Err(DualityError::ElementOutside(past))
    );
}

/// The images that `code` names, read as digits in the base of the target's
/// count.
///
/// # Specification
/// trivial.
fn decode(
    code: ElementSet,
    sources: ElementCount,
    targets: ElementCount,
) -> Vec<Element>
{
    let base = u64::try_from(usize::from(targets)).expect("a small poset");
    let mut rest = u64::from(code);
    elements(sources)
        .map(|_| {
            let digit = rest.checked_rem(base).expect("a nonempty target");
            rest = rest.checked_div(base).expect("a nonempty target");
            Element::from(usize::try_from(digit).expect("a small digit"))
        })
        .collect()
}

/// Checks every map from one small poset to another: the monotone ones are
/// admitted, their preimages are the naive ones, and each reads back from
/// them.
///
/// # Specification
/// trivial.
fn check_maps(
    source: &Small,
    target: &Small,
)
{
    let sources = source.poset.count();
    let targets = target.poset.count();
    let power = u32::try_from(usize::from(sources)).expect("a small poset");
    let Some(maps) = usize::from(targets).checked_pow(power)
    else {
        return;
    };
    let mut preimages = Vec::with_capacity(usize::from(targets));
    for code in 0 .. u64::try_from(maps).expect("a few maps") {
        let code = ElementSet::from(code);
        let images = decode(code, sources, targets);
        let ordered = elements(sources).all(|upper| {
            elements(sources).all(|lower| {
                let lower_image = images[usize::from(lower)];
                let upper_image = images[usize::from(upper)];
                holds(source.closure[usize::from(upper)], lower) == Membership::Outside
                    || holds(target.closure[usize::from(upper_image)], lower_image)
                        == Membership::Inside
            })
        });
        match MonotoneMap::new(&source.poset, &target.poset, images) {
            Ok(map) => {
                assert!(ordered, "{code:?}");
                assert_eq!(map.images(), decode(code, sources, targets).as_slice());
                preimages.clear();
                for down in &target.closure {
                    let naive = elements(sources)
                        .filter(|element| {
                            holds(*down, map.images()[usize::from(*element)]) == Membership::Inside
                        })
                        .fold(ElementSet::EMPTY, |set, element| {
                            union(set, single(element))
                        });
                    let preimage = map.preimage(*down);
                    assert_eq!(preimage, naive);
                    preimages.push(preimage);
                }
                assert_eq!(
                    MonotoneMap::of_preimages(&source.poset, &target.poset, &preimages),
                    Ok(map)
                );
            },
            Err(DualityError::NotMonotone(..)) => assert!(!ordered, "{code:?}"),
            Err(error) => panic!("{code:?} refused by {error:?}"),
        }
    }
}

#[test]
fn posets_close_their_relation_and_refuse_cycles()
{
    let mut relation = Vec::new();
    for size in 0 ..= 3_usize {
        let count = ElementCount::from(size);
        let pairs = pairs(count);
        for choice in subsets(ElementCount::from(pairs.len())) {
            pick(&mut relation, &pairs, choice);
            let closure = naive_closure(count, &relation);
            match (FinitePoset::new(count, &relation), naive_cycle(&closure)) {
                (Ok(poset), Outcome::Acyclic) => {
                    assert_eq!(poset.count(), count);
                    for upper in elements(count) {
                        assert_eq!(poset.below(upper), Ok(closure[usize::from(upper)]));
                        for lower in elements(count) {
                            let expected = included(single(lower), closure[usize::from(upper)]);
                            assert_eq!(poset.compare(lower, upper), Ok(expected));
                        }
                    }
                    let past = Element::from(size);
                    assert_eq!(poset.below(past), Err(DualityError::ElementOutside(past)));
                },
                (Err(DualityError::Cycle(first, second)), Outcome::Cycle(lower, upper)) => {
                    assert_eq!((first, second), (lower, upper));
                },
                (verdict, outcome) => panic!("{relation:?}: {verdict:?} against {outcome:?}"),
            }
        }
    }
    let two = ElementCount::from(2);
    assert_eq!(
        FinitePoset::new(two, &[(Element::from(2), Element::from(0))]),
        Err(DualityError::ElementOutside(Element::from(2)))
    );
    assert_eq!(
        FinitePoset::new(two, &[(Element::from(0), Element::from(2))]),
        Err(DualityError::ElementOutside(Element::from(2)))
    );
    let triangle = [
        (Element::from(0), Element::from(1)),
        (Element::from(1), Element::from(2)),
        (Element::from(2), Element::from(0)),
    ];
    assert_eq!(
        FinitePoset::new(ElementCount::from(3), &triangle),
        Err(DualityError::Cycle(Element::from(0), Element::from(1)))
    );
    assert_eq!(
        ElementSet::single(Element::from(63)),
        Ok(single(Element::from(63)))
    );
    assert_eq!(
        ElementSet::single(Element::from(64)),
        Err(DualityError::ElementOutside(Element::from(64)))
    );
}

#[test]
fn birkhoff_duality_round_trips_on_small_posets()
{
    for small in &small_posets() {
        check_birkhoff(small);
    }
    // The down-sets of a cube are counted by the Dedekind numbers.
    for (size, dedekind) in DEDEKIND.into_iter().enumerate() {
        let cube = FinitePoset::cube(GeneratorCount::from(size)).expect("a small cube");
        let lattice = cube.down_sets(Budget::from(256)).expect("a small lattice");
        assert_eq!(lattice.members().len(), dedekind);
        for lower in elements(cube.count()) {
            for upper in elements(cube.count()) {
                let order = included(
                    ElementSet::from(u64::try_from(usize::from(lower)).expect("a vertex")),
                    ElementSet::from(u64::try_from(usize::from(upper)).expect("a vertex")),
                );
                assert_eq!(cube.compare(lower, upper), Ok(order));
            }
        }
    }
    let seven = GeneratorCount::from(7);
    assert_eq!(FinitePoset::cube(seven), Err(DualityError::TooWide(seven)));
}

#[test]
fn a_ring_of_sets_reads_back_from_its_spectrum()
{
    let mut generators = Vec::new();
    for size in 0 ..= 3_usize {
        let carrier = ElementCount::from(size);
        let family_count = ElementCount::from(subsets(carrier).count());
        for family in subsets(family_count) {
            generators.clear();
            generators.extend(
                subsets(carrier)
                    .enumerate()
                    .filter(|&(index, _)| holds(family, Element::from(index)) == Membership::Inside)
                    .map(|(_, set)| set),
            );
            check_ring(carrier, &generators);
        }
    }
    let two = ElementCount::from(2);
    assert_eq!(
        SetRing::generated(two, &[ElementSet::from(0b100)], Budget::from(64)),
        Err(DualityError::ElementOutside(Element::from(2)))
    );
    let ring =
        SetRing::generated(two, &[ElementSet::from(0b01)], Budget::from(64)).expect("a lattice");
    let spectrum = ring.spectrum().expect("a spectrum");
    let past = Element::from(spectrum.points().len());
    assert_eq!(
        spectrum.member(single(past)),
        Err(DualityError::ElementOutside(past))
    );
}

#[test]
fn monotone_maps_and_preimages_go_one_to_one()
{
    let posets = small_posets();
    for source in &posets {
        for target in &posets {
            check_maps(source, target);
        }
    }
    let chain = FinitePoset::new(ElementCount::from(2), &[(
        Element::from(0),
        Element::from(1),
    )])
    .expect("a chain");
    let point = FinitePoset::new(ElementCount::from(1), &[]).expect("a point");
    let pair = FinitePoset::new(ElementCount::from(2), &[]).expect("an antichain");
    assert_eq!(
        MonotoneMap::new(&chain, &chain, vec![Element::from(1), Element::from(0)]),
        Err(DualityError::NotMonotone(
            Element::from(0),
            Element::from(1)
        ))
    );
    assert_eq!(
        MonotoneMap::new(&chain, &chain, vec![Element::from(0)]),
        Err(DualityError::ImageCount)
    );
    assert_eq!(
        MonotoneMap::new(&point, &chain, vec![Element::from(2)]),
        Err(DualityError::ElementOutside(Element::from(2)))
    );
    let both = single(Element::from(0));
    assert_eq!(
        MonotoneMap::of_preimages(&point, &pair, &[both, both]),
        Err(DualityError::NoLeastImage(Element::from(0)))
    );
    assert_eq!(
        MonotoneMap::of_preimages(&point, &chain, &[both, ElementSet::EMPTY]),
        Err(DualityError::NotHomomorphism(Element::from(1)))
    );
    assert_eq!(
        MonotoneMap::of_preimages(&point, &chain, &[both]),
        Err(DualityError::ImageCount)
    );
    assert_eq!(
        MonotoneMap::of_preimages(&point, &chain, &[single(Element::from(1)), both]),
        Err(DualityError::ElementOutside(Element::from(1)))
    );
}

#[test]
fn enumerations_refuse_past_their_budget()
{
    let three = ElementCount::from(3);
    let antichain = FinitePoset::new(three, &[]).expect("an antichain");
    assert_eq!(
        antichain
            .down_sets(Budget::from(8))
            .map(|lattice| lattice.members().len()),
        Ok(8)
    );
    assert_eq!(
        antichain.down_sets(Budget::from(7)),
        Err(DualityError::PastBudget(Budget::from(7)))
    );
    assert_eq!(
        antichain.down_sets(Budget::from(0)),
        Err(DualityError::PastBudget(Budget::from(0)))
    );
    let singletons: Vec<ElementSet> = elements(three).map(single).collect();
    assert_eq!(
        SetRing::generated(three, &singletons, Budget::from(8))
            .map(|lattice| lattice.members().len()),
        Ok(8)
    );
    assert_eq!(
        SetRing::generated(three, &singletons, Budget::from(7)),
        Err(DualityError::PastBudget(Budget::from(7)))
    );
    let widest = FinitePoset::new(ElementCount::from(64), &[]).expect("the widest antichain");
    assert_eq!(widest.count(), ElementCount::from(64));
    assert_eq!(
        FinitePoset::new(ElementCount::from(65), &[]),
        Err(DualityError::TooManyElements(ElementCount::from(65)))
    );
    let empty =
        SetRing::generated(ElementCount::from(0), &[], Budget::from(1)).expect("the empty lattice");
    assert_eq!(empty.members(), &[ElementSet::EMPTY]);
}
