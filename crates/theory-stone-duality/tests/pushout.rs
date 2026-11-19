//! The pushout of two finite spaces along an open embedding: two chains
//! glued at their bottom point, every pair of small Boolean algebras glued
//! along opens of one size, two charts of Cantor space glued along their
//! common clopen, and the refusals of opens that do not match.

use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::Glued;
use gandr_theory_stone_duality::Membership;
use gandr_theory_stone_duality::SetRing;

/// The set of the points given.
macro_rules! points {
    ($($point:expr),* $(,)?) => {{
        let points: Vec<usize> = vec![$($point),*];
        points.into_iter().fold(ElementSet::EMPTY, |set, point| {
            set.union(ElementSet::single(Element::from(point)).expect("a point of one word"))
        })
    }};
}

/// The chain `0 < 1 < … < count − 1` as the lattice of its down-sets.
///
/// # Specification
/// trivial.
fn chain(count: ElementCount) -> SetRing
{
    let generators: Vec<ElementSet> = (0 .. usize::from(count))
        .map(|top| {
            (0 ..= top).fold(ElementSet::EMPTY, |set, point| {
                set.union(ElementSet::single(Element::from(point)).expect("a small point"))
            })
        })
        .collect();
    SetRing::generated(count, &generators, Budget::from(64_usize)).expect("a chain")
}

/// The Boolean algebra of every subset of `count` points.
///
/// # Specification
/// trivial.
fn boolean(count: ElementCount) -> SetRing
{
    let singletons: Vec<ElementSet> = (0 .. usize::from(count))
        .map(|point| ElementSet::single(Element::from(point)).expect("a small point"))
        .collect();
    SetRing::generated(count, &singletons, Budget::from(64_usize)).expect("a Boolean algebra")
}

#[test]
fn two_chains_glued_at_their_bottom_point_are_the_down_sets_of_a_fork()
{
    let line = chain(ElementCount::from(2_usize));
    let glued = line
        .glued(points![0], &line, points![0], Budget::from(64_usize))
        .expect("the bottoms match");
    // Point 2 is the second chain's top: the fork `0 < 1` and `0 < 2`.
    assert_eq!(glued.right_points(), &[
        Element::from(0_usize),
        Element::from(2_usize)
    ]);
    assert_eq!(glued.ring().members(), &[
        points![],
        points![0],
        points![0, 1],
        points![0, 2],
        points![0, 1, 2]
    ]);
    let spectrum = glued.ring().spectrum().expect("a spectrum");
    assert_eq!(spectrum.points().len(), 3);
    assert_eq!(glued.left(points![0, 2]), Ok(points![0]));
    assert_eq!(glued.right(points![0, 2]), Ok(points![0, 1]));
    assert_eq!(
        glued.left(points![2]),
        Err(DualityError::NotMember(points![2]))
    );
}

#[test]
fn each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout()
{
    let (mut pairs, mut agreeing) = (Vec::new(), Vec::new());
    for left_count in (0 ..= 3_usize).map(ElementCount::from) {
        for right_count in (0 ..= 3_usize).map(ElementCount::from) {
            let (left, right) = (boolean(left_count), boolean(right_count));
            for &open in left.members() {
                for &other_open in right.members() {
                    if open.count() != other_open.count() {
                        continue;
                    }
                    let glued = left
                        .glued(open, &right, other_open, Budget::from(64_usize))
                        .expect("Boolean opens of one size match");
                    // The pullback: the pairs of members that agree on the
                    // open, each read back through both restrictions.
                    pairs.clear();
                    for &member in glued.ring().members() {
                        let (first, second) = (
                            glued.left(member).expect("a member"),
                            glued.right(member).expect("a member"),
                        );
                        assert_eq!(left.holds(first), Membership::Inside);
                        assert_eq!(right.holds(second), Membership::Inside);
                        pairs.push((first, second));
                    }
                    agreeing.clear();
                    for &first in left.members() {
                        for &second in right.members() {
                            let shared = open
                                .elements()
                                .map(|point| first.contains(point) == Membership::Inside);
                            let other = other_open
                                .elements()
                                .map(|point| second.contains(point) == Membership::Inside);
                            if shared.eq(other) {
                                agreeing.push((first, second));
                            }
                        }
                    }
                    pairs.sort_unstable();
                    agreeing.sort_unstable();
                    assert_eq!(pairs, agreeing, "{open:?} and {other_open:?}");
                    // Each restriction keeps unions and intersections.
                    for &one in glued.ring().members() {
                        for &other in glued.ring().members() {
                            for restrict in [Glued::left, Glued::right] {
                                let (one_image, other_image) = (
                                    restrict(&glued, one).expect("a member"),
                                    restrict(&glued, other).expect("a member"),
                                );
                                assert_eq!(
                                    restrict(&glued, one.union(other)),
                                    Ok(one_image.union(other_image))
                                );
                                assert_eq!(
                                    restrict(&glued, one.meet(other)),
                                    Ok(one_image.meet(other_image))
                                );
                            }
                        }
                    }
                    // The spectrum is the pushout: each side's points, the
                    // shared open's once.
                    let spectrum = glued.ring().spectrum().expect("a spectrum");
                    let expected = usize::from(left_count)
                        .checked_add(usize::from(right_count))
                        .and_then(|sum| sum.checked_sub(usize::from(open.count())));
                    assert_eq!(Some(spectrum.points().len()), expected);
                }
            }
        }
    }
}

#[test]
fn two_cantor_charts_glue_along_their_common_clopen_to_one_boolean_algebra()
{
    // Two charts of the fourth level of Cantor space, four clopens each,
    // share two clopens. The glued algebra is the Boolean algebra on six.
    let chart = boolean(ElementCount::from(4_usize));
    let glued = chart
        .glued(points![2, 3], &chart, points![0, 1], Budget::from(64_usize))
        .expect("the common clopen matches");
    assert_eq!(glued.ring(), &boolean(ElementCount::from(6_usize)));
    assert_eq!(glued.right_points(), &[2_usize, 3, 4, 5].map(Element::from));
}

#[test]
fn a_gluing_refuses_opens_that_do_not_match()
{
    let line = chain(ElementCount::from(2_usize));
    let square = boolean(ElementCount::from(2_usize));
    let room = Budget::from(64_usize);
    assert_eq!(
        line.glued(points![1], &line, points![0], room),
        Err(DualityError::NotMember(points![1]))
    );
    assert_eq!(
        line.glued(points![0], &line, points![0, 1], room),
        Err(DualityError::OpenSizes(
            ElementCount::from(1_usize),
            ElementCount::from(2_usize)
        ))
    );
    // The chain localised at its top lacks `{1}`, which the square holds.
    assert_eq!(
        line.glued(points![0, 1], &square, points![0, 1], room),
        Err(DualityError::LocalisationsDiffer(points![1]))
    );
    // Two cubes side by side have 64 members, one past a budget of 63.
    let cube = boolean(ElementCount::from(3_usize));
    assert_eq!(
        cube.glued(points![], &cube, points![], Budget::from(63_usize)),
        Err(DualityError::PastBudget(Budget::from(63_usize)))
    );
    // Two carriers of 33 points side by side pass one machine word.
    let wide = SetRing::generated(ElementCount::from(33_usize), &[], room).expect("a wide lattice");
    assert_eq!(
        wide.glued(points![], &wide, points![], room),
        Err(DualityError::TooManyElements(ElementCount::from(66_usize)))
    );
}
