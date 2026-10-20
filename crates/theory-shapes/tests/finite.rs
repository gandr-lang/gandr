//! Finite subshapes: every subset pair of the small carriers, the union
//! square's universal map, and the refusals at the carrier's edges.

use alloc::collections::BTreeSet;

use gandr_theory_shapes::Block;
use gandr_theory_shapes::Cofibration;
use gandr_theory_shapes::Inclusion;
use gandr_theory_shapes::Leg;
use gandr_theory_shapes::Membership;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::PointCount;
use gandr_theory_shapes::SetOperation;
use gandr_theory_shapes::ShapeError;
use gandr_theory_shapes::Subshape;
use gandr_theory_shapes::UnionSquare;

use crate::carriers::Mask;
use crate::carriers::points;
use crate::carriers::subsets;

/// The points a mask holds, in carrier order.
///
/// # Specification
/// trivial.
fn members(
    count: PointCount,
    mask: Mask,
) -> Vec<Point>
{
    points(count)
        .filter(|point| mask.at(*point) == Membership::Inside)
        .collect()
}

/// Every table of the given length into the two-point carrier, in counting
/// order.
///
/// # Specification
/// trivial.
fn tables(length: PointCount) -> Vec<Vec<Point>>
{
    let width = u32::try_from(usize::from(length)).expect("a short table");
    (0 .. 1_usize.checked_shl(width).expect("a short table"))
        .map(|bits| {
            points(length)
                .map(|position| match Mask(bits).at(position) {
                    Membership::Inside => Point::from(1_usize),
                    Membership::Outside => Point::from(0_usize),
                })
                .collect()
        })
        .collect()
}

/// The value a table over `domain` gives at `point`.
///
/// # Specification
/// trivial.
fn value_at(
    table: &[Point],
    domain: &[Point],
    point: Point,
) -> Point
{
    let position = domain
        .iter()
        .position(|member| *member == point)
        .expect("a point of the domain");
    table[position]
}

#[test]
fn all_small_union_squares()
{
    for size in 0_usize ..= 4 {
        let count = PointCount::from(size);
        let carrier = subsets(count);
        let full = Subshape::new(count, &members(count, Mask(usize::MAX))).expect("full");
        for &(left_mask, ref left) in &carrier {
            let complement = left.complement();
            assert_eq!(left.ambient(), count);
            assert_eq!(complement.ambient(), count);
            for point in points(count) {
                assert_eq!(left.contains(point), Ok(left_mask.at(point)));
                assert_eq!(complement.contains(point), Ok(Mask(!left_mask.0).at(point)));
            }
            for &(right_mask, ref right) in &carrier {
                let square = UnionSquare::new(left, right).expect("square");
                let meet = left.combine(right, SetOperation::Meet).expect("meet");
                let union = left.combine(right, SetOperation::Union).expect("union");
                assert_eq!(meet.ambient(), count);
                assert_eq!(union.ambient(), count);
                assert_eq!(square.blocks().len(), size);
                let mut escape = None;
                for point in points(count) {
                    let in_left = left_mask.at(point) == Membership::Inside;
                    let in_right = right_mask.at(point) == Membership::Inside;
                    assert_eq!(
                        meet.contains(point),
                        Ok(Mask(left_mask.0 & right_mask.0).at(point))
                    );
                    assert_eq!(
                        union.contains(point),
                        Ok(Mask(left_mask.0 | right_mask.0).at(point))
                    );
                    assert_eq!(
                        square.blocks()[usize::from(point)],
                        match (in_left, in_right) {
                            (true, true) => Block::Both,
                            (true, false) => Block::Left,
                            (false, true) => Block::Right,
                            (false, false) => Block::Neither,
                        }
                    );
                    if in_left && !in_right && escape.is_none() {
                        escape = Some(point);
                    }
                }
                if let Some(point) = escape {
                    assert_eq!(left.included(right), Ok(Inclusion::Escapes(point)));
                    assert_eq!(
                        Cofibration::new(left.clone(), right.clone()),
                        Err(ShapeError::NotIncluded(point))
                    );
                }
                else {
                    assert_eq!(left.included(right), Ok(Inclusion::Included));
                    let inclusion =
                        Cofibration::new(left.clone(), right.clone()).expect("an inclusion");
                    let (source, target, rest) = inclusion.presentation();
                    assert_eq!(source, left);
                    assert_eq!(target, right);
                    for point in points(count) {
                        assert_eq!(
                            rest.contains(point),
                            Ok(Mask(right_mask.0 & !left_mask.0).at(point))
                        );
                    }
                }
                // The five arrows of the square are inclusions.
                for (source, target) in [
                    (&meet, left),
                    (&meet, right),
                    (left, &union),
                    (right, &union),
                    (&union, &full),
                ] {
                    assert_eq!(source.included(target), Ok(Inclusion::Included));
                }
            }
        }
    }
}

#[test]
fn union_square_has_unique_mediators()
{
    // Every pair of subshapes of carriers up to three points, every pair of
    // maps out of them into the two-point carrier, and every candidate map
    // out of their union: the mediator exists exactly when the maps agree on
    // the meet, and it is the one candidate that restricts to both.
    let mut glued = 0_usize;
    let mut refused = 0_usize;
    let mut right_set: BTreeSet<Point> = BTreeSet::new();
    for size in 0_usize ..= 3 {
        let count = PointCount::from(size);
        let carrier = subsets(count);
        for &(left_mask, ref left) in &carrier {
            for &(right_mask, ref right) in &carrier {
                let square = UnionSquare::new(left, right).expect("square");
                let left_points = members(count, left_mask);
                let right_points = members(count, right_mask);
                let union_points = members(count, Mask(left_mask.0 | right_mask.0));
                let candidates = tables(PointCount::from(union_points.len()));
                right_set.clear();
                right_set.extend(right_points.iter().copied());
                for left_map in tables(PointCount::from(left_points.len())) {
                    for right_map in tables(PointCount::from(right_points.len())) {
                        let mut restricting = candidates.iter().filter(|candidate| {
                            left_points.iter().all(|point| {
                                value_at(candidate, &union_points, *point)
                                    == value_at(&left_map, &left_points, *point)
                            }) && right_points.iter().all(|point| {
                                value_at(candidate, &union_points, *point)
                                    == value_at(&right_map, &right_points, *point)
                            })
                        });
                        let first = restricting.next();
                        let another = restricting.next();
                        let disagreement = left_points.iter().copied().find(|point| {
                            right_set.contains(point)
                                && value_at(&left_map, &left_points, *point)
                                    != value_at(&right_map, &right_points, *point)
                        });
                        match square.mediator(&left_map, &right_map) {
                            Ok(table) => {
                                assert_eq!((first, another), (Some(&table), None));
                                glued = glued.saturating_add(1);
                            },
                            Err(error) => {
                                assert_eq!(first, None);
                                assert_eq!(Some(error), disagreement.map(ShapeError::Disagreement));
                                refused = refused.saturating_add(1);
                            },
                        }
                    }
                }
            }
        }
    }
    assert!(glued > 0 && refused > 0, "both outcomes are exercised");
}

#[test]
fn finite_boundaries_are_checked()
{
    let point = Point::from;
    let empty = Subshape::new(PointCount::from(0_usize), &[]).expect("empty");
    assert_eq!(
        empty.contains(point(0)),
        Err(ShapeError::PointOutside(point(0)))
    );
    assert_eq!(
        Subshape::new(PointCount::from(1_usize), &[point(1)]),
        Err(ShapeError::PointOutside(point(1)))
    );
    assert_eq!(
        Subshape::new(PointCount::from(2_usize), &[point(0), point(2)]),
        Err(ShapeError::PointOutside(point(2)))
    );
    let one = Subshape::new(PointCount::from(1_usize), &[point(0), point(0)])
        .expect("a repeated point is listed once");
    assert_eq!(one.contains(point(0)), Ok(Membership::Inside));
    assert_eq!(
        one.contains(point(1)),
        Err(ShapeError::PointOutside(point(1)))
    );
    assert_eq!(one.complement().contains(point(0)), Ok(Membership::Outside));
    assert_eq!(empty.complement(), empty);
    for operation in [SetOperation::Meet, SetOperation::Union] {
        assert_eq!(
            empty.combine(&one, operation),
            Err(ShapeError::DifferentAmbient)
        );
        assert_eq!(
            one.combine(&empty, operation),
            Err(ShapeError::DifferentAmbient)
        );
    }
    assert_eq!(empty.included(&one), Err(ShapeError::DifferentAmbient));
    assert_eq!(one.included(&empty), Err(ShapeError::DifferentAmbient));
    assert_eq!(
        Cofibration::new(empty.clone(), one.clone()),
        Err(ShapeError::DifferentAmbient)
    );
    assert_eq!(
        Cofibration::new(one.clone(), empty.clone()),
        Err(ShapeError::DifferentAmbient)
    );
    assert_eq!(
        UnionSquare::new(&empty, &one),
        Err(ShapeError::DifferentAmbient)
    );
    assert_eq!(
        UnionSquare::new(&one, &empty),
        Err(ShapeError::DifferentAmbient)
    );

    // Blocks `Left, Both, Right` over three points: the left map has two
    // values, the right map two, agreeing at point 1.
    let three = PointCount::from(3_usize);
    let left = Subshape::new(three, &[point(0), point(1)]).expect("left");
    let right = Subshape::new(three, &[point(1), point(2)]).expect("right");
    let square = UnionSquare::new(&left, &right).expect("square");
    let (a, b, c, d) = (point(0), point(1), point(2), point(3));
    assert_eq!(square.mediator(&[a, b], &[b, c]), Ok(vec![a, b, c]));
    for (left_map, right_map, refusal) in [
        (vec![], vec![b, c], ShapeError::MapLength(Leg::Left)),
        (vec![a], vec![b, c], ShapeError::MapLength(Leg::Left)),
        (vec![a, b], vec![], ShapeError::MapLength(Leg::Right)),
        (vec![a, b], vec![b], ShapeError::MapLength(Leg::Right)),
        (vec![a, b, d], vec![b, c], ShapeError::MapLength(Leg::Left)),
        (vec![a, b], vec![b, c, d], ShapeError::MapLength(Leg::Right)),
        (
            vec![a, b, d],
            vec![b, c, d],
            ShapeError::MapLength(Leg::Left),
        ),
        (vec![a, b], vec![c, c], ShapeError::Disagreement(point(1))),
        (vec![a, c], vec![b], ShapeError::Disagreement(point(1))),
    ] {
        assert_eq!(square.mediator(&left_map, &right_map), Err(refusal));
    }
}
