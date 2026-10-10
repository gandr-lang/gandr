//! Exhaustive small finite-set and outer-pushout checks.

use gandr_theory_shapes::boundary::Point;
use gandr_theory_shapes::boundary::PointCount;
use gandr_theory_shapes::boundary::ShapeError;
use gandr_theory_shapes::finite::Block;
use gandr_theory_shapes::finite::Cofibration;
use gandr_theory_shapes::finite::Membership;
use gandr_theory_shapes::finite::SetOperation;
use gandr_theory_shapes::finite::Subshape;
use gandr_theory_shapes::finite::UnionSquare;

/// Enumerates every subset of a carrier with at most four points.
///
/// # Specification
/// - requires: a carrier of at most four points.
/// - provides: every membership vector once.
/// - panics: an invalid fixture size.
///
/// # Adequacy
/// - hypothesis: L2 all subsets expose point loss and incorrect inclusion.
/// - witness: `tests::finite::all_small_union_squares`
fn subsets(count: PointCount) -> Vec<Subshape>
{
    let width = u32::try_from(usize::from(count)).expect("small carrier");
    (0_usize .. 1_usize.checked_shl(width).expect("small carrier"))
        .map(|mask| {
            let points: Vec<Point> = (0 .. usize::from(count))
                .filter(|point| {
                    mask & 1_usize
                        .checked_shl(u32::try_from(*point).expect("point"))
                        .expect("point bit")
                        != 0
                })
                .map(Point::from)
                .collect();
            Subshape::new(count, &points).expect("subset")
        })
        .collect()
}

#[test]
fn all_small_union_squares()
{
    for size in 0_usize ..= 4 {
        let carrier = subsets(PointCount::from(size));
        for left in &carrier {
            let complement = left.complement();
            for point in 0 .. size {
                assert_ne!(
                    left.contains(Point::from(point)),
                    complement.contains(Point::from(point))
                );
            }
            for right in &carrier {
                let square = UnionSquare::new(left, right).expect("square");
                let meet = left.combine(right, SetOperation::Meet).expect("meet");
                let union = left.combine(right, SetOperation::Union).expect("union");
                let mut first_outside = None;
                for point in 0 .. size {
                    let a = left.decisions()[point] == Membership::Inside;
                    let b = right.decisions()[point] == Membership::Inside;
                    assert_eq!(meet.decisions()[point] == Membership::Inside, a && b);
                    assert_eq!(union.decisions()[point] == Membership::Inside, a || b);
                    assert_eq!(square.blocks()[point], match (a, b) {
                        | (true, true) => Block::Both,
                        | (true, false) => Block::Left,
                        | (false, true) => Block::Right,
                        | (false, false) => Block::Neither,
                    });
                    if a && !b && first_outside.is_none() {
                        first_outside = Some(Point::from(point));
                    }
                }
                match Cofibration::new(left.clone(), right.clone()) {
                    | Ok(inclusion) => {
                        assert_eq!(first_outside, None);
                        let (source, target, complement) = inclusion.presentation();
                        assert_eq!(
                            source.combine(complement, SetOperation::Union),
                            Ok(target.clone())
                        );
                        assert!(
                            source
                                .combine(complement, SetOperation::Meet)
                                .expect("meet")
                                .decisions()
                                .iter()
                                .all(|v| *v == Membership::Outside)
                        );
                    },
                    | Err(error) => assert_eq!(
                        error,
                        ShapeError::NotIncluded(first_outside.expect("noninclusion point"))
                    ),
                }
                // All five arrows of the four-block square are inclusions.
                for (source, target) in [
                    (&meet, left),
                    (&meet, right),
                    (left, &union),
                    (right, &union),
                    (&union, carrier.last().expect("full carrier")),
                ] {
                    let arrow =
                        Cofibration::new(source.clone(), target.clone()).expect("square leg");
                    let (source, target, complement) = arrow.presentation();
                    assert_eq!(
                        source.combine(complement, SetOperation::Union),
                        Ok(target.clone())
                    );
                }
            }
        }
    }
}

#[test]
fn union_square_has_unique_mediators()
{
    // Every pair of subsets of Fin(0)..Fin(3), every pair of maps to Bool,
    // and every candidate union map: existence iff overlap agrees, unique
    // up to values outside the union (which are not part of the map).
    for size in 0_usize ..= 3 {
        let carrier = subsets(PointCount::from(size));
        for left in &carrier {
            for right in &carrier {
                let square = UnionSquare::new(left, right).expect("square");
                for lmap in &carrier {
                    for rmap in &carrier {
                        let compatible = (0 .. size).all(|point| {
                            square.blocks()[point] != Block::Both
                                || lmap.decisions()[point] == rmap.decisions()[point]
                        });
                        let extensions: Vec<&Subshape> = carrier
                            .iter()
                            .filter(|candidate| {
                                (0 .. size).all(|point| {
                                    (left.decisions()[point] == Membership::Outside
                                        || candidate.decisions()[point] == lmap.decisions()[point])
                                        && (right.decisions()[point] == Membership::Outside
                                            || candidate.decisions()[point]
                                                == rmap.decisions()[point])
                                })
                            })
                            .collect();
                        assert_eq!(!extensions.is_empty(), compatible);
                        if let Some(first) = extensions.first() {
                            for candidate in &extensions {
                                for (point, block) in square.blocks().iter().enumerate() {
                                    if *block != Block::Neither {
                                        assert_eq!(
                                            candidate.decisions()[point],
                                            first.decisions()[point]
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn finite_boundaries_are_checked()
{
    let empty = Subshape::new(PointCount::from(0), &[]).expect("empty");
    assert_eq!(
        empty.contains(Point::from(0)),
        Err(ShapeError::PointOutside(Point::from(0)))
    );
    assert_eq!(
        Subshape::new(PointCount::from(1), &[Point::from(1)]),
        Err(ShapeError::PointOutside(Point::from(1)))
    );
    let one = Subshape::new(PointCount::from(1), &[Point::from(0), Point::from(0)])
        .expect("duplicate is membership");
    assert_eq!(one.contains(Point::from(0)), Ok(Membership::Inside));
    assert_eq!(
        one.complement().contains(Point::from(0)),
        Ok(Membership::Outside)
    );
    for operation in [SetOperation::Meet, SetOperation::Union] {
        assert_eq!(
            empty.combine(&one, operation),
            Err(ShapeError::DifferentAmbient)
        );
    }
    assert_eq!(
        Cofibration::new(empty.clone(), one.clone()),
        Err(ShapeError::DifferentAmbient)
    );
    assert_eq!(
        UnionSquare::new(&empty, &one),
        Err(ShapeError::DifferentAmbient)
    );
}
