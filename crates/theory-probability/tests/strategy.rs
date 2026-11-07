//! The generated inputs the areas share: distributions over small supports
//! with small positive masses, and kernels as tables.

use gandr_theory_probability::Distribution;
use proptest::prelude::*;

/// A point of a generated support: a small whole number.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Point(pub u8);

/// The shape of a generated distribution: its points lie below `points`,
/// and it lists at most `listed` of them.
#[derive(Clone, Copy, Debug)]
pub struct Shape
{
    /// The bound of the points.
    pub points: u8,
    /// The most points a distribution lists before their merge.
    pub listed: usize,
}

/// A point below the bound of `shape`.
///
/// # Specification
/// trivial.
pub fn point(shape: Shape) -> impl Strategy<Value = Point>
{
    return (0 .. shape.points).prop_map(Point);
}

/// A distribution of `shape`, a point listed twice at the sum of its
/// masses. Each point weighs its mass, a whole number from one to eight,
/// over the sum of the masses.
///
/// # Specification
/// trivial.
pub fn distribution(shape: Shape) -> impl Strategy<Value = Distribution<Point>>
{
    return prop::collection::vec((point(shape), 1_u8 ..= 8), 1 ..= shape.listed).prop_map(
        |masses| {
            let total: i128 = masses.iter().map(|&(_, mass)| i128::from(mass)).sum();
            return Distribution::new(
                masses
                    .into_iter()
                    .map(|(at, mass)| (at, rational!(i128::from(mass), total))),
            )
            .expect("masses over their sum are a distribution");
        },
    );
}

/// A kernel as a table: one distribution of `shape` for each point below
/// its bound.
///
/// # Specification
/// trivial.
pub fn kernel(shape: Shape) -> impl Strategy<Value = Vec<Distribution<Point>>>
{
    return prop::collection::vec(distribution(shape), usize::from(shape.points));
}

/// The distribution that `table` gives `at`.
///
/// # Specification
/// trivial.
pub fn apply(
    table: &[Distribution<Point>],
    at: Point,
) -> Distribution<Point>
{
    return table
        .get(usize::from(at.0))
        .cloned()
        .expect("the table covers each point");
}
