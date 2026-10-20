//! Small carriers read by bit mask: the subsets every suite enumerates, and
//! the independent reading they are checked against.

use gandr_theory_shapes::Membership;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::PointCount;
use gandr_theory_shapes::Subshape;

/// A subset of a carrier of at most a word's points, as a bit mask: the
/// reading the suites check [`Subshape`] against.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Mask(pub usize);

impl Mask
{
    /// The mask's decision at a point: inside when the point's bit is set.
    ///
    /// # Specification
    /// trivial.
    pub fn at(
        self,
        point: Point,
    ) -> Membership
    {
        let shift = u32::try_from(usize::from(point)).expect("a small point");
        if self.0.checked_shr(shift).unwrap_or(0) & 1 == 1 {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }
}

/// The points of a carrier, in order.
///
/// # Specification
/// trivial.
pub fn points(count: PointCount) -> impl Iterator<Item = Point>
{
    (0 .. usize::from(count)).map(Point::from)
}

/// Every subset of a carrier of at most four points, each with the mask that
/// names it, in mask order.
///
/// # Specification
/// trivial.
pub fn subsets(count: PointCount) -> Vec<(Mask, Subshape)>
{
    let width = u32::try_from(usize::from(count)).expect("a small carrier");
    let mut inside: Vec<Point> = Vec::new();
    (0 .. 1_usize.checked_shl(width).expect("a small carrier"))
        .map(|bits| {
            let mask = Mask(bits);
            inside.clear();
            inside.extend(points(count).filter(|point| mask.at(*point) == Membership::Inside));
            (
                mask,
                Subshape::new(count, &inside).expect("a subset of the carrier"),
            )
        })
        .collect()
}
