//! The finite Giry monad: the sum of two fair coins by hand, and the three
//! monad laws with the pushforward as a Kleisli extension, on generated
//! distributions and kernels.

use gandr_theory_probability::Distribution;
use proptest::prelude::*;

use crate::strategy::Point;
use crate::strategy::Shape;
use crate::strategy::apply;
use crate::strategy::distribution;
use crate::strategy::kernel;
use crate::strategy::point;

/// Eight points, at most six listed.
const EIGHT: Shape = Shape {
    points: 8,
    listed: 6,
};

/// Two fair coins, each zero or one, sum to zero, one and two with the
/// weights one quarter, one half and one quarter.
#[test]
fn two_fair_coins_sum_to_a_quarter_a_half_and_a_quarter()
{
    let coin = Distribution::uniform([0_u8, 1]).unwrap();
    let sum = coin
        .bind(|&first| coin.map(|&second| first.checked_add(second).unwrap()))
        .unwrap();
    assert_eq!(sum.points(), [
        (0, rational!(1, 4)),
        (1, rational!(1, 2)),
        (2, rational!(1, 4))
    ]);
}

proptest! {
    /// A point is an identity of `bind` on both sides: a point bound to a
    /// kernel is the kernel's distribution there, and a distribution bound
    /// to `point` is itself.
    #[test]
    fn point_is_an_identity_of_bind(value in point(EIGHT), table in kernel(EIGHT), given in distribution(EIGHT)) {
        prop_assert_eq!(Distribution::point(value).bind(|&at| Ok(apply(&table, at)))?, apply(&table, value));
        prop_assert_eq!(given.bind(|&at| Ok(Distribution::point(at)))?, given);
    }

    /// Binding two kernels in turn is binding their Kleisli composite.
    #[test]
    fn bind_is_associative(given in distribution(EIGHT), first in kernel(EIGHT), second in kernel(EIGHT)) {
        let in_turn = given
            .bind(|&at| Ok(apply(&first, at)))?
            .bind(|&at| Ok(apply(&second, at)))?;
        let composite = given.bind(|&at| apply(&first, at).bind(|&next| Ok(apply(&second, next))))?;
        prop_assert_eq!(in_turn, composite);
    }

    /// The pushforward along a map that merges points is the Kleisli
    /// extension of a point after the map.
    #[test]
    fn map_is_bind_after_a_point(given in distribution(Shape { points: 16, listed: 8 })) {
        let image = |at: &Point| Point(at.0.min(5));
        prop_assert_eq!(given.map(image)?, given.bind(|at| Ok(Distribution::point(image(at))))?);
    }
}
