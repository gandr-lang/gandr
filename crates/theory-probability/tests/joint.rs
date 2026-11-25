//! Joint distributions: each marginal of a product is its factor, a product
//! is independent, and a correlation names the first pair where the joint and
//! the product of its marginals differ.

use gandr_theory_probability::Distribution;
use gandr_theory_probability::Independence;
use proptest::prelude::*;

use crate::strategy::Shape;
use crate::strategy::distribution;

/// Eight points, at most six listed.
const EIGHT: Shape = Shape {
    points: 8,
    listed: 6,
};

proptest! {
    /// The first marginal of a product is its first factor, the second
    /// marginal its second.
    #[test]
    fn each_marginal_of_a_product_is_its_factor(first in distribution(EIGHT), second in distribution(EIGHT)) {
        let joint = first.product(&second)?;
        prop_assert_eq!(joint.first_marginal()?, first);
        prop_assert_eq!(joint.second_marginal()?, second);
    }

    /// Every product is independent.
    #[test]
    fn every_product_is_independent(first in distribution(EIGHT), second in distribution(EIGHT)) {
        prop_assert_eq!(first.product(&second)?.independent()?, Independence::Independent);
    }
}

/// Two coins that always agree differ from the product of their marginals at
/// the first pair, and a joint with a pair missing from its support differs
/// at that pair, with the joint weight zero.
#[test]
fn a_product_is_independent_and_a_correlation_names_its_first_pair()
{
    let agreeing =
        Distribution::new([((0_u8, 0_u8), rational!(1, 2)), ((1, 1), rational!(1, 2))]).unwrap();
    assert_eq!(agreeing.independent().unwrap(), Independence::Dependent {
        at: (0, 0),
        joint: rational!(1, 2),
        product: rational!(1, 4),
    });
    let missing = Distribution::new([
        ((0_u8, 0_u8), rational!(1, 4)),
        ((0, 2), rational!(1, 4)),
        ((1, 0), rational!(1, 4)),
        ((1, 1), rational!(1, 4)),
    ])
    .unwrap();
    assert_eq!(missing.independent().unwrap(), Independence::Dependent {
        at: (0, 1),
        joint: rational!(0, 1),
        product: rational!(1, 8),
    });
    let coin = Distribution::uniform([0_u8, 1]).unwrap();
    assert_eq!(
        coin.product(&coin).unwrap().independent().unwrap(),
        Independence::Independent
    );
}
