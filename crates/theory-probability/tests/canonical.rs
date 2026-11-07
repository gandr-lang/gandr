//! The canonical form: each order and each split of one list of weighted
//! points gives one distribution, the uniform distribution is over a set, and
//! every refusal by its name.

use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_probability::Distribution;
use gandr_theory_probability::ProbabilityError;
use proptest::prelude::*;

/// `2^64`, whose square passes the 128-bit integers.
const TWO_TO_THE_64: i128 = 0x0001_0000_0000_0000_0000;

proptest! {
    /// A list, the same list reversed with each point split into two halves
    /// of its weight, and the canonical form agree: the points ascend
    /// strictly, each weight is positive, and the weights sum to one.
    #[test]
    fn each_order_and_split_of_one_list_gives_one_form(masses in prop::collection::vec((0_u8 .. 12, 1_u8 ..= 8), 1 ..= 10)) {
        let total: i128 = masses.iter().map(|&(_, mass)| i128::from(mass)).sum();
        let listed = Distribution::new(masses.iter().map(|&(point, mass)| (point, rational!(i128::from(mass), total))))?;
        let halves = Distribution::new(masses.iter().rev().flat_map(|&(point, mass)| {
            let half = rational!(i128::from(mass), total.checked_mul(2).unwrap());
            return [(point, half), (point, half)];
        }))?;
        prop_assert_eq!(&listed, &halves);
        let points = listed.points();
        prop_assert!(points.iter().zip(points.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0));
        prop_assert!(points.iter().all(|&(_, weight)| i128::from(weight.numerator()) > 0));
        let sum = points.iter().try_fold(Rational::ZERO, |sum, &(_, weight)| sum.plus(weight)).unwrap();
        prop_assert_eq!(sum, Rational::ONE);
    }
}

/// The uniform distribution is over the set of its values: a value given
/// twice is one point, and no value is refused.
#[test]
fn uniform_is_over_the_set_of_its_values()
{
    let uniform = Distribution::uniform([3_u8, 1, 3, 2]).unwrap();
    assert_eq!(uniform.points(), [
        (1, rational!(1, 3)),
        (2, rational!(1, 3)),
        (3, rational!(1, 3))
    ]);
    assert_eq!(uniform.weight(&2), rational!(1, 3));
    assert_eq!(uniform.weight(&7), Rational::ZERO);
    assert_eq!(
        Distribution::<u8>::uniform([]),
        Err(ProbabilityError::Empty)
    );
}

/// A weight that is zero or negative, weights that do not sum to one, and a
/// product past the 128-bit integers are each refused by name.
#[test]
fn each_refusal_is_named()
{
    assert_eq!(
        Distribution::new([(0_u8, Rational::ONE), (1, Rational::ZERO)]),
        Err(ProbabilityError::NotPositive(Rational::ZERO))
    );
    assert_eq!(
        Distribution::new([(0_u8, rational!(3, 2)), (1, rational!(-1, 2))]),
        Err(ProbabilityError::NotPositive(rational!(-1, 2)))
    );
    assert_eq!(
        Distribution::new([(0_u8, rational!(1, 4)), (1, rational!(1, 4))]),
        Err(ProbabilityError::NotNormalised(rational!(1, 2)))
    );
    let fine = Distribution::new([
        (0_u8, rational!(1, TWO_TO_THE_64)),
        (
            1,
            rational!(TWO_TO_THE_64.checked_sub(1).unwrap(), TWO_TO_THE_64),
        ),
    ])
    .unwrap();
    assert_eq!(fine.product(&fine), Err(ProbabilityError::Overflow));
}
