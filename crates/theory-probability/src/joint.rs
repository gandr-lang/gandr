//! A joint distribution over pairs: the marginal of each component, and the
//! decision whether the joint is the product of its marginals.
//!
//! Independence is the probabilistic form of the separation of supports that
//! the nominal site states. Two components are independent when the weight
//! of each pair is the product of the weights of its components.

use anodized::spec;
use gandr_theory_cellular_sheaves::Rational;

use crate::distribution::Distribution;
use crate::error::ProbabilityError;
use crate::error::exact;

/// The verdict on a joint distribution: independent, or the first pair where
/// the joint and the product of the marginals differ.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Independence<First, Second>
{
    /// The joint is the product of its marginals.
    Independent,
    /// The first pair, in ascending order, whose joint weight is not the
    /// product of the marginal weights of its components.
    Dependent
    {
        /// The pair.
        at: (First, Second),
        /// Its weight in the joint, zero when it lies outside the support.
        joint: Rational,
        /// The product of the marginal weights of its two components.
        product: Rational,
    },
}

impl<First, Second> Distribution<(First, Second)>
where
    First: Ord + Clone,
    Second: Ord + Clone,
{
    /// The marginal of the first component: the pushforward along the first
    /// projection, each first component at the sum of the weights of the
    /// pairs that hold it.
    ///
    /// The pairs ascend by their first component, so the adaptive sort of the
    /// canonical form finds one run, and the merge is linear.
    ///
    /// # Specification
    /// - ensures: the canonical form of the first components, each at its
    ///   summed weight.
    /// - fails: a sum past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::Overflow`]: a sum passes the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the first marginal of a product is its first factor,
    ///   so a sum that skips a pair breaks it.
    /// - witness: `tests::joint::each_marginal_of_a_product_is_its_factor`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points().iter().zip(made.points().iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn first_marginal(&self) -> Result<Distribution<First>, ProbabilityError>
    {
        self.map(|&(ref first, _)| first.clone())
    }

    /// The marginal of the second component: the pushforward along the
    /// second projection.
    ///
    /// # Specification
    /// - ensures: the canonical form of the second components, each at its
    ///   summed weight.
    /// - fails: a sum past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::Overflow`]: a sum passes the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the second marginal of a product is its second
    ///   factor.
    /// - witness: `tests::joint::each_marginal_of_a_product_is_its_factor`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points().iter().zip(made.points().iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn second_marginal(&self) -> Result<Distribution<Second>, ProbabilityError>
    {
        self.map(|&(_, ref second)| second.clone())
    }

    /// Whether the joint is the product of its marginals, and if it is not,
    /// the first pair where the two differ.
    ///
    /// The walk visits each pair of the two marginals' supports in ascending
    /// order and reads the joint's points in the same order, so it compares
    /// `m · n` weights for marginals of `m` and `n` points.
    ///
    /// # Specification
    /// - ensures: [`Independence::Independent`] exactly when each pair of the
    ///   marginals' supports weighs the product of its marginal weights;
    ///   otherwise the least such pair that does not.
    /// - fails: a sum or a product past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::Overflow`]: a sum or a product passes the 128-bit
    ///   integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every product is independent, and a correlated pair
    ///   names the first pair whose weight differs from the product.
    /// - witness: `tests::joint::a_product_is_independent_and_a_correlation_names_its_first_pair`
    #[spec(ensures: |ref ret| match *ret {
        Ok(Independence::Dependent { joint, product, .. }) => joint != product,
        Ok(Independence::Independent) | Err(_) => true,
    })]
    #[inline]
    pub fn independent(&self) -> Result<Independence<First, Second>, ProbabilityError>
    {
        let firsts = self.first_marginal()?;
        let seconds = self.second_marginal()?;
        let mut joint = self.points().iter().peekable();
        for &(ref first, first_weight) in firsts.points() {
            for &(ref second, second_weight) in seconds.points() {
                let product = exact(first_weight.times(second_weight))?;
                let held = match joint.peek() {
                    Some(&&((ref left, ref right), weight)) if left == first && right == second => {
                        joint.next();
                        weight
                    },
                    Some(_) | None => Rational::ZERO,
                };
                if held != product {
                    return Ok(Independence::Dependent {
                        at: (first.clone(), second.clone()),
                        joint: held,
                        product,
                    });
                }
            }
        }
        Ok(Independence::Independent)
    }
}
