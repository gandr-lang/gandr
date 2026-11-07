//! A finite distribution with exact weights, and the finite Giry monad on
//! it: a point, a uniform choice, the pushforward, the Kleisli extension, the
//! product of two distributions and the restriction to an event.
//!
//! The support is held in one canonical order, ascending by the order of the
//! points, each point once and with a positive weight. So two distributions
//! are equal in distribution when their forms are equal, and the derived
//! equality decides it.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cellular_sheaves::Integer;
use gandr_theory_cellular_sheaves::Rational;

use crate::error::ProbabilityError;
use crate::error::exact;

/// A finite distribution: each point of its support with an exact positive
/// weight, the weights summing to one.
///
/// # Specification
/// - ensures: the points ascend strictly, each weight is positive, and the
///   weights sum to one, so two equal distributions have equal forms.
/// - provides: the points with their weights, and the weight of any point.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the one that the
///   canonical form gives, which every constructor ends in.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Distribution<T>
{
    /// The points of the support in ascending order, each with its weight.
    points: Vec<(T, Rational)>,
}

impl<T> Distribution<T>
where
    T: Ord,
{
    /// The distribution with all its weight on `value`: the unit of the
    /// monad.
    ///
    /// # Specification
    /// - ensures: one point, `value`, with the weight one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a point is each side of the two identity laws, so a
    ///   weight other than one breaks both.
    /// - witness: `tests::monad::point_is_an_identity_of_bind`
    #[must_use]
    #[spec(ensures: |ref made| made.points.len() == 1 && made.points.first().is_some_and(|&(_, weight)| weight == Rational::ONE))]
    #[inline]
    pub fn point(value: T) -> Self
    {
        Self {
            points: vec![(value, Rational::ONE)],
        }
    }

    /// The uniform distribution over the set of `values`: each value once,
    /// whatever its count among `values`, with the weight one over the size
    /// of the set.
    ///
    /// # Specification
    /// - ensures: one point for each distinct value, each with the same weight.
    /// - fails: a set with no value, or one whose size passes the integers, is
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::Empty`]: `values` holds no value.
    /// - [`ProbabilityError::Overflow`]: the size of the set passes the 128-bit
    ///   integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two fair coins are each uniform, and their sum has
    ///   the weights one quarter, one half and one quarter.
    /// - witness: `tests::monad::two_fair_coins_sum_to_a_quarter_a_half_and_a_quarter`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points.iter().zip(made.points.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn uniform<Values>(values: Values) -> Result<Self, ProbabilityError>
    where
        Values: IntoIterator<Item = T>,
    {
        let mut points: Vec<(T, Rational)> = values
            .into_iter()
            .map(|value| (value, Rational::ZERO))
            .collect();
        points.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        points.dedup_by(|later, kept| later.0 == kept.0);
        if points.is_empty() {
            return Err(ProbabilityError::Empty);
        }
        let size = i128::try_from(points.len()).map_err(|_beyond| ProbabilityError::Overflow)?;
        let weight = exact(Rational::new(Integer::from(1_i128), Integer::from(size)))?;
        for point in &mut points {
            point.1 = weight;
        }
        points.shrink_to_fit();
        Ok(Self { points })
    }

    /// The distribution of weighted `points`: each point at the sum of the
    /// weights given for it.
    ///
    /// # Specification
    /// - requires: each weight is positive, and the weights sum to one.
    /// - ensures: the canonical form of the points, so two lists of one
    ///   distribution, in any order or with a point split, give one value.
    /// - fails: a weight that is not positive, weights that do not sum to one,
    ///   or a sum past the integers, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::NotPositive`]: a weight is zero or negative.
    /// - [`ProbabilityError::NotNormalised`]: the weights do not sum to one.
    /// - [`ProbabilityError::Overflow`]: a sum passes the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each order and each split of one list gives one form,
    ///   so a merge that keeps a point twice breaks equality.
    /// - witness: `tests::canonical::each_order_and_split_of_one_list_gives_one_form`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points.iter().zip(made.points.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn new<Points>(points: Points) -> Result<Self, ProbabilityError>
    where
        Points: IntoIterator<Item = (T, Rational)>,
    {
        let points: Vec<(T, Rational)> = points.into_iter().collect();
        if let Some(&(_, weight)) = points
            .iter()
            .find(|&&(_, weight)| i128::from(weight.numerator()) <= 0)
        {
            return Err(ProbabilityError::NotPositive(weight));
        }
        let points = canonical(points)?;
        let mut sum = Rational::ZERO;
        for &(_, weight) in &points {
            sum = exact(sum.plus(weight))?;
        }
        if sum != Rational::ONE {
            return Err(ProbabilityError::NotNormalised(sum));
        }
        Ok(Self { points })
    }

    /// The points of the support in ascending order, each with its positive
    /// weight.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn points(&self) -> &[(T, Rational)]
    {
        &self.points
    }

    /// The weight of `value`: its weight when it is a point of the support,
    /// and zero otherwise.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn weight(
        &self,
        value: &T,
    ) -> Rational
    {
        self.points
            .binary_search_by(|probe| probe.0.cmp(value))
            .ok()
            .and_then(|place| self.points.get(place))
            .map_or(Rational::ZERO, |&(_, weight)| weight)
    }

    /// The pushforward along `image`: each point of the result weighs the
    /// sum of the weights of the points that `image` sends to it.
    ///
    /// # Specification
    /// - ensures: the canonical form of the images, each at its summed weight.
    /// - fails: a sum past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::Overflow`]: a sum passes the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the pushforward is the Kleisli extension of a point
    ///   after `image`, so a merge that drops a weight breaks it.
    /// - witness: `tests::monad::map_is_bind_after_a_point`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points.iter().zip(made.points.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn map<Image, Map>(
        &self,
        mut image: Map,
    ) -> Result<Distribution<Image>, ProbabilityError>
    where
        Image: Ord,
        Map: FnMut(&T) -> Image,
    {
        let points = self
            .points
            .iter()
            .map(|&(ref value, weight)| (image(value), weight))
            .collect();
        Ok(Distribution {
            points: canonical(points)?,
        })
    }

    /// The Kleisli extension of `kernel`: each point of the result weighs
    /// the sum, over the points of this distribution, of its weight times
    /// the weight that `kernel` gives the result at it.
    ///
    /// # Specification
    /// - ensures: the canonical form of the weighted results.
    /// - fails: a refusal of `kernel`, or a product or a sum past the integers,
    ///   is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::Overflow`]: a product or a sum passes the 128-bit
    ///   integers.
    /// - Each refusal of `kernel`, as it gives it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the three monad laws hold of generated distributions
    ///   and kernels, so a lost or doubled weight breaks one.
    /// - witness: `tests::monad::bind_is_associative`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points.iter().zip(made.points.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn bind<Image, Kernel>(
        &self,
        mut kernel: Kernel,
    ) -> Result<Distribution<Image>, ProbabilityError>
    where
        Image: Ord,
        Kernel: FnMut(&T) -> Result<Distribution<Image>, ProbabilityError>,
    {
        let mut points = Vec::new();
        for &(ref value, weight) in &self.points {
            let result = kernel(value)?;
            points.reserve(result.points.len());
            for (image, inner) in result.points {
                points.push((image, exact(weight.times(inner))?));
            }
        }
        Ok(Distribution {
            points: canonical(points)?,
        })
    }

    /// The joint distribution of this distribution and `other`, taken as
    /// independent: each pair weighs the product of the weights of its two
    /// components.
    ///
    /// # Specification
    /// - ensures: one point for each pair of points, in ascending order of the
    ///   pairs, so the result needs no sort.
    /// - fails: a product past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::Overflow`]: a product passes the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each marginal of a product is its factor, so a wrong
    ///   weight or a missing pair breaks a marginal.
    /// - witness: `tests::joint::each_marginal_of_a_product_is_its_factor`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points.iter().zip(made.points.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn product<Other>(
        &self,
        other: &Distribution<Other>,
    ) -> Result<Distribution<(T, Other)>, ProbabilityError>
    where
        T: Clone,
        Other: Ord + Clone,
    {
        let mut points = Vec::with_capacity(self.points.len().saturating_mul(other.points.len()));
        for &(ref left, left_weight) in &self.points {
            for &(ref right, right_weight) in &other.points {
                let weight = exact(left_weight.times(right_weight))?;
                points.push(((left.clone(), right.clone()), weight));
            }
        }
        Ok(Distribution { points })
    }

    /// The distribution restricted to the points where `event` holds, each
    /// weight divided by the weight of the event.
    ///
    /// # Specification
    /// - requires: `event` holds at a point of the support.
    /// - ensures: the points where `event` holds, their weights summing to one.
    /// - fails: an event of weight zero, or a sum or a quotient past the
    ///   integers, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ProbabilityError::NullEvent`]: `event` holds at no point of the
    ///   support.
    /// - [`ProbabilityError::Overflow`]: a sum or a quotient passes the 128-bit
    ///   integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a posterior is the joint conditioned on the evidence,
    ///   which Bayes' rule computes by enumeration, so a weight not divided by
    ///   the event's breaks it.
    /// - witness: `tests::condition::condition_is_bayes_rule_by_enumeration`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.points.iter().zip(made.points.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
    #[inline]
    pub fn condition<Event>(
        &self,
        mut event: Event,
    ) -> Result<Self, ProbabilityError>
    where
        T: Clone,
        Event: FnMut(&T) -> bool,
    {
        let mut points = Vec::new();
        let mut total = Rational::ZERO;
        for &(ref value, weight) in &self.points {
            if event(value) {
                total = exact(total.plus(weight))?;
                points.push((value.clone(), weight));
            }
        }
        if points.is_empty() {
            return Err(ProbabilityError::NullEvent);
        }
        for point in &mut points {
            point.1 = exact(point.1.over(total))?;
        }
        points.shrink_to_fit();
        Ok(Self { points })
    }
}

/// The canonical form of weighted `points`: ascending by the order of the
/// points, each point once at the sum of its weights, and no spare capacity.
///
/// The sort is stable and adaptive, so `k` ascending runs, as the results of
/// a Kleisli extension are, merge in `O(n log k)` comparisons.
///
/// # Specification
/// - ensures: the points ascend strictly, and each weighs the sum of the
///   weights given for it.
/// - fails: a sum past the integers is refused.
/// - panics: none.
///
/// # Errors
/// - [`ProbabilityError::Overflow`]: a sum passes the 128-bit integers.
///
/// # Adequacy
/// - hypothesis: L2 — each order and each split of one list gives one form.
/// - witness: `tests::canonical::each_order_and_split_of_one_list_gives_one_form`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |made| made.iter().zip(made.iter().skip(1)).all(|(earlier, later)| earlier.0 < later.0)))]
pub fn canonical<T>(mut points: Vec<(T, Rational)>) -> Result<Vec<(T, Rational)>, ProbabilityError>
where
    T: Ord,
{
    points.sort_by(|left, right| left.0.cmp(&right.0));
    let mut fault = None;
    points.dedup_by(|later, kept| {
        if later.0 != kept.0 {
            return false;
        }
        match kept.1.plus(later.1) {
            Ok(sum) => kept.1 = sum,
            Err(_) => fault = Some(ProbabilityError::Overflow),
        }
        true
    });
    if let Some(refused) = fault {
        return Err(refused);
    }
    points.shrink_to_fit();
    Ok(points)
}
