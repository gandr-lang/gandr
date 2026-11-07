//! Conditioning: the posterior that `condition` gives is the one that Bayes'
//! rule computes by enumeration, and an event of weight zero is refused.

use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_probability::Distribution;
use gandr_theory_probability::ProbabilityError;
use proptest::prelude::*;

use crate::strategy::Shape;
use crate::strategy::apply;
use crate::strategy::distribution;
use crate::strategy::kernel;
use crate::strategy::point;

/// Four hypotheses or four kinds of evidence, at most four listed.
const FOUR: Shape = Shape {
    points: 4,
    listed: 4,
};

proptest! {
    /// For a prior over hypotheses and a likelihood of evidence under each,
    /// the joint conditioned on one evidence has, as its first marginal, the
    /// posterior of Bayes' rule: the prior times the likelihood, over the sum
    /// of that product across the hypotheses. Evidence that no hypothesis
    /// gives is refused.
    #[test]
    fn condition_is_bayes_rule_by_enumeration(prior in distribution(FOUR), likelihood in kernel(FOUR), evidence in point(FOUR)) {
        let joint = prior.bind(|&hypothesis| apply(&likelihood, hypothesis).map(|&seen| (hypothesis, seen)))?;
        let mut products = Vec::new();
        let mut marginal = Rational::ZERO;
        for &(hypothesis, weight) in prior.points() {
            let product = weight.times(apply(&likelihood, hypothesis).weight(&evidence)).unwrap();
            marginal = marginal.plus(product).unwrap();
            products.push((hypothesis, product));
        }
        let conditioned = joint.condition(|&(_, seen)| seen == evidence);
        if marginal == Rational::ZERO {
            prop_assert_eq!(conditioned, Err(ProbabilityError::NullEvent));
            return Ok(());
        }
        let posterior = conditioned?.first_marginal()?;
        for (hypothesis, product) in products {
            prop_assert_eq!(posterior.weight(&hypothesis), product.over(marginal).unwrap());
        }
    }
}

/// An event that holds at no point is refused, and one that holds at every
/// point gives the distribution back.
#[test]
fn an_event_of_weight_zero_is_refused()
{
    let die = Distribution::uniform(1_u8 ..= 6).unwrap();
    assert_eq!(
        die.condition(|&face| face > 6),
        Err(ProbabilityError::NullEvent)
    );
    assert_eq!(die.condition(|_| true).unwrap(), die);
    let even = die.condition(|&face| face.is_multiple_of(2)).unwrap();
    assert_eq!(even, Distribution::uniform([2_u8, 4, 6]).unwrap());
}
