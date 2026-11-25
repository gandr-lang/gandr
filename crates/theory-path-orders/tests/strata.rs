//! The evidence of a termination function over rules of toy words, and the
//! replay of its three conditions.

use gandr_theory_path_orders::strata::Breach;
use gandr_theory_path_orders::strata::Condition;
use gandr_theory_path_orders::strata::Layer;
use gandr_theory_path_orders::strata::Measures;
use gandr_theory_path_orders::strata::RuleIndex;
use gandr_theory_path_orders::strata::Stratum;
use gandr_theory_path_orders::strata::Weighing;
use gandr_theory_path_orders::strata::check;

/// A rule of words: its left side and its right side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Rule(&'static str, &'static str);

/// `a → bb`: the count of `a` decreases, and the length increases.
const DOUBLE: Rule = Rule("a", "bb");

/// `b → ε`: the length decreases, and the count of `a` keeps its value.
const ERASE: Rule = Rule("b", "");

/// One measure of a word.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Measure
{
    /// The count of its letters.
    Length,
    /// The count of the letter `a`.
    CountOfA,
}

impl Measure
{
    /// The value of the measure at `word`.
    ///
    /// # Specification
    /// trivial.
    fn of(
        self,
        word: &str,
    ) -> usize
    {
        match self {
            Self::Length => word.len(),
            Self::CountOfA => word.matches('a').count(),
        }
    }
}

/// The measures of the strata, the lowest first.
#[derive(Clone, Copy, Debug)]
struct Listed(&'static [Measure]);

impl Measures for Listed
{
    type Rule = Rule;

    /// The measure of `stratum` at the left side against the right side.
    ///
    /// # Specification
    /// trivial.
    fn weigh(
        &self,
        stratum: Stratum,
        rule: &Rule,
    ) -> Weighing
    {
        let Some(&measure) = self.0.get(usize::from(stratum))
        else {
            return Weighing::Apart;
        };
        let (left, right) = (measure.of(rule.0), measure.of(rule.1));
        match left.cmp(&right) {
            core::cmp::Ordering::Greater => Weighing::Decreases,
            core::cmp::Ordering::Equal => Weighing::Keeps,
            core::cmp::Ordering::Less => Weighing::Increases,
        }
    }
}

/// The breach at `rule`, by `measure`, of `condition`.
///
/// # Specification
/// trivial.
fn breach(
    rule: usize,
    measure: usize,
    condition: Condition,
) -> Breach
{
    Breach {
        rule: RuleIndex::from(rule),
        measure: Stratum::from(measure),
        condition,
    }
}

/// The length below the count of `a` orients `a → bb` above `b → ε`. The
/// length alone does not orient `a → bb`, and the count of `a` alone does not
/// orient `b → ε`.
#[test]
fn two_measures_orient_two_rules_that_neither_orients_alone()
{
    let rules = [DOUBLE, ERASE];
    let strata = Stratum::from(2_usize);
    let measures = Listed(&[Measure::Length, Measure::CountOfA]);
    assert_eq!(
        check(
            &measures,
            &rules,
            &[
                Layer::In(Stratum::from(1_usize)),
                Layer::In(Stratum::from(0_usize))
            ],
            strata
        ),
        Ok(())
    );
    let one = Stratum::from(1_usize);
    let lowest = [Layer::In(Stratum::from(0_usize)); 2];
    assert_eq!(
        check(&Listed(&[Measure::Length]), &rules, &lowest, one),
        Err(breach(0, 0, Condition::Decreases))
    );
    assert_eq!(
        check(&Listed(&[Measure::CountOfA]), &rules, &lowest, one),
        Err(breach(1, 0, Condition::Decreases))
    );
}

/// The count of `a` below the length: `a → bb` in the lower stratum increases
/// the length, the measure of the stratum above it.
#[test]
fn the_two_strata_swapped_break_the_second_condition()
{
    assert_eq!(
        check(
            &Listed(&[Measure::CountOfA, Measure::Length]),
            &[DOUBLE, ERASE],
            &[
                Layer::In(Stratum::from(0_usize)),
                Layer::In(Stratum::from(1_usize))
            ],
            Stratum::from(2_usize)
        ),
        Err(breach(0, 1, Condition::DoesNotIncrease))
    );
}

/// The swap `ab ↔ ba` keeps the length and the count of `a`, so it is idle
/// beside the two rules. The rule `a → b` keeps the length and changes the
/// count of `a`, so it is not idle. A layer that names no measure, and a rule
/// with no layer, are refused.
#[test]
fn an_idle_rule_keeps_each_measure()
{
    let measures = Listed(&[Measure::Length, Measure::CountOfA]);
    let strata = Stratum::from(2_usize);
    let layered = [
        Layer::In(Stratum::from(1_usize)),
        Layer::In(Stratum::from(0_usize)),
        Layer::Idle,
    ];
    assert_eq!(
        check(
            &measures,
            &[DOUBLE, ERASE, Rule("ab", "ba")],
            &layered,
            strata
        ),
        Ok(())
    );
    assert_eq!(
        check(
            &measures,
            &[DOUBLE, ERASE, Rule("a", "b")],
            &layered,
            strata
        ),
        Err(breach(2, 1, Condition::Keeps))
    );
    assert_eq!(
        check(
            &measures,
            &[DOUBLE],
            &[Layer::In(Stratum::from(2_usize))],
            strata
        ),
        Err(breach(0, 2, Condition::InAStratum))
    );
    assert_eq!(
        check(
            &measures,
            &[DOUBLE, ERASE],
            &[Layer::In(Stratum::from(1_usize))],
            strata
        ),
        Err(breach(1, 0, Condition::Placed))
    );
}
