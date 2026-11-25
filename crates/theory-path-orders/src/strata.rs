//! The evidence of a termination function: one measure for each stratum of a
//! system of rules.
//!
//! The rules of a system are in strata, the lowest first, and some rules are
//! idle: the equations that the rewriting is modulo, a symmetry for one. The
//! caller gives one measure for each stratum ([`Measures`]). A measure says how
//! the left side of a rule stands to its right side ([`Weighing`]). The
//! evidence is the stratum of each rule ([`Layer`]). [`check`] replays three
//! conditions:
//!
//! 1. the measure of the stratum of a rule decreases at the rule;
//! 2. the measure of each stratum above it does not increase at the rule;
//! 3. each measure keeps its value at an idle rule.
//!
//! A system with such measures terminates modulo its idle rules: a path has
//! finitely many steps of the highest stratum, then between two of them
//! finitely many of the next, and so on down. The measures together orient
//! more systems than each measure does alone, and each stratum can take a
//! different method of proof.
//!
//! # References
//!
//! - Stéphane Gaussent, Zuan Liu and Philippe Malbos. "Diagrammatic Bases from
//!   Stratified Normalization." `arXiv:2609.36020`, 2026 — the weighted
//!   function (3.1.2), the termination function (3.1.3), and termination modulo
//!   the equations (Theorem 3.1.5).

/// How a measure stands at a rule: its value at the left side of the rule
/// against its value at the right side.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Weighing
{
    /// The value at the left side is above the value at the right side.
    Decreases,
    /// The two values are equal.
    Keeps,
    /// The value at the left side is below the value at the right side.
    Increases,
    /// The measure does not compare the two sides.
    Apart,
}

/// A stratum, by its index from the lowest, which is 0; or a count of strata.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Stratum(usize);

impl From<usize> for Stratum
{
    /// The stratum at the index `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<Stratum> for usize
{
    /// The index of the stratum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(stratum: Stratum) -> Self
    {
        stratum.0
    }
}

/// A rule's index in the list of the rules of the system.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleIndex(usize);

impl From<usize> for RuleIndex
{
    /// The rule at the index `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<RuleIndex> for usize
{
    /// The index of the rule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rule: RuleIndex) -> Self
    {
        rule.0
    }
}

/// The place of one rule in the strata.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Layer
{
    /// An equation that the rewriting is modulo: it rewrites in no stratum.
    Idle,
    /// A rule of this stratum.
    In(Stratum),
}

/// One measure for each stratum, given by the caller.
///
/// # Specification
/// - requires: each measure maps the terms to a well-founded total preorder,
///   and is monotone in each context.
/// - ensures: how the measure of a stratum stands at a rule.
/// - panics: none.
/// - executable: none — a trait declaration; each implementation's witnesses
///   observe its measures.
pub trait Measures
{
    /// The rules of the system.
    type Rule;

    /// How the measure of `stratum` stands at `rule`.
    ///
    /// # Specification
    /// - requires: `stratum` is below the count of the measures.
    /// - ensures: the measure at the left side of `rule` against the measure at
    ///   its right side.
    /// - panics: none.
    /// - executable: none — a trait method; implementations state theirs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the length of a word and the count of one letter
    ///   orient two rules as two strata, which neither orients alone.
    /// - witness: `tests::strata::two_measures_orient_two_rules_that_neither_orients_alone`
    fn weigh(
        &self,
        stratum: Stratum,
        rule: &Self::Rule,
    ) -> Weighing;
}

/// The condition that a rule breaks.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Condition
{
    /// The measure of the stratum of the rule does not decrease at it.
    Decreases,
    /// The measure of a stratum above the stratum of the rule increases at it,
    /// or does not compare its sides.
    DoesNotIncrease,
    /// A measure changes at an idle rule, or does not compare its sides.
    Keeps,
    /// The stratum of the rule is not below the count of the measures.
    InAStratum,
    /// The rule has no layer, or a layer has no rule.
    Placed,
}

/// The first condition that the evidence breaks.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Breach
{
    /// The rule that breaks it.
    pub rule: RuleIndex,
    /// The measure that the condition reads.
    pub measure: Stratum,
    /// The condition.
    pub condition: Condition,
}

/// Whether `layers` replays as the evidence that `measures`, one for each of
/// `strata` strata, is a termination function of `rules`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: holds exactly when `layers` gives each rule one layer and, for
///   each rule in order: a rule in a stratum below `strata` decreases the
///   measure of its stratum, and does not increase or leave apart the measure
///   of each stratum above it; an idle rule keeps each measure.
/// - fails: at the first rule, in order, that breaks a condition, and at the
///   first measure, from the lowest, that the condition reads. A rule past the
///   end of `layers`, or a layer past the end of `rules`, is
///   [`Condition::Placed`] at that index.
/// - panics: none.
/// - executable: none — the replay is the predicate; restating it would replay
///   again.
/// - intension: one pass over the rules, each read by the measure of its
///   stratum and the measures above it.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the length of a word below the count of one letter
///   orients `a → bb` above `b → ε`, which neither measure orients alone, and
///   the two strata swapped break the second condition; a swap of two letters
///   is idle under both measures, and a rule that changes the count of a letter
///   is not. Reading only the measure of the stratum of each rule, or reading
///   the measures below it, changes one of them.
/// - witness: `tests::strata::two_measures_orient_two_rules_that_neither_orients_alone`
/// - witness: `tests::strata::the_two_strata_swapped_break_the_second_condition`
/// - witness: `tests::strata::an_idle_rule_keeps_each_measure`
///
/// # Cost
/// - allocation: none
#[inline]
pub fn check<M>(
    measures: &M,
    rules: &[M::Rule],
    layers: &[Layer],
    strata: Stratum,
) -> Result<(), Breach>
where
    M: Measures,
{
    for (index, (rule, layer)) in rules.iter().zip(layers).enumerate() {
        let breach = |measure: usize, condition: Condition| Breach {
            rule: RuleIndex(index),
            measure: Stratum(measure),
            condition,
        };
        match *layer {
            Layer::Idle => {
                if let Some(measure) = (0 .. strata.0)
                    .find(|&measure| measures.weigh(Stratum(measure), rule) != Weighing::Keeps)
                {
                    return Err(breach(measure, Condition::Keeps));
                }
            },
            Layer::In(Stratum(own)) => {
                if own >= strata.0 {
                    return Err(breach(own, Condition::InAStratum));
                }
                if measures.weigh(Stratum(own), rule) != Weighing::Decreases {
                    return Err(breach(own, Condition::Decreases));
                }
                if let Some(measure) = (own.saturating_add(1) .. strata.0).find(|&measure| {
                    !matches!(
                        measures.weigh(Stratum(measure), rule),
                        Weighing::Decreases | Weighing::Keeps
                    )
                }) {
                    return Err(breach(measure, Condition::DoesNotIncrease));
                }
            },
        }
    }
    if rules.len() == layers.len() {
        Ok(())
    }
    else {
        Err(Breach {
            rule: RuleIndex(rules.len().min(layers.len())),
            measure: Stratum::default(),
            condition: Condition::Placed,
        })
    }
}
