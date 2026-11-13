//! The per-declaration **level context**: the prenex parameters a declaration
//! binds and the landmark constraints it declares over them, admitted together.
//!
//! There is no global level state. A declaration's constraints are admitted
//! when it is, and the admitted poset decides that declaration's universe
//! judgements and nothing else — which is what makes the universe rule a
//! function of the declaration rather than of the environment's history.
//!
//! The rule itself is one call into the level oracle's strict order, and the
//! oracle answers with evidence in both directions. Trust concentrates in the
//! oracle's validators, so this module decides nothing about levels; it only
//! says which query to ask and refuses out-of-scope variables before asking.
//!
//! Admission asks the potential maintenance of `theory-dynamic-graphs` first.
//! When every constraint is a difference constraint, one variable with an
//! offset on each side, the maintenance proposes a model, and the poset
//! validates it before it admits. A model the validator refuses, a positive
//! cycle and a constraint outside that fragment go to the poset's
//! loop-checking, which returns the replayable evidence. The maintenance is
//! outside the trusted base: it proposes, and the poset's validator decides.
//!
//! # References
//!
//! - `Grodin-2026-potential_functions_types` — background: Eq. (1) bounds the
//!   true cost of a sequence of operations by a potential function and the
//!   amortised costs. The potential maintenance counts its raises and
//!   relaxations. Its potentials are a valuation of the constraints, and it
//!   states no potential function or amortised bound in this sense. Harrison
//!   Grodin, Ethan Chu, Runming Li, Jan Hoffmann and Robert Harper, "Potential
//!   Functions as Types", 2026, `arXiv:2607.08547`.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::AdmissionOutcome;
use gandr_kernel_strata::ConsistencyValue;
use gandr_kernel_strata::ConsistencyWitness;
use gandr_kernel_strata::ConstraintRelation;
use gandr_kernel_strata::Entailment;
use gandr_kernel_strata::LandmarkConstraint;
use gandr_kernel_strata::LandmarkPoset;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_term::LevelParamCount;
use gandr_theory_dynamic_graphs::ConstraintVerdict;
use gandr_theory_dynamic_graphs::Offset;
use gandr_theory_dynamic_graphs::PotentialMaintenance;
use gandr_theory_graphs::EdgeId;
use gandr_theory_graphs::NodeId;
use quenchant_shape::shape::Maybe;

use crate::error::KernelError;
use crate::error::LevelOrderRefutation;
use crate::error::UniverseViolation;

/// The admitted level context of one declaration.
#[derive(Clone, Debug)]
pub struct LevelContext
{
    /// The prenex level-parameter count.
    params: LevelParamCount,
    /// The admitted landmark poset, empty when no constraints are declared.
    poset: LandmarkPoset,
}

impl LevelContext
{
    /// Admit a declaration's prenex parameters and declared constraints.
    ///
    /// # Specification
    /// - requires: nothing — a constraint naming a variable outside the count
    ///   is admissible input and is refused here, since the kernel grants the
    ///   producer no credence about its own signature.
    /// - ensures: `Ok(context)` retains the parameter count and constraints
    ///   exactly when every constraint variable is strictly below `params` and
    ///   the constraints have a model; the poset then decides this
    ///   declaration's universe comparisons.
    /// - provides: the per-declaration context. The predicate checks scope,
    ///   retained counts and the returned model certificate. Loop witnesses are
    ///   replayed in tests that retain the consumed input constraints.
    /// - fails: [`KernelError::LevelVariableOutOfScope`] naming the first
    ///   out-of-scope variable in constraint order, left side before right;
    ///   [`KernelError::InconsistentLevelConstraints`] when the constraints
    ///   loop, carrying the replayable pumping witness;
    ///   [`KernelError::LevelOracleFault`] on an oracle fault the theory
    ///   excludes.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L1 validates returned consistency and looping evidence; L3
    ///   at the parameter boundary and on an out-of-scope constraint after a
    ///   loop distinguishes lost parameters, a false model, omitted scope
    ///   checks and changed refusal precedence. Empty and one-constraint
    ///   admitted contexts bound the positive cases.
    /// - witness: `levels::tests::an_empty_context_admits`
    /// - witness: `levels::tests::looping_constraints_are_refused`
    /// - witness: `levels::tests::an_out_of_scope_constraint_variable_is_refused`
    /// - witness: `levels::tests::admission_checks_scope_before_a_loop_and_keeps_input_order`
    #[spec(
        captures: [
            constraint_count = constraints.len(),
            first_out_of_scope = constraints.iter().flat_map(constraint_variables)
                .find(|variable| u32::from(variable.index()) >= u32::from(params)),
        ],
        ensures: |ret| match ret {
            Ok(ref context) => first_out_of_scope.is_none() && context.params == params
                && context.poset.constraints().len() == constraint_count
                && context.poset.constraints().iter().flat_map(constraint_variables)
                    .all(|variable| u32::from(variable.index()) < u32::from(params))
                && gandr_kernel_strata::validate_consistency(
                    context.poset.constraints(), context.poset.consistency()).is_ok(),
            Err(KernelError::LevelVariableOutOfScope { variable }) => first_out_of_scope == Some(variable),
            Err(KernelError::InconsistentLevelConstraints(_) | KernelError::LevelOracleFault(_)) =>
                first_out_of_scope.is_none(),
            Err(_) => false,
        }
    )]
    #[inline]
    pub fn admit(
        params: LevelParamCount,
        constraints: Vec<LandmarkConstraint>,
    ) -> Result<Self, KernelError>
    {
        for constraint in &constraints {
            for variable in constraint_variables(constraint) {
                check_scope(params, variable)?;
            }
        }
        let constraints = match proposed_model(&constraints) {
            Proposal::Model(model) => match LandmarkPoset::admit_modelled(constraints, model) {
                Ok(poset) => return Ok(Self { params, poset }),
                Err(refusal) => refusal.into_constraints(),
            },
            Proposal::Refuted | Proposal::Outside => constraints,
        };
        let outcome = LandmarkPoset::admit(constraints).map_err(KernelError::LevelOracleFault)?;
        match outcome {
            AdmissionOutcome::Admitted(poset) => Ok(Self { params, poset }),
            AdmissionOutcome::Loop(witness) => {
                Err(KernelError::InconsistentLevelConstraints(Box::new(witness)))
            },
        }
    }

    /// The prenex level-parameter count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn params(&self) -> LevelParamCount
    {
        self.params
    }

    /// The declared constraints that the poset was admitted from, in
    /// declaration order. With the parameter count, they are the whole context.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constraints(&self) -> &[gandr_kernel_strata::LandmarkConstraint]
    {
        self.poset.constraints()
    }

    /// Check that every variable of `level` is within the prenex parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: success exactly when every canonical atom is in scope;
    ///   otherwise the refusal names the first out-of-scope atom.
    /// - provides: the scope check for a level embedded in a type.
    /// - fails: [`KernelError::LevelVariableOutOfScope`] naming the first
    ///   out-of-scope variable in the level's canonical atom order.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::LevelVariableOutOfScope`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 at the last admitted and first refused indices, and on
    ///   a mixed canonical atom set with two refused variables; exact success
    ///   and refusal payloads distinguish strictness, omission and selecting a
    ///   later offender.
    /// - witness: `levels::tests::the_level_scope_boundary_is_exact`
    /// - witness: `levels::tests::level_scope_reports_the_first_out_of_scope_canonical_atom`
    #[inline]
    #[spec(ensures: |ret| match (&ret, level.atoms()
        .find(|&(variable, _offset)| u32::from(variable.index()) >= u32::from(self.params))) {
        (&Ok(()), None) => true,
        (&Err(KernelError::LevelVariableOutOfScope { variable }), Some((expected, _offset))) => variable == expected,
        _ => false,
    })]
    pub fn check_level_scope(
        &self,
        level: &Level,
    ) -> Result<(), KernelError>
    {
        for (variable, _offset) in level.atoms() {
            check_scope(self.params, variable)?;
        }
        Ok(())
    }

    /// Decide the strict universe order `lower < upper`.
    ///
    /// # Specification
    /// - requires: `lower.atoms().chain(upper.atoms()).all(|(variable,
    ///   _offset)| u32::from(variable.index()) < u32::from(self.params))` —
    ///   both levels are in scope, as established by
    ///   [`Self::check_level_scope`] at every embedding site.
    /// - ensures: `Ok(())` exactly when `lower < upper` holds — under the
    ///   free-fragment oracle when no constraints are declared and under
    ///   landmark entailment otherwise, the two agreeing on the empty poset.
    /// - provides: the universe rule and a lift's strictness gate. The
    ///   predicate checks refusal subjects, strictness and oracle family;
    ///   witnesses validate the returned refutations without repeating the
    ///   oracle's decision.
    /// - fails: [`KernelError::UniverseViolation`] carrying the oracle's
    ///   refutation; [`KernelError::LevelOracleFault`] on an oracle fault the
    ///   theory excludes.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L1 validates free and landmark refutations against their
    ///   original subjects; L3 at irreflexivity, a successor and a declared
    ///   ordering distinguishes a non-strict query, swapped subjects, wrong
    ///   oracle selection and a reversed decision on these cases.
    /// - witness: `levels::tests::the_universe_rule_is_the_free_strict_order`
    /// - witness: `levels::tests::the_universe_rule_is_irreflexive`
    /// - witness: `levels::tests::a_landmark_hypothesis_decides_the_universe_rule`
    /// - witness: `levels::tests::a_landmark_refusal_preserves_subjects_and_a_valid_countermodel`
    #[inline]
    #[spec(
        requires: lower.atoms().chain(upper.atoms()).all(|(variable, _offset)| u32::from(variable.index()) < u32::from(self.params)),
        ensures: |ret| match ret {
            Ok(()) => true,
            Err(KernelError::UniverseViolation(ref violation)) => violation.lower() == lower
                && violation.upper() == upper && match *violation.refutation() {
                    LevelOrderRefutation::Free(ref refutation) => self.poset.constraints().is_empty()
                        && refutation.strict() == gandr_kernel_strata::Strictness::STRICT,
                    LevelOrderRefutation::Landmark(ref countermodel) => !self.poset.constraints().is_empty()
                        && countermodel.strict() == gandr_kernel_strata::Strictness::STRICT,
                },
            Err(KernelError::LevelOracleFault(_)) => !self.poset.constraints().is_empty(),
            Err(_) => false,
        }
    )]
    pub fn check_universe_below(
        &self,
        lower: &Level,
        upper: &Level,
    ) -> Result<(), KernelError>
    {
        if self.poset.constraints().is_empty() {
            return match lower.lt_with_evidence(upper) {
                Ok(_witness) => Ok(()),
                Err(refutation) => Err(universe_violation(
                    lower,
                    upper,
                    LevelOrderRefutation::Free(refutation),
                )),
            };
        }
        let entailment = self
            .poset
            .entails_lt_with_evidence(lower, upper)
            .map_err(KernelError::LevelOracleFault)?;
        match entailment {
            Entailment::Holds(_witness) => Ok(()),
            Entailment::Refuted(countermodel) => Err(universe_violation(
                lower,
                upper,
                LevelOrderRefutation::Landmark(Box::new(countermodel)),
            )),
        }
    }
}

/// Build the refusal of a strict universe order.
///
/// # Specification
/// trivial.
#[inline]
fn universe_violation(
    lower: &Level,
    upper: &Level,
    refutation: LevelOrderRefutation,
) -> KernelError
{
    KernelError::UniverseViolation(Box::new(UniverseViolation::new(
        lower.clone(),
        upper.clone(),
        refutation,
    )))
}

/// What the potential maintenance makes of a constraint set.
#[derive(Debug)]
enum Proposal
{
    /// Every constraint is a difference constraint, and the maintenance
    /// admits each one: the model is its standing valuation.
    Model(ConsistencyWitness),
    /// The maintenance refutes a constraint by a positive cycle.
    Refuted,
    /// A constraint is outside the difference fragment, or a value is past
    /// the maintenance's range.
    Outside,
}

/// What one constraint does to the potential maintenance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Insertion
{
    /// It is a difference constraint, and the maintenance admits its edges.
    Admitted,
    /// It is a difference constraint, and the maintenance refutes an edge by
    /// a positive cycle.
    Refuted,
    /// It is not a difference constraint, or an offset is past the
    /// maintenance's range.
    Outside,
}

/// Insert the edges of a difference constraint into `maintenance`:
/// `x + k ≤ y + j` is the edge from `x` to `y` with offset `k − j`, a
/// maximum on the left gives one edge for each atom, and an equation of two
/// atoms gives an edge each way.
///
/// # Specification
/// trivial.
fn insert_difference(
    constraint: &LandmarkConstraint,
    maintenance: &mut PotentialMaintenance,
) -> Insertion
{
    let single = |level: &Level| {
        let mut atoms = level.atoms();
        match (
            atoms.next(),
            atoms.next(),
            level.constant_part() == LevelConstant::ZERO,
        ) {
            (Some(atom), None, true) => Some(atom),
            _ => None,
        }
    };
    let edge = |lower: LevelVar, upper: LevelVar| {
        EdgeId::new(
            NodeId::from(u32::from(lower.index())),
            NodeId::from(u32::from(upper.index())),
        )
    };
    let offset = |from: u64, to: u64| {
        i64::try_from(from)
            .ok()
            .zip(i64::try_from(to).ok())
            .and_then(|(from, to)| from.checked_sub(to))
            .map(Offset::from)
    };
    let mut insert = |edge: EdgeId, weight: Option<Offset>| {
        let Some(weight) = weight
        else {
            return Insertion::Outside;
        };
        match maintenance.insert_constraint(edge, weight) {
            Ok(ConstraintVerdict::Satisfied | ConstraintVerdict::SatisfiedAfterRaise) => {
                Insertion::Admitted
            },
            Ok(ConstraintVerdict::Refuted(_)) => Insertion::Refuted,
            Err(_) => Insertion::Outside,
        }
    };
    let Some((upper, upper_offset)) = single(constraint.right())
    else {
        return Insertion::Outside;
    };
    let upper_offset = u64::from(upper_offset);
    match constraint.relation() {
        ConstraintRelation::Leq => {
            if constraint.left().constant_part() != LevelConstant::ZERO {
                return Insertion::Outside;
            }
            for (lower, lower_offset) in constraint.left().atoms() {
                let inserted = insert(
                    edge(lower, upper),
                    offset(u64::from(lower_offset), upper_offset),
                );
                if inserted != Insertion::Admitted {
                    return inserted;
                }
            }
            Insertion::Admitted
        },
        ConstraintRelation::Eq => {
            let Some((lower, lower_offset)) = single(constraint.left())
            else {
                return Insertion::Outside;
            };
            let lower_offset = u64::from(lower_offset);
            match insert(edge(lower, upper), offset(lower_offset, upper_offset)) {
                Insertion::Admitted => {
                    insert(edge(upper, lower), offset(upper_offset, lower_offset))
                },
                other @ (Insertion::Refuted | Insertion::Outside) => other,
            }
        },
    }
}

/// The potential maintenance's proposal for `constraints`.
///
/// # Specification
/// - requires: nothing; the proposal is untrusted, and
///   [`LandmarkPoset::admit_modelled`] validates a model before it admits.
/// - ensures: [`Proposal::Model`] assigns every variable of the constraints its
///   standing value when every constraint is a difference constraint and the
///   maintenance admits each one; [`Proposal::Refuted`] when it refutes one;
///   [`Proposal::Outside`] otherwise.
/// - panics: none.
/// - intension: one insertion per edge, each incremental in the cone it raises;
///   no Horn saturation.
///
/// # Adequacy
/// - hypothesis: L2 — every set of up to three difference constraints over
///   three variables, each offset 0 or 1, gets the verdict the poset's
///   loop-checking gives.
/// - witness: `tests::levels::admission_agrees_with_loop_checking_on_difference_constraints`
#[spec(ensures: |ret| match ret {
    Proposal::Model(ref model) => constraints
        .iter()
        .flat_map(constraint_variables)
        .all(|variable| model.value_of(variable).is_some()),
    Proposal::Refuted | Proposal::Outside => true,
})]
fn proposed_model(constraints: &[LandmarkConstraint]) -> Proposal
{
    let mut maintenance = PotentialMaintenance::new();
    for constraint in constraints {
        match insert_difference(constraint, &mut maintenance) {
            Insertion::Admitted => {},
            Insertion::Refuted => return Proposal::Refuted,
            Insertion::Outside => return Proposal::Outside,
        }
    }
    let mut values = alloc::collections::BTreeMap::new();
    for variable in constraints.iter().flat_map(constraint_variables) {
        let Maybe::Present(potential) =
            maintenance.value(NodeId::from(u32::from(variable.index())))
        else {
            return Proposal::Outside;
        };
        let Ok(value) = u128::try_from(i64::from(potential))
        else {
            return Proposal::Outside;
        };
        let _previous = values.insert(variable, ConsistencyValue::from(value));
    }
    Proposal::Model(ConsistencyWitness::new(values))
}

/// The constraint's variables, left side before right, each in canonical order.
///
/// # Specification
/// trivial.
#[inline]
fn constraint_variables(constraint: &LandmarkConstraint) -> impl Iterator<Item = LevelVar> + '_
{
    let left = constraint
        .left()
        .atoms()
        .map(|(variable, _offset)| variable);
    let right = constraint
        .right()
        .atoms()
        .map(|(variable, _offset)| variable);
    left.chain(right)
}

/// Refuse a level variable at or above the prenex parameter count.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when the variable's index is strictly below
///   `params`, which is the scope boundary every level position in a
///   declaration is held to.
/// - provides: the one scope decision this module makes, so the boundary is
///   written once rather than at each embedding site.
/// - fails: `KernelError::LevelVariableOutOfScope` naming the offending
///   variable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 at the last admitted and first refused indices; exact
///   success and error payloads distinguish a changed guard or wrong variable.
/// - witness: `levels::tests::the_level_scope_boundary_is_exact`
/// - witness: `levels::tests::an_out_of_scope_constraint_variable_is_refused`
#[spec(ensures: |ret| ret == if u32::from(variable.index()) < u32::from(params) {
    Ok(())
} else {
    Err(KernelError::LevelVariableOutOfScope { variable })
})]
#[inline]
fn check_scope(
    params: LevelParamCount,
    variable: LevelVar,
) -> Result<(), KernelError>
{
    if u32::from(variable.index()) < u32::from(params) {
        Ok(())
    }
    else {
        Err(KernelError::LevelVariableOutOfScope { variable })
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_kernel_strata::LandmarkConstraint;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_strata::LevelVar;
    use gandr_kernel_strata::LevelVarIndex;
    use gandr_kernel_term::LevelParamCount;

    use super::LevelContext;
    use crate::error::KernelError;

    /// The level variable at `index`.
    ///
    /// # Specification
    /// trivial.
    fn var(index: LevelVarIndex) -> LevelVar
    {
        LevelVar::new(index)
    }

    /// The level of the variable at `index`.
    ///
    /// # Specification
    /// trivial.
    fn level_var(index: LevelVarIndex) -> Level
    {
        Level::var(var(index))
    }

    /// The constant level `value`.
    ///
    /// # Specification
    /// trivial.
    fn constant(value: LevelConstant) -> Level
    {
        Level::constant(value)
    }

    /// The successor of `level`.
    ///
    /// # Specification
    /// - requires: `level`'s successor is representable, which the fixture
    ///   levels here are small enough to guarantee.
    /// - ensures: the successor of `level`.
    /// - provides: the fixture levels the universe cases are built from.
    /// - fails: never.
    /// - panics: when the successor leaves the representable range, which no
    ///   fixture here reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on the constant-zero and variable-zero fixtures;
    ///   universe and landmark decisions distinguish omitted successors and
    ///   losing an atom or its canonical constant normalization.
    /// - witness: `levels::tests::the_universe_rule_is_the_free_strict_order`
    /// - witness: `levels::tests::a_landmark_hypothesis_decides_the_universe_rule`
    #[spec(requires: u64::from(level.constant_part()) < u64::MAX
        && level.atoms().all(|(_variable, offset)| u64::from(offset) < u64::MAX),
    ensures: |ret| {
        let constant = u64::from(level.constant_part());
        ret.atoms().map(|(variable, offset)| (variable, u64::from(offset)))
            .eq(level.atoms().map(|(variable, offset)| (variable, u64::from(offset).saturating_add(1))))
            && u64::from(ret.constant_part()) == if level.atoms()
                .any(|(_variable, offset)| u64::from(offset) >= constant) { 0 }
                else { constant.saturating_add(1) }
    })]
    fn succ(level: &Level) -> Level
    {
        level.succ().expect("the fixture levels are small")
    }

    /// A context over `params` parameters with no declared constraints.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a level context over `params` parameters with no declared
    ///   constraints, whose universe judgements are the free-fragment oracle's.
    /// - provides: the unconstrained context the landmark cases are contrasted
    ///   against.
    /// - fails: never.
    /// - panics: when admission refuses, which an empty constraint set never
    ///   does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero and two declared parameters; retained counts
    ///   and exact free-order decisions distinguish lost parameters or an
    ///   unintended constraint.
    /// - witness: `levels::tests::an_empty_context_admits`
    /// - witness: `levels::tests::the_universe_rule_is_the_free_strict_order`
    /// - witness: `levels::tests::the_level_scope_boundary_is_exact`
    #[spec(ensures: |ret| ret.params == params && ret.poset.constraints().is_empty())]
    fn empty_context(params: LevelParamCount) -> LevelContext
    {
        LevelContext::admit(params, Vec::new()).expect("an unconstrained context admits")
    }

    #[test]
    fn an_empty_context_admits()
    {
        let context = empty_context(LevelParamCount::from(2_u32));
        assert_eq!(
            LevelParamCount::from(2_u32),
            context.params(),
            "the parameter count is kept verbatim"
        );
    }

    #[test]
    fn the_universe_rule_is_the_free_strict_order()
    {
        let context = empty_context(LevelParamCount::from(0_u32));
        let zero = constant(LevelConstant::from(0));
        let one = succ(&zero);
        assert_eq!(
            Ok(()),
            context.check_universe_below(&zero, &one),
            "a universe inhabits the one above it"
        );
    }

    #[test]
    fn the_universe_rule_is_irreflexive()
    {
        let context = empty_context(LevelParamCount::from(0_u32));
        let zero = constant(LevelConstant::from(0));
        let refused = context.check_universe_below(&zero, &zero);
        assert!(
            matches!(refused, Err(KernelError::UniverseViolation(_))),
            "no universe inhabits itself: {refused:?}"
        );
    }

    #[test]
    fn a_landmark_hypothesis_decides_the_universe_rule()
    {
        let low = level_var(LevelVarIndex::from(0_u32));
        let high = level_var(LevelVarIndex::from(1_u32));
        let constraint = LandmarkConstraint::leq(succ(&low), high.clone())
            .expect("a variable-only constraint is well formed");
        let context = LevelContext::admit(LevelParamCount::from(2_u32), vec![constraint])
            .expect("a single ordering constraint has a model");
        assert_eq!(
            Ok(()),
            context.check_universe_below(&low, &high),
            "the declared hypothesis decides an order the free oracle refuses"
        );
        let free = empty_context(LevelParamCount::from(2_u32));
        let refused = free
            .check_universe_below(&low, &high)
            .expect_err("the free oracle does not entail the declared ordering");
        let KernelError::UniverseViolation(violation) = refused
        else {
            panic!("expected a universe refusal");
        };
        assert_eq!(violation.lower(), &low);
        assert_eq!(violation.upper(), &high);
        let crate::error::LevelOrderRefutation::Free(ref refutation) = *violation.refutation()
        else {
            panic!("expected a free-fragment refutation");
        };
        assert_eq!(refutation.strict(), gandr_kernel_strata::Strictness::STRICT);
        assert_eq!(
            gandr_kernel_strata::validate_refutation(&low, &high, refutation),
            Ok(())
        );
    }

    #[test]
    fn looping_constraints_are_refused()
    {
        let variable = level_var(LevelVarIndex::from(0_u32));
        let constraint = LandmarkConstraint::leq(succ(&variable), variable)
            .expect("a variable-only constraint is well formed");
        let constraints = vec![constraint];
        let refused = LevelContext::admit(LevelParamCount::from(1_u32), constraints.clone());
        let Err(KernelError::InconsistentLevelConstraints(witness)) = refused
        else {
            panic!("expected a replayable looping refusal");
        };
        assert_eq!(
            gandr_kernel_strata::validate_loop_witness(&constraints, &witness),
            Ok(())
        );
    }

    #[test]
    fn an_out_of_scope_constraint_variable_is_refused()
    {
        let constraint = LandmarkConstraint::leq(
            level_var(LevelVarIndex::from(0_u32)),
            level_var(LevelVarIndex::from(1_u32)),
        )
        .expect("a variable-only constraint is well formed");
        let refused = LevelContext::admit(LevelParamCount::from(1_u32), vec![constraint])
            .expect_err("an out-of-scope constraint variable is refused");
        assert_eq!(
            KernelError::LevelVariableOutOfScope {
                variable: var(LevelVarIndex::from(1_u32))
            },
            refused,
            "a constraint may not mention a variable the declaration does not bind"
        );
    }

    #[test]
    fn the_level_scope_boundary_is_exact()
    {
        let context = empty_context(LevelParamCount::from(2_u32));
        assert_eq!(
            Ok(()),
            context.check_level_scope(&level_var(LevelVarIndex::from(1_u32))),
            "the last bound parameter is in scope"
        );
        assert_eq!(
            Err(KernelError::LevelVariableOutOfScope {
                variable: var(LevelVarIndex::from(2_u32))
            }),
            context.check_level_scope(&level_var(LevelVarIndex::from(2_u32))),
            "and the one past it is not"
        );
    }

    #[test]
    fn admission_checks_scope_before_a_loop_and_keeps_input_order()
    {
        let zero = level_var(LevelVarIndex::from(0_u32));
        let looping = LandmarkConstraint::leq(succ(&zero), zero)
            .expect("a variable-only constraint is well formed");
        let first = var(LevelVarIndex::from(3_u32));
        let second = var(LevelVarIndex::from(2_u32));
        let out_of_scope = LandmarkConstraint::leq(Level::var(first), Level::var(second))
            .expect("a variable-only constraint is well formed");
        let refused =
            LevelContext::admit(LevelParamCount::from(1_u32), vec![looping, out_of_scope])
                .expect_err("scope is checked before the oracle runs");
        assert_eq!(refused, KernelError::LevelVariableOutOfScope {
            variable: first
        });
    }

    #[test]
    fn level_scope_reports_the_first_out_of_scope_canonical_atom()
    {
        let context = empty_context(LevelParamCount::from(2_u32));
        let level = level_var(LevelVarIndex::from(3_u32))
            .max(&level_var(LevelVarIndex::from(1_u32)))
            .max(&level_var(LevelVarIndex::from(2_u32)));
        assert_eq!(
            context.check_level_scope(&level),
            Err(KernelError::LevelVariableOutOfScope {
                variable: var(LevelVarIndex::from(2_u32)),
            })
        );
    }

    #[test]
    fn a_landmark_refusal_preserves_subjects_and_a_valid_countermodel()
    {
        let low = level_var(LevelVarIndex::from(0_u32));
        let high = level_var(LevelVarIndex::from(1_u32));
        let constraint = LandmarkConstraint::leq(low.clone(), high.clone())
            .expect("a variable-only constraint is well formed");
        let context = LevelContext::admit(LevelParamCount::from(2_u32), vec![constraint])
            .expect("a non-strict ordering has a model");
        let refused = context
            .check_universe_below(&high, &low)
            .expect_err("the reverse strict order is not entailed");
        let KernelError::UniverseViolation(violation) = refused
        else {
            panic!("expected a universe refusal");
        };
        assert_eq!(violation.lower(), &high);
        assert_eq!(violation.upper(), &low);
        let crate::error::LevelOrderRefutation::Landmark(ref countermodel) =
            *violation.refutation()
        else {
            panic!("expected a landmark countermodel");
        };
        assert_eq!(
            countermodel.strict(),
            gandr_kernel_strata::Strictness::STRICT
        );
        assert_eq!(
            gandr_kernel_strata::validate_entailment_countermodel(
                &context.poset,
                &high,
                &low,
                countermodel,
            ),
            Ok(())
        );
    }
}
