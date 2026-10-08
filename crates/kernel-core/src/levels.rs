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

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::AdmissionOutcome;
use gandr_kernel_strata::Entailment;
use gandr_kernel_strata::LandmarkConstraint;
use gandr_kernel_strata::LandmarkPoset;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_term::LevelParamCount;

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
    /// - ensures: `Ok(context)` carrying an admitted poset exactly when every
    ///   constraint variable is strictly below `params` and the constraint set
    ///   has a model; the poset then decides this declaration's universe
    ///   comparisons and agrees with the free-fragment oracle when empty.
    /// - provides: the per-declaration level context. Admission remains
    ///   prose-only: constraints move into the oracle, and testing model
    ///   existence would repeat that oracle rather than validate its evidence.
    /// - fails: [`KernelError::LevelVariableOutOfScope`] for a constraint
    ///   variable at or above the parameter count;
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
    /// - hypothesis: L1/L2 — admission returns the oracle's own dichotomy as
    ///   evidence, so a mutant admitting a looping set must forge a consistency
    ///   witness; the L3 residues are the scope boundary and the empty context,
    ///   pinned by an at-count constraint variable and by the empty admission.
    /// - witness: `levels::tests::an_empty_context_admits`
    /// - witness: `levels::tests::looping_constraints_are_refused`
    /// - witness: `levels::tests::an_out_of_scope_constraint_variable_is_refused`
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
        let outcome = LandmarkPoset::admit(constraints).map_err(KernelError::LevelOracleFault)?;
        match outcome {
            | AdmissionOutcome::Admitted(poset) => Ok(Self { params, poset }),
            | AdmissionOutcome::Loop(witness) => {
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

    /// Check that every variable of `level` is within the prenex parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.is_ok() == level.atoms().all(|(variable, _offset)|
    ///   u32::from(variable.index()) < u32::from(self.params))` — success
    ///   exactly when every variable index is strictly below the parameter
    ///   count.
    /// - provides: the scope check for a level embedded in a type.
    /// - fails: [`KernelError::LevelVariableOutOfScope`] naming the first
    ///   out-of-scope variable in the level's canonical atom order.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::LevelVariableOutOfScope`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the boundary is `index < params`, separated by an
    ///   at-count variable (refused) and the variable one below it (accepted),
    ///   each asserted as the exact variant or as success.
    /// - witness: `levels::tests::the_level_scope_boundary_is_exact`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == level.atoms().all(|(variable, _offset)| u32::from(variable.index()) < u32::from(self.params)))]
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
    /// - provides: the universe rule and the strictness gate of an explicit
    ///   lift. The order postcondition remains prose-only: repeating the
    ///   oracle's decision would not validate its evidence.
    /// - fails: [`KernelError::UniverseViolation`] carrying the oracle's
    ///   refutation; [`KernelError::LevelOracleFault`] on an oracle fault the
    ///   theory excludes.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L2 — the decision returns oracle evidence either way,
    ///   so a mutant deciding wrongly must forge coherent evidence; the L3
    ///   residues are irreflexivity and the successor boundary, and the third
    ///   is the landmark path, which a declared hypothesis decides where the
    ///   free oracle refuses.
    /// - witness: `levels::tests::the_universe_rule_is_the_free_strict_order`
    /// - witness: `levels::tests::the_universe_rule_is_irreflexive`
    /// - witness: `levels::tests::a_landmark_hypothesis_decides_the_universe_rule`
    #[inline]
    #[spec(requires: lower.atoms().chain(upper.atoms()).all(|(variable, _offset)| u32::from(variable.index()) < u32::from(self.params)))]
    pub fn check_universe_below(
        &self,
        lower: &Level,
        upper: &Level,
    ) -> Result<(), KernelError>
    {
        if self.poset.constraints().is_empty() {
            return match lower.lt_with_evidence(upper) {
                | Ok(_witness) => Ok(()),
                | Err(refutation) => Err(universe_violation(
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
            | Entailment::Holds(_witness) => Ok(()),
            | Entailment::Refuted(countermodel) => Err(universe_violation(
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

/// The variables a landmark constraint mentions, across both sides.
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
        assert!(
            matches!(
                free.check_universe_below(&low, &high),
                Err(KernelError::UniverseViolation(_))
            ),
            "and without the hypothesis it is refused, so the hypothesis is load-bearing"
        );
    }

    #[test]
    fn looping_constraints_are_refused()
    {
        let variable = level_var(LevelVarIndex::from(0_u32));
        let constraint = LandmarkConstraint::leq(succ(&variable), variable)
            .expect("a variable-only constraint is well formed");
        let refused = LevelContext::admit(LevelParamCount::from(1_u32), vec![constraint]);
        assert!(
            matches!(refused, Err(KernelError::InconsistentLevelConstraints(_))),
            "a self-successor constraint has no model and is refused with its pumping witness"
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
}
