//! Related-input products and replayed higher evaluation at pure thunk codes.

use alloc::vec::Vec;

use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::Clause;
use super::Fibers;
use super::Identity;
use super::Mode;
use super::Proof;
use super::Relation;
use super::RelationError;
use super::RelationId;
use super::check_value;
use super::same_type;
use crate::encoding::ContentTable;
use crate::path_universe::Dialogue;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_value;

#[cfg(test)]
mod tests;

/// A zero-based position in kernel-generated constructor coverage.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Component(pub usize);

/// Which endpoint's evaluation failed to replay.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvaluationSide
{
    /// The source function.
    Left,
    /// The target function.
    Right,
}

/// An untrusted returned value and the engine trace that must justify it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evaluation
{
    /// The claimed returned value, scoped under the component's telescope.
    pub value: ValueId,
    /// Replay must certify `force function argument = return value`.
    pub dialogue: Dialogue,
}

/// One observation of the related-input product.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Pointwise
{
    /// Both returners compute and their returned values have related evidence.
    Return
    {
        /// Source evaluation, supplied by an untrusted producer.
        left: Evaluation,
        /// Target evaluation, supplied by an untrusted producer.
        right: Evaluation,
        /// An inhabitant of the output relation, not an equality verdict.
        proof: ValueId,
    },
    /// No returned values are supplied; retain both application computations.
    Suspended,
}

/// A higher-evaluation introduction over exhaustive related-input patterns.
///
/// # Specification
/// - provides: raw pointwise evidence in kernel coverage order. It carries no
///   verdict; every consumer replays all components.
/// - ensures: pattern coverage is generated from the argument relation, never
///   from producer-selected samples.
///
/// # Adequacy
/// - hypothesis: L1/L3 — omitted, extra, forged and false components refuse.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct HigherEvaluation(pub Vec<Pointwise>);

/// Two arguments with explicit evidence of their relation.
#[derive(Clone, Copy, Debug)]
pub struct RelatedArguments
{
    /// Source argument.
    pub left: ValueId,
    /// Target argument, not assumed to be the same syntax.
    pub right: ValueId,
    /// An inhabitant of their computed argument fibre.
    pub proof: ValueId,
}

/// One universally quantified constructor pattern of a first-order relation.
#[derive(Clone, Debug)]
pub struct RelatedPattern
{
    /// Distinct rigid Base leaves, ordered outermost first.
    pub context: Vec<ValueTypeId>,
    /// Shared constructor shape after elimination of the relation premise.
    pub value: ValueId,
    /// Evidence of the related pair at that pattern.
    pub proof: ValueId,
}

/// The application motive's result, including its explicit neutral case.
#[derive(Clone, Debug)]
pub enum Application
{
    /// Both pure returners compute to values in the output relation.
    Return
    {
        /// Source value.
        left: ValueId,
        /// Transported target value.
        right: ValueId,
        /// The checked output fibre in the enclosing relation mode.
        fiber: Fibers,
    },
    /// A variable or stuck application supplies no returner reduct yet.
    Suspended
    {
        /// Source force/application computation.
        left: ComputationId,
        /// Target force/application computation.
        right: ComputationId,
        /// Type of both eventual returned values.
        result: ValueTypeId,
        /// Identity or bridge reading of the eventual output relation.
        mode: Mode,
    },
}

/// Work remaining for symbolic constructor coverage.
#[repr(transparent)]
struct Allowance(u64);

impl Allowance
{
    /// Charge one coverage step or generated pattern.
    ///
    /// # Specification
    /// - ensures: consumes one unit, never wrapping the counter.
    /// - fails: Budget at zero.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Budget`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero work cannot certify a universal introduction.
    /// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
    fn charge(&mut self) -> Result<(), RelationError>
    {
        self.0 = self.0.checked_sub(1).ok_or(RelationError::Budget)?;
        Ok(())
    }
}

impl Relation
{
    /// Resolve the two premises of the function clause.
    ///
    /// # Specification
    /// - ensures: returns argument and result relation addresses.
    /// - fails: Classifier outside a function relation; Arena on bad addresses.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fibre keeps argument and returner boundaries.
    /// - witness: `identity_recursion::function::tests::function_clause_retains_related_inputs_and_neutrals`
    fn function(&self) -> Result<(RelationId, RelationId), RelationError>
    {
        let node = self.node(self.root)?;
        match node.clause {
            | Clause::Function(argument, result) => Ok((argument, result)),
            | _ => Err(RelationError::Classifier),
        }
    }

    /// Generate exhaustive related-input patterns for higher evaluation.
    ///
    /// # Specification
    /// - ensures: Unit has one pattern; Sum has matching injections only;
    ///   Product has all component combinations; discrete Base shares a fresh
    ///   rigid variable after eliminating its equality premise. No Base
    ///   inhabitants are sampled. Both modes use these same relation clauses.
    /// - provides: a universal introduction boundary for first-order arguments.
    ///   Function arguments retain their quantified fibre instead of being
    ///   sampled; their introduction remains suspended.
    /// - fails: `NeutralFiber` for a higher-order argument; Classifier outside
    ///   a function clause; Arena or Budget on invalid or excessive work.
    /// - panics: none.
    /// - intension: sums are left-first; products are lexicographic.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both Bool constructors and independent product Base
    ///   variables must be covered; higher-order inputs never become samples.
    /// - witness: `identity_recursion::function::tests::symbolic_coverage_keeps_base_variables_independent`
    #[inline]
    pub fn related_patterns(
        &self,
        arena: &mut TermArena,
        budget: ReplayBudget,
    ) -> Result<Vec<RelatedPattern>, RelationError>
    {
        let (argument, _) = self.function()?;
        let mut pending = Vec::from([(argument, false)]);
        let mut values = Vec::<Vec<RelatedPattern>>::new();
        let mut table = ContentTable::new();
        let mut allowance = Allowance(u64::from(budget));
        while let Some((relation, expanded)) = pending.pop() {
            allowance.charge()?;
            let node = self.node(relation)?;
            let patterns = match node.clause {
                | Clause::Unit => Vec::from([RelatedPattern {
                    context: Vec::new(),
                    value: arena.value_unit(),
                    proof: arena.value_unit(),
                }]),
                | Clause::Discrete => Vec::from([RelatedPattern {
                    context: Vec::from([node.source]),
                    value: arena.value_variable(DeBruijnIndex::from(0_u32)),
                    proof: arena.value_unit(),
                }]),
                | Clause::Sum(first, second) | Clause::Product(first, second) => {
                    if !expanded {
                        pending.push((relation, true));
                        pending.push((second, false));
                        pending.push((first, false));
                        continue;
                    }
                    let second = values.pop().ok_or(RelationError::Arena)?;
                    let first = values.pop().ok_or(RelationError::Arena)?;
                    let mut joined = Vec::new();
                    match node.clause {
                        | Clause::Sum(..) => {
                            joined.reserve(first.len().saturating_add(second.len()));
                            for (side, branch) in [(Side::Left, first), (Side::Right, second)] {
                                for mut pattern in branch {
                                    allowance.charge()?;
                                    pattern.value = arena.value_injection(side, pattern.value);
                                    joined.push(pattern);
                                }
                            }
                        },
                        | _ => {
                            for left in &first {
                                for right in &second {
                                    allowance.charge()?;
                                    let depth = u32::try_from(right.context.len())
                                        .map_err(|_error| RelationError::Budget)?;
                                    let value = shift_value(
                                        arena,
                                        &mut table,
                                        &mut NullMemo,
                                        left.value,
                                        BinderDepth::default(),
                                        BinderDepth::from(depth),
                                    );
                                    let proof = shift_value(
                                        arena,
                                        &mut table,
                                        &mut NullMemo,
                                        left.proof,
                                        BinderDepth::default(),
                                        BinderDepth::from(depth),
                                    );
                                    let mut context = Vec::with_capacity(
                                        left.context.len().saturating_add(right.context.len()),
                                    );
                                    context.extend_from_slice(&left.context);
                                    context.extend_from_slice(&right.context);
                                    joined.push(RelatedPattern {
                                        context,
                                        value: arena.value_pair(value, right.value),
                                        proof: arena.value_pair(proof, right.proof),
                                    });
                                }
                            }
                        },
                    }
                    joined
                },
                | Clause::Function(..) => return Err(RelationError::NeutralFiber),
                | Clause::Empty | Clause::CaseLeft(..) | Clause::CaseRight(..) => {
                    return Err(RelationError::Classifier);
                },
            };
            values.push(patterns);
        }
        values.pop().ok_or(RelationError::Arena)
    }

    /// Instantiate the related-input product and replay both pure returners.
    ///
    /// # Specification
    /// - ensures: checks functions, both arguments and their relation premise.
    ///   Return evidence checks both evaluation traces and the result-relation
    ///   inhabitant. Suspended evidence retains both computations without
    ///   making an equality or inequality claim.
    /// - fails: typing or fibre errors; Evaluation names a failed replay;
    ///   Pointwise names an invalid output proof; Classifier outside functions.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — unrelated arguments, wrong return values and
    ///   forged result evidence refuse independently in either mode.
    /// - witness: `identity_recursion::function::tests::function_clause_retains_related_inputs_and_neutrals`
    /// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
    #[inline]
    pub fn apply_related(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        functions: (ValueId, ValueId),
        arguments: RelatedArguments,
        evidence: &Pointwise,
        budget: ReplayBudget,
    ) -> Result<Application, RelationError>
    {
        let node = self.node(self.root)?;
        check_value(arena, context, functions.0, node.source)?;
        check_value(arena, context, functions.1, node.target)?;
        self.apply_component(
            arena,
            context,
            functions,
            arguments,
            evidence,
            (Component(0), budget),
        )
    }

    /// Check one component at a kernel-chosen coverage position.
    ///
    /// # Specification
    /// - requires: functions have been checked in context at this relation.
    /// - ensures: input evidence, both evaluations and output evidence check.
    /// - fails: premise typing errors, Evaluation or Pointwise with position.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`, including Arena and `NeutralFiber`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — swapping components cannot change the replay goal.
    /// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
    fn apply_component(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        functions: (ValueId, ValueId),
        arguments: RelatedArguments,
        evidence: &Pointwise,
        position: (Component, ReplayBudget),
    ) -> Result<Application, RelationError>
    {
        let (component, budget) = position;
        let (argument, result) = self.function()?;
        let premise = self.fiber_at(arena, argument, context, arguments.left, arguments.right)?;
        let premise = premise.native(arena)?;
        check_value(arena, context, arguments.proof, premise)?;
        let left = apply(arena, functions.0, arguments.left);
        let right = apply(arena, functions.1, arguments.right);
        let result_type = self.node(result)?;
        let result_type = result_type.source;
        let &Pointwise::Return {
            left: ref left_result,
            right: ref right_result,
            proof,
        } = evidence
        else {
            return Ok(Application::Suspended {
                left,
                right,
                result: result_type,
                mode: self.mode,
            });
        };
        for (side, computation, evaluation) in [
            (EvaluationSide::Left, left, left_result),
            (EvaluationSide::Right, right, right_result),
        ] {
            check_value(arena, context, evaluation.value, result_type)?;
            let mut returned = arena.computation_return(evaluation.value);
            let mut computation = computation;
            for _ in context {
                computation = arena.computation_lambda(computation);
                returned = arena.computation_lambda(returned);
            }
            let computation = arena.value_thunk(computation);
            let returned = arena.value_thunk(returned);
            let verdict = crate::replay::replay(
                arena,
                &Unfoldings::new(Vec::new()),
                ReplaySides::Values(computation, returned),
                EngineClaim::Convertible,
                evaluation.dialogue.0.iter().copied(),
                budget,
            );
            if verdict != KernelVerdict::Convertible {
                return Err(RelationError::Evaluation(component, side, verdict));
            }
        }
        let fiber = self.fiber_at(
            arena,
            result,
            context,
            left_result.value,
            right_result.value,
        )?;
        let ty = fiber.native(arena)?;
        if let Err(error) = check_value(arena, context, proof, ty) {
            return Err(match error {
                | RelationError::Typing(error) => RelationError::Pointwise(component, error),
                | error => error,
            });
        }
        Ok(Application::Return {
            left: left_result.value,
            right: right_result.value,
            fiber,
        })
    }

    /// Replay a universal higher-evaluation introduction in either mode.
    ///
    /// # Specification
    /// - ensures: closed functions check; every generated related-input pattern
    ///   has exactly one fully replayed component, in order. Closed function
    ///   roots have no free indices and are reused beneath pattern binders.
    /// - fails: Coverage on cardinality; `NeutralFiber` for suspended evidence;
    ///   all typing, coverage-budget and component-replay failures propagate.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — both Bool branches and generic Base variables are
    ///   universal obligations, never a producer-selected sample set.
    /// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
    /// - witness: `identity_recursion::function::tests::symbolic_coverage_keeps_base_variables_independent`
    #[inline]
    pub fn check_higher(
        &self,
        arena: &mut TermArena,
        functions: (ValueId, ValueId),
        evidence: &HigherEvaluation,
        budget: ReplayBudget,
    ) -> Result<(), RelationError>
    {
        let mark = arena.watermark();
        let checked = (|| {
            let node = self.node(self.root)?;
            check_value(arena, &[], functions.0, node.source)?;
            check_value(arena, &[], functions.1, node.target)?;
            let patterns = self.related_patterns(arena, budget)?;
            if patterns.len() != evidence.0.len() {
                return Err(RelationError::Coverage);
            }
            for (position, (pattern, pointwise)) in
                patterns.into_iter().zip(&evidence.0).enumerate()
            {
                let arguments = RelatedArguments {
                    left: pattern.value,
                    right: pattern.value,
                    proof: pattern.proof,
                };
                let applied = self.apply_component(
                    arena,
                    &pattern.context,
                    functions,
                    arguments,
                    pointwise,
                    (Component(position), budget),
                )?;
                if matches!(applied, Application::Suspended { .. }) {
                    return Err(RelationError::NeutralFiber);
                }
            }
            Ok(())
        })();
        arena.truncate_to(mark);
        checked
    }

    /// Introduce function identity by its computed related-input product.
    ///
    /// # Specification
    /// - ensures: both functions and every higher-evaluation component check.
    /// - provides: owned raw evidence, rechecked by each eliminator.
    /// - fails: `NonFibrant` in bridge mode; higher-evaluation failures
    ///   otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — double negation relates to identity, negation does
    ///   not, and a bridge cannot acquire identity transport.
    /// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
    #[inline]
    pub fn funext(
        &self,
        arena: &mut TermArena,
        left: ValueId,
        right: ValueId,
        evidence: HigherEvaluation,
        budget: ReplayBudget,
    ) -> Result<Identity, RelationError>
    {
        self.fibrant()?;
        self.check_higher(arena, (left, right), &evidence, budget)?;
        let domain = self.node(self.root)?;
        Ok(Identity {
            domain: domain.source,
            left,
            right,
            proof: Proof::HigherEvaluation(evidence),
        })
    }

    /// Replay lambda reflexivity as higher evaluation on related arguments.
    ///
    /// # Specification
    /// - ensures: applies the same function on both sides, replaying the
    ///   producer's evaluation evidence rather than postulating its action.
    /// - fails: the same typing, coverage and replay errors as funext.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — even reflexivity refuses forged evaluation
    ///   results.
    /// - witness: `identity_recursion::function::tests::lambda_reflexivity_replays_higher_evaluation`
    #[inline]
    pub fn function_reflexivity(
        &self,
        arena: &mut TermArena,
        value: ValueId,
        evidence: HigherEvaluation,
        budget: ReplayBudget,
    ) -> Result<Identity, RelationError>
    {
        self.funext(arena, value, value, evidence, budget)
    }

    /// Transport function identity through the representable application
    /// motive.
    ///
    /// # Specification
    /// - ensures: rechecks universal evidence, instantiates its input relation
    ///   at the argument diagonal, then computes both outputs and their fibre.
    ///   A missing returner reduct stays suspended. General native motives
    ///   retain the separate `Transport::Neutral` rule.
    /// - fails: Boundary for another relation; `NonFibrant` for bridges; input,
    ///   universal-evidence or pointwise-replay errors otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — application returns the target function's value;
    ///   neither forged traces nor changed identity boundaries are trusted.
    /// - witness: `identity_recursion::function::tests::application_transport_computes`
    #[inline]
    pub fn transport_application(
        &self,
        arena: &mut TermArena,
        identity: &Identity,
        argument: ValueId,
        evidence: &Pointwise,
        budget: ReplayBudget,
    ) -> Result<Application, RelationError>
    {
        self.fibrant()?;
        let domain = self.node(self.root)?;
        same_type(arena, domain.source, identity.domain)?;
        let Proof::HigherEvaluation(ref higher) = identity.proof
        else {
            return Err(RelationError::HigherEvaluationRequired);
        };
        self.check_higher(arena, (identity.left, identity.right), higher, budget)?;
        let (domain, _) = self.function()?;
        let fiber = self.fiber_at(arena, domain, &[], argument, argument)?;
        let proof = fiber.inhabitant(arena)?;
        let arguments = RelatedArguments {
            left: argument,
            right: argument,
            proof,
        };
        self.apply_component(
            arena,
            &[],
            (identity.left, identity.right),
            arguments,
            evidence,
            (Component(0), budget),
        )
    }
}

/// Cross the thunk seam and apply, leaving the pure returner unreduced.
///
/// # Specification
/// trivial.
fn apply(
    arena: &mut TermArena,
    function: ValueId,
    argument: ValueId,
) -> ComputationId
{
    let forced = arena.computation_force(function);
    arena.computation_application(forced, argument)
}
