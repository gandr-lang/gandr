//! Related-input products and replayed higher and quantified evaluation at
//! pure thunk codes.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
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
use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::encoding::ContentTable;
use crate::path_universe::Dialogue;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_computation;
use crate::rewrite::shift_value;
use crate::rewrite::substitute_computation;

#[cfg(test)]
pub mod tests;

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
/// - ensures: pattern coverage is generated from the argument relation, never
///   from producer-selected samples.
/// - provides: raw pointwise evidence in kernel coverage order. It carries no
///   verdict; every consumer replays all components.
/// - panics: none.
/// - executable: none — this record holds no relation from which to generate
///   coverage; its consumers compare and replay the kernel-generated patterns.
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

/// One universally quantified pattern of a related-input product.
#[derive(Clone, Debug)]
pub struct RelatedPattern
{
    /// The pattern's binders, ordered outermost first: one rigid leaf per
    /// discrete Base coordinate, three per function coordinate.
    pub context: Vec<ValueTypeId>,
    /// The source argument after elimination of the relation premise.
    pub left: ValueId,
    /// The target argument: the source's own shape except at a function
    /// coordinate, whose two functions stay distinct.
    pub right: ValueId,
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
    #[spec(captures: before = self.0, ensures: |ret| match ret { Ok(()) => before.checked_sub(1) == Some(self.0), Err(RelationError::Budget) => before == 0 && self.0 == 0, Err(_) => false })]
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
    #[spec(ensures: |ret| match ret {
        Ok((argument, result)) => self.node(self.root).is_ok_and(|node| matches!(node.clause, Clause::Function(a, b) if a == argument && b == result)),
        Err(RelationError::Classifier) => self.node(self.root).is_ok_and(|node| !matches!(node.clause, Clause::Function(..))),
        Err(RelationError::Arena) => self.node(self.root).is_err(),
        Err(_) => false,
    })]
    fn function(&self) -> Result<(RelationId, RelationId), RelationError>
    {
        let node = self.node(self.root)?;
        match node.clause {
            Clause::Function(argument, result) => Ok((argument, result)),
            Clause::Unit
            | Clause::Empty
            | Clause::Discrete
            | Clause::Universe
            | Clause::Certificate
            | Clause::Relation
            | Clause::Atom { .. }
            | Clause::Product(..)
            | Clause::Sum(..)
            | Clause::List(_)
            | Clause::CaseLeft(..)
            | Clause::CaseRight(..) => Err(RelationError::Classifier),
        }
    }

    /// Generate exhaustive related-input patterns for higher evaluation.
    ///
    /// # Specification
    /// - ensures: the patterns [`Self::patterns_at`] generates at the function
    ///   clause's argument relation.
    /// - provides: a universal introduction boundary for first-order and
    ///   higher-order arguments, in either mode.
    /// - fails: Classifier outside a function clause; as [`Self::patterns_at`]
    ///   otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both Bool constructors and independent product Base
    ///   variables must be covered; a function argument binds both functions
    ///   and their identity, never a sample, in identity and bridge mode alike.
    /// - witness: `identity_recursion::function::tests::symbolic_coverage_keeps_base_variables_independent`
    /// - witness: `identity_recursion::function::tests::a_higher_order_argument_binds_its_inner_fibre`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |patterns| u64::from(budget) > 0 && !patterns.is_empty()))]
    #[inline]
    pub fn related_patterns(
        &self,
        arena: &mut TermArena,
        budget: ReplayBudget,
    ) -> Result<Vec<RelatedPattern>, RelationError>
    {
        let (argument, _) = self.function()?;
        self.patterns_at(arena, argument, budget)
    }

    /// Generate exhaustive related patterns of the relation at `relation`.
    ///
    /// # Specification
    /// - requires: `relation` addresses a node of this program.
    /// - ensures: Unit has one pattern; Sum has matching injections only;
    ///   Product has all component combinations; discrete Base shares a fresh
    ///   rigid variable after eliminating its equality premise; a function
    ///   coordinate at a thunk type `T` binds two functions and their relation,
    ///   `f₀ f₁ : T` and `p : Path(T, f₀, f₁)`, or `p : Bridge(T, f₀, f₁)` in
    ///   bridge mode, and relates `f₀` to `f₁` by `p`; in bridge mode a
    ///   universe coordinate at `U` binds two codes and a relation between
    ///   their elements, `X₀ X₁ : U` and `R : U(El X₀ → El X₁ → F U)`. No Base
    ///   inhabitants, functions or codes are sampled.
    /// - provides: the coverage both the argument of a higher evaluation and
    ///   the result of a function a quantified evaluation applies are split by.
    ///   A function or universe coordinate's premise is the fold's native fibre
    ///   at the two bound variables, so its relation stays the inner fibre
    ///   rather than a case split.
    /// - fails: Arena or Budget on invalid or excessive work; the named
    ///   requirement of a list coordinate, an identity universe coordinate or a
    ///   certificate coordinate.
    /// - intension: sums are left-first; products are lexicographic.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::related_patterns`], and the Bool result of
    ///   an applied function splits into its two constructors.
    /// - witness: `identity_recursion::function::tests::symbolic_coverage_keeps_base_variables_independent`
    /// - witness: `identity_recursion::function::tests::a_higher_order_argument_binds_its_inner_fibre`
    /// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "the refusal arms read the program's clauses, one per node of the relation the declaration compiled; the body walks the relation through the same table and every pattern it returns, which the success arm reads once"
        )
    )]
    #[spec(ensures: |ret| match ret {
        Ok(ref patterns) => u64::from(budget) > 0 && !patterns.is_empty() && patterns.iter().all(|pattern| pattern.context.iter().all(|&ty| matches!(arena.value_type(ty), Some(&gandr_kernel_term::ValueType::Base(_) | &gandr_kernel_term::ValueType::Thunk(_) | &gandr_kernel_term::ValueType::Path { .. } | &gandr_kernel_term::ValueType::Bridge { .. } | &gandr_kernel_term::ValueType::Universe { .. })))),
        Err(RelationError::RecursiveObservationRequired) => self.nodes.iter().any(|node| matches!(node.clause, Clause::List(_))),
        Err(RelationError::CertificateOperationRequired) => self.nodes.iter().any(|node| matches!(node.clause, Clause::Universe)),
        Err(RelationError::HigherFieldRequired) => self.nodes.iter().any(|node| matches!(node.clause, Clause::Certificate)),
        Err(_) => true,
    })]
    fn patterns_at(
        &self,
        arena: &mut TermArena,
        relation: RelationId,
        budget: ReplayBudget,
    ) -> Result<Vec<RelatedPattern>, RelationError>
    {
        let mut pending = Vec::from([(relation, false)]);
        let mut values = Vec::<Vec<RelatedPattern>>::new();
        let mut table = ContentTable::new();
        let mut allowance = Allowance(u64::from(budget));
        while let Some((relation, expanded)) = pending.pop() {
            allowance.charge()?;
            let node = self.node(relation)?;
            let patterns = match node.clause {
                Clause::Unit => {
                    let unit = arena.value_unit();
                    Vec::from([RelatedPattern {
                        context: Vec::new(),
                        left: unit,
                        right: unit,
                        proof: unit,
                    }])
                },
                Clause::Discrete => {
                    let leaf = arena.value_variable(DeBruijnIndex::from(0_u32));
                    Vec::from([RelatedPattern {
                        context: Vec::from([node.source]),
                        left: leaf,
                        right: leaf,
                        proof: arena.value_unit(),
                    }])
                },
                // A function, universe or atom coordinate binds its two
                // indices and the fold's own fibre between them, so the premise
                // is the identity or bridge the fold lowers that fibre to.
                Clause::Function(..) | Clause::Relation | Clause::Atom { .. } => {
                    let source = arena.value_variable(DeBruijnIndex::from(1_u32));
                    let target = arena.value_variable(DeBruijnIndex::from(0_u32));
                    let premise = self
                        .evaluate_at(arena, relation, source, target)?
                        .native(arena, super::Interfaces::NONE)?;
                    Vec::from([RelatedPattern {
                        context: Vec::from([node.source, node.source, premise]),
                        left: arena.value_variable(DeBruijnIndex::from(2_u32)),
                        right: source,
                        proof: target,
                    }])
                },
                Clause::Sum(first, second) | Clause::Product(first, second) => {
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
                        Clause::Sum(..) => {
                            joined.reserve(first.len().saturating_add(second.len()));
                            for (side, branch) in [(Side::Left, first), (Side::Right, second)] {
                                for mut pattern in branch {
                                    allowance.charge()?;
                                    let shared = pattern.left == pattern.right;
                                    pattern.left = arena.value_injection(side.into(), pattern.left);
                                    pattern.right = if shared {
                                        pattern.left
                                    }
                                    else {
                                        arena.value_injection(side.into(), pattern.right)
                                    };
                                    joined.push(pattern);
                                }
                            }
                        },
                        Clause::Unit
                        | Clause::Empty
                        | Clause::Discrete
                        | Clause::Universe
                        | Clause::Certificate
                        | Clause::Relation
                        | Clause::Atom { .. }
                        | Clause::Product(..)
                        | Clause::Function(..)
                        | Clause::List(_)
                        | Clause::CaseLeft(..)
                        | Clause::CaseRight(..) => {
                            for left in &first {
                                for right in &second {
                                    allowance.charge()?;
                                    let depth = u32::try_from(right.context.len())
                                        .map_err(|_error| RelationError::Budget)?;
                                    let mut shift = |value| {
                                        shift_value(
                                            arena,
                                            &mut table,
                                            &mut NullMemo,
                                            value,
                                            BinderDepth::default(),
                                            BinderDepth::from(depth),
                                        )
                                    };
                                    let source = shift(left.left);
                                    let target = if left.left == left.right {
                                        source
                                    }
                                    else {
                                        shift(left.right)
                                    };
                                    let proof = shift(left.proof);
                                    let mut context = Vec::with_capacity(
                                        left.context.len().saturating_add(right.context.len()),
                                    );
                                    context.extend_from_slice(&left.context);
                                    context.extend_from_slice(&right.context);
                                    let source_value = arena.value_tuple(&[source, right.left]);
                                    let target_value =
                                        if source == target && right.left == right.right {
                                            source_value
                                        }
                                        else {
                                            arena.value_tuple(&[target, right.right])
                                        };
                                    joined.push(RelatedPattern {
                                        context,
                                        left: source_value,
                                        right: target_value,
                                        proof: arena.value_tuple(&[proof, right.proof]),
                                    });
                                }
                            }
                        },
                    }
                    joined
                },
                Clause::List(_) => return Err(RelationError::RecursiveObservationRequired),
                Clause::Universe => return Err(RelationError::CertificateOperationRequired),
                Clause::Certificate => return Err(RelationError::HigherFieldRequired),
                Clause::Empty | Clause::CaseLeft(..) | Clause::CaseRight(..) => {
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
    #[spec(ensures: |ret| match ret {
        Ok(Application::Return { left, right, .. }) => match *evidence { Pointwise::Return { left: ref a, right: ref b, .. } => a.value == left && b.value == right, Pointwise::Suspended => false },
        Ok(Application::Suspended { mode, .. }) => mode == self.mode && matches!(evidence, &Pointwise::Suspended),
        Err(_) => true,
    })]
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
    #[spec(ensures: |ret| match ret {
        Err(RelationError::Evaluation(component, _, verdict)) => component == position.0 && verdict != KernelVerdict::Convertible,
        Err(RelationError::Pointwise(component, _)) => component == position.0,
        _ => match ret {
        Ok(Application::Return { left, right, .. }) => match *evidence { Pointwise::Return { left: ref a, right: ref b, .. } => a.value == left && b.value == right, Pointwise::Suspended => false },
        Ok(Application::Suspended { mode, .. }) => mode == self.mode && matches!(evidence, &Pointwise::Suspended),
        Err(_) => true,
    },
    })]
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
        let premise = premise.native(arena, super::Interfaces::NONE)?;
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
            let verdict = replay_evaluation(
                arena,
                context,
                computation,
                evaluation,
                (&Unfoldings::default(), budget),
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
        let ty = fiber.native(arena, super::Interfaces::NONE)?;
        if let Err(error) = check_value(arena, context, proof, ty) {
            return Err(match error {
                RelationError::Typing(error) => RelationError::Pointwise(component, error),
                error @ (RelationError::Arena
                | RelationError::UnsupportedCode(_)
                | RelationError::UnsupportedType(_)
                | RelationError::AbstractInterface(_)
                | RelationError::AtomTransport(_)
                | RelationError::Path(_)
                | RelationError::Boundary
                | RelationError::NonFibrant
                | RelationError::NeutralFiber
                | RelationError::Evidence
                | RelationError::Classifier
                | RelationError::HigherEvaluationRequired
                | RelationError::Coverage
                | RelationError::Pointwise(..)
                | RelationError::Evaluation(..)
                | RelationError::QuantifiedStep(_)
                | RelationError::HigherOrderDomain(_)
                | RelationError::RecursiveObservationRequired
                | RelationError::HigherFieldRequired
                | RelationError::CertificateOperationRequired
                | RelationError::Budget) => error,
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
    #[spec(
        captures: before = arena.watermark(),
        ensures: |ret| arena.watermark() == before && ret.as_ref().map_or(true, |&()| u64::from(budget) > 0 && evidence.0.iter().all(|pointwise| matches!(pointwise, &Pointwise::Return { .. }))),
    )]
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
                    left: pattern.left,
                    right: pattern.right,
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

    /// Read a higher evaluation as the checking obligations it owes, replaying
    /// every component's dialogues without a nested check.
    ///
    /// # Specification
    /// - requires: the functions are closed and the caller discharges every
    ///   returned obligation, in its component's telescope, before trusting the
    ///   evaluation; the replays here do not depend on those checks for
    ///   soundness, only for the typing of the values they certify. Every body
    ///   `unfoldings` holds is closed and was admitted before the evaluation.
    /// - ensures: one obligation per generated related-input pattern, in
    ///   coverage order. Each owes the pattern's premise evidence at the
    ///   argument fibre, both returned values at the result type, and the
    ///   output evidence at the result fibre of those values; both of its
    ///   dialogues replayed `force f v = return value` positively, unfolding
    ///   only what `unfoldings` defines.
    /// - provides: the checking machine's reading of a persisted higher
    ///   evaluation, sharing coverage and replay with [`Self::check_higher`].
    /// - fails: Coverage on cardinality; `NeutralFiber` for suspended evidence;
    ///   Evaluation with its component and side; fibre refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the persisted not-not and identity functions on
    ///   Bool relate through both branches; a wrong component refuses; a
    ///   composition naming admitted constants replays only with their bodies.
    /// - witness: `element_identity::tests::a_higher_evaluation_proves_function_extensionality`
    /// - witness: `element_identity::tests::a_higher_evaluation_unfolds_what_the_environment_admitted`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| owed.len() == evidence.0.len()))]
    pub(crate) fn evaluation_obligations(
        &self,
        arena: &mut TermArena,
        functions: (ValueId, ValueId),
        evidence: &HigherEvaluation,
        replay: (&Unfoldings, ReplayBudget),
    ) -> Result<Vec<ComponentObligation>, RelationError>
    {
        let (unfoldings, budget) = replay;
        let (argument, result) = self.function()?;
        let result_type = self.node(result)?.source;
        let patterns = self.related_patterns(arena, budget)?;
        if patterns.len() != evidence.0.len() {
            return Err(RelationError::Coverage);
        }
        let mut owed = Vec::new();
        for (position, (pattern, pointwise)) in patterns.into_iter().zip(&evidence.0).enumerate() {
            let &Pointwise::Return {
                left: ref left_result,
                right: ref right_result,
                proof,
            } = pointwise
            else {
                return Err(RelationError::NeutralFiber);
            };
            let premise = self
                .evaluate_at(arena, argument, pattern.left, pattern.right)?
                .native(arena, super::Interfaces::NONE)?;
            for (side, function, input, evaluation) in [
                (EvaluationSide::Left, functions.0, pattern.left, left_result),
                (
                    EvaluationSide::Right,
                    functions.1,
                    pattern.right,
                    right_result,
                ),
            ] {
                let computation = apply(arena, function, input);
                let verdict = replay_evaluation(
                    arena,
                    &pattern.context,
                    computation,
                    evaluation,
                    (unfoldings, budget),
                );
                if verdict != KernelVerdict::Convertible {
                    return Err(RelationError::Evaluation(
                        Component(position),
                        side,
                        verdict,
                    ));
                }
            }
            let output = self
                .evaluate_at(arena, result, left_result.value, right_result.value)?
                .native(arena, super::Interfaces::NONE)?;
            owed.push(ComponentObligation {
                context: pattern.context,
                checks: Vec::from([
                    (pattern.proof, premise),
                    (left_result.value, result_type),
                    (right_result.value, result_type),
                    (proof, output),
                ]),
            });
        }
        Ok(owed)
    }

    /// Read a quantified evaluation as the checking obligations it owes,
    /// replaying every step's dialogues without a nested check.
    ///
    /// # Specification
    /// - requires: as [`Self::evaluation_obligations`].
    /// - ensures: per generated related-input pattern, in coverage order, a
    ///   pre-order walk of one tree of steps. The walk starts at the pattern's
    ///   telescope with `force f₀ v₀` and `force f₁ v₁`. A return step owes, as
    ///   a higher-evaluation component does, both returned values at the result
    ///   type and the output evidence at their result fibre, after both of its
    ///   dialogues replayed the current computations as returning them. An
    ///   application step's dialogues replay each current computation, closed
    ///   under the telescope, as its closed normal form; each form is a thunk
    ///   of one lambda per telescope entry over `force f a` or `x ← force f a;
    ///   K`, whose head is the left or the right function the premise at the
    ///   step's fibre binds — that premise the persisted `Path(T, f₀, f₁)` a
    ///   function coordinate's coverage bound — at one input up to conversion,
    ///   owed at `T`'s argument type. The step then opens one branch per
    ///   pattern [`Self::patterns_at`] generates for `T`'s result relation,
    ///   extending the telescope by the pattern's binders and continuing each
    ///   side at its own output: `return o`, or `K` with `x` instantiated at
    ///   `o`. The pattern's premise evidence is owed first, at the argument
    ///   fibre, in the pattern's telescope.
    /// - provides: the checking machine's reading of a persisted quantified
    ///   evaluation. An application step is sound because `p` relates the two
    ///   functions at related inputs, and one input up to conversion is related
    ///   to itself; their outputs then fall in exactly one covering pattern of
    ///   the result relation, the branch whose continuations the tree proves.
    /// - fails: Coverage when steps are missing or left over; `QuantifiedStep`
    ///   with its component for a normal form that is not stuck at the
    ///   premise's functions at one input; `HigherOrderDomain` with its
    ///   component when the applied function's own domain binds a function;
    ///   Evaluation with its component and side; fibre refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// - reason: the `while let` loop drains a worklist, not recursion.
    /// - measure: the untrusted steps not yet read: each iteration reads one,
    ///   and a branch is pushed only by an application step.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — `λf. f(true)` relates to itself and to its bind
    ///   form through both output branches, a body applying its argument twice
    ///   nests its branches, differing inputs and a function whose domain is a
    ///   function refuse by name, and a step past the tree refuses as coverage.
    /// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
    /// - witness: `element_identity::tests::a_quantified_evaluation_refuses_what_it_cannot_relate`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| !owed.is_empty()))]
    pub(crate) fn quantified_obligations(
        &self,
        arena: &mut TermArena,
        functions: (ValueId, ValueId),
        steps: &[Quantified],
        replay: (&Unfoldings, ReplayBudget),
    ) -> Result<Vec<ComponentObligation>, RelationError>
    {
        let (unfoldings, budget) = replay;
        let (argument, result) = self.function()?;
        let result_type = self.node(result)?.source;
        let patterns = self.related_patterns(arena, budget)?;
        let mut table = ContentTable::new();
        let mut allowance = Allowance(u64::from(budget));
        let mut steps = steps.iter();
        let mut owed = Vec::new();
        for (position, pattern) in patterns.into_iter().enumerate() {
            let component = Component(position);
            let premise = self
                .evaluate_at(arena, argument, pattern.left, pattern.right)?
                .native(arena, super::Interfaces::NONE)?;
            let left = apply(arena, functions.0, pattern.left);
            let right = apply(arena, functions.1, pattern.right);
            owed.push(ComponentObligation {
                context: pattern.context.clone(),
                checks: Vec::from([(pattern.proof, premise)]),
            });
            let mut pending = Vec::from([Branch {
                context: pattern.context,
                left,
                right,
            }]);
            while let Some(branch) = pending.pop() {
                allowance.charge()?;
                let step = steps.next().ok_or(RelationError::Coverage)?;
                match *step {
                    Quantified::Return {
                        left: ref left_result,
                        right: ref right_result,
                        proof,
                    } => {
                        for (side, computation, evaluation) in [
                            (EvaluationSide::Left, branch.left, left_result),
                            (EvaluationSide::Right, branch.right, right_result),
                        ] {
                            let verdict = replay_evaluation(
                                arena,
                                &branch.context,
                                computation,
                                evaluation,
                                (unfoldings, budget),
                            );
                            if verdict != KernelVerdict::Convertible {
                                return Err(RelationError::Evaluation(component, side, verdict));
                            }
                        }
                        let output = self
                            .evaluate_at(arena, result, left_result.value, right_result.value)?
                            .native(arena, super::Interfaces::NONE)?;
                        owed.push(ComponentObligation {
                            context: branch.context,
                            checks: Vec::from([
                                (left_result.value, result_type),
                                (right_result.value, result_type),
                                (proof, output),
                            ]),
                        });
                    },
                    Quantified::Apply {
                        fibre,
                        left: ref left_reduction,
                        right: ref right_reduction,
                    } => {
                        for (side, computation, reduction) in [
                            (EvaluationSide::Left, branch.left, left_reduction),
                            (EvaluationSide::Right, branch.right, right_reduction),
                        ] {
                            let verdict = replay_claim(
                                arena,
                                &branch.context,
                                computation,
                                (reduction.normal, &reduction.dialogue),
                                (unfoldings, budget),
                            );
                            if verdict != KernelVerdict::Convertible {
                                return Err(RelationError::Evaluation(component, side, verdict));
                            }
                        }
                        let classifier = premise_classifier(
                            arena,
                            self.mode,
                            &branch.context,
                            fibre,
                            component,
                        )?;
                        let (inner_argument, inner_result) =
                            self.function_at(classifier, component)?;
                        if self.order(inner_argument)? == Order::Higher {
                            return Err(RelationError::HigherOrderDomain(component));
                        }
                        let heads = premise_functions(fibre, component)?;
                        let left_stuck = stuck(
                            arena,
                            left_reduction.normal,
                            (&branch.context, heads.0),
                            component,
                        )?;
                        let right_stuck = stuck(
                            arena,
                            right_reduction.normal,
                            (&branch.context, heads.1),
                            component,
                        )?;
                        if equal_values(arena, left_stuck.input, right_stuck.input)
                            != Convertibility::Convertible
                        {
                            return Err(RelationError::QuantifiedStep(component));
                        }
                        owed.push(ComponentObligation {
                            context: branch.context.clone(),
                            checks: Vec::from([(
                                left_stuck.input,
                                self.node(inner_argument)?.source,
                            )]),
                        });
                        let outputs = self.patterns_at(arena, inner_result, budget)?;
                        for output in outputs.into_iter().rev() {
                            allowance.charge()?;
                            let extension = BinderDepth::from(
                                u32::try_from(output.context.len())
                                    .map_err(|_error| RelationError::Budget)?,
                            );
                            let left = resume(
                                arena,
                                &mut table,
                                left_stuck.continuation,
                                (output.left, extension),
                            );
                            let right = resume(
                                arena,
                                &mut table,
                                right_stuck.continuation,
                                (output.right, extension),
                            );
                            let mut context = Vec::with_capacity(
                                branch.context.len().saturating_add(output.context.len()),
                            );
                            context.extend_from_slice(&branch.context);
                            context.extend_from_slice(&output.context);
                            pending.push(Branch {
                                context,
                                left,
                                right,
                            });
                        }
                    },
                }
            }
        }
        if steps.next().is_some() {
            return Err(RelationError::Coverage);
        }
        Ok(owed)
    }

    /// The argument and result relations of the function clause at the thunk
    /// type `classifier`.
    ///
    /// # Specification
    /// - ensures: the two premises of the program's function clause whose node
    ///   classifies `classifier`.
    /// - provides: the relation a quantified step's premise relates its
    ///   functions by, read from the program that bound the premise, so the
    ///   fold is not run again.
    /// - fails: `QuantifiedStep` naming `component` when no function clause
    ///   classifies `classifier`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the higher-order argument of the quantified witness
    ///   finds its clause; a fibre naming a Base binder never reaches here.
    /// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body scans the program's nodes for the function clause once; the check scans them once more"
        )
    )]
    #[spec(ensures: |ret| match ret {
        Ok((argument, result)) => self.nodes.iter().any(|node| node.source == classifier && node.clause == Clause::Function(argument, result)),
        Err(_) => !self.nodes.iter().any(|node| node.source == classifier && matches!(node.clause, Clause::Function(..))),
    })]
    fn function_at(
        &self,
        classifier: ValueTypeId,
        component: Component,
    ) -> Result<(RelationId, RelationId), RelationError>
    {
        self.nodes
            .iter()
            .find_map(|node| match node.clause {
                Clause::Function(argument, result) if node.source == classifier => {
                    Some((argument, result))
                },
                Clause::Unit
                | Clause::Empty
                | Clause::Discrete
                | Clause::Universe
                | Clause::Certificate
                | Clause::Relation
                | Clause::Atom { .. }
                | Clause::Product(..)
                | Clause::Sum(..)
                | Clause::Function(..)
                | Clause::List(_)
                | Clause::CaseLeft(..)
                | Clause::CaseRight(..) => None,
            })
            .ok_or(RelationError::QuantifiedStep(component))
    }

    /// Whether the relation at `relation` binds a function anywhere.
    ///
    /// # Specification
    /// - requires: `relation` addresses a node of this program.
    /// - ensures: [`Order::Higher`] exactly when a function clause or a
    ///   universe's relation clause is reachable from `relation` through
    ///   product, sum, list and case premises, itself included;
    ///   [`Order::First`] otherwise.
    /// - provides: the first-order test of a quantified step's argument type:
    ///   one input relates to itself only where its fibre has a diagonal, which
    ///   neither a function's identity nor a code's bridge supplies here.
    /// - fails: Arena on an address outside the program.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// - reason: the `while let` loop drains a worklist, not recursion.
    /// - measure: the program's nodes not yet visited; each is visited once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Bool reads first order; a function from functions
    ///   reads higher order beneath its argument.
    /// - witness: `element_identity::tests::a_quantified_evaluation_refuses_what_it_cannot_relate`
    #[spec(ensures: |ret| match ret {
        Ok(Order::First) => self.node(relation).is_ok_and(|node| !matches!(node.clause, Clause::Function(..) | Clause::Relation | Clause::Atom { .. })),
        Ok(Order::Higher) => true,
        Err(ref error) => matches!(*error, RelationError::Arena),
    })]
    fn order(
        &self,
        relation: RelationId,
    ) -> Result<Order, RelationError>
    {
        let mut pending = Vec::from([relation]);
        let mut visited = alloc::collections::BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            match self.node(id)?.clause {
                Clause::Function(..) | Clause::Relation | Clause::Atom { .. } => {
                    return Ok(Order::Higher);
                },
                Clause::Product(first, second)
                | Clause::Sum(first, second)
                | Clause::CaseLeft(first, second)
                | Clause::CaseRight(first, second) => pending.extend([first, second]),
                Clause::List(element) => pending.push(element),
                Clause::Unit
                | Clause::Empty
                | Clause::Discrete
                | Clause::Universe
                | Clause::Certificate => {},
            }
        }
        Ok(Order::First)
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
    #[spec(
        captures: components = evidence.0.len(),
        ensures: |ret| match ret {
            Ok(ref identity) => self.mode == Mode::Identity && identity.left == left && identity.right == right && matches!(identity.proof, Proof::HigherEvaluation(ref proof) if proof.0.len() == components),
            Err(RelationError::NonFibrant) => self.mode == Mode::Bridge,
            Err(_) => self.mode == Mode::Identity,
        },
    )]
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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |identity| identity.left == value && identity.right == value && matches!(identity.proof, Proof::HigherEvaluation(_))))]
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
    #[spec(ensures: |ret| match ret {
        Err(RelationError::NonFibrant) => self.mode == Mode::Bridge,
        Err(RelationError::HigherEvaluationRequired) => !matches!(identity.proof, Proof::HigherEvaluation(_)),
        _ => self.mode == Mode::Identity && match ret {
        Ok(Application::Return { left, right, .. }) => match *evidence { Pointwise::Return { left: ref a, right: ref b, .. } => a.value == left && b.value == right, Pointwise::Suspended => false },
        Ok(Application::Suspended { mode, .. }) => mode == self.mode && matches!(evidence, &Pointwise::Suspended),
        Err(_) => true,
    },
    })]
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

/// Replay one claimed evaluation, closed over its component's telescope.
///
/// # Specification
/// - requires: every body `replay.0` holds is closed.
/// - ensures: the verdict of replaying `computation = return value` under one
///   lambda per telescope entry, unfolding exactly the constants `replay.0`
///   defines.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — swapping components cannot change the replay goal; L3 — a
///   constant's body unfolds only when the caller supplies it.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
/// - witness: `element_identity::tests::a_higher_evaluation_unfolds_what_the_environment_admitted`
#[spec(ensures: |ret| ret != KernelVerdict::NotConvertible
    && (ret != KernelVerdict::Convertible || u64::from(replay.1) > 0))]
fn replay_evaluation(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    computation: ComputationId,
    evaluation: &Evaluation,
    replay: (&Unfoldings, ReplayBudget),
) -> KernelVerdict
{
    let mut returned = arena.computation_return(evaluation.value);
    for _ in context {
        returned = arena.computation_lambda(returned);
    }
    let returned = arena.value_thunk(returned);
    replay_claim(
        arena,
        context,
        computation,
        (returned, &evaluation.dialogue),
        replay,
    )
}

/// Replay a computation, closed over its telescope, against a closed value.
///
/// # Specification
/// - requires: every body `replay.0` holds is closed; `target.0` is closed.
/// - ensures: the verdict of replaying `thunk(λⁿ. computation) = target.0`
///   along the dialogue `target.1`, with one lambda per telescope entry,
///   unfolding exactly the constants `replay.0` defines.
/// - provides: the one replay a returned value and a stuck normal form share.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — as [`replay_evaluation`], and a stuck normal form
///   replays against the claim that reaches it.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
#[spec(ensures: |ret| ret != KernelVerdict::NotConvertible
    && (ret != KernelVerdict::Convertible || u64::from(replay.1) > 0))]
fn replay_claim(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    computation: ComputationId,
    target: (ValueId, &Dialogue),
    replay: (&Unfoldings, ReplayBudget),
) -> KernelVerdict
{
    let (unfoldings, budget) = replay;
    let (target, dialogue) = target;
    let mut computation = computation;
    for _ in context {
        computation = arena.computation_lambda(computation);
    }
    let computation = arena.value_thunk(computation);
    crate::replay::replay(
        arena,
        unfoldings,
        ReplaySides::Values(computation, target),
        EngineClaim::Convertible,
        dialogue.0.iter().copied(),
        budget,
    )
}

/// The checks one evaluation owes in one closed telescope.
#[derive(Clone, Debug)]
pub struct ComponentObligation
{
    /// The telescope the checks stand in, outermost first.
    pub context: Vec<ValueTypeId>,
    /// Each value with the type it must inhabit, in checking order: for a
    /// higher-evaluation component the premise evidence, both returned values
    /// and the output evidence; a quantified evaluation owes the premise
    /// evidence, each applied input and each return's three checks as
    /// obligations of their own telescopes.
    pub checks: Vec<(ValueId, ValueTypeId)>,
}

/// One untrusted step of a quantified evaluation, its dialogues anchored for
/// replay, in its tree's pre-order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Quantified
{
    /// Both sides return, as a higher-evaluation component does.
    Return
    {
        /// Source evaluation, supplied by an untrusted producer.
        left: Evaluation,
        /// Target evaluation, supplied by an untrusted producer.
        right: Evaluation,
        /// An inhabitant of the output relation, not an equality verdict.
        proof: ValueId,
    },
    /// Both sides reach closed normal forms stuck at an application of the
    /// functions the premise at `fibre` relates.
    Apply
    {
        /// The premise's de Bruijn index in the step's telescope.
        fibre: DeBruijnIndex,
        /// The source side's stuck normal form.
        left: NormalForm,
        /// The target side's stuck normal form.
        right: NormalForm,
    },
}

/// An untrusted closed normal form and the engine trace that must reach it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NormalForm
{
    /// The claimed normal form, closed: a thunk of one lambda per telescope
    /// entry.
    pub normal: ValueId,
    /// Replay must certify `thunk(λⁿ. computation) = normal`.
    pub dialogue: Dialogue,
}

/// One node of a quantified evaluation's pre-order walk: the telescope a step
/// stands in and the two computations it relates there.
struct Branch
{
    /// The telescope, outermost first.
    context: Vec<ValueTypeId>,
    /// The source side's current computation.
    left: ComputationId,
    /// The target side's current computation.
    right: ComputationId,
}

/// Whether a relation binds a function anywhere beneath it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Order
{
    /// No function clause is reachable.
    First,
    /// A function clause is reachable.
    Higher,
}

/// What a stuck application's result flows into.
#[derive(Clone, Copy, Debug)]
enum Continuation
{
    /// The application is the whole computation.
    Tail,
    /// The application is bound, and this body awaits its result.
    Bind(ComputationId),
}

/// A stuck normal form read under its telescope.
struct Stuck
{
    /// The input the function is applied at, under the telescope.
    input: ValueId,
    /// What the application's result flows into.
    continuation: Continuation,
}

/// The thunk type the premise at `fibre` relates two functions of.
///
/// # Specification
/// - ensures: `T` when the telescope entry `fibre` counts to is `Path(T, x₁,
///   x₀)` in identity mode, or `Bridge(T, x₁, x₀)` in bridge mode, over the two
///   entries just before it — the premise a function coordinate's coverage
///   binds.
/// - fails: `QuantifiedStep` naming `component` when the entry is past the
///   telescope or is not such a premise.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — the premise of the quantified witness reads its thunk
///   type; a fibre counting to a function binder refuses by name, and so does a
///   premise of the other mode.
/// - witness: `element_identity::tests::a_quantified_evaluation_refuses_what_it_cannot_relate`
/// - witness: `identity_recursion::function::tests::a_premise_relates_the_two_entries_just_before_it_in_order`
#[spec(ensures: |ret| match ret {
    Ok(domain) => arena.value_type(domain).is_some(),
    Err(ref error) => matches!(*error, RelationError::QuantifiedStep(found) if found == component),
})]
fn premise_classifier(
    arena: &TermArena,
    mode: Mode,
    context: &[ValueTypeId],
    fibre: DeBruijnIndex,
    component: Component,
) -> Result<ValueTypeId, RelationError>
{
    let refusal = || RelationError::QuantifiedStep(component);
    let distance = usize::try_from(u32::from(fibre)).map_err(|_error| refusal())?;
    let position = context
        .len()
        .checked_sub(distance.checked_add(1).ok_or_else(refusal)?)
        .ok_or_else(refusal)?;
    let entry = *context.get(position).ok_or_else(refusal)?;
    let ((
        Mode::Identity,
        Some(&ValueType::Path {
            domain,
            left,
            right,
        }),
    )
    | (
        Mode::Bridge,
        Some(&ValueType::Bridge {
            domain,
            left,
            right,
        }),
    )) = (mode, arena.value_type(entry))
    else {
        return Err(refusal());
    };
    let binds =
        |value: ValueId, index: DeBruijnIndex| arena.value(value) == Some(&Value::Variable(index));
    if binds(left, DeBruijnIndex::from(1_u32)) && binds(right, DeBruijnIndex::from(0_u32)) {
        Ok(domain)
    }
    else {
        Err(refusal())
    }
}

/// The indices of the two functions the premise at `fibre` relates.
///
/// # Specification
/// - ensures: the left function two entries outside the premise, the right one
///   entry outside it, both counted from the step's telescope.
/// - fails: `QuantifiedStep` naming `component` past the index range.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — the quantified witness's premise at index zero names the
///   functions at two and one; an index swapped or offset by one replays the
///   wrong function and refuses.
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
/// - witness: `element_identity::tests::a_quantified_evaluation_refuses_what_it_cannot_relate`
#[spec(ensures: |ret| match ret {
    Ok((left, right)) => Some(u32::from(left)) == u32::from(fibre).checked_add(2)
        && Some(u32::from(right)) == u32::from(fibre).checked_add(1),
    Err(ref error) => matches!(*error, RelationError::QuantifiedStep(found) if found == component),
})]
fn premise_functions(
    fibre: DeBruijnIndex,
    component: Component,
) -> Result<(DeBruijnIndex, DeBruijnIndex), RelationError>
{
    let distance = u32::from(fibre);
    let left = distance
        .checked_add(2)
        .ok_or(RelationError::QuantifiedStep(component))?;
    let right = distance
        .checked_add(1)
        .ok_or(RelationError::QuantifiedStep(component))?;
    Ok((DeBruijnIndex::from(left), DeBruijnIndex::from(right)))
}

/// Read a closed normal form as an application of the function at `under.1`,
/// stuck beneath the telescope `under.0`.
///
/// # Specification
/// - ensures: the input and continuation when `normal` is a thunk of one lambda
///   per telescope entry over `force f a` or `x ← force f a; K` with `f` the
///   variable `under.1`.
/// - fails: `QuantifiedStep` naming `component` for any other form.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a tail application and a bound one both read; a form
///   applying the other function refuses by name.
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
/// - witness: `element_identity::tests::a_quantified_evaluation_refuses_what_it_cannot_relate`
#[spec(ensures: |ret| match ret {
    Ok(ref found) => arena.value(found.input).is_some(),
    Err(ref error) => matches!(*error, RelationError::QuantifiedStep(found) if found == component),
})]
fn stuck(
    arena: &TermArena,
    normal: ValueId,
    under: (&[ValueTypeId], DeBruijnIndex),
    component: Component,
) -> Result<Stuck, RelationError>
{
    let (context, head) = under;
    let refusal = RelationError::QuantifiedStep(component);
    let Some(&Value::Thunk(mut body)) = arena.value(normal)
    else {
        return Err(refusal);
    };
    for _ in context {
        let Some(&Computation::Lambda(inner)) = arena.computation(body)
        else {
            return Err(refusal);
        };
        body = inner;
    }
    let (application, continuation) = match arena.computation(body) {
        Some(&Computation::Bind(bound, rest)) => (bound, Continuation::Bind(rest)),
        _ => (body, Continuation::Tail),
    };
    let Some(&Computation::Application(forced, input)) = arena.computation(application)
    else {
        return Err(refusal);
    };
    let Some(&Computation::Force(function)) = arena.computation(forced)
    else {
        return Err(refusal);
    };
    if arena.value(function) != Some(&Value::Variable(head)) {
        return Err(refusal);
    }
    Ok(Stuck {
        input,
        continuation,
    })
}

/// The computation a stuck side continues as once its application returns
/// `output.0`, beneath `output.1` more binders.
///
/// # Specification
/// - requires: `output.0` stands under the step's telescope extended by
///   `output.1` binders; a bound continuation stands under the telescope and
///   its own binder.
/// - ensures: `return o` for a tail application; for a bound one, its body
///   weakened past the extension above its own binder, then instantiated at
///   `o`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a twice-applied body reads its second application at the
///   first's output; a misplaced shift changes the replayed claim.
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
#[spec(ensures: |ret| match continuation {
    Continuation::Tail => arena.computation(ret) == Some(&Computation::Return(output.0)),
    Continuation::Bind(_) => arena.computation(ret).is_some(),
})]
fn resume(
    arena: &mut TermArena,
    table: &mut ContentTable,
    continuation: Continuation,
    output: (ValueId, BinderDepth),
) -> ComputationId
{
    let (value, extension) = output;
    match continuation {
        Continuation::Tail => arena.computation_return(value),
        Continuation::Bind(body) => {
            let weakened = shift_computation(
                arena,
                table,
                &mut NullMemo,
                body,
                BinderDepth::from(1_u32),
                extension,
            );
            substitute_computation(arena, table, &mut NullMemo, weakened, value)
        },
    }
}
