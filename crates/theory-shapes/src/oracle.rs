//! Decidable entailment, case derivations, and independent evidence replay.

use alloc::vec;
use alloc::vec::Vec;

use crate::boundary::Case;
use crate::boundary::ShapeError;
use crate::boundary::Variable;
use crate::formula::Node;
use crate::formula::Problem;
use crate::formula::Shape;
use crate::formula::Truth;
use crate::formula::Value;

/// A rule of the finite-model entailment derivation calculus.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rule
{
    /// The premise is forced false under the current partial assignment.
    FalsePremise,
    /// The conclusion is forced true under the current partial assignment.
    TrueConclusion,
    /// Derive the claim in every observation case of this unassigned variable.
    /// Child derivations follow in domain order; zero cases discharge
    /// emptiness.
    Split(Variable),
}

/// An untrusted, flat preorder derivation with no owning recursive structure.
///
/// # Specification
/// - provides: a rule tree whose branch arities are supplied by the query's
///   context; arbitrary data may be supplied and must pass [`Self::validate`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 replay plus forged rules distinguish omitted branches,
///   wrong leaf conditions, repeated splits and trailing evidence.
/// - witness: `tests::faces::forged_evidence_is_refused`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Derivation
{
    /// Preorder inference rules, one root followed by all its descendants.
    pub rules: Vec<Rule>,
}

/// An untrusted total assignment intended to satisfy premise and refute goal.
///
/// # Specification
/// - provides: one observation per coordinate; arbitrary values require
///   [`Self::validate`] before they count as a countermodel.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 validation and L3 wrong assignments distinguish false
///   refutations, shape mismatches, and incomplete models.
/// - witness: `tests::faces::forged_evidence_is_refused`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Countermodel
{
    /// Observations in context order.
    pub assignment: Vec<Value>,
}

/// Either a derivation of entailment or a countermodel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Evidence
{
    /// Every observation assignment satisfies the implication.
    Holds(Derivation),
    /// The implication fails at this assignment.
    Refuted(Countermodel),
}

/// A suspended search split; cases before `next` are already discharged.
#[derive(Clone, Copy, Debug)]
struct Frame
{
    /// The assigned coordinate.
    variable: Variable,
    /// Its next unvisited observation case.
    next: Case,
}

/// Whether backtracking found another case.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Progress
{
    /// The shared assignment contains the next case to inspect.
    More,
    /// Every branch is discharged.
    Finished,
}

/// Advances depth-first search without copying assignments.
///
/// # Specification
/// - ensures: each split visits every case in order and restores unassigned
///   status after its last case; finished means no pending split remains.
/// - fails: malformed internal variable or case indices are refused.
/// - panics: none.
///
/// # Errors
/// Returns [`ShapeError::VariableOutside`] or [`ShapeError::CaseOutside`].
///
/// # Adequacy
/// - hypothesis: L2 complete finite-model comparison detects skipped cases or
///   retained assignments; L1 replay rejects a missing positive branch.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
// executable: none — the traversal obligation relates the entire search trace;
// independent replay and finite-model comparison observe that obligation.
fn advance(
    context: &[Shape],
    assignment: &mut [Value],
    frames: &mut Vec<Frame>,
) -> Result<Progress, ShapeError>
{
    while let Some(frame) = frames.last_mut() {
        let shape = *context
            .get(frame.variable.0)
            .ok_or(ShapeError::VariableOutside(frame.variable))?;
        let entry = assignment
            .get_mut(frame.variable.0)
            .ok_or(ShapeError::VariableOutside(frame.variable))?;
        if frame.next.0 < shape.cases().0 {
            *entry = shape.value(frame.next)?;
            frame.next.0 = frame.next.0.saturating_add(1);
            return Ok(Progress::More);
        }
        *entry = Value::Unassigned;
        frames.pop();
    }
    Ok(Progress::Finished)
}

/// Decides the query and returns evidence suitable for independent replay.
///
/// # Specification
/// - ensures: `Holds` carries a derivation accepted by
///   [`Derivation::validate`]; `Refuted` carries an assignment accepted by
///   [`Countermodel::validate`]. The result agrees with implication in every
///   finite observation assignment.
/// - provides: a total decision on admitted finite syntax, subject to available
///   allocation. Iterative search terminates because every finite case tree is
///   exhausted and each split assigns a previously unassigned coordinate.
/// - fails: a broken private query or search invariant is a typed error, never
///   a refutation. Public constructors exclude those malformed states.
/// - panics: none.
/// - intension: for domain sizes `d_i` and formula size `s` (including subset
///   tables), with `n` context coordinates, worst-case time is `O((s+n)(n+1)
///   product(max(1,d_i)))`; traversal storage is `O(s+n)` plus the accumulated
///   proof prefix (returned on success, discarded on refutation). This prefix
///   can be exponential in either outcome. No assignment is copied per branch.
///
/// # Errors
/// Returns [`ShapeError::VariableOutside`], [`ShapeError::WrongShape`],
/// [`ShapeError::PointOutside`], [`ShapeError::CaseOutside`], or
/// [`ShapeError::MalformedFormula`] only for broken private invariants.
///
/// # Adequacy
/// - hypothesis: L2 independent enumeration over all tested finite carriers and
///   generated formulas detects wrong polarity, endpoint coverage, branch loss,
///   and set-membership errors. L1 replay checks every produced certificate.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
/// - witness: `tests::faces::generic_coordinates_refute_endpoint_coverage`
/// - witness: `tests::faces::deep_formulas_use_no_call_stack`
// executable: none — replaying the certificate in an exit predicate would make
// instrumentation perform the full independent validation inside the producer.
#[inline]
pub fn decide(problem: &Problem) -> Result<Evidence, ShapeError>
{
    let (context, premise, conclusion) = problem.parts();
    // Empty finite factors make the entire assignment space empty, even when
    // neither formula mentions that coordinate.
    if let Some(variable) = context.iter().position(|shape| shape.cases().0 == 0) {
        return Ok(Evidence::Holds(Derivation {
            rules: vec![Rule::Split(Variable(variable))],
        }));
    }
    let mut assignment = vec![Value::Unassigned; context.len()];
    let mut scratch = Vec::with_capacity(premise.nodes().len().max(conclusion.nodes().len()));
    let mut frames = Vec::with_capacity(context.len());
    let mut rules = Vec::new();
    loop {
        let left = premise.evaluate(&assignment, &mut scratch)?;
        let right = conclusion.evaluate(&assignment, &mut scratch)?;
        if left == Truth::No {
            rules.push(Rule::FalsePremise);
        }
        else if right == Truth::Yes {
            rules.push(Rule::TrueConclusion);
        }
        else if let Some(variable) =
            premise
                .nodes()
                .iter()
                .chain(conclusion.nodes())
                .find_map(|node| match *node {
                    | Node::Endpoint(variable, _) | Node::Member(variable, _)
                        if assignment.get(variable.0) == Some(&Value::Unassigned) =>
                    {
                        Some(variable)
                    },
                    | _ => None,
                })
        {
            let shape = *context
                .get(variable.0)
                .ok_or(ShapeError::VariableOutside(variable))?;
            let value = shape.value(Case(0))?;
            let entry = assignment
                .get_mut(variable.0)
                .ok_or(ShapeError::VariableOutside(variable))?;
            *entry = value;
            rules.push(Rule::Split(variable));
            frames.push(Frame {
                variable,
                next: Case(1),
            });
            continue;
        }
        else {
            for (shape, value) in context.iter().zip(&mut assignment) {
                if *value == Value::Unassigned {
                    *value = shape.value(Case(0))?;
                }
            }
            return Ok(Evidence::Refuted(Countermodel { assignment }));
        }
        if advance(context, &mut assignment, &mut frames)? == Progress::Finished {
            return Ok(Evidence::Holds(Derivation { rules }));
        }
    }
}

/// Replay tasks, independent of the oracle's search frames and backtracking.
#[derive(Clone, Copy, Debug)]
enum Replay
{
    /// Consume one rule under the current assignment.
    Check,
    /// Install a case, check its child, then proceed to the next case.
    Case(Variable, Case),
}

impl Derivation
{
    /// Replays a derivation without invoking search or trusting its branch
    /// count.
    ///
    /// # Specification
    /// - ensures: success means every required case has a valid child and every
    ///   leaf's indicated truth bound holds. Precisely one tree is consumed.
    /// - fails: false leaves, bad splits, missing or trailing rules are
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::InvalidDerivation`] for malformed evidence; a
    /// broken private query invariant can additionally yield evaluation
    /// errors.
    ///
    /// # Adequacy
    /// - hypothesis: L1 valid replay and L3 hostile evidence distinguish branch
    ///   omission, repeated splits, incorrect leaves, and query replay attacks.
    /// - witness: `tests::faces::forged_evidence_is_refused`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    // executable: none — the independent checker is itself the evidence route;
    // an exit predicate would duplicate replay rather than add an observer.
    #[inline]
    pub fn validate(
        &self,
        problem: &Problem,
    ) -> Result<(), ShapeError>
    {
        let (context, premise, conclusion) = problem.parts();
        let mut assignment = vec![Value::Unassigned; context.len()];
        let mut scratch = Vec::with_capacity(premise.nodes().len().max(conclusion.nodes().len()));
        let mut pending = vec![Replay::Check];
        let mut rules = self.rules.iter();
        while let Some(task) = pending.pop() {
            match task {
                | Replay::Check => match *rules.next().ok_or(ShapeError::InvalidDerivation)? {
                    | Rule::FalsePremise => {
                        if premise.evaluate(&assignment, &mut scratch)? != Truth::No {
                            return Err(ShapeError::InvalidDerivation);
                        }
                    },
                    | Rule::TrueConclusion => {
                        if conclusion.evaluate(&assignment, &mut scratch)? != Truth::Yes {
                            return Err(ShapeError::InvalidDerivation);
                        }
                    },
                    | Rule::Split(variable) => {
                        if assignment.get(variable.0) != Some(&Value::Unassigned) {
                            return Err(ShapeError::InvalidDerivation);
                        }
                        pending.push(Replay::Case(variable, Case(0)));
                    },
                },
                | Replay::Case(variable, case) => {
                    let shape = *context
                        .get(variable.0)
                        .ok_or(ShapeError::InvalidDerivation)?;
                    let entry = assignment
                        .get_mut(variable.0)
                        .ok_or(ShapeError::InvalidDerivation)?;
                    if case.0 == shape.cases().0 {
                        *entry = Value::Unassigned;
                    }
                    else {
                        *entry = shape.value(case)?;
                        pending.push(Replay::Case(variable, Case(case.0.saturating_add(1))));
                        pending.push(Replay::Check);
                    }
                },
            }
        }
        if rules.next().is_some() {
            return Err(ShapeError::InvalidDerivation);
        }
        Ok(())
    }
}

impl Countermodel
{
    /// Checks scope, sorts, totality, and both sides of the claimed refutation.
    ///
    /// # Specification
    /// - ensures: success means every coordinate is admissible, the premise
    ///   holds, and the conclusion fails under exactly this assignment.
    /// - fails: malformed assignments and nonrefuting assignments are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::AssignmentLength`],
    /// [`ShapeError::IncompleteAssignment`], [`ShapeError::WrongShape`],
    /// [`ShapeError::PointOutside`], or [`ShapeError::NotCountermodel`]. A
    /// broken private formula invariant can additionally yield
    /// [`ShapeError::MalformedFormula`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 hostile assignments distinguish type, length, finite
    ///   bounds and totality checks, and both truth requirements independently.
    /// - witness: `tests::faces::forged_evidence_is_refused`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    // executable: none — a second evaluator in an exit predicate would not be
    // independent evidence; the brute-force test evaluator supplies that route.
    #[inline]
    pub fn validate(
        &self,
        problem: &Problem,
    ) -> Result<(), ShapeError>
    {
        let (context, premise, conclusion) = problem.parts();
        if self.assignment.len() != context.len() {
            return Err(ShapeError::AssignmentLength);
        }
        for (index, (shape, value)) in context.iter().zip(&self.assignment).enumerate() {
            match (*shape, *value) {
                | (_, Value::Unassigned) => {
                    return Err(ShapeError::IncompleteAssignment(Variable(index)));
                },
                | (Shape::Bridge, Value::Generic | Value::Endpoint(_)) => {},
                | (Shape::Finite(count), Value::Point(point)) => {
                    if point.0 >= count.0 {
                        return Err(ShapeError::PointOutside(point));
                    }
                },
                | _ => return Err(ShapeError::WrongShape(Variable(index))),
            }
        }
        let mut scratch = Vec::with_capacity(premise.nodes().len().max(conclusion.nodes().len()));
        let left = premise.evaluate(&self.assignment, &mut scratch)?;
        let right = conclusion.evaluate(&self.assignment, &mut scratch)?;
        if left != Truth::Yes || right != Truth::No {
            return Err(ShapeError::NotCountermodel);
        }
        Ok(())
    }
}
