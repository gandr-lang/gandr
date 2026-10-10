//! Hypothesis-indexed structural staging rules and certificate replay.
//!
//! The experimental language lives in `kernel_term::stage`, outside the wire
//! vocabulary. Each public replay forms both endpoints in an ordinary
//! telescope and checks every equation. No cached result supplies authority.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;
use gandr_kernel_term::stage::instantiate;

/// Require an ordinary `j : In model` hypothesis, without changing its context.
///
/// # Specification
/// - ensures: succeeds exactly when the telescope contains the indexed token.
/// - fails: `MissingHypothesis` for a missing token; propagates lookup errors.
/// - panics: none.
///
/// # Errors
/// Returns `MissingHypothesis` or `UnknownType`.
///
/// # Adequacy
/// - hypothesis: L3 — absent and wrong-model tokens distinguish admission.
/// - witness: `stage::tests::hypotheses_and_universe_boundary`
fn permission(
    arena: &Arena,
    context: &[TypeId],
    model: Model,
) -> Result<(), StageError>
{
    for ty in context {
        if arena.ty(*ty)? == Type::In(model) {
            return Ok(());
        }
    }
    Err(StageError::MissingHypothesis(model))
}

/// Form a classifier and return its universe stage.
///
/// # Specification
/// - ensures: arrows stay within one stage, lifts have inner domains, and every
///   inner classifier has its model's ordinary `In` hypothesis.
/// - fails: lookup, budget, missing-hypothesis or stage-formation refusals.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownType`, `Exhausted`, `MissingHypothesis`, `StageMismatch`,
/// or `Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L3 — crossed arrows, nested lifts, and token mismatches
///   distinguish the universe boundary from a context switch.
/// - witness: `stage::tests::hypotheses_and_universe_boundary`
#[inline]
pub fn form(
    arena: &Arena,
    context: &[TypeId],
    root: TypeId,
    budget: &mut Budget,
) -> Result<Stage, StageError>
{
    let mut pending = Vec::from([(root, false)]);
    let mut stages = BTreeMap::new();
    while let Some((id, ready)) = pending.pop() {
        budget.spend()?;
        if stages.contains_key(&id) {
            continue;
        }
        let ty = arena.ty(id)?;
        if !ready {
            pending.push((id, true));
            match ty {
                | Type::Arrow(a, b) => {
                    pending.push((b, false));
                    pending.push((a, false));
                },
                | Type::Lift(inner) => pending.push((inner, false)),
                | _ => {},
            }
            continue;
        }
        let stage = match ty {
            | Type::In(_) | Type::Nat(Stage::Outer) => Stage::Outer,
            | Type::Universe(model) | Type::Nat(Stage::Inner(model)) => {
                permission(arena, context, model)?;
                Stage::Inner(model)
            },
            | Type::Arrow(a, b) => {
                let a = *stages.get(&a).ok_or(StageError::Unbalanced)?;
                let b = *stages.get(&b).ok_or(StageError::Unbalanced)?;
                if a != b {
                    return Err(StageError::StageMismatch);
                }
                a
            },
            | Type::Lift(inner) => {
                if !matches!(stages.get(&inner), Some(Stage::Inner(_))) {
                    return Err(StageError::StageMismatch);
                }
                Stage::Outer
            },
        };
        stages.insert(id, stage);
    }
    stages.get(&root).copied().ok_or(StageError::Unbalanced)
}

/// Check that a code describes the small object signature, not its universe.
///
/// # Specification
/// - ensures: accepts only inner naturals and arrows over those codes.
/// - fails: `TypeMismatch` for a universe, lift, token or outer natural;
///   propagates lookup and work errors.
/// - panics: none.
///
/// # Errors
/// Returns `TypeMismatch`, `UnknownType` or `Exhausted`.
///
/// # Adequacy
/// - hypothesis: L3 — coding the universe directly or beneath an arrow
///   distinguishes the small code family from a type-in-type encoding.
/// - witness: `stage::tests::hypotheses_and_universe_boundary`
fn form_code(
    arena: &Arena,
    root: TypeId,
    budget: &mut Budget,
) -> Result<(), StageError>
{
    let mut pending = Vec::from([root]);
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        budget.spend()?;
        if !seen.insert(id) {
            continue;
        }
        match arena.ty(id)? {
            | Type::Nat(Stage::Inner(_)) => {},
            | Type::Arrow(domain, codomain) => {
                pending.push(domain);
                pending.push(codomain);
            },
            | _ => return Err(StageError::TypeMismatch),
        }
    }
    Ok(())
}

/// A suspended typing obligation.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Infer one term.
    Visit(TermId),
    /// Assemble a constructor from its children's inferred types.
    Finish(Term),
}

/// Infer a staged term under an ordinary structural telescope.
///
/// # Specification
/// - ensures: derives a classifier without adding, deleting, restricting or
///   consuming any caller hypothesis; only a lambda extends the telescope.
/// - fails: malformed syntax, unbound variables, missing tokens, stage or type
///   mismatches, and inner-to-outer elimination are named refusals.
/// - panics: none.
///
/// # Errors
/// Returns syntax/formation errors, `Unbound`, `TypeMismatch`,
/// `InnerToOuter`, `Overflow`, `Exhausted`, or `Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L3 — quotation over an open object variable and splicing over
///   an open lifted variable distinguish the two stages; elimination controls
///   distinguish permission from forbidden escape.
/// - witness: `stage::tests::hypotheses_and_universe_boundary`
/// - witness: `stage::tests::conversion_round_trips`
#[inline]
pub fn infer(
    arena: &mut Arena,
    hypotheses: &[TypeId],
    root: TermId,
    budget: &mut Budget,
) -> Result<TypeId, StageError>
{
    let mut context = Vec::with_capacity(hypotheses.len());
    for ty in hypotheses {
        form(arena, &context, *ty, budget)?;
        context.push(*ty);
    }
    let mut tasks = Vec::from([Task::Visit(root)]);
    let mut answers = Vec::new();
    while let Some(task) = tasks.pop() {
        budget.spend()?;
        match task {
            | Task::Visit(id) => {
                let term = arena.term(id)?;
                match term {
                    | Term::Variable(index) => {
                        let slot = context
                            .len()
                            .checked_sub(index.0.saturating_add(1))
                            .ok_or(StageError::Unbound(index))?;
                        answers.push(*context.get(slot).ok_or(StageError::Unbound(index))?);
                    },
                    | Term::Natural(stage, _) => {
                        let ty = arena.alloc_type(Type::Nat(stage))?;
                        form(arena, &context, ty, budget)?;
                        answers.push(ty);
                    },
                    | Term::Code(ty) => {
                        let Stage::Inner(model) = form(arena, &context, ty, budget)?
                        else {
                            return Err(StageError::StageMismatch);
                        };
                        form_code(arena, ty, budget)?;
                        let ty = arena.alloc_type(Type::Universe(model))?;
                        answers.push(ty);
                    },
                    | Term::Lambda(domain, body) => {
                        form(arena, &context, domain, budget)?;
                        context.push(domain);
                        tasks.push(Task::Finish(term));
                        tasks.push(Task::Visit(body));
                    },
                    | _ => {
                        tasks.push(Task::Finish(term));
                        tasks.extend(term.children().into_iter().flatten().rev().map(Task::Visit));
                    },
                }
            },
            | Task::Finish(term) => {
                let last = answers.pop().ok_or(StageError::Unbalanced)?;
                let ty = match term {
                    | Term::Lambda(domain, _) => {
                        context.pop().ok_or(StageError::Unbalanced)?;
                        arena.alloc_type(Type::Arrow(domain, last))?
                    },
                    | Term::Apply(..) => {
                        let head = answers.pop().ok_or(StageError::Unbalanced)?;
                        let Type::Arrow(domain, codomain) = arena.ty(head)?
                        else {
                            return Err(StageError::TypeMismatch);
                        };
                        if last != domain {
                            return Err(StageError::TypeMismatch);
                        }
                        codomain
                    },
                    | Term::Multiply(..) => {
                        let first = answers.pop().ok_or(StageError::Unbalanced)?;
                        if first != last || !matches!(arena.ty(last)?, Type::Nat(Stage::Inner(_))) {
                            return Err(StageError::TypeMismatch);
                        }
                        last
                    },
                    | Term::Quote(_) => {
                        if !matches!(form(arena, &context, last, budget)?, Stage::Inner(_)) {
                            return Err(StageError::StageMismatch);
                        }
                        arena.alloc_type(Type::Lift(last))?
                    },
                    | Term::Splice(_) => {
                        let Type::Lift(inner) = arena.ty(last)?
                        else {
                            return Err(StageError::TypeMismatch);
                        };
                        inner
                    },
                    | Term::Iterate(..) => {
                        let initial = answers.pop().ok_or(StageError::Unbalanced)?;
                        let count = answers.pop().ok_or(StageError::Unbalanced)?;
                        let Type::Nat(count_stage) = arena.ty(count)?
                        else {
                            return Err(StageError::TypeMismatch);
                        };
                        let result_stage = form(arena, &context, initial, budget)?;
                        if matches!((count_stage, result_stage), (Stage::Inner(_), Stage::Outer)) {
                            return Err(StageError::InnerToOuter);
                        }
                        if count_stage != result_stage {
                            return Err(StageError::StageMismatch);
                        }
                        if arena.ty(last)? != Type::Arrow(initial, initial) {
                            return Err(StageError::TypeMismatch);
                        }
                        initial
                    },
                    | Term::Eliminate(_, target) => {
                        let source_stage = form(arena, &context, last, budget)?;
                        let target_stage = form(arena, &context, target, budget)?;
                        if matches!(
                            (source_stage, target_stage),
                            (Stage::Inner(_), Stage::Outer)
                        ) {
                            return Err(StageError::InnerToOuter);
                        }
                        if last != target {
                            return Err(StageError::TypeMismatch);
                        }
                        target
                    },
                    | _ => return Err(StageError::Unbalanced),
                };
                form(arena, &context, ty, budget)?;
                answers.push(ty);
            },
        }
    }
    answers.pop().ok_or(StageError::Unbalanced)
}

/// Compare syntax structurally, preserving all binders and stage indices.
///
/// # Specification
/// - ensures: accepts exactly equal syntax modulo arena sharing.
/// - fails: `InvalidCertificate` on a differing constructor or payload;
///   propagates lookup and work errors.
/// - panics: none.
///
/// # Errors
/// Returns `InvalidCertificate`, `UnknownTerm`, `Exhausted`, or `Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L3 — a changed literal in an otherwise valid certificate
///   distinguishes content equality from an unchecked producer assertion.
/// - witness: `stage::tests::certificate_tampering_is_refused`
fn same(
    arena: &Arena,
    left: TermId,
    right: TermId,
    budget: &mut Budget,
) -> Result<(), StageError>
{
    let mut pending = Vec::from([(left, right)]);
    let mut seen = BTreeSet::new();
    while let Some((left, right)) = pending.pop() {
        budget.spend()?;
        if left == right || !seen.insert((left, right)) {
            continue;
        }
        let left = arena.term(left)?;
        let right = arena.term(right)?;
        if left.rebuild(right.children())? != right {
            return Err(StageError::InvalidCertificate);
        }
        for (a, b) in left
            .children()
            .into_iter()
            .flatten()
            .zip(right.children().into_iter().flatten())
        {
            pending.push((a, b));
        }
    }
    Ok(())
}

/// Derive the reduct of the named rule, without searching for a redex.
///
/// # Specification
/// - ensures: re-derives exactly the selected local conversion step.
/// - fails: `InvalidCertificate` if the selected rule does not apply;
///   propagates syntax, substitution and budget errors.
/// - panics: none.
///
/// # Errors
/// Returns `InvalidCertificate`, lookup, overflow, exhaustion or work errors.
///
/// # Adequacy
/// - hypothesis: L3 — both quote/splice rules, both iterator rules, beta
///   capture avoidance and incorrect rule tags separate the rule clauses.
/// - witness: `stage::tests::conversion_round_trips`
/// - witness: `stage::tests::certificate_tampering_is_refused`
fn reduct(
    arena: &mut Arena,
    source: TermId,
    rule: Rule,
    budget: &mut Budget,
) -> Result<TermId, StageError>
{
    match (rule, arena.term(source)?) {
        | (Rule::SpliceQuote, Term::Splice(quoted)) => {
            let Term::Quote(body) = arena.term(quoted)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            Ok(body)
        },
        | (Rule::QuoteSplice, Term::Quote(spliced)) => {
            let Term::Splice(body) = arena.term(spliced)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            Ok(body)
        },
        | (Rule::Beta, Term::Apply(head, argument)) => {
            let Term::Lambda(_, body) = arena.term(head)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            instantiate(arena, body, argument, budget)
        },
        | (Rule::IterateZero, Term::Iterate(count, initial, _)) => {
            if !matches!(arena.term(count)?, Term::Natural(_, Natural(0))) {
                return Err(StageError::InvalidCertificate);
            }
            Ok(initial)
        },
        | (Rule::IterateSuccessor, Term::Iterate(count, initial, step)) => {
            let Term::Natural(stage, Natural(count)) = arena.term(count)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            let count = count.checked_sub(1).ok_or(StageError::InvalidCertificate)?;
            let predecessor = arena.alloc(Term::Natural(stage, Natural(count)))?;
            let recursive = arena.alloc(Term::Iterate(predecessor, initial, step))?;
            arena.alloc(Term::Apply(step, recursive))
        },
        | (Rule::Eliminate, Term::Eliminate(body, _)) => Ok(body),
        | _ => Err(StageError::InvalidCertificate),
    }
}

/// Find a replay-local equivalence representative.
///
/// # Specification
/// - ensures: follows only decreasing parent identities, so no cycle occurs.
/// - fails: `Exhausted` if the walk spends its allowance.
/// - panics: none.
///
/// # Errors
/// Returns `Exhausted`.
///
/// # Adequacy
/// - hypothesis: L3 — transitive conversions connect endpoints while a
///   disconnected final proposal is refused.
/// - witness: `stage::tests::certificate_tampering_is_refused`
fn representative(
    parents: &BTreeMap<TermId, TermId>,
    mut id: TermId,
    budget: &mut Budget,
) -> Result<TermId, StageError>
{
    while let Some(parent) = parents.get(&id) {
        budget.spend()?;
        id = *parent;
    }
    Ok(id)
}

/// Replay a complete certificate and return its re-derived classifier.
///
/// # Specification
/// - ensures: both endpoints have the same classifier, every equation is
///   checked, and the endpoint pair is connected by those checked equations.
/// - fails: typing refusals or `InvalidCertificate`; no certificate or memo can
///   assert an equation without a rule that derives it.
/// - panics: none.
///
/// # Errors
/// Returns formation, typing, syntax, budget, or certificate errors.
///
/// # Adequacy
/// - hypothesis: L3 — altered targets, rule tags, missing derivations and
///   cross-universe endpoints distinguish all certificate trust boundaries.
/// - witness: `stage::tests::conversion_round_trips`
/// - witness: `stage::tests::certificate_tampering_is_refused`
#[inline]
pub fn replay(
    arena: &mut Arena,
    context: &[TypeId],
    certificate: &Certificate,
    budget: &mut Budget,
) -> Result<TypeId, StageError>
{
    let source_type = infer(arena, context, certificate.source, budget)?;
    let target_type = infer(arena, context, certificate.target, budget)?;
    if source_type != target_type {
        return Err(StageError::TypeMismatch);
    }
    let mut parents = BTreeMap::new();
    for step in &certificate.steps {
        budget.spend()?;
        let source = arena.term(step.source)?;
        let target = arena.term(step.target)?;
        if step.rule == Rule::Congruence {
            let mut left = source.children();
            let mut right = target.children();
            for child in left.iter_mut().chain(right.iter_mut()).flatten() {
                *child = representative(&parents, *child, budget)?;
            }
            if source.rebuild(left)? != target.rebuild(right)? {
                return Err(StageError::InvalidCertificate);
            }
        }
        else {
            let expected = reduct(arena, step.source, step.rule, budget)?;
            same(arena, expected, step.target, budget)?;
        }
        let source = representative(&parents, step.source, budget)?;
        let target = representative(&parents, step.target, budget)?;
        if source != target {
            parents.insert(source.max(target), source.min(target));
        }
    }
    let source = representative(&parents, certificate.source, budget)?;
    let target = representative(&parents, certificate.target, budget)?;
    if source != target {
        return Err(StageError::InvalidCertificate);
    }
    Ok(source_type)
}

#[cfg(test)]
mod tests;
