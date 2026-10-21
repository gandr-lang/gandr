//! Hypothesis-indexed structural staging rules and certificate replay.
//!
//! The experimental language lives in `kernel_term::stage`, outside the wire
//! vocabulary. Each public replay forms both endpoints in an ordinary
//! telescope and checks every equation. No cached result supplies authority.
//!
//! # The stage universe
//!
//! This module checks a one-depth structural staging language. An ordinary
//! hypothesis `j : In M` admits the inner universe `U₀(M)`; its codes describe
//! naturals and structural arrows. `Lift(A)` classifies meta programs
//! producing inner terms. Quote and splice leave the telescope unchanged.
//! Their two round trips are conversion rules, including over open variables.
//!
//! Formation keeps arrow domains and codomains at one stage. Natural iteration
//! stays within its scrutinee's stage. A proposed elimination from an inner
//! type or its code universe into the outer framework returns
//! `StageError::InnerToOuter`. Missing or wrong-model tokens return
//! `MissingHypothesis`; nested lifts return `StageMismatch`.
//!
//! [`replay`] independently forms both endpoints, derives every elementary
//! reduct, and checks congruence only over child equations it has proved.
//! Its local equivalence table connects checked equations, carries no imported
//! answers, and is discarded on return. The ordinary check memo and its six
//! binding conditions are unchanged. The auxiliary arena retains replay
//! scratch syntax; callers own its lifetime and each walk has an explicit work
//! budget. The [`admission`](crate::admission) module admits guarded families
//! of these equations without replaying the rule per member.
//!
//! The representation is `gandr-kernel-term`'s `stage` arena, the producer
//! `gandr-core-nbe`'s staged normalizer, and residual readmission
//! `gandr-core-checker`'s `stage::compile`. The fragment has one structural
//! stage depth and an auxiliary arena; native formers, artifact encoding and
//! surface syntax are separate integration boundaries.
//!
//! **Placement.** A separate rule language keeps native codecs and all
//! core walks unchanged. Flat arenas, finite worklists and call-local DAG
//! tables avoid recursive ownership and repeated expansion of shared rewrite
//! nodes. The alternative is native former integration across every walker
//! and codec; choose it when persisted staged declarations become the
//! requested boundary. No dependency is added. Normalization strategy remains
//! outside the kernel.
//!
//! The rules follow András Kovács, "Staged Compilation with Two-Level Type
//! Theory", ICFP 2022, §2, `doi:10.1145/3547641`. His TFP 2026 talk "The
//! problem with sub-structural typing"
//! (<https://andraskovacs.github.io/pdfs/tfp26prez.pdf>) identifies why linear
//! application cannot support the same lifted application: the free-variable
//! supports need not be disjoint. This fragment permits weakening and
//! contraction throughout.
//!
//! # Readmission
//!
//! `gandr_core_checker::stage::compile` replays a stage certificate, then
//! extracts its quoted natural function into backward-referencing first-order
//! register instructions. Open captures and every residual constructor other
//! than the single input, natural literals and multiplication are refused.
//!
//! `Program::admit` translates that program to a CBPV thunk with one
//! top-level lambda, sequencing binds and direct primitive calls.
//! [`Environment::add_decl`] checks the declaration. Object naturals use
//! nonnegative integer literals; multiplication is an explicitly admitted
//! typed axiom, visible in the audit. The kernel proves typing and staging
//! conversion, not arithmetic properties of that primitive.
//! `Program::execute` supplies checked machine-natural arithmetic, returning
//! `Overflow` instead of wrapping.
//!
//! The end-to-end witness independently interprets the admitted CBPV body and
//! compares it with exponentiation over the same bounded grid as the
//! producer's witness. It also checks the axiom audit, absent unchecked
//! admissions, open capture refusal and a normal form whose certificate
//! derivation was removed.
//!
//! [`Environment::add_decl`]: crate::Environment::add_decl

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
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
#[spec(ensures: |ret| match ret {
    Ok(()) => context.iter().any(|ty| arena.ty(*ty) == Ok(Type::In(model))),
    Err(StageError::MissingHypothesis(actual)) => actual == model
        && !context.iter().any(|ty| arena.ty(*ty) == Ok(Type::In(model))),
    Err(_) => true,
})]
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
/// - witness: `stage::tests::typing_refusals_preserve_stage_boundary`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|stage|
    (match *stage {
        Stage::Inner(model) => context.iter().any(|ty| arena.ty(*ty) == Ok(Type::In(model))),
        Stage::Outer => true,
    }) && match arena.ty(root) {
        Ok(Type::In(_) | Type::Lift(_)) => *stage == Stage::Outer,
        Ok(Type::Universe(model)) => *stage == Stage::Inner(model),
        Ok(Type::Nat(expected)) => *stage == expected,
        _ => true,
    }))]
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
                Type::Arrow(a, b) => {
                    pending.push((b, false));
                    pending.push((a, false));
                },
                Type::Lift(inner) => pending.push((inner, false)),
                Type::In(_) | Type::Universe(_) | Type::Nat(_) => {},
            }
            continue;
        }
        let stage = match ty {
            Type::In(_) | Type::Nat(Stage::Outer) => Stage::Outer,
            Type::Universe(model) | Type::Nat(Stage::Inner(model)) => {
                permission(arena, context, model)?;
                Stage::Inner(model)
            },
            Type::Arrow(a, b) => {
                let a = *stages.get(&a).ok_or(StageError::Unbalanced)?;
                let b = *stages.get(&b).ok_or(StageError::Unbalanced)?;
                if a != b {
                    return Err(StageError::StageMismatch);
                }
                a
            },
            Type::Lift(inner) => {
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
#[spec(ensures: |ret| ret.is_err() || matches!(arena.ty(root),
    Ok(Type::Nat(Stage::Inner(_)) | Type::Arrow(..))))]
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
            Type::Nat(Stage::Inner(_)) => {},
            Type::Arrow(domain, codomain) => {
                pending.push(domain);
                pending.push(codomain);
            },
            Type::In(_) | Type::Universe(_) | Type::Nat(_) | Type::Lift(_) => {
                return Err(StageError::TypeMismatch);
            },
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
/// - witness: `stage::tests::typing_refusals_preserve_stage_boundary`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|ty|
    form(arena, hypotheses, *ty, &mut Budget(usize::MAX)).is_ok()
    && match arena.term(root) {
        Ok(Term::Variable(index)) => hypotheses.iter().rev().nth(index.0) == Some(ty),
        Ok(Term::Natural(stage, _)) => arena.ty(*ty) == Ok(Type::Nat(stage)),
        Ok(Term::Eliminate(_, target)) => *ty == target,
        _ => true,
    }))]
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
            Task::Visit(id) => {
                let term = arena.term(id)?;
                match term {
                    Term::Variable(index) => {
                        let slot = context
                            .len()
                            .checked_sub(index.0.saturating_add(1))
                            .ok_or(StageError::Unbound(index))?;
                        answers.push(*context.get(slot).ok_or(StageError::Unbound(index))?);
                    },
                    Term::Natural(stage, _) => {
                        let ty = arena.alloc_type(Type::Nat(stage))?;
                        form(arena, &context, ty, budget)?;
                        answers.push(ty);
                    },
                    Term::Code(ty) => {
                        let Stage::Inner(model) = form(arena, &context, ty, budget)?
                        else {
                            return Err(StageError::StageMismatch);
                        };
                        form_code(arena, ty, budget)?;
                        let ty = arena.alloc_type(Type::Universe(model))?;
                        answers.push(ty);
                    },
                    Term::Lambda(domain, body) => {
                        form(arena, &context, domain, budget)?;
                        context.push(domain);
                        tasks.push(Task::Finish(term));
                        tasks.push(Task::Visit(body));
                    },
                    Term::Apply(..)
                    | Term::Multiply(..)
                    | Term::Quote(_)
                    | Term::Splice(_)
                    | Term::Iterate(..)
                    | Term::Eliminate(..) => {
                        tasks.push(Task::Finish(term));
                        tasks.extend(term.children().into_iter().flatten().rev().map(Task::Visit));
                    },
                }
            },
            Task::Finish(term) => {
                let last = answers.pop().ok_or(StageError::Unbalanced)?;
                let ty = match term {
                    Term::Lambda(domain, _) => {
                        context.pop().ok_or(StageError::Unbalanced)?;
                        arena.alloc_type(Type::Arrow(domain, last))?
                    },
                    Term::Apply(..) => {
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
                    Term::Multiply(..) => {
                        let first = answers.pop().ok_or(StageError::Unbalanced)?;
                        if first != last || !matches!(arena.ty(last)?, Type::Nat(Stage::Inner(_))) {
                            return Err(StageError::TypeMismatch);
                        }
                        last
                    },
                    Term::Quote(_) => {
                        if !matches!(form(arena, &context, last, budget)?, Stage::Inner(_)) {
                            return Err(StageError::StageMismatch);
                        }
                        arena.alloc_type(Type::Lift(last))?
                    },
                    Term::Splice(_) => {
                        let Type::Lift(inner) = arena.ty(last)?
                        else {
                            return Err(StageError::TypeMismatch);
                        };
                        inner
                    },
                    Term::Iterate(..) => {
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
                    Term::Eliminate(_, target) => {
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
                    Term::Variable(_) | Term::Natural(..) | Term::Code(_) => {
                        return Err(StageError::Unbalanced);
                    },
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
/// Returns `InvalidCertificate`, `UnknownTerm`, or `Exhausted`.
///
/// # Adequacy
/// - hypothesis: L3 — changed literals and mismatched constructor arities in
///   otherwise typed certificates distinguish structural equality from producer
///   assertions and internal-worklist errors.
/// - witness: `stage::tests::certificate_tampering_is_refused`
/// - witness: `stage::tests::local_rules_and_transitive_congruence`
#[spec(ensures: |ret| ret.is_err() || left == right
    || arena.term(left).is_ok_and(|a| arena.term(right).is_ok_and(|b| a.rebuild(b.children()) == Ok(b))))]
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
        if left.rebuild(right.children()) != Ok(right) {
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
/// - witness: `stage::tests::local_rules_and_transitive_congruence`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|target|
    arena.term(*target).is_ok() && match (rule, arena.term(source)) {
        (Rule::SpliceQuote, Ok(Term::Splice(quote))) => arena.term(quote) == Ok(Term::Quote(*target)),
        (Rule::QuoteSplice, Ok(Term::Quote(splice))) => arena.term(splice) == Ok(Term::Splice(*target)),
        (Rule::IterateZero, Ok(Term::Iterate(count, initial, _))) =>
            *target == initial && matches!(arena.term(count), Ok(Term::Natural(_, Natural(0)))),
        (Rule::IterateSuccessor, Ok(Term::Iterate(count, _, step))) =>
            matches!(arena.term(count), Ok(Term::Natural(_, Natural(n))) if n > 0)
            && matches!(arena.term(*target), Ok(Term::Apply(head, _)) if head == step),
        (Rule::Eliminate, Ok(Term::Eliminate(body, _))) => *target == body,
        (Rule::Beta, Ok(Term::Apply(head, argument))) => match arena.term(head) {
            Ok(Term::Lambda(_, body)) => arena.term(body) != Ok(Term::Variable(gandr_kernel_term::stage::Index(0))) || *target == argument,
            _ => false,
        },
        _ => false,
    }))]
fn reduct(
    arena: &mut Arena,
    source: TermId,
    rule: Rule,
    budget: &mut Budget,
) -> Result<TermId, StageError>
{
    match (rule, arena.term(source)?) {
        (Rule::SpliceQuote, Term::Splice(quoted)) => {
            let Term::Quote(body) = arena.term(quoted)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            Ok(body)
        },
        (Rule::QuoteSplice, Term::Quote(spliced)) => {
            let Term::Splice(body) = arena.term(spliced)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            Ok(body)
        },
        (Rule::Beta, Term::Apply(head, argument)) => {
            let Term::Lambda(_, body) = arena.term(head)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            instantiate(arena, body, argument, budget)
        },
        (Rule::IterateZero, Term::Iterate(count, initial, _)) => {
            if !matches!(arena.term(count)?, Term::Natural(_, Natural(0))) {
                return Err(StageError::InvalidCertificate);
            }
            Ok(initial)
        },
        (Rule::IterateSuccessor, Term::Iterate(count, initial, step)) => {
            let Term::Natural(stage, Natural(count)) = arena.term(count)?
            else {
                return Err(StageError::InvalidCertificate);
            };
            let count = count.checked_sub(1).ok_or(StageError::InvalidCertificate)?;
            let predecessor = arena.alloc(Term::Natural(stage, Natural(count)))?;
            let recursive = arena.alloc(Term::Iterate(predecessor, initial, step))?;
            arena.alloc(Term::Apply(step, recursive))
        },
        (Rule::Eliminate, Term::Eliminate(body, _)) => Ok(body),
        _ => Err(StageError::InvalidCertificate),
    }
}

/// Find a replay-local equivalence representative.
///
/// # Specification
/// - requires: every parent identity is strictly less than its child.
/// - ensures: returns the connected root, no greater than the input identity.
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
/// - witness: `stage::tests::local_rules_and_transitive_congruence`
#[spec(
    requires: parents.iter().all(|(child, parent)| parent < child),
    captures: start = id,
    ensures: |ret| ret.as_ref().ok().is_none_or(|root| *root <= start && !parents.contains_key(root)),
)]
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
/// - hypothesis: L3 — altered targets, rule tags, missing derivations,
///   transitive congruence and cross-universe endpoints distinguish the
///   certificate boundaries on these finite examples.
/// - witness: `stage::tests::conversion_round_trips`
/// - witness: `stage::tests::certificate_tampering_is_refused`
/// - witness: `stage::tests::local_rules_and_transitive_congruence`
/// - witness: `stage::tests::typing_refusals_preserve_stage_boundary`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|ty|
    form(arena, context, *ty, &mut Budget(usize::MAX)).is_ok()
    && arena.term(certificate.source).is_ok() && arena.term(certificate.target).is_ok()
    && (certificate.source == certificate.target || !certificate.steps.is_empty()))) ]
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
