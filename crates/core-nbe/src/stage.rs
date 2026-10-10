//! Certificate-producing strict staging for the experimental stage universe.
//!
//! The producer evaluates meta syntax, including beneath quotations, while
//! preserving object computations. Every rebuilding and reduction contributes
//! an equation for independent kernel replay. No producer verdict admits code.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;
use gandr_kernel_term::stage::instantiate;

/// A normalization continuation, represented as first-order data.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Normalize a node's children.
    Visit(TermId),
    /// Rebuild the parent and contract its head when possible.
    Finish(TermId),
    /// Record a previously reduced source's final normal form.
    Forward(TermId, TermId),
}

/// Normalize staging syntax, recording a replayable equation per step.
///
/// # Specification
/// - ensures: on success, meta beta, quote/splice, outer numeral iteration and
///   outer identity elimination are reduced throughout the source; object beta,
///   iteration, elimination and multiplication remain residual.
/// - provides: an untrusted certificate; the kernel must form and replay it.
/// - fails: malformed syntax, index overflow, or exhausted work allowance.
/// - panics: none.
///
/// # Errors
/// Returns stage syntax, substitution, `Exhausted`, or `Unbalanced` errors.
///
/// # Adequacy
/// - hypothesis: L2/L3 — residual power at exponents zero through eight is
///   compared with integer exponentiation; tampered certificates are refused.
/// - witness: `stage::tests::power_residualizes`
/// - witness: `stage::tests::round_trips_replay`
/// - witness: `stage::tests::object_computations_remain_residual`
/// - witness: `stage::tests::function_accumulator_retains_object_redexes`
/// - witness: `stage::tests::malformed_sources_and_classifier_budgets_are_refused`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|certificate|
    certificate.source == root && arena.term(certificate.target).is_ok()
    && (certificate.source == certificate.target || !certificate.steps.is_empty())
    && certificate.steps.iter().all(|step| arena.term(step.source).is_ok() && arena.term(step.target).is_ok()))) ]
pub fn normalize(
    arena: &mut Arena,
    root: TermId,
    budget: &mut Budget,
) -> Result<Certificate, StageError>
{
    let mut tasks = Vec::from([Task::Visit(root)]);
    let mut normals = BTreeMap::new();
    let mut steps = Vec::new();
    while let Some(task) = tasks.pop() {
        budget.spend()?;
        match task {
            | Task::Visit(id) => {
                if normals.contains_key(&id) {
                    continue;
                }
                let term = arena.term(id)?;
                tasks.push(Task::Finish(id));
                tasks.extend(term.children().into_iter().flatten().rev().map(Task::Visit));
            },
            | Task::Finish(id) => {
                let term = arena.term(id)?;
                let mut children = term.children();
                for child in children.iter_mut().flatten() {
                    *child = *normals.get(child).ok_or(StageError::Unbalanced)?;
                }
                let rebuilt = term.rebuild(children)?;
                let current = if rebuilt == term {
                    id
                }
                else {
                    let target = arena.alloc(rebuilt)?;
                    steps.push(Step {
                        source: id,
                        target,
                        rule: Rule::Congruence,
                    });
                    target
                };
                match contract(arena, current, budget)? {
                    | Reduction::Normal => {
                        normals.insert(id, current);
                    },
                    | Reduction::Step(target, rule) => {
                        steps.push(Step {
                            source: current,
                            target,
                            rule,
                        });
                        tasks.push(Task::Forward(id, target));
                        tasks.push(Task::Visit(target));
                    },
                }
            },
            | Task::Forward(source, target) => {
                let normal = *normals.get(&target).ok_or(StageError::Unbalanced)?;
                normals.insert(source, normal);
            },
        }
    }
    let target = *normals.get(&root).ok_or(StageError::Unbalanced)?;
    Ok(Certificate {
        source: root,
        target,
        steps,
    })
}

/// A producer's head-reduction decision.
#[derive(Clone, Copy, Debug)]
enum Reduction
{
    /// The head is normal.
    Normal,
    /// Proposed reduct and its rule.
    Step(TermId, Rule),
}

/// Select a head conversion and construct its proposed reduct.
///
/// # Specification
/// - ensures: only meta beta, outer natural iteration, outer identity
///   elimination and the two quote/splice round trips contract.
/// - fails: syntax lookup, substitution or work errors.
/// - panics: none.
///
/// # Errors
/// Returns a stage syntax, substitution, or budget error.
///
/// # Adequacy
/// - hypothesis: L2/L3 — exponentiation and open round trips distinguish
///   reduction selection and its reconstructed result.
/// - witness: `stage::tests::power_residualizes`
/// - witness: `stage::tests::round_trips_replay`
/// - witness: `stage::tests::object_computations_remain_residual`
/// - witness: `stage::tests::malformed_sources_and_classifier_budgets_are_refused`
#[spec(ensures: |ret| match ret {
    Ok(Reduction::Step(target, rule)) => arena.term(target).is_ok()
        && match (rule, arena.term(id)) {
            (Rule::Beta, Ok(Term::Apply(head, _))) => match arena.term(head) {
                Ok(Term::Lambda(domain, _)) => classifier_stage(arena, domain, &mut Budget(usize::MAX)) == Ok(Stage::Outer),
                _ => false,
            },
            (Rule::SpliceQuote, Ok(Term::Splice(quote))) => arena.term(quote) == Ok(Term::Quote(target)),
            (Rule::QuoteSplice, Ok(Term::Quote(splice))) => arena.term(splice) == Ok(Term::Splice(target)),
            (Rule::IterateZero, Ok(Term::Iterate(count, initial, _))) =>
                target == initial && arena.term(count) == Ok(Term::Natural(Stage::Outer, Natural(0))),
            (Rule::IterateSuccessor, Ok(Term::Iterate(count, _, step))) =>
                matches!(arena.term(count), Ok(Term::Natural(Stage::Outer, Natural(n))) if n > 0)
                && matches!(arena.term(target), Ok(Term::Apply(head, _)) if head == step),
            (Rule::Eliminate, Ok(Term::Eliminate(body, ty))) => target == body
                && classifier_stage(arena, ty, &mut Budget(usize::MAX)) == Ok(Stage::Outer),
            _ => false,
        },
    _ => true,
})]
fn contract(
    arena: &mut Arena,
    id: TermId,
    budget: &mut Budget,
) -> Result<Reduction, StageError>
{
    let proposal = match arena.term(id)? {
        | Term::Apply(head, argument) => match arena.term(head)? {
            | Term::Lambda(domain, body) => {
                let stage = classifier_stage(arena, domain, budget)?;
                if stage != Stage::Outer {
                    return Ok(Reduction::Normal);
                }
                let target = instantiate(arena, body, argument, budget)?;
                Reduction::Step(target, Rule::Beta)
            },
            | _ => Reduction::Normal,
        },
        | Term::Splice(quoted) => match arena.term(quoted)? {
            | Term::Quote(body) => Reduction::Step(body, Rule::SpliceQuote),
            | _ => Reduction::Normal,
        },
        | Term::Quote(spliced) => match arena.term(spliced)? {
            | Term::Splice(body) => Reduction::Step(body, Rule::QuoteSplice),
            | _ => Reduction::Normal,
        },
        | Term::Iterate(count, initial, step) => match arena.term(count)? {
            | Term::Natural(Stage::Outer, Natural(0)) => {
                Reduction::Step(initial, Rule::IterateZero)
            },
            | Term::Natural(Stage::Outer, Natural(count)) => {
                let count = count.checked_sub(1).ok_or(StageError::Overflow)?;
                let predecessor = arena.alloc(Term::Natural(Stage::Outer, Natural(count)))?;
                let remaining = arena.alloc(Term::Iterate(predecessor, initial, step))?;
                let target = arena.alloc(Term::Apply(step, remaining))?;
                Reduction::Step(target, Rule::IterateSuccessor)
            },
            | _ => Reduction::Normal,
        },
        | Term::Eliminate(body, target) => {
            let stage = classifier_stage(arena, target, budget)?;
            if stage != Stage::Outer {
                return Ok(Reduction::Normal);
            }
            Reduction::Step(body, Rule::Eliminate)
        },
        | _ => Reduction::Normal,
    };
    Ok(proposal)
}

/// Read a classifier's stage for reduction selection, without forming it.
///
/// # Specification
/// - requires: the classifier is well formed; replay checks this independently.
/// - ensures: follows arrow domains to distinguish outer from indexed inner
///   classifiers; a lift is outer regardless of its inner payload.
/// - fails: unknown classifier or exhausted work allowance.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownType` or `Exhausted`.
///
/// # Adequacy
/// - hypothesis: L3 — inner and outer naturals, functions and lifts distinguish
///   stage selection without relying on quotation nesting.
/// - witness: `stage::tests::object_computations_remain_residual`
/// - witness: `stage::tests::malformed_sources_and_classifier_budgets_are_refused`
#[spec(captures: source = ty, ensures: |ret| ret.as_ref().ok().is_none_or(|stage|
    match arena.ty(source) {
        Ok(Type::In(_) | Type::Lift(_)) => *stage == Stage::Outer,
        Ok(Type::Universe(model)) => *stage == Stage::Inner(model),
        Ok(Type::Nat(expected)) => *stage == expected,
        _ => true,
    }))]
fn classifier_stage(
    arena: &Arena,
    mut ty: TypeId,
    budget: &mut Budget,
) -> Result<Stage, StageError>
{
    loop {
        budget.spend()?;
        match arena.ty(ty)? {
            | Type::In(_) | Type::Lift(_) => return Ok(Stage::Outer),
            | Type::Universe(model) => return Ok(Stage::Inner(model)),
            | Type::Nat(stage) => return Ok(stage),
            | Type::Arrow(domain, _) => ty = domain,
        }
    }
}

/// Build `pow : Nat_outer -> Lift Nat_inner -> Lift Nat_inner`.
///
/// The program is `λn. λx. iter n <1> (λp.<~x * ~p>)`. Quoted object
/// input is threaded at the meta level; the iterator carries quoted naturals.
/// Specialization `<λx. ~(pow n <x>)>` creates no object redex.
///
/// # Specification
/// - ensures: constructs one exponent-independent program at the indexed model;
///   specializing a numeral and quoted input leaves that many multiplications.
/// - fails: syntax allocation errors.
/// - panics: none.
///
/// # Errors
/// Propagates stage arena errors.
///
/// # Adequacy
/// - hypothesis: L2 — varying both exponent and input separates a real staged
///   iterator from a precomputed answer or fixed residual.
/// - witness: `stage::tests::power_residualizes`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|root| match arena.term(*root) {
    Ok(Term::Lambda(outer, body)) => arena.ty(outer) == Ok(Type::Nat(Stage::Outer))
        && match arena.term(body) {
            Ok(Term::Lambda(lifted, _)) => match arena.ty(lifted) {
                Ok(Type::Lift(inner)) => arena.ty(inner) == Ok(Type::Nat(Stage::Inner(model))),
                _ => false,
            },
            _ => false,
        },
    _ => false,
}))]
pub fn power(
    arena: &mut Arena,
    model: Model,
) -> Result<TermId, StageError>
{
    let outer = arena.alloc_type(Type::Nat(Stage::Outer))?;
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model)))?;
    let lifted = arena.alloc_type(Type::Lift(inner))?;
    let one = arena.alloc(Term::Natural(Stage::Inner(model), Natural(1)))?;
    let initial = arena.alloc(Term::Quote(one))?;
    let input = arena.alloc(Term::Variable(Index(1)))?;
    let input = arena.alloc(Term::Splice(input))?;
    let previous = arena.alloc(Term::Variable(Index(0)))?;
    let previous = arena.alloc(Term::Splice(previous))?;
    let product = arena.alloc(Term::Multiply(input, previous))?;
    let body = arena.alloc(Term::Quote(product))?;
    let step = arena.alloc(Term::Lambda(lifted, body))?;
    let exponent = arena.alloc(Term::Variable(Index(1)))?;
    let body = arena.alloc(Term::Iterate(exponent, initial, step))?;
    let body = arena.alloc(Term::Lambda(lifted, body))?;
    arena.alloc(Term::Lambda(outer, body))
}

#[cfg(test)]
mod tests;
