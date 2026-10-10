//! Certificate-producing normalization for the experimental stage universe.
//!
//! The producer normalizes object syntax under quotations but leaves object
//! multiplication residual. Every rebuilding and reduction contributes an
//! equation for independent kernel replay. No producer verdict admits code.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

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
/// - ensures: on success, the target contains no beta, quote/splice, numeral
///   iterator or identity-elimination redex reachable in the source.
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
#[inline]
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
/// - ensures: object multiplication remains residual; static beta and natural
///   iteration compute, and both quote/splice round trips cancel.
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
fn contract(
    arena: &mut Arena,
    id: TermId,
    budget: &mut Budget,
) -> Result<Reduction, StageError>
{
    let proposal = match arena.term(id)? {
        | Term::Apply(head, argument) => match arena.term(head)? {
            | Term::Lambda(_, body) => {
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
            | Term::Natural(_, Natural(0)) => Reduction::Step(initial, Rule::IterateZero),
            | Term::Natural(stage, Natural(count)) => {
                let count = count.checked_sub(1).ok_or(StageError::Overflow)?;
                let predecessor = arena.alloc(Term::Natural(stage, Natural(count)))?;
                let remaining = arena.alloc(Term::Iterate(predecessor, initial, step))?;
                let target = arena.alloc(Term::Apply(step, remaining))?;
                Reduction::Step(target, Rule::IterateSuccessor)
            },
            | _ => Reduction::Normal,
        },
        | Term::Eliminate(body, _) => Reduction::Step(body, Rule::Eliminate),
        | _ => Reduction::Normal,
    };
    Ok(proposal)
}

/// Build `pow : Nat_outer -> Lift (Nat_inner -> Nat_inner)`.
///
/// The program is `λn. iter n <λx.1> (λp.<λx. x * (~p) x>)`.
/// The iterator and higher-order accumulator are meta-level terms, not a
/// host-language exponent loop or a special power reduction rule.
///
/// # Specification
/// - ensures: constructs one exponent-independent program at the indexed model;
///   applying a numeral leaves that many object multiplications.
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
pub fn power(
    arena: &mut Arena,
    model: Model,
) -> Result<TermId, StageError>
{
    let outer = arena.alloc_type(Type::Nat(Stage::Outer))?;
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model)))?;
    let function = arena.alloc_type(Type::Arrow(inner, inner))?;
    let lifted = arena.alloc_type(Type::Lift(function))?;
    let one = arena.alloc(Term::Natural(Stage::Inner(model), Natural(1)))?;
    let initial = arena.alloc(Term::Lambda(inner, one))?;
    let initial = arena.alloc(Term::Quote(initial))?;
    let input = arena.alloc(Term::Variable(Index(0)))?;
    let previous = arena.alloc(Term::Variable(Index(1)))?;
    let previous = arena.alloc(Term::Splice(previous))?;
    let applied = arena.alloc(Term::Apply(previous, input))?;
    let product = arena.alloc(Term::Multiply(input, applied))?;
    let body = arena.alloc(Term::Lambda(inner, product))?;
    let body = arena.alloc(Term::Quote(body))?;
    let step = arena.alloc(Term::Lambda(lifted, body))?;
    let exponent = arena.alloc(Term::Variable(Index(0)))?;
    let body = arena.alloc(Term::Iterate(exponent, initial, step))?;
    arena.alloc(Term::Lambda(outer, body))
}

#[cfg(test)]
mod tests;
