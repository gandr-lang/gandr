//! Closed-code coverage and the iterative shadow of transport's beta rules.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Allowance;
use super::Dialogue;
use super::Direction;
use super::PathError;
use super::Paths;
use super::PatternPosition;
use super::Reduct;
use super::Transport;
use crate::check::check_closed_value;
use crate::encoding::ContentTable;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_value;

/// Read a quoted code and validate its entire first-order type graph.
///
/// # Specification
/// - requires: the code root belongs to `arena`.
/// - ensures: every reachable former is Base, Unit, Product or Sum.
/// - provides: closed level-zero decoding without a type-level evaluator.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `Arena` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — Bool and product codes admit; thunk codes refuse.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
pub(super) fn code(
    arena: &TermArena,
    code: ValueId,
    allowance: &mut Allowance,
) -> Result<ValueTypeId, PathError>
{
    let Some(&Value::Quote(root)) = arena.value(code)
    else {
        return Err(PathError::UnsupportedCode(code));
    };
    let mut pending = Vec::from([root]);
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        allowance.charge()?;
        if !seen.insert(id) {
            continue;
        }
        let node = arena.value_type(id).ok_or(PathError::Arena)?;
        match node {
            | &ValueType::Unit | &ValueType::Base(_) => {},
            | &ValueType::Sum(first, second) | &ValueType::Product(first, second) => {
                pending.push(second);
                pending.push(first);
            },
            | _ => return Err(PathError::UnsupportedType(id)),
        }
    }
    Ok(root)
}

/// Check a closed CBPV translator at its exact source and target.
///
/// # Specification
/// - requires: the endpoint types have passed `code`.
/// - ensures: `function : U (source -> F target)` in the empty context.
/// - provides: typing independently of any round-trip trace.
/// - fails: `PathError::Typing` with the kernel's original diagnostic.
/// - panics: none.
///
/// # Errors
/// `PathError::Typing`.
///
/// # Adequacy
/// - hypothesis: L3 — a unit value cannot masquerade as a translator.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
pub(super) fn translator(
    arena: &mut TermArena,
    function: ValueId,
    source: ValueTypeId,
    target: ValueTypeId,
) -> Result<(), PathError>
{
    let result = arena.comp_type_returner(target);
    let arrow = arena.comp_type_arrow(source, result);
    let expected = arena.value_type_thunk(arrow);
    check_closed_value(arena, function, expected)
        .map_err(|error| PathError::Typing(Box::new(error)))
}

/// A canonical constructor pattern with fresh rigid variables at base leaves.
#[derive(Clone, Copy)]
struct Pattern
{
    /// The symbolic value; base variables occur exactly once each.
    value: ValueId,
    /// The number of independent base variables bound outside this pattern.
    binders: BinderDepth,
}

/// A postorder coverage instruction.
#[derive(Clone, Copy)]
enum Cover
{
    /// Expand one type's constructor patterns.
    Visit(ValueTypeId),
    /// Join summand patterns with their distinct injection tags.
    Sum,
    /// Form every pair of component patterns, renaming base variables apart.
    Product,
}

/// Enumerate constructor coverage without enumerating base inhabitants.
///
/// # Specification
/// - requires: `root` is a validated closed first-order type.
/// - ensures: exactly one pattern per constructor choice; every base position
///   is a distinct rigid variable, including repeated base types in products.
/// - provides: a symbolic universal boundary for a round-trip dialogue.
/// - fails: `Arena`, `UnsupportedType` or `Budget`.
/// - panics: none.
/// - intension: sums are left-first and products are lexicographic.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — both Bool branches are required; a literal sample cannot
///   establish a Base round trip, while a generic product identity is admitted.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
fn patterns(
    arena: &mut TermArena,
    root: ValueTypeId,
    allowance: &mut Allowance,
) -> Result<Vec<Pattern>, PathError>
{
    let mut pending = Vec::from([Cover::Visit(root)]);
    let mut results = Vec::<Vec<Pattern>>::new();
    let mut table = ContentTable::new();
    while let Some(task) = pending.pop() {
        allowance.charge()?;
        match task {
            | Cover::Visit(id) => {
                let node = arena.value_type(id).ok_or(PathError::Arena)?;
                match node {
                    | &ValueType::Unit => results.push(Vec::from([Pattern {
                        value: arena.value_unit(),
                        binders: BinderDepth::default(),
                    }])),
                    | &ValueType::Base(_) => results.push(Vec::from([Pattern {
                        value: arena.value_variable(DeBruijnIndex::from(0_u32)),
                        binders: BinderDepth::from(1_u32),
                    }])),
                    | &ValueType::Sum(first, second) => {
                        pending.push(Cover::Sum);
                        pending.push(Cover::Visit(second));
                        pending.push(Cover::Visit(first));
                    },
                    | &ValueType::Product(first, second) => {
                        pending.push(Cover::Product);
                        pending.push(Cover::Visit(second));
                        pending.push(Cover::Visit(first));
                    },
                    | _ => return Err(PathError::UnsupportedType(id)),
                }
            },
            | Cover::Sum => {
                let second = results.pop().ok_or(PathError::Arena)?;
                let first = results.pop().ok_or(PathError::Arena)?;
                let mut joined = Vec::with_capacity(first.len().saturating_add(second.len()));
                for (side, branch) in [(Side::Left, first), (Side::Right, second)] {
                    for pattern in branch {
                        allowance.charge()?;
                        joined.push(Pattern {
                            value: arena.value_injection(side, pattern.value),
                            binders: pattern.binders,
                        });
                    }
                }
                results.push(joined);
            },
            | Cover::Product => {
                let second = results.pop().ok_or(PathError::Arena)?;
                let first = results.pop().ok_or(PathError::Arena)?;
                let mut joined = Vec::new();
                for left in first {
                    for right in &second {
                        allowance.charge()?;
                        let binders = u32::from(left.binders)
                            .checked_add(u32::from(right.binders))
                            .ok_or(PathError::Budget)?;
                        let value = shift_value(
                            arena,
                            &mut table,
                            &mut NullMemo,
                            left.value,
                            BinderDepth::default(),
                            right.binders,
                        );
                        joined.push(Pattern {
                            value: arena.value_pair(value, right.value),
                            binders: BinderDepth::from(binders),
                        });
                    }
                }
                results.push(joined);
            },
        }
    }
    results.pop().ok_or(PathError::Arena)
}

/// Construct and replay every component of one universal round-trip claim.
///
/// # Specification
/// - requires: the translators are closed and checked at opposite arrows.
/// - ensures: every code-generated pattern replays `Convertible`; no supplied
///   dialogue chooses its own boundary, suppresses a pattern, or adds one.
/// - provides: formation evidence derived by the existing kernel replay.
/// - fails: `Coverage` on dialogue cardinality, `RoundTrip` on failed replay,
///   or the code-pattern construction error.
/// - panics: none.
///
/// # Errors
/// `Coverage`, `RoundTrip`, `Arena`, `UnsupportedType`, or `Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — constant true fails on the false branch; missing,
///   additional and forged dialogues cannot make formation succeed.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
pub(super) fn round_trip(
    arena: &mut TermArena,
    source: ValueTypeId,
    forward: ValueId,
    backward: ValueId,
    dialogues: &[Dialogue],
    direction: Direction,
    budget: ReplayBudget,
) -> Result<(), PathError>
{
    let patterns = patterns(arena, source, &mut Allowance(u64::from(budget)))?;
    if patterns.len() != dialogues.len() {
        return Err(PathError::Coverage(direction));
    }
    let unfoldings = Unfoldings::new(Vec::new());
    for (position, (pattern, dialogue)) in patterns.into_iter().zip(dialogues).enumerate() {
        let first = arena.computation_force(forward);
        let first = arena.computation_application(first, pattern.value);
        let second = arena.computation_force(backward);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let second = arena.computation_application(second, variable);
        let composite = arena.computation_bind(first, second);
        let identity = arena.computation_return(pattern.value);
        let verdict = crate::replay::replay(
            arena,
            &unfoldings,
            ReplaySides::Computations(composite, identity),
            EngineClaim::Convertible,
            dialogue.0.iter().copied(),
            budget,
        );
        if verdict != KernelVerdict::Convertible {
            return Err(PathError::RoundTrip {
                direction,
                pattern: PatternPosition(position),
                verdict,
            });
        }
    }
    Ok(())
}

/// A transport-expansion continuation.
#[derive(Clone, Copy)]
enum Lower
{
    /// Fire a path's beta rule.
    Transport(Transport),
    /// Pair two component computations using ordinary CBPV sequencing.
    Pair,
}

/// Expand canonical transport into ordinary CBPV computation syntax.
///
/// # Specification
/// - requires: the path is formed and its input is a closed typed value.
/// - ensures: equivalence uses `force f v`, reflexivity uses `return v`, and
///   products sequence the left and right transports and return their pair.
/// - provides: the kernel's reduction, with no producer-supplied reduct.
/// - fails: beta's path/shape errors, `Arena`, or `Budget`.
/// - panics: none.
///
/// # Errors
/// `UnknownPath`, `ExpectedPair`, `Arena`, or `Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — negation and product negation distinguish both forward
///   action and pair order; reflexivity preserves its input exactly.
/// - witness: `path_universe::tests::transport_computes`
/// - witness: `path_universe::tests::it_computes_through_a_former`
/// - witness: `path_universe::tests::refl_collapses`
pub(super) fn lower(
    arena: &mut TermArena,
    paths: &Paths,
    term: Transport,
    budget: ReplayBudget,
) -> Result<ComputationId, PathError>
{
    let mut pending = Vec::from([Lower::Transport(term)]);
    let mut results = Vec::new();
    let mut allowance = Allowance(u64::from(budget));
    while let Some(task) = pending.pop() {
        allowance.charge()?;
        match task {
            | Lower::Transport(term) => {
                let reduct = super::beta(arena, paths, term)?;
                match reduct {
                    | Reduct::Return(value) => results.push(arena.computation_return(value)),
                    | Reduct::Apply(function, value) => {
                        let force = arena.computation_force(function);
                        results.push(arena.computation_application(force, value));
                    },
                    | Reduct::Pair(first, second) => {
                        pending.push(Lower::Pair);
                        pending.push(Lower::Transport(second));
                        pending.push(Lower::Transport(first));
                    },
                }
            },
            | Lower::Pair => {
                let second = results.pop().ok_or(PathError::Arena)?;
                let first = results.pop().ok_or(PathError::Arena)?;
                let left = arena.value_variable(DeBruijnIndex::from(1_u32));
                let right = arena.value_variable(DeBruijnIndex::from(0_u32));
                let pair = arena.value_pair(left, right);
                let result = arena.computation_return(pair);
                // Both component computations are closed: placing the second
                // beneath the first result's binder needs no weakening.
                let result = arena.computation_bind(second, result);
                results.push(arena.computation_bind(first, result));
            },
        }
    }
    results.pop().ok_or(PathError::Arena)
}
