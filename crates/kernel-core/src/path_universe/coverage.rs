//! Closed-code coverage and the iterative shadow of transport's beta rules.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Allowance;
use super::Direction;
use super::PathError;
use super::PatternPosition;
use crate::encoding::ContentTable;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_value;

/// Inspect quoted first-order shapes or finite guarded session graphs.
///
/// # Specification
/// - requires: the code root belongs to `arena`.
/// - ensures: outer formers are Base, Unit, Product, Sum or Session; session
///   graph structure and guards check. Native formation separately checks
///   session payload codes in an empty term context.
/// - provides: code-shape inspection, never a checking verdict.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `Session`, `Arena` or
///   `Budget`.
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
            | &ValueType::Session {
                ref graph,
                payloads,
            } => {
                crate::session::validate_graph(arena, graph, payloads)
                    .map_err(PathError::Session)?;
                // Ordinary formation checks payload codes in an empty
                // telescope.
            },
            | &ValueType::Sum(first, second) | &ValueType::Product(first, second) => {
                pending.push(second);
                pending.push(first);
            },
            | _ => return Err(PathError::UnsupportedType(id)),
        }
    }
    Ok(root)
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
pub fn round_trip(
    arena: &mut TermArena,
    source: ValueTypeId,
    forward: ValueId,
    backward: ValueId,
    dialogues: &[Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>],
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
            dialogue.iter().copied().map(super::anchor),
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
