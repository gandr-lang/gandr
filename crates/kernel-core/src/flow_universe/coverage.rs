//! Symbolic container patterns and their leaf-natural forward obligations.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Allowance;
use super::FlowError;
use super::Image;
use super::PatternPosition;
use crate::check::check_closed_value;
use crate::encoding::ContentTable;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_value;

/// Validate a quoted code's complete first-order graph.
///
/// # Specification
/// - ensures: the returned type contains only Unit, Base, Sum and Product.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `Arena` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — non-code and higher-order endpoints refuse.
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
pub(super) fn code(
    arena: &TermArena,
    code: ValueId,
    allowance: &mut Allowance,
) -> Result<ValueTypeId, FlowError>
{
    let Some(&Value::Quote(root)) = arena.value(code)
    else {
        return Err(FlowError::UnsupportedCode(code));
    };
    let mut pending = Vec::from([root]);
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        allowance.charge()?;
        if !seen.insert(id) {
            continue;
        }
        match arena.value_type(id).ok_or(FlowError::Arena)? {
            | &ValueType::Base(_) | &ValueType::Unit => {},
            | &ValueType::Sum(left, right) | &ValueType::Product(left, right) => {
                pending.push(right);
                pending.push(left);
            },
            | _ => return Err(FlowError::UnsupportedType(id)),
        }
    }
    Ok(root)
}

/// Check a closed forward translator in a fresh checker session.
///
/// # Specification
/// - requires: endpoints have passed closed-code validation.
/// - ensures: `function : U (source -> F target)` in the empty context.
/// - fails: `Typing` with the ordinary kernel diagnostic.
/// - panics: none.
///
/// # Errors
/// `FlowError::Typing`.
///
/// # Adequacy
/// - hypothesis: L3 — a nonfunction cannot certify a forward map.
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
pub(super) fn translator(
    arena: &mut TermArena,
    function: ValueId,
    source: ValueTypeId,
    target: ValueTypeId,
) -> Result<(), FlowError>
{
    let returned = arena.comp_type_returner(target);
    let arrow = arena.comp_type_arrow(source, returned);
    let expected = arena.value_type_thunk(arrow);
    check_closed_value(arena, function, expected)
        .map_err(|error| FlowError::Typing(Box::new(error)))
}

/// One canonical source shape, with independent typed leaves.
struct Pattern
{
    /// Constructor pattern with distinct rigid variables.
    value: ValueId,
    /// Leaf types in left-to-right order; the last is de Bruijn zero.
    leaves: Vec<BaseType>,
}

/// Postorder pattern enumeration work.
enum Cover
{
    /// Visit one closed type.
    Visit(ValueTypeId),
    /// Join summand shapes.
    Sum,
    /// Take the product of component shapes, renaming leaves apart.
    Product,
}

/// Enumerate all constructor shapes with distinct variables at Base leaves.
///
/// # Specification
/// - requires: `root` is a validated closed first-order type.
/// - ensures: left-first sum order and lexicographic product order; leaves are
///   never sampled and equal-typed positions remain distinct.
/// - fails: `Arena`, `UnsupportedType` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — repeated Base positions and both sum branches matter.
/// - witness: `flow_universe::tests::one_way_classes_preserve_leaves`
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
fn patterns(
    arena: &mut TermArena,
    root: ValueTypeId,
    allowance: &mut Allowance,
) -> Result<Vec<Pattern>, FlowError>
{
    let mut pending = Vec::from([Cover::Visit(root)]);
    let mut results = Vec::<Vec<Pattern>>::new();
    let mut table = ContentTable::new();
    while let Some(task) = pending.pop() {
        allowance.charge()?;
        match task {
            | Cover::Visit(id) => match arena.value_type(id).ok_or(FlowError::Arena)? {
                | &ValueType::Unit => results.push(Vec::from([Pattern {
                    value: arena.value_unit(),
                    leaves: Vec::new(),
                }])),
                | &ValueType::Base(base) => results.push(Vec::from([Pattern {
                    value: arena.value_variable(DeBruijnIndex::from(0_u32)),
                    leaves: Vec::from([base]),
                }])),
                | &ValueType::Sum(left, right) => {
                    pending.push(Cover::Sum);
                    pending.push(Cover::Visit(right));
                    pending.push(Cover::Visit(left));
                },
                | &ValueType::Product(left, right) => {
                    pending.push(Cover::Product);
                    pending.push(Cover::Visit(right));
                    pending.push(Cover::Visit(left));
                },
                | _ => return Err(FlowError::UnsupportedType(id)),
            },
            | Cover::Sum => {
                let right = results.pop().ok_or(FlowError::Arena)?;
                let left = results.pop().ok_or(FlowError::Arena)?;
                let mut joined = Vec::with_capacity(left.len().saturating_add(right.len()));
                for (side, branch) in [(Side::Left, left), (Side::Right, right)] {
                    for pattern in branch {
                        allowance.charge()?;
                        joined.push(Pattern {
                            value: arena.value_injection(side, pattern.value),
                            leaves: pattern.leaves,
                        });
                    }
                }
                results.push(joined);
            },
            | Cover::Product => {
                let right = results.pop().ok_or(FlowError::Arena)?;
                let left = results.pop().ok_or(FlowError::Arena)?;
                let mut joined = Vec::new();
                for first in left {
                    for second in &right {
                        allowance.charge()?;
                        let depth = u32::try_from(second.leaves.len())
                            .map_err(|_overflow| FlowError::Budget)?;
                        let value = shift_value(
                            arena,
                            &mut table,
                            &mut NullMemo,
                            first.value,
                            BinderDepth::default(),
                            BinderDepth::from(depth),
                        );
                        let mut leaves = Vec::with_capacity(
                            first.leaves.len().saturating_add(second.leaves.len()),
                        );
                        leaves.extend_from_slice(&first.leaves);
                        leaves.extend_from_slice(&second.leaves);
                        joined.push(Pattern {
                            value: arena.value_pair(value, second.value),
                            leaves,
                        });
                    }
                }
                results.push(joined);
            },
        }
    }
    results.pop().ok_or(FlowError::Arena)
}

/// Validate a container-shaped target using only correctly typed source leaves.
///
/// # Specification
/// - ensures: every target Base position selects a same-typed source position;
///   all other nodes are the canonical constructor of the target code.
/// - fails: `NonNatural` for literals, wrong shapes, fresh or mistyped leaves;
///   `Arena` or `Budget` for unresolved types or exhausted traversal.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — literals cannot hide beneath sums or products, and typed
///   leaf selection rejects fresh variables and differently typed leaves.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
fn natural(
    arena: &TermArena,
    output: ValueId,
    target: ValueTypeId,
    leaves: &[BaseType],
    allowance: &mut Allowance,
) -> Result<(), FlowError>
{
    let mut pending = Vec::from([(output, target)]);
    while let Some((value, ty)) = pending.pop() {
        allowance.charge()?;
        let ty = arena.value_type(ty).ok_or(FlowError::Arena)?;
        match (arena.value(value), ty) {
            | (Some(&Value::Unit), &ValueType::Unit) => {},
            | (Some(&Value::Variable(index)), &ValueType::Base(base)) => {
                let index =
                    usize::try_from(u32::from(index)).map_err(|_overflow| FlowError::Budget)?;
                let source = leaves
                    .len()
                    .checked_sub(index.saturating_add(1))
                    .and_then(|position| leaves.get(position));
                if source != Some(&base) {
                    return Err(FlowError::NonNatural(value));
                }
            },
            | (Some(&Value::Pair(left, right)), &ValueType::Product(first, second)) => {
                pending.push((right, second));
                pending.push((left, first));
            },
            | (Some(&Value::Injection(side, value)), &ValueType::Sum(left, right)) => {
                pending.push((value, match side {
                    | Side::Left => left,
                    | Side::Right => right,
                }));
            },
            | _ => return Err(FlowError::NonNatural(value)),
        }
    }
    Ok(())
}

/// Replay the translator against exhaustive, validated symbolic images.
///
/// # Specification
/// - requires: endpoints and translator have been checked.
/// - ensures: each source shape maps to a leaf-natural target shape by ordinary
///   kernel replay; the kernel chooses the source, action and positive claim.
/// - fails: `Coverage`, `NonNatural`, `ForwardReplay`, or construction errors.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — omitted constructors, constant Base maps and false traces
///   cannot certify a forward action.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
pub(super) fn forward(
    arena: &mut TermArena,
    source: ValueTypeId,
    target: ValueTypeId,
    function: ValueId,
    images: &[Image],
    budget: ReplayBudget,
) -> Result<(), FlowError>
{
    let mut allowance = Allowance(u64::from(budget));
    let patterns = patterns(arena, source, &mut allowance)?;
    if images.len() != patterns.len() {
        return Err(FlowError::Coverage);
    }
    let unfoldings = Unfoldings::new(Vec::new());
    for (position, (pattern, image)) in patterns.into_iter().zip(images).enumerate() {
        natural(arena, image.output, target, &pattern.leaves, &mut allowance)?;
        let force = arena.computation_force(function);
        let application = arena.computation_application(force, pattern.value);
        let expected = arena.computation_return(image.output);
        let verdict = crate::replay::replay(
            arena,
            &unfoldings,
            ReplaySides::Computations(application, expected),
            EngineClaim::Convertible,
            image.dialogue.0.iter().copied(),
            budget,
        );
        if verdict != KernelVerdict::Convertible {
            return Err(FlowError::ForwardReplay {
                pattern: PatternPosition(position),
                verdict,
            });
        }
    }
    Ok(())
}
