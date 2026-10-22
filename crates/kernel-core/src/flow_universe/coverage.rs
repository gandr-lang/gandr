//! Symbolic container patterns and their leaf-natural forward obligations.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Dialogue;
use gandr_kernel_term::Summand;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Allowance;
use super::FlowError;
use super::FlowType;
use super::PatternPosition;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::encoding::ContentTable;
use crate::path_universe::anchor;
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
/// - ensures: the returned type contains only Base, Product (the unit among
///   them), Sum of at least one summand and List; the empty sum is refused, as
///   the retired empty type was.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `Arena` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — non-code and higher-order endpoints refuse.
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(root) => allowance.0 < before && matches!(arena.value(code), Some(&Value::Quote(ty)) if root == ty),
        Err(FlowError::UnsupportedCode(named)) => named == code && !matches!(arena.value(code), Some(&Value::Quote(_))),
        Err(FlowError::UnsupportedType(ty)) => arena.value_type(ty).is_some_and(|node| !matches!(node, &ValueType::Base(_) | &ValueType::Product(..) | &ValueType::List(_)) && node.summands().is_none_or(<[_]>::is_empty)),
        Err(FlowError::Budget) => allowance.0 == 0,
        Err(FlowError::Arena) => true,
        Err(_) => false,
    },
)]
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
    first_order(arena, root, allowance)?;
    Ok(root)
}

/// Validate a type's complete first-order graph.
///
/// # Specification
/// - ensures: every node reachable from `root` is Base, Product, List or a Sum
///   of at least one summand; each visit charges `allowance` once.
/// - fails: `UnsupportedType` naming the first other node, `Arena` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a function code refuses at a forward endpoint and beneath
///   a function code's argument; Bool, Unit and a list of Bool pass.
/// - witness: `flow_universe::tests::function::constant_map_refusal_holds_at_a_thunk_code`
/// - witness: `flow_universe::tests::stay_and_forward_admit_and_ride`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(()) => allowance.0 < before,
        Err(FlowError::UnsupportedType(ty)) => arena.value_type(ty).is_some_and(|node| !matches!(node, &ValueType::Base(_) | &ValueType::Product(..) | &ValueType::List(_)) && node.summands().is_none_or(<[_]>::is_empty)),
        Err(FlowError::Budget) => allowance.0 == 0,
        Err(FlowError::Arena) => true,
        Err(_) => false,
    },
)]
fn first_order(
    arena: &TermArena,
    root: ValueTypeId,
    allowance: &mut Allowance,
) -> Result<(), FlowError>
{
    let mut pending = Vec::from([root]);
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        allowance.charge()?;
        if !seen.insert(id) {
            continue;
        }
        match arena.value_type(id).ok_or(FlowError::Arena)? {
            &ValueType::Base(_) => {},
            &ValueType::Sum(ref parts) if parts.is_empty() => {
                return Err(FlowError::UnsupportedType(id));
            },
            &ValueType::Sum(ref parts) | &ValueType::Product(ref parts) => {
                pending.extend(parts.iter().rev().copied());
            },
            &ValueType::List(element) => pending.push(element),
            &ValueType::Data { .. }
            | &ValueType::Record(_)
            | &ValueType::Session { .. }
            | &ValueType::PathUniverse(..)
            | &ValueType::FlowUniverse(..)
            | &ValueType::Path { .. }
            | &ValueType::Flow { .. }
            | &ValueType::Bridge { .. }
            | &ValueType::Sigma { .. }
            | &ValueType::Thunk(_)
            | &ValueType::Universe { .. }
            | &ValueType::Lift { .. }
            | &ValueType::Element { .. }
            | &ValueType::Abstract(_)
            | &ValueType::StaticPi { .. }
            | &ValueType::Staged { .. } => return Err(FlowError::UnsupportedType(id)),
        }
    }
    Ok(())
}

/// A validated function code `U (A → F B)` over closed first-order codes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Arrow
{
    /// The thunk type itself.
    pub code: ValueTypeId,
    /// The argument's first-order type `A`.
    pub domain: ValueTypeId,
    /// The returned first-order type `B`.
    pub codomain: ValueTypeId,
}

/// Validate a quoted function code whose argument and result are first-order.
///
/// # Specification
/// - ensures: the quoted type is `U (A → F B)` with `A` and `B` passing
///   first-order validation; the returned parts are exactly `A` and `B`.
/// - fails: `UnsupportedCode` for a non-code; `UnsupportedType` for any other
///   former at the root, a non-returner codomain, or a higher-order part;
///   `Arena` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — Bool and Unit function codes decode with their parts in
///   place; a first-order code at a function boundary refuses.
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
/// - witness: `flow_universe::tests::function::constant_map_refusal_holds_at_a_thunk_code`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(arrow) => allowance.0 < before && matches!(arena.value(code), Some(&Value::Quote(ty)) if ty == arrow.code)
            && matches!(arena.value_type(arrow.code), Some(&ValueType::Thunk(body)) if matches!(arena.comp_type(body), Some(&CompType::Arrow { domain, codomain }) if domain == arrow.domain && arena.comp_type(codomain) == Some(&CompType::Returner(arrow.codomain)))),
        Err(FlowError::UnsupportedCode(named)) => named == code && !matches!(arena.value(code), Some(&Value::Quote(_))),
        Err(FlowError::UnsupportedType(_) | FlowError::Budget | FlowError::Arena) => true,
        Err(_) => false,
    },
)]
pub fn function(
    arena: &TermArena,
    code: ValueId,
    allowance: &mut Allowance,
) -> Result<Arrow, FlowError>
{
    let Some(&Value::Quote(root)) = arena.value(code)
    else {
        return Err(FlowError::UnsupportedCode(code));
    };
    allowance.charge()?;
    let &ValueType::Thunk(body) = arena.value_type(root).ok_or(FlowError::Arena)?
    else {
        return Err(FlowError::UnsupportedType(root));
    };
    let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(body)
    else {
        return Err(FlowError::UnsupportedType(root));
    };
    let Some(&CompType::Returner(codomain)) = arena.comp_type(codomain)
    else {
        return Err(FlowError::UnsupportedType(root));
    };
    first_order(arena, domain, allowance)?;
    first_order(arena, codomain, allowance)?;
    Ok(Arrow {
        code: root,
        domain,
        codomain,
    })
}

/// Validate a Stay endpoint: a first-order code or a function code over them.
///
/// # Specification
/// - ensures: a quoted thunk validates as a function code; every other quoted
///   type validates as a first-order code.
/// - fails: as `function` for a thunk, otherwise as `code`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — Stay forms at a function code and still refuses a thunk
///   of a bare returner.
/// - witness: `flow_universe::tests::function::stay_at_a_thunk_code_collapses`
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && ret.as_ref().map_or(true, |&root| allowance.0 < before && matches!(arena.value(code), Some(&Value::Quote(ty)) if ty == root)),
)]
pub fn endpoint(
    arena: &TermArena,
    code: ValueId,
    allowance: &mut Allowance,
) -> Result<ValueTypeId, FlowError>
{
    if let Some(&Value::Quote(root)) = arena.value(code)
        && matches!(arena.value_type(root), Some(&ValueType::Thunk(_)))
    {
        let arrow = function(arena, code, allowance)?;
        return Ok(arrow.code);
    }
    self::code(arena, code, allowance)
}

/// Validate a native `Flow_U` endpoint: a session code or a Stay endpoint.
///
/// # Specification
/// - ensures: a quoted session type validates as a finite guarded session code;
///   every other quoted type validates as a Stay endpoint.
/// - fails: `Path` for a malformed session code, otherwise as `endpoint`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — session and first-order endpoints decode; a thunk of a
///   bare returner refuses.
/// - witness: `session::tests::session_flows_persist_and_refuse_by_family`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && ret.as_ref().map_or(true, |&root| matches!(arena.value(code), Some(&Value::Quote(ty)) if ty == root)),
)]
pub(super) fn vocabulary(
    arena: &TermArena,
    code: ValueId,
    allowance: &mut Allowance,
    budget: ReplayBudget,
) -> Result<ValueTypeId, FlowError>
{
    if let Some(&Value::Quote(root)) = arena.value(code)
        && matches!(arena.value_type(root), Some(&ValueType::Session { .. }))
    {
        allowance.charge()?;
        return crate::path_universe::code(arena, code, budget).map_err(FlowError::Path);
    }
    endpoint(arena, code, allowance)
}

/// The type a pattern binds at one leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Leaf
{
    /// A base atom.
    Base(BaseType),
    /// A rigid list tail, at this list type.
    Tail(ValueTypeId),
}

/// One canonical source shape, with independent typed leaves.
struct Pattern
{
    /// Constructor pattern with distinct rigid variables.
    value: ValueId,
    /// Leaf types in left-to-right order; the last is de Bruijn zero.
    leaves: Vec<Leaf>,
}

/// Postorder pattern enumeration work.
enum Cover
{
    /// Visit one closed type.
    Visit(ValueTypeId),
    /// Join the shapes of this many summands.
    Sum(usize),
    /// Take the product of this many components' shapes, renaming leaves
    /// apart.
    Product(usize),
    /// Unfold one cell of this list type over the element's shapes.
    List(ValueTypeId),
}

/// Enumerate all constructor shapes with distinct variables at Base leaves and
/// list tails.
///
/// # Specification
/// - requires: `root` is a validated closed first-order type.
/// - ensures: first-summand-first sum order and lexicographic product order; a
///   list unfolds one cell: the empty list, then each element pattern consed
///   onto a fresh rigid tail, the element read past the tail's binder; leaves
///   are never sampled and equal-typed positions remain distinct.
/// - fails: `Arena`, `UnsupportedType` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — repeated Base positions and both sum branches matter; a
///   product of three keeps its leaf order with distinct variables; a list of
///   Bool covers the empty list and one cell per boolean over a tail leaf.
/// - witness: `flow_universe::tests::one_way_classes_preserve_leaves`
/// - witness: `flow_universe::coverage::tests::n_ary_products_cover_with_ordered_leaves`
/// - witness: `flow_universe::coverage::tests::a_list_code_covers_one_cell_over_a_tail_leaf`
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && ret.as_ref().map_or(true, |patterns| allowance.0 < before && match arena.value_type(root) {
Some(held) if held.product_parts() == Some(&[]) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| pattern.leaves.is_empty() && arena.value(pattern.value).and_then(Value::components) == Some(&[])),
        Some(&ValueType::Base(base)) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| pattern.leaves == [Leaf::Base(base)] && matches!(arena.value(pattern.value), Some(&Value::Variable(index)) if u32::from(index) == 0)),
        Some(held) if held.product_parts().is_some() => patterns.iter().all(|pattern| arena.value(pattern.value).and_then(Value::components).map(<[_]>::len) == held.product_parts().map(<[_]>::len)),
        Some(&ValueType::Sum(..)) => patterns.iter().all(|pattern| matches!(arena.value(pattern.value), Some(&Value::Injection(..)))),
        Some(&ValueType::List(_)) => patterns.len() >= 2 && patterns.first().is_some_and(|pattern| pattern.leaves.is_empty() && matches!(arena.value(pattern.value), Some(&Value::ListNil)))
            && patterns.iter().skip(1).all(|pattern| pattern.leaves.last() == Some(&Leaf::Tail(root)) && matches!(arena.value(pattern.value), Some(&Value::ListCons(..)))),
        _ => false,
    }),
)]
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
            Cover::Visit(id) => match arena.value_type(id).ok_or(FlowError::Arena)? {
                &ValueType::Base(base) => results.push(Vec::from([Pattern {
                    value: arena.value_variable(DeBruijnIndex::from(0_u32)),
                    leaves: Vec::from([Leaf::Base(base)]),
                }])),
                &ValueType::Sum(ref parts) if parts.is_empty() => {
                    return Err(FlowError::UnsupportedType(id));
                },
                &ValueType::Sum(ref parts) => {
                    pending.push(Cover::Sum(parts.len()));
                    pending.extend(parts.iter().rev().copied().map(Cover::Visit));
                },
                &ValueType::Product(ref parts) => {
                    pending.push(Cover::Product(parts.len()));
                    pending.extend(parts.iter().rev().copied().map(Cover::Visit));
                },
                &ValueType::List(element) => {
                    pending.push(Cover::List(id));
                    pending.push(Cover::Visit(element));
                },
                &ValueType::Data { .. }
                | &ValueType::Record(_)
                | &ValueType::Session { .. }
                | &ValueType::PathUniverse(..)
                | &ValueType::FlowUniverse(..)
                | &ValueType::Path { .. }
                | &ValueType::Flow { .. }
                | &ValueType::Bridge { .. }
                | &ValueType::Sigma { .. }
                | &ValueType::Thunk(_)
                | &ValueType::Universe { .. }
                | &ValueType::Lift { .. }
                | &ValueType::Element { .. }
                | &ValueType::Abstract(_)
                | &ValueType::StaticPi { .. }
                | &ValueType::Staged { .. } => return Err(FlowError::UnsupportedType(id)),
            },
            Cover::Sum(arity) => {
                let start = results.len().checked_sub(arity).ok_or(FlowError::Arena)?;
                let mut joined = Vec::new();
                for (summand, branch) in results.drain(start ..).enumerate() {
                    for pattern in branch {
                        allowance.charge()?;
                        joined.push(Pattern {
                            value: arena.value_injection(Summand::from(summand), pattern.value),
                            leaves: pattern.leaves,
                        });
                    }
                }
                results.push(joined);
            },
            // Each step crosses the tuples so far with the next component's
            // shapes; the earlier components' leaves shift past the new
            // component's, so every leaf stays distinct.
            Cover::Product(arity) => {
                let start = results.len().checked_sub(arity).ok_or(FlowError::Arena)?;
                let mut tuples = Vec::from([(Vec::<ValueId>::new(), Vec::<Leaf>::new())]);
                for component in results.drain(start ..) {
                    let mut crossed = Vec::new();
                    for tuple in &tuples {
                        let (ref prefix, ref prefix_leaves) = *tuple;
                        for next in &component {
                            allowance.charge()?;
                            let depth = u32::try_from(next.leaves.len())
                                .map_err(|_overflow| FlowError::Budget)?;
                            let mut values = Vec::with_capacity(prefix.len().saturating_add(1));
                            for &earlier in prefix {
                                values.push(shift_value(
                                    arena,
                                    &mut table,
                                    &mut NullMemo,
                                    earlier,
                                    BinderDepth::default(),
                                    BinderDepth::from(depth),
                                ));
                            }
                            values.push(next.value);
                            let mut leaves = Vec::with_capacity(
                                prefix_leaves.len().saturating_add(next.leaves.len()),
                            );
                            leaves.extend_from_slice(prefix_leaves);
                            leaves.extend_from_slice(&next.leaves);
                            crossed.push((values, leaves));
                        }
                    }
                    tuples = crossed;
                }
                let joined = tuples
                    .into_iter()
                    .map(|(values, leaves)| Pattern {
                        value: arena.value_tuple(&values),
                        leaves,
                    })
                    .collect();
                results.push(joined);
            },
            // The element shifts past the tail's binder; the tail is the
            // innermost variable, the pattern's last leaf.
            Cover::List(list) => {
                let elements = results.pop().ok_or(FlowError::Arena)?;
                let mut joined = Vec::with_capacity(elements.len().saturating_add(1));
                joined.push(Pattern {
                    value: arena.value_list_nil(),
                    leaves: Vec::new(),
                });
                for element in elements {
                    allowance.charge()?;
                    let head = shift_value(
                        arena,
                        &mut table,
                        &mut NullMemo,
                        element.value,
                        BinderDepth::default(),
                        BinderDepth::from(1_u32),
                    );
                    let tail = arena.value_variable(DeBruijnIndex::from(0_u32));
                    let mut leaves = element.leaves;
                    leaves.push(Leaf::Tail(list));
                    joined.push(Pattern {
                        value: arena.value_list_cons(head, tail),
                        leaves,
                    });
                }
                results.push(joined);
            },
        }
    }
    results.pop().ok_or(FlowError::Arena)
}

/// The leaf a variable of an image's output names: the pattern's leaves are
/// in left-to-right order, the last at de Bruijn zero.
///
/// # Specification
/// trivial.
fn source_leaf(
    leaves: &[Leaf],
    index: DeBruijnIndex,
) -> Option<Leaf>
{
    let index = usize::try_from(u32::from(index)).ok()?;
    leaves
        .len()
        .checked_sub(index.checked_add(1)?)
        .and_then(|position| leaves.get(position))
        .copied()
}

/// Validate a container-shaped target using only correctly typed source leaves.
///
/// # Specification
/// - ensures: every target Base position selects a same-typed source position
///   and every list position is a list constructor or selects a source tail of
///   a convertible list type; all other nodes are the canonical constructor of
///   the target code.
/// - fails: `NonNatural` for literals, wrong shapes, fresh or mistyped leaves;
///   `Arena` or `Budget` for unresolved types or exhausted traversal.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — literals cannot hide beneath sums, products or list
///   cells, typed leaf selection rejects fresh variables and differently typed
///   leaves, a tail stands only at its own list type, and a constant literal at
///   a String leaf, a type of infinitely many values, is refused naming that
///   literal.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
/// - witness: `flow_universe::tests::a_list_flow_moves_its_tail_unread`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && ret.as_ref().map_or(true, |&()| allowance.0 < before && match (arena.value(output), arena.value_type(target)) {
        (Some(value), Some(classifier)) if value.components().is_some() => value.components().map(<[_]>::len) == classifier.product_parts().map(<[_]>::len),
        (Some(&Value::Injection(summand, _)), Some(classifier)) => classifier.summands().is_some_and(|summands| usize::from(summand) < summands.len()),
        (Some(&Value::Variable(index)), Some(&ValueType::Base(base))) => source_leaf(leaves, index) == Some(Leaf::Base(base)),
        (Some(&Value::Variable(index)), Some(&ValueType::List(_))) => matches!(source_leaf(leaves, index), Some(Leaf::Tail(_))),
        (Some(&Value::ListNil | &Value::ListCons(..)), Some(&ValueType::List(_))) => true,
        _ => false,
    }),
)]
fn natural(
    arena: &TermArena,
    output: ValueId,
    target: ValueTypeId,
    leaves: &[Leaf],
    allowance: &mut Allowance,
) -> Result<(), FlowError>
{
    let mut pending = Vec::from([(output, target)]);
    while let Some((value, at)) = pending.pop() {
        allowance.charge()?;
        let ty = arena.value_type(at).ok_or(FlowError::Arena)?;
        match (arena.value(value), ty) {
            (Some(&Value::Variable(index)), &ValueType::Base(base)) => {
                if source_leaf(leaves, index) != Some(Leaf::Base(base)) {
                    return Err(FlowError::NonNatural(value));
                }
            },
            (Some(&Value::Variable(index)), &ValueType::List(_)) => {
                let Some(Leaf::Tail(source)) = source_leaf(leaves, index)
                else {
                    return Err(FlowError::NonNatural(value));
                };
                if convertible_value_types(arena, source, at) != Convertibility::Convertible {
                    return Err(FlowError::NonNatural(value));
                }
            },
            (Some(&Value::ListNil), &ValueType::List(_)) => {},
            (Some(&Value::ListCons(head, tail)), &ValueType::List(element)) => {
                pending.push((tail, at));
                pending.push((head, element));
            },
            (Some(&Value::Tuple(ref components)), &ValueType::Product(ref parts))
                if components.len() == parts.len() =>
            {
                pending.extend(components.iter().copied().zip(parts.iter().copied()).rev());
            },
            (Some(&Value::Injection(summand, value)), &ValueType::Sum(ref summands)) => {
                let summand = summands
                    .get(usize::from(summand))
                    .copied()
                    .ok_or(FlowError::NonNatural(value))?;
                pending.push((value, summand));
            },
            _ => return Err(FlowError::NonNatural(value)),
        }
    }
    Ok(())
}

/// Open one image `thunk(λ…λ. return o)` binding one lambda per pattern leaf.
///
/// # Specification
/// - ensures: the output `o` beneath exactly one lambda per leaf; its variables
///   name the pattern's leaves, the last at de Bruijn zero.
/// - fails: `NonNatural` naming the image for any other shape, a different
///   binder count among them; `Budget` on exhausted traversal.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — an image binding one leaf too few refuses by name.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(_) => matches!(arena.value(image), Some(&Value::Thunk(_))),
        Err(FlowError::NonNatural(named)) => named == image,
        Err(FlowError::Budget) => true,
        Err(_) => false,
    },
)]
fn peel(
    arena: &TermArena,
    image: ValueId,
    leaves: &[Leaf],
    allowance: &mut Allowance,
) -> Result<ValueId, FlowError>
{
    let Some(&Value::Thunk(mut body)) = arena.value(image)
    else {
        return Err(FlowError::NonNatural(image));
    };
    for _leaf in leaves {
        allowance.charge()?;
        let Some(&Computation::Lambda(inner)) = arena.computation(body)
        else {
            return Err(FlowError::NonNatural(image));
        };
        body = inner;
    }
    match arena.computation(body) {
        Some(&Computation::Return(output)) => Ok(output),
        _ => Err(FlowError::NonNatural(image)),
    }
}

/// Replay the translator against exhaustive, validated symbolic images.
///
/// # Specification
/// - requires: the endpoints are first-order codes and the translator checked
///   at `U (source → F target)` in the empty context.
/// - ensures: one image and one dialogue per source shape; each image opens to
///   a leaf-natural target shape, and the translator applied to the shape
///   converts with its return by ordinary kernel replay of the dialogue,
///   unfolding only what `unfoldings` admits. The kernel chooses the source,
///   the action and the positive claim.
/// - fails: `Coverage`, `NonNatural`, `ForwardReplay`, or construction errors.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — omitted constructors, constant Base maps and false traces
///   cannot certify a forward action, and a tampered image refuses by name at
///   readmission.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
#[spec(ensures: |ret| match ret {
    Ok(()) => u64::from(budget) > 0 && !images.is_empty() && images.len() == dialogues.len(),
    Err(FlowError::ForwardReplay { pattern, verdict }) => pattern.0 < images.len() && verdict != KernelVerdict::Convertible,
    Err(_) => true,
})]
pub fn forward(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    flow: FlowType,
    translator: ValueId,
    (images, dialogues): (&[ValueId], &[Dialogue]),
    budget: ReplayBudget,
) -> Result<(), FlowError>
{
    let mut allowance = Allowance(u64::from(budget));
    let patterns = patterns(arena, flow.source, &mut allowance)?;
    if images.len() != patterns.len() || dialogues.len() != patterns.len() {
        return Err(FlowError::Coverage);
    }
    for (position, ((pattern, &image), dialogue)) in
        patterns.into_iter().zip(images).zip(dialogues).enumerate()
    {
        let output = peel(arena, image, &pattern.leaves, &mut allowance)?;
        natural(arena, output, flow.target, &pattern.leaves, &mut allowance)?;
        let force = arena.computation_force(translator);
        let application = arena.computation_application(force, pattern.value);
        let expected = arena.computation_return(output);
        let verdict = crate::replay::replay(
            arena,
            unfoldings,
            ReplaySides::Computations(application, expected),
            EngineClaim::Convertible,
            dialogue.iter().copied().map(anchor),
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

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;

    use super::Allowance;
    use super::FlowError;
    use super::Leaf;
    use super::natural;
    use super::patterns;

    /// A product of three base types covers in one pattern whose leaves keep
    /// their component order and whose variables stay distinct, first
    /// component outermost; the empty sum is outside the vocabulary.
    #[test]
    fn n_ary_products_cover_with_ordered_leaves()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_type_base(BaseType::String);
        let triple = arena.value_type_product(&[integer, text, integer]);
        let covered =
            patterns(&mut arena, triple, &mut Allowance(u64::MAX)).expect("a product covers");
        let [ref only] = *covered.as_slice()
        else {
            panic!("one pattern for a product of base types");
        };
        assert_eq!(
            vec![
                Leaf::Base(BaseType::Integer),
                Leaf::Base(BaseType::String),
                Leaf::Base(BaseType::Integer)
            ],
            only.leaves
        );
        let indices = arena
            .value(only.value)
            .and_then(Value::components)
            .expect("a tuple")
            .iter()
            .map(|&component| match arena.value(component) {
                Some(&Value::Variable(index)) => u32::from(index),
                _ => panic!("a base position is a variable"),
            })
            .collect::<Vec<_>>();
        assert_eq!(vec![2_u32, 1_u32, 0_u32], indices);

        let empty = arena.value_type_empty();
        assert!(matches!(
            patterns(&mut arena, empty, &mut Allowance(u64::MAX)),
            Err(FlowError::UnsupportedType(found)) if found == empty
        ));
    }

    /// A list code unfolds one cell: the empty list with no leaf, then each
    /// element shape consed onto a tail that is the innermost variable and
    /// the last leaf, the element's own leaves read past it. An output may
    /// cons cells over that tail or return it bare, at the tail's own list
    /// type only; an element leaf at the tail's position, or the tail at
    /// another list type, is no natural image.
    #[test]
    fn a_list_code_covers_one_cell_over_a_tail_leaf()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let boolean = arena.value_type_sum(&[unit, unit]);
        let booleans = arena.value_type_list(boolean);
        let covered =
            patterns(&mut arena, booleans, &mut Allowance(u64::MAX)).expect("a list covers");
        let [ref empty, ref truth, ref falsity] = *covered.as_slice()
        else {
            panic!("the empty list and one cell per boolean");
        };
        assert!(matches!(arena.value(empty.value), Some(&Value::ListNil)));
        assert!(empty.leaves.is_empty());
        for (cell, summand) in [(truth, 0_usize), (falsity, 1_usize)] {
            assert_eq!(vec![Leaf::Tail(booleans)], cell.leaves);
            let Some(&Value::ListCons(head, tail)) = arena.value(cell.value)
            else {
                panic!("a cell is consed");
            };
            assert!(
                matches!(arena.value(head), Some(&Value::Injection(found, _)) if usize::from(found) == summand)
            );
            assert!(
                matches!(arena.value(tail), Some(&Value::Variable(index)) if u32::from(index) == 0)
            );
        }

        let integer = arena.value_type_base(BaseType::Integer);
        let integers = arena.value_type_list(integer);
        let covered =
            patterns(&mut arena, integers, &mut Allowance(u64::MAX)).expect("a list covers");
        let [_, ref cell] = *covered.as_slice()
        else {
            panic!("the empty list and one cell");
        };
        assert_eq!(
            vec![Leaf::Base(BaseType::Integer), Leaf::Tail(integers)],
            cell.leaves
        );
        let Some(&Value::ListCons(head, _)) = arena.value(cell.value)
        else {
            panic!("a cell is consed");
        };
        assert!(
            matches!(arena.value(head), Some(&Value::Variable(index)) if u32::from(index) == 1),
            "the element is read past the tail's binder"
        );

        let leaves = cell.leaves.clone();
        let element = arena.value_variable(DeBruijnIndex::from(1_u32));
        let tail = arena.value_variable(DeBruijnIndex::from(0_u32));
        let kept = arena.value_list_cons(element, tail);
        let doubled = arena.value_list_cons(element, kept);
        let again = arena.value_type_list(integer);
        for natural_output in [kept, doubled, tail] {
            assert_eq!(
                natural(
                    &arena,
                    natural_output,
                    again,
                    &leaves,
                    &mut Allowance(u64::MAX)
                ),
                Ok(()),
                "cells over the tail, at its list type allocated apart"
            );
        }
        let misplaced = arena.value_list_cons(element, element);
        assert_eq!(
            natural(
                &arena,
                misplaced,
                integers,
                &leaves,
                &mut Allowance(u64::MAX)
            ),
            Err(FlowError::NonNatural(element)),
            "an element leaf at the tail's position"
        );
        let text = arena.value_type_base(BaseType::String);
        let texts = arena.value_type_list(text);
        assert_eq!(
            natural(&arena, tail, texts, &leaves, &mut Allowance(u64::MAX)),
            Err(FlowError::NonNatural(tail)),
            "the tail at another list type"
        );
    }

    /// A quoted empty sum is no first-order code, at its root or beneath a
    /// product; a tuple of another arity than its product is no natural
    /// image; and a forward flow owes one dialogue per pattern as well as
    /// one image.
    #[test]
    fn coverage_counts_every_part_it_is_owed()
    {
        let mut arena = TermArena::new();
        let empty = arena.value_type_empty();
        let integer = arena.value_type_base(BaseType::Integer);
        let holding = arena.value_type_product(&[integer, empty]);
        for root in [empty, holding] {
            let quoted = arena.value_quote(root);
            assert_eq!(
                super::code(&arena, quoted, &mut Allowance(u64::MAX)),
                Err(FlowError::UnsupportedType(empty))
            );
        }

        let pair = arena.value_type_product(&[integer, integer]);
        let leaf = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
        let short = arena.value_tuple(&[leaf]);
        assert_eq!(
            super::natural(
                &arena,
                short,
                pair,
                &[Leaf::Base(BaseType::Integer)],
                &mut Allowance(u64::MAX)
            ),
            Err(FlowError::NonNatural(short))
        );

        let unit = arena.value_type_unit();
        let unit_value = arena.value_unit();
        let returned = arena.computation_return(unit_value);
        let image = arena.value_thunk(returned);
        let translator = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
        assert_eq!(
            super::forward(
                &mut arena,
                &crate::replay::Unfoldings::default(),
                super::FlowType {
                    source: unit,
                    target: unit,
                },
                translator,
                (&[image], &[]),
                crate::replay::ReplayBudget::DEFAULT,
            ),
            Err(FlowError::Coverage),
            "one image and no dialogue for Unit's one pattern"
        );
    }
}
