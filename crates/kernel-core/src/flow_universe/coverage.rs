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
///   them) and Sum of at least one summand; the empty sum is refused, as the
///   retired empty type was.
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
        Err(FlowError::UnsupportedType(ty)) => arena.value_type(ty).is_some_and(|node| !matches!(node, &ValueType::Base(_) | &ValueType::Product(..)) && node.summands().is_none_or(<[_]>::is_empty)),
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
/// - ensures: every node reachable from `root` is Base, Product or a Sum of at
///   least one summand; each visit charges `allowance` once.
/// - fails: `UnsupportedType` naming the first other node, `Arena` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a function code refuses at a forward endpoint and beneath
///   a function code's argument; Bool and Unit pass.
/// - witness: `flow_universe::tests::function::constant_map_refusal_holds_at_a_thunk_code`
/// - witness: `flow_universe::tests::stay_and_forward_admit_and_ride`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(()) => allowance.0 < before,
        Err(FlowError::UnsupportedType(ty)) => arena.value_type(ty).is_some_and(|node| !matches!(node, &ValueType::Base(_) | &ValueType::Product(..)) && node.summands().is_none_or(<[_]>::is_empty)),
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
            &ValueType::Data { .. }
            | &ValueType::Record(_)
            | &ValueType::Session { .. }
            | &ValueType::PathUniverse(..)
            | &ValueType::FlowUniverse(..)
            | &ValueType::Path { .. }
            | &ValueType::Flow { .. }
            | &ValueType::Sigma { .. }
            | &ValueType::List(_)
            | &ValueType::Thunk(_)
            | &ValueType::Universe { .. }
            | &ValueType::Lift { .. }
            | &ValueType::Element { .. }
            | &ValueType::Abstract(_)
            | &ValueType::StaticPi { .. } => return Err(FlowError::UnsupportedType(id)),
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
/// - hypothesis: L3 — session and first-order endpoints decode; a List code
///   refuses.
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
    /// Join the shapes of this many summands.
    Sum(usize),
    /// Take the product of this many components' shapes, renaming leaves
    /// apart.
    Product(usize),
}

/// Enumerate all constructor shapes with distinct variables at Base leaves.
///
/// # Specification
/// - requires: `root` is a validated closed first-order type.
/// - ensures: first-summand-first sum order and lexicographic product order;
///   leaves are never sampled and equal-typed positions remain distinct.
/// - fails: `Arena`, `UnsupportedType` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — repeated Base positions and both sum branches matter; a
///   product of three keeps its leaf order with distinct variables.
/// - witness: `flow_universe::tests::one_way_classes_preserve_leaves`
/// - witness: `flow_universe::coverage::tests::n_ary_products_cover_with_ordered_leaves`
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && ret.as_ref().map_or(true, |patterns| allowance.0 < before && match arena.value_type(root) {
Some(held) if held.product_parts() == Some(&[]) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| pattern.leaves.is_empty() && arena.value(pattern.value).and_then(Value::components) == Some(&[])),
        Some(&ValueType::Base(base)) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| pattern.leaves == [base] && matches!(arena.value(pattern.value), Some(&Value::Variable(index)) if u32::from(index) == 0)),
        Some(held) if held.product_parts().is_some() => patterns.iter().all(|pattern| arena.value(pattern.value).and_then(Value::components).map(<[_]>::len) == held.product_parts().map(<[_]>::len)),
        Some(&ValueType::Sum(..)) => patterns.iter().all(|pattern| matches!(arena.value(pattern.value), Some(&Value::Injection(..)))),
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
                    leaves: Vec::from([base]),
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
                &ValueType::Data { .. }
                | &ValueType::Record(_)
                | &ValueType::Session { .. }
                | &ValueType::PathUniverse(..)
                | &ValueType::FlowUniverse(..)
                | &ValueType::Path { .. }
                | &ValueType::Flow { .. }
                | &ValueType::Sigma { .. }
                | &ValueType::List(_)
                | &ValueType::Thunk(_)
                | &ValueType::Universe { .. }
                | &ValueType::Lift { .. }
                | &ValueType::Element { .. }
                | &ValueType::Abstract(_)
                | &ValueType::StaticPi { .. } => return Err(FlowError::UnsupportedType(id)),
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
                let mut tuples = Vec::from([(Vec::<ValueId>::new(), Vec::<BaseType>::new())]);
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
/// - hypothesis: L3 — literals cannot hide beneath sums or products, typed leaf
///   selection rejects fresh variables and differently typed leaves, and a
///   constant literal at a String leaf, a type of infinitely many values, is
///   refused naming that literal.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && ret.as_ref().map_or(true, |&()| allowance.0 < before && match (arena.value(output), arena.value_type(target)) {
        (Some(value), Some(classifier)) if value.components().is_some() => value.components().map(<[_]>::len) == classifier.product_parts().map(<[_]>::len),
        (Some(&Value::Injection(summand, _)), Some(classifier)) => classifier.summands().is_some_and(|summands| usize::from(summand) < summands.len()),
        (Some(&Value::Variable(index)), Some(&ValueType::Base(base))) => usize::try_from(u32::from(index)).ok().and_then(|index| leaves.len().checked_sub(index.saturating_add(1))).and_then(|position| leaves.get(position)) == Some(&base),
        _ => false,
    }),
)]
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
            (Some(&Value::Variable(index)), &ValueType::Base(base)) => {
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
    leaves: &[BaseType],
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
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;

    use super::Allowance;
    use super::FlowError;
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
            vec![BaseType::Integer, BaseType::String, BaseType::Integer],
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
}
