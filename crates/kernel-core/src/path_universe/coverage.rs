//! Closed-code coverage and the iterative shadow of transport's beta rules.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Summand;
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
/// - ensures: outer formers are Base, Product (the unit among them), a Sum of
///   at least one summand, or Session; session graph structure and guards
///   check. The empty sum is refused, as the retired empty type was. A List
///   code is refused as an uncertified stratum: its inhabitants are unbounded,
///   so no finite constructor coverage certifies a round trip over it. Native
///   formation separately checks session payload codes in an empty term
///   context.
/// - provides: code-shape inspection, never a checking verdict.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `UncertifiedStratum`,
///   `Session`, `Arena` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — Bool and product codes admit; thunk codes refuse; a list
///   code refuses by its stratum.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
/// - witness: `path_universe::tests::a_recursive_code_is_an_uncertified_stratum`
/// - witness: `session::tests::session_codes_are_closed_and_contractive`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(root) => allowance.0 < before && matches!(arena.value(code), Some(&Value::Quote(quoted)) if root == quoted),
        Err(PathError::UnsupportedCode(named)) => named == code && !matches!(arena.value(code), Some(&Value::Quote(_))),
        Err(PathError::UnsupportedType(root)) => arena.value_type(root).is_some_and(|node| !matches!(node, &ValueType::Base(_) | &ValueType::Product(..) | &ValueType::Session { .. } | &ValueType::List(_)) && node.summands().is_none_or(<[_]>::is_empty)),
        Err(PathError::UncertifiedStratum(root)) => matches!(arena.value_type(root), Some(&ValueType::List(_))),
        Err(PathError::Budget) => allowance.0 == 0,
        Err(PathError::Arena | PathError::Session(_)) => true,
        Err(_) => false,
    },
)]
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
            | &ValueType::Base(_) => {},
            | &ValueType::Session {
                ref graph,
                payloads,
            } => {
                crate::session::validate_graph(arena, graph, payloads)
                    .map_err(PathError::Session)?;
                // Ordinary formation checks payload codes in an empty
                // telescope.
            },
            | &ValueType::Sum(ref parts) if parts.is_empty() => {
                return Err(PathError::UnsupportedType(id));
            },
            | &ValueType::Sum(ref parts) | &ValueType::Product(ref parts) => {
                pending.extend(parts.iter().rev().copied());
            },
            | &ValueType::List(_) => return Err(PathError::UncertifiedStratum(id)),
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
    /// Join the patterns of this many summands with their distinct injection
    /// tags.
    Sum(usize),
    /// Form every tuple of this many components' patterns, renaming base
    /// variables apart.
    Product(usize),
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
/// - intension: sums are first-summand-first and products are lexicographic.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — both Bool branches are required; a literal sample cannot
///   establish a Base round trip, while a generic product identity is admitted.
///   A product and a sum of three cover by position with distinct variables.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
/// - witness: `path_universe::coverage::tests::n_ary_codes_cover_by_position`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(ref patterns) => allowance.0 < before
            && patterns.iter().all(|pattern| arena.value(pattern.value).is_some())
            && match arena.value_type(root) {
Some(held) if held.product_parts() == Some(&[]) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| u32::from(pattern.binders) == 0 && arena.value(pattern.value).and_then(Value::components) == Some(&[])),
                Some(&ValueType::Base(_)) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| u32::from(pattern.binders) == 1 && matches!(arena.value(pattern.value), Some(&Value::Variable(index)) if u32::from(index) == 0)),
                Some(&ValueType::Sum(..) | &ValueType::Product(..)) => !patterns.is_empty(),
                _ => false,
            },
        Err(_) => true,
    },
)]
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
                    | &ValueType::Base(_) => results.push(Vec::from([Pattern {
                        value: arena.value_variable(DeBruijnIndex::from(0_u32)),
                        binders: BinderDepth::from(1_u32),
                    }])),
                    | &ValueType::Sum(ref parts) if parts.is_empty() => {
                        return Err(PathError::UnsupportedType(id));
                    },
                    | &ValueType::Sum(ref parts) => {
                        pending.push(Cover::Sum(parts.len()));
                        pending.extend(parts.iter().rev().copied().map(Cover::Visit));
                    },
                    | &ValueType::Product(ref parts) => {
                        pending.push(Cover::Product(parts.len()));
                        pending.extend(parts.iter().rev().copied().map(Cover::Visit));
                    },
                    | _ => return Err(PathError::UnsupportedType(id)),
                }
            },
            | Cover::Sum(arity) => {
                let start = results.len().checked_sub(arity).ok_or(PathError::Arena)?;
                let mut joined = Vec::new();
                for (summand, branch) in results.drain(start ..).enumerate() {
                    for pattern in branch {
                        allowance.charge()?;
                        joined.push(Pattern {
                            value: arena.value_injection(Summand::from(summand), pattern.value),
                            binders: pattern.binders,
                        });
                    }
                }
                results.push(joined);
            },
            // Each step crosses the tuples so far with the next component's
            // patterns; the earlier components' base variables shift past the
            // new component's, so every variable stays distinct.
            | Cover::Product(arity) => {
                let start = results.len().checked_sub(arity).ok_or(PathError::Arena)?;
                let mut tuples = Vec::from([(Vec::<ValueId>::new(), 0_u32)]);
                for component in results.drain(start ..) {
                    let mut crossed = Vec::new();
                    for &(ref prefix, binders) in &tuples {
                        for next in &component {
                            allowance.charge()?;
                            let binders = binders
                                .checked_add(u32::from(next.binders))
                                .ok_or(PathError::Budget)?;
                            let mut values = Vec::with_capacity(prefix.len().saturating_add(1));
                            for &earlier in prefix {
                                values.push(shift_value(
                                    arena,
                                    &mut table,
                                    &mut NullMemo,
                                    earlier,
                                    BinderDepth::default(),
                                    next.binders,
                                ));
                            }
                            values.push(next.value);
                            crossed.push((values, binders));
                        }
                    }
                    tuples = crossed;
                }
                let joined = tuples
                    .into_iter()
                    .map(|(values, binders)| Pattern {
                        value: arena.value_tuple(&values),
                        binders: BinderDepth::from(binders),
                    })
                    .collect();
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
#[spec(ensures: |ret| match ret {
    Ok(()) => u64::from(budget) > 0 && !dialogues.is_empty(),
    Err(PathError::Coverage(found)) => found == direction,
    Err(PathError::RoundTrip { direction: found, pattern, verdict }) => found == direction && pattern.0 < dialogues.len() && verdict != KernelVerdict::Convertible,
    Err(PathError::Arena | PathError::UnsupportedType(_) | PathError::Budget) => true,
    Err(_) => false,
})]
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

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::Summand;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;

    use super::Allowance;
    use super::patterns;
    use crate::path_universe::PathError;

    /// A product of three base types covers in one pattern whose three base
    /// variables stay distinct, first component outermost; a sum of three
    /// covers in one pattern per summand, tagged by position; the empty sum is
    /// outside the vocabulary.
    #[test]
    fn n_ary_codes_cover_by_position()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let triple = arena.value_type_product(&[integer, integer, integer]);
        let covered =
            patterns(&mut arena, triple, &mut Allowance(u64::MAX)).expect("a product covers");
        let [ref only] = *covered.as_slice()
        else {
            panic!("one pattern for a product of base types");
        };
        assert_eq!(3_u32, u32::from(only.binders));
        let components = arena
            .value(only.value)
            .and_then(Value::components)
            .expect("a tuple")
            .to_vec();
        let indices = components
            .iter()
            .map(|&component| match arena.value(component) {
                | Some(&Value::Variable(index)) => u32::from(index),
                | _ => panic!("a base position is a variable"),
            })
            .collect::<Vec<_>>();
        assert_eq!(vec![2_u32, 1_u32, 0_u32], indices);

        let unit = arena.value_type_unit();
        let choice = arena.value_type_sum(&[unit, unit, unit]);
        let covered = patterns(&mut arena, choice, &mut Allowance(u64::MAX)).expect("a sum covers");
        let summands = covered
            .iter()
            .map(|pattern| match arena.value(pattern.value) {
                | Some(&Value::Injection(summand, _)) => summand,
                | _ => panic!("a sum pattern is an injection"),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            vec![
                Summand::from(0_usize),
                Summand::from(1_usize),
                Summand::from(2_usize)
            ],
            summands
        );

        let empty = arena.value_type_empty();
        assert!(matches!(
            patterns(&mut arena, empty, &mut Allowance(u64::MAX)),
            Err(PathError::UnsupportedType(found)) if found == empty
        ));
    }
}
