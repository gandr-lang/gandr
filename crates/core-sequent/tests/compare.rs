//! Structural equality of the supported pure term fragment across arenas.
//!
//! The core's derived equality compares child ids, which two arenas assign
//! independently; these walks compare what the ids name instead, node by node,
//! over an explicit stack. The types focusing erases — a datatype
//! constructor's datatype and a nominal match's motive — are not compared.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;

/// Whether two terms agree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Agreement
{
    /// Every supported node agrees.
    Same,
    /// A node differs, an address dangles, or a quoted type is outside the
    /// fragment.
    Differ,
}

/// One pending pair of nodes.
#[derive(Clone, Copy, Debug)]
enum Pending
{
    /// Two values.
    Values(ValueId, ValueId),
    /// Two computations.
    Computations(ComputationId, ComputationId),
}

/// Compare acyclic computations using the pure-fragment relation of [`walk`].
///
/// # Specification
/// - requires: both reachable term graphs are acyclic.
/// - ensures: the pure-fragment structural relation specified by [`walk`],
///   independent of either arena's node addresses.
/// - provides: a computation comparison for the semantic test oracles.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — independently numbered graphs agree; different labels and
///   ordered children do not. Missing roots are refused, distinguishing address
///   equality and unvalidated lookups. This observes the finite pure fragment,
///   not cyclic graphs or equivalence modulo reduction.
/// - witness: `tests::compare::computation_comparison_preserves_every_child_role`
#[spec(ensures: |ret| ret != Agreement::Same ||
    (left_arena.computation(left).is_some() && right_arena.computation(right).is_some()))]
pub fn same_computation(
    left_arena: &CoreArena,
    left: ComputationId,
    right_arena: &CoreArena,
    right: ComputationId,
) -> Agreement
{
    walk(left_arena, right_arena, Pending::Computations(left, right))
}

/// Compare acyclic values using the pure-fragment relation of [`walk`].
///
/// # Specification
/// - requires: both reachable term graphs are acyclic.
/// - ensures: the pure-fragment structural relation specified by [`walk`],
///   independent of either arena's node addresses.
/// - provides: a value comparison for the semantic test oracles.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — independently numbered graphs agree; different labels and
///   ordered children do not. Missing roots are refused, distinguishing address
///   equality and unvalidated lookups. This observes the finite pure fragment,
///   not cyclic graphs or equivalence modulo reduction.
/// - witness: `tests::compare::structural_equality_ignores_addresses_but_not_labels`
#[spec(ensures: |ret| ret != Agreement::Same ||
    (left_arena.value(left).is_some() && right_arena.value(right).is_some()))]
pub fn same_value(
    left_arena: &CoreArena,
    left: ValueId,
    right_arena: &CoreArena,
    right: ValueId,
) -> Agreement
{
    walk(left_arena, right_arena, Pending::Values(left, right))
}

/// Compare from a starting pair.
///
/// # Specification
/// - requires: both reachable term graphs are acyclic.
/// - ensures: Same exactly when every corresponding supported node has the same
///   constructor, labels and ordered children; absent nodes, quoted types and
///   static forms and native paths differ, even if their raw addresses agree. A
///   datatype constructor's datatype and a nominal match's motive are not
///   compared.
/// - provides: equality independent of each arena's allocation history for the
///   pure term fragment used by the focusing and machine suites.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — independently allocated graphs agree despite different
///   addresses; distinct leaves, each pair field, branch labels, binders,
///   eliminators, constructor ordinals and field counts, nominal branches and
///   fixpoint evidence differ, while a datatype or motive alone does not.
///   Missing nodes, quotes, static forms and native paths are outside this
///   observer's pure focusing fragment. These finite cases challenge ignored
///   labels or children and address comparison, not cyclic inputs or
///   equivalence modulo evaluation.
/// - witness: `tests::compare::structural_equality_ignores_addresses_but_not_labels`
/// - witness: `tests::compare::computation_comparison_preserves_every_child_role`
#[spec(ensures: |ret| match start {
    | Pending::Values(left, right) => match (left_arena.value(left), right_arena.value(right)) {
        | (Some(left), Some(right)) => match *left {
            | Value::Unit | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) => (ret == Agreement::Same) == (left == right),
            | Value::Injection(side, _) => ret != Agreement::Same || matches!(*right, Value::Injection(other_side, _) if side == other_side),
            | Value::Lift { ref target, .. } => ret != Agreement::Same || matches!(*right, Value::Lift { target: ref other_target, .. } if target == other_target),
            | Value::Pair(_, _) | Value::Thunk(_) => ret != Agreement::Same || core::mem::discriminant(left) == core::mem::discriminant(right),
            | Value::Constructor { tag, ref fields, .. } => ret != Agreement::Same
                || matches!(*right, Value::Constructor { tag: other_tag, fields: ref other_fields, .. } if tag == other_tag && fields.len() == other_fields.len()),
            Value::Record(_) | Value::Primitive { .. } | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(_, _) | Value::Hole(_) | Value::Mark { .. } => ret == Agreement::Differ,
        },
        | _ => ret == Agreement::Differ,
    },
    | Pending::Computations(left, right) => ret != Agreement::Same || match (left_arena.computation(left), right_arena.computation(right)) {
        | (Some(left), Some(right)) => core::mem::discriminant(left) == core::mem::discriminant(right),
        | _ => false,
    },
})]
fn walk(
    left_arena: &CoreArena,
    right_arena: &CoreArena,
    start: Pending,
) -> Agreement
{
    let mut pending: Vec<Pending> = alloc::vec![start];
    while let Some(pair) = pending.pop() {
        let agrees = match pair {
            | Pending::Values(left, right) => {
                let (Some(left), Some(right)) = (left_arena.value(left), right_arena.value(right))
                else {
                    return Agreement::Differ;
                };
                match (left, right) {
                    | (
                        &Value::Variable { zone, index },
                        &Value::Variable {
                            zone: other_zone,
                            index: other_index,
                        },
                    ) => zone == other_zone && index == other_index,
                    | (&Value::Constant(constant), &Value::Constant(other)) => constant == other,
                    | (&Value::Unit, &Value::Unit) => true,
                    | (&Value::Literal(ref literal), &Value::Literal(ref other)) => {
                        literal == other
                    },
                    | (&Value::Pair(first, second), &Value::Pair(other_first, other_second)) => {
                        pending.push(Pending::Values(first, other_first));
                        pending.push(Pending::Values(second, other_second));
                        true
                    },
                    | (
                        &Value::Injection(side, body),
                        &Value::Injection(other_side, other_body),
                    ) => {
                        pending.push(Pending::Values(body, other_body));
                        side == other_side
                    },
                    | (&Value::Thunk(body), &Value::Thunk(other_body)) => {
                        pending.push(Pending::Computations(body, other_body));
                        true
                    },
                    | (
                        &Value::Lift { ref target, body },
                        &Value::Lift {
                            target: ref other_target,
                            body: other_body,
                        },
                    ) => {
                        pending.push(Pending::Values(body, other_body));
                        target == other_target
                    },
                    | (
                        &Value::Constructor {
                            tag, ref fields, ..
                        },
                        &Value::Constructor {
                            tag: other_tag,
                            fields: ref other_fields,
                            ..
                        },
                    ) => {
                        pending.extend(
                            fields
                                .iter()
                                .zip(other_fields)
                                .map(|(&field, &other)| Pending::Values(field, other)),
                        );
                        tag == other_tag && fields.len() == other_fields.len()
                    },
                    | _ => false,
                }
            },
            | Pending::Computations(left, right) => {
                let (Some(left), Some(right)) =
                    (left_arena.computation(left), right_arena.computation(right))
                else {
                    return Agreement::Differ;
                };
                match (left, right) {
                    | (&Computation::Lambda(body), &Computation::Lambda(other)) => {
                        pending.push(Pending::Computations(body, other));
                        true
                    },
                    | (
                        &Computation::Application(head, argument),
                        &Computation::Application(other_head, other_argument),
                    ) => {
                        pending.push(Pending::Computations(head, other_head));
                        pending.push(Pending::Values(argument, other_argument));
                        true
                    },
                    | (&Computation::Return(value), &Computation::Return(other))
                    | (&Computation::Force(value), &Computation::Force(other)) => {
                        pending.push(Pending::Values(value, other));
                        true
                    },
                    | (
                        &Computation::Bind(head, body),
                        &Computation::Bind(other_head, other_body),
                    ) => {
                        pending.push(Pending::Computations(head, other_head));
                        pending.push(Pending::Computations(body, other_body));
                        true
                    },
                    | (
                        &Computation::Case {
                            scrutinee,
                            on_left,
                            on_right,
                        },
                        &Computation::Case {
                            scrutinee: other_scrutinee,
                            on_left: other_left,
                            on_right: other_right,
                        },
                    ) => {
                        pending.push(Pending::Values(scrutinee, other_scrutinee));
                        pending.push(Pending::Computations(on_left, other_left));
                        pending.push(Pending::Computations(on_right, other_right));
                        true
                    },
                    | (
                        &Computation::DataCase {
                            scrutinee,
                            ref branches,
                            ..
                        },
                        &Computation::DataCase {
                            scrutinee: other_scrutinee,
                            branches: ref other_branches,
                            ..
                        },
                    ) => {
                        pending.push(Pending::Values(scrutinee, other_scrutinee));
                        pending.extend(
                            branches
                                .iter()
                                .zip(other_branches)
                                .map(|(&branch, &other)| Pending::Computations(branch, other)),
                        );
                        branches.len() == other_branches.len()
                    },
                    | (
                        &Computation::Fixpoint { body, evidence },
                        &Computation::Fixpoint {
                            body: other_body,
                            evidence: other_evidence,
                        },
                    ) => {
                        pending.push(Pending::Computations(body, other_body));
                        evidence == other_evidence
                    },
                    | _ => false,
                }
            },
        };
        if !agrees {
            return Agreement::Differ;
        }
    }
    Agreement::Same
}

/// Independently numbered graphs agree only when their supported labels and
/// fields do.
#[test]
fn structural_equality_ignores_addresses_but_not_labels()
{
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::Side;

    use crate::generate::Integer;
    use crate::generate::integer;

    let mut left = CoreArena::new();
    let left_unit = left.value_unit();
    let left_variable = left.value_variable(Zone::Intuitionistic, 0_u32.into());
    let left_pair = left.value_pair(left_unit, left_variable);
    let left_constant = left.value_constant(0_usize.into());
    let left_integer = integer(&mut left, Integer(7));
    let left_injection = left.value_injection(Side::Left, left_unit);
    let left_lift = left.value_lift(Level::zero(), left_unit);
    let left_datatype = left.value_type_data(0_usize.into(), alloc::vec![]);
    let left_constructor = left.value_constructor(left_datatype, 1_usize.into(), alloc::vec![
        left_unit,
        left_variable
    ]);
    let mut right = CoreArena::new();
    let other_zone = right.value_variable(Zone::Linear, 0_u32.into());
    let right_unit = right.value_unit();
    let right_variable = right.value_variable(Zone::Intuitionistic, 0_u32.into());
    let right_pair = right.value_pair(right_unit, right_variable);
    let right_constant = right.value_constant(0_usize.into());
    let right_integer = integer(&mut right, Integer(7));
    let right_injection = right.value_injection(Side::Left, right_unit);
    let right_lift = right.value_lift(Level::zero(), right_unit);
    let erased = right.value_type_unknown();
    let right_constructor = right.value_constructor(erased, 1_usize.into(), alloc::vec![
        right_unit,
        right_variable
    ]);
    let changed_ordinal = right.value_constructor(erased, 0_usize.into(), alloc::vec![
        right_unit,
        right_variable
    ]);
    let changed_field =
        right.value_constructor(erased, 1_usize.into(), alloc::vec![right_unit, right_unit]);
    let dropped_field = right.value_constructor(erased, 1_usize.into(), alloc::vec![right_unit]);
    for (a, b) in [
        (left_unit, right_unit),
        (left_variable, right_variable),
        (left_pair, right_pair),
        (left_constant, right_constant),
        (left_integer, right_integer),
        (left_injection, right_injection),
        (left_lift, right_lift),
        (left_constructor, right_constructor),
    ] {
        assert_eq!(Agreement::Same, same_value(&left, a, &right, b));
    }
    for (a, b) in [
        (left_constructor, changed_ordinal),
        (left_constructor, changed_field),
        (left_constructor, dropped_field),
    ] {
        assert_eq!(Agreement::Differ, same_value(&left, a, &right, b));
    }
    let changed_index = right.value_variable(Zone::Intuitionistic, 1_u32.into());
    let changed_first = right.value_pair(right_variable, right_variable);
    let changed_second = right.value_pair(right_unit, right_unit);
    let exchanged = right.value_pair(right_variable, right_unit);
    let changed_constant = right.value_constant(1_usize.into());
    let changed_integer = integer(&mut right, Integer(8));
    let changed_side = right.value_injection(Side::Right, right_unit);
    let changed_injected_body = right.value_injection(Side::Left, right_variable);
    let changed_level = right.value_lift(
        Level::zero().succ().expect("one is representable"),
        right_unit,
    );
    let changed_lifted_body = right.value_lift(Level::zero(), right_variable);
    for (a, b) in [
        (left_variable, other_zone),
        (left_variable, changed_index),
        (left_pair, changed_first),
        (left_pair, changed_second),
        (left_pair, exchanged),
        (left_constant, changed_constant),
        (left_integer, changed_integer),
        (left_injection, changed_side),
        (left_injection, changed_injected_body),
        (left_lift, changed_level),
        (left_lift, changed_lifted_body),
        (left_unit, right_variable),
    ] {
        assert_eq!(Agreement::Differ, same_value(&left, a, &right, b));
    }
    let empty = CoreArena::new();
    assert_eq!(
        Agreement::Differ,
        same_value(&empty, left_unit, &empty, left_unit)
    );
    let unit_type = left.value_type_unit();
    let quote = left.value_quote(unit_type);
    let returned_type = left.comp_type_returner(unit_type);
    let computation_quote = left.value_quote_computation(returned_type);
    let static_lambda = left.value_static_lambda(left_variable);
    let static_application = left.value_static_application(static_lambda, left_unit);
    for root in [quote, computation_quote, static_lambda, static_application] {
        assert_eq!(Agreement::Differ, same_value(&left, root, &left, root));
    }
}

/// Every ordered computation operand affects comparison, including suspended
/// bodies.
#[test]
fn computation_comparison_preserves_every_child_role()
{
    use gandr_core_term::Zone;
    use gandr_kernel_term::FixpointEvidence;
    use gandr_kernel_term::Side;

    let mut left = CoreArena::new();
    let unit = left.value_unit();
    let variable = left.value_variable(Zone::Intuitionistic, 0_u32.into());
    let returned_unit = left.computation_return(unit);
    let returned_variable = left.computation_return(variable);
    let function = left.computation_lambda(returned_variable);
    let applied = left.computation_application(function, unit);
    let thunk = left.value_thunk(returned_unit);
    let forced = left.computation_force(thunk);
    let bound = left.computation_bind(returned_unit, returned_variable);
    let injected = left.value_injection(Side::Left, unit);
    let cased = left.computation_case(injected, returned_unit, returned_variable);
    let unit_type = left.value_type_unit();
    let motive = left.comp_type_returner(unit_type);
    let matched =
        left.computation_data_case(unit, motive, alloc::vec![returned_unit, returned_variable]);
    let recursive = left.computation_fixpoint(returned_unit, FixpointEvidence::StructuralDescent);
    let mut right = CoreArena::new();
    let other_variable = right.value_variable(Zone::Intuitionistic, 0_u32.into());
    right.computation_return(other_variable);
    let other_unit = right.value_unit();
    let other_returned_unit = right.computation_return(other_unit);
    let other_returned_variable = right.computation_return(other_variable);
    let other_function = right.computation_lambda(other_returned_variable);
    let other_applied = right.computation_application(other_function, other_unit);
    let other_thunk = right.value_thunk(other_returned_unit);
    let other_forced = right.computation_force(other_thunk);
    let other_bound = right.computation_bind(other_returned_unit, other_returned_variable);
    let other_injected = right.value_injection(Side::Left, other_unit);
    let other_cased =
        right.computation_case(other_injected, other_returned_unit, other_returned_variable);
    let erased = right.comp_type_unknown();
    let other_matched = right.computation_data_case(other_unit, erased, alloc::vec![
        other_returned_unit,
        other_returned_variable
    ]);
    let other_recursive =
        right.computation_fixpoint(other_returned_unit, FixpointEvidence::StructuralDescent);
    for (a, b) in [
        (returned_unit, other_returned_unit),
        (returned_variable, other_returned_variable),
        (function, other_function),
        (applied, other_applied),
        (forced, other_forced),
        (bound, other_bound),
        (cased, other_cased),
        (matched, other_matched),
        (recursive, other_recursive),
    ] {
        assert_eq!(Agreement::Same, same_computation(&left, a, &right, b));
    }
    assert_eq!(
        Agreement::Same,
        same_value(&left, thunk, &right, other_thunk)
    );
    let changed_thunk = right.value_thunk(other_returned_variable);
    assert_eq!(
        Agreement::Differ,
        same_value(&left, thunk, &right, changed_thunk)
    );
    let changed_scrutinee = right.value_injection(Side::Right, other_unit);
    let changed_function = right.computation_lambda(other_returned_unit);
    let changed_head = right.computation_application(other_returned_unit, other_unit);
    let changed_argument = right.computation_application(other_function, other_variable);
    let changed_force = right.computation_force(changed_thunk);
    let returned_thunk = right.computation_return(other_thunk);
    let changed_bound = right.computation_bind(other_returned_variable, other_returned_variable);
    let changed_body = right.computation_bind(other_returned_unit, other_returned_unit);
    let changed_case_scrutinee = right.computation_case(
        changed_scrutinee,
        other_returned_unit,
        other_returned_variable,
    );
    let changed_left_arm = right.computation_case(
        other_injected,
        other_returned_variable,
        other_returned_variable,
    );
    let changed_right_arm =
        right.computation_case(other_injected, other_returned_unit, other_returned_unit);
    let changed_match_scrutinee = right.computation_data_case(other_variable, erased, alloc::vec![
        other_returned_unit,
        other_returned_variable
    ]);
    let changed_branch = right.computation_data_case(other_unit, erased, alloc::vec![
        other_returned_unit,
        other_returned_unit
    ]);
    let dropped_branch =
        right.computation_data_case(other_unit, erased, alloc::vec![other_returned_unit]);
    let changed_evidence =
        right.computation_fixpoint(other_returned_unit, FixpointEvidence::Partial);
    let changed_recursive_body =
        right.computation_fixpoint(other_returned_variable, FixpointEvidence::StructuralDescent);
    for (a, b) in [
        (function, changed_function),
        (applied, changed_head),
        (applied, changed_argument),
        (forced, changed_force),
        (forced, returned_thunk),
        (bound, changed_bound),
        (bound, changed_body),
        (cased, changed_case_scrutinee),
        (cased, changed_left_arm),
        (cased, changed_right_arm),
        (matched, changed_match_scrutinee),
        (matched, changed_branch),
        (matched, dropped_branch),
        (recursive, changed_evidence),
        (recursive, changed_recursive_body),
    ] {
        assert_eq!(Agreement::Differ, same_computation(&left, a, &right, b));
    }
    let empty = CoreArena::new();
    assert_eq!(
        Agreement::Differ,
        same_computation(&empty, returned_unit, &empty, returned_unit)
    );
}
