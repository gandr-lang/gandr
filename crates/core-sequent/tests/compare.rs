//! Structural equality of core terms across two arenas.
//!
//! The core's derived equality compares child ids, which two arenas assign
//! independently; these walks compare what the ids name instead, node by node,
//! over an explicit stack.

use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;

/// Whether two terms agree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Agreement
{
    /// Every node agrees.
    Same,
    /// Some node differs, or an id dangles.
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

/// Compare two computations structurally.
///
/// # Specification
/// trivial.
pub fn same_computation(
    left_arena: &CoreArena,
    left: ComputationId,
    right_arena: &CoreArena,
    right: ComputationId,
) -> Agreement
{
    walk(left_arena, right_arena, Pending::Computations(left, right))
}

/// Compare two values structurally.
///
/// # Specification
/// trivial.
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
/// trivial.
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
