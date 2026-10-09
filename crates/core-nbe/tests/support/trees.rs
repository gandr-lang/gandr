//! Two erased terms compared as trees.
//!
//! Erasure names a share's leg once and every occurrence of it by that one id,
//! so two erasures of one term can be different DAGs. Walking both as trees
//! compares the terms the unshared pipeline would walk. The walk reads the core
//! arenas alone and shares nothing with the duplication walk or with erasure,
//! and it costs the expansion it compares, so it is asked only of terms whose
//! expansion a test can walk.

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;

/// A core node of an evaluation family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Term
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
}

/// Whether two terms are one tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Trees
{
    /// They are.
    Same,
    /// They differ at some position.
    Different,
}

/// Whether `left` in `left_arena` and `right` in `right_arena` are one tree.
///
/// # Specification
/// - requires: both terms resolve in their arenas.
/// - ensures: [`Trees::Same`] exactly when a simultaneous walk from both roots
///   meets the same former with the same payload at every pair of positions it
///   reaches.
/// - provides: the oracle the duplication property and the spinal differentials
///   compare erasures and readbacks by.
/// - panics: when a reached node does not resolve, which the requirement
///   excludes.
pub fn same_tree(
    left_arena: &CoreArena,
    left: Term,
    right_arena: &CoreArena,
    right: Term,
) -> Trees
{
    let mut pending = Vec::from([(left, right)]);
    while let Some(pair) = pending.pop() {
        match pair {
            | (Term::Value(left), Term::Value(right)) => {
                let left = left_arena.value(left).expect("a reached value resolves");
                let right = right_arena.value(right).expect("a reached value resolves");
                match (left, right) {
                    | (&Value::Pair(first, second), &Value::Pair(other_first, other_second)) => {
                        pending.push((Term::Value(second), Term::Value(other_second)));
                        pending.push((Term::Value(first), Term::Value(other_first)));
                    },
                    | (
                        &Value::Injection(side, body),
                        &Value::Injection(other_side, other_body),
                    ) if side == other_side => {
                        pending.push((Term::Value(body), Term::Value(other_body)));
                    },
                    | (
                        &Value::Lift { ref target, body },
                        &Value::Lift {
                            target: ref other_target,
                            body: other_body,
                        },
                    ) if target == other_target => {
                        pending.push((Term::Value(body), Term::Value(other_body)));
                    },
                    | (&Value::Thunk(body), &Value::Thunk(other_body)) => {
                        pending.push((Term::Computation(body), Term::Computation(other_body)));
                    },
                    | (
                        &(Value::Variable { .. }
                        | Value::Constant(_)
                        | Value::Unit
                        | Value::Literal(_)),
                        _,
                    ) if left == right => {},
                    | _ => return Trees::Different,
                }
            },
            | (Term::Computation(left), Term::Computation(right)) => {
                let left = left_arena
                    .computation(left)
                    .expect("a reached computation resolves");
                let right = right_arena
                    .computation(right)
                    .expect("a reached computation resolves");
                match (left, right) {
                    | (&Computation::Lambda(body), &Computation::Lambda(other_body)) => {
                        pending.push((Term::Computation(body), Term::Computation(other_body)));
                    },
                    | (
                        &Computation::Application(head, argument),
                        &Computation::Application(other_head, other_argument),
                    ) => {
                        pending.push((Term::Value(argument), Term::Value(other_argument)));
                        pending.push((Term::Computation(head), Term::Computation(other_head)));
                    },
                    | (&Computation::Return(value), &Computation::Return(other_value))
                    | (&Computation::Force(value), &Computation::Force(other_value)) => {
                        pending.push((Term::Value(value), Term::Value(other_value)));
                    },
                    | (
                        &Computation::Bind(bound, body),
                        &Computation::Bind(other_bound, other_body),
                    ) => {
                        pending.push((Term::Computation(body), Term::Computation(other_body)));
                        pending.push((Term::Computation(bound), Term::Computation(other_bound)));
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
                        pending.push((Term::Computation(on_right), Term::Computation(other_right)));
                        pending.push((Term::Computation(on_left), Term::Computation(other_left)));
                        pending.push((Term::Value(scrutinee), Term::Value(other_scrutinee)));
                    },
                    | _ => return Trees::Different,
                }
            },
            | (Term::Value(_), Term::Computation(_)) | (Term::Computation(_), Term::Value(_)) => {
                return Trees::Different;
            },
        }
    }
    Trees::Same
}
