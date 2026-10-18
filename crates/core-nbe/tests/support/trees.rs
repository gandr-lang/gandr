//! Two erased terms compared as trees.
//!
//! Erasure names a share's leg once and every occurrence of it by that one id,
//! so two erasures of one term can be different DAGs. Walking both as trees
//! compares the terms the unshared pipeline would walk. The walk reads the core
//! arenas alone and shares nothing with the duplication walk or with erasure,
//! and it costs the expansion it compares, so it is asked only of terms whose
//! expansion a test can walk.

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;

/// A core node in one of the four term and type families.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Term
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
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
/// - requires: the reachable graphs are finite and acyclic. Missing ids are
///   admitted and compare as different, including identical missing ids.
/// - ensures: [`Trees::Same`] exactly when the trees have the same formers,
///   ordered children and payloads. Static terms, native paths and both quoted
///   type families are traversed, not compared by their arena-local ids.
/// - provides: one structural oracle for readback and duplication witnesses.
/// - fails: a missing node or mismatched family is [`Trees::Different`].
/// - panics: none.
/// - intension: depth costs a heap worklist; sharing is compared by expansion.
///
/// # Adequacy
/// - hypothesis: L3 — finite syntax may share children, cross quoted type
///   families, use distinct arena ids or contain missing references. Exact leaf
///   comparison and root-family guards exclude permissive comparisons;
///   independently built positive and negative terms distinguish wrong
///   payloads, swapped children, omitted static formers and id-based equality.
/// - witness: `tests::readback_terms::the_comparator_separates_terms_it_is_asked_to_pin`
/// - witness: `tests::readback_terms::the_comparator_reads_static_formers`
/// - witness: `tests::readback_terms::the_comparator_descends_into_quoted_type_families`
/// - witness: `tests::readback_terms::native_tree_comparison_preserves_endpoints_maps_and_evidence`
#[spec(
    ensures: |ret| match (left, right) {
        (Term::Value(left), Term::Value(right)) => match (left_arena.value(left), right_arena.value(right)) {
            (Some(a), Some(b)) => match *a {
                Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) => (ret == Trees::Same) == (a == b),
                Value::Tuple(ref components) if components.is_empty() => (ret == Trees::Same) == (a == b),
                Value::Univalence(..) |
                Value::Primitive { .. } | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Tuple(_) | Value::Injection(..) | Value::ListNil | Value::ListCons(..) | Value::Thunk(_) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..) | Value::Constructor { .. } | Value::Record(_) | Value::Hole(_) | Value::Mark { .. } | Value::Reify(_) => ret == Trees::Different || core::mem::discriminant(a) == core::mem::discriminant(b),
            },
            _ => ret == Trees::Different,
        },
        (Term::Computation(left), Term::Computation(right)) => match (left_arena.computation(left), right_arena.computation(right)) {
            (Some(a), Some(b)) => ret == Trees::Different || core::mem::discriminant(a) == core::mem::discriminant(b),
            _ => ret == Trees::Different,
        },
        (Term::ValueType(left), Term::ValueType(right)) => match (left_arena.value_type(left), right_arena.value_type(right)) {
            (Some(a), Some(b)) => match *a {
                ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) => (ret == Trees::Same) == (a == b),
                ValueType::Data { .. } | ValueType::Record(_) | ValueType::PathUniverse(..) | ValueType::Path { .. } | ValueType::Flow { .. } | ValueType::Run(_) | ValueType::Product(_) | ValueType::Sigma { .. } | ValueType::Sum(_) | ValueType::List(_) | ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::StaticPi { .. } | ValueType::Unknown | ValueType::Stack { .. } | ValueType::Session(_) | ValueType::Capability { .. } | ValueType::Staged { .. } | ValueType::World(_) => ret == Trees::Different || core::mem::discriminant(a) == core::mem::discriminant(b),
            },
            _ => ret == Trees::Different,
        },
        (Term::CompType(left), Term::CompType(right)) => match (left_arena.comp_type(left), right_arena.comp_type(right)) {
            (Some(a), Some(b)) => ret == Trees::Different || core::mem::discriminant(a) == core::mem::discriminant(b),
            _ => ret == Trees::Different,
        },
        _ => ret == Trees::Different,
    }
)]
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
            (Term::Value(left), Term::Value(right)) => {
                let (Some(left), Some(right)) = (left_arena.value(left), right_arena.value(right))
                else {
                    return Trees::Different;
                };
                match (left, right) {
                    (
                        &Value::PathEquiv {
                            path_type,
                            forward,
                            backward,
                            ref evidence,
                        },
                        &Value::PathEquiv {
                            path_type: other_type,
                            forward: other_forward,
                            backward: other_backward,
                            evidence: ref other_evidence,
                        },
                    ) if evidence == other_evidence => {
                        pending.push((Term::Value(backward), Term::Value(other_backward)));
                        pending.push((Term::Value(forward), Term::Value(other_forward)));
                        pending.push((Term::ValueType(path_type), Term::ValueType(other_type)));
                    },
                    (
                        &Value::PathProduct(first, second),
                        &Value::PathProduct(other_first, other_second),
                    )
                    | (
                        &Value::ListCons(first, second),
                        &Value::ListCons(other_first, other_second),
                    )
                    | (
                        &Value::StaticApplication(first, second),
                        &Value::StaticApplication(other_first, other_second),
                    ) => {
                        pending.push((Term::Value(second), Term::Value(other_second)));
                        pending.push((Term::Value(first), Term::Value(other_first)));
                    },
                    (&Value::Injection(side, body), &Value::Injection(other_side, other_body))
                        if side == other_side =>
                    {
                        pending.push((Term::Value(body), Term::Value(other_body)));
                    },
                    (
                        &Value::Lift { ref target, body },
                        &Value::Lift {
                            target: ref other_target,
                            body: other_body,
                        },
                    ) if target == other_target => {
                        pending.push((Term::Value(body), Term::Value(other_body)));
                    },
                    (&Value::PathRefl(body), &Value::PathRefl(other_body))
                    | (&Value::StaticLambda(body), &Value::StaticLambda(other_body)) => {
                        pending.push((Term::Value(body), Term::Value(other_body)));
                    },
                    (&Value::Thunk(body), &Value::Thunk(other_body)) => {
                        pending.push((Term::Computation(body), Term::Computation(other_body)));
                    },
                    (&Value::Quote(body), &Value::Quote(other_body)) => {
                        pending.push((Term::ValueType(body), Term::ValueType(other_body)));
                    },
                    (&Value::QuoteComputation(body), &Value::QuoteComputation(other_body)) => {
                        pending.push((Term::CompType(body), Term::CompType(other_body)));
                    },
                    (&Value::Tuple(ref components), &Value::Tuple(ref others))
                        if components.len() == others.len() =>
                    {
                        pending.extend(components.iter().zip(others.iter()).rev().map(
                            |(&component, &other)| (Term::Value(component), Term::Value(other)),
                        ));
                    },
                    (
                        &(Value::Variable { .. }
                        | Value::Constant(_)
                        | Value::ListNil
                        | Value::Literal(_)),
                        _,
                    ) if left == right => {},
                    _ => return Trees::Different,
                }
            },
            (Term::Computation(left), Term::Computation(right)) => {
                let (Some(left), Some(right)) =
                    (left_arena.computation(left), right_arena.computation(right))
                else {
                    return Trees::Different;
                };
                match (left, right) {
                    (
                        &Computation::ListFold {
                            element,
                            result,
                            list,
                            on_nil,
                            on_cons,
                        },
                        &Computation::ListFold {
                            element: other_element,
                            result: other_result,
                            list: other_list,
                            on_nil: other_nil,
                            on_cons: other_cons,
                        },
                    ) => pending.extend([
                        (Term::ValueType(element), Term::ValueType(other_element)),
                        (Term::ValueType(result), Term::ValueType(other_result)),
                        (Term::Value(list), Term::Value(other_list)),
                        (Term::Computation(on_nil), Term::Computation(other_nil)),
                        (Term::Computation(on_cons), Term::Computation(other_cons)),
                    ]),
                    (
                        &Computation::Transport(path, value),
                        &Computation::Transport(other_path, other_value),
                    ) => {
                        pending.push((Term::Value(value), Term::Value(other_value)));
                        pending.push((Term::Value(path), Term::Value(other_path)));
                    },
                    (&Computation::Lambda(body), &Computation::Lambda(other_body)) => {
                        pending.push((Term::Computation(body), Term::Computation(other_body)));
                    },
                    (
                        &Computation::Application(head, argument),
                        &Computation::Application(other_head, other_argument),
                    ) => {
                        pending.push((Term::Value(argument), Term::Value(other_argument)));
                        pending.push((Term::Computation(head), Term::Computation(other_head)));
                    },
                    (&Computation::Return(value), &Computation::Return(other_value))
                    | (&Computation::Force(value), &Computation::Force(other_value)) => {
                        pending.push((Term::Value(value), Term::Value(other_value)));
                    },
                    (
                        &Computation::Bind(bound, body),
                        &Computation::Bind(other_bound, other_body),
                    ) => {
                        pending.push((Term::Computation(body), Term::Computation(other_body)));
                        pending.push((Term::Computation(bound), Term::Computation(other_bound)));
                    },
                    (
                        &Computation::Case {
                            scrutinee,
                            ref branches,
                        },
                        &Computation::Case {
                            scrutinee: other_scrutinee,
                            branches: ref others,
                        },
                    ) if branches.len() == others.len() => {
                        pending.extend(branches.iter().zip(others.iter()).rev().map(
                            |(&branch, &other)| {
                                (Term::Computation(branch), Term::Computation(other))
                            },
                        ));
                        pending.push((Term::Value(scrutinee), Term::Value(other_scrutinee)));
                    },
                    _ => return Trees::Different,
                }
            },
            (Term::ValueType(left), Term::ValueType(right)) => {
                let (Some(left), Some(right)) =
                    (left_arena.value_type(left), right_arena.value_type(right))
                else {
                    return Trees::Different;
                };
                match (left, right) {
                    (&ValueType::List(element), &ValueType::List(other_element)) => {
                        pending.push((Term::ValueType(element), Term::ValueType(other_element)));
                    },
                    (
                        &ValueType::PathUniverse(source, target),
                        &ValueType::PathUniverse(other_source, other_target),
                    ) => {
                        pending.push((Term::Value(target), Term::Value(other_target)));
                        pending.push((Term::Value(source), Term::Value(other_source)));
                    },
                    (&ValueType::Product(ref parts), &ValueType::Product(ref other_parts))
                    | (&ValueType::Sum(ref parts), &ValueType::Sum(ref other_parts))
                        if parts.len() == other_parts.len() =>
                    {
                        pending.extend(parts.iter().zip(other_parts.iter()).rev().map(
                            |(&part, &other)| (Term::ValueType(part), Term::ValueType(other)),
                        ));
                    },
                    (
                        &ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        },
                        &ValueType::StaticPi {
                            domain: other_first,
                            codomain: other_second,
                        },
                    ) => {
                        pending.push((Term::ValueType(second), Term::ValueType(other_second)));
                        pending.push((Term::ValueType(first), Term::ValueType(other_first)));
                    },
                    (&ValueType::Thunk(body), &ValueType::Thunk(other_body)) => {
                        pending.push((Term::CompType(body), Term::CompType(other_body)));
                    },
                    (
                        &ValueType::Lift { inner, ref target },
                        &ValueType::Lift {
                            inner: other_inner,
                            target: ref other_target,
                        },
                    ) if target == other_target => {
                        pending.push((Term::ValueType(inner), Term::ValueType(other_inner)));
                    },
                    (
                        &ValueType::Element { code, ref target },
                        &ValueType::Element {
                            code: other_code,
                            target: ref other_target,
                        },
                    ) if target == other_target => {
                        pending.push((Term::Value(code), Term::Value(other_code)));
                    },
                    (
                        &(ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_)),
                        _,
                    ) if left == right => {},
                    _ => return Trees::Different,
                }
            },
            (Term::CompType(left), Term::CompType(right)) => {
                let (Some(left), Some(right)) =
                    (left_arena.comp_type(left), right_arena.comp_type(right))
                else {
                    return Trees::Different;
                };
                match (left, right) {
                    (
                        &CompType::Returner {
                            result: value,
                            effects: ref left,
                        },
                        &CompType::Returner {
                            result: other_value,
                            effects: ref right,
                        },
                    ) => {
                        if left.signatures().len() != right.signatures().len() {
                            return Trees::Different;
                        }
                        for (left, right) in left.signatures().zip(right.signatures()) {
                            if left.name() != right.name()
                                || left.operations().len() != right.operations().len()
                            {
                                return Trees::Different;
                            }
                            for (left, right) in left.operations().zip(right.operations()) {
                                if left.name != right.name {
                                    return Trees::Different;
                                }
                                pending.extend([
                                    (
                                        Term::ValueType(left.payload),
                                        Term::ValueType(right.payload),
                                    ),
                                    (Term::ValueType(left.reply), Term::ValueType(right.reply)),
                                ]);
                            }
                        }
                        pending.push((Term::ValueType(value), Term::ValueType(other_value)));
                    },
                    (
                        &CompType::Arrow { domain, codomain },
                        &CompType::Arrow {
                            domain: other_domain,
                            codomain: other_codomain,
                        },
                    )
                    | (
                        &CompType::Pi { domain, codomain },
                        &CompType::Pi {
                            domain: other_domain,
                            codomain: other_codomain,
                        },
                    ) => {
                        pending.push((Term::CompType(codomain), Term::CompType(other_codomain)));
                        pending.push((Term::ValueType(domain), Term::ValueType(other_domain)));
                    },
                    (
                        &CompType::Element { code, ref target },
                        &CompType::Element {
                            code: other_code,
                            target: ref other_target,
                        },
                    ) if target == other_target => {
                        pending.push((Term::Value(code), Term::Value(other_code)));
                    },
                    _ => return Trees::Different,
                }
            },
            _ => return Trees::Different,
        }
    }
    Trees::Same
}
