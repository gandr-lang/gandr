//! The expansion oracle: an erased term's size, counted by walking it as a
//! tree.
//!
//! Erasure names a share's leg once and every occurrence of it by that one
//! id, so an erased term is a core DAG of the overlay's size. Walked as a tree,
//! the DAG visits a leg's nodes once per occurrence: the unfolding that inlines
//! every leg at each of its occurrences, which is the term the unshared
//! pipeline walks. An opaque node's core id was already in the arena before
//! erasure, so the walk counts it once, as the leaf it is to the overlay, and
//! does not descend into it.
//!
//! The walk is independent of the measure: it reads the erased core arena and
//! nothing of the overlay, and it costs the expansion it counts, so it is
//! asked only of terms whose expansion a test can walk.

use anodized::spec;
use gandr_core_nbe::SharingMeasure;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;

/// A core node of any family, as the walk visits it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CoreNode
{
    /// A core value.
    Value(ValueId),
    /// A core computation.
    Computation(ComputationId),
    /// A core value type.
    ValueType(ValueTypeId),
    /// A core computation type.
    CompType(CompTypeId),
}

/// The five quantities of a measure, read out for comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Quantities
{
    /// The share count.
    pub shares: u64,
    /// The occurrence count.
    pub occurrences: u64,
    /// The share depth.
    pub depth: u64,
    /// The node count.
    pub nodes: u64,
    /// The expansion size.
    pub expansion: u64,
}

impl From<SharingMeasure> for Quantities
{
    /// Read each quantity of `measured` out.
    ///
    /// # Specification
    /// trivial.
    fn from(measured: SharingMeasure) -> Self
    {
        Self {
            shares: u64::from(measured.shares()),
            occurrences: u64::from(measured.occurrences()),
            depth: u64::from(measured.depth()),
            nodes: u64::from(measured.nodes()),
            expansion: u64::from(measured.expansion()),
        }
    }
}

/// How many nodes an erased term holds walked as a tree.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unfolded(pub u64);

/// Count the nodes of the tree `root` unfolds to in `erased`, each node
/// `before` already held counting once as a leaf.
///
/// # Specification
/// - requires: `erased` is `before` with one erasure's nodes appended, and
///   `root` is that erasure's result.
/// - ensures: one count per visit of a walk from `root` that descends into
///   every child of every node erasure minted, once per path that reaches it,
///   and stops at every node `before` holds.
/// - provides: the oracle the measure's expansion size is compared with.
/// - panics: when a reached node does not resolve in `erased`, which the
///   requirement excludes, or when the count passes its counter, which no
///   walkable term reaches.
///
/// # Adequacy
/// - hypothesis: L3 — the erased arena extends the entry arena and the finite
///   tree fits the counter. A pre-existing root counts exactly once; a newly
///   minted leaf counts once, and a composite contributes at least itself and
///   each immediate child. The independent overlay measures observe the full
///   count, including repeated DAG paths and opaque bind bases; the local
///   predicate does not replay that walk.
/// - witness: `deep_evaluation::deep_evaluation::the_deep_evaluation_cases_measure_as_their_erasure_inside_a_small_stack`
/// - witness: `deep_readback::deep_readback::the_deep_readback_cases_measure_as_their_erasure_inside_a_small_stack`
/// - witness: `measure::measure::the_expansion_size_is_what_the_unshared_walk_visits`
#[spec(
    requires: match root {
        CoreNode::Value(id) => erased.value(id).is_some(),
        CoreNode::Computation(id) => erased.computation(id).is_some(),
        CoreNode::ValueType(id) => erased.value_type(id).is_some(),
        CoreNode::CompType(id) => erased.comp_type(id).is_some(),
    },
    ensures: |ret| {
        let opaque = match root {
            CoreNode::Value(id) => before.value(id).is_some(),
            CoreNode::Computation(id) => before.computation(id).is_some(),
            CoreNode::ValueType(id) => before.value_type(id).is_some(),
            CoreNode::CompType(id) => before.comp_type(id).is_some(),
        };
        if opaque { return ret.0 == 1; }
        let minimum = match root {
            CoreNode::Value(id) => {
                let Some(node) = erased.value(id) else { return false; };
                match *node {
                    Value::Constructor { ref fields, .. } => 2_u64.saturating_add(u64::try_from(fields.len()).unwrap_or(u64::MAX)),
                    Value::Record(ref fields) => 1_u64.saturating_add(u64::try_from(fields.len()).unwrap_or(u64::MAX)),
                    Value::Reify(ref frames) => 1_u64.checked_add(u64::try_from(frames.iter().filter(|frame| !matches!(frame, gandr_core_term::control::StackFrame::Project(_))).count()).expect("walkable frame arity")).expect("walkable frame arity"),
                    Value::ListNil | Value::Primitive { .. } | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Hole(_) => 1,
                    Value::Tuple(ref components) => 1_u64.saturating_add(u64::try_from(components.len()).unwrap_or(u64::MAX)),
                    Value::Recorded(ref moves) => 1_u64.saturating_add(u64::try_from(moves.iter().filter(|movement| matches!(movement, gandr_core_term::session::RecordedMove::Sent(_) | gandr_core_term::session::RecordedMove::Received(_))).count()).unwrap_or(u64::MAX)),
                    Value::ListCons(..) | Value::PathProduct(..) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::StaticApplication(_, _) | Value::SessionRelated { .. } | Value::Then(..) | Value::FlowProduct(..) | Value::FunctionFlow(..) => 3,
                    Value::PathEquiv { .. } => 4,
                    Value::PathRefl(_) | Value::Here(_) | Value::Stay(_) | Value::Forward(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::StaticLambda(_) | Value::Injection(_, _) | Value::Lift { .. } | Value::Thunk(_) | Value::Quote(_) | Value::QuoteComputation(_) | Value::Mark { .. } => 2,
                }
            },
            CoreNode::Computation(id) => {
                let Some(node) = erased.computation(id) else { return false; };
                match *node {
                    Computation::DataCase { ref branches, .. } => 3_u64.saturating_add(u64::try_from(branches.len()).unwrap_or(u64::MAX)),
                    Computation::Perform { ref signature, .. } => 2_u64.checked_add(u64::try_from(signature.types().count()).expect("walkable interface arity")).expect("walkable interface arity"),
                    Computation::Handle { ref signature, ref clauses, .. } | Computation::Scope { ref signature, ref clauses, .. } => 3_u64.checked_add(u64::try_from(signature.types().count()).expect("walkable interface arity")).and_then(|count| count.checked_add(u64::try_from(clauses.len()).expect("walkable clause arity"))).expect("walkable handler arity"),
                    Computation::Exercise { ref signature, .. } => 3_u64.checked_add(u64::try_from(signature.types().count()).expect("walkable interface arity")).expect("walkable interface arity"),
                    Computation::Resume(..) | Computation::Split { .. } | Computation::With(..) | Computation::Transport(..) | Computation::Application(_, _) | Computation::Bind(_, _) => 3,
                    Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Reset(_) | Computation::Shift(_) | Computation::Project(..) | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Return(_) | Computation::Force(_) | Computation::Mark { .. } => 2,
                    Computation::Hole(_) => 1,
                    Computation::ListFold { .. } | Computation::TelescopeTransport { .. } => 6,
                    Computation::Primitive { arguments, .. } => if arguments.len() == 1 { 2 } else { 3 },
                    Computation::Case { .. } | Computation::PathTransport { .. } | Computation::Ride { .. } => 4,
                    Computation::Session(ref action) => 1_u64.saturating_add(u64::try_from(action.values().count().saturating_add(action.computations().count()).saturating_add(action.value_types().count())).unwrap_or(u64::MAX)),
                }
            },
            CoreNode::ValueType(id) => {
                let Some(node) = erased.value_type(id) else { return false; };
                match *node {
                    ValueType::Data { ref arguments, .. } => 1_u64.saturating_add(u64::try_from(arguments.len()).unwrap_or(u64::MAX)),
                    ValueType::Record(ref fields) => 1_u64.saturating_add(u64::try_from(fields.len()).unwrap_or(u64::MAX)),
                    ValueType::Product(ref parts) | ValueType::Sum(ref parts) => 1_u64.saturating_add(u64::try_from(parts.len()).unwrap_or(u64::MAX)),
                    ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) | ValueType::Unknown => 1,
                    ValueType::Session(ref session) => 1_u64.saturating_add(u64::try_from(session.payloads().len()).unwrap_or(u64::MAX)),
                    ValueType::Capability { ref authority, .. } => 1_u64.checked_add(u64::try_from(authority.types().count()).expect("walkable authority arity")).expect("walkable authority arity"),
                    ValueType::Stack { .. } | ValueType::PathUniverse(..) | ValueType::StaticPi { .. } | ValueType::Sigma { .. } => 3,
                    ValueType::Path { .. } | ValueType::Flow { .. } => 4,
                    ValueType::List(_) | ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::Run(_) => 2,
                }
            },
            CoreNode::CompType(id) => {
                let Some(node) = erased.comp_type(id) else { return false; };
                match *node {
                    CompType::Returner { ref effects, .. } => 2_u64.checked_add(u64::try_from(effects.types().count()).expect("walkable row arity fits the counter")).expect("walkable row arity fits the counter"),
                    CompType::Element { .. } => 2,
                    CompType::With(..) | CompType::Arrow { .. } | CompType::Pi { .. } => 3,
                    CompType::Unknown => 1,
                }
            },
        };
        if minimum == 1 { ret.0 == 1 } else { ret.0 >= minimum }
    }
)]
pub fn unfolded(
    erased: &CoreArena,
    root: CoreNode,
    before: &CoreArena,
) -> Unfolded
{
    let mut visited = 0_u64;
    let mut pending = Vec::from([root]);
    while let Some(node) = pending.pop() {
        visited = visited
            .checked_add(1)
            .expect("a walkable unfolding fits the counter");
        let opaque = match node {
            CoreNode::Value(id) => before.value(id).is_some(),
            CoreNode::Computation(id) => before.computation(id).is_some(),
            CoreNode::ValueType(id) => before.value_type(id).is_some(),
            CoreNode::CompType(id) => before.comp_type(id).is_some(),
        };
        if opaque {
            continue;
        }
        match node {
            CoreNode::Value(id) => match *erased.value(id).expect("an erased value resolves") {
                Value::Constructor {
                    datatype,
                    ref fields,
                    ..
                } => {
                    pending.push(CoreNode::ValueType(datatype));
                    pending.extend(fields.iter().copied().map(CoreNode::Value));
                },
                Value::Record(ref fields) => {
                    pending.extend(fields.values().copied().map(CoreNode::Value));
                },
                Value::Reify(ref frames) => {
                    pending.extend(frames.iter().filter_map(|frame| match *frame {
                        gandr_core_term::control::StackFrame::Apply(value) => {
                            Some(CoreNode::Value(value))
                        },
                        gandr_core_term::control::StackFrame::Bind(body) => {
                            Some(CoreNode::Computation(body))
                        },
                        gandr_core_term::control::StackFrame::Project(_) => None,
                    }));
                },
                Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                } => pending.extend([
                    CoreNode::ValueType(path_type),
                    CoreNode::Value(forward),
                    CoreNode::Value(backward),
                ]),
                Value::Primitive { .. }
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::ListNil
                | Value::Literal(_)
                | Value::Hole(_) => {},
                Value::Tuple(ref components) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| CoreNode::Value(component)),
                    );
                },
                Value::Recorded(ref moves) => {
                    pending.extend(moves.iter().filter_map(|movement| match *movement {
                        gandr_core_term::session::RecordedMove::Sent(payload)
                        | gandr_core_term::session::RecordedMove::Received(payload) => {
                            Some(CoreNode::Value(payload))
                        },
                        gandr_core_term::session::RecordedMove::Selected(_)
                        | gandr_core_term::session::RecordedMove::Offered(_)
                        | gandr_core_term::session::RecordedMove::Closed => None,
                    }));
                },
                Value::PathProduct(first, second)
                | Value::Funext(first, second)
                | Value::Equiv(first, second)
                | Value::Then(first, second)
                | Value::FlowProduct(first, second)
                | Value::FunctionFlow(first, second)
                | Value::SessionRelated {
                    source: first,
                    target: second,
                    ..
                }
                | Value::Ua {
                    forward: first,
                    backward: second,
                    ..
                }
                | Value::ListCons(first, second)
                | Value::StaticApplication(first, second) => {
                    pending.push(CoreNode::Value(first));
                    pending.push(CoreNode::Value(second));
                },
                Value::StaticLambda(body) => pending.push(CoreNode::Value(body)),
                Value::PathRefl(body)
                | Value::Here(body)
                | Value::Stay(body)
                | Value::Forward(body)
                | Value::Injection(_, body)
                | Value::Lift { body, .. }
                | Value::Mark { body, .. } => {
                    pending.push(CoreNode::Value(body));
                },
                Value::Thunk(body)
                | Value::Returned(body)
                | Value::Nested(body)
                | Value::Run(body) => {
                    pending.push(CoreNode::Computation(body));
                },
                Value::Quote(quoted) => pending.push(CoreNode::ValueType(quoted)),
                Value::QuoteComputation(quoted) => pending.push(CoreNode::CompType(quoted)),
            },
            CoreNode::Computation(id) => {
                match *erased
                    .computation(id)
                    .expect("an erased computation resolves")
                {
                    Computation::DataCase {
                        scrutinee,
                        motive,
                        ref branches,
                    } => {
                        pending.extend([CoreNode::Value(scrutinee), CoreNode::CompType(motive)]);
                        pending.extend(branches.iter().copied().map(CoreNode::Computation));
                    },
                    Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _) => {
                        pending.push(CoreNode::Value(record));
                    },
                    Computation::Perform {
                        payload,
                        ref signature,
                        ..
                    } => {
                        pending.push(CoreNode::Value(payload));
                        pending.extend(signature.types().map(CoreNode::ValueType));
                    },
                    Computation::Exercise {
                        capability,
                        payload,
                        ref signature,
                        ..
                    } => {
                        pending.extend([CoreNode::Value(capability), CoreNode::Value(payload)]);
                        pending.extend(signature.types().map(CoreNode::ValueType));
                    },
                    Computation::Handle {
                        subject,
                        on_return,
                        ref signature,
                        ref clauses,
                    }
                    | Computation::Scope {
                        subject,
                        on_return,
                        ref signature,
                        ref clauses,
                    } => {
                        pending.extend([
                            CoreNode::Computation(subject),
                            CoreNode::Computation(on_return),
                        ]);
                        pending.extend(signature.types().map(CoreNode::ValueType));
                        pending.extend(
                            clauses
                                .iter()
                                .map(|clause| CoreNode::Computation(clause.body)),
                        );
                    },
                    Computation::Split {
                        scrutinee,
                        motive: gandr_core_term::SplitMotive::Scrutinee(motive),
                        body,
                        ..
                    } => pending.extend([
                        CoreNode::Value(scrutinee),
                        CoreNode::CompType(motive),
                        CoreNode::Computation(body),
                    ]),
                    Computation::Resume(stack, body)
                    | Computation::Split {
                        scrutinee: stack,
                        body,
                        ..
                    } => {
                        pending.extend([CoreNode::Value(stack), CoreNode::Computation(body)]);
                    },
                    Computation::With(first, second) => pending
                        .extend([CoreNode::Computation(first), CoreNode::Computation(second)]),
                    Computation::Reset(body)
                    | Computation::Shift(body)
                    | Computation::Project(_, body)
                    | Computation::Lambda(body) => pending.push(CoreNode::Computation(body)),
                    Computation::ListFold {
                        element,
                        result,
                        list,
                        on_nil,
                        on_cons,
                    } => pending.extend([
                        CoreNode::ValueType(element),
                        CoreNode::ValueType(result),
                        CoreNode::Value(list),
                        CoreNode::Computation(on_nil),
                        CoreNode::Computation(on_cons),
                    ]),
                    Computation::Primitive { arguments, .. } => {
                        pending.extend(arguments.iter().copied().map(CoreNode::Value));
                    },
                    Computation::Transport(path, value) => {
                        pending.extend([CoreNode::Value(path), CoreNode::Value(value)]);
                    },
                    Computation::PathTransport {
                        motive,
                        path,
                        value,
                    }
                    | Computation::Ride {
                        motive,
                        flow: path,
                        value,
                    } => pending.extend([
                        CoreNode::ValueType(motive),
                        CoreNode::Value(path),
                        CoreNode::Value(value),
                    ]),
                    Computation::TelescopeTransport {
                        motive,
                        path,
                        start,
                        over,
                        value,
                    } => pending.extend([
                        CoreNode::CompType(motive),
                        CoreNode::Value(path),
                        CoreNode::Value(start),
                        CoreNode::Value(over),
                        CoreNode::Value(value),
                    ]),
                    Computation::Mark { body, .. } | Computation::Fixpoint { body, .. } => {
                        pending.push(CoreNode::Computation(body));
                    },
                    Computation::Hole(_) => {},
                    Computation::Application(head, argument) => {
                        pending.push(CoreNode::Computation(head));
                        pending.push(CoreNode::Value(argument));
                    },
                    Computation::Return(value) | Computation::Force(value) => {
                        pending.push(CoreNode::Value(value));
                    },
                    Computation::Bind(bound, body) => {
                        pending.push(CoreNode::Computation(bound));
                        pending.push(CoreNode::Computation(body));
                    },
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        pending.push(CoreNode::Value(scrutinee));
                        pending
                            .extend(branches.iter().map(|&branch| CoreNode::Computation(branch)));
                    },
                    Computation::Session(ref action) => {
                        pending.extend(action.value_types().map(CoreNode::ValueType));
                        pending.extend(action.values().map(CoreNode::Value));
                        pending.extend(action.computations().map(CoreNode::Computation));
                    },
                }
            },
            CoreNode::ValueType(id) => {
                match *erased
                    .value_type(id)
                    .expect("an erased value type resolves")
                {
                    ValueType::Data { ref arguments, .. } => {
                        pending.extend(arguments.iter().copied().map(CoreNode::Value));
                    },
                    ValueType::Record(ref fields) => {
                        pending.extend(fields.values().copied().map(CoreNode::ValueType));
                    },
                    ValueType::Session(ref session) => {
                        pending.extend(session.payloads().iter().copied().map(CoreNode::ValueType));
                    },
                    ValueType::Stack { input, output } => {
                        pending.extend([CoreNode::CompType(input), CoreNode::CompType(output)]);
                    },
                    ValueType::PathUniverse(source, target) => {
                        pending.extend([CoreNode::Value(source), CoreNode::Value(target)]);
                    },
                    ValueType::Path {
                        carrier,
                        left,
                        right,
                    }
                    | ValueType::Flow {
                        carrier,
                        source: left,
                        target: right,
                    } => pending.extend([
                        CoreNode::ValueType(carrier),
                        CoreNode::Value(left),
                        CoreNode::Value(right),
                    ]),
                    ValueType::Run(session) => pending.push(CoreNode::Value(session)),
                    ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                        pending.extend(parts.iter().map(|&part| CoreNode::ValueType(part)));
                    },
                    ValueType::Base(_)
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_)
                    | ValueType::Unknown => {},
                    ValueType::Capability { ref authority, .. } => {
                        pending.extend(authority.types().map(CoreNode::ValueType));
                    },
                    ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    }
                    | ValueType::Sigma { first, second } => {
                        pending.push(CoreNode::ValueType(first));
                        pending.push(CoreNode::ValueType(second));
                    },
                    ValueType::Thunk(body) => pending.push(CoreNode::CompType(body)),
                    ValueType::List(inner) | ValueType::Lift { inner, .. } => {
                        pending.push(CoreNode::ValueType(inner));
                    },
                    ValueType::Element { code, .. } => pending.push(CoreNode::Value(code)),
                }
            },
            CoreNode::CompType(id) => {
                match *erased
                    .comp_type(id)
                    .expect("an erased computation type resolves")
                {
                    CompType::With(first, second) => {
                        pending.extend([CoreNode::CompType(first), CoreNode::CompType(second)]);
                    },
                    CompType::Returner {
                        result,
                        ref effects,
                    } => {
                        pending.push(CoreNode::ValueType(result));
                        pending.extend(effects.types().map(CoreNode::ValueType));
                    },
                    CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => {
                        pending.push(CoreNode::ValueType(domain));
                        pending.push(CoreNode::CompType(codomain));
                    },
                    CompType::Element { code, .. } => pending.push(CoreNode::Value(code)),
                    CompType::Unknown => {},
                }
            },
        }
    }
    Unfolded(visited)
}
