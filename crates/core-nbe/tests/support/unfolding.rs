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
            CoreNode::Value(id) => match erased.value(id) {
                Some(&Value::PathEquiv { .. }) => 4,
                Some(&(Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_))) => 1,
                Some(&(Value::PathProduct(..) | Value::Pair(_, _) | Value::StaticApplication(_, _))) => 3,
                Some(&(Value::PathRefl(_) | Value::StaticLambda(_) | Value::Injection(_, _) | Value::Lift { .. } | Value::Thunk(_) | Value::Quote(_) | Value::QuoteComputation(_))) => 2,
                None => return false,
            },
            CoreNode::Computation(id) => match erased.computation(id) {
                Some(&(Computation::Lambda(_) | Computation::Return(_) | Computation::Force(_))) => 2,
                Some(&(Computation::Transport(..) | Computation::Application(_, _) | Computation::Bind(_, _))) => 3,
                Some(&Computation::Case { .. }) => 4,
                None => return false,
            },
            CoreNode::ValueType(id) => match erased.value_type(id) {
                Some(&(ValueType::Base(_) | ValueType::Unit | ValueType::Universe { .. } | ValueType::Abstract(_))) => 1,
                Some(&(ValueType::PathUniverse(..) | ValueType::Product(_, _) | ValueType::Sum(_, _) | ValueType::StaticPi { .. })) => 3,
                Some(&(ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. })) => 2,
                None => return false,
            },
            CoreNode::CompType(id) => match erased.comp_type(id) {
                Some(&(CompType::Returner(_) | CompType::Element { .. })) => 2,
                Some(&(CompType::Arrow { .. } | CompType::Pi { .. })) => 3,
                None => return false,
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
            | CoreNode::Value(id) => before.value(id).is_some(),
            | CoreNode::Computation(id) => before.computation(id).is_some(),
            | CoreNode::ValueType(id) => before.value_type(id).is_some(),
            | CoreNode::CompType(id) => before.comp_type(id).is_some(),
        };
        if opaque {
            continue;
        }
        match node {
            | CoreNode::Value(id) => match *erased.value(id).expect("an erased value resolves") {
                | Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                } => pending.extend([
                    CoreNode::ValueType(path_type),
                    CoreNode::Value(forward),
                    CoreNode::Value(backward),
                ]),
                | Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_) => {
                },
                | Value::PathProduct(first, second)
                | Value::Pair(first, second)
                | Value::StaticApplication(first, second) => {
                    pending.push(CoreNode::Value(first));
                    pending.push(CoreNode::Value(second));
                },
                | Value::StaticLambda(body) => pending.push(CoreNode::Value(body)),
                | Value::PathRefl(body) | Value::Injection(_, body) | Value::Lift { body, .. } => {
                    pending.push(CoreNode::Value(body));
                },
                | Value::Thunk(body) => pending.push(CoreNode::Computation(body)),
                | Value::Quote(quoted) => pending.push(CoreNode::ValueType(quoted)),
                | Value::QuoteComputation(quoted) => pending.push(CoreNode::CompType(quoted)),
            },
            | CoreNode::Computation(id) => {
                match *erased
                    .computation(id)
                    .expect("an erased computation resolves")
                {
                    | Computation::Transport(path, value) => {
                        pending.extend([CoreNode::Value(path), CoreNode::Value(value)]);
                    },
                    | Computation::Lambda(body) => pending.push(CoreNode::Computation(body)),
                    | Computation::Application(head, argument) => {
                        pending.push(CoreNode::Computation(head));
                        pending.push(CoreNode::Value(argument));
                    },
                    | Computation::Return(value) | Computation::Force(value) => {
                        pending.push(CoreNode::Value(value));
                    },
                    | Computation::Bind(bound, body) => {
                        pending.push(CoreNode::Computation(bound));
                        pending.push(CoreNode::Computation(body));
                    },
                    | Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => {
                        pending.push(CoreNode::Value(scrutinee));
                        pending.push(CoreNode::Computation(on_left));
                        pending.push(CoreNode::Computation(on_right));
                    },
                }
            },
            | CoreNode::ValueType(id) => {
                match *erased
                    .value_type(id)
                    .expect("an erased value type resolves")
                {
                    | ValueType::PathUniverse(source, target) => {
                        pending.extend([CoreNode::Value(source), CoreNode::Value(target)]);
                    },
                    | ValueType::Base(_)
                    | ValueType::Unit
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_) => {},
                    | ValueType::Product(first, second)
                    | ValueType::Sum(first, second)
                    | ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    } => {
                        pending.push(CoreNode::ValueType(first));
                        pending.push(CoreNode::ValueType(second));
                    },
                    | ValueType::Thunk(body) => pending.push(CoreNode::CompType(body)),
                    | ValueType::Lift { inner, .. } => pending.push(CoreNode::ValueType(inner)),
                    | ValueType::Element { code, .. } => pending.push(CoreNode::Value(code)),
                }
            },
            | CoreNode::CompType(id) => {
                match *erased
                    .comp_type(id)
                    .expect("an erased computation type resolves")
                {
                    | CompType::Returner(result) => pending.push(CoreNode::ValueType(result)),
                    | CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => {
                        pending.push(CoreNode::ValueType(domain));
                        pending.push(CoreNode::CompType(codomain));
                    },
                    | CompType::Element { code, .. } => pending.push(CoreNode::Value(code)),
                }
            },
        }
    }
    Unfolded(visited)
}
