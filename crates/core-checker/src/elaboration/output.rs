//! Materialize universe transport per occurrence, sharing unchanged subterms.
//!
//! The walk rebuilds the formers of the route's fragment — thunks, lambdas,
//! applications, returns, forces, binds, ascriptions, tuples, injections,
//! cases, lifts and static applications and lambdas — and reads every other
//! former as an opaque leaf. A lift recorded beneath an opaque former is not
//! written into the term: it is handed back in a side table keyed by node, as
//! ordinary checking keeps every lift, so the output still readmits.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;

use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CoreNode;
use crate::Lift;
use crate::TermNode;

/// One code occurrence's conversion transport.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CodeUse
{
    /// The occurrence checks at its natural universe.
    Unchanged,
    /// This occurrence crosses to a higher value universe.
    Lifted(Lift),
}

/// Whether output syntax needs any reconstruction.
#[derive(Default, Eq, PartialEq)]
enum Effect
{
    /// Every code occurrence stays at its own level.
    #[default]
    Identity,
    /// At least one code occurrence needs an explicit lift.
    Lift,
}

/// Code conversions in judgement order, independently for each source node.
#[derive(Default)]
pub struct Transports
{
    /// A shared code can be checked at different universes at different uses.
    uses: BTreeMap<ValueId, VecDeque<CodeUse>>,
    /// Enables the identity output fast path.
    effect: Effect,
}

impl Transports
{
    /// Record one universe conversion at its source occurrence.
    ///
    /// # Specification
    /// - requires: calls follow the judgement's left-to-right term traversal.
    /// - ensures: appends this use without replacing earlier uses of the node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — a shared code used at two universes must emit
    ///   distinct transports, both accepted by the kernel.
    /// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
    #[spec(
        captures: before = (self.uses.get(&at).cloned().unwrap_or_default(), transport.clone()),
        ensures: self.uses.get(&at).is_some_and(|uses| {
            uses.len() == before.0.len().saturating_add(1)
                && uses.iter().take(before.0.len()).eq(before.0.iter())
                && uses.back() == Some(&before.1)
        }) && (!matches!(before.1, CodeUse::Lifted(_)) || self.effect == Effect::Lift),
    )]
    pub fn record(
        &mut self,
        at: ValueId,
        transport: CodeUse,
    )
    {
        if matches!(transport, CodeUse::Lifted(_)) {
            self.effect = Effect::Lift;
        }
        self.uses.entry(at).or_default().push_back(transport);
    }
}

/// Ordinary checking keeps its side table; elaboration records occurrences.
#[derive(Default)]
pub enum Emission
{
    /// No term-producing run is active.
    #[default]
    Off,
    /// A term-producing declaration judgement is recording its transports.
    Recording(Transports),
}

impl Emission
{
    /// Drop what a recording holds, keeping the mode.
    ///
    /// # Specification
    /// trivial.
    pub fn restart(&mut self)
    {
        if let Self::Recording(ref mut transports) = *self {
            *transports = Transports::default();
        }
    }
}

/// An emitted body and the lifts left in a side table: those recorded beneath
/// a former the walk reads as a leaf.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Emitted
{
    /// The body, every lift on a path of the fragment's formers explicit.
    pub body: ValueId,
    /// The lifts not written into the body, by node.
    pub lifts: BTreeMap<ValueId, Lift>,
}

/// A postorder traversal phase.
#[derive(Clone, Copy)]
enum Visit
{
    /// Schedule children before rebuilding their parent.
    Enter,
    /// All children have outputs on the result stack.
    Leave,
}

/// Produce a core value with every occurrence's universe transport explicit.
///
/// # Specification
/// - requires: `root` passed the judgement and `transports` records that
///   judgement's universe comparisons in traversal order.
/// - ensures: unchanged paths retain their ids; a lifted occurrence reached
///   through the fragment's formers becomes a quote of its lifted decode, and
///   sharing never conflates two such occurrences. A lift beneath a former the
///   walk reads as a leaf is in [`Emitted::lifts`] at its node, its last use
///   kept, as ordinary checking keeps it.
/// - fails: dangling nodes, inconsistent child families, or an exhausted
///   budget.
/// - panics: none.
/// - intension: a heap postorder walk, one visit per term occurrence per phase;
///   no walk or allocation when all transports are identities.
///
/// # Errors
/// Returns the corresponding `CheckRefusal` for invalid input or exhausted
/// work.
///
/// # Adequacy
/// - hypothesis: L1/L3 — the kernel independently checks emitted terms; nested
///   and shared code occurrences separate transport placement and multiplicity,
///   and unchanged paths beside a lift observe that they keep their ids.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
/// - witness: `elaboration::tests::unchanged_paths_keep_their_ids_beside_a_lift`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|emitted| arena.value(emitted.body).is_some()))]
pub(super) fn emit(
    arena: &mut CoreArena,
    root: ValueId,
    mut transports: Transports,
    budget: CheckBudget,
) -> Result<Emitted, CheckRefusal>
{
    if transports.effect == Effect::Identity {
        return Ok(Emitted {
            body: root,
            lifts: BTreeMap::new(),
        });
    }
    let mut pending = Vec::from([(TermNode::Value(root), Visit::Enter)]);
    let mut emitted = Vec::new();
    let mut remaining = usize::from(budget);
    while let Some((node, visit)) = pending.pop() {
        if remaining == 0 {
            return Err(CheckRefusal::BudgetExceeded { budget });
        }
        remaining = remaining.saturating_sub(1);
        match visit {
            Visit::Enter => {
                pending.push((node, Visit::Leave));
                children(arena, node, &mut pending)?;
            },
            Visit::Leave => {
                let rebuilt = rebuild(arena, node, &mut emitted)?;
                let rebuilt = match (node, rebuilt) {
                    (TermNode::Value(original), TermNode::Value(body)) => {
                        let transport = transports
                            .uses
                            .get_mut(&original)
                            .and_then(VecDeque::pop_front);
                        let body = match transport {
                            Some(CodeUse::Lifted(lift)) => lift.mint(arena, body),
                            Some(CodeUse::Unchanged) | None => body,
                        };
                        TermNode::Value(body)
                    },
                    (_, rebuilt) => rebuilt,
                };
                emitted.push(rebuilt);
            },
        }
    }
    let body = value(&mut emitted)?;
    let mut lifts = BTreeMap::new();
    for (at, uses) in transports.uses {
        if let Some(CodeUse::Lifted(lift)) = uses.into_iter().last() {
            lifts.insert(at, lift);
        }
    }
    Ok(Emitted { body, lifts })
}

/// Schedule term children in the judgement's left-to-right order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the term children of a former of the fragment, each to be
///   entered, in reverse order for the LIFO traversal; quotes have type
///   children, whose decodes compare classifiers exactly and never insert
///   universe lifts; any other former is a leaf. The one push site writes
///   [`Visit::Enter`], so the clause checks only that nothing was removed.
/// - fails: `DanglingNode` when the input id does not resolve.
/// - panics: none.
///
/// # Errors
/// Returns `CheckRefusal::DanglingNode` for an unresolved id.
///
/// # Adequacy
/// - hypothesis: L1/L3 — shared code occurrences observe traversal order.
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
#[spec(captures: depth = pending.len(), ensures: pending.len() >= depth)]
fn children(
    arena: &CoreArena,
    node: TermNode,
    pending: &mut Vec<(TermNode, Visit)>,
) -> Result<(), CheckRefusal>
{
    let mut push = |child| pending.push((child, Visit::Enter));
    let dangling = CheckRefusal::DanglingNode {
        node: CoreNode::Term(node),
    };
    match node {
        TermNode::Value(id) => match *arena.value(id).ok_or(dangling)? {
            Value::Thunk(body) => push(TermNode::Computation(body)),
            Value::StaticApplication(first, second) => {
                push(TermNode::Value(second));
                push(TermNode::Value(first));
            },
            Value::Tuple(ref components) => {
                for &component in components.iter().rev() {
                    push(TermNode::Value(component));
                }
            },
            Value::Injection(_, body)
            | Value::StaticLambda(body)
            | Value::Lift { body, .. }
            | Value::Ascribe { value: body, .. } => {
                push(TermNode::Value(body));
            },
            Value::Primitive { .. }
            | Value::PathRefl(_)
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Here(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Univalence(..)
            | Value::Ua { .. }
            | Value::Compose { .. }
            | Value::SessionRelated { .. }
            | Value::Stay(_)
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::FunctionFlow(..)
            | Value::Recorded(_)
            | Value::Dialogue(_)
            | Value::Web(_)
            | Value::Returned(_)
            | Value::Nested(_)
            | Value::Run(_)
            | Value::RecordUpdate { .. }
            | Value::Variable { .. }
            | Value::Constant(_)
            | Value::Literal(_)
            | Value::ListNil
            | Value::ListCons(..)
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::Constructor { .. }
            | Value::Record(_)
            | Value::Hole(_)
            | Value::Mark { .. }
            | Value::Reify(_)
            | Value::Row(_) => {},
        },
        TermNode::Computation(id) => match *arena.computation(id).ok_or(dangling)? {
            Computation::Lambda(body) | Computation::Ascribe { body, .. } => {
                push(TermNode::Computation(body));
            },
            Computation::Application(head, argument) => {
                push(TermNode::Value(argument));
                push(TermNode::Computation(head));
            },
            Computation::Return(body) | Computation::Force(body) | Computation::Decompose(body) => {
                push(TermNode::Value(body));
            },
            Computation::Bind(bound, body) => {
                push(TermNode::Computation(body));
                push(TermNode::Computation(bound));
            },
            Computation::Case {
                scrutinee,
                ref branches,
            } => {
                for &branch in branches.iter().rev() {
                    push(TermNode::Computation(branch));
                }
                push(TermNode::Value(scrutinee));
            },
            Computation::Primitive { .. }
            | Computation::Transport(..)
            | Computation::PathTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Fixpoint { .. }
            | Computation::Split { .. }
            | Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..)
            | Computation::Hole(_)
            | Computation::Mark { .. }
            | Computation::ListFold { .. }
            | Computation::ListCase { .. }
            | Computation::Perform { .. }
            | Computation::Handle { .. }
            | Computation::Exercise { .. }
            | Computation::Scope { .. }
            | Computation::Resume(..)
            | Computation::Abandon(_)
            | Computation::Reset(_)
            | Computation::Shift(_)
            | Computation::With(..)
            | Computation::Project(..)
            | Computation::Session(_)
            | Computation::Memory(_)
            | Computation::World(_) => {},
        },
    }
    Ok(())
}

/// Pop an emitted value child.
///
/// # Specification
/// - requires: the child was visited before its parent.
/// - ensures: consumes and returns its value id.
/// - fails: `MachineInvariant` for a missing or wrong-family result.
/// - panics: none.
///
/// # Errors
/// Returns `CheckRefusal::MachineInvariant` for inconsistent traversal state.
///
/// # Adequacy
/// - hypothesis: L1 — kernel readmission checks the child relation.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[spec(
    captures: before = (emitted.last().copied(), emitted.len()),
    ensures: |ret| emitted.len() == before.1.saturating_sub(1) && match before.0 {
        Some(TermNode::Value(body)) => ret == Ok(body),
        _ => ret == Err(CheckRefusal::MachineInvariant),
    },
)]
fn value(emitted: &mut Vec<TermNode>) -> Result<ValueId, CheckRefusal>
{
    match emitted.pop() {
        Some(TermNode::Value(body)) => Ok(body),
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// Pop an emitted computation child.
///
/// # Specification
/// - requires: the child was visited before its parent.
/// - ensures: consumes and returns its computation id.
/// - fails: `MachineInvariant` for a missing or wrong-family result.
/// - panics: none.
///
/// # Errors
/// Returns `CheckRefusal::MachineInvariant` for inconsistent traversal state.
///
/// # Adequacy
/// - hypothesis: L1 — kernel readmission checks the child relation.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[spec(
    captures: before = (emitted.last().copied(), emitted.len()),
    ensures: |ret| emitted.len() == before.1.saturating_sub(1) && match before.0 {
        Some(TermNode::Computation(body)) => ret == Ok(body),
        _ => ret == Err(CheckRefusal::MachineInvariant),
    },
)]
fn computation(emitted: &mut Vec<TermNode>) -> Result<ComputationId, CheckRefusal>
{
    match emitted.pop() {
        Some(TermNode::Computation(body)) => Ok(body),
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// Pop the emitted counterparts of the value children `originals`, restoring
/// their traversal order.
///
/// # Specification
/// - requires: the children were visited before their parent, in order.
/// - ensures: consumes one emitted value per original and returns them first to
///   last.
/// - fails: `MachineInvariant` for a missing or wrong-family result.
/// - panics: none.
///
/// # Errors
/// Returns `CheckRefusal::MachineInvariant` for inconsistent traversal state.
///
/// # Adequacy
/// - hypothesis: L1 — kernel readmission checks the child relation.
/// - witness: `elaboration::tests::residual_conjunction_does_not_hide_refusal`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|values| values.len() == originals.len()))]
fn values(
    emitted: &mut Vec<TermNode>,
    originals: &[ValueId],
) -> Result<Vec<ValueId>, CheckRefusal>
{
    let mut values = Vec::with_capacity(originals.len());
    for _ in originals {
        values.push(value(emitted)?);
    }
    values.reverse();
    Ok(values)
}

/// Pop the emitted counterparts of the computation children `originals`,
/// restoring their traversal order.
///
/// # Specification
/// - requires: the children were visited before their parent, in order.
/// - ensures: consumes one emitted computation per original and returns them
///   first to last.
/// - fails: `MachineInvariant` for a missing or wrong-family result.
/// - panics: none.
///
/// # Errors
/// Returns `CheckRefusal::MachineInvariant` for inconsistent traversal state.
///
/// # Adequacy
/// - hypothesis: L1 — kernel readmission checks the child relation.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|computations| computations.len() == originals.len()))]
fn computations(
    emitted: &mut Vec<TermNode>,
    originals: &[ComputationId],
) -> Result<Vec<ComputationId>, CheckRefusal>
{
    let mut computations = Vec::with_capacity(originals.len());
    for _ in originals {
        computations.push(computation(emitted)?);
    }
    computations.reverse();
    Ok(computations)
}

/// Rebuild a parent only if a term child changed at this occurrence.
///
/// # Specification
/// - requires: emitted children are on the stack in their traversal order.
/// - ensures: consumes exactly the children [`children`] scheduled and retains
///   the original id if they are unchanged; otherwise mints one parent with
///   those children. A leaf is its own output.
/// - fails: dangling input or inconsistent traversal state.
/// - panics: none.
///
/// # Errors
/// Returns the input or traversal `CheckRefusal`.
///
/// # Adequacy
/// - hypothesis: L1/L3 — nested and shared lifts distinguish occurrence-local
///   reconstruction from a source-id remapping; a lift under each former of the
///   fragment separates rebuilding that former from keeping it, and unchanged
///   formers beside a lift separate keeping them from minting a copy.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
/// - witness: `elaboration::tests::every_fragment_former_carries_a_nested_lift`
/// - witness: `elaboration::tests::unchanged_paths_keep_their_ids_beside_a_lift`
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
#[spec(ensures: |ret| match (ret, node) {
    (Ok(TermNode::Value(body)), TermNode::Value(_)) => arena.value(body).is_some(),
    (Ok(TermNode::Computation(body)), TermNode::Computation(_)) => arena.computation(body).is_some(),
    (Err(_), _) => true,
    _ => false,
})]
fn rebuild(
    arena: &mut CoreArena,
    node: TermNode,
    emitted: &mut Vec<TermNode>,
) -> Result<TermNode, CheckRefusal>
{
    let dangling = CheckRefusal::DanglingNode {
        node: CoreNode::Term(node),
    };
    match node {
        TermNode::Value(id) => {
            let rebuilt = match *arena.value(id).ok_or(dangling)? {
                Value::Thunk(original) => {
                    let body = computation(emitted)?;
                    (body != original).then(|| arena.value_thunk(body))
                },
                Value::StaticApplication(head, argument) => {
                    let new_argument = value(emitted)?;
                    let new_head = value(emitted)?;
                    (new_head != head || new_argument != argument)
                        .then(|| arena.value_static_application(new_head, new_argument))
                },
                Value::StaticLambda(original) => {
                    let body = value(emitted)?;
                    (body != original).then(|| arena.value_static_lambda(body))
                },
                Value::Injection(summand, original) => {
                    let body = value(emitted)?;
                    (body != original).then(|| arena.value_injection(summand, body))
                },
                Value::Lift {
                    ref target,
                    body: original,
                } => {
                    let target = target.clone();
                    let body = value(emitted)?;
                    (body != original).then(|| arena.value_lift(target, body))
                },
                Value::Ascribe {
                    value: original,
                    ty,
                } => {
                    let body = value(emitted)?;
                    (body != original).then(|| arena.value_ascribe(body, ty))
                },
                Value::Tuple(ref components) => {
                    let original = components.to_vec();
                    let rebuilt = values(emitted, &original)?;
                    (rebuilt != original).then(|| arena.value_tuple(&rebuilt))
                },
                Value::Primitive { .. }
                | Value::PathRefl(_)
                | Value::PathProduct(..)
                | Value::PathEquiv { .. }
                | Value::Here(_)
                | Value::Funext(..)
                | Value::Equiv(..)
                | Value::Univalence(..)
                | Value::Ua { .. }
                | Value::Compose { .. }
                | Value::SessionRelated { .. }
                | Value::Stay(_)
                | Value::Then(..)
                | Value::FlowProduct(..)
                | Value::Forward(_)
                | Value::FunctionFlow(..)
                | Value::Recorded(_)
                | Value::Dialogue(_)
                | Value::Web(_)
                | Value::Returned(_)
                | Value::Nested(_)
                | Value::Run(_)
                | Value::RecordUpdate { .. }
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::Hole(_)
                | Value::Mark { .. }
                | Value::Reify(_)
                | Value::Row(_) => None,
            };
            Ok(TermNode::Value(rebuilt.unwrap_or(id)))
        },
        TermNode::Computation(id) => {
            let rebuilt = match *arena.computation(id).ok_or(dangling)? {
                Computation::Lambda(original) => {
                    let body = computation(emitted)?;
                    (body != original).then(|| arena.computation_lambda(body))
                },
                Computation::Ascribe { body: original, ty } => {
                    let body = computation(emitted)?;
                    (body != original).then(|| arena.computation_ascribe(body, ty))
                },
                Computation::Return(original) => {
                    let body = value(emitted)?;
                    (body != original).then(|| arena.computation_return(body))
                },
                Computation::Force(original) => {
                    let body = value(emitted)?;
                    (body != original).then(|| arena.computation_force(body))
                },
                Computation::Decompose(original) => {
                    let body = value(emitted)?;
                    (body != original).then(|| arena.computation_decompose(body))
                },
                Computation::Application(head, argument) => {
                    let new_argument = value(emitted)?;
                    let new_head = computation(emitted)?;
                    (new_head != head || new_argument != argument)
                        .then(|| arena.computation_application(new_head, new_argument))
                },
                Computation::Bind(bound, body) => {
                    let new_body = computation(emitted)?;
                    let new_bound = computation(emitted)?;
                    (new_bound != bound || new_body != body)
                        .then(|| arena.computation_bind(new_bound, new_body))
                },
                Computation::Case {
                    scrutinee,
                    ref branches,
                } => {
                    let original = branches.to_vec();
                    let rebuilt = computations(emitted, &original)?;
                    let new_scrutinee = value(emitted)?;
                    (new_scrutinee != scrutinee || rebuilt != original)
                        .then(|| arena.computation_case(new_scrutinee, &rebuilt))
                },
                Computation::Primitive { .. }
                | Computation::Transport(..)
                | Computation::PathTransport { .. }
                | Computation::Ride { .. }
                | Computation::TelescopeTransport { .. }
                | Computation::Fixpoint { .. }
                | Computation::Split { .. }
                | Computation::DataCase { .. }
                | Computation::RecordProjection(..)
                | Computation::TupleProjection(..)
                | Computation::Hole(_)
                | Computation::Mark { .. }
                | Computation::ListFold { .. }
                | Computation::ListCase { .. }
                | Computation::Perform { .. }
                | Computation::Handle { .. }
                | Computation::Exercise { .. }
                | Computation::Scope { .. }
                | Computation::Resume(..)
                | Computation::Abandon(_)
                | Computation::Reset(_)
                | Computation::Shift(_)
                | Computation::With(..)
                | Computation::Project(..)
                | Computation::Session(_)
                | Computation::Memory(_)
                | Computation::World(_) => None,
            };
            Ok(TermNode::Computation(rebuilt.unwrap_or(id)))
        },
    }
}
