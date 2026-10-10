//! Materialize universe transport per occurrence, sharing unchanged subterms.

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
    /// A private declaration elaboration is recording its transports.
    Recording(Transports),
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
/// - requires: `root` passed the route-fragment judgement and `transports`
///   records that judgement's universe comparisons in traversal order.
/// - ensures: unchanged paths retain their ids; a lifted occurrence becomes a
///   quote of its lifted decode. Sharing never conflates two occurrences.
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
///   and shared code occurrences separate transport placement and multiplicity.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
#[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|body| arena.value(body).is_some()))]
pub(super) fn emit(
    arena: &mut CoreArena,
    root: ValueId,
    mut transports: Transports,
    budget: CheckBudget,
) -> Result<ValueId, CheckRefusal>
{
    if transports.effect == Effect::Identity {
        return Ok(root);
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
            | Visit::Enter => {
                pending.push((node, Visit::Leave));
                children(arena, node, &mut pending)?;
            },
            | Visit::Leave => {
                let rebuilt = rebuild(arena, node, &mut emitted)?;
                let rebuilt = match (node, rebuilt) {
                    | (TermNode::Value(original), TermNode::Value(body)) => {
                        let transport = transports
                            .uses
                            .get_mut(&original)
                            .and_then(VecDeque::pop_front);
                        let body = match transport {
                            | Some(CodeUse::Lifted(lift)) => lift.mint(arena, body),
                            | Some(CodeUse::Unchanged) | None => body,
                        };
                        TermNode::Value(body)
                    },
                    | (_, rebuilt) => rebuilt,
                };
                emitted.push(rebuilt);
            },
        }
    }
    value(&mut emitted)
}

/// Schedule term children in the judgement's left-to-right order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends term children in reverse order for the LIFO traversal;
///   quotes have type children, whose route-fragment decodes compare
///   classifiers exactly and never insert universe lifts.
/// - fails: `DanglingNode` when the input id does not resolve.
/// - panics: none.
///
/// # Errors
/// Returns `CheckRefusal::DanglingNode` for an unresolved id.
///
/// # Adequacy
/// - hypothesis: L1/L3 — shared code occurrences observe traversal order.
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
#[spec(
    captures: depth = pending.len(),
    ensures: pending.len() >= depth
        && pending.iter().skip(depth).all(|&(_, visit)| matches!(visit, Visit::Enter)),
)]
fn children(
    arena: &CoreArena,
    node: TermNode,
    pending: &mut Vec<(TermNode, Visit)>,
) -> Result<(), CheckRefusal>
{
    let mut push = |child| pending.push((child, Visit::Enter));
    match node {
        | TermNode::Value(id) => match *arena.value(id).ok_or(CheckRefusal::DanglingNode {
            node: CoreNode::Term(node),
        })? {
            | Value::Thunk(body) => push(TermNode::Computation(body)),
            | Value::Pair(first, second) | Value::StaticApplication(first, second) => {
                push(TermNode::Value(second));
                push(TermNode::Value(first));
            },
            | Value::Injection(_, body) | Value::StaticLambda(body) | Value::Lift { body, .. } => {
                push(TermNode::Value(body));
            },
            | Value::Variable { .. }
            | Value::Constant(_)
            | Value::Unit
            | Value::Literal(_)
            | Value::Quote(_)
            | Value::QuoteComputation(_) => {},
        },
        | TermNode::Computation(id) => {
            match *arena.computation(id).ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(node),
            })? {
                | Computation::Lambda(body) => push(TermNode::Computation(body)),
                | Computation::Application(head, argument) => {
                    push(TermNode::Value(argument));
                    push(TermNode::Computation(head));
                },
                | Computation::Return(body) | Computation::Force(body) => {
                    push(TermNode::Value(body));
                },
                | Computation::Bind(bound, body) => {
                    push(TermNode::Computation(body));
                    push(TermNode::Computation(bound));
                },
                | Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                } => {
                    push(TermNode::Computation(on_right));
                    push(TermNode::Computation(on_left));
                    push(TermNode::Value(scrutinee));
                },
            }
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
        | Some(TermNode::Value(body)) => ret == Ok(body),
        | _ => ret == Err(CheckRefusal::MachineInvariant),
    },
)]
fn value(emitted: &mut Vec<TermNode>) -> Result<ValueId, CheckRefusal>
{
    match emitted.pop() {
        | Some(TermNode::Value(body)) => Ok(body),
        | _ => Err(CheckRefusal::MachineInvariant),
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
        | Some(TermNode::Computation(body)) => ret == Ok(body),
        | _ => ret == Err(CheckRefusal::MachineInvariant),
    },
)]
fn computation(emitted: &mut Vec<TermNode>) -> Result<ComputationId, CheckRefusal>
{
    match emitted.pop() {
        | Some(TermNode::Computation(body)) => Ok(body),
        | _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// Rebuild a parent only if a term child changed at this occurrence.
///
/// # Specification
/// - requires: emitted children are on the stack in their traversal order.
/// - ensures: consumes exactly those children and retains the original id if
///   they are unchanged; otherwise mints one parent with those children.
/// - fails: dangling input or inconsistent traversal state.
/// - panics: none.
///
/// # Errors
/// Returns the input or traversal `CheckRefusal`.
///
/// # Adequacy
/// - hypothesis: L1/L3 — nested and shared lifts distinguish occurrence-local
///   reconstruction from a source-id remapping.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
#[spec(ensures: |ret| match (ret, node) {
    | (Ok(TermNode::Value(body)), TermNode::Value(_)) => arena.value(body).is_some(),
    | (Ok(TermNode::Computation(body)), TermNode::Computation(_)) => arena.computation(body).is_some(),
    | (Err(_), _) => true,
    | _ => false,
})]
fn rebuild(
    arena: &mut CoreArena,
    node: TermNode,
    emitted: &mut Vec<TermNode>,
) -> Result<TermNode, CheckRefusal>
{
    match node {
        | TermNode::Value(id) => {
            let original = arena.value(id).ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(node),
            })?;
            let rebuilt = match *original {
                | Value::Thunk(_) => {
                    let body = computation(emitted)?;
                    Value::Thunk(body)
                },
                | Value::Pair(..) => {
                    let second = value(emitted)?;
                    let first = value(emitted)?;
                    Value::Pair(first, second)
                },
                | Value::StaticApplication(..) => {
                    let argument = value(emitted)?;
                    let head = value(emitted)?;
                    Value::StaticApplication(head, argument)
                },
                | Value::StaticLambda(_) => {
                    let body = value(emitted)?;
                    Value::StaticLambda(body)
                },
                | Value::Injection(side, _) => {
                    let body = value(emitted)?;
                    Value::Injection(side, body)
                },
                | Value::Lift { ref target, .. } => {
                    let body = value(emitted)?;
                    Value::Lift {
                        target: target.clone(),
                        body,
                    }
                },
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Unit
                | Value::Literal(_)
                | Value::Quote(_)
                | Value::QuoteComputation(_) => return Ok(node),
            };
            if rebuilt == *original {
                return Ok(node);
            }
            let rebuilt = match rebuilt {
                | Value::Thunk(body) => arena.value_thunk(body),
                | Value::Pair(first, second) => arena.value_pair(first, second),
                | Value::StaticApplication(head, argument) => {
                    arena.value_static_application(head, argument)
                },
                | Value::StaticLambda(body) => arena.value_static_lambda(body),
                | Value::Injection(side, body) => arena.value_injection(side, body),
                | Value::Lift { target, body } => arena.value_lift(target, body),
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Unit
                | Value::Literal(_)
                | Value::Quote(_)
                | Value::QuoteComputation(_) => return Err(CheckRefusal::MachineInvariant),
            };
            Ok(TermNode::Value(rebuilt))
        },
        | TermNode::Computation(id) => {
            let original = arena.computation(id).ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(node),
            })?;
            let rebuilt = match *original {
                | Computation::Lambda(_) => {
                    let body = computation(emitted)?;
                    Computation::Lambda(body)
                },
                | Computation::Return(_) => {
                    let body = value(emitted)?;
                    Computation::Return(body)
                },
                | Computation::Force(_) => {
                    let body = value(emitted)?;
                    Computation::Force(body)
                },
                | Computation::Application(..) => {
                    let argument = value(emitted)?;
                    let head = computation(emitted)?;
                    Computation::Application(head, argument)
                },
                | Computation::Bind(..) => {
                    let body = computation(emitted)?;
                    let bound = computation(emitted)?;
                    Computation::Bind(bound, body)
                },
                | Computation::Case { .. } => {
                    let on_right = computation(emitted)?;
                    let on_left = computation(emitted)?;
                    let scrutinee = value(emitted)?;
                    Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    }
                },
            };
            if rebuilt == *original {
                return Ok(node);
            }
            let rebuilt = match rebuilt {
                | Computation::Lambda(body) => arena.computation_lambda(body),
                | Computation::Return(body) => arena.computation_return(body),
                | Computation::Force(body) => arena.computation_force(body),
                | Computation::Application(head, argument) => {
                    arena.computation_application(head, argument)
                },
                | Computation::Bind(bound, body) => arena.computation_bind(bound, body),
                | Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                } => arena.computation_case(scrutinee, on_left, on_right),
            };
            Ok(TermNode::Computation(rebuilt))
        },
    }
}
