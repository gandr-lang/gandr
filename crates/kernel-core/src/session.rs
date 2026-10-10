//! Search-free finite replay of session bisimulations and simulations.
//!
//! The producer supplies every related pair. Replay checks local obligations
//! and set membership; it never generates a candidate relation or unfolds a
//! recursive type to a fixed point. Payload paths are ordinary checker goals.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::session::Evidence;
use gandr_kernel_term::session::Graph;
use gandr_kernel_term::session::Label;
use gandr_kernel_term::session::Node;
use gandr_kernel_term::session::PayloadSlot;
use gandr_kernel_term::session::State;
use gandr_kernel_term::session::StatePair;

use crate::conv::Convertibility;
use crate::conv::convertible_value_types;

/// Which local coinductive rule the certificate claims.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Relation
{
    /// Equal labels and directions, with both observations preserved.
    Bisimulation,
    /// Fewer selections or more offers on the source side.
    Simulation,
}

/// A finite session formation or replay refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SessionError
{
    /// A native reference does not resolve.
    Arena,
    /// An endpoint is not a session code.
    ExpectedSession(ValueTypeId),
    /// A graph edge is out of bounds.
    MissingState(State),
    /// A structural edge repeats a syntax occurrence.
    RepeatedState(State),
    /// A variable escapes its lexical binder.
    UnboundVariable(State),
    /// A Mu body exposes no action before another administrative edge.
    NonContractive(State),
    /// The graph contains unreachable syntax.
    UnreachableState(State),
    /// The payload-code telescope is not a product spine ending in Unit.
    PayloadTelescope,
    /// A payload slot is outside that telescope.
    MissingPayload(PayloadSlot),
    /// The supplied relation omits a required observable pair.
    MissingPair(StatePair),
    /// A supplied pair names Mu or Var instead of its resolved action.
    AdministrativePair(StatePair),
    /// The two actions have different kinds or directions.
    WrongAction(StatePair),
    /// A required label is missing or bisimulation widths differ.
    WrongLabels(StatePair),
    /// Different payload codes have no supplied native path obligation.
    PayloadMismatch(StatePair),
    /// A payload obligation is duplicated.
    DuplicatePayloadPath(PayloadSlot, PayloadSlot),
}

impl core::fmt::Display for SessionError
{
    /// Render a named refusal with the offending position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Arena => f.write_str("unreadable session payload code"),
            | Self::ExpectedSession(_) => f.write_str("expected a session code"),
            | Self::MissingState(State(state)) => write!(f, "missing session state {state}"),
            | Self::RepeatedState(State(state)) => write!(f, "repeated session occurrence {state}"),
            | Self::UnboundVariable(State(state)) => {
                write!(f, "unbound session variable at {state}")
            },
            | Self::NonContractive(State(state)) => {
                write!(f, "noncontractive session binder at {state}")
            },
            | Self::UnreachableState(State(state)) => {
                write!(f, "unreachable session occurrence {state}")
            },
            | Self::PayloadTelescope => f.write_str("session payload telescope must end in Unit"),
            | Self::MissingPayload(PayloadSlot(slot)) => {
                write!(f, "missing session payload slot {slot}")
            },
            | Self::MissingPair(pair) => write!(
                f,
                "missing session pair ({}, {})",
                pair.source.0, pair.target.0
            ),
            | Self::AdministrativePair(pair) => write!(
                f,
                "session pair ({}, {}) is not observable",
                pair.source.0, pair.target.0
            ),
            | Self::WrongAction(pair) => write!(
                f,
                "session action mismatch at ({}, {})",
                pair.source.0, pair.target.0
            ),
            | Self::WrongLabels(pair) => write!(
                f,
                "session label mismatch at ({}, {})",
                pair.source.0, pair.target.0
            ),
            | Self::PayloadMismatch(pair) => write!(
                f,
                "session payload mismatch at ({}, {})",
                pair.source.0, pair.target.0
            ),
            | Self::DuplicatePayloadPath(PayloadSlot(source), PayloadSlot(target)) => {
                write!(f, "duplicate session payload path ({source}, {target})")
            },
        }
    }
}
impl core::error::Error for SessionError
{
}

/// Graph traversal instructions; leaving restores lexical binder scope.
#[derive(Clone, Copy)]
enum Visit
{
    /// Inspect a structural occurrence.
    Enter(State),
    /// End the scope of this Mu binder.
    Leave(State),
}

/// Extract the finite payload-code telescope.
///
/// # Specification
/// - ensures: returns fields in slot order and only accepts a Unit-terminated
///   product spine; no recursive session edge is followed.
/// - fails: unreadable native references or malformed telescope shape.
/// - panics: none.
///
/// # Errors
/// `Arena` or `PayloadTelescope`.
///
/// # Adequacy
/// - hypothesis: L3 malformed payload slots and spines refuse at formation.
/// - witness: `session::tests::session_codes_are_closed_and_contractive`
#[inline]
pub fn payload_codes(
    arena: &TermArena,
    mut payloads: ValueTypeId,
) -> Result<Vec<ValueTypeId>, SessionError>
{
    let mut fields = Vec::new();
    loop {
        match *arena.value_type(payloads).ok_or(SessionError::Arena)? {
            | ValueType::Product(field, rest) => {
                fields.push(field);
                payloads = rest;
            },
            | ValueType::Unit => return Ok(fields),
            | _ => return Err(SessionError::PayloadTelescope),
        }
    }
}

/// Check finite structural closure, lexical binding and contractivity.
///
/// # Specification
/// - ensures: structural edges form one rooted tree, variables name enclosing
///   Mu nodes, every Mu body starts with an action or End, and payload slots
///   name fields of the supplied finite telescope.
/// - fails: missing/repeated/unreachable states, escaped variables, unguarded
///   recursion, malformed telescopes and missing payload slots are named.
/// - panics: none.
///
/// # Errors
/// The corresponding `SessionError` formation variant.
///
/// # Adequacy
/// - hypothesis: L3 each malformed graph boundary has a distinguishing refusal;
///   observable recursion remains admitted.
/// - witness: `session::tests::session_codes_are_closed_and_contractive`
#[inline]
pub fn validate_graph(
    arena: &TermArena,
    graph: &Graph,
    mut payloads: ValueTypeId,
) -> Result<(), SessionError>
{
    let mut fields = PayloadSlot(0);
    loop {
        match *arena.value_type(payloads).ok_or(SessionError::Arena)? {
            | ValueType::Product(_, rest) => {
                fields.0 = fields.0.saturating_add(1);
                payloads = rest;
            },
            | ValueType::Unit => break,
            | _ => return Err(SessionError::PayloadTelescope),
        }
    }
    let mut seen = alloc::vec![false; graph.nodes.len()];
    let mut binders = alloc::vec![false; graph.nodes.len()];
    let mut pending = alloc::vec![Visit::Enter(graph.root)];
    while let Some(visit) = pending.pop() {
        let id = match visit {
            | Visit::Leave(id) => {
                *binders
                    .get_mut(id.0)
                    .ok_or(SessionError::MissingState(id))? = false;
                continue;
            },
            | Visit::Enter(id) => id,
        };
        let node = node(graph, id)?;
        if core::mem::replace(
            seen.get_mut(id.0).ok_or(SessionError::MissingState(id))?,
            true,
        ) {
            return Err(SessionError::RepeatedState(id));
        }
        match node {
            | &Node::Send(slot, next) | &Node::Receive(slot, next) => {
                if slot.0 >= fields.0 {
                    return Err(SessionError::MissingPayload(slot));
                }
                pending.push(Visit::Enter(next));
            },
            | &Node::Select(ref branches) | &Node::Offer(ref branches) => {
                pending.extend(branches.values().copied().map(Visit::Enter));
            },
            | &Node::Mu(body) => {
                if matches!(*self::node(graph, body)?, Node::Mu(_) | Node::Var(_)) {
                    return Err(SessionError::NonContractive(id));
                }
                *binders
                    .get_mut(id.0)
                    .ok_or(SessionError::MissingState(id))? = true;
                pending.push(Visit::Leave(id));
                pending.push(Visit::Enter(body));
            },
            | &Node::Var(binder) => {
                if !matches!(binders.get(binder.0), Some(&true)) {
                    return Err(SessionError::UnboundVariable(id));
                }
            },
            | &Node::End => {},
        }
    }
    for (index, &visited) in seen.iter().enumerate() {
        if !visited {
            return Err(SessionError::UnreachableState(State(index)));
        }
    }
    Ok(())
}

/// Resolve a finite graph reference.
///
/// # Specification
/// - ensures: returns the exact addressed syntax occurrence.
/// - fails: `MissingState` for an out-of-range reference.
/// - panics: none.
///
/// # Errors
/// `MissingState`.
///
/// # Adequacy
/// - hypothesis: L3 malformed edges retain their precise state.
/// - witness: `session::tests::session_codes_are_closed_and_contractive`
fn node(
    graph: &Graph,
    state: State,
) -> Result<&Node, SessionError>
{
    graph
        .nodes
        .get(state.0)
        .ok_or(SessionError::MissingState(state))
}

/// Resolve at most Var → Mu → action, never a fixed-point expansion.
///
/// # Specification
/// - requires: graph formation established binding and guards.
/// - ensures: returns the observable state after at most two administrative
///   edges; malformed input still refuses rather than diverging.
/// - fails: missing nodes or an unguarded administrative chain.
/// - panics: none.
///
/// # Errors
/// `MissingState` or `NonContractive`.
///
/// # Adequacy
/// - hypothesis: L3 the one-unfold equivalence reaches the same cyclic action.
/// - witness: `session::tests::session_relations_replay_without_search`
#[inline]
pub fn head(
    graph: &Graph,
    mut state: State,
) -> Result<State, SessionError>
{
    for _ in 0_u8 .. 3 {
        match node(graph, state)? {
            | &Node::Mu(next) | &Node::Var(next) => state = next,
            | _ => return Ok(state),
        }
    }
    Err(SessionError::NonContractive(state))
}

/// Read a native session code's finite graph and payload telescope.
///
/// # Specification
/// - ensures: exposes only the exact session constructor at the supplied id.
/// - fails: `ExpectedSession` for every other constructor or missing id.
/// - panics: none.
///
/// # Errors
/// `ExpectedSession`.
///
/// # Adequacy
/// - hypothesis: L3 non-session endpoints cannot receive session evidence.
/// - witness: `session::tests::session_relations_replay_without_search`
#[inline]
pub fn view(
    arena: &TermArena,
    ty: ValueTypeId,
) -> Result<(&Graph, ValueTypeId), SessionError>
{
    match arena.value_type(ty) {
        | Some(&ValueType::Session {
            ref graph,
            payloads,
        }) => Ok((graph, payloads)),
        | _ => Err(SessionError::ExpectedSession(ty)),
    }
}

/// Require one resolved continuation pair in supplied evidence.
///
/// # Specification
/// - ensures: checks membership of exactly the named observable pair.
/// - fails: missing pair or invalid administrative edge.
/// - panics: none.
///
/// # Errors
/// `MissingPair`, `MissingState`, or `NonContractive`.
///
/// # Adequacy
/// - hypothesis: L3 deleting a continuation obligation refuses by pair.
/// - witness: `session::tests::session_relations_replay_without_search`
fn require_pair(
    source: &Graph,
    target: &Graph,
    pair: StatePair,
    evidence: &Evidence,
) -> Result<(), SessionError>
{
    let source = head(source, pair.source)?;
    let target = head(target, pair.target)?;
    let pair = StatePair { source, target };
    if evidence.pairs.contains(&pair) {
        Ok(())
    }
    else {
        Err(SessionError::MissingPair(pair))
    }
}

/// Verify local label obligations while retaining continuation orientation.
///
/// # Specification
/// - ensures: bisimulation requires equal labels; simulation requires source
///   selections ⊆ target selections and target offers ⊆ source offers.
/// - fails: missing labels, missing continuation pairs or malformed edges.
/// - panics: none.
///
/// # Errors
/// `WrongLabels` or a required-pair refusal.
///
/// # Adequacy
/// - hypothesis: L3 both width polarities and a missing recursive pair refuse.
/// - witness: `session::tests::session_relations_replay_without_search`
fn branches(
    graphs: (&Graph, &Graph),
    pair: StatePair,
    labels: (&BTreeMap<Label, State>, &BTreeMap<Label, State>),
    evidence: &Evidence,
    relation: Relation,
    polarity: Choice,
) -> Result<(), SessionError>
{
    let (source, target) = labels;
    if relation == Relation::Bisimulation && source.len() != target.len() {
        return Err(SessionError::WrongLabels(pair));
    }
    let required = match polarity {
        | Choice::Select => source,
        | Choice::Offer => target,
    };
    for label in required.keys() {
        let source = source.get(label).ok_or(SessionError::WrongLabels(pair))?;
        let target = target.get(label).ok_or(SessionError::WrongLabels(pair))?;
        require_pair(
            graphs.0,
            graphs.1,
            StatePair {
                source: *source,
                target: *target,
            },
            evidence,
        )?;
    }
    Ok(())
}

/// Which endpoint controls a choice.
#[derive(Clone, Copy)]
enum Choice
{
    /// Source selects.
    Select,
    /// Peer selects.
    Offer,
}

/// Replay a finite relation and produce native payload-check obligations.
///
/// # Specification
/// - requires: both endpoint types passed closed-code formation.
/// - ensures: checks roots and every supplied pair without relation search;
///   payloads are structurally identical or covered by a native `Path_U` goal.
///   The returned product type must be checked against the supplied proof tuple
///   before this relation is evidence.
/// - fails: wrong directions, labels, payloads, missing pairs, administrative
///   pairs and malformed payload obligations are named.
/// - panics: none.
///
/// # Errors
/// Any session formation or relation refusal.
///
/// # Adequacy
/// - hypothesis: L1 the independent producer supplies pairs; L3 deletion,
///   reversal, wrong action and forged payload proof distinguish replay guards.
/// - witness: `session::tests::session_relations_replay_without_search`
pub(crate) fn obligations(
    arena: &mut TermArena,
    source: ValueTypeId,
    target: ValueTypeId,
    evidence: &Evidence,
    relation: Relation,
) -> Result<ValueTypeId, SessionError>
{
    let (left, left_payloads) = view(arena, source)?;
    let (right, right_payloads) = view(arena, target)?;
    let source_fields = payload_codes(arena, left_payloads)?;
    let target_fields = payload_codes(arena, right_payloads)?;
    let mut payload_pairs = BTreeSet::new();
    for &(source, target) in &evidence.payloads {
        source_fields
            .get(source.0)
            .ok_or(SessionError::MissingPayload(source))?;
        target_fields
            .get(target.0)
            .ok_or(SessionError::MissingPayload(target))?;
        if !payload_pairs.insert((source, target)) {
            return Err(SessionError::DuplicatePayloadPath(source, target));
        }
    }
    require_pair(
        left,
        right,
        StatePair {
            source: left.root,
            target: right.root,
        },
        evidence,
    )?;
    for &pair in &evidence.pairs {
        let a = node(left, pair.source)?;
        let b = node(right, pair.target)?;
        if matches!(*a, Node::Mu(_) | Node::Var(_)) || matches!(*b, Node::Mu(_) | Node::Var(_)) {
            return Err(SessionError::AdministrativePair(pair));
        }
        if let Node::Select(ref source_labels) = *a {
            let Node::Select(ref target_labels) = *b
            else {
                return Err(SessionError::WrongAction(pair));
            };
            branches(
                (left, right),
                pair,
                (source_labels, target_labels),
                evidence,
                relation,
                Choice::Select,
            )?;
            continue;
        }
        if let Node::Offer(ref source_labels) = *a {
            let Node::Offer(ref target_labels) = *b
            else {
                return Err(SessionError::WrongAction(pair));
            };
            branches(
                (left, right),
                pair,
                (source_labels, target_labels),
                evidence,
                relation,
                Choice::Offer,
            )?;
            continue;
        }
        match (a, b) {
            | (&Node::End, &Node::End) => {},
            | (&Node::Send(a, next_a), &Node::Send(b, next_b))
            | (&Node::Receive(a, next_a), &Node::Receive(b, next_b)) => {
                let source = *source_fields
                    .get(a.0)
                    .ok_or(SessionError::MissingPayload(a))?;
                let target = *target_fields
                    .get(b.0)
                    .ok_or(SessionError::MissingPayload(b))?;
                if convertible_value_types(arena, source, target) != Convertibility::Convertible
                    && !payload_pairs.contains(&(a, b))
                {
                    return Err(SessionError::PayloadMismatch(pair));
                }
                require_pair(
                    left,
                    right,
                    StatePair {
                        source: next_a,
                        target: next_b,
                    },
                    evidence,
                )?;
            },
            | _ => return Err(SessionError::WrongAction(pair)),
        }
    }
    let mut expected = arena.value_type_unit();
    for &(source, target) in evidence.payloads.iter().rev() {
        let source = *source_fields
            .get(source.0)
            .ok_or(SessionError::MissingPayload(source))?;
        let target = *target_fields
            .get(target.0)
            .ok_or(SessionError::MissingPayload(target))?;
        let source = arena.value_quote(source);
        let target = arena.value_quote(target);
        let path = arena.value_type_path_universe(source, target);
        expected = arena.value_type_product(path, expected);
    }
    Ok(expected)
}

#[cfg(test)]
mod tests;
