//! A theory read as the interface a capability scope handles.
//!
//! `handle c : T with sort S = A { M } with { … }` handles the theory `T` as
//! an effect interface, its handler a model of `T` whose carrier is the
//! handler's answer. The carrier is the one unindexed sort every effect
//! operation returns; every other sort is a value sort, which the manifest
//! fixes at the type it writes. An operation `oper op : (p : P, …, k : pi+ (x :
//! R, …) . C) --> C` takes its continuation last, at the carrier: the inputs
//! before it are the payload, a value of each `P`, and the continuation's
//! binders are the reply, a value of each `R`. No value is the unit, one is its
//! own type, and several are their tuple, as an exercise's arguments are. This
//! is the correspondence between an algebraic operation `P × C^R → C` and the
//! generic effect `P → T R` that performs it. Each law of `T` is read over
//! those operations ([`laws`]), for the scope to be checked as a model of it,
//! and, from the side `T`'s order puts above the other, as a rewrite of the
//! scope's subject ([`rules`]), which normalises by it before it runs.
//!
//! A value operation, `oper zero : N` or `oper plus : (a : N, b : N) --> N`,
//! takes and returns values of sorts the manifest fixes and performs nothing,
//! so no clause answers it: a model the scope names does ([`operations`]). A
//! law that applies one is the model's to state, never the clauses' to owe
//! ([`laws`]).
//!
//! # Examples
//!
//! ```text
//! theory State {
//!   sort S : Type+;
//!   sort C : Type;
//!   oper get : (k : pi+ (s : S) . C) --> C;
//!   oper put : (s : S, k : C) --> C;
//! }
//! ```
//!
//! Handled at `State with sort S = Integer`, `get` sends the unit and replies
//! an `Integer`, and `put` sends an `Integer` and replies the unit.
//!
//! # References
//!
//! - Gordon Plotkin and John Power. "Algebraic Operations and Generic Effects."
//!   _Applied Categorical Structures_ 11(1) (2003). <https://doi.org/10.1023/A:1023064908962>
//! - `vault:01a16b8f-6aec-7282-b400-974aedeaa341` — lineage: an effect is a
//!   theory whose rules are its equations, so a scope's subject normalises by
//!   the theory's laws before it runs ([`rules`]).
//! - `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: which of
//!   state's laws are rules, get-get, put-get and put-put, and which wait on a
//!   grade condition.
//! - `vault:01a14daa-a317-7d92-bd17-3f20e87634cd` — lineage: a model meets the
//!   laws it owes by conversion or by certificate, so a law applying a value
//!   operation is the model's to state, never the clauses' ([`laws`]).

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComponentCount;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_core_term::handler;
use gandr_core_term::handler::Arity;
use gandr_core_term::handler::ReadLaw;
use gandr_core_term::handler::subject;
use gandr_core_term::handler::subject::SubjectRule;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::RuleIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperationKind;
use gandr_theory_levitation::RuleTurn;
use gandr_theory_levitation::TermView;

use crate::form::Placed;
use crate::model::InterfaceFault;
use crate::model::Members;
use crate::model::Port;
use crate::model::PresentedOperation;

#[cfg(test)]
mod tests;

/// A theory read as an effect interface, at the scope that handles it or the
/// row entry that names it at the sorts it fixes.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct TheoryInterface
{
    /// The capability scope handling the theory, or the name of the row
    /// entry naming it, whose signature the mint keeps for every form naming
    /// it.
    pub scope: NodeIndex,
    /// The interface's name: the theory's.
    pub name: EffectName,
    /// The theory's declaration, which the written name refers to.
    pub theory: ConstantIndex,
    /// Each effect operation, in the theory's order.
    pub operations: Vec<TheoryOperation>,
    /// Each value operation, in the theory's order, which only a model the
    /// scope names answers.
    pub values: Vec<ValueOperation>,
    /// Each law, in the theory's order, read for a scope's clauses.
    pub laws: Vec<TheoryLaw>,
    /// Each law the theory's order orients as a rewrite of a scope's subject,
    /// in the theory's order.
    pub rules: Vec<SubjectRule>,
    /// Each sort the manifest fixes beside the node of the type it writes, in
    /// the order written.
    pub manifest: Vec<(Name, NodeIndex)>,
    /// The declaration whose body or signature holds the form; for a scope,
    /// the one that owes the laws.
    pub owner: ConstantIndex,
}

impl TheoryInterface
{
    /// The operation named `name`, when the theory declares one.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(in crate::lower) fn operation(
        &self,
        name: &OperationName,
    ) -> Option<&TheoryOperation>
    {
        self.operations
            .iter()
            .find(|operation| operation.name == *name)
    }
}

/// An operation of a theory read as an effect operation: the type of each
/// value its payload carries and its reply returns, each the manifest's
/// written type for the value's sort.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct TheoryOperation
{
    /// The operation's name.
    pub name: OperationName,
    /// The type of each input before the continuation, in order.
    pub payload: Vec<NodeIndex>,
    /// The type of each value the continuation binds, in order.
    pub reply: Vec<NodeIndex>,
}

/// A value operation of a theory: every input and its output at a sort the
/// manifest fixes, so it performs nothing and a model answers it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct ValueOperation
{
    /// The operation's name.
    pub name: Name,
    /// Its name tile in the theory.
    pub named: Placed,
}

/// A theory's operations read as an effect interface: the effect operations,
/// and apart from them the value operations.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct Operations
{
    /// Each effect operation, in the theory's order.
    pub effects: Vec<TheoryOperation>,
    /// Each value operation, in the theory's order.
    pub values: Vec<ValueOperation>,
}

/// A law of a theory read for the clauses of a scope that handles it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct TheoryLaw
{
    /// The law's place among the theory's rules.
    pub rule: RuleIndex,
    /// Its two sides, over its metavariables.
    pub read: ReadLaw,
}

/// The operations of the theory `members` presents, read as an effect
/// interface whose value sorts `fixed` fixes, each sort's name beside the
/// node of the type it is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each presented operation once, in order, either a value
///   operation, its every input and its one output an unindexed port at a sort
///   `fixed` fixes, binding and abstracting nothing; or an effect operation,
///   its payload the fixed type of each input before its last and its reply the
///   fixed type of each binder of its last.
/// - fails: the first member out of shape, sorts before operations, each in
///   written order, beside its name tile and its fault: an indexed sort
///   [`InterfaceFault::Indexed`]; a fixed carrier [`InterfaceFault::Fixed`]; an
///   unfixed sort other than the carrier [`InterfaceFault::Unfixed`]; a member
///   neither a value operation nor an operation whose one output is the carrier
///   [`InterfaceFault::Carrier`]; a last input other than a continuation
///   [`InterfaceFault::Continuation`]; an earlier input other than a value of a
///   fixed sort [`InterfaceFault::Payload`].
/// - panics: none.
///
/// # Errors
/// The member out of shape and its fault.
///
/// # Adequacy
/// - hypothesis: L3 — `State` read as its two operations, a theory refused at
///   each fault, and a cost theory's `zero` and `plus` read as value operations
///   apart from its `charge`.
/// - witness: `lower::capability::theory::tests::state_reads_as_a_get_and_a_put_2272`
/// - witness: `lower::capability::theory::tests::each_member_out_of_shape_is_refused_by_its_fault_2272`
/// - witness: `lower::capability::theory::tests::a_value_operation_is_read_apart_from_the_effects_2288`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| read.effects.len().saturating_add(read.values.len()) == members.operations.len()))]
pub(in crate::lower) fn operations(
    members: &Members,
    fixed: &BTreeMap<Name, NodeIndex>,
) -> Result<Operations, (Placed, InterfaceFault)>
{
    let carrier = members
        .operations
        .first()
        .and_then(|operation| operation.outputs.first())
        .map(|port| &port.sort.sort);
    for sort in &members.sorts {
        let fault = if sort.indices.is_empty() {
            match (carrier == Some(&sort.name), fixed.contains_key(&sort.name)) {
                (true, true) => Some(InterfaceFault::Fixed),
                (false, false) => Some(InterfaceFault::Unfixed),
                (true, false) | (false, true) => None,
            }
        }
        else {
            Some(InterfaceFault::Indexed)
        };
        if let Some(fault) = fault {
            return Err((sort.named, fault));
        }
    }
    let mut read = Operations {
        effects: Vec::new(),
        values: Vec::new(),
    };
    for operation in &members.operations {
        if let Some(value) = value_operation(operation, fixed) {
            read.values.push(value);
        }
        else {
            read.effects.push(
                effect_operation(operation, carrier, fixed)
                    .map_err(|fault| (operation.named, fault))?,
            );
        }
    }
    Ok(read)
}

/// The laws of the theory `members` presents, each read for the clauses of a
/// scope that answers `operations`, a law applying one of `values` left to the
/// model that answers it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one law per law `members` presents that applies none of `values`,
///   in order, at its place among the theory's rules, its sides read by
///   [`handler::read_law`] over the payload and reply each operation's clause
///   takes; every law when `values` is empty.
/// - fails: the first law no handler's clauses read that applies none of
///   `values`, beside its name tile and [`InterfaceFault::Law`].
/// - panics: none.
///
/// # Errors
/// The law no handler reads.
///
/// # Adequacy
/// - hypothesis: L3 — put-get read over State's operations, a law storing a
///   constructor refused, and a cost theory's two laws, each applying a value
///   operation, left to the model.
/// - witness: `lower::capability::theory::tests::a_theory_s_laws_read_for_its_handler_2272`
/// - witness: `lower::capability::theory::tests::a_value_operation_is_read_apart_from_the_effects_2288`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |laws| laws.len() <= members.laws.len() && (laws.len() == members.laws.len() || !values.is_empty())))]
pub(in crate::lower) fn laws(
    members: &Members,
    operations: &[TheoryOperation],
    values: &[ValueOperation],
) -> Result<Vec<TheoryLaw>, (Placed, InterfaceFault)>
{
    let arities = arities(operations);
    let valued: BTreeSet<&Name> = values.iter().map(|value| &value.name).collect();
    members
        .laws
        .iter()
        .enumerate()
        .filter_map(|(place, law)| {
            if applied_value(&law.left, &valued)
                .or_else(|| applied_value(&law.right, &valued))
                .is_some()
            {
                return None;
            }
            Some(
                handler::read_law((&law.left, &law.right), |name| arities.get(name).copied())
                    .map(|read| TheoryLaw {
                        rule: RuleIndex::from(place),
                        read,
                    })
                    .map_err(|_unread| (law.named, InterfaceFault::Law)),
            )
        })
        .collect()
}

/// The first of `values` that `term` applies anywhere beneath it.
///
/// # Specification
/// trivial.
fn applied_value<'term>(
    term: &'term FreeTerm,
    values: &BTreeSet<&Name>,
) -> Option<&'term Name>
{
    let mut pending = vec![term.to_node()];
    while let Some(node) = pending.pop() {
        match node.view() {
            TermView::Op { name, args } => {
                if values.contains(name) {
                    return Some(name);
                }
                pending.extend(args);
            },
            TermView::Ctor { args, .. }
            | TermView::Results { args }
            | TermView::Inst { args, .. }
            | TermView::Abs { args, .. }
            | TermView::Lam { args, .. } => pending.extend(args),
            TermView::Var(_) | TermView::Atom(_) | TermView::Bound(_) => {},
        }
    }
    None
}

/// The laws of the theory `members` presents, each oriented as `turns`
/// orients it, read as rewrites of the subject of a scope that answers
/// `operations`.
///
/// # Specification
/// - requires: `turns` is the orientation the theory's rule certificate gives
///   its written laws.
/// - ensures: one rule per law [`subject::subject_rule`] reads, in the theory's
///   order, each rewriting from the side the theory's order puts above the
///   other: the written left side, or the right where `turns` marks the law
///   turned; a law it reads as none is left out.
/// - fails: never; a law no subject rewrite reads is left out.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — State's three laws read as three rules and a reordering
///   law as none, and get-get marked turned is read from its right side, which
///   grows, as none.
/// - witness: `lower::capability::theory::tests::a_theory_s_laws_rewrite_its_scope_s_subject_2272`
#[spec(ensures: |ret| ret.len() <= members.laws.len())]
pub(in crate::lower) fn rules(
    members: &Members,
    operations: &[TheoryOperation],
    turns: &[RuleTurn],
) -> Vec<SubjectRule>
{
    let arities = arities(operations);
    members
        .laws
        .iter()
        .enumerate()
        .filter_map(|(place, law)| {
            let sides = match turns.get(place) {
                Some(&RuleTurn::Turned) => (&law.right, &law.left),
                Some(&RuleTurn::AsWritten) | None => (&law.left, &law.right),
            };
            subject::subject_rule(RuleIndex::from(place), sides, |name| {
                arities.get(name).copied()
            })
        })
        .collect()
}

/// The payload and reply count of each of `operations`, by name.
///
/// # Specification
/// trivial.
fn arities(operations: &[TheoryOperation]) -> BTreeMap<Name, Arity>
{
    operations
        .iter()
        .map(|operation| {
            (Name::from(operation.name.as_ref()), Arity {
                payload: ComponentCount::from(operation.payload.len()),
                reply: ComponentCount::from(operation.reply.len()),
            })
        })
        .collect()
}

/// The value operation `operation` is, when it is one: an `oper` member whose
/// every input and one output are unindexed ports at sorts `fixed` fixes,
/// binding and abstracting nothing.
///
/// # Specification
/// trivial.
fn value_operation(
    operation: &PresentedOperation,
    fixed: &BTreeMap<Name, NodeIndex>,
) -> Option<ValueOperation>
{
    let at_fixed = |port: &Port| {
        port.sort.indices.is_empty()
            && port.binders.is_empty()
            && port.abstractions.is_empty()
            && fixed.contains_key(&port.sort.sort)
    };
    (matches!(
        operation.kind,
        OperationKind::Operation | OperationKind::Constant
    ) && matches!(operation.outputs.as_slice(), [output] if at_fixed(output))
        && operation.inputs.iter().all(at_fixed))
    .then(|| ValueOperation {
        name: operation.name.clone(),
        named: operation.named,
    })
}

/// The operation `operation` read as an effect operation over the carrier
/// `carrier`, its value sorts fixed by `fixed`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the operation's name, the fixed type of each input before its
///   last, and the fixed type of each binder of its last.
/// - fails: as [`operations`] for one operation, except that a value operation
///   fails [`InterfaceFault::Carrier`] too: [`operations`] reads it before.
/// - panics: none.
///
/// # Errors
/// The operation's fault.
///
/// # Adequacy
/// - hypothesis: L3 — as [`operations`].
/// - witness: `lower::capability::theory::tests::each_member_out_of_shape_is_refused_by_its_fault_2272`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| read.name.as_ref() == operation.name.as_ref()))]
fn effect_operation(
    operation: &PresentedOperation,
    carrier: Option<&Name>,
    fixed: &BTreeMap<Name, NodeIndex>,
) -> Result<TheoryOperation, InterfaceFault>
{
    let at_carrier = |port: &Port| carrier == Some(&port.sort.sort) && port.sort.indices.is_empty();
    let &[ref output] = operation.outputs.as_slice()
    else {
        return Err(InterfaceFault::Carrier);
    };
    if operation.kind != OperationKind::Operation
        || !at_carrier(output)
        || !output.binders.is_empty()
    {
        return Err(InterfaceFault::Carrier);
    }
    let Some((continuation, payload)) = operation.inputs.split_last()
    else {
        return Err(InterfaceFault::Continuation);
    };
    if !at_carrier(continuation) || !continuation.abstractions.is_empty() {
        return Err(InterfaceFault::Continuation);
    }
    let reply = continuation
        .binders
        .iter()
        .map(|binder| fixed.get(&binder.sort.sort).copied())
        .collect::<Option<Vec<NodeIndex>>>()
        .ok_or(InterfaceFault::Continuation)?;
    let payload = payload
        .iter()
        .map(|port| {
            if port.binders.is_empty() && port.abstractions.is_empty() {
                fixed.get(&port.sort.sort).copied()
            }
            else {
                None
            }
        })
        .collect::<Option<Vec<NodeIndex>>>()
        .ok_or(InterfaceFault::Payload)?;
    Ok(TheoryOperation {
        name: OperationName::from(operation.name.as_ref()),
        payload,
        reply,
    })
}
