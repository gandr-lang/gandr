//! A theory read as the interface a capability scope handles.
//!
//! `handle c : T with sort S = A { M } with { … }` handles the theory `T` as
//! an effect interface, its handler a model of `T` whose carrier is the
//! handler's answer. The carrier is the one unindexed sort every operation
//! returns; every other sort is a value sort, which the manifest fixes at the
//! type it writes. An operation `oper op : (p : P, …, k : pi+ (x : R, …) . C)
//! --> C` takes its continuation last, at the carrier: the inputs before it
//! are the payload, a value of each `P`, and the continuation's binders are
//! the reply, a value of each `R`. No value is the unit, one is its own type,
//! and several are their tuple, as an exercise's arguments are. This is the
//! correspondence between an algebraic operation `P × C^R → C` and the
//! generic effect `P → T R` that performs it.
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

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperationKind;

use crate::form::Placed;
use crate::model::InterfaceFault;
use crate::model::Members;
use crate::model::Port;
use crate::model::PresentedOperation;

#[cfg(test)]
mod tests;

/// A theory read as an effect interface, at the scope that handles it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct TheoryInterface
{
    /// The capability scope handling the theory, whose signature the mint
    /// keeps for every form naming it.
    pub scope: NodeIndex,
    /// The interface's name: the theory's.
    pub name: EffectName,
    /// Each operation, in the theory's order.
    pub operations: Vec<TheoryOperation>,
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

/// The operations of the theory `members` presents, read as an effect
/// interface whose value sorts `fixed` fixes, each sort's name beside the
/// node of the type it is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one operation per presented operation, in order, its payload the
///   fixed type of each input before its last and its reply the fixed type of
///   each binder of its last.
/// - fails: the first member out of shape, sorts before operations, each in
///   written order, beside its name tile and its fault: an indexed sort
///   [`InterfaceFault::Indexed`]; a fixed carrier [`InterfaceFault::Fixed`]; an
///   unfixed sort other than the carrier [`InterfaceFault::Unfixed`]; a member
///   other than an operation whose one output is the carrier
///   [`InterfaceFault::Carrier`]; a last input other than a continuation
///   [`InterfaceFault::Continuation`]; an earlier input other than a value of a
///   fixed sort [`InterfaceFault::Payload`].
/// - panics: none.
///
/// # Errors
/// The member out of shape and its fault.
///
/// # Adequacy
/// - hypothesis: L3 — `State` read as its two operations, and a theory refused
///   at each fault.
/// - witness: `lower::capability::theory::tests::state_reads_as_a_get_and_a_put_2272`
/// - witness: `lower::capability::theory::tests::each_member_out_of_shape_is_refused_by_its_fault_2272`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |operations| operations.len() == members.operations.len()))]
pub(in crate::lower) fn operations(
    members: &Members,
    fixed: &BTreeMap<Name, NodeIndex>,
) -> Result<Vec<TheoryOperation>, (Placed, InterfaceFault)>
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
    members
        .operations
        .iter()
        .map(|operation| {
            effect_operation(operation, carrier, fixed).map_err(|fault| (operation.named, fault))
        })
        .collect()
}

/// The operation `operation` read as an effect operation over the carrier
/// `carrier`, its value sorts fixed by `fixed`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the operation's name, the fixed type of each input before its
///   last, and the fixed type of each binder of its last.
/// - fails: as [`operations`] for one operation.
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
