//! The value types that focusing writes into the IL (#8161): the type of each
//! bind's binder and of each field of a structural former, joined from the
//! checker's typings, beside the signature of each declared family.
//!
//! The checker keeps a typing for each judgement that it finishes, and a term
//! finishes after each term inside it. [`typed`] walks the typings of each
//! declaration once, in that order. When a constructor's typing comes, the
//! latest typing of each field is the judgement of this occurrence. A bind's
//! head holds its latest typing in the same way. The module's run reads each
//! kept type through the solutions of its implicits, so each type here is
//! solved.
//!
//! The table keys a binder's type by the computation that its bind runs. The
//! elaboration rebuilds a bind of a nested call over the call itself (#4466),
//! so a bind that focusing reads is often no node that the checker judged. The
//! computation it runs is one: a judged bind's head, read through
//! [`bound_run`], or the call of a judged nested value.
//!
//! A field of a declared constructor takes no type from the typings. Its
//! layout is a fact of its declaration, so focusing reads the type that the
//! family's signature states for it.
//!
//! # Boundaries
//!
//! - **A node that two occurrences type apart holds a conflict.** Two sites can
//!   share one node of the core arena. The table keys a type by the node. A key
//!   that takes two contents holds [`Recorded::Conflict`], and focusing counts
//!   the position as a conflict. Two ids of one content are one type.
//! - **A field that its constructor's judgement did not judge holds no type.**
//!   The join reads the latest typing of the field before the constructor's.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::TypedModule;
use gandr_core_sequent::Recorded;
use gandr_core_sequent::Typed;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::session::RecordedMove;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldPosition;

use crate::schedule::bound_run;

/// The table of the binder types and the field types that the typings of
/// `module` give over `core`, beside the signatures `declared` of the
/// families in scope.
///
/// # Specification
/// - requires: `module` is the typed run of a module over `core`, and
///   `declared` the signatures that the run admits.
/// - ensures: a bind is keyed with the result type of its head's returner, and
///   field `i` of a constructor with the type of its field value, each read
///   from the latest typing before the typing of the bind or the constructor; a
///   key that two occurrences give two contents holds a conflict; no other key
///   is held. The table holds `declared` unchanged.
/// - panics: none.
/// - executable: none — unwitnessable provenance: the typings must be the run
///   of a module over `core`, and the call holds no judgement to check them
///   against.
///
/// # Cost
/// - allocation: the table, growth within the typed binds and fields
/// - allocation: two maps of the latest typings of one declaration, growth
///   within that declaration's typings
///
/// # Adequacy
/// - hypothesis: L3 — a pair, a cons cell and a bind over a returner are each
///   read at the types that their judgements give.
/// - witness: `annotate::tests::the_join_reads_each_field_and_binder_at_its_occurrence_8161`
pub fn typed(
    core: &CoreArena,
    module: &TypedModule,
    declared: BTreeMap<ConstantIndex, Arc<DataSignature>>,
) -> Typed
{
    let same = |old, new| {
        gandr_core_term::equal_type_syntax(core, old, new)
            == gandr_core_term::CertificateEquality::Equal
    };
    let mut binders: BTreeMap<ComputationId, Recorded> = BTreeMap::new();
    let mut fields: BTreeMap<(ValueId, FieldPosition), Recorded> = BTreeMap::new();
    for typings in module.typings().values() {
        let mut values: BTreeMap<ValueId, ValueTypeId> = BTreeMap::new();
        let mut returned: BTreeMap<ComputationId, ValueTypeId> = BTreeMap::new();
        for typing in typings.typings() {
            match (typing.term, typing.ty) {
                (TermNode::Value(value), TypeNode::Value(ty)) => {
                    each_field(core, value, |position, field| {
                        if let Some(&held) = values.get(&field) {
                            Recorded::join(&mut fields, (value, position), held, same);
                        }
                    });
                    if let Some(&Value::Nested(call)) = core.value(value) {
                        Recorded::join(&mut binders, call, ty, same);
                    }
                    let _latest = values.insert(value, ty);
                },
                (TermNode::Computation(term), TypeNode::Computation(ty)) => {
                    if let Some(&Computation::Bind(head, _)) = core.computation(term) {
                        let run = bound_run(core, head);
                        if let Some(&result) = returned.get(&head).or_else(|| returned.get(&run)) {
                            Recorded::join(&mut binders, run, result, same);
                        }
                    }
                    if let Some(&CompType::Returner { result, .. }) = core.comp_type(ty) {
                        let _latest = returned.insert(term, result);
                    }
                },
                (TermNode::Value(_), TypeNode::Computation(_))
                | (TermNode::Computation(_), TypeNode::Value(_)) => {},
            }
        }
    }
    Typed::checked(binders, fields, declared)
}

/// Call `each` with the position and the value of each producer field of
/// `value`, in the order in which focusing pushes the fields.
///
/// # Specification
/// trivial.
fn each_field(
    core: &CoreArena,
    value: ValueId,
    mut each: impl FnMut(FieldPosition, ValueId),
)
{
    let mut at = 0_usize;
    let mut next = |field: ValueId| {
        each(FieldPosition::from(at), field);
        at = at.saturating_add(1);
    };
    match core.value(value) {
        Some(&Value::Record(ref fields)) => fields.values().copied().for_each(&mut next),
        Some(&Value::Constructor { ref fields, .. }) => fields.iter().copied().for_each(&mut next),
        Some(&Value::Tuple(ref components)) => components.iter().copied().for_each(&mut next),
        Some(&Value::ListCons(head, tail)) => {
            next(head);
            next(tail);
        },
        Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => next(body),
        Some(&Value::Recorded(ref moves)) => {
            for movement in moves.iter() {
                if let RecordedMove::Sent(payload) | RecordedMove::Received(payload) = *movement {
                    next(payload);
                }
            }
        },
        Some(&Value::Dialogue(ref turns)) => {
            for turn in turns.iter() {
                if let RecordedMove::Sent(payload) | RecordedMove::Received(payload) = turn.movement
                {
                    next(payload);
                }
            }
        },
        Some(_) | None => {},
    }
}

#[cfg(test)]
mod tests;
