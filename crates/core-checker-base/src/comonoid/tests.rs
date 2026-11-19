//! The comonoid walk refuses a qubit and each type that holds one by the
//! binder's own type, and passes a gate's thunk and every type minted before
//! the arena's first qubit.

use alloc::collections::BTreeMap;
use alloc::string::String;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::FieldLabel;

use super::Grade;
use super::require;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;
use crate::session::LinearityDefect;

/// The refusal [`require`] gives for a binder of `ty` at `grade`, at the type
/// itself.
///
/// # Specification
/// trivial.
fn absent(
    ty: ValueTypeId,
    grade: Grade,
) -> Result<(), CheckRefusal>
{
    Err(CheckRefusal::Linearity {
        at: CoreNode::Type(TypeNode::Value(ty)),
        defect: LinearityDefect::ComonoidAbsent { ty, grade },
    })
}

#[test]
fn a_qubit_is_refused_at_each_grade_5739()
{
    let mut arena = CoreArena::new();
    let qubit = arena.value_type_qubit();
    let at = CoreNode::Type(TypeNode::Value(qubit));
    for grade in [Grade::Many, Grade::Zero] {
        assert_eq!(
            require(&arena, at, qubit, grade),
            absent(qubit, grade),
            "a binder at {grade:?} needs what the qubit lacks"
        );
    }
}

#[test]
fn a_type_that_holds_a_qubit_is_refused_by_its_own_name_5739()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let qubit = arena.value_type_qubit();
    let unit = arena.value_type_unit();
    let record = arena.value_type_record(BTreeMap::from([
        (FieldLabel::from(String::from("count")), integer),
        (FieldLabel::from(String::from("held")), qubit),
    ]));
    let sum = arena.value_type_sum(&[unit, qubit]);
    let pair = arena.value_type_product(&[integer, sum]);
    let listed = arena.value_type_list(pair);
    for held in [record, sum, listed] {
        assert_eq!(
            require(
                &arena,
                CoreNode::Type(TypeNode::Value(held)),
                held,
                Grade::Many
            ),
            absent(held, Grade::Many),
            "the refusal names the binder's type, not the qubit inside it"
        );
    }
}

#[test]
fn a_gate_and_a_type_before_the_first_qubit_carry_a_comonoid_5739()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let early = arena.value_type_product(&[integer, integer]);
    let qubit = arena.value_type_qubit();
    let returns = arena.comp_type_returner(qubit);
    let multiplicity = arena.value_unit();
    let gate = arena.comp_type_linear_arrow(qubit, multiplicity, returns);
    let suspended = arena.value_type_thunk(gate);
    let late = arena.value_type_product(&[integer, suspended]);
    for carried in [early, suspended, late] {
        assert_eq!(
            require(
                &arena,
                CoreNode::Type(TypeNode::Value(carried)),
                carried,
                Grade::Many
            ),
            Ok(()),
            "a thunk copies only its captures, and none holds a qubit"
        );
    }
}
