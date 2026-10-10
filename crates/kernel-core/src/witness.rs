//! Building the self-contained type witnesses a refusal carries.
//!
//! A refusal outlives the arena that produced it — admission truncates on
//! rejection — so what it carries has to be content rather than a reference.
//! These functions derive witnesses from arena content, so refusal sites
//! share one construction of the head and digest.

use anodized::spec;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;

use crate::encoding::content_digest;
use crate::error::CompTypeHead;
use crate::error::CompTypeWitness;
use crate::error::ValueTypeHead;
use crate::error::ValueTypeWitness;

/// The self-contained witness of a value type.
///
/// # Specification
/// - requires: nothing — an unreadable id is admissible and yields the
///   unreadable head beside the digest of the unreadable record.
/// - ensures: `|ret| ret.head() ==
///   arena.value_type(id).map_or(ValueTypeHead::Unreadable, ValueTypeHead::of)
///   && ret.digest() == content_digest(arena, AnyNode::ValueType(id))` — the
///   type's head former and whole-content digest distinguish types sharing a
///   head and remain meaningful after arena truncation.
/// - provides: the payload of every value-type refusal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on integer/string base types and a unit type before and
///   after truncation; exact heads and differing digests distinguish head
///   substitution, hashing only the head and stale readable content.
/// - witness: `witness::tests::two_types_of_one_head_are_still_separated`
/// - witness: `witness::tests::an_unreadable_type_witnesses_as_unreadable`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.head() == arena.value_type(id).map_or(ValueTypeHead::Unreadable, ValueTypeHead::of) && ret.digest() == content_digest(arena, AnyNode::ValueType(id)))]
pub fn value_type_witness(
    arena: &TermArena,
    id: ValueTypeId,
) -> ValueTypeWitness
{
    let head = arena
        .value_type(id)
        .map_or(ValueTypeHead::Unreadable, ValueTypeHead::of);
    let digest = content_digest(arena, AnyNode::ValueType(id));
    ValueTypeWitness::new(head, digest)
}

/// The self-contained witness of a computation type; see
/// [`value_type_witness`].
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| ret.head() ==
///   arena.comp_type(id).map_or(CompTypeHead::Unreadable, CompTypeHead::of) &&
///   ret.digest() == content_digest(arena, AnyNode::CompType(id))` — the type's
///   head former and the digest of its whole content.
/// - provides: the payload of every computation-type refusal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on unit/integer returners and a returner before and after
///   truncation; exact heads and differing digests distinguish head
///   substitution, hashing only the head and stale readable content.
/// - witness: `witness::tests::two_computation_types_of_one_head_are_separated`
/// - witness: `witness::tests::an_unreadable_computation_type_witnesses_as_unreadable`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.head() == arena.comp_type(id).map_or(CompTypeHead::Unreadable, CompTypeHead::of) && ret.digest() == content_digest(arena, AnyNode::CompType(id)))]
pub fn comp_type_witness(
    arena: &TermArena,
    id: CompTypeId,
) -> CompTypeWitness
{
    let head = arena
        .comp_type(id)
        .map_or(CompTypeHead::Unreadable, CompTypeHead::of);
    let digest = content_digest(arena, AnyNode::CompType(id));
    CompTypeWitness::new(head, digest)
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::TermArena;

    use super::comp_type_witness;
    use super::value_type_witness;
    use crate::error::CompTypeHead;
    use crate::error::ValueTypeHead;

    #[test]
    fn two_types_of_one_head_are_still_separated()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let first = value_type_witness(&arena, integer);
        let second = value_type_witness(&arena, string);
        assert_eq!(ValueTypeHead::Base, first.head());
        assert_eq!(ValueTypeHead::Base, second.head());
        assert_ne!(
            first.digest(),
            second.digest(),
            "the digest is what tells two types of one head apart"
        );
    }

    #[test]
    fn an_unreadable_type_witnesses_as_unreadable()
    {
        let mut arena = TermArena::new();
        let floor = arena.watermark();
        let unit = arena.value_type_unit();
        let readable = value_type_witness(&arena, unit);
        assert_eq!(readable.head(), ValueTypeHead::Unit);
        arena.truncate_to(floor);
        let unreadable = value_type_witness(&arena, unit);
        assert_eq!(
            ValueTypeHead::Unreadable,
            unreadable.head(),
            "a refusal about a node that is gone still says so rather than panicking"
        );
        assert_ne!(unreadable.digest(), readable.digest());
    }

    #[test]
    fn two_computation_types_of_one_head_are_separated()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit_returner = arena.comp_type_returner(unit);
        let integer_returner = arena.comp_type_returner(integer);
        let first = comp_type_witness(&arena, unit_returner);
        let second = comp_type_witness(&arena, integer_returner);
        assert_eq!(CompTypeHead::Returner, first.head());
        assert_eq!(CompTypeHead::Returner, second.head());
        assert_ne!(first.digest(), second.digest());
    }

    #[test]
    fn an_unreadable_computation_type_witnesses_as_unreadable()
    {
        let mut arena = TermArena::new();
        let floor = arena.watermark();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let readable = comp_type_witness(&arena, returner);
        assert_eq!(readable.head(), CompTypeHead::Returner);
        arena.truncate_to(floor);
        let unreadable = comp_type_witness(&arena, returner);
        assert_eq!(unreadable.head(), CompTypeHead::Unreadable);
        assert_ne!(unreadable.digest(), readable.digest());
    }
}
