use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageDepth;
use gandr_kernel_term::StageId;

use super::Part;
use super::unstaged;
use crate::CertificateEquality;
use crate::CoreArena;
use crate::ValueTypeId;
use crate::equal_type_syntax;

/// `(Nat[0] => -F List(Nat[<0]))` as a thunk, and the plain type it reads
/// as, the naturals at position zero.
///
/// # Specification
/// trivial.
fn staged_function(arena: &mut CoreArena) -> (ValueTypeId, ValueTypeId)
{
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec::Vec::new());
    let anchor = StageId::from(0_usize);
    let at = arena.value_type_staged(nat, Stage::At(anchor));
    let below = arena.value_type_staged(nat, Stage::Below {
        anchor,
        depth: StageDepth::from(core::num::NonZeroU32::MIN),
    });
    let listed = arena.value_type_list(below);
    let returned = arena.comp_type_returner(listed);
    let arrow = arena.comp_type_arrow(at, returned);
    let staged = arena.value_type_thunk(arrow);
    let plain_list = arena.value_type_list(nat);
    let plain_returned = arena.comp_type_returner(plain_list);
    let plain_arrow = arena.comp_type_arrow(nat, plain_returned);
    let plain = arena.value_type_thunk(plain_arrow);
    (staged, plain)
}

#[test]
fn every_placed_stage_is_erased()
{
    let mut arena = CoreArena::new();
    let (staged, plain) = staged_function(&mut arena);
    let Some(Part::Value(erased)) = unstaged(&mut arena, Part::Value(staged))
    else {
        panic!("a value type erases to a value type");
    };
    assert_ne!(erased, staged, "a staged type is rebuilt");
    assert_eq!(
        equal_type_syntax(&arena, erased, plain),
        CertificateEquality::Equal,
        "the domain's stage and the list element's are both erased"
    );
}

#[test]
fn a_plain_type_is_its_own_erasure()
{
    let mut arena = CoreArena::new();
    let (_staged, plain) = staged_function(&mut arena);
    assert_eq!(
        unstaged(&mut arena, Part::Value(plain)),
        Some(Part::Value(plain)),
        "nothing is rebuilt where no stage stands"
    );
}
