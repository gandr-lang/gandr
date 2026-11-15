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

/// One placed former over `child`; a computation type is held in a thunk.
type Placed = fn(&mut CoreArena, ValueTypeId) -> ValueTypeId;

/// Every former that places a child erases a stage standing there, and
/// reads as the same former over the plain type.
#[test]
fn every_placed_former_erases_the_stage_it_holds()
{
    let formers: [(&str, Placed); 9] = [
        ("a data argument", |a, c| {
            let quoted = a.value_quote(c);
            a.value_type_data(ConstantIndex::from(1_usize), alloc::vec![quoted])
        }),
        ("a record field", |a, c| {
            a.value_type_record(alloc::collections::BTreeMap::from([(
                gandr_kernel_term::FieldLabel::from(alloc::string::String::from("a")),
                c,
            )]))
        }),
        ("a product component", |a, c| {
            let unit = a.value_type_unit();
            a.value_type_product(&[c, unit])
        }),
        ("a summand", |a, c| {
            let unit = a.value_type_unit();
            a.value_type_sum(&[unit, c])
        }),
        ("a dependent pair's first", |a, c| {
            let unit = a.value_type_unit();
            a.value_type_sigma(c, unit)
        }),
        ("a dependent pair's second", |a, c| {
            let unit = a.value_type_unit();
            a.value_type_sigma(unit, c)
        }),
        ("a dependent function's domain", |a, c| {
            let unit = a.value_type_unit();
            let returned = a.comp_type_returner(unit);
            let pi = a.comp_type_pi(c, returned);
            a.value_type_thunk(pi)
        }),
        ("a lazy product's component", |a, c| {
            let unit = a.value_type_unit();
            let (held, other) = (a.comp_type_returner(c), a.comp_type_returner(unit));
            let with = a.comp_type_with(&[other, held]);
            a.value_type_thunk(with)
        }),
        ("a list element", |a, c| a.value_type_list(c)),
    ];
    for (what, former) in formers {
        let mut arena = CoreArena::new();
        let nat = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec::Vec::new());
        let at = arena.value_type_staged(nat, Stage::At(StageId::from(0_usize)));
        let staged = former(&mut arena, at);
        let plain = former(&mut arena, nat);
        let Some(Part::Value(erased)) = unstaged(&mut arena, Part::Value(staged))
        else {
            panic!("{what}: a value type erases to a value type");
        };
        assert_eq!(
            equal_type_syntax(&arena, erased, plain),
            CertificateEquality::Equal,
            "{what}: the stage is erased"
        );
    }
}
