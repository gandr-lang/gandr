use gandr_core_term::CoreArena;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::host::HostSignatures;
use gandr_core_term::effect::host::partiality;
use quenchant_shape::shape::Maybe;

use super::programmed;
use super::unprogrammed::Absent;

#[test]
fn a_returner_over_a_row_of_operations_is_programmed_6642()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).expect("host interfaces");
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let console = EffectRow::singleton(host.console.clone());
    let both = console
        .union(&EffectRow::singleton(host.rand), &arena)
        .expect("two interfaces join");
    let at_console = arena.comp_type_returner_with_effects(integer, console.clone());
    let at_both = arena.comp_type_returner_with_effects(integer, both.clone());
    let pure = arena.comp_type_returner(integer);
    let open = arena.comp_type_returner_with_effects(integer, console.with_tail(Some(integer)));
    let divergent = arena.comp_type_returner_with_effects(
        integer,
        both.union(&EffectRow::singleton(partiality()), &arena)
            .expect("divergence joins"),
    );

    assert_eq!(
        programmed(&arena, at_console),
        Maybe::Present((integer, &console)),
        "a returner over one host interface reads its result and row"
    );
    assert_eq!(
        programmed(&arena, at_both),
        Maybe::Present((integer, &both)),
        "a returner over two interfaces reads its whole row"
    );
    assert_eq!(programmed(&arena, pure), Maybe::Absent(Absent::Pure));
    assert_eq!(programmed(&arena, open), Maybe::Absent(Absent::Open));
    assert_eq!(
        programmed(&arena, divergent),
        Maybe::Absent(Absent::Divergent),
        "a row of operations with divergence waits on the delay model"
    );
}
