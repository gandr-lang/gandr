use alloc::string::String;

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;

use super::*;
use crate::focus::Provenance;
use crate::focus::Writers;
use crate::focus::focus_computation;
use crate::pretty::render_command;

/// The cell's interface, as a source would spell it.
///
/// # Specification
/// trivial.
fn cell() -> EffectSig
{
    EffectSig::new(EffectName::from(CELL), core::iter::empty()).expect("no operation conflicts")
}

/// A spawn of the cell, sending `payload`.
///
/// # Specification
/// trivial.
fn spawning(
    core: &mut CoreArena,
    payload: ValueId,
) -> ComputationId
{
    core.computation_perform(cell(), OperationName::from(SPAWN), payload)
}

/// A read of the cell, sending `handle`.
///
/// # Specification
/// trivial.
fn reading(
    core: &mut CoreArena,
    handle: ValueId,
) -> ComputationId
{
    core.computation_perform(cell(), OperationName::from(READ), handle)
}

/// A de Bruijn index: the number of binders out a variable names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Outward(u32);

/// The variable `index` binders out.
///
/// # Specification
/// trivial.
fn variable(
    core: &mut CoreArena,
    index: Outward,
) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, index.0.into())
}

/// `program` focused into `arena` with `writers` named.
///
/// # Specification
/// trivial.
fn focused(
    core: &CoreArena,
    program: ComputationId,
    arena: &mut CommandArena,
    writers: &Writers,
) -> CommandId
{
    focus_computation(core, program, arena, &mut Provenance::new(), writers)
        .expect("the program focuses")
}

/// `program` focused with `writers` named, then scheduled, rendered.
///
/// # Specification
/// trivial.
fn scheduled(
    core: &CoreArena,
    program: ComputationId,
    writers: &Writers,
) -> String
{
    let mut arena = CommandArena::new();
    let root = focused(core, program, &mut arena, writers);
    let (root, _definitions) =
        spawn_independent(&mut arena, (root, &Definitions::new())).expect("the program schedules");
    render_command(&arena, root)
}

/// `program`, its spawns and reads written by hand, focused with no writer
/// named, rendered.
///
/// # Specification
/// trivial.
fn written(
    core: &CoreArena,
    program: ComputationId,
) -> String
{
    let mut arena = CommandArena::new();
    let root = focused(core, program, &mut arena, &Writers::NONE);
    render_command(&arena, root)
}

/// `x ← return (); y ← return ((), ()); return (y, x)`, its first writer
/// named, spawns that writer and reads it past the second bind, before the
/// return that names `x`: as `h ← spawn {return ()}; y ← return ((), ());
/// x ← read h; return (y, x)` focuses.
#[test]
fn a_marked_cut_spawns_its_writer_and_reads_it_where_first_named()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let pair = core.value_tuple(&[unit, unit]);
    let first = core.computation_return(unit);
    let second = core.computation_return(pair);
    let fields = [
        variable(&mut core, Outward(0)),
        variable(&mut core, Outward(1)),
    ];
    let answer = core.value_tuple(&fields);
    let returned = core.computation_return(answer);
    let inner = core.computation_bind(second, returned);
    let program = core.computation_bind(first, inner);

    let suspended = core.value_thunk(first);
    let spawn = spawning(&mut core, suspended);
    let handle = variable(&mut core, Outward(1));
    let read = reading(&mut core, handle);
    let fields = [
        variable(&mut core, Outward(1)),
        variable(&mut core, Outward(0)),
    ];
    let answer = core.value_tuple(&fields);
    let returned = core.computation_return(answer);
    let read_then = core.computation_bind(read, returned);
    let second_then = core.computation_bind(second, read_then);
    let by_hand = core.computation_bind(spawn, second_then);

    assert_eq!(
        written(&core, by_hand),
        scheduled(&core, program, &core::iter::once(first).collect()),
        "the writer is spawned and read where `x` is first named"
    );
}

/// `x ← return (); y ← return (x, ()); return (y, x)`, both writers named,
/// reads `x` before it spawns the writer that names it: as `h ← spawn
/// {return ()}; x ← read h; k ← spawn {return (x, ())}; y ← read k;
/// return (y, x)` focuses.
#[test]
fn an_inner_writer_reads_the_outer_binder_before_its_spawn()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let first = core.computation_return(unit);
    let x = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[x, unit]);
    let second = core.computation_return(pair);
    let fields = [
        variable(&mut core, Outward(0)),
        variable(&mut core, Outward(1)),
    ];
    let answer = core.value_tuple(&fields);
    let returned = core.computation_return(answer);
    let inner = core.computation_bind(second, returned);
    let program = core.computation_bind(first, inner);

    let outer_thunk = core.value_thunk(first);
    let outer_spawn = spawning(&mut core, outer_thunk);
    let outer_handle = variable(&mut core, Outward(0));
    let outer_read = reading(&mut core, outer_handle);
    let inner_thunk = core.value_thunk(second);
    let inner_spawn = spawning(&mut core, inner_thunk);
    let inner_handle = variable(&mut core, Outward(0));
    let inner_read = reading(&mut core, inner_handle);
    let fields = [
        variable(&mut core, Outward(0)),
        variable(&mut core, Outward(2)),
    ];
    let answer = core.value_tuple(&fields);
    let returned = core.computation_return(answer);
    let inner_read_then = core.computation_bind(inner_read, returned);
    let inner_spawn_then = core.computation_bind(inner_spawn, inner_read_then);
    let outer_read_then = core.computation_bind(outer_read, inner_spawn_then);
    let by_hand = core.computation_bind(outer_spawn, outer_read_then);

    assert_eq!(
        written(&core, by_hand),
        scheduled(&core, program, &[first, second].into_iter().collect()),
        "the outer read stands before the spawn whose writer names `x`"
    );
}

/// `x ← return (); return ((), ())`, its writer named, reads `x` before its
/// return though nothing names it: as `h ← spawn {return ()}; x ← read h;
/// return ((), ())` focuses.
#[test]
fn a_binder_never_named_is_read_before_the_end()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let pair = core.value_tuple(&[unit, unit]);
    let first = core.computation_return(unit);
    let returned = core.computation_return(pair);
    let program = core.computation_bind(first, returned);

    let suspended = core.value_thunk(first);
    let spawn = spawning(&mut core, suspended);
    let handle = variable(&mut core, Outward(0));
    let read = reading(&mut core, handle);
    let read_then = core.computation_bind(read, returned);
    let by_hand = core.computation_bind(spawn, read_then);

    assert_eq!(
        written(&core, by_hand),
        scheduled(&core, program, &core::iter::once(first).collect()),
        "the run reads the writer it started before it ends"
    );
}

/// A definition whose thunk holds a marked cut is scheduled as the root is,
/// beside an opaque definition, which stays opaque.
#[test]
fn a_marked_cut_in_a_definition_spawns_there()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let first = core.computation_return(unit);
    let x = variable(&mut core, Outward(0));
    let returned = core.computation_return(x);
    let program = core.computation_bind(first, returned);

    let suspended = core.value_thunk(first);
    let spawn = spawning(&mut core, suspended);
    let handle = variable(&mut core, Outward(0));
    let read = reading(&mut core, handle);
    let read_then = core.computation_bind(read, returned);
    let by_hand = core.computation_bind(spawn, read_then);

    let mut arena = CommandArena::new();
    let body = focused(
        &core,
        program,
        &mut arena,
        &core::iter::once(first).collect(),
    );
    let thunk = arena
        .mint_producer(ProducerNode::Thunk { body })
        .expect("the thunk mints");
    let mut definitions = Definitions::new();
    let defined = definitions.push(Definition::Transparent(thunk));
    let opaque = definitions.push(Definition::Opaque);
    let root = focused(&core, first, &mut arena, &Writers::NONE);
    let (_root, definitions) =
        spawn_independent(&mut arena, (root, &definitions)).expect("the program schedules");

    let Some(Definition::Transparent(thunk)) = definitions.get(defined)
    else {
        panic!("the definition stays transparent");
    };
    let Some(&ProducerNode::Thunk { body }) = arena.producer(thunk)
    else {
        panic!("the definition stays a thunk");
    };
    assert_eq!(
        written(&core, by_hand),
        render_command(&arena, body),
        "the definition's cut spawns its writer"
    );
    assert_eq!(
        Some(Definition::Opaque),
        definitions.get(opaque),
        "an opaque definition stays opaque"
    );
}

/// An arena with no marked binder is given back as it was: the root, the
/// definitions and the arena's mark.
#[test]
fn an_unmarked_arena_is_given_back_unchanged()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let first = core.computation_return(unit);
    let x = variable(&mut core, Outward(0));
    let returned = core.computation_return(x);
    let program = core.computation_bind(first, returned);

    let mut arena = CommandArena::new();
    let root = focused(&core, program, &mut arena, &Writers::NONE);
    let thunk = arena
        .mint_producer(ProducerNode::Thunk { body: root })
        .expect("the thunk mints");
    let mut definitions = Definitions::new();
    definitions.push(Definition::Transparent(thunk));
    let mark = arena.watermark();

    assert_eq!(
        Ok((root, definitions.clone())),
        spawn_independent(&mut arena, (root, &definitions)),
        "nothing is rewritten"
    );
    assert_eq!(mark, arena.watermark(), "nothing is minted");
}
