use gandr_core_term::CoreArena;

use super::*;
use crate::boundary::ProducerArity;
use crate::focus::focus_computation;

/// Focusing `return ()` yields one node per family and one command of
/// origin `return`, which the dump names with the total.
#[test]
fn stats_and_dump_report_a_terminal_cut()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let root = focus_computation(
        &core,
        returned,
        &mut arena,
        &mut provenance,
        &crate::Writers::NONE,
    )
    .expect("a closed term focuses");

    let population = stats(&arena);
    assert_eq!(NodeCount::from(1_usize), population.commands, "one command");
    assert_eq!(
        NodeCount::from(1_usize),
        population.producers,
        "one producer"
    );
    assert_eq!(
        NodeCount::from(1_usize),
        population.consumers,
        "one consumer"
    );
    assert_eq!(
        NodeCount::from(3_usize),
        population.total(),
        "three nodes in all"
    );

    assert_eq!(
        BTreeMap::from([(FocusOrigin::Return, NodeCount::from(1_usize))]),
        origin_histogram(&provenance),
        "the one command came from the return"
    );
    assert_eq!(
        "root [return]: ⟨() |+ ★⟩\nnodes: 1 producers, 1 consumers, 1 commands (3 total)",
        dump(&arena, &provenance, root),
        "the dump names the origin, the rendering and the total"
    );
}

/// Saturation distinguishes the exact ceiling from wrapping at either
/// addition.
#[test]
fn totals_saturate_at_both_addition_boundaries()
{
    for (producers, consumers, commands, expected) in [
        (0_usize, 0_usize, 0_usize, 0_usize),
        (2, 3, 1, 6),
        (usize::MAX.saturating_sub(1), 1, 0, usize::MAX),
        (usize::MAX.saturating_sub(1), 2, 0, usize::MAX),
        (1, usize::MAX.saturating_sub(1), 1, usize::MAX),
    ] {
        let population = Stats {
            producers: producers.into(),
            consumers: consumers.into(),
            commands: commands.into(),
        };
        assert_eq!(NodeCount::from(expected), population.total());
    }
}

/// Unequal family populations and missing provenance remain visible in the
/// dump.
#[test]
fn asymmetric_populations_and_unrecorded_roots_remain_distinct()
{
    use alloc::boxed::Box;

    use gandr_theory_cell_complexes::Polarity;

    use crate::il::ConstructorTag;
    use crate::il::ConsumerNode;
    use crate::il::ProducerNode;

    let mut arena = CommandArena::new();
    assert_eq!(
        Stats {
            producers: 0_usize.into(),
            consumers: 0_usize.into(),
            commands: 0_usize.into()
        },
        stats(&arena)
    );
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    arena
        .mint_consumer(ConsumerNode::Covariable(0_u32.into()))
        .expect("leaf");
    arena
        .mint_consumer(ConsumerNode::Covariable(1_u32.into()))
        .expect("leaf");
    let root = arena
        .mint_cut(Polarity::Positive, unit, top)
        .expect("children resolve");
    assert_eq!(
        Stats {
            producers: 2_usize.into(),
            consumers: 3_usize.into(),
            commands: 1_usize.into()
        },
        stats(&arena)
    );
    let provenance = Provenance::new();
    assert_eq!(
        "root [unrecorded]: ⟨() |+ ★⟩\nnodes: 2 producers, 3 consumers, 1 commands (6 total)",
        dump(&arena, &provenance, root)
    );
    assert_eq!(
        "root [unrecorded]: <dangling>\nnodes: 2 producers, 3 consumers, 1 commands (6 total)",
        dump(&arena, &provenance, CommandId::from(u32::MAX))
    );
}

/// Repeated and distinct origins count separately, while empty provenance
/// stays empty.
#[test]
fn histograms_count_repeated_origins_without_inventing_categories()
{
    let mut provenance = Provenance::new();
    assert_eq!(BTreeMap::new(), origin_histogram(&provenance));
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let thunk = core.value_thunk(returned);
    let forced = core.computation_force(thunk);
    let mut arena = CommandArena::new();
    focus_computation(
        &core,
        returned,
        &mut arena,
        &mut provenance,
        &crate::Writers::NONE,
    )
    .expect("closed return");
    let root = focus_computation(
        &core,
        forced,
        &mut arena,
        &mut provenance,
        &crate::Writers::NONE,
    )
    .expect("closed force");
    assert_eq!(
        BTreeMap::from([
            (FocusOrigin::Return, NodeCount::from(2_usize)),
            (FocusOrigin::Force, NodeCount::from(1_usize))
        ]),
        origin_histogram(&provenance)
    );
    let shown = dump(&arena, &provenance, root);
    assert!(shown.starts_with("root [force]: ⟨{force(α) ⇒ ⟨() |+ α0⟩} |+ force(★)⟩\n"));
}

/// Every origin focusing records is named in the dump's head: the root of
/// each control, memory, world and pure former, and a declaration's value.
#[test]
fn dumps_name_every_origin()
{
    use gandr_core_term::Zone;
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::memory::HoldGrade;
    use gandr_core_term::memory::MemoryForm;
    use gandr_core_term::world::World;
    use gandr_core_term::world::WorldForm;

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let ty = core.value_type_unit();
    let signature = EffectSig::new("E".into(), [EffectOp {
        name: "op".into(),
        payload: ty,
        reply: ty,
    }])
    .expect("one operation");
    let returned = core.computation_return(unit);
    let clauses = alloc::sync::Arc::from([EffectClause {
        operation: "op".into(),
        body: returned,
    }]);
    let performed = core.computation_perform(signature.clone(), "op".into(), unit);
    let handled = core.computation_handle(
        signature.clone(),
        performed,
        returned,
        alloc::sync::Arc::clone(&clauses),
    );
    let exercised = core.computation_exercise(zero, signature.clone(), "op".into(), unit);
    let scoped = core.computation_scope(signature, returned, returned, clauses);
    let resumed = core.computation_resume(zero, returned);
    let abandoned = core.computation_abandon(zero);
    let shifted = core.computation_shift(returned);
    let reset = core.computation_reset(returned);
    let with = core.computation_with(&[returned, returned]);
    let thunk = core.value_thunk(returned);
    let forced = core.computation_force(thunk);
    let fixed = core.computation_fixpoint(returned, gandr_kernel_term::FixpointEvidence::Partial);
    let lambda = core.computation_lambda(returned);
    let pair = core.value_tuple(&[unit, unit]);
    let split = core.computation_split(pair, 2_usize.into(), returned);
    let projected = core.computation_tuple_projection(pair, 1_usize.into());
    let nil = core.value_list_nil();
    let folded = core.computation_list_fold(ty, ty, nil, returned, returned);
    let function = core.computation_lambda(returned);
    let bound = core.computation_bind(returned, function);
    let bound = core.computation_application(bound, unit);
    let held = core.computation_memory(MemoryForm::Hold {
        value: unit,
        body: returned,
        grade: HoldGrade::Many,
    });
    let migrated = core.computation_world(WorldForm::Migrate {
        world: World::Host,
        body: returned,
    });
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let mut heads: alloc::vec::Vec<alloc::string::String> = [
        performed, handled, exercised, scoped, resumed, abandoned, reset, shifted, with, returned,
        forced, fixed, lambda, split, projected, folded, bound, held, migrated,
    ]
    .into_iter()
    .map(|computation| {
        let root = focus_computation(
            &core,
            computation,
            &mut arena,
            &mut provenance,
            &crate::Writers::NONE,
        )
        .expect("each former focuses");
        dump(&arena, &provenance, root)
    })
    .collect();
    let top = crate::focus::focus_top_value(
        &core,
        unit,
        &mut arena,
        &mut provenance,
        &crate::Writers::NONE,
    )
    .expect("a closed value focuses");
    heads.push(dump(&arena, &provenance, top));
    let heads: alloc::vec::Vec<&str> = heads
        .iter()
        .map(|shown| shown.split_once(": ").map_or("", |(head, _)| head))
        .collect();
    assert_eq!(heads, [
        "root [perform]",
        "root [handle]",
        "root [exercise]",
        "root [scope]",
        "root [resume]",
        "root [abandon]",
        "root [reset]",
        "root [shift]",
        "root [with]",
        "root [return]",
        "root [force]",
        "root [fixpoint]",
        "root [lambda]",
        "root [case]",
        "root [projection]",
        "root [list-fold]",
        "root [bind]",
        "root [memory]",
        "root [world]",
        "root [top-value]",
    ]);
}
