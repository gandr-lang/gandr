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
    let root = focus_computation(&core, returned, &mut arena, &mut provenance)
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
    focus_computation(&core, returned, &mut arena, &mut provenance).expect("closed return");
    let root = focus_computation(&core, forced, &mut arena, &mut provenance).expect("closed force");
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
