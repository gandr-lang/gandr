//! Inspection: the population of an arena, the provenance of its commands,
//! and a textual dump of a focused root.
//!
//! [`stats`] counts an arena's three node families, [`origin_histogram`]
//! counts the commands focusing created by the core former each was created
//! for — the un-sugaring view of a focused term — and [`dump`] combines a
//! root's rendering, its origin and the population in one view.

use alloc::collections::BTreeMap;
use alloc::string::String;

use crate::boundary::NodeCount;
use crate::focus::FocusOrigin;
use crate::focus::Provenance;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::pretty::render_command;

/// The node population of an arena.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Stats
{
    /// The producer nodes.
    pub producers: NodeCount,
    /// The consumer nodes.
    pub consumers: NodeCount,
    /// The command nodes.
    pub commands: NodeCount,
}

impl Stats
{
    /// The nodes across the three families.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the saturating sum of the three counts.
    /// - provides: the figure a dump reports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and distinct ordinary counts, the exact ceiling
    ///   and overflow at each addition are observed by the exact total. These
    ///   distinguish omitted families, wrapping and premature saturation.
    /// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
    /// - witness: `inspect::tests::totals_saturate_at_both_addition_boundaries`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| usize::from(ret) == usize::from(self.producers)
        .saturating_add(usize::from(self.consumers)).saturating_add(usize::from(self.commands)))]
    pub fn total(&self) -> NodeCount
    {
        NodeCount::from(
            usize::from(self.producers)
                .saturating_add(usize::from(self.consumers))
                .saturating_add(usize::from(self.commands)),
        )
    }
}

/// The node population of an arena.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the counts are exactly the arena's family lengths.
/// - provides: the population view.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and asymmetrically populated arenas expose swapped
///   or omitted family counts; exact totals and dump fields observe all three
///   families without assuming they grow together.
/// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
/// - witness: `inspect::tests::asymmetric_populations_and_unrecorded_roots_remain_distinct`
#[inline]
#[must_use]
#[anodized::spec(ensures: |ret| ret.producers == arena.producer_count()
    && ret.consumers == arena.consumer_count() && ret.commands == arena.command_count())]
pub fn stats(arena: &CommandArena) -> Stats
{
    Stats {
        producers: arena.producer_count(),
        consumers: arena.consumer_count(),
        commands: arena.command_count(),
    }
}

/// How many commands each core former contributed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the counts sum to the number of commands `provenance` records,
///   keyed by [`FocusOrigin`] in its declaration order.
/// - provides: the un-sugaring view of a focused term.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty provenance and two distinct origins with unequal
///   multiplicities have exact maps. This distinguishes omitted entries,
///   exchanged keys, overwritten counts and invented zero-count categories.
/// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
/// - witness: `inspect::tests::histograms_count_repeated_origins_without_inventing_categories`
#[inline]
#[must_use]
#[anodized::spec(ensures: |ref ret|
    ret.values().try_fold(0_usize, |total, &count| total.checked_add(usize::from(count))) == Some(usize::from(provenance.len()))
        && ret.iter().all(|(origin, count)| usize::from(*count) > 0
            && usize::from(*count) == provenance.entries().filter(|&(_, found)| found == *origin).count())
)]
pub fn origin_histogram(provenance: &Provenance) -> BTreeMap<FocusOrigin, NodeCount>
{
    let mut histogram: BTreeMap<FocusOrigin, NodeCount> = BTreeMap::new();
    for (_, origin) in provenance.entries() {
        let count = histogram.entry(origin).or_default();
        *count = NodeCount::from(usize::from(*count).saturating_add(1));
    }
    histogram
}

/// A textual dump of a focused root: its rendering, its origin and the
/// arena's population.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two lines, `root [<origin>]: <rendering>` and the population with
///   its total; a root the table does not record shows as `unrecorded`.
/// - provides: the debugging view of a focused term.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — recorded, unrecorded and dangling roots have exact
///   two-line displays, and unequal family counts expose exchanged labels or
///   totals. A force root and a return root distinguish origin naming; this is
///   a structural debug view, not a parseable serialization format.
/// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
/// - witness: `inspect::tests::asymmetric_populations_and_unrecorded_roots_remain_distinct`
/// - witness: `inspect::tests::histograms_count_repeated_origins_without_inventing_categories`
#[inline]
#[must_use]
#[anodized::spec(ensures: |ref ret| ret.lines().count() == 2
    && ret.split_once('\n').is_some_and(|(_, population)| population.starts_with("nodes: ") && population.ends_with(" total)"))
    && ret.starts_with(match provenance.origin(root) {
        | Some(FocusOrigin::Return) => "root [return]: ",
        | Some(FocusOrigin::Force) => "root [force]: ",
        | Some(FocusOrigin::Lambda) => "root [lambda]: ",
        | Some(FocusOrigin::Case) => "root [case]: ",
        | Some(FocusOrigin::Bind) => "root [bind]: ",
        | Some(FocusOrigin::TopValue) => "root [top-value]: ",
        | None => "root [unrecorded]: ",
    })
)]
pub fn dump(
    arena: &CommandArena,
    provenance: &Provenance,
    root: CommandId,
) -> String
{
    let population = stats(arena);
    let origin = match provenance.origin(root) {
        | Some(FocusOrigin::Return) => "return",
        | Some(FocusOrigin::Force) => "force",
        | Some(FocusOrigin::Lambda) => "lambda",
        | Some(FocusOrigin::Case) => "case",
        | Some(FocusOrigin::Bind) => "bind",
        | Some(FocusOrigin::TopValue) => "top-value",
        | None => "unrecorded",
    };
    alloc::format!(
        "root [{origin}]: {}\nnodes: {} producers, {} consumers, {} commands ({} total)",
        render_command(arena, root),
        population.producers,
        population.consumers,
        population.commands,
        population.total()
    )
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;

    use super::*;
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
                tag: ConstructorTag::Unit,
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
        let root =
            focus_computation(&core, forced, &mut arena, &mut provenance).expect("closed force");
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
}
