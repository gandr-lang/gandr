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
    /// - hypothesis: L3 — the terminal cut's one node per family sums to three.
    /// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
    #[inline]
    #[must_use]
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
/// - hypothesis: L3 — as [`Stats::total`].
/// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — as [`Stats::total`].
/// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — as [`Stats::total`].
/// - witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`
#[inline]
#[must_use]
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
}
