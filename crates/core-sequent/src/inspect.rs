//! Inspection: the population of an arena, the provenance of its commands,
//! and a textual dump of a focused root.
//!
//! [`stats`] counts an arena's three node families, [`origin_histogram`]
//! counts the commands focusing created by the core former each was created
//! for — the un-sugaring view of a focused term — and [`dump`] combines a
//! root's rendering, its origin and the population in one view.

use alloc::collections::BTreeMap;
use alloc::string::String;

use anodized::spec;

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
    #[spec(ensures: |ret| usize::from(ret) == usize::from(self.producers)
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
#[spec(ensures: |ret| ret.producers == arena.producer_count()
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
#[spec(ensures: |ref ret|
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
/// - witness: `inspect::tests::dumps_name_every_origin`
#[inline]
#[must_use]
#[spec(ensures: |ref ret| ret.lines().count() == 2
    && ret.split_once('\n').is_some_and(|(_, population)| population.starts_with("nodes: ") && population.ends_with(" total)"))
    && ret.starts_with(match provenance.origin(root) {
        | Some(FocusOrigin::Perform) => "root [perform]: ",
        | Some(FocusOrigin::Handle) => "root [handle]: ",
        | Some(FocusOrigin::Exercise) => "root [exercise]: ",
        | Some(FocusOrigin::Scope) => "root [scope]: ",
        | Some(FocusOrigin::Resume) => "root [resume]: ",
        | Some(FocusOrigin::Abandon) => "root [abandon]: ",
        | Some(FocusOrigin::Reset) => "root [reset]: ",
        | Some(FocusOrigin::Shift) => "root [shift]: ",
        | Some(FocusOrigin::With) => "root [with]: ",
        | Some(FocusOrigin::Return) => "root [return]: ",
        | Some(FocusOrigin::Force) => "root [force]: ",
        | Some(FocusOrigin::Fixpoint) => "root [fixpoint]: ",
        | Some(FocusOrigin::Lambda) => "root [lambda]: ",
        | Some(FocusOrigin::Case) => "root [case]: ",
        | Some(FocusOrigin::Projection) => "root [projection]: ",
        | Some(FocusOrigin::ListFold) => "root [list-fold]: ",
        | Some(FocusOrigin::Bind) => "root [bind]: ",
        | Some(FocusOrigin::TopValue) => "root [top-value]: ",
        | Some(FocusOrigin::Memory) => "root [memory]: ",
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
        Some(FocusOrigin::Perform) => "perform",
        Some(FocusOrigin::Handle) => "handle",
        Some(FocusOrigin::Exercise) => "exercise",
        Some(FocusOrigin::Scope) => "scope",
        Some(FocusOrigin::Resume) => "resume",
        Some(FocusOrigin::Abandon) => "abandon",
        Some(FocusOrigin::Reset) => "reset",
        Some(FocusOrigin::Shift) => "shift",
        Some(FocusOrigin::With) => "with",
        Some(FocusOrigin::Return) => "return",
        Some(FocusOrigin::Force) => "force",
        Some(FocusOrigin::Fixpoint) => "fixpoint",
        Some(FocusOrigin::Lambda) => "lambda",
        Some(FocusOrigin::Case) => "case",
        Some(FocusOrigin::Projection) => "projection",
        Some(FocusOrigin::ListFold) => "list-fold",
        Some(FocusOrigin::Bind) => "bind",
        Some(FocusOrigin::TopValue) => "top-value",
        Some(FocusOrigin::Memory) => "memory",
        None => "unrecorded",
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
mod tests;
