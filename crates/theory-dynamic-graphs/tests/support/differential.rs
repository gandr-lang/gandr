//! The **zero-drift differential**: every incremental verdict is compared
//! against the batch acyclicity answer over the same edge set, offer by offer.
//!
//! The comparison is direct rather than translated. The incremental structure
//! refuses with a [`gandr_theory_graphs::CycleWitness`] and the batch oracle
//! answers with the same type, so a divergence is a disagreement about the
//! graph and never about how two vocabularies line up.
//!
//! Four things are checked at every step, and the last two are what make this a
//! differential rather than a smoke test: the verdict matches the batch answer;
//! a refusal's witness is a closed walk whose every edge is really present; the
//! maintained order is still topological; and the retained graph is still
//! acyclic under the batch traversal.
//!
//! # The teeth
//!
//! A differential nobody has seen fail proves nothing about its own
//! sensitivity, so `the_differential_catches_a_seeded_wrong_verdict` runs the
//! same harness with one verdict deliberately reported backwards — at every
//! position in turn — and requires the comparison to reject each run. The
//! companion corruption, a maintained order rewritten behind the structure's
//! back, is seeded in the crate's own unit tests where the private state is
//! reachable.

use anodized::spec;
use gandr_theory_dynamic_graphs::AcyclicityMaintenance;
use gandr_theory_dynamic_graphs::EdgeVerdict;
use gandr_theory_graphs::EdgeId;
use gandr_theory_graphs::cycle_witness;

use crate::support::BatchGraph;
use crate::support::Cost;
use crate::support::Depth;
use crate::support::NodeSpan;
use crate::support::Tally;

/// A deliberate fault injected into a run, so the differential can be shown to
/// catch one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fault
{
    /// The run is honest.
    None,
    /// The offer at this position reports the opposite of the verdict the
    /// structure actually returned.
    FlipVerdictAt(Depth),
}

/// What one run measured.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Report
{
    /// Offers made.
    pub offers: Tally,
    /// Offers admitted without moving anything.
    pub admitted: Tally,
    /// Offers admitted after a repair.
    pub repaired: Tally,
    /// Offers refused.
    pub refused: Tally,
    /// Nodes the bounded searches reached, in total.
    pub visited: Cost,
    /// Nodes moved in the maintained order, in total.
    pub relocated: Cost,
    /// What a batch recheck of every offer would have cost.
    pub batch_cost: Cost,
}

impl Report
{
    /// The visited-plus-relocated operation projection.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn incremental_cost(self) -> Cost
    {
        self.visited.plus(self.relocated)
    }
}

/// Runs one stream through maintenance against the independent batch oracle.
///
/// # Specification
/// - ensures: every compared verdict agrees with the batch answer; refusal
///   walks use actual candidate edges, and every retained prefix stays acyclic.
/// - fails: returns a diagnostic for the first wrong verdict, invalid walk,
///   invariant failure, or insertion/traversal error.
/// - panics: only for fixture identities outside the host address space.
///
/// # Adequacy
/// - hypothesis: finite fixture streams distinguish invalid graph observations
///   and incomplete comparisons through L2 agreement and L3 exact boundaries.
/// - witness: `dynamic_graphs::differential::tests::the_differential_catches_a_seeded_wrong_verdict`
#[inline]
#[spec(ensures: |ret| ret.as_ref().map_or(true, |report| usize::try_from(u64::from(report.offers)) == Ok(offers.len()) && report.admitted.plus(report.repaired).plus(report.refused) == report.offers))]
pub fn run(
    offers: &[EdgeId],
    nodes: NodeSpan,
    fault: Fault,
) -> Result<Report, String>
{
    let mut structure =
        AcyclicityMaintenance::new().map_err(|failure| format!("construction: {failure}"))?;
    let mut admitted: Vec<EdgeId> = Vec::new();
    let mut report = Report::default();

    for (position, &offer) in offers.iter().enumerate() {
        let here = Depth::from(position);
        report.offers = report.offers.increment();

        // The oracle: a graph built from nothing but the admitted edges plus
        // this offer, decided by the ordinary batch traversal.
        let mut candidate = BatchGraph::with_edges(nodes, &admitted);
        candidate.add(offer);
        let batch_refuses = bool::from(candidate.has_cycle());
        report.batch_cost = report.batch_cost.plus(candidate.batch_cost());

        let verdict = structure
            .insert_edge(offer)
            .map_err(|failure| format!("offer {here}: insertion failed: {failure}"))?;
        let truly_refused = matches!(verdict, EdgeVerdict::Refused(_));
        let reported_refused = match fault {
            | Fault::FlipVerdictAt(at) if at == here => !truly_refused,
            | Fault::FlipVerdictAt(_) | Fault::None => truly_refused,
        };
        if reported_refused != batch_refuses {
            return Err(format!(
                "offer {here} ({offer}): incremental refused={reported_refused}, \
                 batch refused={batch_refuses}"
            ));
        }

        match verdict {
            | EdgeVerdict::Refused(witness) => {
                report.refused = report.refused.increment();
                if witness.nodes.first() != witness.nodes.last() {
                    return Err(format!("offer {here}: the witness walk is not closed"));
                }
                if witness.nodes.len() < 2 {
                    return Err(format!("offer {here}: the witness walk is empty"));
                }
                let mut present = BatchGraph::with_edges(nodes, &admitted);
                present.add(offer);
                for &step in &witness.edges {
                    if !bool::from(present.holds(step)) {
                        return Err(format!(
                            "offer {here}: witness edge {step} is not in the graph"
                        ));
                    }
                }
                let walked: Vec<EdgeId> = witness
                    .nodes
                    .windows(2)
                    .filter_map(|pair| match *pair {
                        | [source, target] => Some(EdgeId::new(source, target)),
                        | _ => None,
                    })
                    .collect();
                if walked != witness.edges {
                    return Err(format!(
                        "offer {here}: the witness edges do not follow its own walk"
                    ));
                }
            },
            | EdgeVerdict::Admitted => {
                report.admitted = report.admitted.increment();
                admitted.push(offer);
            },
            | EdgeVerdict::AdmittedAfterRepair => {
                report.repaired = report.repaired.increment();
                admitted.push(offer);
            },
        }

        if !bool::from(structure.order_is_topological()) {
            return Err(format!(
                "offer {here}: an admitted edge runs backwards in the maintained order"
            ));
        }
        let retained = cycle_witness(&structure)
            .map_err(|failure| format!("offer {here}: batch check failed: {failure}"))?;
        if retained.is_some() {
            return Err(format!("offer {here}: the retained graph holds a cycle"));
        }
    }

    let telemetry = structure.telemetry();
    report.visited = Cost::from(u64::from(telemetry.nodes_visited));
    report.relocated = Cost::from(u64::from(telemetry.nodes_relocated));
    Ok(report)
}

#[cfg(test)]
mod tests
{
    use gandr_theory_graphs::NodeId;
    use proptest::prelude::*;

    use super::*;
    use crate::support::Bound;
    use crate::support::Family;
    use crate::support::Seed;
    use crate::support::StreamLength;
    use crate::support::stream;

    /// The stream shape the property runs over: a small node span and a run of
    /// ordered pairs over it, self loops excluded so the property measures the
    /// interesting refusals rather than the trivial one.
    ///
    /// # Specification
    /// trivial.
    fn stream_strategy() -> impl Strategy<Value = (NodeSpan, Vec<EdgeId>)>
    {
        (4usize .. 12usize).prop_flat_map(|nodes| {
            let bound = u32::try_from(nodes).expect("a small node count fits");
            let pairs = proptest::collection::vec((0 .. bound, 0 .. bound), 0 .. 48);
            (Just(NodeSpan::from(nodes)), pairs).prop_map(|(span, drawn)| {
                let offers = drawn
                    .into_iter()
                    .filter(|&(source, target)| source != target)
                    .map(|(source, target)| EdgeId::new(NodeId::from(source), NodeId::from(target)))
                    .collect();
                (span, offers)
            })
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 192, failure_persistence: Some(Box::new(proptest::test_runner::FileFailurePersistence::Direct("tests/support/differential.proptest-regressions"))), rng_seed: proptest::test_runner::RngSeed::Fixed(0xD06), .. ProptestConfig::default() })]

        /// Zero drift: every incremental verdict equals the batch answer over
        /// the admitted edges plus the offer, and the structure's own
        /// invariants hold after every step.
        #[test]
        fn incremental_verdicts_equal_the_batch_answer((nodes, offers) in stream_strategy())
        {
            let outcome = run(&offers, nodes, Fault::None);
            prop_assert!(
                outcome.is_ok(),
                "{}",
                outcome.err().unwrap_or_else(|| "unreachable".to_owned())
            );
        }
    }

    #[test]
    fn every_stream_family_is_drift_free()
    {
        let nodes = Bound::from(24u32);
        let length = StreamLength::from(400usize);
        for family in Family::all() {
            for seed in 0u64 .. 8u64 {
                let offers = stream(family, nodes, length, Seed::from(seed));
                let outcome = run(&offers, NodeSpan::from(nodes), Fault::None);
                assert!(
                    outcome.is_ok(),
                    "{} seed {seed}: {}",
                    family.label(),
                    outcome.err().unwrap_or_default()
                );
            }
        }
    }

    #[test]
    fn the_differential_catches_a_seeded_wrong_verdict()
    {
        let nodes = Bound::from(16u32);
        let length = StreamLength::from(200usize);
        let offers = stream(Family::Interleaved, nodes, length, Seed::from(11));
        let span = NodeSpan::from(nodes);
        let honest = run(&offers, span, Fault::None).expect("the honest run is drift free");
        assert!(
            bool::from(honest.refused.is_positive())
                && bool::from(honest.admitted.plus(honest.repaired).is_positive()),
            "the stream must exercise both answers for a flip to be meaningful"
        );

        // Every single-offer flip must be caught: a differential that only
        // notices some wrong verdicts is not a gate.
        for position in 0 .. offers.len() {
            let corrupted = run(&offers, span, Fault::FlipVerdictAt(Depth::from(position)));
            assert!(
                corrupted.is_err(),
                "a verdict reported backwards at offer {position} slipped through"
            );
        }
    }

    #[test]
    fn a_single_shot_graph_costs_more_than_one_batch_check()
    {
        // The other side of the amortization: a consumer that builds a graph,
        // asks once, and discards it gets nothing back for the structure it
        // paid to build. The maintenance must offer every edge and create every
        // node before it can answer, which is already the whole batch pass, and
        // any repair is on top.
        //
        // The sizes swept here are the range a per-call graph actually reaches,
        // where the fixed cost dominates and the amortized advantage has no
        // stream to accumulate over.
        let mut rows: Vec<(Bound, usize, Cost, Cost)> = Vec::new();
        for span in [4u32, 8, 16, 24] {
            let nodes = Bound::from(span);
            let width = usize::from(NodeSpan::from(nodes));
            let length = StreamLength::from(width.saturating_mul(2));
            let offers = stream(Family::Interleaved, nodes, length, Seed::from(7));

            let mut structure = AcyclicityMaintenance::new().expect("construction succeeds");
            let mut offered = Tally::default();
            for &offer in &offers {
                structure.insert_edge(offer).expect("insertion succeeds");
                offered = offered.increment();
            }
            let telemetry = structure.telemetry();
            // Every offer costs at least its order comparison, and every node
            // costs its insertion into the order; the searches and relocations
            // are what a batch check never pays.
            let single_shot = Cost::from(u64::from(offered))
                .plus(Cost::from(u64::from(u32::from(structure.nodes()))))
                .plus(Cost::from(u64::from(telemetry.nodes_visited)))
                .plus(Cost::from(u64::from(telemetry.nodes_relocated)));

            let batch = BatchGraph::with_edges(NodeSpan::from(nodes), &offers).batch_cost();
            rows.push((nodes, offers.len(), single_shot, batch));
        }

        println!("nodes  edges  single-shot  one batch check");
        for &(nodes, edges, single_shot, batch) in &rows {
            println!("{nodes:>5}  {edges:>5}  {single_shot:>11}  {batch:>16}");
        }

        for &(nodes, _edges, single_shot, batch) in &rows {
            assert!(
                u64::from(single_shot) >= u64::from(batch),
                "at {nodes} nodes the maintenance paid {single_shot} against one batch check's \
                 {batch}, which would make a per-call graph worth maintaining"
            );
        }
    }

    #[test]
    fn amortized_cost_is_below_batch_recheck()
    {
        let nodes = Bound::from(64u32);
        let length = StreamLength::from(1200usize);
        let mut rows: Vec<(Family, Report)> = Vec::new();
        for family in Family::all() {
            let offers = stream(family, nodes, length, Seed::from(4));
            let report =
                run(&offers, NodeSpan::from(nodes), Fault::None).expect("the run is drift free");
            rows.push((family, report));
        }

        println!("family                  offers  admit  repair  refuse  incremental  batch");
        for &(family, report) in &rows {
            println!(
                "{:<22}  {:>6}  {:>5}  {:>6}  {:>6}  {:>11}  {:>5}",
                family.label(),
                report.offers,
                report.admitted,
                report.repaired,
                report.refused,
                report.incremental_cost(),
                report.batch_cost
            );
        }

        for &(family, report) in &rows {
            assert!(
                u64::from(report.incremental_cost()) < u64::from(report.batch_cost),
                "{}: the maintenance paid {} against a batch recheck's {}",
                family.label(),
                report.incremental_cost(),
                report.batch_cost
            );
        }
    }
}
