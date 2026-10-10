//! The **weighted-edge probe**: where the graph-theoretic maintenance stops
//! agreeing with the offset-carrying one.
//!
//! The same edge stream is offered twice — once to
//! [`gandr_theory_dynamic_graphs::AcyclicityMaintenance`], which sees only the
//! edges, and once to [`gandr_theory_dynamic_graphs::PotentialMaintenance`],
//! which sees the offsets too. The probe records where their verdicts first
//! disagree, which is well defined precisely up to that point: before it the
//! two structures hold the same admitted set, and after it they do not, so
//! nothing past the first divergence is a comparison of like with like.
//!
//! # What is being located
//!
//! Acyclicity is a sound and incomplete approximation of offset satisfiability.
//! It is **exactly** complete when every offset is at least one, because every
//! cycle then sums positive and is genuinely unsatisfiable. Admit a zero offset
//! and completeness fails: a cycle summing to zero forces its nodes to share a
//! value and is satisfiable, while no topological order can hold it.
//!
//! So the probe is not looking for a bug. It measures the price of the
//! approximation as a function of the offsets — the divergence rate and the
//! stream depth at which the cheaper structure first over-refuses — and it pins
//! the direction: the order structure refuses a **superset** of what the
//! valuation refuses, never the other way round.

use anodized::spec;
use gandr_theory_dynamic_graphs::AcyclicityMaintenance;
use gandr_theory_dynamic_graphs::ConstraintVerdict;
use gandr_theory_dynamic_graphs::EdgeVerdict;
use gandr_theory_dynamic_graphs::Offset;
use gandr_theory_dynamic_graphs::PotentialMaintenance;
use gandr_theory_graphs::EdgeId;

use crate::support::Cost;
use crate::support::Depth;
use crate::support::DrawnOffset;
use crate::support::Generator;
use crate::support::Label;
use crate::support::Seed;
use crate::support::StreamLength;
use crate::support::Tally;

/// Which offsets a probe run draws from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Regime
{
    /// Every offset at least one: the trivial coupling, where every cycle sums
    /// positive and the order structure is exact.
    StrictlyPositive,
    /// Offsets may be zero: the first regime where a cycle can be satisfiable.
    WithZero,
    /// Offsets of either sign: the general level-constraint shape.
    Mixed,
}

impl Regime
{
    /// Every regime, for a test that sweeps them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn all() -> [Self; 3]
    {
        [Self::StrictlyPositive, Self::WithZero, Self::Mixed]
    }

    /// The offsets this regime draws from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn choices(self) -> Vec<DrawnOffset>
    {
        let raw: &[i64] = match self {
            | Self::StrictlyPositive => &[1, 2, 3],
            | Self::WithZero => &[0, 1, 2],
            | Self::Mixed => &[-2, -1, 0, 1, 2],
        };
        raw.iter().copied().map(DrawnOffset::from).collect()
    }

    /// A short name for a measurement row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn label(self) -> Label
    {
        match self {
            | Self::StrictlyPositive => Label::from("offsets >= 1"),
            | Self::WithZero => Label::from("offsets >= 0"),
            | Self::Mixed => Label::from("offsets of either sign"),
        }
    }
}

/// A deliberate fault injected into a probe run, so the direction check can be
/// shown to catch one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fault
{
    /// The run is honest.
    None,
    /// The offer at this position reports the valuation as refuting, whatever
    /// it actually answered — the converse direction the probe must reject.
    ForceRefutationAt(Depth),
}

/// What one probe run measured.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Row
{
    /// Offers compared, up to and including the first divergence.
    pub compared: Tally,
    /// Where the two structures first disagreed, when they did.
    pub first_divergence: Option<Depth>,
    /// Nodes the order structure's searches reached.
    pub order_cost: Cost,
    /// Constraints the valuation's propagation examined.
    pub valuation_cost: Cost,
}

/// Offers a stream to both structures and reports where they first disagree.
///
/// The direction is checked at every compared step: the valuation refuting
/// something the order admitted would mean an unsatisfiable set with no cycle
/// in it, which cannot happen, so it is reported as an error rather than
/// counted.
///
/// # Specification
/// - ensures: stops at the first order/valuation divergence and reports its
///   zero-based position; missing offsets mean zero.
/// - fails: reports insertion errors, broken invariants, or a valuation
///   refutation where the order admitted the same prefix.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: finite fixture streams distinguish invalid graph observations
///   and incomplete comparisons through L2 agreement and L3 exact boundaries.
/// - witness: `dynamic_graphs::probe::tests::the_probe_catches_a_seeded_converse_divergence`
#[inline]
#[spec(ensures: |ret| ret.as_ref().map_or(true, |row| usize::try_from(u64::from(row.compared)) == Ok(row.first_divergence.map_or(offers.len(), |depth| usize::from(depth).saturating_add(1)))))]
pub fn compare(
    offers: &[EdgeId],
    offsets: &[DrawnOffset],
    fault: Fault,
) -> Result<Row, String>
{
    let mut order =
        AcyclicityMaintenance::new().map_err(|failure| format!("construction: {failure}"))?;
    let mut valuation = PotentialMaintenance::new();
    let mut row = Row::default();

    for (position, &offer) in offers.iter().enumerate() {
        let here = Depth::from(position);
        let offset = offsets.get(position).copied().unwrap_or_default();
        row.compared = row.compared.increment();

        let order_verdict = order
            .insert_edge(offer)
            .map_err(|failure| format!("offer {here}: order insertion failed: {failure}"))?;
        let valuation_verdict = valuation
            .insert_constraint(offer, Offset::from(i64::from(offset)))
            .map_err(|failure| format!("offer {here}: constraint insertion failed: {failure}"))?;

        if !bool::from(order.order_is_topological()) {
            return Err(format!("offer {here}: the maintained order broke"));
        }
        if !bool::from(valuation.valuation_is_feasible()) {
            return Err(format!("offer {here}: the maintained valuation broke"));
        }

        let order_refused = matches!(order_verdict, EdgeVerdict::Refused(_));
        let truly_refuted = matches!(valuation_verdict, ConstraintVerdict::Refuted(_));
        let valuation_refuted = match fault {
            | Fault::ForceRefutationAt(at) if at == here => true,
            | Fault::ForceRefutationAt(_) | Fault::None => truly_refuted,
        };

        if valuation_refuted && !order_refused {
            return Err(format!(
                "offer {here} ({offer}, offset {offset}): the valuation refuted a constraint \
                 the order admitted, so an unsatisfiable set has no cycle in it"
            ));
        }
        if order_refused != valuation_refuted {
            row.first_divergence = Some(here);
            break;
        }
    }

    row.order_cost = Cost::from(u64::from(order.telemetry().nodes_visited))
        .plus(Cost::from(u64::from(order.telemetry().nodes_relocated)));
    row.valuation_cost = Cost::from(u64::from(valuation.telemetry().relaxations));
    Ok(row)
}

/// The offsets for one stream, drawn from `regime` under an explicit seed.
///
/// # Specification
/// - ensures: returns exactly the requested number of offsets, each chosen from
///   the selected regime, deterministically for the supplied seed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: finite fixture streams distinguish invalid graph observations
///   and incomplete comparisons through L2 agreement and L3 exact boundaries.
/// - witness: `dynamic_graphs::probe::tests::the_dichotomy_boundary_is_measured`
#[inline]
#[spec(ensures: |ret| ret.len() == usize::from(length) && { let choices = regime.choices(); ret.iter().all(|offset| choices.contains(offset)) })]
pub fn offsets_for(
    regime: Regime,
    length: StreamLength,
    seed: Seed,
) -> Vec<DrawnOffset>
{
    let choices = regime.choices();
    let mut generator = Generator::new(seed.companion());
    core::iter::repeat_with(|| generator.pick(&choices))
        .take(usize::from(length))
        .collect()
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::support::Bound;
    use crate::support::Family;
    use crate::support::stream;

    /// What one regime's sweep over every family and seed measured.
    struct Sweep
    {
        /// Runs performed.
        runs: Tally,
        /// Runs in which the two structures disagreed.
        diverged: Tally,
        /// Where each divergence happened.
        depths: Vec<Depth>,
        /// Total order-structure search cost.
        order_cost: Cost,
        /// Total valuation propagation cost.
        valuation_cost: Cost,
    }

    /// How many seeds every sweep draws.
    const SEEDS: u64 = 24;

    /// The node span and stream length every sweep uses.
    ///
    /// # Specification
    /// trivial.
    fn dimensions() -> (Bound, StreamLength)
    {
        (Bound::from(20u32), StreamLength::from(300usize))
    }

    /// Every stream family under one regime, summarized.
    ///
    /// # Specification
    /// trivial.
    fn sweep(regime: Regime) -> Sweep
    {
        let (nodes, length) = dimensions();
        let mut result = Sweep {
            runs: Tally::default(),
            diverged: Tally::default(),
            depths: Vec::new(),
            order_cost: Cost::default(),
            valuation_cost: Cost::default(),
        };
        for family in Family::all() {
            for seed in 0 .. SEEDS {
                let offers = stream(family, nodes, length, Seed::from(seed));
                let offsets =
                    offsets_for(regime, StreamLength::from(offers.len()), Seed::from(seed));
                let row = compare(&offers, &offsets, Fault::None).unwrap_or_else(|failure| {
                    panic!(
                        "{} seed {seed} under {}: {failure}",
                        family.label(),
                        regime.label()
                    )
                });
                result.runs = result.runs.increment();
                if let Some(depth) = row.first_divergence {
                    result.diverged = result.diverged.increment();
                    result.depths.push(depth);
                }
                result.order_cost = result.order_cost.plus(row.order_cost);
                result.valuation_cost = result.valuation_cost.plus(row.valuation_cost);
            }
        }
        result
    }

    #[test]
    fn strictly_positive_offsets_leave_the_order_structure_exact()
    {
        let result = sweep(Regime::StrictlyPositive);
        assert!(bool::from(result.runs.is_positive()), "the sweep ran");
        assert_eq!(
            Tally::default(),
            result.diverged,
            "with every offset at least one, every cycle sums positive, so the order structure \
             refuses exactly what the valuation refuses"
        );
    }

    #[test]
    fn a_zero_offset_breaks_the_agreement()
    {
        let result = sweep(Regime::WithZero);
        assert!(bool::from(result.runs.is_positive()), "the sweep ran");
        assert!(
            bool::from(result.diverged.is_positive()),
            "admitting a zero offset makes some cycle satisfiable, which the order structure \
             cannot represent and therefore over-refuses"
        );
    }

    #[test]
    fn acyclicity_refuses_a_superset_of_what_offsets_refute()
    {
        // The direction is the load-bearing claim: `compare` errors whenever the
        // valuation refutes something the order admitted, so a clean sweep over
        // every regime is the assertion.
        for regime in Regime::all() {
            let result = sweep(regime);
            assert!(
                bool::from(result.runs.is_positive()),
                "{}: the sweep ran",
                regime.label()
            );
        }
    }

    #[test]
    fn the_probe_catches_a_seeded_converse_divergence()
    {
        // The teeth: a run in which the valuation is reported as refuting an
        // offer the order admitted must be rejected, at every position where the
        // order admits.
        let (nodes, length) = dimensions();
        let offers = stream(Family::Interleaved, nodes, length, Seed::from(3));
        let offsets = offsets_for(
            Regime::StrictlyPositive,
            StreamLength::from(offers.len()),
            Seed::from(3),
        );
        let honest = compare(&offers, &offsets, Fault::None).expect("the honest run is clean");
        assert_eq!(
            None, honest.first_divergence,
            "strictly positive offsets do not diverge"
        );

        let mut caught = Tally::default();
        let mut attempted = Tally::default();
        for position in 0 .. offers.len() {
            let mut order = AcyclicityMaintenance::new().expect("construction succeeds");
            let mut admits_here = false;
            for (step, &offer) in offers.iter().enumerate() {
                let verdict = order.insert_edge(offer).expect("insertion succeeds");
                if step == position {
                    admits_here = !matches!(verdict, EdgeVerdict::Refused(_));
                    break;
                }
            }
            if !admits_here {
                continue;
            }
            attempted = attempted.increment();
            let corrupted = compare(
                &offers,
                &offsets,
                Fault::ForceRefutationAt(Depth::from(position)),
            );
            if corrupted.is_err() {
                caught = caught.increment();
            }
        }
        assert!(
            bool::from(attempted.is_positive()),
            "the stream admits somewhere"
        );
        assert_eq!(
            attempted, caught,
            "every seeded converse divergence must be rejected"
        );
    }

    #[test]
    fn the_dichotomy_boundary_is_measured()
    {
        let offers = [(0_u32, 1_u32), (1, 2), (2, 0), (9, 9)]
            .map(|(source, target)| EdgeId::new(source.into(), target.into()));
        let positive = [1_i64, 1, 1, 1].map(DrawnOffset::from);
        let zero = [0_i64, 0, 0, 1].map(DrawnOffset::from);
        let mixed = [1_i64, 1, -2, 1].map(DrawnOffset::from);
        let row = compare(&offers, &positive, Fault::None).expect("positive cycles agree");
        assert_eq!(row.first_divergence, None);
        assert_eq!(u64::from(row.compared), 4);
        for offsets in [zero, mixed] {
            let row = compare(&offers, &offsets, Fault::None).expect("nonpositive cycles diverge");
            assert_eq!(row.first_divergence, Some(Depth::from(2_usize)));
            assert_eq!(u64::from(row.compared), 3);
        }
    }
}
