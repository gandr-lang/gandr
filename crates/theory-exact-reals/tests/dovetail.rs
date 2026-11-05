//! The refinement machine's obligations and outcomes, and its dovetailing
//! scheduler: each outcome by name, the minimum service of every live
//! obligation in each round, the budget and the cancellation of a run with
//! its resumption, and the replay of every certificate that a run gives.

use core::cell::Cell;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanError;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::StepCount;
use gandr_theory_exact_reals::Steps;
use gandr_theory_exact_reals::Stop;
use gandr_theory_exact_reals::SuspendReason;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::refine;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;
use proptest::prelude::*;

/// The laws evidence of every registered cut here.
///
/// # Specification
/// trivial.
fn laws() -> Evidence
{
    return Evidence::from(0_u32);
}

/// The dyadic `mantissa · 2^exponent`.
///
/// # Specification
/// trivial.
fn dyadic(
    mantissa: BigInt,
    exponent: Exponent,
) -> Dyadic
{
    return Dyadic::new(mantissa, exponent).unwrap();
}

/// `45/32`, a point of the lower cut of the square root of two.
///
/// # Specification
/// trivial.
fn below_root() -> Dyadic
{
    return dyadic(BigInt::from(45_u8), Exponent::from(-5_i32));
}

/// `3/2`, a point of the upper cut of the square root of two.
///
/// # Specification
/// trivial.
fn three_halves() -> Dyadic
{
    return dyadic(BigInt::from(3_u8), Exponent::from(-1_i32));
}

/// A plan whose root joins comparisons: `p < sqrt 2` at `p = 45/32`, `sqrt 2 <
/// sqrt 2`, `1 < 2`, `2 < 1`, `1 + 1 < 3`, and `sqrt 2 < 3/2`, each a node
/// that an obligation can name.
///
/// # Specification
/// trivial.
fn comparisons() -> ValidatedPlan
{
    let mut builder = PlanBuilder::new();
    let root = square_root_of_two(&mut builder, laws()).unwrap();
    let point = builder.real(Real::Constant(below_root())).unwrap();
    let one = builder.real(Real::Constant(Dyadic::from(1_i64))).unwrap();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let three = builder.real(Real::Constant(Dyadic::from(3_i64))).unwrap();
    let three_halves = builder.real(Real::Constant(three_halves())).unwrap();
    let sum = builder.real(Real::Add(one, one)).unwrap();
    let opens = [
        builder.open(Open::Less(point, root)).unwrap(),
        builder.open(Open::Less(root, root)).unwrap(),
        builder.open(Open::Less(one, two)).unwrap(),
        builder.open(Open::Less(two, one)).unwrap(),
        builder.open(Open::Less(sum, three)).unwrap(),
        builder.open(Open::Less(root, three_halves)).unwrap(),
    ];
    let mut joined = opens[0];
    for open in &opens[1 ..] {
        joined = builder.open(Open::Join(joined, *open)).unwrap();
    }
    let mut table = EvidenceTable::new();
    table.register(laws(), Judgement::CutLaws).unwrap();
    return admit(
        builder.finish(Root::Open(joined)).unwrap(),
        &Quotas::default(),
        &table,
    )
    .unwrap();
}

/// The first node of `plan` that `wanted` accepts.
///
/// # Specification
/// trivial.
fn find<Wanted>(
    plan: &ValidatedPlan,
    wanted: Wanted,
) -> NodeId
where
    Wanted: Fn(&ValidatedPlan, &Node) -> bool,
{
    let count = usize::from(plan.plan().node_count());
    return (0 .. count)
        .map(|index| NodeId::try_from(index).unwrap())
        .find(|&id| wanted(plan, plan.plan().node(id).unwrap()))
        .unwrap();
}

/// Whether a test accepts a node.
#[repr(transparent)]
struct Accepts(bool);

/// Whether the real at `id` of `plan` is the constant `value`.
///
/// # Specification
/// trivial.
fn constant(
    plan: &ValidatedPlan,
    id: NodeId,
    value: &Dyadic,
) -> Accepts
{
    return Accepts(
        matches!(plan.plan().node(id), Ok(&Node::Real(Real::Constant(ref held))) if held == value),
    );
}

/// Whether the real at `id` of `plan` is a cut.
///
/// # Specification
/// trivial.
fn cut(
    plan: &ValidatedPlan,
    id: NodeId,
) -> Accepts
{
    return Accepts(matches!(
        plan.plan().node(id),
        Ok(&Node::Real(Real::Cut(_)))
    ));
}

/// The steps that `dovetail` did on the obligation at `index`.
///
/// # Specification
/// trivial.
fn spent(
    dovetail: &Dovetail<'_>,
    index: Position,
) -> Steps
{
    return dovetail.spent(index).unwrap();
}

/// The comparison of `plan` whose operands `first` and `second` accept.
///
/// # Specification
/// trivial.
fn less<First, Second>(
    plan: &ValidatedPlan,
    first: First,
    second: Second,
) -> NodeId
where
    First: Fn(&ValidatedPlan, NodeId) -> Accepts,
    Second: Fn(&ValidatedPlan, NodeId) -> Accepts,
{
    return find(
        plan,
        |plan, node| matches!(*node, Node::Open(Open::Less(left, right)) if first(plan, left.node()).0 && second(plan, right.node()).0),
    );
}

/// `p < sqrt 2`, which settles, and `sqrt 2 < sqrt 2`, which never settles.
///
/// # Specification
/// trivial.
fn try_first(plan: &ValidatedPlan) -> [Obligation; 2]
{
    let point = below_root();
    let settles = less(plan, |plan, id| constant(plan, id, &point), cut);
    let never = less(plan, cut, cut);
    return [
        Obligation::new(plan, settles, Demand::Holds).unwrap(),
        Obligation::new(plan, never, Demand::Holds).unwrap(),
    ];
}

/// The quantum of `steps` steps.
///
/// # Specification
/// trivial.
fn quantum(steps: Steps) -> Quantum
{
    let steps = u32::try_from(u64::from(steps)).unwrap();
    return Quantum::from(NonZeroU32::new(steps).unwrap());
}

/// A budget that no test spends.
///
/// # Specification
/// trivial.
fn ample() -> Budget
{
    return Budget::from(u64::MAX);
}

/// The certificate of a certified outcome.
///
/// # Specification
/// trivial.
fn certificate(outcome: Option<Outcome<'_>>) -> &Certificate
{
    let Some(Outcome::Certified(certificate)) = outcome
    else {
        panic!("the obligation is certified, not {outcome:?}");
    };
    return certificate;
}

/// The conclusion that `certificate` replays to over `plan`.
///
/// # Specification
/// trivial.
fn replayed(
    plan: &ValidatedPlan,
    certificate: &Certificate,
) -> Conclusion
{
    return check(plan, certificate, &CheckerQuotas::default())
        .unwrap()
        .conclusion()
        .clone();
}

#[test]
fn an_obligation_names_a_node_of_its_sort()
{
    let plan = comparisons();
    let open = less(&plan, cut, cut);
    let real = find(&plan, |_, node| matches!(*node, Node::Real(Real::Cut(_))));
    let width = Demand::Encloses {
        width: Exponent::from(-8_i32),
    };
    assert!(Obligation::new(&plan, open, Demand::Holds).is_ok());
    assert!(Obligation::new(&plan, open, Demand::Fails).is_ok());
    assert!(Obligation::new(&plan, real, width).is_ok());
    assert_eq!(
        Obligation::new(&plan, open, width),
        Err(PlanError::WrongSort)
    );
    assert_eq!(
        Obligation::new(&plan, real, Demand::Holds),
        Err(PlanError::WrongSort)
    );
    let past = NodeId::try_from(usize::from(plan.plan().node_count())).unwrap();
    assert_eq!(
        Obligation::new(&plan, past, Demand::Holds),
        Err(PlanError::UnknownNode)
    );
}

#[test]
fn two_obligations_run_round_by_round()
{
    // The try-first of the unit: `45/32 < sqrt 2` beside `sqrt 2 < sqrt 2`,
    // one step a turn, one round a run.
    let plan = comparisons();
    let [settles, never_settles] = try_first(&plan);
    let mut dovetail = Dovetail::new(
        &plan,
        [settles, never_settles],
        quantum(Steps::from(1_u64)),
        CheckerQuotas::default(),
    );
    let mut round = 0_u64;
    let certified = loop {
        round += 1;
        let report = dovetail.run(ample(), Rounds::from(1_u64), || false);
        assert_eq!(report.work().rounds, 1);
        assert_eq!(report.outcome(Position::from(1)), Some(Outcome::Pending));
        match report.outcome(Position::from(0)) {
            Some(Outcome::Pending) => assert_eq!(report.stop(), Stop::Rounds),
            Some(Outcome::Certified(certificate)) => break certificate.clone(),
            other => panic!("round {round} gave {other:?}"),
        }
        assert!(round < 64, "the comparison settles within 64 rounds");
    };
    // One step a round: the comparison settles at the round of its last step,
    // and its sibling has had one step in each round.
    assert_eq!(
        StepCount::from(usize::try_from(round).unwrap()),
        certified.step_count()
    );
    assert_eq!(
        dovetail.spent(Position::from(1)).map(u64::from),
        Some(round)
    );
    let settles = try_first(&plan)[0].node();
    assert_eq!(replayed(&plan, &certified), Conclusion::Holds {
        open: settles
    });
}

#[test]
fn each_live_obligation_gets_its_quantum_in_each_round()
{
    // A divergent sibling before and after the settling comparison: the
    // comparison settles at the same round with the same certificate.
    let plan = comparisons();
    let [settles, never_settles] = try_first(&plan);
    let mut settled = Vec::new();
    for (order, index) in [
        ([never_settles, settles], 1_usize),
        ([settles, never_settles], 0),
    ] {
        let mut dovetail = Dovetail::new(
            &plan,
            order,
            quantum(Steps::from(3_u64)),
            CheckerQuotas::default(),
        );
        let divergent = 1 - index;
        for round in 1_u64 .. 64 {
            let certified = match dovetail
                .run(ample(), Rounds::from(1_u64), || false)
                .outcome(Position::from(index))
            {
                Some(Outcome::Certified(certificate)) => Some(certificate.clone()),
                Some(Outcome::Pending) => None,
                other => panic!("round {round} gave {other:?}"),
            };
            assert_eq!(
                dovetail.spent(Position::from(divergent)).map(u64::from),
                Some(round * 3),
                "the divergent sibling's quantum"
            );
            if let Some(certificate) = certified {
                settled.push((round, certificate));
                break;
            }
        }
    }
    assert_eq!(settled.len(), 2);
    assert_eq!(settled[0], settled[1]);
}

#[test]
fn a_run_past_its_budget_is_exhausted_and_resumes()
{
    let plan = comparisons();
    let [settles, never_settles] = try_first(&plan);
    let mut whole = Dovetail::new(
        &plan,
        [never_settles, settles],
        quantum(Steps::from(2_u64)),
        CheckerQuotas::default(),
    );
    let uninterrupted = certificate(
        whole
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(1)),
    )
    .clone();
    let mut split = Dovetail::new(
        &plan,
        [never_settles, settles],
        quantum(Steps::from(2_u64)),
        CheckerQuotas::default(),
    );
    let report = split.run(Budget::from(5_u64), Rounds::from(64_u64), || false);
    assert_eq!(report.stop(), Stop::Budget);
    assert_eq!(
        report.work().steps,
        5,
        "the run stops at its budget and not past it"
    );
    assert_eq!(report.outcome(Position::from(0)), Some(Outcome::Exhausted));
    assert_eq!(report.outcome(Position::from(1)), Some(Outcome::Exhausted));
    assert_eq!(
        u64::from(spent(&split, Position::from(0))) + u64::from(spent(&split, Position::from(1))),
        5
    );
    let resumed = certificate(
        split
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(1)),
    )
    .clone();
    assert_eq!(resumed, uninterrupted);
    assert_eq!(
        spent(&split, Position::from(1)),
        spent(&whole, Position::from(1))
    );
}

#[test]
fn a_cancelled_run_resumes_at_the_next_turn()
{
    let plan = comparisons();
    let [settles, never_settles] = try_first(&plan);
    let mut whole = Dovetail::new(
        &plan,
        [settles, never_settles],
        quantum(Steps::from(1_u64)),
        CheckerQuotas::default(),
    );
    let uninterrupted = certificate(
        whole
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(0)),
    )
    .clone();
    let mut cancelled = Dovetail::new(
        &plan,
        [settles, never_settles],
        quantum(Steps::from(1_u64)),
        CheckerQuotas::default(),
    );
    // The third turn is cancelled: the first obligation has had two turns and
    // the second one, so the next turn is the second obligation's.
    let asked = Cell::new(0_u32);
    let report = cancelled.run(ample(), Rounds::from(64_u64), || {
        asked.set(asked.get() + 1);
        asked.get() == 4
    });
    assert_eq!(report.stop(), Stop::Cancelled);
    assert_eq!(report.outcome(Position::from(0)), Some(Outcome::Cancelled));
    assert_eq!(report.outcome(Position::from(1)), Some(Outcome::Cancelled));
    assert_eq!(
        (
            spent(&cancelled, Position::from(0)),
            spent(&cancelled, Position::from(1))
        ),
        (Steps::from(2_u64), Steps::from(1_u64))
    );
    let report = cancelled.run(ample(), Rounds::from(1_u64), || false);
    assert_eq!(
        report.work().steps,
        1,
        "the resumed run completes the round it stopped in"
    );
    assert_eq!(
        (
            spent(&cancelled, Position::from(0)),
            spent(&cancelled, Position::from(1))
        ),
        (Steps::from(2_u64), Steps::from(2_u64))
    );
    let resumed = certificate(
        cancelled
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(0)),
    )
    .clone();
    assert_eq!(resumed, uninterrupted);
}

#[test]
fn each_form_settles_or_suspends_by_name()
{
    let plan = comparisons();
    let quotas = CheckerQuotas::default();
    let one = Dyadic::from(1_i64);
    let two = Dyadic::from(2_i64);
    let root = find(&plan, |_, node| matches!(*node, Node::Real(Real::Cut(_))));
    let sum = find(&plan, |_, node| matches!(*node, Node::Real(Real::Add(..))));
    let ascending = less(
        &plan,
        |plan, id| constant(plan, id, &one),
        |plan, id| constant(plan, id, &two),
    );
    let descending = less(
        &plan,
        |plan, id| constant(plan, id, &two),
        |plan, id| constant(plan, id, &one),
    );
    let summed = less(&plan, |_, id| Accepts(id == sum), |_, _| Accepts(true));
    let above = less(&plan, cut, |plan, id| constant(plan, id, &three_halves()));
    let join = find(&plan, |_, node| matches!(*node, Node::Open(Open::Join(..))));
    let width = Exponent::from(-20_i32);
    let obligations = [
        Obligation::new(&plan, root, Demand::Encloses { width }).unwrap(),
        Obligation::new(&plan, ascending, Demand::Holds).unwrap(),
        Obligation::new(&plan, descending, Demand::Holds).unwrap(),
        Obligation::new(&plan, descending, Demand::Fails).unwrap(),
        Obligation::new(&plan, sum, Demand::Encloses { width }).unwrap(),
        Obligation::new(&plan, summed, Demand::Holds).unwrap(),
        Obligation::new(&plan, join, Demand::Holds).unwrap(),
        Obligation::new(&plan, above, Demand::Fails).unwrap(),
    ];
    let mut dovetail = Dovetail::new(&plan, obligations, quantum(Steps::from(4_u64)), quotas);
    let report = dovetail.run(ample(), Rounds::from(64_u64), || false);
    assert_eq!(report.stop(), Stop::Settled);
    // The enclosure is the refinement that `refine` writes.
    assert_eq!(
        *certificate(report.outcome(Position::from(0))),
        refine(&plan, root, width, &quotas).unwrap()
    );
    assert_eq!(
        replayed(&plan, certificate(report.outcome(Position::from(1)))),
        Conclusion::Holds { open: ascending }
    );
    assert_eq!(
        report.outcome(Position::from(2)),
        Some(Outcome::Suspended(SuspendReason::Opposed))
    );
    assert_eq!(
        replayed(&plan, certificate(report.outcome(Position::from(3)))),
        Conclusion::Fails { open: descending }
    );
    assert_eq!(
        report.outcome(Position::from(4)),
        Some(Outcome::Suspended(SuspendReason::NoRule))
    );
    assert_eq!(
        report.outcome(Position::from(5)),
        Some(Outcome::Suspended(SuspendReason::NoRule))
    );
    assert_eq!(
        report.outcome(Position::from(6)),
        Some(Outcome::Suspended(SuspendReason::NoRule))
    );
    assert_eq!(
        report.outcome(Position::from(7)),
        Some(Outcome::Suspended(SuspendReason::Opposed))
    );
    // A step quota below what the width needs suspends the enclosure.
    let short = CheckerQuotas {
        steps: StepCount::from(3_usize),
        ..CheckerQuotas::default()
    };
    let mut bounded = Dovetail::new(
        &plan,
        [Obligation::new(&plan, root, Demand::Encloses { width }).unwrap()],
        quantum(Steps::from(4_u64)),
        short,
    );
    let report = bounded.run(ample(), Rounds::from(64_u64), || false);
    assert_eq!(
        report.outcome(Position::from(0)),
        Some(Outcome::Suspended(SuspendReason::Quota))
    );
    assert_eq!(spent(&bounded, Position::from(0)), Steps::from(3_u64));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Generated comparisons with the square root of two, asked for either
    /// pole and run under generated quanta, budgets and rounds: the work stays
    /// within the budget, each certificate replays to its demand, and two
    /// schedulers given one input agree.
    #[test]
    fn every_certificate_replays_to_its_evidence(
        mantissa in 1_i64 .. 4096,
        shift in 1_i32 .. 12_i32,
        poles in proptest::collection::vec(any::<bool>(), 1 .. 6),
        steps in 1_u32 .. 8,
        budget in 0_u64 .. 400,
        rounds in 0_u64 .. 80,
    ) {
        let point = dyadic(BigInt::from(mantissa), Exponent::from(shift.checked_neg().unwrap()));
        let mut builder = PlanBuilder::new();
        let root = square_root_of_two(&mut builder, laws()).unwrap();
        let constant_node = builder.real(Real::Constant(point.clone())).unwrap();
        let below = builder.open(Open::Less(constant_node, root)).unwrap();
        let above = builder.open(Open::Less(root, constant_node)).unwrap();
        let joined = builder.open(Open::Join(below, above)).unwrap();
        let mut table = EvidenceTable::new();
        table.register(laws(), Judgement::CutLaws).unwrap();
        let plan = admit(builder.finish(Root::Open(joined)).unwrap(), &Quotas::default(), &table).unwrap();
        let opens = [
            less(&plan, |plan, id| constant(plan, id, &point), cut),
            less(&plan, cut, |plan, id| constant(plan, id, &point)),
        ];
        let obligations: Vec<Obligation> = poles
            .iter()
            .enumerate()
            .map(|(index, &holds)| {
                let demand = if holds { Demand::Holds } else { Demand::Fails };
                Obligation::new(&plan, opens[index % 2], demand).unwrap()
            })
            .collect();
        let mut first = Dovetail::new(&plan, obligations.clone(), quantum(Steps::from(u64::from(steps))), CheckerQuotas::default());
        let mut second = Dovetail::new(&plan, obligations.clone(), quantum(Steps::from(u64::from(steps))), CheckerQuotas::default());
        let report = first.run(Budget::from(budget), Rounds::from(rounds), || false);
        let again = second.run(Budget::from(budget), Rounds::from(rounds), || false);
        prop_assert!(report.work().steps <= budget);
        prop_assert_eq!(report.work(), again.work());
        prop_assert_eq!(report.stop(), again.stop());
        for (index, obligation) in obligations.iter().enumerate() {
            let outcome = report.outcome(Position::from(index));
            prop_assert_eq!(outcome, again.outcome(Position::from(index)));
            match outcome {
                Some(Outcome::Certified(certificate)) => {
                    let conclusion = replayed(&plan, certificate);
                    let wanted = match obligation.demand() {
                        Demand::Holds => Some(Conclusion::Holds { open: obligation.node() }),
                        Demand::Fails => Some(Conclusion::Fails { open: obligation.node() }),
                        Demand::Encloses { .. } => None,
                    };
                    prop_assert_eq!(Some(conclusion), wanted);
                },
                Some(Outcome::Suspended(reason)) => prop_assert_eq!(reason, SuspendReason::Opposed),
                Some(Outcome::Pending | Outcome::Exhausted | Outcome::Cancelled) | None => {},
            }
        }
        // The point lies on one side of the irrational root, so no run ever
        // certifies both poles of one comparison.
        for open in opens {
            let poles: Vec<Conclusion> = (0 .. obligations.len())
                .filter(|&index| obligations[index].node() == open)
                .filter_map(|index| match report.outcome(Position::from(index)) {
                    Some(Outcome::Certified(certificate)) => Some(replayed(&plan, certificate)),
                    _ => None,
                })
                .collect();
            let both = poles.contains(&Conclusion::Holds { open }) && poles.contains(&Conclusion::Fails { open });
            prop_assert!(!both, "one comparison is certified at both poles");
        }
    }
}
