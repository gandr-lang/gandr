//! The measurement of the refinement machine: one turn of a quantum on a
//! comparison that never settles, and a whole run of the try-first of the
//! scheduler.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `turn` | one round of a fresh scheduler over `sqrt 2 < sqrt 2`, which does one quantum of steps |
//! | `settle` | a fresh scheduler over `45/32 < sqrt 2` and `sqrt 2 < sqrt 2`, run until the first settles |
//!
//! Each row names the quantum and the steps that the run did. `cargo bench`
//! runs the full measurement and prints one table. Under any other runner the
//! binary runs one short pass of every row and prints nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

mod support;

use core::hint::black_box;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::CheckerQuotas;
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
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::Steps;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The admitted plan that joins `45/32 < sqrt 2` and `sqrt 2 < sqrt 2`, and
/// the two obligations that ask that each holds.
///
/// # Specification
/// trivial.
fn try_first() -> (ValidatedPlan, Obligation, Obligation)
{
    let laws = Evidence::from(0_u32);
    let mut builder = PlanBuilder::new();
    let root = square_root_of_two(&mut builder, laws).expect("a cut");
    let point = Dyadic::new(BigInt::from(45_u8), Exponent::from(-5_i32)).expect("a dyadic");
    let point = builder.real(Real::Constant(point)).expect("a constant");
    let settles = builder.open(Open::Less(point, root)).expect("a comparison");
    let never = builder.open(Open::Less(root, root)).expect("a comparison");
    let joined = builder.open(Open::Join(settles, never)).expect("a join");
    let mut table = EvidenceTable::new();
    table
        .register(laws, Judgement::CutLaws)
        .expect("a fresh table");
    let plan = admit(
        builder.finish(Root::Open(joined)).expect("a plan"),
        &Quotas::default(),
        &table,
    )
    .expect("a valid plan");
    // The cut's own comparisons read its bound variable, so each comparison
    // here is found by its operands: two cuts, or a constant before a cut.
    let real = |id: NodeId| plan.plan().node(id).ok().cloned();
    let comparison = |constant_first: bool| {
        let count = usize::from(plan.plan().node_count());
        (0 .. count)
            .map(|index| NodeId::try_from(index).expect("a position"))
            .find(|&id| {
                let Ok(&Node::Open(Open::Less(first, second))) = plan.plan().node(id)
                else {
                    return false;
                };
                let cut = matches!(real(second.node()), Some(Node::Real(Real::Cut(_))));
                let left = real(first.node());
                cut && if constant_first {
                    matches!(left, Some(Node::Real(Real::Constant(_))))
                }
                else {
                    matches!(left, Some(Node::Real(Real::Cut(_))))
                }
            })
            .expect("the comparison")
    };
    let settles = Obligation::new(&plan, comparison(true), Demand::Holds).expect("an obligation");
    let never = Obligation::new(&plan, comparison(false), Demand::Holds).expect("an obligation");
    return (plan, settles, never);
}

/// Measure every row at the quantum `steps`, printing the rows when `print`
/// asks.
///
/// # Specification
/// trivial.
fn rows(
    (plan, settles, never): (&ValidatedPlan, Obligation, Obligation),
    steps: Steps,
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let count = u64::from(steps);
    let quantum = Quantum::from(
        NonZeroU32::new(u32::try_from(count).expect("a narrow quantum")).expect("a quantum"),
    );
    let quotas = CheckerQuotas::default();
    let budget = Budget::from(u64::MAX);
    // The rounds until the first obligation settles: its sibling never does,
    // so the timed run stops at that many rounds.
    let mut probe = Dovetail::new(plan, [settles, never], quantum, quotas);
    let mut needed = 0_u64;
    loop {
        let outcome = probe
            .run(budget, Rounds::from(1_u64), || false)
            .outcome(Position::from(0));
        if matches!(
            outcome,
            Some(gandr_theory_exact_reals::Outcome::Certified(_))
        ) {
            break;
        }
        assert!(
            matches!(outcome, Some(gandr_theory_exact_reals::Outcome::Pending)),
            "the comparison settles"
        );
        needed = needed.checked_add(1).expect("a count");
    }
    let needed = Rounds::from(needed.checked_add(1).expect("a count"));
    let turn = measure(batch, samples, || {
        let mut dovetail = Dovetail::new(black_box(plan), [never], quantum, quotas);
        black_box(dovetail.run(budget, Rounds::from(1_u64), || false).work());
    });
    let settle = measure(batch, samples, || {
        let mut dovetail = Dovetail::new(black_box(plan), [settles, never], quantum, quotas);
        black_box(dovetail.run(budget, needed, || false).work());
    });
    if matches!(print, Output::Table) {
        let mut dovetail = Dovetail::new(plan, [settles, never], quantum, quotas);
        let settled = dovetail.run(budget, needed, || false).work().steps;
        for (operation, done, figures) in [("turn", count, &turn), ("settle", settled, &settle)] {
            print_row(format_args!("{count} | {done} | {operation}"), figures);
        }
    }
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let (batch, samples) = match output {
        Output::Table => (Count(16), Count(400)),
        Output::Silent => (Count(1), Count(1)),
    };
    if matches!(output, Output::Table) {
        println!("| Quantum | Steps | Operation | p50 ns | p99 ns | Allocations |");
        println!("| ------- | ----- | --------- | ------ | ------ | ----------- |");
    }
    let (plan, settles, never) = try_first();
    for steps in [1_u64, 8_u64, 64_u64] {
        rows(
            (&plan, settles, never),
            Steps::from(steps),
            batch,
            samples,
            output,
        );
    }
}
