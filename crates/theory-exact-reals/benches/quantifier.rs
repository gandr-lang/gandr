//! The measurement of bounded quantifiers: the search of each form of
//! evidence, and the replay of the certificate that it writes.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `settle` | a fresh scheduler over one quantified formula, run until the formula settles |
//! | `replay` | the checker's replay of the certificate that the run writes |
//!
//! Each row names the formula, the pole asked of it, and the steps of its
//! certificate. `cargo bench` runs the full measurement and prints one table.
//! Under any other runner the binary runs one short pass of every row and
//! prints nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

mod support;

use core::hint::black_box;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Domain;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceSlot;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantifier;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use num_bigint::BigInt;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The quantifier of a formula.
#[derive(Clone, Copy)]
enum Form
{
    /// An existential.
    Exists,
    /// A universal.
    Forall,
}

/// `1/2`.
///
/// # Specification
/// trivial.
fn half() -> Dyadic
{
    return Dyadic::new(BigInt::from(1_u8), Exponent::from(-1_i32)).expect("a half");
}

/// The admitted formula of `form` over the closed interval from `lower` to
/// `upper`, whose body compares the two operands that `operands` builds from
/// the variable, and the node of its quantifier.
///
/// # Specification
/// trivial.
fn formula<Operands>(
    form: Form,
    (lower, upper): (Dyadic, Dyadic),
    operands: Operands,
) -> (ValidatedPlan, NodeId)
where
    Operands: FnOnce(&mut PlanBuilder, RealId) -> (RealId, RealId),
{
    let (overt, compact) = (Evidence::from(1_u32), Evidence::from(2_u32));
    let mut table = EvidenceTable::new();
    table.register(overt, Judgement::Overt).expect("a table");
    table
        .register(compact, Judgement::Compact)
        .expect("a table");
    let mut builder = PlanBuilder::new();
    let hull = NumericInterval::new(
        Bound::closed(lower),
        Bound::closed(upper),
        Orientation::Proper,
    )
    .expect("a hull");
    let domain = builder
        .domain(Domain::Interval {
            hull,
            overt: EvidenceSlot::Given(overt),
            compact: EvidenceSlot::Given(compact),
        })
        .expect("a domain");
    let variable = builder
        .real(Real::Bound(DeBruijn::from(0_u32)))
        .expect("a variable");
    let (first, second) = operands(&mut builder, variable);
    let body = builder.open(Open::Less(first, second)).expect("a body");
    let (evidence, dual) = match form {
        Form::Exists => (overt, compact),
        Form::Forall => (compact, overt),
    };
    let quantifier = Quantifier {
        domain,
        body,
        evidence,
        dual: EvidenceSlot::Given(dual),
    };
    let root = builder
        .open(match form {
            Form::Exists => Open::Exists(quantifier),
            Form::Forall => Open::Forall(quantifier),
        })
        .expect("a quantifier");
    let plan = admit(
        builder.finish(Root::Open(root)).expect("a plan"),
        &Quotas::default(),
        &table,
    )
    .expect("an admitted plan");
    // The canonical walk numbers the nodes anew, so the quantifier is read
    // back from the admitted plan.
    let count = usize::from(plan.plan().node_count());
    let node = (0 .. count)
        .map(|index| NodeId::try_from(index).expect("a node"))
        .find(|&id| {
            matches!(
                plan.plan().node(id),
                Ok(&Node::Open(Open::Exists(_) | Open::Forall(_)))
            )
        })
        .expect("the quantifier");
    return (plan, node);
}

/// The certificate that a fresh scheduler writes for `obligation`.
///
/// # Specification
/// trivial.
fn settle(
    plan: &ValidatedPlan,
    obligation: Obligation,
) -> Option<Certificate>
{
    let quantum = Quantum::from(NonZeroU32::new(64)?);
    let mut dovetail = Dovetail::new(plan, [obligation], quantum, CheckerQuotas::default());
    return match dovetail
        .run(Budget::from(u64::MAX), Rounds::from(u64::MAX), || false)
        .outcome(Position::from(0))
    {
        Some(Outcome::Certified(certificate)) => Some(certificate.clone()),
        Some(
            Outcome::Pending | Outcome::Suspended(_) | Outcome::Exhausted | Outcome::Cancelled,
        )
        | None => None,
    };
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
        println!("| Formula | Asked | Steps | Operation | p50 ns | p99 ns | Allocations |");
        println!("| ------- | ----- | ----- | --------- | ------ | ------ | ----------- |");
    }
    let unit = || (Dyadic::ZERO, Dyadic::ONE);
    let rows = [
        (
            "forall x in [1, 2]. 0 < x * x",
            Demand::Holds,
            formula(
                Form::Forall,
                (Dyadic::ONE, Dyadic::from(2_i64)),
                |builder, x| {
                    let zero = builder.real(Real::Constant(Dyadic::ZERO)).expect("a zero");
                    let square = builder.real(Real::Mul(x, x)).expect("a square");
                    (zero, square)
                },
            ),
        ),
        (
            "forall x in [0, 1]. 1/2 < x * x - x + 1",
            Demand::Holds,
            formula(Form::Forall, unit(), |builder, x| {
                let half = builder.real(Real::Constant(half())).expect("a half");
                let one = builder.real(Real::Constant(Dyadic::ONE)).expect("a one");
                let square = builder.real(Real::Mul(x, x)).expect("a square");
                let difference = builder.real(Real::Sub(square, x)).expect("a difference");
                let sum = builder.real(Real::Add(difference, one)).expect("a sum");
                (half, sum)
            }),
        ),
        (
            "exists x in [0, 1]. 1/2 < x",
            Demand::Holds,
            formula(Form::Exists, unit(), |builder, x| {
                let half = builder.real(Real::Constant(half())).expect("a half");
                (half, x)
            }),
        ),
        (
            "forall x in [0, 1]. x < 1/2",
            Demand::Fails,
            formula(Form::Forall, unit(), |builder, x| {
                let half = builder.real(Real::Constant(half())).expect("a half");
                (x, half)
            }),
        ),
        (
            "exists x in [0, 1]. 2 < x",
            Demand::Fails,
            formula(Form::Exists, unit(), |builder, x| {
                let two = builder
                    .real(Real::Constant(Dyadic::from(2_i64)))
                    .expect("a two");
                (two, x)
            }),
        ),
    ];
    let quotas = CheckerQuotas::default();
    for &(name, demand, (ref plan, node)) in &rows {
        let obligation = Obligation::new(plan, node, demand).expect("an obligation");
        let certificate = settle(plan, obligation).expect("the formula settles");
        let steps = usize::from(certificate.step_count());
        let settled = measure(batch, samples, || {
            black_box(settle(black_box(plan), obligation));
        });
        let replayed = measure(batch, samples, || {
            black_box(check(black_box(plan), black_box(&certificate), &quotas)).expect("a replay");
        });
        if matches!(output, Output::Table) {
            let asked = match demand {
                Demand::Holds => "holds",
                Demand::Fails | Demand::Encloses { .. } => "fails",
            };
            for (operation, figures) in [("settle", &settled), ("replay", &replayed)] {
                print_row(
                    format_args!("{name} | {asked} | {steps} | {operation}"),
                    figures,
                );
            }
        }
    }
}
