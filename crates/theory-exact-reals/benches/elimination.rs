//! The measurement of cut elimination: the rewrite of four plans, and the
//! run of `45/32 < sqrt 2` before and after it.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `none` | the rewrite of `1 < 2`, a plan with no cut, which comes back as it is |
//! | `try-first` | the rewrite of `45/32 < sqrt 2`, `sqrt 2 < 3/2` and `sqrt 2 < sqrt 2`, joined |
//! | `table` | the rewrite of the six comparisons of the rewrite table, over the square roots of two and of three, joined |
//! | `wide` | the rewrite of 64 comparisons of points with the square root of two, joined |
//! | `compare` | a run of `45/32 < sqrt 2` until it settles |
//! | `cut` | a run of its lower cut until it settles |
//! | `restore` | the move of the lower cut's certificate back to the comparison |
//!
//! `cargo bench` runs the full measurement and prints one table. Under any
//! other runner the binary runs one short pass of every row and prints
//! nothing.

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
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::OpenId;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::eliminate;
use gandr_theory_exact_reals::square_root;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The table that registers the laws of every cut here.
///
/// # Specification
/// trivial.
fn table() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    table
        .register(Evidence::from(0_u32), Judgement::CutLaws)
        .expect("a table");
    return table;
}

/// The plan that `build` makes, admitted.
///
/// # Specification
/// trivial.
fn admitted<Build>(build: Build) -> ValidatedPlan
where
    Build: FnOnce(&mut PlanBuilder) -> OpenId,
{
    let mut builder = PlanBuilder::new();
    let root = build(&mut builder);
    return admit(
        builder.finish(Root::Open(root)).expect("a plan"),
        &Quotas::default(),
        &table(),
    )
    .expect("an admitted plan");
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
    return Dyadic::new(mantissa, exponent).expect("a dyadic");
}

/// The certificate of `obligation`, run until it settles.
///
/// # Specification
/// trivial.
fn run(
    plan: &ValidatedPlan,
    obligation: Obligation,
) -> Option<Certificate>
{
    let mut dovetail = Dovetail::new(
        plan,
        [obligation],
        Quantum::from(NonZeroU32::new(64)?),
        CheckerQuotas::default(),
    );
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
        println!("| Row | What | p50 ns | p99 ns | Allocations |");
        println!("| --- | ---- | ------ | ------ | ----------- |");
    }
    let quotas = Quotas::default();
    let table = table();
    let none = admitted(|builder| {
        let one = builder.real(Real::Constant(Dyadic::ONE)).expect("a one");
        let two = builder
            .real(Real::Constant(Dyadic::from(2_i64)))
            .expect("a two");
        builder.open(Open::Less(one, two)).expect("a comparison")
    });
    let try_first = admitted(|builder| {
        let root = square_root_of_two(builder, Evidence::from(0_u32)).expect("a cut");
        let point = builder
            .real(Real::Constant(dyadic(
                BigInt::from(45_u8),
                Exponent::from(-5_i32),
            )))
            .expect("a point");
        let above = builder
            .real(Real::Constant(dyadic(
                BigInt::from(3_u8),
                Exponent::from(-1_i32),
            )))
            .expect("a point");
        let below = builder.open(Open::Less(point, root)).expect("a comparison");
        let over = builder.open(Open::Less(root, above)).expect("a comparison");
        let itself = builder.open(Open::Less(root, root)).expect("a comparison");
        let joined = builder.open(Open::Join(below, over)).expect("a join");
        builder.open(Open::Join(joined, itself)).expect("a join")
    });
    // The plan of `each_comparison_rewrites_as_the_table_states`: three of its
    // six comparisons rewrite.
    let table_plan = admitted(|builder| {
        let two = square_root_of_two(builder, Evidence::from(0_u32)).expect("a cut");
        let hull = NumericInterval::new(
            Bound::closed(Dyadic::ONE),
            Bound::closed(Dyadic::from(2_i64)),
            Orientation::Proper,
        )
        .expect("a hull");
        let three =
            square_root(builder, Dyadic::from(3_i64), hull, Evidence::from(0_u32)).expect("a cut");
        let one = builder.real(Real::Constant(Dyadic::ONE)).expect("a one");
        let shifted = builder.real(Real::Add(two, one)).expect("a sum");
        let [first, rest @ ..] = [
            Open::Less(one, two),
            Open::Less(two, one),
            Open::Less(two, two),
            Open::Less(shifted, two),
            Open::Less(one, one),
            Open::Less(two, three),
        ];
        let mut joined = builder.open(first).expect("a comparison");
        for open in rest {
            let next = builder.open(open).expect("a comparison");
            joined = builder.open(Open::Join(joined, next)).expect("a join");
        }
        joined
    });
    let wide = admitted(|builder| {
        let root = square_root_of_two(builder, Evidence::from(0_u32)).expect("a cut");
        let mut joined = builder.open(Open::Bottom).expect("a bottom");
        for mantissa in 1 ..= 64_u16 {
            let point = builder
                .real(Real::Constant(dyadic(
                    BigInt::from(mantissa),
                    Exponent::from(-5_i32),
                )))
                .expect("a point");
            let less = builder.open(Open::Less(point, root)).expect("a comparison");
            joined = builder.open(Open::Join(joined, less)).expect("a join");
        }
        joined
    });
    let rewrite = |plan: &ValidatedPlan| {
        return measure(batch, samples, || {
            black_box(eliminate(black_box(plan.clone()), &quotas, &table)).expect("a rewrite");
        });
    };
    let (none_figures, try_figures, table_figures, wide_figures) = (
        rewrite(&none),
        rewrite(&try_first),
        rewrite(&table_plan),
        rewrite(&wide),
    );
    let real = |id: RealId| try_first.plan().node(id.node());
    let less = try_first
        .plan()
        .nodes()
        .find(|&(_, node)| {
            matches!(*node, Node::Open(Open::Less(left, right))
                if matches!(real(left), Ok(&Node::Real(Real::Constant(_))))
                    && matches!(real(right), Ok(&Node::Real(Real::Cut(_)))))
        })
        .map(|(id, _)| id)
        .expect("the comparison at 45/32");
    let asked = Obligation::new(&try_first, less, Demand::Holds).expect("an obligation");
    let elimination = eliminate(try_first.clone(), &quotas, &table).expect("a rewrite");
    let moved = elimination.obligation(asked).expect("the moved obligation");
    let compare = measure(batch, samples, || {
        black_box(run(black_box(&try_first), asked)).expect("the comparison settles");
    });
    let cut = measure(batch, samples, || {
        black_box(run(black_box(elimination.plan()), moved)).expect("the lower cut settles");
    });
    let certificate = run(elimination.plan(), moved).expect("the lower cut settles");
    let restore = measure(batch, samples, || {
        black_box(elimination.restored(black_box(&certificate))).expect("a restored certificate");
    });
    if matches!(output, Output::Table) {
        for (row, what, figures) in [
            ("none", "1 < 2, no cut", &none_figures),
            (
                "try-first",
                "45/32 < sqrt 2, sqrt 2 < 3/2 and sqrt 2 < sqrt 2",
                &try_figures,
            ),
            (
                "table",
                "the six comparisons of the table, two cuts",
                &table_figures,
            ),
            ("wide", "64 points below sqrt 2", &wide_figures),
            ("compare", "45/32 < sqrt 2, run", &compare),
            ("cut", "its lower cut, run", &cut),
            ("restore", "its certificate, moved back", &restore),
        ] {
            print_row(format_args!("{row} | {what}"), figures);
        }
    }
}
