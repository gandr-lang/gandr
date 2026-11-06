//! The measurement of the builtin elementary functions: the enclosure rule of
//! each at 64, 256 and 1024 bits, and the replay of a certificate of two
//! builtin steps.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `pi` | [`pi`] at the precision |
//! | `cos` | [`cosine`] at the point `23/16` |
//! | `sin` | [`sine`] at the point `23/16` |
//! | `arg` | [`angle`] at the point `(3, 4)` |
//! | `check` | [`check`] of a `Pi` step and a `Cosine` step over it |
//!
//! Each row names the precision. `cargo bench` runs the full measurement and
//! prints one table. Under any other runner the binary runs one short pass of
//! every row and prints nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

mod support;

use core::hint::black_box;

use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::FormatVersion;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Step;
use gandr_theory_exact_reals::StepId;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::angle;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::cosine;
use gandr_theory_exact_reals::pi;
use gandr_theory_exact_reals::sine;
use num_bigint::BigInt;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The admitted plan of `cos π`, and the certificate of its enclosure at
/// `precision`.
///
/// # Specification
/// trivial.
fn cosine_of_pi(precision: Precision) -> (ValidatedPlan, Certificate)
{
    let mut builder = PlanBuilder::new();
    let circle = builder.real(Real::Pi).expect("a node");
    let wave = builder.real(Real::Cos(circle)).expect("a node");
    let plan = admit(
        builder.finish(Root::Real(wave)).expect("a plan"),
        &Quotas::default(),
        &EvidenceTable::new(),
    )
    .expect("a valid plan");
    let (circle, _) = plan
        .plan()
        .nodes()
        .find(|&(_, node)| matches!(*node, Node::Real(Real::Pi)))
        .expect("the π node");
    let certificate = Certificate::new(FormatVersion::CURRENT, vec![
        Step::Pi {
            real: circle,
            precision,
        },
        Step::Cosine {
            real: plan.plan().root().node(),
            argument: StepId::from(0_u32),
            precision,
        },
    ]);
    return (plan, certificate);
}

/// Measure every row at `precision`, printing the rows when `print` asks.
///
/// # Specification
/// trivial.
fn rows(
    precision: Precision,
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let quotas = CheckerQuotas::default();
    let point = NumericInterval::point(
        Dyadic::new(BigInt::from(23_u8), Exponent::from(-4_i32)).expect("a point"),
    );
    let (x, y) = (
        NumericInterval::point(Dyadic::from(3_i64)),
        NumericInterval::point(Dyadic::from(4_i64)),
    );
    let (plan, certificate) = cosine_of_pi(precision);
    let circle = measure(batch, samples, || {
        black_box(pi(black_box(precision))).expect("an enclosure");
    });
    let wave = measure(batch, samples, || {
        black_box(cosine(black_box(&point), precision)).expect("an enclosure");
    });
    let odd = measure(batch, samples, || {
        black_box(sine(black_box(&point), precision)).expect("an enclosure");
    });
    let turned = measure(batch, samples, || {
        black_box(angle(black_box(&x), black_box(&y), precision)).expect("an enclosure");
    });
    let checked = measure(batch, samples, || {
        black_box(check(black_box(&plan), black_box(&certificate), &quotas)).expect("a replay");
    });
    if matches!(print, Output::Table) {
        let bits = u32::from(precision);
        for (operation, figures) in [
            ("pi", &circle),
            ("cos", &wave),
            ("sin", &odd),
            ("arg", &turned),
            ("check", &checked),
        ] {
            print_row(format_args!("{bits} | {operation}"), figures);
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
        Output::Table => (Count(4), Count(200)),
        Output::Silent => (Count(1), Count(1)),
    };
    if matches!(output, Output::Table) {
        println!("| Bits | Operation | p50 ns | p99 ns | Allocations |");
        println!("| ---- | --------- | ------ | ------ | ----------- |");
    }
    for bits in [64_u32, 256_u32, 1024_u32] {
        let precision = Precision::try_from(bits).expect("a precision");
        rows(precision, batch, samples, output);
    }
}
