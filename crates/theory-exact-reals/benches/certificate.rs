//! The measurement of certificates: the refinement of the square root of
//! two to widths from `2^-8` to `2^-256`, the replay of each certificate, and
//! its canonical bytes.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `refine` | [`refine`] of the registered cut to the width |
//! | `check` | [`check`] of the refinement's certificate |
//! | `encode` | [`Certificate::encode`] of the certificate |
//! | `decode` | [`Certificate::decode`] of its canonical bytes |
//!
//! Each row names the width, the certificate's steps and its bytes. `cargo
//! bench` runs the full measurement and prints one table. Under any other
//! runner the binary runs one short pass of every row and prints nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

mod support;

use core::hint::black_box;

use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::EncodedCertificate;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::refine;
use gandr_theory_exact_reals::square_root_of_two;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The admitted plan of the square root of two, and its cut.
///
/// # Specification
/// trivial.
fn root_two() -> (ValidatedPlan, NodeId)
{
    let laws = Evidence::from(0_u32);
    let mut builder = PlanBuilder::new();
    let cut = square_root_of_two(&mut builder, laws).expect("a cut");
    let mut table = EvidenceTable::new();
    table
        .register(laws, Judgement::CutLaws)
        .expect("a fresh table");
    let plan = admit(
        builder.finish(Root::Real(cut)).expect("a plan"),
        &Quotas::default(),
        &table,
    )
    .expect("a valid plan");
    let node = plan.plan().root().node();
    return (plan, node);
}

/// Measure every row at the width `2^width`, printing the rows when `print`
/// asks.
///
/// # Specification
/// trivial.
fn rows(
    (plan, cut): (&ValidatedPlan, NodeId),
    width: Exponent,
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let quotas = CheckerQuotas::default();
    let certificate = refine(plan, cut, width, &quotas).expect("a refinement");
    let bytes = certificate.encode();
    let refined = measure(batch, samples, || {
        black_box(refine(black_box(plan), cut, width, &quotas)).expect("a refinement");
    });
    let checked = measure(batch, samples, || {
        black_box(check(black_box(plan), black_box(&certificate), &quotas)).expect("a replay");
    });
    let encoded = measure(batch, samples, || {
        black_box(black_box(&certificate).encode());
    });
    let decoded = measure(batch, samples, || {
        black_box(Certificate::decode(EncodedCertificate::from(black_box(
            &bytes,
        ))))
        .expect("canonical bytes");
    });
    if matches!(print, Output::Table) {
        let bits = i32::from(width).unsigned_abs();
        let steps = usize::from(certificate.step_count());
        let length = bytes.as_ref().len();
        for (operation, figures) in [
            ("refine", &refined),
            ("check", &checked),
            ("encode", &encoded),
            ("decode", &decoded),
        ] {
            print_row(
                format_args!("2^-{bits} | {steps} | {length} | {operation}"),
                figures,
            );
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
        println!("| Width | Steps | Bytes | Operation | p50 ns | p99 ns | Allocations |");
        println!("| ----- | ----- | ----- | --------- | ------ | ------ | ----------- |");
    }
    let (plan, cut) = root_two();
    for bits in [8_i32, 64_i32, 256_i32] {
        let width = Exponent::from(bits.checked_neg().expect("a width"));
        rows((&plan, cut), width, batch, samples, output);
    }
}
