//! The measurement of the adapter of `std.reals.Eff`: `admit`, `enclose` and
//! `decide` through the host, and the same work through `theory-exact-reals`
//! with no adapter.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `admit` | the host decodes the text and the bytes, validates the plan and holds it; the crate validates the bytes, and a copy of the decoded plan |
//! | `enclose` | `sqrt 2` no wider than `2^-64`, and the replay of its certificate; the host also finds the plan and spells both ends |
//! | `decide` | `sqrt 2 < 3/2` for 16 quanta, and the replay of its certificate; the host also holds the machine and spells the verdict |
//!
//! The difference of the two paths of a row is the cost of the adapter. Each
//! path reads the plan that the corpus spells. `cargo bench` runs the full
//! measurement and prints one table. Under any other runner the binary runs
//! one short pass of every row and prints nothing.

#![expect(
    clippy::expect_used,
    clippy::panic,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

#[path = "../../theory-exact-reals/benches/support.rs"]
mod support;

use core::hint::black_box;
use core::num::NonZeroU32;

use gandr_kernel_term::StringLiteral;
use gandr_surface_dispatcher::RealsAdapter;
use gandr_surface_dispatcher::RealsProfile;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::Plan;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::Steps;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::validate;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The canonical bytes of the plan of `sqrt 2` in lowercase hexadecimal:
/// `rootTwo` of `corpus/model/reals/sqrt-two.gandr`.
const ROOT_TWO: &str = "4758525001000b0000000000000001000000000200000000000000000000000012000000000100000005000000000000000002010000000100000000000000011203000000040000001402000000050000001201000000000000001204000000030000001307000000080000000800010000000001000000000000000100010100000001000000000000000100060000000900000000000000";

/// The canonical bytes of the plan of `sqrt 2 < 3/2` in lowercase
/// hexadecimal: `belowThreeHalves` of `corpus/model/reals/reals-base.gandr`.
const BELOW_THREE_HALVES: &str = "4758525001000d000000000000000100000000020000000000000000000000001200000000010000000500000000000000000201000000010000000000000001120300000004000000140200000005000000120100000000000000120400000003000000130700000008000000080001000000000100000000000000010001010000000100000000000000010006000000090000000000000002ffffffff010000000000000003120a0000000b000000";

/// The power of two that bounds the width of each enclosure.
const WIDTH: i32 = -64;

/// The quanta of each `decide`.
const QUANTA: u64 = 16;

/// The steps of one `enclose`: the step quota of the default checker.
const STEPS: u64 = 0x0001_0000;

/// The plan that `text` spells, decoded into memory as a caller of the crate
/// holds it.
///
/// # Specification
/// trivial.
fn decoded(text: &StringLiteral) -> Plan
{
    let text: &str = text.as_ref();
    let bytes: Vec<u8> = text
        .as_bytes()
        .chunks(2)
        .map(|pair| {
            u8::from_str_radix(core::str::from_utf8(pair).expect("ASCII"), 16)
                .expect("a hexadecimal pair")
        })
        .collect();
    Plan::decode(EncodedPlan::from(bytes.as_slice())).expect("a plan")
}

/// The evidence that the host registers: the laws of the cut at zero, and
/// the overtness and the compactness of a domain at one and two.
///
/// # Specification
/// trivial.
fn evidence() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    for (reference, judgement) in [
        (0_u32, Judgement::CutLaws),
        (1, Judgement::Overt),
        (2, Judgement::Compact),
    ] {
        table
            .register(Evidence::from(reference), judgement)
            .expect("a fresh table");
    }
    table
}

/// Measure every row, printing the rows when `print` asks.
///
/// # Specification
/// trivial.
fn rows(
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let width = Exponent::from(WIDTH);
    let (root_two, below) = (
        StringLiteral::new(ROOT_TWO.into()),
        StringLiteral::new(BELOW_THREE_HALVES.into()),
    );
    let host_root = RealsAdapter::new(root_two.clone(), RealsProfile::Default)
        .expect("the host admits the plan");
    let host_below =
        RealsAdapter::new(below.clone(), RealsProfile::Default).expect("the host admits the plan");
    let verdict = host_below.decide(Steps::from(QUANTA)).expect("a verdict");
    assert_eq!(verdict.0, "holds", "the comparison holds within its quanta");
    let (plan_quotas, quotas, table) = (Quotas::default(), CheckerQuotas::default(), evidence());
    let root_plan = decoded(&root_two);
    let root = admit(root_plan.clone(), &plan_quotas, &table).expect("a valid plan");
    let root_bytes: Vec<u8> = root_plan.encode().into();
    let comparison = admit(decoded(&below), &plan_quotas, &table).expect("a valid plan");
    let enclosed = || {
        let node = root.plan().root().node();
        let obligation =
            Obligation::new(&root, node, Demand::Encloses { width }).expect("a real root");
        let mut machine =
            Dovetail::new(&root, [obligation], Quantum::from(NonZeroU32::MAX), quotas);
        let report = machine.run(Budget::from(STEPS), Rounds::from(1_u64), || false);
        let Some(Outcome::Certified(certificate)) = report.outcome(Position::from(0_usize))
        else {
            panic!("an enclosure");
        };
        black_box(check(&root, certificate, &quotas)).expect("a replay");
    };
    let decided = || {
        let node = comparison.plan().root().node();
        let poles = [
            Obligation::new(&comparison, node, Demand::Holds).expect("an open root"),
            Obligation::new(&comparison, node, Demand::Fails).expect("an open root"),
        ];
        let mut machine = Dovetail::new(&comparison, poles, Quantum::from(NonZeroU32::MIN), quotas);
        let report = machine.run(Budget::from(QUANTA), Rounds::from(u64::MAX), || false);
        let certificate = (0_usize .. 2)
            .find_map(|position| match report.outcome(Position::from(position)) {
                Some(Outcome::Certified(certificate)) => Some(certificate),
                Some(
                    Outcome::Pending
                    | Outcome::Suspended(_)
                    | Outcome::Exhausted
                    | Outcome::Cancelled,
                )
                | None => None,
            })
            .expect("a pole certifies");
        black_box(check(&comparison, certificate, &quotas)).expect("a replay");
    };
    let measured = [
        (
            "admit",
            "host",
            measure(batch, samples, || {
                black_box(host_root.admit()).expect("a handle");
            }),
        ),
        (
            "admit",
            "crate, bytes",
            measure(batch, samples, || {
                black_box(validate(
                    EncodedPlan::from(root_bytes.as_slice()),
                    &plan_quotas,
                    &table,
                ))
                .expect("a valid plan");
            }),
        ),
        (
            "admit",
            "crate, plan",
            measure(batch, samples, || {
                black_box(admit(root_plan.clone(), &plan_quotas, &table)).expect("a valid plan");
            }),
        ),
        (
            "enclose",
            "host",
            measure(batch, samples, || {
                black_box(host_root.enclose(width)).expect("an enclosure");
            }),
        ),
        ("enclose", "crate", measure(batch, samples, enclosed)),
        (
            "decide",
            "host",
            measure(batch, samples, || {
                black_box(host_below.decide(Steps::from(QUANTA))).expect("a verdict");
            }),
        ),
        ("decide", "crate", measure(batch, samples, decided)),
    ];
    if matches!(print, Output::Table) {
        for &(operation, path, ref figures) in &measured {
            print_row(format_args!("{operation} | {path}"), figures);
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
        Output::Table => (Count(4), Count(500)),
        Output::Silent => (Count(1), Count(1)),
    };
    if matches!(output, Output::Table) {
        println!("| Operation | Path | p50 ns | p99 ns | Allocations |");
        println!("| --------- | ---- | ------ | ------ | ----------- |");
    }
    rows(batch, samples, output);
}
