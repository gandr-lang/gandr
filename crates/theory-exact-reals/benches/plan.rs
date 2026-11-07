//! The measurement of plans: the canonical form, the bytes, their reading
//! back, their validation, their dual approximation, and the minimal form
//! under bisimulation. It reads the cut of the square root of two, plans of
//! a thousand distinct nodes, the families of the benchmark matrix, and the
//! phases of the ZX-calculus.
//!
//! `cargo bench` runs the full measurement and prints the tables. Under any
//! other runner the binary runs one short pass of every row and prints
//! nothing.
//!
//! # Items
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `finish` | [`PlanBuilder::finish`] of a builder that holds the plan's nodes once |
//! | `finish, unshared` | [`PlanBuilder::finish`] of a builder that holds every node of the plan's tree, each subterm again |
//! | `encode` | [`Plan::encode`] |
//! | `decode` | [`Plan::decode`] of the canonical bytes, with its check that they are canonical |
//! | `admit` | [`admit`] of the plan under the default quotas |
//! | `validate` | [`validate`] of the canonical bytes: the reading and the pass |
//! | `approximate` | [`approximate`] of the admitted plan at 64 bits |
//! | `graph` | [`PlanGraph::from`] of the plan |
//! | `core` | [`PlanGraph::core`]: the matching and its check |
//!
//! The plan of a thousand nodes sums 500 distinct constants of 63 bits into
//! a chain of 499 sums and compares the sum with zero. Its tree form builds
//! each square of a chain of ten squares of one again, 2047 nodes for 11
//! distinct ones, so that row times the walk that finds equal nodes.
//!
//! A second table times [`PlanGraph::minimal`] and gives the classes, the
//! core, the peak bytes and the start of the key. A third table counts the
//! distinct structural keys and the distinct minimal keys of each family of
//! phases.
//!
//! # Boundaries
//!
//! The minimal forms read the plans above and one plan for each other family
//! of the benchmark matrix whose plan has its own shape: a nested cut, a
//! comparison near its boundary, a sum that cancels, and a bounded
//! alternation. The other families change the run and not the plan. Then
//! come one fusion sum of four phases, one Euler angle, and a ring of a
//! thousand nodes `x = 2^-y` that unfolds as `x = 2^-x`. A fusion sum of
//! `k π / 4` phases takes each order and each bracketing. An Euler angle is
//! the argument of the sum of two angles `a` and `b` from 1, 2 and 3, each
//! sum and product in each order.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

extern crate alloc;

mod support;

use alloc::collections::BTreeSet;
use core::hint::black_box;

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Cut;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::Domain;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceSlot;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::GraphBuilder;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Label;
use gandr_theory_exact_reals::LabelBytes;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Operands;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Plan;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanGraph;
use gandr_theory_exact_reals::PlanKey;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Quantifier;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::approximate;
use gandr_theory_exact_reals::validate;
use num_bigint::BigInt;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The cut of the square root of `radicand`, a real between one and four:
/// below it each `x` with `x < 0` or `x · x < radicand`, above it each `x`
/// with `0 < x` and `radicand < x · x`, inside the hull from one to two.
///
/// # Specification
/// trivial.
fn square_root(
    builder: &mut PlanBuilder,
    radicand: RealId,
) -> RealId
{
    let x = builder
        .real(Real::Bound(DeBruijn::from(0)))
        .expect("a node");
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).expect("a node");
    let square = builder.real(Real::Mul(x, x)).expect("a node");
    let negative = builder.open(Open::Less(x, zero)).expect("a node");
    let small = builder.open(Open::Less(square, radicand)).expect("a node");
    let lower = builder.open(Open::Join(negative, small)).expect("a node");
    let positive = builder.open(Open::Less(zero, x)).expect("a node");
    let large = builder.open(Open::Less(radicand, square)).expect("a node");
    let upper = builder.open(Open::Meet(positive, large)).expect("a node");
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ONE),
        Bound::closed(Dyadic::from(2_i64)),
        Orientation::Proper,
    )
    .expect("an ordered hull");
    return builder
        .real(Real::Cut(Cut {
            hull,
            lower,
            upper,
            laws: Evidence::from(0),
        }))
        .expect("a node");
}

/// The builder of the cut of the square root of two.
///
/// # Specification
/// trivial.
fn square_root_of_two() -> (PlanBuilder, Root)
{
    let mut builder = PlanBuilder::new();
    let two = builder
        .real(Real::Constant(Dyadic::from(2_i64)))
        .expect("a node");
    let cut = square_root(&mut builder, two);
    return (builder, Root::Real(cut));
}

/// The builder of a nested cut: the square root of the cut of the square
/// root of two.
///
/// # Specification
/// trivial.
fn fourth_root_of_two() -> (PlanBuilder, Root)
{
    let (mut builder, root) = square_root_of_two();
    let Root::Real(inner) = root
    else {
        return (builder, root);
    };
    let cut = square_root(&mut builder, inner);
    return (builder, Root::Real(cut));
}

/// The builder of a comparison close to its boundary: the square root of
/// two below the double nearest it, `6369051672525773 · 2^-52`.
///
/// # Specification
/// trivial.
fn near_boundary() -> (PlanBuilder, Root)
{
    let (mut builder, root) = square_root_of_two();
    let Root::Real(cut) = root
    else {
        return (builder, root);
    };
    let nearest = Dyadic::new(
        BigInt::from(6_369_051_672_525_773_i64),
        Exponent::from(-52_i32),
    )
    .expect("a dyadic");
    let nearest = builder.real(Real::Constant(nearest)).expect("a node");
    let below = builder.open(Open::Less(cut, nearest)).expect("a node");
    return (builder, Root::Open(below));
}

/// The builder of a sum that cancels: `(2^62 + 1) - 2^62`, compared with
/// zero.
///
/// # Specification
/// trivial.
fn cancellation() -> (PlanBuilder, Root)
{
    let mut builder = PlanBuilder::new();
    let large = builder
        .real(Real::Constant(Dyadic::from(0x4000_0000_0000_0000_i64)))
        .expect("a node");
    let one = builder.real(Real::Constant(Dyadic::ONE)).expect("a node");
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).expect("a node");
    let sum = builder.real(Real::Add(large, one)).expect("a node");
    let difference = builder.real(Real::Sub(sum, large)).expect("a node");
    let positive = builder.open(Open::Less(zero, difference)).expect("a node");
    return (builder, Root::Open(positive));
}

/// The builder of a bounded alternation: some `x` in `[0, 2]` such that
/// every `y` in `[0, 1]` has `y · y < x`.
///
/// # Specification
/// trivial.
fn alternation() -> (PlanBuilder, Root)
{
    let (overt, compact) = (Evidence::from(1_u32), Evidence::from(2_u32));
    let mut builder = PlanBuilder::new();
    let domain = |builder: &mut PlanBuilder, upper: i64| {
        let hull = NumericInterval::new(
            Bound::closed(Dyadic::ZERO),
            Bound::closed(Dyadic::from(upper)),
            Orientation::Proper,
        )
        .expect("a hull");
        return builder
            .domain(Domain::Interval {
                hull,
                overt: EvidenceSlot::Given(overt),
                compact: EvidenceSlot::Given(compact),
            })
            .expect("a domain");
    };
    let outer = domain(&mut builder, 2);
    let inner = domain(&mut builder, 1);
    let y = builder
        .real(Real::Bound(DeBruijn::from(0)))
        .expect("a node");
    let x = builder
        .real(Real::Bound(DeBruijn::from(1)))
        .expect("a node");
    let square = builder.real(Real::Mul(y, y)).expect("a node");
    let below = builder.open(Open::Less(square, x)).expect("a node");
    let every = builder
        .open(Open::Forall(Quantifier {
            domain: inner,
            body: below,
            evidence: compact,
            dual: EvidenceSlot::Given(overt),
        }))
        .expect("a node");
    let some = builder
        .open(Open::Exists(Quantifier {
            domain: outer,
            body: every,
            evidence: overt,
            dual: EvidenceSlot::Given(compact),
        }))
        .expect("a node");
    return (builder, Root::Open(some));
}

/// The builder of a thousand distinct nodes: a chain of sums of distinct
/// constants, compared with zero.
///
/// # Specification
/// trivial.
fn thousand() -> (PlanBuilder, Root)
{
    let mut builder = PlanBuilder::new();
    let mut draw = 0x9E37_79B9_7F4A_7C15_u64;
    let mut constant = |builder: &mut PlanBuilder| {
        // xorshift64, kept odd and below 2^63 so each constant is inline.
        draw ^= draw.wrapping_shl(13);
        draw ^= draw.wrapping_shr(7);
        draw ^= draw.wrapping_shl(17);
        let mantissa = i64::try_from(draw.wrapping_shr(1) | 1).expect("below 2^63");
        builder
            .real(Real::Constant(Dyadic::from(mantissa)))
            .expect("a node")
    };
    let mut sum: RealId = constant(&mut builder);
    for _ in 1_u32 .. 500 {
        let next = constant(&mut builder);
        sum = builder.real(Real::Add(sum, next)).expect("a node");
    }
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).expect("a node");
    let positive = builder.open(Open::Less(zero, sum)).expect("a node");
    return (builder, Root::Open(positive));
}

/// The builder of a chain of ten squares of one written as a tree: every
/// operand built again.
///
/// # Specification
/// trivial.
fn unshared() -> (PlanBuilder, Root)
{
    let mut builder = PlanBuilder::new();
    let mut frontier: Vec<RealId> =
        core::iter::repeat_with(|| builder.real(Real::Constant(Dyadic::ONE)).expect("a node"))
            .take(1024)
            .collect();
    while frontier.len() > 1 {
        frontier = frontier
            .chunks(2)
            .map(|operands| {
                let left = operands.first().copied().expect("a left operand");
                let right = operands.get(1).copied().expect("a right operand");
                builder.real(Real::Mul(left, right)).expect("a node")
            })
            .collect();
    }
    let root = frontier.first().copied().expect("one root");
    return (builder, Root::Real(root));
}

/// Measure every row of one plan, printing the rows when `print` asks.
///
/// # Specification
/// trivial.
fn rows(
    name: core::fmt::Arguments<'_>,
    (builder, root): (PlanBuilder, Root),
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let plan = builder.clone().finish(root).expect("a plan");
    let bytes = plan.encode();
    let quotas = Quotas::default();
    let mut table = EvidenceTable::new();
    table
        .register(Evidence::from(0), Judgement::CutLaws)
        .expect("a fresh table");
    let finish = measure(batch, samples, || {
        black_box(black_box(builder.clone()).finish(root)).expect("a plan");
    });
    let encode = measure(batch, samples, || {
        black_box(black_box(&plan).encode());
    });
    let decode = measure(batch, samples, || {
        black_box(Plan::decode(EncodedPlan::from(black_box(&bytes)))).expect("canonical bytes");
    });
    let admitted = measure(batch, samples, || {
        black_box(admit(black_box(plan.clone()), &quotas, &table)).expect("a valid plan");
    });
    let validated = measure(batch, samples, || {
        black_box(validate(
            EncodedPlan::from(black_box(&bytes)),
            &quotas,
            &table,
        ))
        .expect("a valid plan");
    });
    let admitted_plan = admit(plan.clone(), &quotas, &table).expect("a valid plan");
    let precision = Precision::try_from(64_u32).expect("a precision");
    let approximated = measure(batch, samples, || {
        black_box(approximate(black_box(&admitted_plan), precision));
    });
    let graphed = measure(batch, samples, || {
        black_box(PlanGraph::from(black_box(&plan)));
    });
    let graph = PlanGraph::from(&plan);
    let cored = measure(batch, samples, || {
        black_box(black_box(&graph).core()).expect("a core");
    });
    if matches!(print, Output::Table) {
        let nodes = usize::from(plan.node_count());
        let length = bytes.as_ref().len();
        print_row(
            format_args!("{name} | {nodes} | {length} | finish"),
            &finish,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | encode"),
            &encode,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | decode"),
            &decode,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | admit"),
            &admitted,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | validate"),
            &validated,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | approximate"),
            &approximated,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | graph"),
            &graphed,
        );
        print_row(format_args!("{name} | {nodes} | {length} | core"), &cored);
    }
}

/// One token of a bracketing written in postfix: a phase, or the sum of the
/// two terms before it.
#[derive(Clone, Copy)]
enum Token
{
    /// The next phase of the order.
    Phase,
    /// The sum of the two terms before it.
    Sum,
}

/// Every fusion sum of `count` distinct phases `k π / 4`, `k` from one to
/// `count`: each order of the phases under each bracketing.
///
/// # Specification
/// trivial.
fn fusions(count: Count) -> Vec<Plan>
{
    // The bracketings of zero to `count` terms, each in postfix.
    let mut shapes: Vec<Vec<Vec<Token>>> = vec![Vec::new(), vec![vec![Token::Phase]]];
    for terms in 2 ..= count.0 {
        let mut all = Vec::new();
        for left in 1 .. terms {
            let right = terms.saturating_sub(left);
            for first in shapes.get(left).expect("shorter bracketings") {
                for second in shapes.get(right).expect("shorter bracketings") {
                    let mut shape = Vec::with_capacity(
                        first.len().saturating_add(second.len()).saturating_add(1),
                    );
                    shape.extend_from_slice(first);
                    shape.extend_from_slice(second);
                    shape.push(Token::Sum);
                    all.push(shape);
                }
            }
        }
        shapes.push(all);
    }
    // Each order: each word of `count` digits below `count` with no digit
    // twice.
    let width = u32::try_from(count.0).expect("a few phases");
    let words = count.0.checked_pow(width).expect("a few phases");
    let mut orders: Vec<Vec<usize>> = Vec::new();
    let mut order: Vec<usize> = Vec::with_capacity(count.0);
    for word in 0 .. words {
        order.clear();
        let mut rest = word;
        let mut seen = 0_u64;
        for _ in 0 .. count.0 {
            let digit = rest.checked_rem(count.0).expect("a phase");
            rest = rest.checked_div(count.0).expect("a phase");
            seen |= 1_u64
                .checked_shl(u32::try_from(digit).expect("a digit"))
                .expect("a digit");
            order.push(digit);
        }
        if seen.count_ones() == width {
            orders.push(order.clone());
        }
    }
    let mut plans = Vec::new();
    let mut stack = Vec::with_capacity(count.0);
    for shape in shapes.get(count.0).expect("the bracketings") {
        for order in &orders {
            let mut builder = PlanBuilder::new();
            let pi = builder.real(Real::Pi).expect("a node");
            let mut phases = order.iter();
            stack.clear();
            for &token in shape {
                let term = match token {
                    Token::Phase => {
                        let multiple = phases.next().copied().expect("a phase").saturating_add(1);
                        let quarter = Dyadic::new(BigInt::from(multiple), Exponent::from(-2_i32))
                            .expect("a dyadic");
                        let quarter = builder.real(Real::Constant(quarter)).expect("a node");
                        builder.real(Real::Mul(quarter, pi)).expect("a node")
                    },
                    Token::Sum => {
                        let right = stack.pop().expect("a right term");
                        let left = stack.pop().expect("a left term");
                        builder.real(Real::Add(left, right)).expect("a node")
                    },
                };
                stack.push(term);
            }
            let root = stack.pop().expect("one sum");
            plans.push(builder.finish(Root::Real(root)).expect("a plan"));
        }
    }
    return plans;
}

/// Every Euler angle of two angles `a` and `b` from 1, 2 and 3: the argument
/// of `(cos a cos b - sin a sin b, sin a cos b + cos a sin b)`, each product
/// and the sum in each order.
///
/// # Specification
/// trivial.
fn euler_angles() -> Vec<Plan>
{
    let mut plans = Vec::new();
    for a in 1_i64 ..= 3 {
        for b in 1_i64 ..= 3 {
            for spelling in 0_u32 .. 32 {
                let turned = |bit: u32| spelling.checked_shr(bit).unwrap_or_default() & 1 == 1;
                let mut builder = PlanBuilder::new();
                let mut real = |node: Real| builder.real(node).expect("a node");
                let (first, second) = (
                    real(Real::Constant(Dyadic::from(a))),
                    real(Real::Constant(Dyadic::from(b))),
                );
                let (cos_a, sin_a) = (real(Real::Cos(first)), real(Real::Sin(first)));
                let (cos_b, sin_b) = (real(Real::Cos(second)), real(Real::Sin(second)));
                let mut product = |left: RealId, right: RealId, bit: u32| {
                    return if turned(bit) {
                        real(Real::Mul(right, left))
                    }
                    else {
                        real(Real::Mul(left, right))
                    };
                };
                let cosines = product(cos_a, cos_b, 0);
                let sines = product(sin_a, sin_b, 1);
                let rising = product(sin_a, cos_b, 2);
                let falling = product(cos_a, sin_b, 3);
                let x = real(Real::Sub(cosines, sines));
                let y = if turned(4) {
                    real(Real::Add(falling, rising))
                }
                else {
                    real(Real::Add(rising, falling))
                };
                let angle = real(Real::Arg(x, y));
                plans.push(builder.finish(Root::Real(angle)).expect("a plan"));
            }
        }
    }
    return plans;
}

/// A ring of a thousand nodes, each `2^-y` of the one before it, which
/// unfolds as `x = 2^-x`.
///
/// # Specification
/// trivial.
fn ring() -> PlanGraph
{
    let label = Label::new(
        LabelBytes::from(b"two to the minus".as_slice()),
        Operands::Ordered,
    );
    let mut builder = GraphBuilder::new();
    let first = builder.reserve().expect("a node");
    let mut previous = first;
    for _ in 1_u32 .. 1000 {
        previous = builder.node(label.clone(), &[previous]).expect("a node");
    }
    builder.define(first, label, &[previous]).expect("a node");
    return builder.finish(first).expect("a graph");
}

/// Measure the minimal form of `graph`, printing its row when `print` asks.
///
/// # Specification
/// trivial.
fn form(
    name: core::fmt::Arguments<'_>,
    graph: &PlanGraph,
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let figures = measure(batch, samples, || {
        black_box(black_box(graph).minimal());
    });
    if matches!(print, Output::Table) {
        let minimal = graph.minimal();
        let core = graph.core().expect("a core");
        let peak = allocation_counter::measure(|| {
            black_box(black_box(graph).minimal());
        })
        .bytes_max;
        let key = minimal
            .key()
            .as_ref()
            .iter()
            .take(4)
            .fold(0_u32, |start, &byte| {
                start.wrapping_shl(8) | u32::from(byte)
            });
        let nodes = usize::from(graph.node_count());
        let classes = usize::from(minimal.class_count());
        let critical = core.nodes().len();
        print_row(
            format_args!("{name} | {nodes} | {classes} | {critical} | {peak} | {key:08x}"),
            &figures,
        );
    }
}

/// Count the distinct structural keys and the distinct minimal keys of
/// `plans`, printing the row when `print` asks.
///
/// # Specification
/// trivial.
fn sharing(
    name: core::fmt::Arguments<'_>,
    plans: &[Plan],
    print: Output,
)
{
    let structural: BTreeSet<Vec<u8>> = plans.iter().map(|plan| plan.encode().into()).collect();
    let minimal: BTreeSet<PlanKey> = plans
        .iter()
        .map(|plan| PlanGraph::from(plan).minimal().key())
        .collect();
    if matches!(print, Output::Table) {
        println!(
            "| {name} | {} | {} | {} |",
            plans.len(),
            structural.len(),
            minimal.len()
        );
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
        println!("| Plan | Nodes | Bytes | Operation | p50 ns | p99 ns | Allocations |");
        println!("| ---- | ----- | ----- | --------- | ------ | ------ | ----------- |");
    }
    rows(
        format_args!("square root of two"),
        square_root_of_two(),
        batch,
        samples,
        output,
    );
    rows(
        format_args!("a thousand nodes"),
        thousand(),
        batch,
        samples,
        output,
    );
    rows(
        format_args!("ten squares, unshared"),
        unshared(),
        batch,
        samples,
        output,
    );
    let plan = |(builder, root): (PlanBuilder, Root)| builder.finish(root).expect("a plan");
    let three = fusions(Count(3));
    let four = fusions(Count(4));
    let angles = euler_angles();
    if matches!(output, Output::Table) {
        println!();
        println!(
            "| Graph | Nodes | Classes | Core | Peak bytes | Key | p50 ns | p99 ns | Allocations |"
        );
        println!(
            "| ----- | ----- | ------- | ---- | ---------- | --- | ------ | ------ | ----------- |"
        );
    }
    let graphs = [
        (
            "square root of two",
            PlanGraph::from(&plan(square_root_of_two())),
        ),
        ("a thousand nodes", PlanGraph::from(&plan(thousand()))),
        ("ten squares, unshared", PlanGraph::from(&plan(unshared()))),
        (
            "fourth root of two",
            PlanGraph::from(&plan(fourth_root_of_two())),
        ),
        ("near a boundary", PlanGraph::from(&plan(near_boundary()))),
        ("cancellation", PlanGraph::from(&plan(cancellation()))),
        ("alternation", PlanGraph::from(&plan(alternation()))),
        (
            "fusion of four phases",
            PlanGraph::from(four.first().expect("a fusion")),
        ),
        (
            "Euler angle",
            PlanGraph::from(angles.last().expect("an angle")),
        ),
        ("ring of a thousand", ring()),
    ];
    for &(name, ref graph) in &graphs {
        form(format_args!("{name}"), graph, batch, samples, output);
    }
    if matches!(output, Output::Table) {
        println!();
        println!("| Family | Plans | Structural keys | Minimal keys |");
        println!("| ------ | ----- | --------------- | ------------ |");
    }
    sharing(format_args!("fusion of three phases"), &three, output);
    sharing(format_args!("fusion of four phases"), &four, output);
    sharing(format_args!("Euler angles"), &angles, output);
}
