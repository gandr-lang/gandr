//! The measure of the two split policies on the workloads of the benchmark
//! matrix that split: cut enclosures to two widths, a comparison close to its
//! boundary, and bounded quantifiers over aligned and unaligned domains.
//!
//! | Column | What it counts |
//! | ------ | -------------- |
//! | `Steps` | the steps of the certificate |
//! | `Splits` | the intervals that the run splits |
//! | `Fewer` | the splits where the simplest point has fewer bits than the point taken |
//! | `Bits` | the mantissa bits of the split points, summed |
//! | `Widest` | the mantissa bits of the widest split point |
//! | `Inline` | the share of split points whose mantissa fits an `i64`, in percent |
//! | `Signs` | the lengths of the split points' sign expansions, summed |
//! | `Bytes` | the canonical bytes of the certificate |
//!
//! Each row also times a fresh scheduler to its certificate. `cargo bench`
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
use core::ops::Add as _;
use core::ops::Shl as _;
use core::ops::Shr as _;

use gandr_theory_exact_reals::BitWidth;
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
use gandr_theory_exact_reals::Side;
use gandr_theory_exact_reals::Split;
use gandr_theory_exact_reals::Step;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::square_root;
use num_bigint::BigInt;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The quantifier of a formula.
#[derive(Clone, Copy)]
enum Form
{
    /// `exists`.
    Exists,
    /// `forall`.
    Forall,
}

/// The split points of one certificate, as the table counts them.
struct Points
{
    /// The intervals that the run splits.
    splits: usize,
    /// The splits where the simplest point has fewer bits than the point
    /// taken.
    fewer: usize,
    /// The mantissa bits of the split points, summed.
    bits: u64,
    /// The mantissa bits of the widest split point.
    widest: u64,
    /// The share of split points whose mantissa fits an `i64`, in percent.
    inline: usize,
    /// The lengths of the sign expansions of the split points, summed.
    signs: u64,
}

/// The evidence table of every plan here: the overt and the compact domain
/// evidence, and the laws of the square root.
///
/// # Specification
/// trivial.
fn table() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    for (evidence, judgement) in [
        (Evidence::from(1_u32), Judgement::Overt),
        (Evidence::from(2_u32), Judgement::Compact),
        (Evidence::from(3_u32), Judgement::CutLaws),
    ] {
        table.register(evidence, judgement).expect("a table");
    }
    return table;
}

/// The closed interval from `lower` to `upper`.
///
/// # Specification
/// trivial.
fn closed(
    lower: Dyadic,
    upper: Dyadic,
) -> NumericInterval
{
    return NumericInterval::new(
        Bound::closed(lower),
        Bound::closed(upper),
        Orientation::Proper,
    )
    .expect("a hull");
}

/// `mantissa · 2^exponent`.
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

/// The admitted plan of `builder` with `root`, and its first node that
/// `wanted` accepts. The canonical walk numbers the nodes anew, so the node
/// is read back from the admitted plan.
///
/// # Specification
/// trivial.
fn admitted<Wanted>(
    builder: PlanBuilder,
    root: Root,
    wanted: Wanted,
) -> (ValidatedPlan, NodeId)
where
    Wanted: Fn(&ValidatedPlan, &Node) -> bool,
{
    let plan = admit(
        builder.finish(root).expect("a plan"),
        &Quotas::default(),
        &table(),
    )
    .expect("an admitted plan");
    let count = usize::from(plan.plan().node_count());
    let node = (0 .. count)
        .map(|index| NodeId::try_from(index).expect("a node"))
        .find(|&id| plan.plan().node(id).is_ok_and(|node| wanted(&plan, node)))
        .expect("the node");
    return (plan, node);
}

/// The square root of `radicand` over `hull`, and the node of its cut.
///
/// # Specification
/// trivial.
fn enclosed(
    radicand: Dyadic,
    hull: NumericInterval,
) -> (ValidatedPlan, NodeId)
{
    let mut builder = PlanBuilder::new();
    let root = square_root(&mut builder, radicand, hull, Evidence::from(3_u32)).expect("a cut");
    return admitted(builder, Root::Real(root), |_, node| {
        return matches!(*node, Node::Real(Real::Cut(_)));
    });
}

/// `point < sqrt radicand` with the cut over `hull`, and the node of the
/// comparison.
///
/// # Specification
/// trivial.
fn compared(
    point: Dyadic,
    radicand: Dyadic,
    hull: NumericInterval,
) -> (ValidatedPlan, NodeId)
{
    let mut builder = PlanBuilder::new();
    let root = square_root(&mut builder, radicand, hull, Evidence::from(3_u32)).expect("a cut");
    let constant = builder.real(Real::Constant(point)).expect("a point");
    let less = builder
        .open(Open::Less(constant, root))
        .expect("a comparison");
    return admitted(builder, Root::Open(less), |plan, node| {
        let Node::Open(Open::Less(_, right)) = *node
        else {
            return false;
        };
        return matches!(
            plan.plan().node(right.node()),
            Ok(&Node::Real(Real::Cut(_)))
        );
    });
}

/// The formula of `form` over `hull` whose body compares the two operands
/// that `operands` builds from the variable, and the node of its
/// quantifier.
///
/// # Specification
/// trivial.
fn formula<Operands>(
    form: Form,
    hull: NumericInterval,
    operands: Operands,
) -> (ValidatedPlan, NodeId)
where
    Operands: FnOnce(&mut PlanBuilder, RealId) -> (RealId, RealId),
{
    let (overt, compact) = (Evidence::from(1_u32), Evidence::from(2_u32));
    let mut builder = PlanBuilder::new();
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
    return admitted(builder, Root::Open(root), |_, node| {
        return matches!(*node, Node::Open(Open::Exists(_) | Open::Forall(_)));
    });
}

/// The certificate that a fresh scheduler writes for `obligation`, each split
/// at the point of `split`.
///
/// # Specification
/// trivial.
fn settle(
    plan: &ValidatedPlan,
    obligation: Obligation,
    split: Split,
) -> Certificate
{
    let quantum = Quantum::from(NonZeroU32::new(64).expect("a quantum"));
    let mut dovetail = Dovetail::with_split(
        plan,
        [obligation],
        (quantum, CheckerQuotas::default()),
        split,
    );
    let report = dovetail.run(Budget::from(u64::MAX), Rounds::from(u64::MAX), || false);
    let certificate = match report.outcome(Position::from(0_usize)) {
        Some(Outcome::Certified(certificate)) => Some(certificate.clone()),
        Some(
            Outcome::Pending | Outcome::Suspended(_) | Outcome::Exhausted | Outcome::Cancelled,
        )
        | None => None,
    };
    return certificate.expect("the obligation certifies");
}

/// The split points of `certificate`. A cut's split names its point, and the
/// enclosure that it splits is the one its earlier steps leave. A searched
/// piece splits at `p` when the pieces from its lower end to `p` and from `p`
/// to its upper end follow it.
///
/// # Specification
/// trivial.
fn points(certificate: &Certificate) -> Points
{
    let steps = certificate.steps();
    let cuts = steps
        .iter()
        .scan(None, |enclosure: &mut Option<(&Dyadic, &Dyadic)>, step| {
            if let Step::Witnesses {
                ref lower,
                ref upper,
                ..
            } = *step
            {
                *enclosure = Some((lower, upper));
            }
            let Step::Split {
                ref point, side, ..
            } = *step
            else {
                return Some(None);
            };
            let Some((lower, upper)) = *enclosure
            else {
                return Some(None);
            };
            *enclosure = Some(match side {
                Side::Lower => (point, upper),
                Side::Upper => (lower, point),
            });
            return Some(Some((lower, point, upper)));
        })
        .flatten();
    let pieces: Vec<(&Dyadic, &Dyadic)> = steps
        .iter()
        .filter_map(|step| {
            let Step::Variable {
                ref lower,
                ref upper,
                ..
            } = *step
            else {
                return None;
            };
            return Some((lower, upper));
        })
        .collect();
    let searched = pieces.iter().filter_map(|&(lower, upper)| {
        let &(_, point) = pieces
            .iter()
            .find(|&&(low, high)| low == lower && high < upper)?;
        return pieces
            .iter()
            .any(|&(low, high)| low == point && high == upper)
            .then_some((lower, point, upper));
    });
    let splits: Vec<(&Dyadic, &Dyadic, &Dyadic)> = cuts.chain(searched).collect();
    let width = |value: &Dyadic| u64::from(value.width());
    // The length of a sign expansion is the birthday: `|x|` for an integer,
    // and `floor |x| + 1 + k` for a dyadic of `k` fractional bits.
    let birthday = |value: &Dyadic| {
        let magnitude = value.mantissa().magnitude().clone();
        let exponent = i32::from(value.exponent());
        let places = exponent.unsigned_abs();
        let length = if exponent >= 0_i32 {
            magnitude.shl(places)
        }
        else {
            magnitude.shr(places).add(1_u32).add(places)
        };
        return u64::try_from(&length).unwrap_or(u64::MAX);
    };
    let fewer = splits
        .iter()
        .filter(|&&(lower, point, upper)| {
            Dyadic::simplest(lower, upper).is_ok_and(|simplest| simplest.width() < point.width())
        })
        .count();
    let inline = splits
        .iter()
        .filter(|&&(_, point, _)| point.width() <= BitWidth::from(63_u64))
        .count();
    return Points {
        splits: splits.len(),
        fewer,
        bits: splits
            .iter()
            .fold(0, |sum, &(_, point, _)| width(point).saturating_add(sum)),
        widest: splits
            .iter()
            .map(|&(_, point, _)| width(point))
            .max()
            .unwrap_or(0),
        inline: inline
            .saturating_mul(100)
            .checked_div(splits.len())
            .unwrap_or(100),
        signs: splits
            .iter()
            .fold(0, |sum, &(_, point, _)| birthday(point).saturating_add(sum)),
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
        println!(
            "| Workload | Split | Steps | Splits | Fewer | Bits | Widest | Inline % | Signs | Bytes | p50 ns | p99 ns | Allocations |"
        );
        println!(
            "| -------- | ----- | ----- | ------ | ----- | ---- | ------ | -------- | ----- | ----- | ------ | ------ | ----------- |"
        );
    }
    let two = || Dyadic::from(2_i64);
    let half = || dyadic(BigInt::from(1_u8), Exponent::from(-1_i32));
    let narrow = Demand::Encloses {
        width: Exponent::from(-16_i32),
    };
    let fine = Demand::Encloses {
        width: Exponent::from(-56_i32),
    };
    // `x · x - x + 1`, whose least value on the reals is `3/4`.
    let parabola = |builder: &mut PlanBuilder, x: RealId| {
        let half = builder.real(Real::Constant(half())).expect("a half");
        let one = builder.real(Real::Constant(Dyadic::ONE)).expect("a one");
        let square = builder.real(Real::Mul(x, x)).expect("a square");
        let difference = builder.real(Real::Sub(square, x)).expect("a difference");
        let sum = builder.real(Real::Add(difference, one)).expect("a sum");
        (half, sum)
    };
    let rows = [
        (
            "sqrt 2 over [1, 2] to 2^-56",
            fine,
            enclosed(two(), closed(Dyadic::ONE, two())),
        ),
        (
            "sqrt 2 over [0, 3] to 2^-56",
            fine,
            enclosed(two(), closed(Dyadic::ZERO, Dyadic::from(3_i64))),
        ),
        (
            "sqrt 10 over [0, 10] to 2^-56",
            fine,
            enclosed(
                Dyadic::from(10_i64),
                closed(Dyadic::ZERO, Dyadic::from(10_i64)),
            ),
        ),
        (
            "sqrt 1000 over [0, 1000] to 2^-16",
            narrow,
            enclosed(
                Dyadic::from(1000_i64),
                closed(Dyadic::ZERO, Dyadic::from(1000_i64)),
            ),
        ),
        (
            "sqrt 1000 over [0, 1000] to 2^-56",
            fine,
            enclosed(
                Dyadic::from(1000_i64),
                closed(Dyadic::ZERO, Dyadic::from(1000_i64)),
            ),
        ),
        (
            "45/32 < sqrt 2 over [0, 3]",
            Demand::Holds,
            compared(
                dyadic(BigInt::from(45_u8), Exponent::from(-5_i32)),
                two(),
                closed(Dyadic::ZERO, Dyadic::from(3_i64)),
            ),
        ),
        (
            "forall x in [1, 2]. 0 < x * x",
            Demand::Holds,
            formula(Form::Forall, closed(Dyadic::ONE, two()), |builder, x| {
                let zero = builder.real(Real::Constant(Dyadic::ZERO)).expect("a zero");
                let square = builder.real(Real::Mul(x, x)).expect("a square");
                (zero, square)
            }),
        ),
        (
            "forall x in [0, 1]. 1/2 < x * x - x + 1",
            Demand::Holds,
            formula(Form::Forall, closed(Dyadic::ZERO, Dyadic::ONE), parabola),
        ),
        (
            "forall x in [0, 3]. 1/2 < x * x - x + 1",
            Demand::Holds,
            formula(
                Form::Forall,
                closed(Dyadic::ZERO, Dyadic::from(3_i64)),
                parabola,
            ),
        ),
        (
            "forall x in [-1, 3]. -1/2 < x * x",
            Demand::Holds,
            formula(
                Form::Forall,
                closed(Dyadic::from(-1_i64), Dyadic::from(3_i64)),
                |builder, x| {
                    let bound = builder
                        .real(Real::Constant(dyadic(
                            BigInt::from(-1_i8),
                            Exponent::from(-1_i32),
                        )))
                        .expect("a bound");
                    let square = builder.real(Real::Mul(x, x)).expect("a square");
                    (bound, square)
                },
            ),
        ),
        (
            "exists x in [0, 10]. 7 < x * x",
            Demand::Holds,
            formula(
                Form::Exists,
                closed(Dyadic::ZERO, Dyadic::from(10_i64)),
                |builder, x| {
                    let seven = builder
                        .real(Real::Constant(Dyadic::from(7_i64)))
                        .expect("a seven");
                    let square = builder.real(Real::Mul(x, x)).expect("a square");
                    (seven, square)
                },
            ),
        ),
    ];
    let quotas = CheckerQuotas::default();
    for &(name, demand, (ref plan, node)) in &rows {
        let obligation = Obligation::new(plan, node, demand).expect("an obligation");
        for (label, split) in [("midpoint", Split::Midpoint), ("simplest", Split::Simplest)] {
            let certificate = settle(plan, obligation, split);
            check(plan, &certificate, &quotas).expect("the certificate replays");
            let figures = measure(batch, samples, || {
                black_box(settle(black_box(plan), obligation, split));
            });
            if matches!(output, Output::Table) {
                let steps = usize::from(certificate.step_count());
                let bytes = certificate.encode().as_ref().len();
                let Points {
                    splits,
                    fewer,
                    bits,
                    widest,
                    inline,
                    signs,
                } = points(&certificate);
                print_row(
                    format_args!(
                        "{name} | {label} | {steps} | {splits} | {fewer} | {bits} | {widest} | {inline} | {signs} | {bytes}"
                    ),
                    &figures,
                );
            }
        }
    }
}
