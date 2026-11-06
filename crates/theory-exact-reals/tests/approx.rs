//! The exemplar of dual approximation: a differential test against the slow
//! rational oracle over generated plans at several precisions, with the hand
//! example `1/3 + 1/3 < 1`, comparisons that never decide, the meet and join
//! tables, a divisor whose enclosure holds zero, and the lookups.
//!
//! The oracle evaluates each node of a closed plan as an exact rational or an
//! exact truth value, with no interval and no rounding. A positive
//! approximant must never meet a false proposition, and a negative
//! approximant must never meet a true one.

use core::cmp::Ordering;

use gandr_theory_exact_reals::BilateralApprox;
use gandr_theory_exact_reals::Containment;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::NegativeApprox;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::OpenId;
use gandr_theory_exact_reals::Plan;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanError;
use gandr_theory_exact_reals::PositiveApprox;
use gandr_theory_exact_reals::Power;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::approximate;
use num_bigint::BigInt;
use proptest::prelude::*;

use crate::oracle::Rational;

/// The precisions of the differential test, from one bit to past 128.
const PRECISIONS: [u32; 6] = [1, 2, 8, 32, 64, 200];

/// The bound in bits on the numerator and the denominator of a generated
/// value, which keeps the oracle's work bounded.
const SIZE_BOUND: u64 = 2048;

/// One step of a generated closed plan. A child names an earlier node of its
/// sort by a draw that wraps around the nodes built so far.
#[derive(Clone, Debug)]
enum Step
{
    /// A constant.
    Constant(Dyadic),
    /// A sum, a difference, a product or a quotient, by the kind's draw.
    Arithmetic(u8, usize, usize),
    /// A power of at most three.
    Power(usize, u32),
    /// A strict comparison.
    Less(usize, usize),
    /// A meet, or a join.
    Lattice(bool, usize, usize),
    /// The true or the false proposition.
    ConstantOpen(bool),
}

/// The oracle's value of one node.
#[derive(Clone, Debug)]
enum Exact
{
    /// A real node's exact value.
    Real(Rational),
    /// An open node that holds.
    Holds,
    /// An open node that fails.
    Fails,
    /// A node whose value the oracle does not define: a quotient by zero, or a
    /// node that reads one.
    Undefined,
}

/// The nonzero evidence that every quotient names.
///
/// # Specification
/// trivial.
fn nonzero() -> Evidence
{
    return Evidence::from(0_u32);
}

/// Admit a plan whose quotients name [`nonzero`].
///
/// # Specification
/// trivial.
fn admitted(
    builder: PlanBuilder,
    root: Root,
) -> ValidatedPlan
{
    let mut table = EvidenceTable::new();
    table.register(nonzero(), Judgement::NonZero).unwrap();
    return admit(builder.finish(root).unwrap(), &Quotas::default(), &table).unwrap();
}

/// The plan that `steps` build, rooted at the last open node, or at the last
/// real node when no step builds an open node. A step whose exact value could
/// pass [`SIZE_BOUND`] bits is skipped, so the oracle's work stays bounded.
///
/// # Specification
/// trivial.
fn build(steps: &[Step]) -> ValidatedPlan
{
    let mut builder = PlanBuilder::new();
    let mut reals: Vec<(RealId, u64)> =
        vec![(builder.real(Real::Constant(Dyadic::ONE)).unwrap(), 1)];
    let mut opens: Vec<OpenId> = Vec::new();
    for step in steps {
        let real = |draw: usize| reals[draw.checked_rem(reals.len()).unwrap()];
        let open = |draw: usize| {
            opens
                .get(draw.checked_rem(opens.len().max(1)).unwrap())
                .copied()
        };
        match *step {
            Step::Constant(ref value) => {
                // The exponent spans at most eight bits of the fraction.
                let size = u64::from(value.width()).checked_add(8).unwrap();
                reals.push((builder.real(Real::Constant(value.clone())).unwrap(), size));
            },
            Step::Arithmetic(kind, left, right) => {
                let ((left, left_size), (right, right_size)) = (real(left), real(right));
                // A rational's numerator and denominator each grow by at most
                // the operands' sizes under each of the four operations.
                let size = left_size.checked_add(right_size).unwrap();
                if size <= SIZE_BOUND {
                    let node = match kind.checked_rem(4).unwrap() {
                        0 => Real::Add(left, right),
                        1 => Real::Sub(left, right),
                        2 => Real::Mul(left, right),
                        _ => Real::Div {
                            numerator: left,
                            denominator: right,
                            nonzero: nonzero(),
                        },
                    };
                    reals.push((builder.real(node).unwrap(), size));
                }
            },
            Step::Power(base, power) => {
                let (base, base_size) = real(base);
                let size = base_size.checked_mul(u64::from(power)).unwrap().max(1);
                if size <= SIZE_BOUND {
                    let node = Real::Power(base, Power::from(power));
                    reals.push((builder.real(node).unwrap(), size));
                }
            },
            Step::Less(left, right) => {
                let less = Open::Less(real(left).0, real(right).0);
                opens.push(builder.open(less).unwrap());
            },
            Step::Lattice(meet, left, right) => {
                if let (Some(left), Some(right)) = (open(left), open(right)) {
                    let node = if meet {
                        Open::Meet(left, right)
                    }
                    else {
                        Open::Join(left, right)
                    };
                    opens.push(builder.open(node).unwrap());
                }
            },
            Step::ConstantOpen(holds) => {
                let node = if holds { Open::Top } else { Open::Bottom };
                opens.push(builder.open(node).unwrap());
            },
        }
    }
    let root = opens.last().map_or_else(
        || Root::Real(reals.last().unwrap().0),
        |&open| Root::Open(open),
    );
    return admitted(builder, root);
}

/// The oracle's value of every node of a closed plan, in node order.
///
/// # Specification
/// - ensures: one value per node; a quotient by zero and every node that reads
///   an undefined node are undefined.
/// - panics: none.
/// - executable: none — the oracle is the specification that a clause would
///   restate.
///
/// # Adequacy
/// - hypothesis: L2 — the oracle of the differential test.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
fn evaluated(plan: &Plan) -> Vec<Exact>
{
    let mut values: Vec<Exact> = Vec::new();
    for (_, node) in plan.nodes() {
        let real = |id: RealId| match values.get(usize::from(id.node())) {
            Some(&Exact::Real(ref value)) => Some(value.clone()),
            _ => None,
        };
        let truth = |id: OpenId| match values.get(usize::from(id.node())) {
            Some(&Exact::Holds) => Some(true),
            Some(&Exact::Fails) => Some(false),
            _ => None,
        };
        let value = match *node {
            Node::Real(ref real_node) => {
                let value = match *real_node {
                    Real::Constant(ref constant) => Some(Rational::of(constant)),
                    Real::Add(left, right) => real(left).zip(real(right)).map(|(x, y)| x.plus(&y)),
                    Real::Sub(left, right) => real(left).zip(real(right)).map(|(x, y)| x.minus(&y)),
                    Real::Mul(left, right) => real(left).zip(real(right)).map(|(x, y)| x.times(&y)),
                    Real::Div {
                        numerator,
                        denominator,
                        ..
                    } => real(numerator)
                        .zip(real(denominator))
                        .and_then(|(x, y)| x.quotient(&y).ok()),
                    Real::Power(base, power) => real(base).map(|x| {
                        (0 .. u32::from(power))
                            .fold(Rational::of(&Dyadic::ONE), |product, _| product.times(&x))
                    }),
                    Real::Bound(_)
                    | Real::Cut(_)
                    | Real::Pi
                    | Real::Cos(_)
                    | Real::Sin(_)
                    | Real::Arg(..) => None,
                };
                value.map_or(Exact::Undefined, Exact::Real)
            },
            Node::Open(ref open) => {
                let holds = match *open {
                    Open::Top => Some(true),
                    Open::Bottom => Some(false),
                    Open::Less(left, right) => real(left)
                        .zip(real(right))
                        .map(|(x, y)| x.order(&y) == Ordering::Less),
                    Open::LowerCut(cut, point) => real(point)
                        .zip(real(cut))
                        .map(|(x, y)| x.order(&y) == Ordering::Less),
                    Open::UpperCut(cut, point) => real(cut)
                        .zip(real(point))
                        .map(|(x, y)| x.order(&y) == Ordering::Less),
                    Open::Meet(left, right) => truth(left).zip(truth(right)).map(|(x, y)| x && y),
                    Open::Join(left, right) => truth(left).zip(truth(right)).map(|(x, y)| x || y),
                    Open::Exists(_) | Open::Forall(_) => None,
                };
                match holds {
                    Some(true) => Exact::Holds,
                    Some(false) => Exact::Fails,
                    None => Exact::Undefined,
                }
            },
            Node::Domain(_) => Exact::Undefined,
        };
        values.push(value);
    }
    return values;
}

/// Generated constants: small dyadics of both signs and, less often, wide
/// ones that a low precision must round.
///
/// # Specification
/// - ensures: every generated value is canonical.
/// - panics: none.
/// - executable: none — a strategy is opaque to the attribute backend.
///
/// # Adequacy
/// - hypothesis: L2 — the generator feeds the differential test.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
fn constant() -> impl Strategy<Value = Dyadic>
{
    let bytes = prop_oneof![
        4 => proptest::collection::vec(any::<u8>(), 0 ..= 2),
        1 => proptest::collection::vec(any::<u8>(), 3 ..= 12),
    ];
    return (bytes, any::<bool>(), -6_i32 ..= 6_i32).prop_map(|(bytes, negative, exponent)| {
        let magnitude = BigInt::from_bytes_le(num_bigint::Sign::Plus, &bytes);
        let mantissa = if negative {
            core::ops::Neg::neg(magnitude)
        }
        else {
            magnitude
        };
        Dyadic::new(mantissa, Exponent::from(exponent)).unwrap()
    });
}

/// The strategy of one step: arithmetic and comparisons most often.
///
/// # Specification
/// - ensures: every generated step builds a closed node.
/// - panics: none.
/// - executable: none — a strategy is opaque to the attribute backend.
///
/// # Adequacy
/// - hypothesis: L2 — the generator feeds the differential test.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
fn step() -> impl Strategy<Value = Step>
{
    let index = 0_usize .. 64;
    return prop_oneof![
        2 => constant().prop_map(Step::Constant),
        4 => (any::<u8>(), index.clone(), index.clone())
            .prop_map(|(kind, left, right)| Step::Arithmetic(kind, left, right)),
        1 => (index.clone(), 0_u32 ..= 3).prop_map(|(base, power)| Step::Power(base, power)),
        3 => (index.clone(), index.clone()).prop_map(|(left, right)| Step::Less(left, right)),
        2 => (any::<bool>(), index.clone(), index)
            .prop_map(|(meet, left, right)| Step::Lattice(meet, left, right)),
        1 => any::<bool>().prop_map(Step::ConstantOpen),
    ];
}

/// The constant `value` in `builder`.
///
/// # Specification
/// trivial.
fn constant_in(
    builder: &mut PlanBuilder,
    value: Dyadic,
) -> RealId
{
    return builder.real(Real::Constant(value)).unwrap();
}

/// The quotient of two reals in `builder`.
///
/// # Specification
/// trivial.
fn quotient_in(
    builder: &mut PlanBuilder,
    numerator: RealId,
    denominator: RealId,
) -> RealId
{
    return builder
        .real(Real::Div {
            numerator,
            denominator,
            nonzero: nonzero(),
        })
        .unwrap();
}

/// The expression `1/3` in `builder`.
///
/// # Specification
/// trivial.
fn third_in(builder: &mut PlanBuilder) -> RealId
{
    let one = constant_in(builder, Dyadic::ONE);
    let three = constant_in(builder, Dyadic::from(3_i64));
    return quotient_in(builder, one, three);
}

/// The expression `1/3 + 1/3` in `builder`.
///
/// # Specification
/// trivial.
fn twice_third_in(builder: &mut PlanBuilder) -> RealId
{
    let third = third_in(builder);
    return builder.real(Real::Add(third, third)).unwrap();
}

/// The plan of `left < right`, both built in `builder`.
///
/// # Specification
/// trivial.
fn below(
    mut builder: PlanBuilder,
    left: RealId,
    right: RealId,
) -> ValidatedPlan
{
    let less = builder.open(Open::Less(left, right)).unwrap();
    return admitted(builder, Root::Open(less));
}

/// The approximants of a plan's open root at `precision`.
///
/// # Specification
/// trivial.
fn root_approximants(
    plan: &ValidatedPlan,
    precision: Precision,
) -> BilateralApprox
{
    return approximate(plan, precision)
        .approximants(plan.plan().root().node())
        .unwrap();
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Every oracle value lies in its node's enclosure, every proven
    /// approximant agrees with the oracle's truth, and no proposition is
    /// proven both true and false, at each of several precisions.
    #[test]
    fn approximants_agree_with_the_rational_oracle(steps in prop::collection::vec(step(), 0 .. 24)) {
        let plan = build(&steps);
        let exact = evaluated(plan.plan());
        for bits in PRECISIONS {
            let approximation = approximate(&plan, Precision::try_from(bits).unwrap());
            for (node, value) in exact.iter().enumerate() {
                let node = NodeId::try_from(node).unwrap();
                if let Exact::Real(ref value) = *value {
                    let enclosure = approximation.enclosure(node).unwrap();
                    prop_assert_eq!(value.within(enclosure), Containment::Contains, "{} bits", bits);
                }
                if let Ok(approximants) = approximation.approximants(node) {
                    let proven_true = approximants.positive == PositiveApprox::ProvenTrue;
                    let proven_false = approximants.negative == NegativeApprox::ProvenFalse;
                    prop_assert!(!(proven_true && proven_false), "both proven at {} bits", bits);
                    match *value {
                        Exact::Holds => prop_assert!(!proven_false, "a true node proven false at {} bits", bits),
                        Exact::Fails => prop_assert!(!proven_true, "a false node proven true at {} bits", bits),
                        Exact::Real(_) | Exact::Undefined => {},
                    }
                }
            }
        }
    }
}

#[test]
fn a_third_twice_decides_below_one_at_a_finer_precision()
{
    let at = |count: u32| Precision::try_from(count).unwrap();
    let mut builder = PlanBuilder::new();
    let twice = twice_third_in(&mut builder);
    let one = constant_in(&mut builder, Dyadic::ONE);
    let below_one = below(builder, twice, one);
    for count in [1, 2, 8, 64] {
        assert_eq!(
            root_approximants(&below_one, at(count)),
            BilateralApprox::TRUE
        );
    }
    // 683/1024 lies 1/3072 above 2/3, so the enclosure of 2/3 must narrow
    // below it before the comparison decides. It decides from ten bits on,
    // and below ten bits it stays undecided.
    let mut builder = PlanBuilder::new();
    let twice = twice_third_in(&mut builder);
    let numerator = constant_in(&mut builder, Dyadic::from(683_i64));
    let denominator = constant_in(&mut builder, Dyadic::from(1024_i64));
    let bound = quotient_in(&mut builder, numerator, denominator);
    let below_bound = below(builder, twice, bound);
    for count in 1 ..= 16 {
        let expected = if count < 10 {
            BilateralApprox::UNDECIDED
        }
        else {
            BilateralApprox::TRUE
        };
        assert_eq!(
            root_approximants(&below_bound, at(count)),
            expected,
            "{count} bits"
        );
    }
}

#[test]
fn an_undecided_comparison_is_never_false()
{
    // Each comparison has equal sides: `1/3 · 3` and one in both orders,
    // `1/3 + 1/3` and `2/3`, and `1/3` and itself.
    let mut plans = Vec::new();
    for flipped in [false, true] {
        let mut builder = PlanBuilder::new();
        let third = third_in(&mut builder);
        let three = constant_in(&mut builder, Dyadic::from(3_i64));
        let one_again = builder.real(Real::Mul(third, three)).unwrap();
        let one = constant_in(&mut builder, Dyadic::ONE);
        plans.push(if flipped {
            below(builder, one, one_again)
        }
        else {
            below(builder, one_again, one)
        });
    }
    let mut builder = PlanBuilder::new();
    let twice = twice_third_in(&mut builder);
    let two = constant_in(&mut builder, Dyadic::from(2_i64));
    let three = constant_in(&mut builder, Dyadic::from(3_i64));
    let two_thirds = quotient_in(&mut builder, two, three);
    plans.push(below(builder, twice, two_thirds));
    let mut builder = PlanBuilder::new();
    let third = third_in(&mut builder);
    plans.push(below(builder, third, third));
    for plan in &plans {
        for count in [1, 2, 8, 32, 64, 128, 256, 1024] {
            assert_eq!(
                root_approximants(plan, Precision::try_from(count).unwrap()),
                BilateralApprox::UNDECIDED,
                "{count} bits"
            );
        }
    }
}

#[test]
fn meet_and_join_follow_their_tables()
{
    let truth = |approximants: BilateralApprox| match approximants {
        BilateralApprox::TRUE => Some(true),
        BilateralApprox::FALSE => Some(false),
        _ => None,
    };
    let of = |value: Option<bool>| match value {
        Some(true) => BilateralApprox::TRUE,
        Some(false) => BilateralApprox::FALSE,
        None => BilateralApprox::UNDECIDED,
    };
    let all = [
        BilateralApprox::TRUE,
        BilateralApprox::FALSE,
        BilateralApprox::UNDECIDED,
    ];
    for left in all {
        for right in all {
            let meet = match (truth(left), truth(right)) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            };
            let join = match (truth(left), truth(right)) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            };
            assert_eq!(left.meet(right), of(meet), "{left:?} meet {right:?}");
            assert_eq!(left.join(right), of(join), "{left:?} join {right:?}");
        }
    }
}

#[test]
fn a_divisor_enclosing_zero_gives_the_whole_line()
{
    let mut builder = PlanBuilder::new();
    let third = third_in(&mut builder);
    let zero = builder.real(Real::Sub(third, third)).unwrap();
    let one = constant_in(&mut builder, Dyadic::ONE);
    let quotient = quotient_in(&mut builder, one, zero);
    let plan = admitted(builder, Root::Real(quotient));
    let approximation = approximate(&plan, Precision::try_from(64_u32).unwrap());
    let root = plan.plan().root().node();
    assert_eq!(
        approximation.enclosure(root).unwrap(),
        &NumericInterval::whole()
    );
}

#[test]
fn lookups_refuse_a_foreign_node()
{
    let mut builder = PlanBuilder::new();
    let one = constant_in(&mut builder, Dyadic::ONE);
    let two = constant_in(&mut builder, Dyadic::from(2_i64));
    let plan = below(builder, one, two);
    let approximation = approximate(&plan, Precision::try_from(8_u32).unwrap());
    let root = plan.plan().root().node();
    let past = NodeId::try_from(usize::from(plan.plan().node_count())).unwrap();
    assert_eq!(approximation.approximants(root), Ok(BilateralApprox::TRUE));
    assert_eq!(approximation.enclosure(root), Err(PlanError::WrongSort));
    assert_eq!(approximation.enclosure(past), Err(PlanError::UnknownNode));
    assert_eq!(
        approximation.approximants(past),
        Err(PlanError::UnknownNode)
    );
    let first = NodeId::try_from(0_usize).unwrap();
    assert_eq!(
        approximation.enclosure(first),
        Ok(&NumericInterval::point(Dyadic::ONE))
    );
    assert_eq!(approximation.approximants(first), Err(PlanError::WrongSort));
}
