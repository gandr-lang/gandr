//! The builtin elementary functions: π held to its decimal digits, the cosine
//! and the sine held to their identities, the angle held to the octants, and
//! each enclosure nested inside the enclosure at a coarser precision. The
//! checker refuses a builtin's step past its width quota, and the refinement
//! machine certifies obligations over the builtins and resumes them.

use core::cmp::Ordering;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Answer;
use gandr_theory_exact_reals::BitWidth;
use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CertificateCheck;
use gandr_theory_exact_reals::CertificateRefusal;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::DecodeError;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedCertificate;
use gandr_theory_exact_reals::EncodedCheckpoint;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::FormatVersion;
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
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounding;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::Step;
use gandr_theory_exact_reals::StepId;
use gandr_theory_exact_reals::StepSite;
use gandr_theory_exact_reals::SuspendReason;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::angle;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::cosine;
use gandr_theory_exact_reals::pi;
use gandr_theory_exact_reals::sine;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;

use crate::oracle::Rational;

/// A decimal truncation of a positive real: the real lies at or above it,
/// and below it plus one unit of its last digit.
#[repr(transparent)]
struct Decimal(&'static str);

/// The first 70 decimal digits of π.
const PI: Decimal =
    Decimal("3.141592653589793238462643383279502884197169399375105820974944592307816");

/// The first 60 decimals of `cos 1/2`.
const COS_HALF: Decimal = Decimal("0.877582561890372716116281582603829651991645197109744052997610");

/// The first 60 decimals of `sin 1/2`.
const SIN_HALF: Decimal = Decimal("0.479425538604203000273287935215571388081803367940600675188616");

/// The first 60 decimals of `atan 1/2`.
const ATAN_HALF: Decimal =
    Decimal("0.463647609000806116214256231461214402028537054286120263810933");

/// The first 60 decimals of `cos (π/4)`, the square root of one half.
const COS_QUARTER_PI: Decimal =
    Decimal("0.707106781186547524400844362104849039284835937688474036588339");

/// The truncation as a rational, and one unit of its last digit.
///
/// # Specification
/// trivial.
fn fraction(decimal: &Decimal) -> (Rational, Rational)
{
    let integer = |value: BigInt| Rational::of(&Dyadic::new(value, Exponent::from(0_i32)).unwrap());
    let (whole, part) = decimal.0.split_once('.').unwrap();
    let digits: BigInt = format!("{whole}{part}").parse().unwrap();
    let scale = integer(BigInt::from(10_u8).pow(u32::try_from(part.len()).unwrap()));
    let truncation = integer(digits).quotient(&scale).unwrap();
    let unit = integer(BigInt::from(1_u8)).quotient(&scale).unwrap();
    return (truncation, unit);
}

/// The finite ends of a proper interval.
///
/// # Specification
/// trivial.
fn ends(interval: &NumericInterval) -> (Dyadic, Dyadic)
{
    let (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) =
        (&interval.lower().endpoint, &interval.upper().endpoint)
    else {
        panic!("a finite interval: {interval:?}");
    };
    assert_eq!(interval.orientation(), Orientation::Proper);
    return (lower.clone(), upper.clone());
}

/// Assert that `interval` meets the span of `decimal`, from the truncation
/// to the truncation plus one unit of its last digit, as it does when it
/// holds the real.
///
/// # Specification
/// trivial.
fn meets(
    interval: &NumericInterval,
    decimal: &Decimal,
)
{
    let (lower, upper) = ends(interval);
    let (truncation, unit) = fraction(decimal);
    assert_ne!(
        Rational::of(&upper).order(&truncation),
        Ordering::Less,
        "{interval:?} ends below {}",
        decimal.0
    );
    assert_ne!(
        Rational::of(&lower).order(&truncation.plus(&unit)),
        Ordering::Greater,
        "{interval:?} starts above {}",
        decimal.0
    );
}

/// The exact width of a finite interval.
///
/// # Specification
/// trivial.
fn width(interval: &NumericInterval) -> Dyadic
{
    let (lower, upper) = ends(interval);
    return upper
        .sub(&lower, Precision::MAX, Rounding::Ceiling)
        .unwrap()
        .into_value();
}

/// `2^exponent`.
///
/// # Specification
/// trivial.
fn power_of_two(exponent: Exponent) -> Dyadic
{
    return Dyadic::new(BigInt::from(1_u8), exponent).unwrap();
}

/// Assert that `inner` lies inside `outer`.
///
/// # Specification
/// trivial.
fn nested(
    inner: &NumericInterval,
    outer: &NumericInterval,
)
{
    let (inner_lower, inner_upper) = ends(inner);
    let (outer_lower, outer_upper) = ends(outer);
    assert!(
        outer_lower <= inner_lower && inner_upper <= outer_upper,
        "{inner:?} lies inside {outer:?}"
    );
}

/// Assert that `first` and `second` share a point.
///
/// # Specification
/// trivial.
fn overlap(
    first: &NumericInterval,
    second: &NumericInterval,
)
{
    let (first_lower, first_upper) = ends(first);
    let (second_lower, second_upper) = ends(second);
    assert!(
        first_lower <= second_upper && second_lower <= first_upper,
        "{first:?} meets {second:?}"
    );
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
    .unwrap();
}

#[test]
fn pi_holds_its_first_seventy_digits()
{
    // The try-first of the unit: π at 256 bits holds its first 70 digits.
    let precision = Precision::try_from(256_u32).unwrap();
    let enclosure = pi(precision).unwrap();
    meets(&enclosure, &PI);
    assert!(width(&enclosure) <= power_of_two(Exponent::from(-253_i32)));
}

#[test]
fn cosine_and_sine_meet_their_identities()
{
    let bits = |count: u32| Precision::try_from(count).unwrap();
    let point = |value: i64| NumericInterval::point(Dyadic::from(value));
    let exact = Precision::MAX;
    let precision = bits(256);
    let narrow = power_of_two(Exponent::from(-253_i32));
    let half = NumericInterval::point(power_of_two(Exponent::from(-1_i32)));
    meets(&cosine(&half, precision).unwrap(), &COS_HALF);
    meets(&sine(&half, precision).unwrap(), &SIN_HALF);
    let (cos_zero, sin_zero) = (
        ends(&cosine(&point(0), precision).unwrap()),
        ends(&sine(&point(0), precision).unwrap()),
    );
    assert!(cos_zero.0 <= Dyadic::ONE && cos_zero.1 == Dyadic::ONE);
    assert!(sin_zero.0 < Dyadic::ZERO && Dyadic::ZERO < sin_zero.1);
    // `cos² x + sin² x = 1` and `cos 2x = 1 − 2 sin² x`, at points past many
    // turns of each sign, up to the last point that a reduction serves.
    let one = NumericInterval::point(Dyadic::ONE);
    let two = point(2);
    for value in [-7_i64, 3, 100, 30_000, -30_001, 0x7FFF] {
        let (c, s) = (
            cosine(&point(value), precision).unwrap(),
            sine(&point(value), precision).unwrap(),
        );
        assert!(
            width(&c) <= narrow && width(&s) <= narrow,
            "narrow at {value}"
        );
        let square = |x: &NumericInterval| x.mul(x, exact).unwrap();
        let pythagoras = square(&c).add(&square(&s), exact).unwrap();
        overlap(&pythagoras, &one);
        let doubled = cosine(&point(value * 2), precision).unwrap();
        let identity = one
            .sub(&two.mul(&square(&s), exact).unwrap(), exact)
            .unwrap();
        overlap(&doubled, &identity);
    }
    // An interval that holds a critical point reaches its extreme.
    let three_to_four = closed(Dyadic::from(3_i64), Dyadic::from(4_i64));
    let (lower, upper) = ends(&cosine(&three_to_four, precision).unwrap());
    assert!(lower == -&Dyadic::ONE && upper < Dyadic::ZERO);
    let one_to_two = closed(Dyadic::ONE, Dyadic::from(2_i64));
    let (lower, upper) = ends(&sine(&one_to_two, precision).unwrap());
    assert!(Dyadic::ZERO < lower && upper == Dyadic::ONE);
    // An interval two turns wide, and a point past 2^16, give the unit range.
    let unit = closed(-&Dyadic::ONE, Dyadic::ONE);
    let wide = closed(Dyadic::ZERO, Dyadic::from(7_i64));
    assert_eq!(cosine(&wide, precision).unwrap(), unit);
    assert_eq!(sine(&point(0x0001_0000), precision).unwrap(), unit);
    let near = ends(&sine(&point(0xFFFF), precision).unwrap());
    assert!(-&Dyadic::ONE < near.0 && near.1 < Dyadic::ONE);
}

#[test]
fn angles_of_the_octants_and_the_origin()
{
    let precision = Precision::try_from(256_u32).unwrap();
    let exact = Precision::MAX;
    let point = |value: i64| NumericInterval::point(Dyadic::from(value));
    let narrow = power_of_two(Exponent::from(-252_i32));
    let pi_interval = pi(precision).unwrap();
    let octants = [
        (1_i64, 0_i64, 0_i64),
        (1, 1, 1),
        (0, 1, 2),
        (-1, 1, 3),
        (-1, 0, 4),
        (-1, -1, -3),
        (0, -1, -2),
        (1, -1, -1),
        (5, 5, 1),
    ];
    for (x, y, eighths) in octants {
        let found = angle(&point(x), &point(y), precision).unwrap();
        assert!(width(&found) <= narrow, "narrow at ({x}, {y})");
        let quarter = Dyadic::new(BigInt::from(eighths), Exponent::from(-2_i32)).unwrap();
        let expected = pi_interval
            .mul(&NumericInterval::point(quarter), exact)
            .unwrap();
        overlap(&found, &expected);
    }
    meets(&angle(&point(2), &point(1), precision).unwrap(), &ATAN_HALF);
    meets(&angle(&point(4), &point(2), precision).unwrap(), &ATAN_HALF);
    // The angle of `(1, 2)` is `π/2 − atan (1/2)`.
    let steep = angle(&point(1), &point(2), precision).unwrap();
    let half_pi = pi_interval
        .mul(
            &NumericInterval::point(power_of_two(Exponent::from(-1_i32))),
            exact,
        )
        .unwrap();
    meets(&half_pi.sub(&steep, exact).unwrap(), &ATAN_HALF);
    // The origin, a box that holds it, and a box across the negative axis.
    assert_eq!(
        angle(&point(0), &point(0), precision).unwrap(),
        NumericInterval::point(Dyadic::ZERO)
    );
    let unit = closed(-&Dyadic::ONE, Dyadic::ONE);
    let circle = angle(&unit, &unit, precision).unwrap();
    let (lower, upper) = ends(&circle);
    // The circle reaches past π on each side, and no further than twice the
    // enclosure of π spans.
    let (pi_truncation, _pi_unit) = fraction(&PI);
    assert_eq!(
        Rational::of(&upper).order(&pi_truncation),
        Ordering::Greater
    );
    assert_eq!(
        Rational::of(&-&lower).order(&pi_truncation),
        Ordering::Greater
    );
    assert!(
        width(&circle)
            <= pi_interval
                .mul(&NumericInterval::point(Dyadic::from(2_i64)), exact)
                .map(|twice| ends(&twice).1)
                .unwrap()
    );
    let left = closed(Dyadic::from(-2_i64), -&Dyadic::ONE);
    assert_eq!(angle(&left, &unit, precision).unwrap(), circle);
    // A box of the first quadrant spans the angles of its corners.
    let box_side = closed(Dyadic::ONE, Dyadic::from(2_i64));
    let span = angle(&box_side, &box_side, precision).unwrap();
    meets(&span, &ATAN_HALF);
    let (lower, _) = ends(&span);
    assert!(lower > Dyadic::new(BigInt::from(29_u8), Exponent::from(-6_i32)).unwrap());
}

#[test]
fn a_finer_precision_nests_inside_a_coarser_one()
{
    let bits = |count: u32| Precision::try_from(count).unwrap();
    let point = |value: i64| NumericInterval::point(Dyadic::from(value));
    let half = NumericInterval::point(power_of_two(Exponent::from(-1_i32)));
    let arguments = [
        half.clone(),
        point(30_000),
        point(-5),
        closed(Dyadic::from(3_i64), Dyadic::from(4_i64)),
        closed(Dyadic::ONE, Dyadic::from(2_i64)),
    ];
    let corners = [
        (point(-1), point(1)),
        (point(3), point(-2)),
        (
            closed(Dyadic::ONE, Dyadic::from(2_i64)),
            closed(Dyadic::ONE, Dyadic::from(2_i64)),
        ),
    ];
    for (coarse, fine) in [(64_u32, 256_u32), (256, 1024)] {
        let (coarse, fine) = (bits(coarse), bits(fine));
        nested(&pi(fine).unwrap(), &pi(coarse).unwrap());
        for argument in &arguments {
            nested(
                &cosine(argument, fine).unwrap(),
                &cosine(argument, coarse).unwrap(),
            );
            nested(
                &sine(argument, fine).unwrap(),
                &sine(argument, coarse).unwrap(),
            );
        }
        for &(ref x, ref y) in &corners {
            nested(&angle(x, y, fine).unwrap(), &angle(x, y, coarse).unwrap());
        }
        // A finer enclosure of the argument, at a finer precision, lies
        // inside the coarser enclosure over the coarser argument.
        let (fine_argument, coarse_argument) =
            (cosine(&half, fine).unwrap(), cosine(&half, coarse).unwrap());
        nested(
            &sine(&fine_argument, fine).unwrap(),
            &sine(&coarse_argument, coarse).unwrap(),
        );
    }
}

#[test]
fn a_step_past_the_width_quota_is_refused()
{
    let bits = |count: u32| Precision::try_from(count).unwrap();
    let mut builder = PlanBuilder::new();
    let circle = builder.real(Real::Pi).unwrap();
    let wave = builder.real(Real::Cos(circle)).unwrap();
    let plan = admit(
        builder.finish(Root::Real(wave)).unwrap(),
        &Quotas::default(),
        &EvidenceTable::new(),
    )
    .unwrap();
    let circle_constant = find(&plan, |node| matches!(*node, Node::Real(Real::Pi)));
    let wave = plan.plan().root().node();
    let quotas = CheckerQuotas {
        width: BitWidth::from(1000_u64),
        ..CheckerQuotas::default()
    };
    let certificate = |steps: Vec<Step>| Certificate::new(FormatVersion::CURRENT, steps);
    let refused = |index: u32, refusal: CertificateCheck| {
        Err(CertificateRefusal {
            site: StepSite::Step(StepId::from(index)),
            check: refusal,
        })
    };
    let first = |precision: Precision| Step::Pi {
        real: circle_constant,
        precision,
    };
    // A rule works at its precision plus 88 bits, so 912 bits fit a width
    // quota of 1000 bits and 913 do not.
    let at_quota = certificate(vec![first(bits(912)), Step::Cosine {
        real: wave,
        argument: StepId::from(0_u32),
        precision: bits(912),
    }]);
    let checked = check(&plan, &at_quota, &quotas).unwrap();
    let Conclusion::Encloses { real, ref interval } = *checked.conclusion()
    else {
        panic!("a cosine step encloses its node");
    };
    assert_eq!(real, wave);
    let (lower, _) = ends(interval);
    assert!(lower == -&Dyadic::ONE && width(interval) <= power_of_two(Exponent::from(-900_i32)));
    assert_eq!(
        check(&plan, &certificate(vec![first(bits(913))]), &quotas),
        refused(0, CertificateCheck::WidthQuota)
    );
    let past = certificate(vec![first(bits(64)), Step::Cosine {
        real: wave,
        argument: StepId::from(0_u32),
        precision: bits(913),
    }]);
    assert_eq!(
        check(&plan, &past, &quotas),
        refused(1, CertificateCheck::WidthQuota)
    );
    // A step of another node, and a premise of another node, are refused by
    // name.
    let wrong = certificate(vec![Step::Pi {
        real: wave,
        precision: bits(64),
    }]);
    assert_eq!(
        check(&plan, &wrong, &quotas),
        refused(0, CertificateCheck::WrongNode)
    );
    let misread = certificate(vec![
        first(bits(64)),
        Step::Cosine {
            real: wave,
            argument: StepId::from(0_u32),
            precision: bits(64),
        },
        Step::Sine {
            real: wave,
            argument: StepId::from(0_u32),
            precision: bits(64),
        },
    ]);
    assert_eq!(
        check(&plan, &misread, &quotas),
        refused(2, CertificateCheck::WrongNode)
    );
    let premise = certificate(vec![
        first(bits(64)),
        Step::Cosine {
            real: wave,
            argument: StepId::from(0_u32),
            precision: bits(64),
        },
        Step::Cosine {
            real: wave,
            argument: StepId::from(1_u32),
            precision: bits(64),
        },
    ]);
    assert_eq!(
        check(&plan, &premise, &quotas),
        refused(2, CertificateCheck::PremiseConclusion)
    );
    // The bytes of a builtin's step round-trip, and a precision of no bits
    // is refused.
    let bytes = at_quota.encode();
    assert_eq!(
        Certificate::decode(EncodedCertificate::from(&bytes)),
        Ok(at_quota)
    );
    let mut zero: Vec<u8> = bytes.into();
    let length = zero.len();
    zero.splice(length - 4 .. length, 0_u32.to_le_bytes());
    assert!(matches!(
        Certificate::decode(EncodedCertificate::from(zero.as_slice())),
        Err(DecodeError::Dyadic(_))
    ));
}

/// The first node of `plan` that `wanted` picks.
///
/// # Specification
/// trivial.
fn find<Wanted>(
    plan: &ValidatedPlan,
    wanted: Wanted,
) -> NodeId
where
    Wanted: Fn(&Node) -> bool,
{
    return plan
        .plan()
        .nodes()
        .find(|&(_, node)| wanted(node))
        .unwrap()
        .0;
}

/// The nodes of the machine's plan.
struct Nodes
{
    /// `cos (π/4)`.
    cosine: NodeId,
    /// `π`.
    circle: NodeId,
    /// `181/256 < cos (π/4)`.
    above: NodeId,
    /// `sin (π/4) < 2897/4096`.
    below: NodeId,
    /// `2897/4096 < cos (π/4)`, which fails.
    reversed: NodeId,
    /// The angle of the origin.
    origin: NodeId,
    /// The cosine of the square root of two, a cut.
    over_cut: NodeId,
}

/// The machine's plan, and its nodes.
///
/// # Specification
/// trivial.
fn machine_plan() -> (ValidatedPlan, Nodes)
{
    let value = |mantissa: u16, exponent: i32| {
        Dyadic::new(BigInt::from(mantissa), Exponent::from(exponent)).unwrap()
    };
    let (low, high) = (value(181, -8_i32), value(2897, -12_i32));
    let mut builder = PlanBuilder::new();
    let mut constant = |value: &Dyadic| builder.real(Real::Constant(value.clone())).unwrap();
    let (quarter, low_node, high_node, zero) = (
        constant(&value(1, -2_i32)),
        constant(&low),
        constant(&high),
        constant(&Dyadic::ZERO),
    );
    let circle = builder.real(Real::Pi).unwrap();
    let eighth_turn = builder.real(Real::Mul(circle, quarter)).unwrap();
    let cosine = builder.real(Real::Cos(eighth_turn)).unwrap();
    let sine = builder.real(Real::Sin(eighth_turn)).unwrap();
    let above = builder.open(Open::Less(low_node, cosine)).unwrap();
    let below = builder.open(Open::Less(sine, high_node)).unwrap();
    let reversed = builder.open(Open::Less(high_node, cosine)).unwrap();
    let origin = builder.real(Real::Arg(zero, zero)).unwrap();
    let laws = Evidence::from(0_u32);
    let root_two = square_root_of_two(&mut builder, laws).unwrap();
    let over_cut = builder.real(Real::Cos(root_two)).unwrap();
    let mut joined = builder.open(Open::Join(above, below)).unwrap();
    joined = builder.open(Open::Join(joined, reversed)).unwrap();
    for real in [origin, over_cut, circle] {
        let reads = builder.open(Open::Less(real, real)).unwrap();
        joined = builder.open(Open::Join(joined, reads)).unwrap();
    }
    let mut table = EvidenceTable::new();
    table.register(laws, Judgement::CutLaws).unwrap();
    let plan = admit(
        builder.finish(Root::Open(joined)).unwrap(),
        &Quotas::default(),
        &table,
    )
    .unwrap();
    // The canonical form numbers the nodes again, so each is found by its
    // form.
    let real = |id: RealId| match plan.plan().node(id.node()) {
        Ok(&Node::Real(ref real)) => Some(real.clone()),
        Ok(_) | Err(_) => None,
    };
    let is_constant = |id: RealId, wanted: &Dyadic| matches!(real(id), Some(Real::Constant(ref found)) if found == wanted);
    let nodes = Nodes {
        cosine: find(
            &plan,
            |node| matches!(*node, Node::Real(Real::Cos(x)) if matches!(real(x), Some(Real::Mul(..)))),
        ),
        circle: find(&plan, |node| matches!(*node, Node::Real(Real::Pi))),
        above: find(
            &plan,
            |node| matches!(*node, Node::Open(Open::Less(left, right)) if is_constant(left, &low) && matches!(real(right), Some(Real::Cos(_)))),
        ),
        below: find(
            &plan,
            |node| matches!(*node, Node::Open(Open::Less(left, _)) if matches!(real(left), Some(Real::Sin(_)))),
        ),
        reversed: find(
            &plan,
            |node| matches!(*node, Node::Open(Open::Less(left, right)) if is_constant(left, &high) && matches!(real(right), Some(Real::Cos(_)))),
        ),
        origin: find(&plan, |node| matches!(*node, Node::Real(Real::Arg(..)))),
        over_cut: find(
            &plan,
            |node| matches!(*node, Node::Real(Real::Cos(x)) if matches!(real(x), Some(Real::Cut(_)))),
        ),
    };
    return (plan, nodes);
}

#[test]
fn the_machine_certifies_the_builtins()
{
    let (plan, nodes) = machine_plan();
    let quotas = CheckerQuotas::default();
    let quantum = Quantum::from(NonZeroU32::new(1).unwrap());
    let ample = Budget::from(u64::MAX);
    let enclose = |real: NodeId, exponent: i32| {
        Obligation::new(&plan, real, Demand::Encloses {
            width: Exponent::from(exponent),
        })
        .unwrap()
    };
    let decide = |open: NodeId, demand: Demand| Obligation::new(&plan, open, demand).unwrap();
    let obligations = [
        enclose(nodes.cosine, -100_i32),
        enclose(nodes.circle, -200_i32),
        decide(nodes.above, Demand::Holds),
        decide(nodes.below, Demand::Holds),
        decide(nodes.reversed, Demand::Fails),
        decide(nodes.reversed, Demand::Holds),
        enclose(nodes.origin, -10_i32),
        enclose(nodes.over_cut, -10_i32),
    ];
    let mut dovetail = Dovetail::new(&plan, obligations, quantum, quotas);
    let report = dovetail.run(ample, Rounds::from(4096_u64), || false);
    let mut certificates: Vec<Certificate> = Vec::new();
    for (index, obligation) in obligations.iter().enumerate() {
        match report.outcome(Position::from(index)) {
            Some(Outcome::Certified(certificate)) => {
                let checked = check(&plan, certificate, &quotas).unwrap();
                assert_eq!(
                    obligation.answered_by(checked.conclusion()),
                    Answer::Answers
                );
                certificates.push(certificate.clone());
            },
            Some(Outcome::Suspended(reason)) => {
                let expected = match index {
                    5 => SuspendReason::Opposed,
                    7 => SuspendReason::NoRule,
                    _ => panic!("obligation {index} suspends with {reason:?}"),
                };
                assert_eq!(reason, expected);
            },
            other => panic!("obligation {index} settles, not {other:?}"),
        }
    }
    assert_eq!(certificates.len(), 6);
    let conclusion = |certificate: &Certificate| {
        let checked = check(&plan, certificate, &quotas).unwrap();
        let Conclusion::Encloses { ref interval, .. } = *checked.conclusion()
        else {
            panic!("an enclosure");
        };
        interval.clone()
    };
    let cosine_enclosure = conclusion(&certificates[0]);
    meets(&cosine_enclosure, &COS_QUARTER_PI);
    assert!(width(&cosine_enclosure) <= power_of_two(Exponent::from(-100_i32)));
    meets(&conclusion(&certificates[1]), &PI);
    assert_eq!(
        conclusion(&certificates[5]),
        NumericInterval::point(Dyadic::ZERO)
    );
    // A run stopped after each of its turns and resumed from its checkpoint
    // certifies the cosine as the unbroken run does.
    let single = [obligations[0]];
    let mut unbroken = Dovetail::new(&plan, single, quantum, quotas);
    let whole = unbroken.run(ample, Rounds::from(4096_u64), || false);
    let Some(Outcome::Certified(whole)) = whole.outcome(Position::from(0))
    else {
        panic!("the cosine is certified");
    };
    let whole = whole.clone();
    assert!(whole.steps().len() > 4, "the cosine needs a second attempt");
    for stop in 1 .. whole.steps().len() {
        let mut first = Dovetail::new(&plan, single, quantum, quotas);
        let bytes = first
            .run(ample, Rounds::from(u64::try_from(stop).unwrap()), || false)
            .checkpoint();
        let mut resumed = Dovetail::resume(&plan, EncodedCheckpoint::from(&bytes)).unwrap();
        let report = resumed.run(ample, Rounds::from(4096_u64), || false);
        assert_eq!(
            report.outcome(Position::from(0)),
            Some(Outcome::Certified(&whole)),
            "resumed after {stop} turns"
        );
    }
}
