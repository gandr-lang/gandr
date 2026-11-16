//! The recurrence node: the validation of its ratio, its rule, the plans of
//! `exp` and `log` over it, and the replay of their certificates.

use core::cmp::Ordering;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Answer;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CertificateCheck;
use gandr_theory_exact_reals::CertificateRefusal;
use gandr_theory_exact_reals::Check;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Coefficient;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::Containment;
use gandr_theory_exact_reals::DecodeError;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::FormatVersion;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanError;
use gandr_theory_exact_reals::Polynomial;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Recurrence;
use gandr_theory_exact_reals::Refusal;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::Site;
use gandr_theory_exact_reals::Squarings;
use gandr_theory_exact_reals::Step;
use gandr_theory_exact_reals::StepId;
use gandr_theory_exact_reals::StepSite;
use gandr_theory_exact_reals::Terms;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::approximate;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::series;
use gandr_theory_exact_reals::series_after;
use gandr_theory_exact_reals::validate;

use crate::oracle::Rational;

/// The polynomial whose coefficients are `coefficients`, the constant first.
///
/// # Specification
/// trivial.
fn polynomial(coefficients: &[Coefficient]) -> Polynomial
{
    return Polynomial::try_from(coefficients.to_vec()).unwrap();
}

/// The ratio of `exp`: `1 / (n + 1)`.
///
/// # Specification
/// trivial.
fn exp_ratio() -> (Polynomial, Polynomial)
{
    return (
        polynomial(&[1].map(Coefficient::from)),
        polynomial(&[1, 1].map(Coefficient::from)),
    );
}

/// The ratio of `log`: `(2n + 1) / (2n + 3)`.
///
/// # Specification
/// trivial.
fn log_ratio() -> (Polynomial, Polynomial)
{
    return (
        polynomial(&[1, 2].map(Coefficient::from)),
        polynomial(&[3, 2].map(Coefficient::from)),
    );
}

/// The evidence that the quotient of the plan of `log` names.
///
/// # Specification
/// trivial.
fn nonzero() -> Evidence
{
    return Evidence::from(1_u32);
}

/// The table that registers the evidence of the plan of `log`.
///
/// # Specification
/// trivial.
fn table() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    table.register(nonzero(), Judgement::NonZero).unwrap();
    return table;
}

/// The plan rooted at `root`, admitted.
///
/// # Specification
/// trivial.
fn admitted(
    builder: PlanBuilder,
    root: RealId,
) -> ValidatedPlan
{
    return admit(
        builder.finish(Root::Real(root)).unwrap(),
        &Quotas::default(),
        &table(),
    )
    .unwrap();
}

/// The refusal of the plan rooted at `root`.
///
/// # Specification
/// trivial.
fn refused(
    builder: PlanBuilder,
    root: RealId,
) -> Refusal
{
    return admit(
        builder.finish(Root::Real(root)).unwrap(),
        &Quotas::default(),
        &table(),
    )
    .unwrap_err();
}

/// The enclosure of the root of `plan` that the machine certifies to
/// `2^width`, after the checker replays its certificate.
///
/// # Specification
/// trivial.
fn certified(
    plan: &ValidatedPlan,
    width: Exponent,
) -> NumericInterval
{
    let quotas = CheckerQuotas::default();
    let root = plan.plan().root().node();
    let obligation = Obligation::new(plan, root, Demand::Encloses { width }).unwrap();
    let quantum = Quantum::from(NonZeroU32::new(1).unwrap());
    let mut dovetail = Dovetail::new(plan, [obligation], quantum, quotas);
    let report = dovetail.run(Budget::from(u64::MAX), Rounds::from(4096_u64), || false);
    let Some(Outcome::Certified(certificate)) = report.outcome(Position::from(0_usize))
    else {
        panic!(
            "the root is certified, not {:?}",
            report.outcome(Position::from(0_usize))
        );
    };
    let checked = check(plan, certificate, &quotas).unwrap();
    assert_eq!(
        obligation.answered_by(checked.conclusion()),
        Answer::Answers
    );
    let Conclusion::Encloses { ref interval, .. } = *checked.conclusion()
    else {
        panic!("an enclosure");
    };
    return interval.clone();
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
    return (lower.clone(), upper.clone());
}

/// The rational `2^exponent`.
///
/// # Specification
/// trivial.
fn power_of_two(exponent: Exponent) -> Rational
{
    return Rational::of(&Dyadic::new(num_bigint::BigInt::from(1_u8), exponent).unwrap());
}

/// Assert that `interval` holds each point of the bracket from `low` to
/// `low + tail`, so it holds the real that the bracket holds, and that it is
/// at most `2^width` wide.
///
/// # Specification
/// trivial.
fn holds(
    interval: &NumericInterval,
    (low, tail): (&Rational, &Rational),
    width: Exponent,
)
{
    assert_eq!(low.within(interval), Containment::Contains, "{interval:?}");
    assert_eq!(
        low.plus(tail).within(interval),
        Containment::Contains,
        "{interval:?}"
    );
    let (lower, upper) = ends(interval);
    let span = Rational::of(&upper).minus(&Rational::of(&lower));
    assert_ne!(
        span.order(&power_of_two(width)),
        Ordering::Greater,
        "{interval:?}"
    );
}

/// `e = Σ 1/k!` to `k = 200`, and the bound `2 / 201!` on the rest.
///
/// # Specification
/// trivial.
fn euler() -> (Rational, Rational)
{
    let natural = |value: u32| Rational::of(&Dyadic::from(i64::from(value)));
    let mut term = natural(1);
    let mut sum = term.clone();
    for k in 1_u32 ..= 201 {
        term = term.quotient(&natural(k)).unwrap();
        if k <= 200 {
            sum = sum.plus(&term);
        }
    }
    return (sum, term.plus(&term));
}

/// `log 2 = Σ 1/(k · 2^k)` to `k = 1100`, and the bound `1 / (1101 · 2^1100)`
/// on the rest. The series is not the series of the plan of `log`.
///
/// # Specification
/// trivial.
fn log_two() -> (Rational, Rational)
{
    let natural = |value: u32| Rational::of(&Dyadic::from(i64::from(value)));
    let half = natural(1).quotient(&natural(2)).unwrap();
    let mut power = natural(1);
    let mut sum = Rational::of(&Dyadic::ZERO);
    for k in 1_u32 ..= 1100 {
        power = power.times(&half);
        sum = sum.plus(&power.quotient(&natural(k)).unwrap());
    }
    return (sum, power.quotient(&natural(1101)).unwrap());
}

#[test]
fn a_malformed_ratio_is_refused_by_name()
{
    let coefficients = |values: &[i32]| {
        values
            .iter()
            .copied()
            .map(Coefficient::from)
            .collect::<Vec<_>>()
    };
    // At the builder: no coefficients, six, and a zero leading coefficient.
    for list in [&[][..], &[1_i32, 1_i32, 1_i32, 1_i32, 1_i32, 1_i32], &[
        1_i32, 0_i32,
    ]] {
        assert_eq!(
            Polynomial::try_from(coefficients(list)),
            Err(PlanError::Polynomial)
        );
    }
    // In the bytes: the series of `exp` at one ends with its denominator
    // `1 + n`, its count and then its two coefficients.
    let mut builder = PlanBuilder::new();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let (numerator, denominator) = exp_ratio();
    let node = builder
        .real(Real::Recurrence(Recurrence {
            argument: one,
            numerator,
            denominator,
        }))
        .unwrap();
    let bytes: Vec<u8> = builder.finish(Root::Real(node)).unwrap().encode().into();
    let length = bytes.len();
    let mut zeroed = bytes.clone();
    zeroed[length.checked_sub(4).unwrap() ..].copy_from_slice(&0_i32.to_le_bytes());
    let mut long = bytes.clone();
    long[length.checked_sub(12).unwrap() .. length.checked_sub(8).unwrap()]
        .copy_from_slice(&6_u32.to_le_bytes());
    for corrupt in [zeroed, long] {
        let refusal = validate(
            EncodedPlan::from(corrupt.as_slice()),
            &Quotas::default(),
            &table(),
        )
        .unwrap_err();
        assert_eq!(refusal.check, Check::Decode(DecodeError::Polynomial));
    }
    assert!(
        validate(
            EncodedPlan::from(bytes.as_slice()),
            &Quotas::default(),
            &table()
        )
        .is_ok()
    );
    // At validation: a numerator of the higher degree, and a denominator that
    // vanishes at zero, at one or at twelve.
    let ratio = |numerator: &[i32], denominator: &[i32]| {
        let mut builder = PlanBuilder::new();
        let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
        let node = builder
            .real(Real::Recurrence(Recurrence {
                argument: one,
                numerator: Polynomial::try_from(coefficients(numerator)).unwrap(),
                denominator: Polynomial::try_from(coefficients(denominator)).unwrap(),
            }))
            .unwrap();
        return (builder, node);
    };
    let (builder, node) = ratio(&[1_i32, 1_i32], &[2_i32]);
    let refusal = refused(builder, node);
    assert_eq!(refusal.check, Check::RatioDegree);
    assert!(matches!(refusal.site, Site::Node(_)));
    for denominator in [
        &[0_i32, 1_i32][..],
        &[-1_i32, 1_i32],
        &[12_i32, -13_i32, 1_i32],
        &[-12_i32, 1_i32],
    ] {
        let (builder, node) = ratio(&[1_i32], denominator);
        assert_eq!(
            refused(builder, node).check,
            Check::RatioRoot,
            "{denominator:?}"
        );
    }
    // The ratios of `exp`, of `log` and of the cosine are admitted.
    for (numerator, denominator) in [
        (&[1_i32][..], &[1_i32, 1_i32][..]),
        (&[1_i32, 2_i32], &[3_i32, 2_i32]),
        (&[-1_i32], &[2_i32, 6_i32, 4_i32]),
        (&[1_i32], &[12_i32, 1_i32, 1_i32]),
    ] {
        let (builder, node) = ratio(numerator, denominator);
        admitted(builder, node);
    }
}

#[test]
fn exp_of_one_encloses_e_and_its_certificate_replays()
{
    let width = Exponent::from(-1000_i32);
    let euler = euler();
    // With no squaring, and with four: the series at `1/16` raised to the
    // sixteenth power.
    for squarings in [0_u32, 4] {
        let mut builder = PlanBuilder::new();
        let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
        let root = builder.exp(one, Squarings::from(squarings)).unwrap();
        let plan = admitted(builder, root);
        holds(&certified(&plan, width), (&euler.0, &euler.1), width);
    }
    // A plan of `exp` past 31 squarings has no power.
    let mut builder = PlanBuilder::new();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    assert_eq!(
        builder.exp(one, Squarings::from(32_u32)),
        Err(PlanError::Squarings)
    );
}

#[test]
fn log_of_two_encloses_its_digits_and_its_certificate_replays()
{
    let width = Exponent::from(-1000_i32);
    let mut builder = PlanBuilder::new();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let root = builder.log(two, nonzero()).unwrap();
    let plan = admitted(builder, root);
    let log_two = log_two();
    holds(&certified(&plan, width), (&log_two.0, &log_two.1), width);
}

#[test]
fn exp_of_log_three_holds_three()
{
    let three = Rational::of(&Dyadic::from(3_i64));
    let zero = Rational::of(&Dyadic::ZERO);
    for squarings in [0_u32, 2] {
        let mut builder = PlanBuilder::new();
        let argument = builder.real(Real::Constant(Dyadic::from(3_i64))).unwrap();
        let logarithm = builder.log(argument, nonzero()).unwrap();
        let root = builder.exp(logarithm, Squarings::from(squarings)).unwrap();
        let plan = admitted(builder, root);
        // The approximation pass at 256 bits, and the machine's certificate.
        let pass = approximate(&plan, Precision::try_from(256_u32).unwrap());
        let enclosure = pass.enclosure(plan.plan().root().node()).unwrap();
        assert_eq!(
            three.within(enclosure),
            Containment::Contains,
            "{enclosure:?}"
        );
        let width = Exponent::from(-200_i32);
        holds(&certified(&plan, width), (&three, &zero), width);
    }
}

#[test]
fn exp_meets_its_identity_at_each_sign()
{
    let precision = Precision::try_from(256_u32).unwrap();
    let (numerator, denominator) = exp_ratio();
    let ratio = (&numerator, &denominator);
    let point = |mantissa: i64| {
        NumericInterval::point(
            Dyadic::new(num_bigint::BigInt::from(mantissa), Exponent::from(-2_i32)).unwrap(),
        )
    };
    let one = Rational::of(&Dyadic::ONE);
    // `exp x · exp (−x) = 1` for points of each sign: the terms at a negative
    // point alternate.
    for mantissa in [1_i64, 3, 7] {
        let (above, _) = series(&point(mantissa), ratio, precision).unwrap();
        let (below, _) = series(&point(mantissa.checked_neg().unwrap()), ratio, precision).unwrap();
        let product = above.mul(&below, Precision::MAX).unwrap();
        assert_eq!(one.within(&product), Containment::Contains, "{product:?}");
    }
    // Over an argument that holds zero, the enclosure holds the enclosure at
    // each end and at zero.
    let (low, high) = (point(-1), point(1));
    let span =
        NumericInterval::new(low.lower().clone(), high.upper().clone(), low.orientation()).unwrap();
    let (around, _) = series(&span, ratio, precision).unwrap();
    for inner in [low, high, NumericInterval::point(Dyadic::ZERO)] {
        let (at, _) = series(&inner, ratio, precision).unwrap();
        let (lower, upper) = ends(&at);
        assert_eq!(Rational::of(&lower).within(&around), Containment::Contains);
        assert_eq!(Rational::of(&upper).within(&around), Containment::Contains);
    }
}

#[test]
fn a_step_with_no_tail_bound_is_refused_by_name()
{
    let precision = Precision::try_from(128_u32).unwrap();
    let quotas = CheckerQuotas::default();
    let certificate = |steps: Vec<Step>| Certificate::new(FormatVersion::CURRENT, steps);
    let refused_at = |step: u32, check: CertificateCheck| CertificateRefusal {
        site: StepSite::Step(StepId::from(step)),
        check,
    };
    // The series of `exp` at one.
    let mut builder = PlanBuilder::new();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let (numerator, denominator) = exp_ratio();
    let root = builder
        .real(Real::Recurrence(Recurrence {
            argument: one,
            numerator: numerator.clone(),
            denominator: denominator.clone(),
        }))
        .unwrap();
    let plan = admitted(builder, root);
    let (constant, node) = (NodeId::from(0_u32), plan.plan().root().node());
    let step = |terms: Terms| Step::Recurrence {
        real: node,
        argument: StepId::from(0_u32),
        terms,
        precision,
    };
    let with = |terms: Terms| certificate(vec![Step::Constant { real: constant }, step(terms)]);
    // The writer's count replays to the writer's enclosure.
    let point = NumericInterval::point(Dyadic::ONE);
    let (enclosure, terms) = series(&point, (&numerator, &denominator), precision).unwrap();
    let checked = check(&plan, &with(terms), &quotas).unwrap();
    assert_eq!(*checked.conclusion(), Conclusion::Encloses {
        real: node,
        interval: enclosure.clone(),
    });
    assert_eq!(
        series_after(&point, (&numerator, &denominator), terms, precision),
        Ok(enclosure)
    );
    // No term, and one term after which the ratio bound reaches one.
    for count in [0_u32, 1] {
        assert_eq!(
            check(&plan, &with(Terms::from(count)), &quotas).err(),
            Some(refused_at(1, CertificateCheck::Tail))
        );
    }
    // A count past the term quota.
    let past = Terms::from(u32::from(Terms::MAX).checked_add(1).unwrap());
    assert_eq!(
        check(&plan, &with(past), &quotas).err(),
        Some(refused_at(1, CertificateCheck::TermQuota))
    );
    // A step that names another node.
    let wrong = certificate(vec![Step::Constant { real: constant }, Step::Recurrence {
        real: constant,
        argument: StepId::from(0_u32),
        terms,
        precision,
    }]);
    assert_eq!(
        check(&plan, &wrong, &quotas).err(),
        Some(refused_at(1, CertificateCheck::WrongNode))
    );
    // The series of `log` at two lies past its radius of convergence, so no
    // count bounds its tail, and the approximation pass gives the whole line.
    let mut builder = PlanBuilder::new();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let (numerator, denominator) = log_ratio();
    let root = builder
        .real(Real::Recurrence(Recurrence {
            argument: two,
            numerator: numerator.clone(),
            denominator: denominator.clone(),
        }))
        .unwrap();
    let plan = admitted(builder, root);
    let node = plan.plan().root().node();
    let divergent = certificate(vec![Step::Constant { real: constant }, Step::Recurrence {
        real: node,
        argument: StepId::from(0_u32),
        terms: Terms::from(100_u32),
        precision,
    }]);
    assert_eq!(
        check(&plan, &divergent, &quotas).err(),
        Some(refused_at(1, CertificateCheck::Tail))
    );
    let point = NumericInterval::point(Dyadic::from(2_i64));
    assert_eq!(
        series(&point, (&numerator, &denominator), precision),
        Err(CertificateCheck::Tail)
    );
    let pass = approximate(&plan, precision);
    assert_eq!(*pass.enclosure(node).unwrap(), NumericInterval::whole());
}

#[test]
fn a_divisor_that_reaches_zero_is_refused_by_name()
{
    let precision = Precision::try_from(64_u32).unwrap();
    let quotas = CheckerQuotas::default();
    let mut builder = PlanBuilder::new();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).unwrap();
    let root = builder
        .real(Real::Div {
            numerator: one,
            denominator: zero,
            nonzero: nonzero(),
        })
        .unwrap();
    let plan = admitted(builder, root);
    let node = plan.plan().root().node();
    let steps = vec![
        Step::Constant {
            real: NodeId::from(0_u32),
        },
        Step::Constant {
            real: NodeId::from(1_u32),
        },
        Step::Quotient {
            real: node,
            numerator: StepId::from(0_u32),
            denominator: StepId::from(1_u32),
            precision,
        },
    ];
    assert_eq!(
        check(
            &plan,
            &Certificate::new(FormatVersion::CURRENT, steps),
            &quotas
        )
        .err(),
        Some(CertificateRefusal {
            site: StepSite::Step(StepId::from(2_u32)),
            check: CertificateCheck::ZeroDivisor,
        })
    );
}
