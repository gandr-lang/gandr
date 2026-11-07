//! The exemplar of the stage-A gate: the square root of two refined to
//! widths from `2^-8` to `2^-256`, each certificate replayed, with a forged
//! cut, corrupted certificates and malformed bytes each refused by name.
//!
//! The rational oracle checks each replayed enclosure independently: its
//! lower end squares below the radicand, and its upper end squares above it.

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CertificateCheck;
use gandr_theory_exact_reals::CertificateRefusal;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::Cut;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::DecodeError;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedCertificate;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::FormatVersion;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Side;
use gandr_theory_exact_reals::Step;
use gandr_theory_exact_reals::StepCount;
use gandr_theory_exact_reals::StepId;
use gandr_theory_exact_reals::StepSite;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::refine;
use gandr_theory_exact_reals::square_root;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;
use proptest::prelude::*;

use crate::oracle::Rational;

/// The laws evidence of every registered cut here.
///
/// # Specification
/// trivial.
fn laws() -> Evidence
{
    return Evidence::from(0_u32);
}

/// Admit a plan rooted at `root`, whose cuts name [`laws`].
///
/// # Specification
/// trivial.
fn admitted(
    builder: PlanBuilder,
    root: Root,
) -> ValidatedPlan
{
    let mut table = EvidenceTable::new();
    table.register(laws(), Judgement::CutLaws).unwrap();
    return admit(builder.finish(root).unwrap(), &Quotas::default(), &table).unwrap();
}

/// The validated plan of the square root of two, and the cut's position in
/// it.
///
/// # Specification
/// trivial.
fn root_two() -> (ValidatedPlan, NodeId)
{
    let mut builder = PlanBuilder::new();
    let cut = square_root_of_two(&mut builder, laws()).unwrap();
    let plan = admitted(builder, Root::Real(cut));
    let node = plan.plan().root().node();
    return (plan, node);
}

/// The dyadic `2^exponent`.
///
/// # Specification
/// trivial.
fn power_of_two(exponent: Exponent) -> Dyadic
{
    return Dyadic::new(BigInt::from(1_u8), exponent).unwrap();
}

/// The checker's refusal at step `step` with `check`.
///
/// # Specification
/// trivial.
fn at(
    step: StepId,
    check: CertificateCheck,
) -> CertificateRefusal
{
    return CertificateRefusal {
        site: StepSite::Step(step),
        check,
    };
}

#[test]
fn the_square_root_of_two_refines_and_replays_at_each_width()
{
    let (plan, cut) = root_two();
    let quotas = CheckerQuotas::default();
    let two = Rational::of(&Dyadic::from(2_i64));
    for bits in [8_i32, 16_i32, 32_i32, 64_i32, 128_i32, 256_i32] {
        let width = Exponent::from(bits.checked_neg().unwrap());
        let certificate = refine(&plan, cut, width, &quotas).unwrap();
        // The hull has width one, so each halving is one step after the
        // witnesses of the hull.
        assert_eq!(
            usize::from(certificate.step_count()),
            usize::try_from(bits).unwrap().checked_add(1).unwrap()
        );
        let checked = check(&plan, &certificate, &quotas).unwrap();
        let Conclusion::Encloses { real, ref interval } = *checked.conclusion()
        else {
            panic!("a refinement encloses its cut");
        };
        assert_eq!(real, cut);
        let (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) =
            (&interval.lower().endpoint, &interval.upper().endpoint)
        else {
            panic!("a refinement has finite ends");
        };
        let (lower, upper) = (Rational::of(lower), Rational::of(upper));
        assert_eq!(lower.times(&lower).order(&two), core::cmp::Ordering::Less);
        assert_eq!(
            upper.times(&upper).order(&two),
            core::cmp::Ordering::Greater
        );
        let gap = upper.minus(&lower);
        assert_ne!(
            gap.order(&Rational::of(&power_of_two(width))),
            core::cmp::Ordering::Greater,
            "{bits} bits"
        );
    }
}

#[test]
fn the_first_refinement_step_is_two_steps()
{
    let (plan, cut) = root_two();
    let certificate = refine(
        &plan,
        cut,
        Exponent::from(-1_i32),
        &CheckerQuotas::default(),
    )
    .unwrap();
    let three_halves = Dyadic::new(BigInt::from(3_u8), Exponent::from(-1_i32)).unwrap();
    assert_eq!(certificate.steps(), [
        Step::Witnesses {
            cut,
            lower: Dyadic::ONE,
            upper: Dyadic::from(2_i64),
        },
        Step::Split {
            premise: StepId::from(0_u32),
            point: three_halves,
            side: Side::Upper,
        },
    ]);
    // The header takes 14 bytes, the witnesses 31 and the split 19.
    assert_eq!(certificate.encode().as_ref().len(), 64);
}

#[test]
fn a_forged_cut_is_refused()
{
    // A cut whose upper cut names three where its lower cut names two: no
    // registered schema states its laws, though its evidence names them.
    let mut builder = PlanBuilder::new();
    let x = builder.real(Real::Bound(DeBruijn::from(0_u32))).unwrap();
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).unwrap();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let three = builder.real(Real::Constant(Dyadic::from(3_i64))).unwrap();
    let square = builder.real(Real::Mul(x, x)).unwrap();
    let negative = builder.open(Open::Less(x, zero)).unwrap();
    let small = builder.open(Open::Less(square, two)).unwrap();
    let lower = builder.open(Open::Join(negative, small)).unwrap();
    let positive = builder.open(Open::Less(zero, x)).unwrap();
    let large = builder.open(Open::Less(three, square)).unwrap();
    let upper = builder.open(Open::Meet(positive, large)).unwrap();
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ONE),
        Bound::closed(Dyadic::from(2_i64)),
        Orientation::Proper,
    )
    .unwrap();
    let forged = builder
        .real(Real::Cut(Cut {
            hull,
            lower,
            upper,
            laws: laws(),
        }))
        .unwrap();
    let plan = admitted(builder, Root::Real(forged));
    let cut = plan.plan().root().node();
    let quotas = CheckerQuotas::default();
    assert_eq!(
        refine(&plan, cut, Exponent::from(-8_i32), &quotas),
        Err(CertificateCheck::ForgedCut)
    );
    let certificate = Certificate::new(FormatVersion::CURRENT, vec![Step::Witnesses {
        cut,
        lower: Dyadic::ONE,
        upper: Dyadic::from(2_i64),
    }]);
    assert_eq!(
        check(&plan, &certificate, &quotas),
        Err(at(StepId::from(0_u32), CertificateCheck::ForgedCut))
    );
}

#[test]
fn corrupted_certificates_are_refused_by_name()
{
    let (plan, cut) = root_two();
    let quotas = CheckerQuotas::default();
    let sound = refine(&plan, cut, Exponent::from(-4_i32), &quotas).unwrap();
    assert!(check(&plan, &sound, &quotas).is_ok());
    let half = |mantissa: u8| Dyadic::new(BigInt::from(mantissa), Exponent::from(-1_i32)).unwrap();
    let edited = |index: usize, step: Step| {
        let mut steps = sound.steps().to_vec();
        steps[index] = step;
        Certificate::new(FormatVersion::CURRENT, steps)
    };
    let first = StepId::from(0_u32);
    let second = StepId::from(1_u32);
    let corruptions = [
        // A lower witness above the root, and an upper witness below it.
        (
            edited(0, Step::Witnesses {
                cut,
                lower: half(3),
                upper: Dyadic::from(2_i64),
            }),
            at(first, CertificateCheck::NotLower),
        ),
        (
            edited(0, Step::Witnesses {
                cut,
                lower: Dyadic::ONE,
                upper: Dyadic::ONE,
            }),
            at(first, CertificateCheck::NotUpper),
        ),
        // A split that claims the wrong side, and one outside its enclosure.
        (
            edited(1, Step::Split {
                premise: first,
                point: half(3),
                side: Side::Lower,
            }),
            at(second, CertificateCheck::NotLower),
        ),
        (
            edited(1, Step::Split {
                premise: first,
                point: Dyadic::from(2_i64),
                side: Side::Upper,
            }),
            at(second, CertificateCheck::OutsideEnclosure),
        ),
        // A premise at or after its own step.
        (
            edited(1, Step::Split {
                premise: second,
                point: half(3),
                side: Side::Upper,
            }),
            at(second, CertificateCheck::ForwardPremise),
        ),
        // A witnesses step that names a node other than a cut, and a node
        // past the plan.
        (
            edited(0, Step::Witnesses {
                cut: NodeId::from(0_u32),
                lower: Dyadic::ONE,
                upper: Dyadic::from(2_i64),
            }),
            at(first, CertificateCheck::WrongNode),
        ),
        (
            edited(0, Step::Witnesses {
                cut: NodeId::from(999_u32),
                lower: Dyadic::ONE,
                upper: Dyadic::from(2_i64),
            }),
            at(first, CertificateCheck::UnknownNode),
        ),
        // A constant step that names the cut.
        (
            edited(1, Step::Constant { real: cut }),
            at(second, CertificateCheck::WrongNode),
        ),
    ];
    for (certificate, refusal) in corruptions {
        assert_eq!(check(&plan, &certificate, &quotas), Err(refusal));
    }
    let mut foreign = sound.steps().to_vec();
    foreign.truncate(1);
    assert_eq!(
        check(
            &plan,
            &Certificate::new(FormatVersion::from(2_u16), foreign),
            &quotas
        ),
        Err(CertificateRefusal {
            site: StepSite::Certificate,
            check: CertificateCheck::Format,
        })
    );
    assert_eq!(
        check(
            &plan,
            &Certificate::new(FormatVersion::CURRENT, Vec::new()),
            &quotas
        ),
        Err(CertificateRefusal {
            site: StepSite::Certificate,
            check: CertificateCheck::Empty,
        })
    );
}

#[test]
fn comparisons_with_the_cut_are_certified()
{
    // `sqrt 2 < 3/2` holds, and `3/2 < sqrt 2` fails.
    let quotas = CheckerQuotas::default();
    let three_halves = Dyadic::new(BigInt::from(3_u8), Exponent::from(-1_i32)).unwrap();
    for flipped in [false, true] {
        let mut builder = PlanBuilder::new();
        let root = square_root_of_two(&mut builder, laws()).unwrap();
        let bound = builder.real(Real::Constant(three_halves.clone())).unwrap();
        let less = if flipped {
            builder.open(Open::Less(bound, root)).unwrap()
        }
        else {
            builder.open(Open::Less(root, bound)).unwrap()
        };
        let plan = admitted(builder, Root::Open(less));
        let less = plan.plan().root().node();
        let Ok(&gandr_theory_exact_reals::Node::Open(Open::Less(first, second))) =
            plan.plan().node(less)
        else {
            panic!("the root is a comparison");
        };
        let (cut, constant) = if flipped {
            (second.node(), first.node())
        }
        else {
            (first.node(), second.node())
        };
        let refinement = refine(&plan, cut, Exponent::from(-4_i32), &quotas).unwrap();
        let mut steps = refinement.steps().to_vec();
        let enclosure = StepId::try_from(steps.len().checked_sub(1).unwrap()).unwrap();
        let point = StepId::try_from(steps.len()).unwrap();
        steps.push(Step::Constant { real: constant });
        let (left, right) = if flipped {
            (point, enclosure)
        }
        else {
            (enclosure, point)
        };
        let holds = Step::Below { less, left, right };
        let fails = Step::NotBelow { less, left, right };
        let (sound, unsound, conclusion) = if flipped {
            (fails, holds, Conclusion::Fails { open: less })
        }
        else {
            (holds, fails, Conclusion::Holds { open: less })
        };
        let mut sound_steps = steps.clone();
        sound_steps.push(sound);
        let checked = check(
            &plan,
            &Certificate::new(FormatVersion::CURRENT, sound_steps),
            &quotas,
        )
        .unwrap();
        assert_eq!(*checked.conclusion(), conclusion);
        let last = StepId::try_from(steps.len()).unwrap();
        steps.push(unsound);
        assert_eq!(
            check(
                &plan,
                &Certificate::new(FormatVersion::CURRENT, steps),
                &quotas
            ),
            Err(at(last, CertificateCheck::NotSeparated))
        );
    }
}

#[test]
fn quotas_bound_the_checker()
{
    let (plan, cut) = root_two();
    let width = Exponent::from(-16_i32);
    let certificate = refine(&plan, cut, width, &CheckerQuotas::default()).unwrap();
    let steps = certificate.step_count();
    let tight = CheckerQuotas {
        steps,
        ..CheckerQuotas::default()
    };
    assert!(check(&plan, &certificate, &tight).is_ok());
    let short = CheckerQuotas {
        steps: StepCount::from(usize::from(steps).checked_sub(1).unwrap()),
        ..CheckerQuotas::default()
    };
    assert_eq!(
        check(&plan, &certificate, &short),
        Err(CertificateRefusal {
            site: StepSite::Certificate,
            check: CertificateCheck::StepQuota,
        })
    );
    assert_eq!(
        refine(&plan, cut, width, &short),
        Err(CertificateCheck::StepQuota)
    );
    // The split points of a width of 2^-16 have at most 17 bits.
    let narrow = CheckerQuotas {
        width: gandr_theory_exact_reals::BitWidth::from(8_u64),
        ..CheckerQuotas::default()
    };
    let Err(refusal) = check(&plan, &certificate, &narrow)
    else {
        panic!("a point past the width quota is refused");
    };
    assert_eq!(refusal.check, CertificateCheck::WidthQuota);
}

#[test]
fn certificates_round_trip_through_their_canonical_bytes()
{
    let (plan, cut) = root_two();
    let quotas = CheckerQuotas::default();
    let mut steps = refine(&plan, cut, Exponent::from(-64_i32), &quotas)
        .unwrap()
        .steps()
        .to_vec();
    steps.push(Step::Constant { real: cut });
    steps.push(Step::Below {
        less: cut,
        left: StepId::from(0_u32),
        right: StepId::from(1_u32),
    });
    steps.push(Step::NotBelow {
        less: cut,
        left: StepId::from(1_u32),
        right: StepId::from(0_u32),
    });
    let certificate = Certificate::new(FormatVersion::CURRENT, steps);
    let bytes = certificate.encode();
    assert_eq!(
        Certificate::decode(EncodedCertificate::from(&bytes)),
        Ok(certificate)
    );
}

#[test]
fn malformed_certificate_bytes_are_refused_by_name()
{
    let (plan, cut) = root_two();
    let bytes: Vec<u8> = refine(
        &plan,
        cut,
        Exponent::from(-1_i32),
        &CheckerQuotas::default(),
    )
    .unwrap()
    .encode()
    .into();
    let decode = |bytes: &[u8]| Certificate::decode(EncodedCertificate::from(bytes));
    assert!(decode(&bytes).is_ok());
    let mut magic = bytes.clone();
    magic[3] = b'P';
    assert_eq!(decode(&magic), Err(DecodeError::Magic));
    let mut version = bytes.clone();
    version[4] = 2;
    assert_eq!(decode(&version), Err(DecodeError::Version));
    let mut empty = bytes[.. 6].to_vec();
    empty.extend_from_slice(&0_u64.to_le_bytes());
    assert_eq!(decode(&empty), Err(DecodeError::Empty));
    for end in 0 .. bytes.len() {
        assert!(decode(&bytes[.. end]).is_err(), "the prefix of {end} bytes");
    }
    let mut kind = bytes.clone();
    kind[14] = 0x41;
    assert_eq!(decode(&kind), Err(DecodeError::UnknownKind));
    let mut side = bytes.clone();
    let last = side.len().checked_sub(1).unwrap();
    side[last] = 0x07;
    assert_eq!(decode(&side), Err(DecodeError::UnknownKind));
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(decode(&trailing), Err(DecodeError::TrailingBytes));
}

#[test]
fn failures_render_distinct_phrases()
{
    let checks = [
        CertificateCheck::Format,
        CertificateCheck::Empty,
        CertificateCheck::StepQuota,
        CertificateCheck::WidthQuota,
        CertificateCheck::UnknownNode,
        CertificateCheck::WrongNode,
        CertificateCheck::ForgedCut,
        CertificateCheck::ForwardPremise,
        CertificateCheck::PremiseConclusion,
        CertificateCheck::NotLower,
        CertificateCheck::NotUpper,
        CertificateCheck::OutsideEnclosure,
        CertificateCheck::NotSeparated,
        CertificateCheck::Reversed,
        CertificateCheck::Hypothesis,
        CertificateCheck::Hypothetical,
        CertificateCheck::OutsideDomain,
        CertificateCheck::Gap,
        CertificateCheck::Modality,
        CertificateCheck::TermQuota,
        CertificateCheck::Tail,
        CertificateCheck::ZeroDivisor,
    ];
    let lines: Vec<String> = checks.iter().map(ToString::to_string).collect();
    for (index, line) in lines.iter().enumerate() {
        assert!(
            !line.is_empty() && !line.contains('\n'),
            "not one line: {line}"
        );
        assert!(
            lines
                .iter()
                .skip(index.checked_add(1).unwrap())
                .all(|other| other != line),
            "a repeated line: {line}"
        );
    }
    let whole = CertificateRefusal {
        site: StepSite::Certificate,
        check: CertificateCheck::Empty,
    };
    let step = at(StepId::from(3_u32), CertificateCheck::Empty);
    assert_ne!(whole.to_string(), step.to_string());
}

/// The validated plan of the square root of `radicand`, with the hull from
/// zero to `radicand + 1`, and the cut's position.
///
/// # Specification
/// trivial.
fn root_of(radicand: &Dyadic) -> (ValidatedPlan, NodeId)
{
    let upper = radicand
        .add(
            &Dyadic::ONE,
            gandr_theory_exact_reals::Precision::MAX,
            gandr_theory_exact_reals::Rounding::Floor,
        )
        .unwrap()
        .into_value();
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ZERO),
        Bound::closed(upper),
        Orientation::Proper,
    )
    .unwrap();
    let mut builder = PlanBuilder::new();
    let cut: RealId = square_root(&mut builder, radicand.clone(), hull, laws()).unwrap();
    let plan = admitted(builder, Root::Real(cut));
    let node = plan.plan().root().node();
    return (plan, node);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// A refinement of a generated radicand to a generated width replays,
    /// encloses the root by the oracle, and round trips through its bytes.
    #[test]
    fn refinement_holds_for_generated_radicands(mantissa in 1_u32 ..= 100_000, exponent in -12_i32 ..= 12_i32, bits in 1_i32 ..= 96_i32) {
        let radicand = Dyadic::new(BigInt::from(mantissa), Exponent::from(exponent)).unwrap();
        let (plan, cut) = root_of(&radicand);
        let quotas = CheckerQuotas::default();
        let width = Exponent::from(bits.checked_neg().unwrap());
        let certificate = refine(&plan, cut, width, &quotas).unwrap();
        let checked = check(&plan, &certificate, &quotas).unwrap();
        let Conclusion::Encloses { ref interval, .. } = *checked.conclusion() else {
            panic!("a refinement encloses its cut");
        };
        let (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) = (&interval.lower().endpoint, &interval.upper().endpoint) else {
            panic!("a refinement has finite ends");
        };
        let c = Rational::of(&radicand);
        let (lower, upper) = (Rational::of(lower), Rational::of(upper));
        prop_assert!(lower.order(&Rational::of(&Dyadic::ZERO)) == core::cmp::Ordering::Less || lower.times(&lower).order(&c) == core::cmp::Ordering::Less);
        prop_assert_eq!(upper.times(&upper).order(&c), core::cmp::Ordering::Greater);
        prop_assert_ne!(upper.minus(&lower).order(&Rational::of(&power_of_two(width))), core::cmp::Ordering::Greater);
        let bytes = certificate.encode();
        prop_assert_eq!(Certificate::decode(EncodedCertificate::from(&bytes)), Ok(certificate));
    }
}
