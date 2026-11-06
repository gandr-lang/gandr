//! Bounded quantifiers over dyadic intervals: a cover of pieces certifies a
//! universal and a witness an existential, each corruption of their
//! certificates is refused by name, the machine settles each quantified form
//! or suspends it by name, generated formulas settle to certificates that
//! replay and agree with exact evaluation, and a search resumes from its
//! checkpoint.

use core::num::NonZeroU32;

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CertificateCheck;
use gandr_theory_exact_reals::CertificateRefusal;
use gandr_theory_exact_reals::Check;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Closure;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Domain;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedCertificate;
use gandr_theory_exact_reals::EncodedCheckpoint;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceSlot;
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
use gandr_theory_exact_reals::Quantifier;
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
use gandr_theory_exact_reals::Steps;
use gandr_theory_exact_reals::SuspendReason;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;
use proptest::prelude::*;

/// The laws evidence of every registered cut here.
///
/// # Specification
/// trivial.
fn laws() -> Evidence
{
    return Evidence::from(0_u32);
}

/// The overt evidence of every domain here.
///
/// # Specification
/// trivial.
fn overt() -> Evidence
{
    return Evidence::from(1_u32);
}

/// The compact evidence of every closed domain here.
///
/// # Specification
/// trivial.
fn compact() -> Evidence
{
    return Evidence::from(2_u32);
}

/// The table that registers the three references.
///
/// # Specification
/// trivial.
fn table() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    table.register(laws(), Judgement::CutLaws).unwrap();
    table.register(overt(), Judgement::Overt).unwrap();
    table.register(compact(), Judgement::Compact).unwrap();
    return table;
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
    return Dyadic::new(mantissa, exponent).unwrap();
}

/// `1/2`.
///
/// # Specification
/// trivial.
fn half() -> Dyadic
{
    return dyadic(BigInt::from(1_u8), Exponent::from(-1_i32));
}

/// `3/2`.
///
/// # Specification
/// trivial.
fn three_halves() -> Dyadic
{
    return dyadic(BigInt::from(3_u8), Exponent::from(-1_i32));
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

/// The quantifier of a formula.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Form
{
    /// An existential.
    Exists,
    /// A universal.
    Forall,
}

/// Whether a formula's quantifier has evidence of the other modality.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Dual
{
    /// The quantifier names the domain's other slot.
    Given,
    /// The quantifier names none.
    Absent,
}

/// A formula `Q x ∈ hull. first < second` and the nodes that a certificate
/// names.
struct Formula
{
    /// The admitted plan.
    plan: ValidatedPlan,
    /// The quantifier.
    quantifier: NodeId,
    /// The comparison that the body is.
    less: NodeId,
    /// The bound variable.
    variable: NodeId,
}

/// The formula of `form` over `hull` whose body compares the two operands that
/// `operands` builds from the variable.
///
/// # Specification
/// trivial.
fn formula<Operands>(
    form: Form,
    hull: NumericInterval,
    dual: Dual,
    operands: Operands,
) -> Formula
where
    Operands: FnOnce(&mut PlanBuilder, RealId) -> (RealId, RealId),
{
    let mut builder = PlanBuilder::new();
    let ends_closed =
        hull.lower().closure == Closure::Closed && hull.upper().closure == Closure::Closed;
    let overt_slot = EvidenceSlot::Given(overt());
    let compact_slot = if ends_closed {
        EvidenceSlot::Given(compact())
    }
    else {
        EvidenceSlot::Absent
    };
    let domain = builder
        .domain(Domain::Interval {
            hull,
            overt: overt_slot,
            compact: compact_slot,
        })
        .unwrap();
    let variable = builder.real(Real::Bound(DeBruijn::from(0_u32))).unwrap();
    let (first, second) = operands(&mut builder, variable);
    let less = builder.open(Open::Less(first, second)).unwrap();
    let (evidence, other) = match form {
        Form::Exists => (overt(), compact_slot),
        Form::Forall => (compact(), overt_slot),
    };
    let quantifier = Quantifier {
        domain,
        body: less,
        evidence,
        dual: match dual {
            Dual::Given => other,
            Dual::Absent => EvidenceSlot::Absent,
        },
    };
    let node = builder
        .open(match form {
            Form::Exists => Open::Exists(quantifier),
            Form::Forall => Open::Forall(quantifier),
        })
        .unwrap();
    let plan = admit(
        builder.finish(Root::Open(node)).unwrap(),
        &Quotas::default(),
        &table(),
    )
    .unwrap();
    // The canonical walk numbers the nodes anew, so the ids are read back from
    // the admitted plan.
    let quantifier = find(&plan, |node| {
        matches!(*node, Node::Open(Open::Exists(_) | Open::Forall(_)))
    });
    let Ok(&Node::Open(Open::Exists(read) | Open::Forall(read))) = plan.plan().node(quantifier)
    else {
        panic!("the quantifier is an open node");
    };
    let variable = find(&plan, |node| matches!(*node, Node::Real(Real::Bound(_))));
    return Formula {
        less: read.body.node(),
        plan,
        quantifier,
        variable,
    };
}

/// The first node of `plan` that `wanted` accepts.
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
    let count = usize::from(plan.plan().node_count());
    return (0 .. count)
        .map(|index| NodeId::try_from(index).unwrap())
        .find(|&id| wanted(plan.plan().node(id).unwrap()))
        .unwrap();
}

/// The constant node of `plan` whose value is `value`.
///
/// # Specification
/// trivial.
fn constant_node(
    plan: &ValidatedPlan,
    value: &Dyadic,
) -> NodeId
{
    return find(
        plan,
        |node| matches!(*node, Node::Real(Real::Constant(ref held)) if held == value),
    );
}

/// `forall x ∈ [-1, 1]` or `forall x ∈ [1, 2]` of `0 < x · x` over `hull`,
/// with the nodes of the constant and of the square.
///
/// # Specification
/// trivial.
fn squared(hull: NumericInterval) -> (Formula, NodeId, NodeId)
{
    let formula = formula(Form::Forall, hull, Dual::Absent, |builder, x| {
        let zero = builder.real(Real::Constant(Dyadic::ZERO)).unwrap();
        let square = builder.real(Real::Mul(x, x)).unwrap();
        (zero, square)
    });
    let zero = constant_node(&formula.plan, &Dyadic::ZERO);
    let square = find(&formula.plan, |node| {
        matches!(*node, Node::Real(Real::Mul(..)))
    });
    return (formula, zero, square);
}

/// `forall x ∈ [1, 2]. 0 < x · x`, the try-first of the unit, with the nodes
/// of the constant and of the square.
///
/// # Specification
/// trivial.
fn square() -> (Formula, NodeId, NodeId)
{
    return squared(closed(Dyadic::ONE, Dyadic::from(2_i64)));
}

/// The certificate of `steps` in the current format.
///
/// # Specification
/// trivial.
fn certificate(steps: Vec<Step>) -> Certificate
{
    return Certificate::new(FormatVersion::CURRENT, steps);
}

/// The step at `index`.
///
/// # Specification
/// trivial.
fn at(index: StepId) -> StepId
{
    return index;
}

/// The refusal at the step `index` by `check`.
///
/// # Specification
/// trivial.
fn refused_at(
    index: StepId,
    check: CertificateCheck,
) -> CertificateRefusal
{
    return CertificateRefusal {
        site: StepSite::Step(index),
        check,
    };
}

/// The quantum of `steps` steps.
///
/// # Specification
/// trivial.
fn quantum(steps: Steps) -> Quantum
{
    let steps = u32::try_from(u64::from(steps)).unwrap();
    return Quantum::from(NonZeroU32::new(steps).unwrap());
}

/// The outcome of one obligation of `demand` on the quantifier of `formula`,
/// run to its end within `budget`.
///
/// # Specification
/// trivial.
fn settle(
    formula: &Formula,
    demand: Demand,
    budget: Budget,
) -> Option<Result<Certificate, SuspendReason>>
{
    let obligation = Obligation::new(&formula.plan, formula.quantifier, demand).unwrap();
    let mut dovetail = Dovetail::new(
        &formula.plan,
        [obligation],
        quantum(Steps::from(64_u64)),
        CheckerQuotas::default(),
    );
    let report = dovetail.run(budget, Rounds::from(u64::MAX), || false);
    return match report.outcome(Position::from(0)) {
        Some(Outcome::Certified(certificate)) => Some(Ok(certificate.clone())),
        Some(Outcome::Suspended(reason)) => Some(Err(reason)),
        Some(Outcome::Pending | Outcome::Exhausted | Outcome::Cancelled) | None => None,
    };
}

#[test]
fn a_cover_of_two_pieces_certifies_the_universal()
{
    // The try-first: `0 < x · x` on `[1, 3/2]` and on `[3/2, 2]`.
    let (formula, zero, square) = square();
    let steps = vec![
        Step::Constant { real: zero },
        Step::Variable {
            real: formula.variable,
            lower: Dyadic::ONE,
            upper: three_halves(),
        },
        Step::Product {
            real: square,
            left: StepId::from(1_u32),
            right: StepId::from(1_u32),
        },
        Step::Below {
            less: formula.less,
            left: StepId::from(0_u32),
            right: StepId::from(2_u32),
        },
        Step::Variable {
            real: formula.variable,
            lower: three_halves(),
            upper: Dyadic::from(2_i64),
        },
        Step::Product {
            real: square,
            left: StepId::from(4_u32),
            right: StepId::from(4_u32),
        },
        Step::Below {
            less: formula.less,
            left: StepId::from(0_u32),
            right: StepId::from(5_u32),
        },
        Step::Cover {
            forall: formula.quantifier,
            premises: vec![StepId::from(3_u32), StepId::from(6_u32)],
        },
    ];
    let cover = certificate(steps);
    let checked = check(&formula.plan, &cover, &CheckerQuotas::default()).unwrap();
    assert_eq!(*checked.conclusion(), Conclusion::Holds {
        open: formula.quantifier
    });
    // The certificate round trips through its canonical bytes.
    let bytes = cover.encode();
    assert_eq!(
        Certificate::decode(EncodedCertificate::from(&bytes)).unwrap(),
        cover
    );
}

#[test]
fn each_corruption_of_a_quantifier_certificate_is_refused_by_name()
{
    let (formula, zero, square) = square();
    let quotas = CheckerQuotas::default();
    let piece = |lower: Dyadic, upper: Dyadic, base: StepId| {
        let first = u32::from(base);
        vec![
            Step::Variable {
                real: formula.variable,
                lower,
                upper,
            },
            Step::Product {
                real: square,
                left: StepId::from(first),
                right: StepId::from(first),
            },
            Step::Below {
                less: formula.less,
                left: StepId::from(0_u32),
                right: StepId::from(first.checked_add(1).unwrap()),
            },
        ]
    };
    let two = Dyadic::from(2_i64);
    let constant = Step::Constant { real: zero };
    let lower_piece = piece(Dyadic::ONE, three_halves(), StepId::from(1_u32));
    let refusal = |steps: Vec<Step>| check(&formula.plan, &certificate(steps), &quotas).err();
    let with = |pieces: &[&[Step]], last: Option<Step>| {
        let mut steps = vec![constant.clone()];
        for piece in pieces {
            steps.extend_from_slice(piece);
        }
        steps.extend(last);
        steps
    };
    // A last step under a hypothesis.
    assert_eq!(
        refusal(with(&[&lower_piece], None)),
        Some(refused_at(
            at(StepId::from(3_u32)),
            CertificateCheck::Hypothetical
        ))
    );
    // A cover that stops short of the domain's upper end.
    let cover = |premises: Vec<StepId>| Step::Cover {
        forall: formula.quantifier,
        premises,
    };
    assert_eq!(
        refusal(with(
            &[&lower_piece],
            Some(cover(vec![StepId::from(3_u32)]))
        )),
        Some(refused_at(StepId::from(4_u32), CertificateCheck::Gap))
    );
    // A cover of no piece.
    assert_eq!(
        refusal(with(&[&lower_piece], Some(cover(Vec::new())))),
        Some(refused_at(StepId::from(4_u32), CertificateCheck::Gap))
    );
    // A cover with a gap between its pieces.
    let gapped = piece(
        dyadic(BigInt::from(7_u8), Exponent::from(-2_i32)),
        two.clone(),
        StepId::from(4_u32),
    );
    assert_eq!(
        refusal(with(
            &[&lower_piece, &gapped],
            Some(cover(vec![StepId::from(3_u32), StepId::from(6_u32)]))
        )),
        Some(refused_at(StepId::from(7_u32), CertificateCheck::Gap))
    );
    // A cover whose premise is no conclusion of the body.
    assert_eq!(
        refusal(with(
            &[&lower_piece],
            Some(cover(vec![StepId::from(2_u32)]))
        )),
        Some(refused_at(
            StepId::from(4_u32),
            CertificateCheck::PremiseConclusion
        ))
    );
    // A hypothesis with its lower end above its upper end.
    assert_eq!(
        refusal(vec![Step::Variable {
            real: formula.variable,
            lower: two.clone(),
            upper: Dyadic::ONE,
        }]),
        Some(refused_at(StepId::from(0_u32), CertificateCheck::Reversed))
    );
    // A variable step on a constant.
    assert_eq!(
        refusal(vec![Step::Variable {
            real: zero,
            lower: Dyadic::ONE,
            upper: two.clone(),
        }]),
        Some(refused_at(StepId::from(0_u32), CertificateCheck::WrongNode))
    );
    // A product of two enclosures under different hypotheses.
    let upper_piece = piece(three_halves(), two, StepId::from(4_u32));
    let mut mixed = with(&[&lower_piece, &upper_piece], None);
    mixed.push(Step::Product {
        real: square,
        left: StepId::from(1_u32),
        right: StepId::from(4_u32),
    });
    assert_eq!(
        refusal(mixed),
        Some(refused_at(
            StepId::from(7_u32),
            CertificateCheck::Hypothesis
        ))
    );
    // A sum step that names a product.
    let mut sum = with(&[&lower_piece], None);
    sum[2] = Step::Sum {
        real: square,
        left: StepId::from(1_u32),
        right: StepId::from(1_u32),
    };
    assert_eq!(
        refusal(sum),
        Some(refused_at(StepId::from(2_u32), CertificateCheck::WrongNode))
    );
    // A witness that names a universal.
    assert_eq!(
        refusal(with(
            &[&lower_piece],
            Some(Step::Witness {
                exists: formula.quantifier,
                premise: StepId::from(3_u32),
            })
        )),
        Some(refused_at(StepId::from(4_u32), CertificateCheck::WrongNode))
    );
    // A counterexample to a universal with no evidence of overtness. The
    // premise is the failure of the body, written by hand at the point zero
    // of a wider plan below.
    let negative = formula_with_failure();
    assert_eq!(
        check(&negative.0.plan, &certificate(negative.1), &quotas).err(),
        Some(refused_at(negative.2, CertificateCheck::Modality))
    );
    // A product past the width quota.
    let narrow = CheckerQuotas {
        width: gandr_theory_exact_reals::BitWidth::from(1_u64),
        ..quotas
    };
    let wide = vec![
        constant.clone(),
        Step::Variable {
            real: formula.variable,
            lower: Dyadic::ONE,
            upper: Dyadic::ONE,
        },
        Step::Product {
            real: square,
            left: StepId::from(1_u32),
            right: StepId::from(1_u32),
        },
    ];
    assert_eq!(
        check(&formula.plan, &certificate(wide.clone()), &quotas)
            .err()
            .map(|refusal| refusal.check),
        Some(CertificateCheck::Hypothetical)
    );
    let mut wider = wide;
    wider[1] = Step::Variable {
        real: formula.variable,
        lower: Dyadic::from(3_i64),
        upper: Dyadic::from(3_i64),
    };
    assert_eq!(
        check(&formula.plan, &certificate(wider), &narrow)
            .err()
            .map(|refusal| refusal.check),
        Some(CertificateCheck::WidthQuota)
    );
}

/// `forall x ∈ [-1, 1]. 0 < x · x` with no evidence of overtness, and a
/// certificate that answers it with a counterexample at zero, and the step of
/// the counterexample.
///
/// # Specification
/// trivial.
fn formula_with_failure() -> (Formula, Vec<Step>, StepId)
{
    let (formula, zero, square) = squared(closed(Dyadic::from(-1_i64), Dyadic::ONE));
    let steps = vec![
        Step::Constant { real: zero },
        Step::Variable {
            real: formula.variable,
            lower: Dyadic::ZERO,
            upper: Dyadic::ZERO,
        },
        Step::Product {
            real: square,
            left: StepId::from(1_u32),
            right: StepId::from(1_u32),
        },
        Step::NotBelow {
            less: formula.less,
            left: StepId::from(0_u32),
            right: StepId::from(2_u32),
        },
        Step::Counterexample {
            forall: formula.quantifier,
            premise: StepId::from(3_u32),
        },
    ];
    return (formula, steps, StepId::from(4_u32));
}

#[test]
fn a_witness_at_an_open_end_is_refused()
{
    // `exists x ∈ (0, 1]. x < 2`: a witness on `[0, 1/2]` reaches the open
    // end, and a witness on `[1/2, 1]` lies inside the domain.
    let hull = NumericInterval::new(
        Bound::open(Endpoint::Finite(Dyadic::ZERO)),
        Bound::closed(Dyadic::ONE),
        Orientation::Proper,
    )
    .unwrap();
    let formula = formula(Form::Exists, hull, Dual::Absent, |builder, x| {
        let constant = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
        (x, constant)
    });
    let two = constant_node(&formula.plan, &Dyadic::from(2_i64));
    let witness = |lower: Dyadic, upper: Dyadic| {
        certificate(vec![
            Step::Constant { real: two },
            Step::Variable {
                real: formula.variable,
                lower,
                upper,
            },
            Step::Below {
                less: formula.less,
                left: StepId::from(1_u32),
                right: StepId::from(0_u32),
            },
            Step::Witness {
                exists: formula.quantifier,
                premise: StepId::from(2_u32),
            },
        ])
    };
    let quotas = CheckerQuotas::default();
    assert_eq!(
        check(&formula.plan, &witness(Dyadic::ZERO, half()), &quotas).err(),
        Some(refused_at(
            StepId::from(3_u32),
            CertificateCheck::OutsideDomain
        ))
    );
    assert_eq!(
        *check(&formula.plan, &witness(half(), Dyadic::ONE), &quotas)
            .unwrap()
            .conclusion(),
        Conclusion::Holds {
            open: formula.quantifier
        }
    );
}

#[test]
fn a_quantifier_over_an_unbounded_domain_is_refused()
{
    let mut builder = PlanBuilder::new();
    let ray = NumericInterval::new(
        Bound::open(Endpoint::NegInf),
        Bound::closed(Dyadic::ONE),
        Orientation::Proper,
    )
    .unwrap();
    let domain = builder
        .domain(Domain::Interval {
            hull: ray,
            overt: EvidenceSlot::Given(overt()),
            compact: EvidenceSlot::Absent,
        })
        .unwrap();
    let x = builder.real(Real::Bound(DeBruijn::from(0_u32))).unwrap();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let below = builder.open(Open::Less(x, two)).unwrap();
    let exists = builder
        .open(Open::Exists(Quantifier {
            domain,
            body: below,
            evidence: overt(),
            dual: EvidenceSlot::Absent,
        }))
        .unwrap();
    let refusal = admit(
        builder.finish(Root::Open(exists)).unwrap(),
        &Quotas::default(),
        &table(),
    )
    .err()
    .map(|refusal| refusal.check);
    assert_eq!(refusal, Some(Check::DomainHull));
}

#[test]
fn each_quantified_form_settles_or_suspends_by_name()
{
    let unit = || closed(Dyadic::ZERO, Dyadic::ONE);
    let budget = Budget::from(4096_u64);
    let constant = |value: Dyadic| {
        move |builder: &mut PlanBuilder, x: RealId| {
            let constant = builder.real(Real::Constant(value)).unwrap();
            (x, constant)
        }
    };
    let above = |value: Dyadic| {
        move |builder: &mut PlanBuilder, x: RealId| {
            let constant = builder.real(Real::Constant(value)).unwrap();
            (constant, x)
        }
    };
    let replayed = |formula: &Formula, certificate: &Certificate| {
        check(&formula.plan, certificate, &CheckerQuotas::default())
            .unwrap()
            .conclusion()
            .clone()
    };
    // `forall x ∈ [1, 2]. 0 < x · x` holds, by a cover.
    let (square, ..) = square();
    let cover = settle(&square, Demand::Holds, budget).unwrap().unwrap();
    assert!(matches!(cover.steps().last(), Some(&Step::Cover { .. })));
    assert_eq!(replayed(&square, &cover), Conclusion::Holds {
        open: square.quantifier
    });
    // Its failure has no evidence of overtness to stand on.
    assert_eq!(
        settle(&square, Demand::Fails, budget),
        Some(Err(SuspendReason::NoRule))
    );
    // `exists x ∈ [0, 1]. 1/2 < x` holds, by a witness.
    let exists = formula(Form::Exists, unit(), Dual::Given, above(half()));
    let witness = settle(&exists, Demand::Holds, budget).unwrap().unwrap();
    assert!(matches!(
        witness.steps().last(),
        Some(&Step::Witness { .. })
    ));
    assert_eq!(replayed(&exists, &witness), Conclusion::Holds {
        open: exists.quantifier
    });
    assert_eq!(
        settle(&exists, Demand::Fails, budget),
        Some(Err(SuspendReason::Opposed))
    );
    // `exists x ∈ [0, 1]. 2 < x` fails, by a refutation.
    let never = formula(
        Form::Exists,
        unit(),
        Dual::Given,
        above(Dyadic::from(2_i64)),
    );
    let refutation = settle(&never, Demand::Fails, budget).unwrap().unwrap();
    assert!(matches!(
        refutation.steps().last(),
        Some(&Step::Refutation { .. })
    ));
    assert_eq!(replayed(&never, &refutation), Conclusion::Fails {
        open: never.quantifier
    });
    assert_eq!(
        settle(&never, Demand::Holds, budget),
        Some(Err(SuspendReason::Opposed))
    );
    // `forall x ∈ [0, 1]. x < 1/2` fails, by a counterexample.
    let below = formula(Form::Forall, unit(), Dual::Given, constant(half()));
    let counterexample = settle(&below, Demand::Fails, budget).unwrap().unwrap();
    assert!(matches!(
        counterexample.steps().last(),
        Some(&Step::Counterexample { .. })
    ));
    assert_eq!(replayed(&below, &counterexample), Conclusion::Fails {
        open: below.quantifier
    });
    assert_eq!(
        settle(&below, Demand::Holds, budget),
        Some(Err(SuspendReason::Opposed))
    );
    // `forall x ∈ [0, 1]. 0 < x · x` fails only at zero, where no piece
    // separates: the search spends its budget and never answers false.
    let touching = formula(Form::Forall, unit(), Dual::Given, |builder, x| {
        let zero = builder.real(Real::Constant(Dyadic::ZERO)).unwrap();
        let square = builder.real(Real::Mul(x, x)).unwrap();
        (zero, square)
    });
    assert_eq!(
        settle(&touching, Demand::Holds, Budget::from(512_u64)),
        None
    );
    // A body that reads a cut has no rule yet.
    let cut = formula(Form::Forall, unit(), Dual::Given, |builder, x| {
        let root = square_root_of_two(builder, laws()).unwrap();
        (x, root)
    });
    assert_eq!(
        settle(&cut, Demand::Holds, budget),
        Some(Err(SuspendReason::NoRule))
    );
}

#[test]
fn a_search_resumes_from_its_checkpoint()
{
    // `forall x ∈ [0, 1]. 1/2 < x · x - x + 1` needs several pieces near the
    // minimum at `1/2`.
    let formula = formula(
        Form::Forall,
        closed(Dyadic::ZERO, Dyadic::ONE),
        Dual::Given,
        |builder, x| {
            let half = builder.real(Real::Constant(half())).unwrap();
            let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
            let square = builder.real(Real::Mul(x, x)).unwrap();
            let difference = builder.real(Real::Sub(square, x)).unwrap();
            let sum = builder.real(Real::Add(difference, one)).unwrap();
            (half, sum)
        },
    );
    let obligation = Obligation::new(&formula.plan, formula.quantifier, Demand::Holds).unwrap();
    let quotas = CheckerQuotas::default();
    let run = |dovetail: &mut Dovetail<&ValidatedPlan>| match dovetail
        .run(Budget::from(u64::MAX), Rounds::from(u64::MAX), || false)
        .outcome(Position::from(0))
    {
        Some(Outcome::Certified(certificate)) => certificate.clone(),
        other => panic!("the search settles: {other:?}"),
    };
    let mut unbroken = Dovetail::new(
        &formula.plan,
        [obligation],
        quantum(Steps::from(1_u64)),
        quotas,
    );
    let whole = run(&mut unbroken);
    let total = u64::try_from(usize::from(whole.step_count())).unwrap();
    assert!(total > 8, "the search visits several pieces");
    for stop in 1 .. total {
        let mut stopped = Dovetail::new(
            &formula.plan,
            [obligation],
            quantum(Steps::from(1_u64)),
            quotas,
        );
        let bytes = stopped
            .run(Budget::from(stop), Rounds::from(u64::MAX), || false)
            .checkpoint();
        let mut resumed = Dovetail::resume(&formula.plan, EncodedCheckpoint::from(&bytes)).unwrap();
        assert_eq!(run(&mut resumed), whole, "resumed after {stop} steps");
    }
}

/// The value of `c0 + c1 · x + c2 · x · x` at `x`, computed exactly.
///
/// # Specification
/// trivial.
fn polynomial(
    (c0, c1, c2): (&Dyadic, &Dyadic, &Dyadic),
    x: &Dyadic,
) -> Dyadic
{
    let exact = |value: Result<gandr_theory_exact_reals::Rounded, _>| value.unwrap().into_value();
    let square = exact(x.mul(x, Precision::MAX, Rounding::Floor));
    let linear = exact(c1.mul(x, Precision::MAX, Rounding::Floor));
    let quadratic = exact(c2.mul(&square, Precision::MAX, Rounding::Floor));
    let partial = exact(c0.add(&linear, Precision::MAX, Rounding::Floor));
    return exact(partial.add(&quadratic, Precision::MAX, Rounding::Floor));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Each generated quantified formula over a dyadic interval, asked to hold
    /// and to fail, settles to a certificate that replays to the evidence
    /// asked for, or stops for a stated reason. A certified universal holds,
    /// and a refuted existential fails, at each point of a grid of its domain.
    #[test]
    fn quantified_formulas_settle_to_certificates_that_replay(
        exists in any::<bool>(),
        lower in -8_i64 .. 8,
        width in 1_i64 .. 8,
        coefficients in (-8_i64 .. 8, -8_i64 .. 8, -4_i64 .. 4),
        threshold in -16_i64 .. 16,
        flipped in any::<bool>(),
    ) {
        let quarter = |value: i64| dyadic(BigInt::from(value), Exponent::from(-2_i32));
        let (low, high) = (quarter(lower), quarter(lower.checked_add(width).unwrap()));
        let (c0, c1, c2) = (quarter(coefficients.0), quarter(coefficients.1), quarter(coefficients.2));
        let bound = quarter(threshold);
        let form = if exists { Form::Exists } else { Form::Forall };
        let (first, second, third, limit) = (c0.clone(), c1.clone(), c2.clone(), bound.clone());
        let formula = formula(form, closed(low.clone(), high.clone()), Dual::Given, move |builder, x| {
            let c0 = builder.real(Real::Constant(first)).unwrap();
            let c1 = builder.real(Real::Constant(second)).unwrap();
            let c2 = builder.real(Real::Constant(third)).unwrap();
            let square = builder.real(Real::Mul(x, x)).unwrap();
            let linear = builder.real(Real::Mul(c1, x)).unwrap();
            let quadratic = builder.real(Real::Mul(c2, square)).unwrap();
            let partial = builder.real(Real::Add(c0, linear)).unwrap();
            let value = builder.real(Real::Add(partial, quadratic)).unwrap();
            let limit = builder.real(Real::Constant(limit)).unwrap();
            if flipped { (limit, value) } else { (value, limit) }
        });
        // The body at `x`: `p(x) < bound`, or `bound < p(x)` when flipped.
        let body = |x: &Dyadic| {
            let value = polynomial((&c0, &c1, &c2), x);
            if flipped { bound < value } else { value < bound }
        };
        let grid: Vec<Dyadic> = (0_i64 ..= 8)
            .map(|step| {
                let span = high.sub(&low, Precision::MAX, Rounding::Floor).unwrap().into_value();
                let offset = span
                    .mul(&dyadic(BigInt::from(step), Exponent::from(-3_i32)), Precision::MAX, Rounding::Floor)
                    .unwrap()
                    .into_value();
                low.add(&offset, Precision::MAX, Rounding::Floor).unwrap().into_value()
            })
            .collect();
        for demand in [Demand::Holds, Demand::Fails] {
            let Some(Ok(certificate)) = settle(&formula, demand, Budget::from(2048_u64)) else {
                continue;
            };
            let conclusion = check(&formula.plan, &certificate, &CheckerQuotas::default())
                .unwrap()
                .conclusion()
                .clone();
            let expected = match demand {
                Demand::Holds => Conclusion::Holds { open: formula.quantifier },
                Demand::Fails | Demand::Encloses { .. } => Conclusion::Fails { open: formula.quantifier },
            };
            prop_assert_eq!(conclusion, expected);
            match (form, demand) {
                (Form::Forall, Demand::Holds) => prop_assert!(grid.iter().all(&body)),
                (Form::Exists, Demand::Fails) => prop_assert!(!grid.iter().any(&body)),
                (Form::Exists | Form::Forall, Demand::Holds | Demand::Fails | Demand::Encloses { .. }) => {},
            }
        }
    }
}
