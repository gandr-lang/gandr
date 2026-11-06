//! Witnesses of total validation: every well-formed generated plan is
//! admitted, each fault injected into one is refused by name at its node,
//! each quota admits at its bound and refuses past it, the square root of two
//! is admitted, and the evidence table refuses a second judgement.

use gandr_theory_exact_reals::BitWidth;
use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Check;
use gandr_theory_exact_reals::Conflict;
use gandr_theory_exact_reals::Cut;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::DecodeError;
use gandr_theory_exact_reals::Domain;
use gandr_theory_exact_reals::DomainId;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceSlot;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Height;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NodeCount;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::OpenId;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Plan;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Power;
use gandr_theory_exact_reals::Quantifier;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Refusal;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Site;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::validate;
use proptest::prelude::*;

/// The first reference of each judgement's range of four.
const LAWS: u32 = 10;
/// The first nonzero reference.
const NONZERO: u32 = 20;
/// The first overt reference.
const OVERT: u32 = 30;
/// The first compact reference.
const COMPACT: u32 = 40;
/// The first product reference.
const PRODUCT: u32 = 50;
/// The first subdomain reference.
const SUBDOMAIN: u32 = 60;

/// The table that registers each judgement's four references.
///
/// # Specification
/// trivial.
fn table() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    for (first, judgement) in [
        (LAWS, Judgement::CutLaws),
        (NONZERO, Judgement::NonZero),
        (OVERT, Judgement::Overt),
        (COMPACT, Judgement::Compact),
        (PRODUCT, Judgement::Product),
        (SUBDOMAIN, Judgement::Subdomain),
    ] {
        for offset in 0 .. 4 {
            table
                .register(
                    Evidence::from(first.checked_add(offset).unwrap()),
                    judgement,
                )
                .unwrap();
        }
    }
    return table;
}

/// The closed proper interval from `lower` to `upper`.
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

/// One step of a well-formed generated plan.
#[derive(Clone, Debug)]
enum Step
{
    Bound(u32),
    Constant(i64),
    Arithmetic(u8, usize, usize),
    Div(usize, usize, u32),
    Power(usize, u32),
    Cut(i64, i64, usize, usize, u32),
    Less(usize, usize),
    Lattice(bool, usize, usize),
    Quantifier(bool, usize, usize, u32, bool),
    Interval(i64, i64, u32, u32),
    Product(usize, usize, u32),
    Subdomain(usize, usize, u32),
}

/// The strategy of one step.
///
/// # Specification
/// trivial.
fn step() -> impl Strategy<Value = Step>
{
    let index = 0_usize .. 64;
    return prop_oneof![
        (0_u32 .. 3).prop_map(Step::Bound),
        any::<i64>().prop_map(Step::Constant),
        (0_u8 .. 3, index.clone(), index.clone())
            .prop_map(|(kind, left, right)| Step::Arithmetic(kind, left, right)),
        (index.clone(), index.clone(), any::<u32>())
            .prop_map(|(left, right, draw)| Step::Div(left, right, draw)),
        (index.clone(), 0_u32 .. 9).prop_map(|(base, power)| Step::Power(base, power)),
        (
            -50_i64 .. 50,
            0_i64 .. 50,
            index.clone(),
            index.clone(),
            any::<u32>()
        )
            .prop_map(|(lower, width, below, above, draw)| Step::Cut(
                lower, width, below, above, draw
            )),
        (index.clone(), index.clone()).prop_map(|(left, right)| Step::Less(left, right)),
        (any::<bool>(), index.clone(), index.clone())
            .prop_map(|(meet, left, right)| Step::Lattice(meet, left, right)),
        (
            any::<bool>(),
            index.clone(),
            index.clone(),
            any::<u32>(),
            any::<bool>()
        )
            .prop_map(|(exists, domain, body, draw, dual)| Step::Quantifier(
                exists, domain, body, draw, dual
            )),
        (-50_i64 .. 50, 0_i64 .. 50, any::<u32>(), any::<u32>()).prop_map(
            |(lower, width, overt, compact)| Step::Interval(lower, width, overt, compact)
        ),
        (index.clone(), index.clone(), any::<u32>())
            .prop_map(|(left, right, draw)| Step::Product(left, right, draw)),
        (index.clone(), index, any::<u32>())
            .prop_map(|(parent, classifier, draw)| Step::Subdomain(parent, classifier, draw)),
    ];
}

/// The parts of a generated plan that a fault reuses: the builder, the
/// closed root and a domain to quantify over.
struct Parts
{
    builder: PlanBuilder,
    root: OpenId,
    unit: DomainId,
}

/// The well-formed plan that `steps` build: every bound variable below three,
/// the root closed under three existentials over the unit interval, and every
/// evidence reference registered for the judgement its slot takes.
///
/// # Specification
/// trivial.
fn build(steps: &[Step]) -> Parts
{
    // The reference `first + draw % 4`.
    let evidence = |first: u32, draw: u32| {
        Evidence::from(first.checked_add(draw.checked_rem(4).unwrap()).unwrap())
    };
    // The closed hull from `lower` of `width`.
    let span = |lower: i64, width: i64| {
        closed(
            Dyadic::from(lower),
            Dyadic::from(lower.checked_add(width).unwrap()),
        )
    };
    let mut builder = PlanBuilder::new();
    let unit = builder
        .domain(Domain::Interval {
            hull: closed(Dyadic::ZERO, Dyadic::ONE),
            overt: EvidenceSlot::Given(Evidence::from(OVERT)),
            compact: EvidenceSlot::Given(Evidence::from(COMPACT)),
        })
        .unwrap();
    let mut reals: Vec<RealId> = vec![builder.real(Real::Constant(Dyadic::ONE)).unwrap()];
    let mut opens: Vec<OpenId> = vec![builder.open(Open::Top).unwrap()];
    // Each domain with the slots its quantifiers must name, when it is an
    // interval.
    let mut domains: Vec<(DomainId, Option<(Evidence, Evidence)>)> =
        vec![(unit, Some((Evidence::from(OVERT), Evidence::from(COMPACT))))];
    for step in steps {
        let real = |index: usize| reals[index.checked_rem(reals.len()).unwrap()];
        let open = |index: usize| opens[index.checked_rem(opens.len()).unwrap()];
        let domain = |index: usize| domains[index.checked_rem(domains.len()).unwrap()];
        match *step {
            Step::Bound(index) => {
                reals.push(builder.real(Real::Bound(DeBruijn::from(index))).unwrap());
            },
            Step::Constant(value) => {
                reals.push(builder.real(Real::Constant(Dyadic::from(value))).unwrap());
            },
            Step::Arithmetic(kind, left, right) => {
                let (left, right) = (real(left), real(right));
                let node = match kind {
                    0 => Real::Add(left, right),
                    1 => Real::Sub(left, right),
                    _ => Real::Mul(left, right),
                };
                reals.push(builder.real(node).unwrap());
            },
            Step::Div(left, right, draw) => {
                let node = Real::Div {
                    numerator: real(left),
                    denominator: real(right),
                    nonzero: evidence(NONZERO, draw),
                };
                reals.push(builder.real(node).unwrap());
            },
            Step::Power(base, power) => {
                reals.push(
                    builder
                        .real(Real::Power(real(base), Power::from(power)))
                        .unwrap(),
                );
            },
            Step::Cut(lower, width, below, above, draw) => {
                let cut = Cut {
                    hull: span(lower, width),
                    lower: open(below),
                    upper: open(above),
                    laws: evidence(LAWS, draw),
                };
                reals.push(builder.real(Real::Cut(cut)).unwrap());
            },
            Step::Less(left, right) => {
                opens.push(builder.open(Open::Less(real(left), real(right))).unwrap());
            },
            Step::Lattice(meet, left, right) => {
                let (left, right) = (open(left), open(right));
                let node = if meet {
                    Open::Meet(left, right)
                }
                else {
                    Open::Join(left, right)
                };
                opens.push(builder.open(node).unwrap());
            },
            Step::Quantifier(exists, over, body, draw, dual) => {
                let (over, slots) = domain(over);
                let (own, other) = match (slots, exists) {
                    (Some((overt, compact)), true) => (overt, compact),
                    (Some((overt, compact)), false) => (compact, overt),
                    (None, true) => (evidence(OVERT, draw), evidence(COMPACT, draw)),
                    (None, false) => (evidence(COMPACT, draw), evidence(OVERT, draw)),
                };
                let quantifier = Quantifier {
                    domain: over,
                    body: open(body),
                    evidence: own,
                    dual: if dual {
                        EvidenceSlot::Given(other)
                    }
                    else {
                        EvidenceSlot::Absent
                    },
                };
                let node = if exists {
                    Open::Exists(quantifier)
                }
                else {
                    Open::Forall(quantifier)
                };
                opens.push(builder.open(node).unwrap());
            },
            Step::Interval(lower, width, overt, compact) => {
                let (overt, compact) = (evidence(OVERT, overt), evidence(COMPACT, compact));
                let node = Domain::Interval {
                    hull: span(lower, width),
                    overt: EvidenceSlot::Given(overt),
                    compact: EvidenceSlot::Given(compact),
                };
                domains.push((builder.domain(node).unwrap(), Some((overt, compact))));
            },
            Step::Product(left, right, draw) => {
                let node = Domain::Product {
                    left: domain(left).0,
                    right: domain(right).0,
                    evidence: evidence(PRODUCT, draw),
                };
                domains.push((builder.domain(node).unwrap(), None));
            },
            Step::Subdomain(parent, classifier, draw) => {
                let node = Domain::Subdomain {
                    parent: domain(parent).0,
                    classifier: open(classifier),
                    evidence: evidence(SUBDOMAIN, draw),
                };
                domains.push((builder.domain(node).unwrap(), None));
            },
        }
    }
    let last = *reals.last().unwrap();
    let compared = builder.open(Open::Less(last, last)).unwrap();
    let mut root = builder
        .open(Open::Meet(*opens.last().unwrap(), compared))
        .unwrap();
    for _ in 0_u32 .. 3 {
        root = builder
            .open(Open::Exists(Quantifier {
                domain: unit,
                body: root,
                evidence: Evidence::from(OVERT),
                dual: EvidenceSlot::Absent,
            }))
            .unwrap();
    }
    return Parts {
        builder,
        root,
        unit,
    };
}

/// The plan of `parts` with `fault` met beside its root.
///
/// # Specification
/// trivial.
fn beside(
    parts: &Parts,
    fault: impl FnOnce(&mut PlanBuilder, DomainId) -> OpenId,
) -> Plan
{
    let mut builder = parts.builder.clone();
    let fault = fault(&mut builder, parts.unit);
    let root = builder.open(Open::Meet(parts.root, fault)).unwrap();
    return builder.finish(Root::Open(root)).unwrap();
}

/// The position of the first node that `wanted` picks.
///
/// # Specification
/// trivial.
fn position(
    plan: &Plan,
    wanted: impl Fn(&Node) -> bool,
) -> NodeId
{
    return plan.nodes().find(|&(_, node)| wanted(node)).unwrap().0;
}

/// A cut over `top` with `hull` and `laws`, compared with itself.
///
/// # Specification
/// trivial.
fn cut_beside(
    builder: &mut PlanBuilder,
    hull: NumericInterval,
    laws: Evidence,
) -> OpenId
{
    let top = builder.open(Open::Top).unwrap();
    let cut = builder
        .real(Real::Cut(Cut {
            hull,
            lower: top,
            upper: top,
            laws,
        }))
        .unwrap();
    return builder.open(Open::Less(cut, cut)).unwrap();
}

proptest! {
    #[test]
    fn well_formed_generated_plans_are_admitted(steps in prop::collection::vec(step(), 0 .. 48))
    {
        let parts = build(&steps);
        let plan = parts.builder.finish(Root::Open(parts.root)).unwrap();
        let bytes = plan.encode();
        let admitted = validate(EncodedPlan::from(&bytes), &Quotas::default(), &table());
        prop_assert_eq!(admitted.map(ValidatedPlan::into_plan), Ok(plan.clone()));
        prop_assert!(admit(plan, &Quotas::default(), &table()).is_ok());
    }

    #[test]
    fn each_fault_is_refused_by_name_at_its_node(steps in prop::collection::vec(step(), 0 .. 32))
    {
        // The bytes of `plan` with one node appended: `kind` and two children
        // at `child`.
        let appended = |plan: &Plan, kind: u8, child: u32| {
            let mut bytes: Vec<u8> = plan.encode().into();
            let count = u64::try_from(usize::from(plan.node_count()))
                .unwrap()
                .checked_add(1)
                .unwrap();
            bytes[6 .. 14].copy_from_slice(&count.to_le_bytes());
            bytes.push(kind);
            bytes.extend_from_slice(&child.to_le_bytes());
            bytes.extend_from_slice(&child.to_le_bytes());
            bytes
        };
        let parts = build(&steps);
        let quotas = Quotas::default();
        let table = table();
        let refused = |plan: Plan| admit(plan, &quotas, &table).unwrap_err();
        let at = |site: NodeId, check: Check| Refusal { site: Site::Node(site), check };
        // An escaped binder: the variable at index zero under no binder.
        let plan = beside(&parts, |builder, _| {
            let x = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
            builder.open(Open::Less(x, x)).unwrap()
        });
        let x = position(&plan, |node| *node == Node::Real(Real::Bound(DeBruijn::from(0))));
        prop_assert_eq!(refused(plan), at(x, Check::EscapedBinder));
        // A child of the wrong sort, and a child that names its own node: a
        // cycle. Both stand at the appended node.
        let plan = parts.builder.clone().finish(Root::Open(parts.root)).unwrap();
        let last = u32::try_from(usize::from(plan.node_count())).unwrap();
        let root = u32::from(plan.root().node());
        let sum = 0x03_u8;
        for (child, error) in [(root, DecodeError::WrongSort), (last, DecodeError::ForwardReference)] {
            let bytes = appended(&plan, sum, child);
            prop_assert_eq!(
                validate(EncodedPlan::from(bytes.as_slice()), &quotas, &table),
                Err(at(NodeId::from(last), Check::Decode(error)))
            );
        }
        // An unregistered cut, and a cut whose laws name a divisor.
        for (laws, check) in [
            (Evidence::from(999), Check::UnknownEvidence),
            (Evidence::from(NONZERO), Check::EvidenceKind { expected: Judgement::CutLaws, found: Judgement::NonZero }),
        ] {
            let plan = beside(&parts, |builder, _| cut_beside(builder, closed(Dyadic::ONE, Dyadic::from(2_i64)), laws));
            let cut = position(&plan, |node| matches!(*node, Node::Real(Real::Cut(ref cut)) if cut.laws == laws));
            prop_assert_eq!(refused(plan), at(cut, check));
        }
        // A dual hull and a ray as the hull of a cut.
        let ray = NumericInterval::new(Bound::open(Endpoint::NegInf), Bound::closed(Dyadic::ONE), Orientation::Proper).unwrap();
        for hull in [closed(Dyadic::ONE, Dyadic::from(2_i64)).dual(), ray] {
            let plan = beside(&parts, |builder, _| cut_beside(builder, hull.clone(), Evidence::from(LAWS)));
            let cut = position(&plan, |node| matches!(*node, Node::Real(Real::Cut(ref cut)) if cut.hull == hull));
            prop_assert_eq!(refused(plan), at(cut, Check::CutHull));
        }
        // An existential over the unit interval that names other overt
        // evidence than the interval states.
        let plan = beside(&parts, |builder, unit| {
            let top = builder.open(Open::Top).unwrap();
            builder.open(Open::Exists(Quantifier {
                domain: unit,
                body: top,
                evidence: Evidence::from(OVERT.checked_add(1).unwrap()),
                dual: EvidenceSlot::Absent,
            })).unwrap()
        });
        let stated = |quantifier: Quantifier| matches!(
            plan.node(quantifier.domain.node()),
            Ok(&Node::Domain(Domain::Interval { overt: EvidenceSlot::Given(overt), .. })) if overt != quantifier.evidence
        );
        let exists = position(&plan, |node| matches!(*node, Node::Open(Open::Exists(quantifier)) if stated(quantifier)));
        prop_assert_eq!(refused(plan), at(exists, Check::DomainEvidence));
        // A lower cut whose first operand is a constant, not a cut.
        let plan = beside(&parts, |builder, _| {
            let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
            builder.open(Open::LowerCut(one, one)).unwrap()
        });
        let lower = position(&plan, |node| matches!(*node, Node::Open(Open::LowerCut(..))));
        prop_assert_eq!(refused(plan), at(lower, Check::CutOperand));
        // A quota one below what the plan needs, at the input or at a node.
        let plan = parts.builder.clone().finish(Root::Open(parts.root)).unwrap();
        let fewer = Quotas { nodes: NodeCount::from(usize::from(plan.node_count()).checked_sub(1).unwrap()), ..quotas };
        prop_assert_eq!(admit(plan.clone(), &fewer, &table), Err(Refusal { site: Site::Input, check: Check::NodeQuota }));
        prop_assert_eq!(
            validate(EncodedPlan::from(&plan.encode()), &fewer, &table),
            Err(Refusal { site: Site::Input, check: Check::NodeQuota })
        );
        let lower = Quotas { binders: Height::from(2), ..quotas };
        prop_assert_eq!(admit(plan.clone(), &lower, &table).map_err(|refusal| refusal.check), Err(Check::BinderQuota));
        let short = Quotas { height: Height::from(3), ..quotas };
        prop_assert_eq!(admit(plan, &short, &table).map_err(|refusal| refusal.check), Err(Check::HeightQuota));
    }
}

#[test]
fn quotas_admit_at_the_bound_and_refuse_past_it()
{
    let table = table();
    // `x^4` under one existential over the unit interval: four nodes high
    // under one binder.
    let mut builder = PlanBuilder::new();
    let unit = builder
        .domain(Domain::Interval {
            hull: closed(Dyadic::ZERO, Dyadic::ONE),
            overt: EvidenceSlot::Given(Evidence::from(OVERT)),
            compact: EvidenceSlot::Absent,
        })
        .unwrap();
    let x = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
    let power = builder.real(Real::Power(x, Power::from(4))).unwrap();
    let wide = builder.real(Real::Constant(Dyadic::from(255_i64))).unwrap();
    let below = builder.open(Open::Less(power, wide)).unwrap();
    let exists = builder
        .open(Open::Exists(Quantifier {
            domain: unit,
            body: below,
            evidence: Evidence::from(OVERT),
            dual: EvidenceSlot::Absent,
        }))
        .unwrap();
    let plan = builder.finish(Root::Open(exists)).unwrap();
    let bytes = plan.encode();
    let exact = Quotas {
        bytes: bytes.as_ref().len().into(),
        nodes: plan.node_count(),
        height: Height::from(4),
        binders: Height::from(1),
        width: BitWidth::from(8_u64),
        power: Power::from(4),
    };
    assert!(validate(EncodedPlan::from(&bytes), &exact, &table).is_ok());
    let past = |quotas: Quotas| {
        validate(EncodedPlan::from(&bytes), &quotas, &table).map_err(|refusal| refusal.check)
    };
    let fewer = |count: usize| count.checked_sub(1).unwrap();
    assert_eq!(
        past(Quotas {
            bytes: fewer(bytes.as_ref().len()).into(),
            ..exact
        }),
        Err(Check::ByteQuota)
    );
    assert_eq!(
        past(Quotas {
            nodes: fewer(usize::from(plan.node_count())).into(),
            ..exact
        }),
        Err(Check::NodeQuota)
    );
    assert_eq!(
        past(Quotas {
            height: Height::from(3),
            ..exact
        }),
        Err(Check::HeightQuota)
    );
    assert_eq!(
        past(Quotas {
            binders: Height::from(0),
            ..exact
        }),
        Err(Check::BinderQuota)
    );
    assert_eq!(
        past(Quotas {
            width: BitWidth::from(7_u64),
            ..exact
        }),
        Err(Check::WidthQuota)
    );
    assert_eq!(
        past(Quotas {
            power: Power::from(3),
            ..exact
        }),
        Err(Check::PowerQuota)
    );
}

#[test]
fn the_square_root_of_two_is_admitted()
{
    let mut builder = PlanBuilder::new();
    let x = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).unwrap();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let square = builder.real(Real::Mul(x, x)).unwrap();
    let negative = builder.open(Open::Less(x, zero)).unwrap();
    let small = builder.open(Open::Less(square, two)).unwrap();
    let lower = builder.open(Open::Join(negative, small)).unwrap();
    let positive = builder.open(Open::Less(zero, x)).unwrap();
    let large = builder.open(Open::Less(two, square)).unwrap();
    let upper = builder.open(Open::Meet(positive, large)).unwrap();
    let cut = builder
        .real(Real::Cut(Cut {
            hull: closed(Dyadic::ONE, Dyadic::from(2_i64)),
            lower,
            upper,
            laws: Evidence::from(LAWS),
        }))
        .unwrap();
    let plan = builder.finish(Root::Real(cut)).unwrap();
    let admitted = admit(plan.clone(), &Quotas::default(), &table()).unwrap();
    assert_eq!(admitted.plan(), &plan);
    // Without its laws in the table, the cut is refused at the cut.
    let refused = admit(plan, &Quotas::default(), &EvidenceTable::new());
    assert_eq!(
        refused,
        Err(Refusal {
            site: Site::Node(NodeId::from(10)),
            check: Check::UnknownEvidence,
        })
    );
}

#[test]
fn the_table_refuses_a_second_judgement()
{
    let mut table = EvidenceTable::new();
    let laws = Evidence::from(7);
    assert_eq!(table.register(laws, Judgement::CutLaws), Ok(()));
    assert_eq!(table.register(laws, Judgement::CutLaws), Ok(()));
    assert_eq!(
        table.register(laws, Judgement::Compact),
        Err(Conflict {
            held: Judgement::CutLaws,
        })
    );
    assert_eq!(table.judgement(laws), Ok(Judgement::CutLaws));
    assert_eq!(
        table.judgement(Evidence::from(8)),
        Err(Check::UnknownEvidence)
    );
}

/// Whether each line is one nonempty line and no two are alike.
///
/// # Specification
/// trivial.
fn distinct_lines(lines: &[String])
{
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
}

#[test]
fn refusals_render_distinct_phrases()
{
    let checks = [
        Check::Decode(DecodeError::WrongSort),
        Check::ByteQuota,
        Check::NodeQuota,
        Check::HeightQuota,
        Check::BinderQuota,
        Check::WidthQuota,
        Check::PowerQuota,
        Check::EscapedBinder,
        Check::CutHull,
        Check::DomainHull,
        Check::UnknownEvidence,
        Check::EvidenceKind {
            expected: Judgement::CutLaws,
            found: Judgement::NonZero,
        },
        Check::DomainEvidence,
        Check::CutOperand,
    ];
    distinct_lines(&checks.map(|check| check.to_string()));
    distinct_lines(
        &[
            Judgement::CutLaws,
            Judgement::NonZero,
            Judgement::Overt,
            Judgement::Compact,
            Judgement::Product,
            Judgement::Subdomain,
        ]
        .map(|judgement| judgement.to_string()),
    );
    let input = Refusal {
        site: Site::Input,
        check: Check::ByteQuota,
    };
    let node = Refusal {
        site: Site::Node(NodeId::from(3)),
        check: Check::ByteQuota,
    };
    distinct_lines(&[input.to_string(), node.to_string()]);
    assert!(node.to_string().contains('3'));
}
