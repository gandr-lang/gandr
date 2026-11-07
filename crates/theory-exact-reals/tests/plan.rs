//! Witnesses of the plan DAG and its canonical serialization: the cut of the
//! square root of two written by hand, the round trip over generated plans,
//! sharing kept as edges, one canonical form whatever built a plan, the
//! builder's refusals, each decoding refusal by name, and the decoder's
//! acceptance of canonical bytes alone.

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Closure;
use gandr_theory_exact_reals::Cut;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::DecodeError;
use gandr_theory_exact_reals::Domain;
use gandr_theory_exact_reals::DomainId;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::DyadicError;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceSlot;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::IntervalError;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::OpenId;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Plan;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanError;
use gandr_theory_exact_reals::Power;
use gandr_theory_exact_reals::Quantifier;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Sort;
use num_bigint::BigInt;
use proptest::prelude::*;

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

/// The cut of the square root of two: the reals below it are those below
/// zero or with a square below two, and the reals above it are those above
/// zero with a square above two.
///
/// # Specification
/// trivial.
fn square_root_of_two(builder: &mut PlanBuilder) -> RealId
{
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
    return builder
        .real(Real::Cut(Cut {
            hull: closed(Dyadic::ONE, Dyadic::from(2_i64)),
            lower,
            upper,
            laws: Evidence::from(0),
        }))
        .unwrap();
}

#[test]
fn the_square_root_of_two_is_a_small_cut()
{
    let mut builder = PlanBuilder::new();
    let cut = square_root_of_two(&mut builder);
    let plan = builder.finish(Root::Real(cut)).unwrap();
    let encoded = plan.encode();
    // Eleven distinct nodes: the variable, zero, two, the square, four
    // comparisons, the join, the meet and the cut.
    assert_eq!(usize::from(plan.node_count()), 11);
    assert_eq!(encoded.as_ref().len(), 153);
    assert_eq!(
        Plan::decode(EncodedPlan::from(encoded.as_ref())),
        Ok(plan.clone())
    );
    let Root::Real(root) = plan.root()
    else {
        panic!("the cut is a real");
    };
    assert_eq!(usize::from(root.node()), 10);
    let Ok(&Node::Real(Real::Cut(ref cut))) = plan.node(root.node())
    else {
        panic!("the root is the cut");
    };
    assert!(matches!(
        plan.node(cut.lower.node()),
        Ok(Node::Open(Open::Join(..)))
    ));
    assert!(matches!(
        plan.node(cut.upper.node()),
        Ok(Node::Open(Open::Meet(..)))
    ));
    // The variable, zero, two and the square each stand once, whatever
    // number of comparisons read them.
    let constants = plan
        .nodes()
        .filter(|&(_, node)| matches!(node, Node::Real(Real::Constant(_))))
        .count();
    assert_eq!(constants, 2);
    assert_eq!(plan.node(NodeId::from(11)), Err(PlanError::UnknownNode));
}

#[test]
fn shared_subterms_serialize_once()
{
    // A chain of squares, each read twice by the next: a tree of 2^32 leaves,
    // and 33 nodes as a DAG.
    let mut builder = PlanBuilder::new();
    let mut square = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
    for _ in 0_u32 .. 32 {
        square = builder.real(Real::Mul(square, square)).unwrap();
    }
    let plan = builder.finish(Root::Real(square)).unwrap();
    assert_eq!(usize::from(plan.node_count()), 33);
    // The header, the variable, then one product of two children per square.
    assert_eq!(plan.encode().as_ref().len(), 14 + 5 + 32 * 9);
    // The same chain built as a tree, every operand built again: the plan
    // and the bytes do not change.
    let depth = 10_usize;
    let mut builder = PlanBuilder::new();
    let mut frontier: Vec<RealId> =
        core::iter::repeat_with(|| builder.real(Real::Bound(DeBruijn::from(0))).unwrap())
            .take(1024)
            .collect();
    while frontier.len() > 1 {
        frontier = frontier
            .chunks(2)
            .map(|operands| {
                let [left, right] = *operands
                else {
                    panic!("an even frontier");
                };
                builder.real(Real::Mul(left, right)).unwrap()
            })
            .collect();
    }
    assert!(usize::from(builder.node_count()) > 2000);
    let tree = builder.finish(Root::Real(frontier[0])).unwrap();
    let mut builder = PlanBuilder::new();
    let mut square = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
    for _ in 0 .. depth {
        square = builder.real(Real::Mul(square, square)).unwrap();
    }
    let dag = builder.finish(Root::Real(square)).unwrap();
    assert_eq!(usize::from(tree.node_count()), depth + 1);
    assert_eq!(tree, dag);
    assert_eq!(tree.encode(), dag.encode());
}

#[test]
fn canonical_form_ignores_order_sharing_and_dead_nodes()
{
    // `exists y in [0, 1] (x + 1) · (x + 1) < y`, with its parts built in
    // one order and every part shared.
    let mut builder = PlanBuilder::new();
    let x = builder.real(Real::Bound(DeBruijn::from(1))).unwrap();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let sum = builder.real(Real::Add(x, one)).unwrap();
    let square = builder.real(Real::Mul(sum, sum)).unwrap();
    let y = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
    let below = builder.open(Open::Less(square, y)).unwrap();
    let domain = builder
        .domain(Domain::Interval {
            hull: closed(Dyadic::ZERO, Dyadic::ONE),
            overt: EvidenceSlot::Given(Evidence::from(7)),
            compact: EvidenceSlot::Absent,
        })
        .unwrap();
    let exists = builder
        .open(Open::Exists(Quantifier {
            domain,
            body: below,
            evidence: Evidence::from(7),
            dual: EvidenceSlot::Absent,
        }))
        .unwrap();
    let shared = builder.finish(Root::Open(exists)).unwrap();
    // The same proposition built in another order, each sum built twice, and
    // with nodes that the root does not reach.
    let mut builder = PlanBuilder::new();
    let domain = builder
        .domain(Domain::Interval {
            hull: closed(Dyadic::ZERO, Dyadic::ONE),
            overt: EvidenceSlot::Given(Evidence::from(7)),
            compact: EvidenceSlot::Absent,
        })
        .unwrap();
    let _dead = builder.open(Open::Top).unwrap();
    let y = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let x = builder.real(Real::Bound(DeBruijn::from(1))).unwrap();
    let first = builder.real(Real::Add(x, one)).unwrap();
    let again = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let second = builder.real(Real::Add(x, again)).unwrap();
    let square = builder.real(Real::Mul(first, second)).unwrap();
    let _dead = builder.real(Real::Sub(square, y)).unwrap();
    let below = builder.open(Open::Less(square, y)).unwrap();
    let exists = builder
        .open(Open::Exists(Quantifier {
            domain,
            body: below,
            evidence: Evidence::from(7),
            dual: EvidenceSlot::Absent,
        }))
        .unwrap();
    let unshared = builder.finish(Root::Open(exists)).unwrap();
    assert_eq!(shared, unshared);
    assert_eq!(shared.encode(), unshared.encode());
    // The interval domain, the bound variables, one, the sum, the square,
    // the comparison and the quantifier.
    assert_eq!(usize::from(shared.node_count()), 8);
    // A plan whose structure differs, even in one field, gives other bytes.
    let mut builder = PlanBuilder::new();
    let x = builder.real(Real::Bound(DeBruijn::from(1))).unwrap();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let sum = builder.real(Real::Add(one, x)).unwrap();
    let square = builder.real(Real::Mul(sum, sum)).unwrap();
    let y = builder.real(Real::Bound(DeBruijn::from(0))).unwrap();
    let below = builder.open(Open::Less(square, y)).unwrap();
    let domain = builder
        .domain(Domain::Interval {
            hull: closed(Dyadic::ZERO, Dyadic::ONE),
            overt: EvidenceSlot::Given(Evidence::from(7)),
            compact: EvidenceSlot::Absent,
        })
        .unwrap();
    let exists = builder
        .open(Open::Exists(Quantifier {
            domain,
            body: below,
            evidence: Evidence::from(7),
            dual: EvidenceSlot::Absent,
        }))
        .unwrap();
    let commuted = builder.finish(Root::Open(exists)).unwrap();
    assert_ne!(shared, commuted);
    assert_ne!(shared.encode(), commuted.encode());
}

#[test]
fn builder_refuses_a_foreign_or_missorted_child()
{
    let mut reals = PlanBuilder::new();
    let constant = reals.real(Real::Constant(Dyadic::ONE)).unwrap();
    let mut opens = PlanBuilder::new();
    let top = opens.open(Open::Top).unwrap();
    // A child that names a node of another sort in this builder.
    assert_eq!(
        opens.real(Real::Add(constant, constant)),
        Err(PlanError::WrongSort)
    );
    assert_eq!(
        opens.finish(Root::Real(constant)).unwrap_err(),
        PlanError::WrongSort
    );
    // A child that names no node of this builder.
    let mut empty = PlanBuilder::new();
    assert_eq!(
        empty.real(Real::Mul(constant, constant)),
        Err(PlanError::UnknownNode)
    );
    assert_eq!(
        empty.open(Open::Meet(top, top)),
        Err(PlanError::UnknownNode)
    );
    assert_eq!(empty.sort_of(NodeId::from(0)), Err(PlanError::UnknownNode));
    assert_eq!(usize::from(empty.node_count()), 0);
    assert_eq!(
        PlanBuilder::new().finish(Root::Open(top)).unwrap_err(),
        PlanError::UnknownNode
    );
    // Each slot takes its own sort.
    let mut builder = PlanBuilder::new();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let top = builder.open(Open::Top).unwrap();
    let domain = builder
        .domain(Domain::Interval {
            hull: closed(Dyadic::ZERO, Dyadic::ONE),
            overt: EvidenceSlot::Absent,
            compact: EvidenceSlot::Absent,
        })
        .unwrap();
    assert_eq!(builder.sort_of(one.node()), Ok(Sort::Real));
    assert_eq!(builder.sort_of(top.node()), Ok(Sort::Open));
    assert_eq!(builder.sort_of(domain.node()), Ok(Sort::Domain));
    let mut foreign = PlanBuilder::new();
    let _first = foreign.open(Open::Top).unwrap();
    let wrong_real = foreign.real(Real::Constant(Dyadic::ONE)).unwrap();
    let wrong_open = foreign.open(Open::Bottom).unwrap();
    // In `builder`, position 1 is an open node and position 2 a domain.
    assert_eq!(
        builder.real(Real::Power(wrong_real, Power::from(2))),
        Err(PlanError::WrongSort)
    );
    assert_eq!(
        builder.domain(Domain::Subdomain {
            parent: domain,
            classifier: wrong_open,
            evidence: Evidence::from(0),
        }),
        Err(PlanError::WrongSort)
    );
    // A refused node leaves the builder as it was, and an admitted one takes
    // the next position.
    let before = usize::from(builder.node_count());
    assert_eq!(before, 3);
    let forall = builder
        .open(Open::Forall(Quantifier {
            domain,
            body: top,
            evidence: Evidence::from(0),
            dual: EvidenceSlot::Absent,
        }))
        .unwrap();
    assert_eq!(usize::from(forall.node()), before);
    assert_eq!(usize::from(builder.node_count()), before + 1);
    let edges: Vec<_> = Node::Real(Real::Div {
        numerator: one,
        denominator: one,
        nonzero: Evidence::from(3),
    })
    .edges()
    .map(|edge| (edge.node, edge.sort))
    .collect();
    assert_eq!(edges, [(one.node(), Sort::Real), (one.node(), Sort::Real)]);
}

#[test]
fn decoding_refuses_malformed_bytes_by_name()
{
    let decode = |bytes: &[u8]| Plan::decode(EncodedPlan::from(bytes));
    // The magic, the version, the count, then the nodes' bytes.
    let bytes = |count: u64, nodes: &[&[u8]]| {
        let mut out = b"GXRP".to_vec();
        out.extend_from_slice(&1_u16.to_le_bytes());
        out.extend_from_slice(&count.to_le_bytes());
        for node in nodes {
            out.extend_from_slice(node);
        }
        out
    };
    // A constant node with an inline mantissa.
    let constant = |exponent: i32, mantissa: &[u8]| {
        let mut out = vec![0x02];
        out.extend_from_slice(&exponent.to_le_bytes());
        out.extend_from_slice(&u64::try_from(mantissa.len()).unwrap().to_le_bytes());
        out.extend_from_slice(mantissa);
        out
    };
    // A node of one kind and two children.
    let pair = |kind: u8, left: u32, right: u32| {
        let mut out = vec![kind];
        out.extend_from_slice(&left.to_le_bytes());
        out.extend_from_slice(&right.to_le_bytes());
        out
    };
    let one = constant(0_i32, &[0x01]);
    let top = [0x10_u8];
    assert_eq!(decode(b"GXRQ"), Err(DecodeError::Magic));
    assert_eq!(decode(b"GXR"), Err(DecodeError::Truncated));
    let mut version = bytes(1, &[&top]);
    version[4] = 2;
    assert_eq!(decode(&version), Err(DecodeError::Version));
    assert_eq!(decode(&bytes(0, &[])), Err(DecodeError::Empty));
    // Every prefix of a valid plan is refused, never read past its end.
    let valid = bytes(1, &[&one]);
    assert_eq!(
        decode(&valid).map(|plan| plan.encode().as_ref().to_vec()),
        Ok(valid.clone())
    );
    for end in 0 .. valid.len() {
        assert!(decode(&valid[.. end]).is_err(), "the prefix of {end} bytes");
    }
    assert_eq!(
        decode(&valid[.. valid.len() - 1]),
        Err(DecodeError::Truncated)
    );
    assert_eq!(decode(&bytes(1, &[&[0xFF]])), Err(DecodeError::UnknownKind));
    // A sum that names itself, and one that names an open node.
    assert_eq!(
        decode(&bytes(1, &[&pair(0x03, 0, 0)])),
        Err(DecodeError::ForwardReference)
    );
    assert_eq!(
        decode(&bytes(2, &[&top, &pair(0x03, 0, 0)])),
        Err(DecodeError::WrongSort)
    );
    // An interval domain as the root.
    let mut domain = vec![0x20, 0x00];
    domain.extend_from_slice(&[0x01]);
    domain.extend_from_slice(&constant(0_i32, &[])[1 ..]);
    domain.extend_from_slice(&[0x00, 0x01]);
    domain.extend_from_slice(&constant(0_i32, &[0x01])[1 ..]);
    domain.extend_from_slice(&[0x00, 0x00, 0x00]);
    assert_eq!(decode(&bytes(1, &[&domain])), Err(DecodeError::DomainRoot));
    let mut trailing = valid;
    trailing.push(0x00);
    assert_eq!(decode(&trailing), Err(DecodeError::TrailingBytes));
    // A count that the bytes cannot hold ends inside a node.
    assert_eq!(
        decode(&bytes(u64::MAX, &[&one])),
        Err(DecodeError::Truncated)
    );
    // An even mantissa whose canonical exponent leaves its range.
    assert_eq!(
        decode(&bytes(1, &[&constant(i32::MAX, &[0x02])])),
        Err(DecodeError::Dyadic(DyadicError::ExponentOutOfRange))
    );
    // A cut whose hull runs from two down to one.
    let mut cut = vec![0x08, 0x00, 0x01];
    cut.extend_from_slice(&constant(1_i32, &[0x01])[1 ..]);
    cut.extend_from_slice(&[0x00, 0x01]);
    cut.extend_from_slice(&constant(0_i32, &[0x01])[1 ..]);
    cut.extend_from_slice(&[0x00]);
    cut.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(
        decode(&bytes(2, &[&top, &cut])),
        Err(DecodeError::Interval(IntervalError::Reversed))
    );
    // An orientation byte that names no orientation.
    let mut bad_orientation = cut.clone();
    bad_orientation[1] = 0x07;
    assert_eq!(
        decode(&bytes(2, &[&top, &bad_orientation])),
        Err(DecodeError::UnknownKind)
    );
    // Bytes that decode but are not canonical: a duplicate node, a padded
    // mantissa, a node the root does not reach, and children out of order.
    assert_eq!(
        decode(&bytes(3, &[&one, &one, &pair(0x03, 0, 1)])),
        Err(DecodeError::NotCanonical)
    );
    assert_eq!(
        decode(&bytes(1, &[&constant(0_i32, &[0x01, 0x00])])),
        Err(DecodeError::NotCanonical)
    );
    assert_eq!(
        decode(&bytes(1, &[&constant(3_i32, &[])])),
        Err(DecodeError::NotCanonical)
    );
    let two = constant(1_i32, &[0x01]);
    assert_eq!(
        decode(&bytes(2, &[&one, &two])),
        Err(DecodeError::NotCanonical)
    );
    assert_eq!(
        decode(&bytes(3, &[&two, &one, &pair(0x03, 1, 0)])),
        Err(DecodeError::NotCanonical)
    );
    assert!(decode(&bytes(3, &[&one, &two, &pair(0x03, 0, 1)])).is_ok());
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
fn failures_render_distinct_phrases()
{
    distinct_lines(
        &[
            PlanError::UnknownNode,
            PlanError::WrongSort,
            PlanError::TooManyNodes,
        ]
        .map(|error| error.to_string()),
    );
    let decoding = [
        DecodeError::Magic,
        DecodeError::Version,
        DecodeError::Truncated,
        DecodeError::UnknownKind,
        DecodeError::ForwardReference,
        DecodeError::WrongSort,
        DecodeError::Empty,
        DecodeError::DomainRoot,
        DecodeError::TrailingBytes,
        DecodeError::TooManyNodes,
        DecodeError::Dyadic(DyadicError::ExponentOutOfRange),
        DecodeError::Interval(IntervalError::Reversed),
        DecodeError::NotCanonical,
    ]
    .map(|error| error.to_string());
    distinct_lines(&decoding);
    assert!(decoding[10].contains(&DyadicError::ExponentOutOfRange.to_string()));
    assert!(decoding[11].contains(&IntervalError::Reversed.to_string()));
}

/// One step of a generated plan: a node kind and the draws that choose its
/// children and its payload.
#[derive(Clone, Debug)]
pub enum Step
{
    Bound(u32),
    Constant(i128, i32),
    Arithmetic(u8, usize, usize),
    Builtin(u8, usize, usize),
    Div(usize, usize, u32),
    Power(usize, u32),
    Cut(i64, i64, usize, usize, u32),
    Constant0(bool),
    Less(usize, usize),
    Lattice(bool, usize, usize),
    Quantifier(bool, usize, usize, u32, Option<u32>),
    Interval(i64, i64, bool, Option<u32>, Option<u32>),
    Product(usize, usize, u32),
    Subdomain(usize, usize, u32),
}

/// The strategy of one step.
///
/// # Specification
/// trivial.
pub fn step() -> impl Strategy<Value = Step>
{
    let index = 0_usize .. 64;
    return prop_oneof![
        (0_u32 .. 4).prop_map(Step::Bound),
        (any::<i128>(), -70_i32 .. 70)
            .prop_map(|(mantissa, exponent)| Step::Constant(mantissa, exponent)),
        (-300_i128 .. 300, -4_i32 .. 4)
            .prop_map(|(mantissa, exponent)| Step::Constant(mantissa, exponent)),
        (0_u8 .. 3, index.clone(), index.clone())
            .prop_map(|(kind, left, right)| Step::Arithmetic(kind, left, right)),
        (0_u8 .. 4, index.clone(), index.clone())
            .prop_map(|(kind, left, right)| Step::Builtin(kind, left, right)),
        (index.clone(), index.clone(), any::<u32>())
            .prop_map(|(left, right, evidence)| Step::Div(left, right, evidence)),
        (index.clone(), 0_u32 .. 9).prop_map(|(base, power)| Step::Power(base, power)),
        (
            -50_i64 .. 50,
            0_i64 .. 50,
            index.clone(),
            index.clone(),
            any::<u32>()
        )
            .prop_map(|(lower, width, below, above, laws)| Step::Cut(
                lower, width, below, above, laws
            )),
        any::<bool>().prop_map(Step::Constant0),
        (index.clone(), index.clone()).prop_map(|(left, right)| Step::Less(left, right)),
        (any::<bool>(), index.clone(), index.clone())
            .prop_map(|(meet, left, right)| Step::Lattice(meet, left, right)),
        (
            any::<bool>(),
            index.clone(),
            index.clone(),
            any::<u32>(),
            any::<Option<u32>>()
        )
            .prop_map(|(exists, domain, body, evidence, dual)| Step::Quantifier(
                exists, domain, body, evidence, dual
            )),
        (
            -50_i64 .. 50,
            -1_i64 .. 50,
            any::<bool>(),
            any::<Option<u32>>(),
            any::<Option<u32>>()
        )
            .prop_map(|(lower, width, dual, overt, compact)| Step::Interval(
                lower, width, dual, overt, compact
            )),
        (index.clone(), index.clone(), any::<u32>())
            .prop_map(|(left, right, evidence)| Step::Product(left, right, evidence)),
        (index.clone(), index, any::<u32>()).prop_map(|(parent, classifier, evidence)| {
            Step::Subdomain(parent, classifier, evidence)
        }),
    ];
}

/// The plan that `steps` build, rooted at the last real or open node; a step
/// whose children have no node of their sort yet is skipped.
///
/// # Specification
/// trivial.
pub fn build(steps: &[Step]) -> (PlanBuilder, Root)
{
    let slot = |draw: Option<u32>| {
        draw.map_or(EvidenceSlot::Absent, |index| {
            EvidenceSlot::Given(Evidence::from(index))
        })
    };
    // The hull from `lower` of `width`, a ray below when the width is
    // negative.
    let hull = |lower: i64, width: i64| {
        if width < 0 {
            return NumericInterval::new(
                Bound::open(Endpoint::NegInf),
                Bound::new(Endpoint::Finite(Dyadic::from(lower)), Closure::Open),
                Orientation::Proper,
            )
            .unwrap();
        }
        closed(
            Dyadic::from(lower),
            Dyadic::from(lower.checked_add(width).unwrap()),
        )
    };
    let mut builder = PlanBuilder::new();
    let mut reals: Vec<RealId> = vec![builder.real(Real::Constant(Dyadic::ONE)).unwrap()];
    let mut opens: Vec<OpenId> = Vec::new();
    let mut domains: Vec<DomainId> = Vec::new();
    let mut root = Root::Real(reals[0]);
    for step in steps {
        let real = |index: usize| reals[index.checked_rem(reals.len()).unwrap()];
        let open = |index: usize| {
            opens
                .get(index.checked_rem(opens.len().max(1)).unwrap())
                .copied()
        };
        let domain = |index: usize| {
            domains
                .get(index.checked_rem(domains.len().max(1)).unwrap())
                .copied()
        };
        match *step {
            Step::Bound(index) => {
                reals.push(builder.real(Real::Bound(DeBruijn::from(index))).unwrap());
            },
            Step::Constant(mantissa, exponent) => {
                reals.push(
                    builder
                        .real(Real::Constant(
                            Dyadic::new(BigInt::from(mantissa), Exponent::from(exponent)).unwrap(),
                        ))
                        .unwrap(),
                );
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
            Step::Builtin(kind, left, right) => {
                let node = match kind {
                    0 => Real::Pi,
                    1 => Real::Cos(real(left)),
                    2 => Real::Sin(real(left)),
                    _ => Real::Arg(real(left), real(right)),
                };
                reals.push(builder.real(node).unwrap());
            },
            Step::Div(left, right, evidence) => {
                let node = Real::Div {
                    numerator: real(left),
                    denominator: real(right),
                    nonzero: Evidence::from(evidence),
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
            Step::Cut(lower, width, below, above, laws) => {
                let (Some(below), Some(above)) = (open(below), open(above))
                else {
                    continue;
                };
                let cut = Cut {
                    hull: hull(lower, width),
                    lower: below,
                    upper: above,
                    laws: Evidence::from(laws),
                };
                reals.push(builder.real(Real::Cut(cut)).unwrap());
            },
            Step::Constant0(top) => {
                opens.push(
                    builder
                        .open(if top { Open::Top } else { Open::Bottom })
                        .unwrap(),
                );
            },
            Step::Less(left, right) => {
                opens.push(builder.open(Open::Less(real(left), real(right))).unwrap());
            },
            Step::Lattice(meet, left, right) => {
                let (Some(left), Some(right)) = (open(left), open(right))
                else {
                    continue;
                };
                let node = if meet {
                    Open::Meet(left, right)
                }
                else {
                    Open::Join(left, right)
                };
                opens.push(builder.open(node).unwrap());
            },
            Step::Quantifier(exists, over, body, evidence, dual) => {
                let (Some(over), Some(body)) = (domain(over), open(body))
                else {
                    continue;
                };
                let quantifier = Quantifier {
                    domain: over,
                    body,
                    evidence: Evidence::from(evidence),
                    dual: slot(dual),
                };
                let node = if exists {
                    Open::Exists(quantifier)
                }
                else {
                    Open::Forall(quantifier)
                };
                opens.push(builder.open(node).unwrap());
            },
            Step::Interval(lower, width, dual, overt, compact) => {
                let interval = hull(lower, width);
                let interval = if dual { interval.dual() } else { interval };
                let node = Domain::Interval {
                    hull: interval,
                    overt: slot(overt),
                    compact: slot(compact),
                };
                domains.push(builder.domain(node).unwrap());
            },
            Step::Product(left, right, evidence) => {
                let (Some(left), Some(right)) = (domain(left), domain(right))
                else {
                    continue;
                };
                let node = Domain::Product {
                    left,
                    right,
                    evidence: Evidence::from(evidence),
                };
                domains.push(builder.domain(node).unwrap());
            },
            Step::Subdomain(parent, classifier, evidence) => {
                let (Some(parent), Some(classifier)) = (domain(parent), open(classifier))
                else {
                    continue;
                };
                let node = Domain::Subdomain {
                    parent,
                    classifier,
                    evidence: Evidence::from(evidence),
                };
                domains.push(builder.domain(node).unwrap());
            },
        }
        root = match (reals.last(), opens.last()) {
            (_, Some(&open))
                if matches!(
                    step,
                    Step::Constant0(_) | Step::Less(..) | Step::Lattice(..) | Step::Quantifier(..)
                ) =>
            {
                Root::Open(open)
            },
            (Some(&real), _) => Root::Real(real),
            (None, _) => root,
        };
    }
    return (builder, root);
}

proptest! {
    #[test]
    fn encoding_round_trips_generated_plans(steps in prop::collection::vec(step(), 0 .. 48))
    {
        let (builder, root) = build(&steps);
        let plan = builder.clone().finish(root).unwrap();
        let encoded = plan.encode();
        let decoded = Plan::decode(EncodedPlan::from(encoded.as_ref()));
        prop_assert_eq!(decoded.as_ref(), Ok(&plan));
        prop_assert_eq!(decoded.unwrap().encode(), encoded);
        // Finishing twice gives the same plan: the canonical form is a fixed
        // point.
        prop_assert_eq!(builder.finish(root).unwrap(), plan);
    }

    #[test]
    fn decoding_accepts_only_canonical_bytes(
        steps in prop::collection::vec(step(), 0 .. 24),
        at in any::<usize>(),
        flip in 1_u8 ..,
        noise in prop::collection::vec(any::<u8>(), 0 .. 64),
    )
    {
        let (builder, root) = build(&steps);
        let mut edited: Vec<u8> = builder.finish(root).unwrap().encode().into();
        let position = at.checked_rem(edited.len()).unwrap();
        edited[position] ^= flip;
        if let Ok(plan) = Plan::decode(EncodedPlan::from(edited.as_slice())) {
            let again: Vec<u8> = plan.encode().into();
            prop_assert_eq!(again, edited);
        }
        let count = u64::from(noise.first().copied().unwrap_or(1));
        let mut noisy = b"GXRP".to_vec();
        noisy.extend_from_slice(&1_u16.to_le_bytes());
        noisy.extend_from_slice(&count.to_le_bytes());
        noisy.extend_from_slice(&noise);
        if let Ok(plan) = Plan::decode(EncodedPlan::from(noisy.as_slice())) {
            let again: Vec<u8> = plan.encode().into();
            prop_assert_eq!(again, noisy);
        }
    }
}
