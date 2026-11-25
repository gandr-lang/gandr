//! Cut elimination: the rewrite of each comparison that reads a cut on one
//! side, the machine's rule for the rewritten node, and the move of an
//! obligation forward and of its certificate back.

use core::num::NonZeroU32;

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Elimination;
use gandr_theory_exact_reals::EliminationError;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NodeCount;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanError;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::StepCount;
use gandr_theory_exact_reals::SuspendReason;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::eliminate;
use gandr_theory_exact_reals::radicand;
use gandr_theory_exact_reals::square_root;
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

/// The evidence table that registers [`laws`].
///
/// # Specification
/// trivial.
fn table() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    table.register(laws(), Judgement::CutLaws).unwrap();
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

/// `45/32`, a point of the lower cut of the square root of two.
///
/// # Specification
/// trivial.
fn below_root() -> Dyadic
{
    return dyadic(BigInt::from(45_u8), Exponent::from(-5_i32));
}

/// `3/2`, a point of the upper cut of the square root of two.
///
/// # Specification
/// trivial.
fn three_halves() -> Dyadic
{
    return dyadic(BigInt::from(3_u8), Exponent::from(-1_i32));
}

/// The plan that `builder` holds under `root`, admitted.
///
/// # Specification
/// trivial.
fn admitted(
    builder: PlanBuilder,
    root: Root,
) -> ValidatedPlan
{
    return admit(builder.finish(root).unwrap(), &Quotas::default(), &table()).unwrap();
}

/// The rewrite of `plan`.
///
/// # Specification
/// trivial.
fn eliminated(plan: &ValidatedPlan) -> Elimination
{
    return eliminate(plan.clone(), &Quotas::default(), &table()).unwrap();
}

/// What a real operand of a comparison is.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Shape
{
    /// A constant.
    Constant(Dyadic),
    /// The registered cut of the square root of the radicand.
    Root(Dyadic),
    /// Any other real.
    Other,
}

/// The form of an open node that compares two reals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Form
{
    /// A strict comparison of its first operand below its second.
    Less,
    /// The lower cut of its first operand at its second.
    LowerCut,
    /// The upper cut of its first operand at its second.
    UpperCut,
}

/// A comparison by its form and the shapes of its operands, in field order.
type Comparison = (Form, Shape, Shape);

/// The shape of the real at `real` of `plan`.
///
/// # Specification
/// trivial.
fn shape(
    plan: &ValidatedPlan,
    real: RealId,
) -> Shape
{
    return match plan.plan().node(real.node()) {
        Ok(&Node::Real(Real::Constant(ref value))) => Shape::Constant(value.clone()),
        Ok(&Node::Real(Real::Cut(_))) => Shape::Root(radicand(plan.plan(), real.node()).unwrap()),
        Ok(_) | Err(_) => Shape::Other,
    };
}

/// The comparison at `node` of `plan`, or `None` for another node.
///
/// # Specification
/// trivial.
fn comparison(
    plan: &ValidatedPlan,
    node: NodeId,
) -> Option<Comparison>
{
    return match plan.plan().node(node) {
        Ok(&Node::Open(Open::Less(left, right))) => {
            Some((Form::Less, shape(plan, left), shape(plan, right)))
        },
        Ok(&Node::Open(Open::LowerCut(cut, point))) => {
            Some((Form::LowerCut, shape(plan, cut), shape(plan, point)))
        },
        Ok(&Node::Open(Open::UpperCut(cut, point))) => {
            Some((Form::UpperCut, shape(plan, cut), shape(plan, point)))
        },
        Ok(_) | Err(_) => None,
    };
}

/// The node of `plan` that holds the comparison `wanted`.
///
/// # Specification
/// trivial.
fn located(
    plan: &ValidatedPlan,
    wanted: &Comparison,
) -> NodeId
{
    return plan
        .plan()
        .nodes()
        .map(|(id, _)| id)
        .find(|&id| comparison(plan, id).as_ref() == Some(wanted))
        .unwrap();
}

/// The square root of two, as an operand.
///
/// # Specification
/// trivial.
fn root_of_two() -> Shape
{
    return Shape::Root(Dyadic::from(2_i64));
}

/// The certificate of one obligation run alone under `quotas`, or the reason
/// it suspends.
///
/// # Specification
/// trivial.
fn settled(
    plan: &ValidatedPlan,
    obligation: Obligation,
    quotas: CheckerQuotas,
) -> Result<Certificate, SuspendReason>
{
    let quantum = Quantum::from(NonZeroU32::new(4).unwrap());
    let mut dovetail = Dovetail::new(plan, [obligation], quantum, quotas);
    let report = dovetail.run(Budget::from(u64::MAX), Rounds::from(1024_u64), || false);
    return match report.outcome(Position::from(0)) {
        Some(Outcome::Certified(certificate)) => Ok(certificate.clone()),
        Some(Outcome::Suspended(reason)) => Err(reason),
        other => panic!("the obligation settles, not {other:?}"),
    };
}

/// The conclusion that `certificate` replays to over `plan`.
///
/// # Specification
/// trivial.
fn replayed(
    plan: &ValidatedPlan,
    certificate: &Certificate,
) -> Conclusion
{
    return check(plan, certificate, &CheckerQuotas::default())
        .unwrap()
        .conclusion()
        .clone();
}

/// The comparisons of the try-first, joined: `45/32 < sqrt 2`, `sqrt 2 < 3/2`
/// and `sqrt 2 < sqrt 2`.
///
/// # Specification
/// trivial.
fn try_first() -> ValidatedPlan
{
    let mut builder = PlanBuilder::new();
    let root = square_root_of_two(&mut builder, laws()).unwrap();
    let point = builder.real(Real::Constant(below_root())).unwrap();
    let above = builder.real(Real::Constant(three_halves())).unwrap();
    let below = builder.open(Open::Less(point, root)).unwrap();
    let over = builder.open(Open::Less(root, above)).unwrap();
    let itself = builder.open(Open::Less(root, root)).unwrap();
    let joined = builder.open(Open::Join(below, over)).unwrap();
    let joined = builder.open(Open::Join(joined, itself)).unwrap();
    return admitted(builder, Root::Open(joined));
}

#[test]
fn the_square_root_of_two_above_45_32_is_its_lower_cut()
{
    // The try-first of the unit. `45/32 < sqrt 2` becomes the lower cut of
    // the square root of two at `45/32`. Its evidence is two steps: the point
    // `45/32`, and the step that reads `(45/32)² = 2025/1024 < 2`. The run of
    // the comparison writes eight steps, because it encloses the root too.
    let plan = try_first();
    let point = Shape::Constant(below_root());
    let less = located(&plan, &(Form::Less, point.clone(), root_of_two()));
    let elimination = eliminated(&plan);
    let lower = elimination.place(less).unwrap();
    let rewritten = elimination.plan();
    assert_eq!(
        comparison(rewritten, lower),
        Some((Form::LowerCut, root_of_two(), point))
    );
    let asked = Obligation::new(&plan, less, Demand::Holds).unwrap();
    let quotas = CheckerQuotas::default();
    let direct = settled(&plan, asked, quotas).expect("the comparison settles");
    let moved = elimination.obligation(asked).unwrap();
    let cut = settled(rewritten, moved, quotas).expect("the lower cut settles");
    assert_eq!(direct.step_count(), StepCount::from(8));
    assert_eq!(cut.step_count(), StepCount::from(2));
    assert_eq!(replayed(rewritten, &cut), Conclusion::Holds { open: lower });
    let restored = elimination.restored(&cut).unwrap();
    assert_eq!(replayed(&plan, &restored), Conclusion::Holds { open: less });
}

#[test]
fn each_comparison_rewrites_as_the_table_states()
{
    // `p < c` and `c < p` with a constant `p` rewrite. `c < c`, a point that
    // reads its cut, and a comparison of two constants stay. Of two cuts, the
    // cut on the right takes the comparison.
    let mut builder = PlanBuilder::new();
    let two = square_root_of_two(&mut builder, laws()).unwrap();
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ONE),
        Bound::closed(Dyadic::from(2_i64)),
        Orientation::Proper,
    )
    .unwrap();
    let three = square_root(&mut builder, Dyadic::from(3_i64), hull, laws()).unwrap();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let shifted = builder.real(Real::Add(two, one)).unwrap();
    let opens = [
        Open::Less(one, two),
        Open::Less(two, one),
        Open::Less(two, two),
        Open::Less(shifted, two),
        Open::Less(one, one),
        Open::Less(two, three),
    ];
    let mut joined = builder.open(opens[0].clone()).unwrap();
    for open in &opens[1 ..] {
        let next = builder.open(open.clone()).unwrap();
        joined = builder.open(Open::Join(joined, next)).unwrap();
    }
    let plan = admitted(builder, Root::Open(joined));
    let elimination = eliminated(&plan);
    let (unit, root_of_three) = (
        Shape::Constant(Dyadic::ONE),
        Shape::Root(Dyadic::from(3_i64)),
    );
    let cases = [
        (
            (Form::Less, unit.clone(), root_of_two()),
            (Form::LowerCut, root_of_two(), unit.clone()),
        ),
        (
            (Form::Less, root_of_two(), unit.clone()),
            (Form::UpperCut, root_of_two(), unit.clone()),
        ),
        (
            (Form::Less, root_of_two(), root_of_two()),
            (Form::Less, root_of_two(), root_of_two()),
        ),
        (
            (Form::Less, Shape::Other, root_of_two()),
            (Form::Less, Shape::Other, root_of_two()),
        ),
        (
            (Form::Less, unit.clone(), unit.clone()),
            (Form::Less, unit.clone(), unit),
        ),
        (
            (Form::Less, root_of_two(), root_of_three.clone()),
            (Form::LowerCut, root_of_three, root_of_two()),
        ),
    ];
    for (before, after) in cases {
        let place = elimination.place(located(&plan, &before)).unwrap();
        assert_eq!(
            comparison(elimination.plan(), place),
            Some(after),
            "{before:?}"
        );
    }
    assert_eq!(elimination.rewritten(), NodeCount::from(3));
}

#[test]
fn a_plan_with_no_cut_comes_back_as_it_is()
{
    let mut builder = PlanBuilder::new();
    let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let less = builder.open(Open::Less(one, two)).unwrap();
    let plan = admitted(builder, Root::Open(less));
    let elimination = eliminated(&plan);
    assert_eq!(elimination.rewritten(), NodeCount::from(0));
    assert_eq!(elimination.plan(), &plan);
    let node = located(
        &plan,
        &(
            Form::Less,
            Shape::Constant(Dyadic::ONE),
            Shape::Constant(Dyadic::from(2_i64)),
        ),
    );
    assert_eq!(elimination.place(node), Some(node));
}

#[test]
fn the_machine_settles_each_cut_by_its_operand_alone()
{
    // Each pole of the lower cut at `45/32` and of the upper cut at `3/2`. The
    // pole that the point's side gives settles in two steps. The other pole
    // suspends as opposed. The lower cut of the square root of two at itself
    // never leaves the cut's value, so it suspends at the step quota.
    let plan = try_first();
    let elimination = eliminated(&plan);
    let rewritten = elimination.plan();
    let pole = |wanted: Comparison, demand: Demand| {
        let node = located(rewritten, &wanted);
        let obligation = Obligation::new(rewritten, node, demand).unwrap();
        return settled(rewritten, obligation, CheckerQuotas::default()).map(|certificate| {
            assert_eq!(certificate.step_count(), StepCount::from(2));
            return replayed(rewritten, &certificate);
        });
    };
    let lower = (Form::LowerCut, root_of_two(), Shape::Constant(below_root()));
    let upper = (
        Form::UpperCut,
        root_of_two(),
        Shape::Constant(three_halves()),
    );
    let (lower_node, upper_node) = (located(rewritten, &lower), located(rewritten, &upper));
    assert_eq!(
        pole(lower.clone(), Demand::Holds),
        Ok(Conclusion::Holds { open: lower_node })
    );
    assert_eq!(pole(lower, Demand::Fails), Err(SuspendReason::Opposed));
    assert_eq!(
        pole(upper.clone(), Demand::Holds),
        Ok(Conclusion::Holds { open: upper_node })
    );
    assert_eq!(pole(upper, Demand::Fails), Err(SuspendReason::Opposed));
    let mut builder = PlanBuilder::new();
    let alone = square_root_of_two(&mut builder, laws()).unwrap();
    let itself = builder.open(Open::LowerCut(alone, alone)).unwrap();
    let selfish = admitted(builder, Root::Open(itself));
    let node = located(&selfish, &(Form::LowerCut, root_of_two(), root_of_two()));
    let short = CheckerQuotas {
        steps: StepCount::from(32),
        ..CheckerQuotas::default()
    };
    let obligation = Obligation::new(&selfish, node, Demand::Holds).unwrap();
    assert_eq!(
        settled(&selfish, obligation, short).map(|certificate| certificate.step_count()),
        Err(SuspendReason::Quota)
    );
}

#[test]
fn errors_render_distinct_phrases()
{
    let mut builder = PlanBuilder::new();
    let root = square_root_of_two(&mut builder, laws()).unwrap();
    let less = builder.open(Open::Less(root, root)).unwrap();
    let unregistered = admit(
        builder.finish(Root::Open(less)).unwrap(),
        &Quotas::default(),
        &EvidenceTable::new(),
    )
    .unwrap_err();
    let plan = EliminationError::Plan(PlanError::UnknownNode).to_string();
    let refused = EliminationError::Refused(unregistered).to_string();
    assert_ne!(plan, refused);
}

proptest! {
    /// Generated points beside the square root of two, each comparison asked
    /// for either pole: the rewritten obligation settles as the original
    /// does, and its certificate moves back to a certificate of the original
    /// comparison.
    #[test]
    fn generated_plans_answer_alike_after_the_elimination(
        mantissa in 1_i64 .. 4096,
        shift in 1_i32 .. 12_i32,
        holds in any::<bool>(),
    ) {
        let point = dyadic(BigInt::from(mantissa), Exponent::from(shift.checked_neg().unwrap()));
        let mut builder = PlanBuilder::new();
        let root = square_root_of_two(&mut builder, laws()).unwrap();
        let constant = builder.real(Real::Constant(point.clone())).unwrap();
        let below = builder.open(Open::Less(constant, root)).unwrap();
        let above = builder.open(Open::Less(root, constant)).unwrap();
        let joined = builder.open(Open::Join(below, above)).unwrap();
        let plan = admitted(builder, Root::Open(joined));
        let elimination = eliminated(&plan);
        prop_assert_eq!(elimination.rewritten(), NodeCount::from(2));
        let demand = if holds { Demand::Holds } else { Demand::Fails };
        let opens = [
            (Form::Less, Shape::Constant(point.clone()), root_of_two()),
            (Form::Less, root_of_two(), Shape::Constant(point)),
        ];
        for open in &opens {
            let asked = Obligation::new(&plan, located(&plan, open), demand).unwrap();
            let moved = elimination.obligation(asked).unwrap();
            let before = settled(&plan, asked, CheckerQuotas::default());
            let after = settled(elimination.plan(), moved, CheckerQuotas::default());
            match (before, after) {
                (Ok(original), Ok(cut)) => {
                    let conclusion = replayed(&plan, &original);
                    let restored = elimination.restored(&cut).unwrap();
                    prop_assert_eq!(replayed(&plan, &restored), conclusion);
                    prop_assert!(cut.step_count() <= original.step_count());
                },
                (Err(first), Err(second)) => prop_assert_eq!(first, second),
                (before, after) => prop_assert!(false, "{before:?} became {after:?}"),
            }
        }
    }
}
