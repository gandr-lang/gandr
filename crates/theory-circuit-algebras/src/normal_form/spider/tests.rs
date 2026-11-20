use alloc::boxed::Box;
use alloc::vec::Vec;

use super::*;
use crate::interface::EdgeCount;
use crate::interface::Generator;
use crate::interface::GeneratorLabel;
use crate::interface::GeneratorName;
use crate::interface::GeneratorSort;
use crate::interface::Interface;
use crate::interface::Wire;
use crate::interface::WireCount;
use crate::interface::Wiring;
use crate::normal_form::DiagramEquality;
use crate::normal_form::PortCount;
use crate::normal_form::same_diagram;

/// No ports: an empty port list.
const NONE: [Wire; 0] = [];

/// The spider label of the sort `z`.
///
/// # Specification
/// trivial.
fn z() -> GeneratorLabel
{
    GeneratorLabel::new("z", GeneratorSort::Spider)
}

/// The spider label of a second sort, `x`.
///
/// # Specification
/// trivial.
fn x() -> GeneratorLabel
{
    GeneratorLabel::new("x", GeneratorSort::Spider)
}

/// A value label.
///
/// # Specification
/// trivial.
fn value<N>(name: N) -> GeneratorLabel
where
    N: Into<GeneratorName>,
{
    GeneratorLabel::new(name, GeneratorSort::Value)
}

/// A budget that no fixture exhausts.
///
/// # Specification
/// trivial.
fn budget() -> SpiderBudget
{
    SpiderBudget::from(1_000)
}

/// A fixture diagram, which is in the fragment.
///
/// # Specification
/// trivial.
fn diagram<W, Inputs, Outputs>(
    wires: W,
    generators: Vec<Generator>,
    inputs: Inputs,
    outputs: Outputs,
) -> Wiring
where
    W: Into<WireCount>,
    Inputs: Into<Box<[Wire]>>,
    Outputs: Into<Box<[Wire]>>,
{
    Wiring::assemble(wires.into(), generators, Interface::new(inputs, outputs))
        .expect("a fixture is monogamous, boundary-honest and acyclic")
}

/// The decision of `left` and `right` modulo the laws, within the fixture
/// budget.
///
/// # Specification
/// trivial.
fn decide(
    left: &Wiring,
    right: &Wiring,
) -> SpiderEquality
{
    same_modulo_frobenius(left, right, budget()).expect("no fixture exhausts the budget")
}

/// The verdict of the decision, with neither arm's evidence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Verdict
{
    /// One diagram modulo the laws.
    Same,
    /// Two diagrams.
    Distinct,
}

/// The verdict on `left` and `right`, with each canon of a `Same` verified
/// against its own input.
///
/// # Specification
/// trivial.
fn verdict(
    left: &Wiring,
    right: &Wiring,
) -> Verdict
{
    match decide(left, right) {
        SpiderEquality::Same(shared) => {
            assert_eq!(
                Ok(()),
                shared.left().verify(left),
                "the left canon is evidence"
            );
            assert_eq!(
                Ok(()),
                shared.right().verify(right),
                "the right canon is evidence"
            );
            Verdict::Same
        },
        SpiderEquality::Distinct(_) => Verdict::Distinct,
    }
}

/// A plain wire: one input that is the one output.
///
/// # Specification
/// trivial.
fn plain_wire() -> Wiring
{
    diagram(1, Vec::new(), wires![0], wires![0])
}

#[test]
fn two_merges_in_either_association_are_one_spider()
{
    let left = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![0, 1], wires![3]),
            Generator::new(z(), wires![3, 2], wires![4]),
        ],
        wires![0, 1, 2],
        wires![4],
    );
    let right = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![1, 2], wires![3]),
            Generator::new(z(), wires![0, 3], wires![4]),
        ],
        wires![0, 1, 2],
        wires![4],
    );
    let one = diagram(
        4,
        alloc::vec![Generator::new(z(), wires![0, 1, 2], wires![3])],
        wires![0, 1, 2],
        wires![3],
    );
    assert!(
        matches!(same_diagram(&left, &right), DiagramEquality::Distinct(_)),
        "the presentation relation tells the two associations apart"
    );
    assert_eq!(Verdict::Same, verdict(&left, &right), "associativity");
    assert_eq!(
        Verdict::Same,
        verdict(&left, &one),
        "both associations are the one merge of three wires"
    );
    let fused = spider_normal_form(&left).expect("a fused form assembles");
    assert_eq!(
        fused.generators(),
        [Generator::new(z(), wires![0, 1, 2], wires![3])],
        "the inner wire goes, and the class holds the open wires in member order"
    );
    assert_eq!(fused.wire_count(), WireCount::from(4));
    assert_eq!(
        fused.boundary(),
        &Interface::new(wires![0, 1, 2], wires![3])
    );
}

#[test]
fn commuted_legs_are_one_spider()
{
    let merge = |sources: [Wire; 2]| {
        diagram(
            3,
            alloc::vec![Generator::new(z(), sources, wires![2])],
            wires![0, 1],
            wires![2],
        )
    };
    assert!(
        matches!(
            same_diagram(&merge(wires![0, 1]), &merge(wires![1, 0])),
            DiagramEquality::Distinct(_)
        ),
        "the presentation relation reads the legs in order"
    );
    assert_eq!(
        Verdict::Same,
        verdict(&merge(wires![0, 1]), &merge(wires![1, 0])),
        "commutativity"
    );
    let ordered = |sources: [Wire; 2]| {
        diagram(
            3,
            alloc::vec![Generator::new(value("f"), sources, wires![2])],
            wires![0, 1],
            wires![2],
        )
    };
    assert_eq!(
        Verdict::Distinct,
        verdict(&ordered(wires![0, 1]), &ordered(wires![1, 0])),
        "a generator that orders its ports does not commute"
    );
}

#[test]
fn the_units_and_the_counits_vanish()
{
    let unit = diagram(
        3,
        alloc::vec![
            Generator::new(z(), NONE, wires![0]),
            Generator::new(z(), wires![0, 1], wires![2]),
        ],
        wires![1],
        wires![2],
    );
    let counit = diagram(
        3,
        alloc::vec![
            Generator::new(z(), wires![0], wires![1, 2]),
            Generator::new(z(), wires![2], NONE),
        ],
        wires![0],
        wires![1],
    );
    assert_eq!(Verdict::Same, verdict(&unit, &plain_wire()), "the unit law");
    assert_eq!(
        Verdict::Same,
        verdict(&counit, &plain_wire()),
        "the counit law"
    );
    let fused = spider_normal_form(&unit).expect("a fused form assembles");
    assert!(fused.generators().is_empty(), "the identity spider goes");
    assert_eq!(
        fused.boundary(),
        &Interface::new(wires![0], wires![0]),
        "and its two wires are one wire on both legs"
    );
}

#[test]
fn the_frobenius_law_holds()
{
    let left = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![1], wires![2, 3]),
            Generator::new(z(), wires![0, 2], wires![4]),
        ],
        wires![0, 1],
        wires![4, 3],
    );
    let middle = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![0, 1], wires![2]),
            Generator::new(z(), wires![2], wires![3, 4]),
        ],
        wires![0, 1],
        wires![3, 4],
    );
    let right = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![0], wires![2, 3]),
            Generator::new(z(), wires![3, 1], wires![4]),
        ],
        wires![0, 1],
        wires![2, 4],
    );
    assert_eq!(
        Verdict::Same,
        verdict(&left, &middle),
        "the left Frobenius law"
    );
    assert_eq!(
        Verdict::Same,
        verdict(&right, &middle),
        "the right Frobenius law"
    );
}

#[test]
fn a_bubble_is_a_plain_wire()
{
    let bubble = diagram(
        4,
        alloc::vec![
            Generator::new(z(), wires![0], wires![1, 2]),
            Generator::new(z(), wires![1, 2], wires![3]),
        ],
        wires![0],
        wires![3],
    );
    assert_eq!(Verdict::Same, verdict(&bubble, &plain_wire()), "speciality");
    let around = diagram(
        6,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(z(), wires![1], wires![2, 3]),
            Generator::new(z(), wires![2, 3], wires![4]),
            Generator::new(value("g"), wires![4], wires![5]),
        ],
        wires![0],
        wires![5],
    );
    let composite = diagram(
        3,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("g"), wires![1], wires![2]),
        ],
        wires![0],
        wires![2],
    );
    assert_eq!(
        Verdict::Same,
        verdict(&around, &composite),
        "a bubble between two generators is their wire"
    );
}

#[test]
fn a_split_and_a_merge_around_a_generator_fuse_into_a_loop()
{
    let looped = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![0], wires![1, 2]),
            Generator::new(value("f"), wires![1], wires![3]),
            Generator::new(z(), wires![2, 3], wires![4]),
        ],
        wires![0],
        wires![4],
    );
    let fused = spider_normal_form(&looped).expect("a loop through a spider assembles");
    assert_eq!(
        fused.generators(),
        [
            Generator::new(z(), wires![0, 2], wires![1, 3]),
            Generator::new(value("f"), wires![1], wires![2]),
        ],
        "the spider feeds f and reads it back"
    );
    let canon = spider_canonicalize(&looped, budget()).expect("no tie");
    assert!(
        matches!(
            canon.form().to_wiring(),
            Err(WiringObstruction::DirectedCycle { .. })
        ),
        "the form of the loop is no wiring"
    );
    let relisted = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![4, 1], wires![2]),
            Generator::new(value("f"), wires![3], wires![1]),
            Generator::new(z(), wires![0], wires![3, 4]),
        ],
        wires![0],
        wires![2],
    );
    assert_eq!(
        Verdict::Same,
        verdict(&looped, &relisted),
        "the loop is one diagram in any presentation"
    );
}

#[test]
fn two_scalars_stay_two()
{
    let scalar = || {
        [
            Generator::new(z(), NONE, wires![0]),
            Generator::new(z(), wires![0], NONE),
        ]
    };
    let one = diagram(1, scalar().to_vec(), NONE, NONE);
    let mut pair = scalar().to_vec();
    pair.extend([
        Generator::new(z(), NONE, wires![1]),
        Generator::new(z(), wires![1], NONE),
    ]);
    let two = diagram(2, pair, NONE, NONE);
    let fused = spider_normal_form(&one).expect("a scalar assembles");
    assert_eq!(
        fused.generators(),
        [Generator::new(z(), NONE, NONE)],
        "a unit and a counit fuse into one scalar spider"
    );
    assert_eq!(
        decide(&one, &two),
        SpiderEquality::Distinct(DiagramDivergence::GeneratorCount {
            left: EdgeCount::from(1),
            right: EdgeCount::from(2),
        }),
        "two scalars are not one"
    );
}

#[test]
fn spiders_of_two_names_stay_apart()
{
    let mixed = diagram(
        5,
        alloc::vec![
            Generator::new(z(), wires![0, 1], wires![2]),
            Generator::new(x(), wires![2, 3], wires![4]),
        ],
        wires![0, 1, 3],
        wires![4],
    );
    let fused = spider_normal_form(&mixed).expect("two spiders assemble");
    assert_eq!(
        fused.generators().len(),
        2,
        "a wire between two names fuses nothing"
    );
    let one = diagram(
        4,
        alloc::vec![Generator::new(z(), wires![0, 1, 2], wires![3])],
        wires![0, 1, 2],
        wires![3],
    );
    assert_eq!(
        Verdict::Distinct,
        verdict(&mixed, &one),
        "the two names are two algebras"
    );
}

#[test]
fn a_removed_identity_fuses_its_neighbours()
{
    let between = diagram(
        6,
        alloc::vec![
            Generator::new(z(), wires![0, 1], wires![2]),
            Generator::new(x(), wires![2], wires![3]),
            Generator::new(z(), wires![3], wires![4, 5]),
        ],
        wires![0, 1],
        wires![4, 5],
    );
    let one = diagram(
        4,
        alloc::vec![Generator::new(z(), wires![0, 1], wires![2, 3])],
        wires![0, 1],
        wires![2, 3],
    );
    assert_eq!(
        Verdict::Same,
        verdict(&between, &one),
        "the identity goes, and its neighbours fuse"
    );
}

#[test]
fn fusion_is_idempotent()
{
    let fixtures = [
        diagram(
            5,
            alloc::vec![
                Generator::new(z(), wires![0, 1], wires![3]),
                Generator::new(z(), wires![3, 2], wires![4]),
            ],
            wires![0, 1, 2],
            wires![4],
        ),
        diagram(
            5,
            alloc::vec![
                Generator::new(z(), wires![0], wires![1, 2]),
                Generator::new(value("f"), wires![1], wires![3]),
                Generator::new(z(), wires![2, 3], wires![4]),
            ],
            wires![0],
            wires![4],
        ),
        diagram(
            6,
            alloc::vec![
                Generator::new(z(), wires![0, 1], wires![2]),
                Generator::new(x(), wires![2], wires![3]),
                Generator::new(z(), wires![3], wires![4, 5]),
            ],
            wires![0, 1],
            wires![4, 5],
        ),
    ];
    for fixture in &fixtures {
        let once = spider_normal_form(fixture).expect("a fused form assembles");
        let twice = spider_normal_form(&once.wiring).expect("and again");
        assert_eq!(once, twice, "a fused form is its own fused form");
    }
}

/// A split whose two legs feed two `f`s, which lead to `g` and to `h`: legs
/// that tie on their far end.
///
/// # Specification
/// trivial.
fn tied(targets: [Wire; 2]) -> Wiring
{
    diagram(
        7,
        alloc::vec![
            Generator::new(z(), wires![0], targets),
            Generator::new(value("f"), wires![1], wires![3]),
            Generator::new(value("f"), wires![2], wires![4]),
            Generator::new(value("g"), wires![3], wires![5]),
            Generator::new(value("h"), wires![4], wires![6]),
        ],
        wires![0],
        wires![5, 6],
    )
}

#[test]
fn tied_legs_have_one_form_in_every_order()
{
    assert_ne!(
        canonicalize(&tied(wires![1, 2])).form(),
        canonicalize(&tied(wires![2, 1])).form(),
        "the presentation canon reads the order of the tied legs"
    );
    let first = spider_canonicalize(&tied(wires![1, 2]), budget()).expect("two trials");
    let second = spider_canonicalize(&tied(wires![2, 1]), budget()).expect("two trials");
    assert_eq!(
        first.form(),
        second.form(),
        "the least of both orders is one form"
    );
    assert_eq!(first.trials(), SpiderTrials::from(2));
    assert_eq!(Ok(()), first.verify(&tied(wires![1, 2])));
    assert_eq!(Ok(()), second.verify(&tied(wires![2, 1])));
}

#[test]
fn leaves_of_one_label_are_no_tie()
{
    let leaves = |targets: [Wire; 3]| {
        diagram(
            4,
            alloc::vec![
                Generator::new(z(), wires![0], targets),
                Generator::new(value("t"), wires![1], NONE),
                Generator::new(value("t"), wires![2], NONE),
                Generator::new(value("t"), wires![3], NONE),
            ],
            wires![0],
            NONE,
        )
    };
    let canon = spider_canonicalize(&leaves(wires![1, 2, 3]), budget()).expect("one trial");
    assert_eq!(
        canon.trials(),
        SpiderTrials::from(1),
        "three leaves trade places freely"
    );
    assert_eq!(
        Verdict::Same,
        verdict(&leaves(wires![1, 2, 3]), &leaves(wires![3, 1, 2])),
        "the leaves are one diagram in any order"
    );
}

/// A split whose three legs each feed an `f` to the boundary: a tie of three.
///
/// # Specification
/// trivial.
fn three_way() -> Wiring
{
    diagram(
        7,
        alloc::vec![
            Generator::new(z(), wires![0], wires![1, 2, 3]),
            Generator::new(value("f"), wires![1], wires![4]),
            Generator::new(value("f"), wires![2], wires![5]),
            Generator::new(value("f"), wires![3], wires![6]),
        ],
        wires![0],
        wires![4, 5, 6],
    )
}

#[test]
fn the_budget_is_refused_before_any_trial()
{
    assert_eq!(
        spider_canonicalize(&three_way(), SpiderBudget::from(5)),
        Err(SpiderObstruction::BudgetExhausted {
            needed: SpiderTrials::from(6),
            budget: SpiderBudget::from(5),
        }),
        "a tie of three needs six trials"
    );
    let canon = spider_canonicalize(&three_way(), SpiderBudget::from(6)).expect("six trials");
    assert_eq!(canon.trials(), SpiderTrials::from(6));
}

#[test]
fn the_budget_is_shared_by_both_canons()
{
    assert_eq!(
        same_modulo_frobenius(&three_way(), &three_way(), SpiderBudget::from(11)),
        Err(SpiderObstruction::BudgetExhausted {
            needed: SpiderTrials::from(12),
            budget: SpiderBudget::from(11),
        }),
        "the right canon spends what the left one left"
    );
    assert!(matches!(
        same_modulo_frobenius(&three_way(), &three_way(), SpiderBudget::from(12)),
        Ok(SpiderEquality::Same(_))
    ));
}

#[test]
fn a_run_steps_through_every_order()
{
    let mut run = wires![0, 1, 2];
    let mut seen = alloc::vec![run];
    while next_order(&mut run) == Odometer::Stepped {
        seen.push(run);
    }
    assert_eq!(
        seen,
        [
            wires![0, 1, 2],
            wires![0, 2, 1],
            wires![1, 0, 2],
            wires![1, 2, 0],
            wires![2, 0, 1],
            wires![2, 1, 0],
        ],
        "six orders in lexicographic order"
    );
    assert_eq!(run, wires![0, 1, 2], "the carry restores the first order");
}

#[test]
fn the_decision_locates_where_two_forms_part()
{
    let merge = diagram(
        3,
        alloc::vec![Generator::new(z(), wires![0, 1], wires![2])],
        wires![0, 1],
        wires![2],
    );
    let split = diagram(
        3,
        alloc::vec![Generator::new(z(), wires![0], wires![1, 2])],
        wires![0],
        wires![1, 2],
    );
    assert_eq!(
        decide(&merge, &split),
        SpiderEquality::Distinct(DiagramDivergence::BoundaryArity {
            leg: Leg::Input,
            left: PortCount::from(2),
            right: PortCount::from(1),
        }),
        "the input arity parts first"
    );
    let then = |name: &str| {
        diagram(
            4,
            alloc::vec![
                Generator::new(z(), wires![0, 1], wires![2]),
                Generator::new(value(name), wires![2], wires![3]),
            ],
            wires![0, 1],
            wires![3],
        )
    };
    assert_eq!(
        decide(&then("f"), &then("g")),
        SpiderEquality::Distinct(DiagramDivergence::Generator { at: Edge::from(1) }),
        "the records part at the generator after the merge"
    );
}

#[test]
fn the_evidence_verifies_against_each_input()
{
    let listed = diagram(
        4,
        alloc::vec![
            Generator::new(z(), wires![0, 1], wires![2]),
            Generator::new(value("f"), wires![2], wires![3]),
        ],
        wires![0, 1],
        wires![3],
    );
    // One numbering, another listing: the first generator differs.
    let relisted = diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![2], wires![3]),
            Generator::new(z(), wires![1, 0], wires![2]),
        ],
        wires![0, 1],
        wires![3],
    );
    // Another numbering: the boundary differs before any generator.
    let renumbered = diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![3]),
            Generator::new(z(), wires![2, 1], wires![0]),
        ],
        wires![1, 2],
        wires![3],
    );
    let SpiderEquality::Same(shared) = decide(&listed, &relisted)
    else {
        panic!("two presentations of one diagram");
    };
    assert_eq!(Ok(()), shared.left().verify(&listed));
    assert_eq!(Ok(()), shared.right().verify(&relisted));
    assert_eq!(
        shared.left().verify(&relisted),
        Err(SpiderDefect::Generator { at: Edge::from(0) }),
        "the evidence of one listing is refused for another"
    );
    assert_eq!(
        Verdict::Same,
        verdict(&listed, &renumbered),
        "a renumbering is one diagram too"
    );
    assert_eq!(
        shared.left().verify(&renumbered),
        Err(SpiderDefect::Boundary),
        "and the evidence of one numbering is refused for another at the boundary"
    );
}
