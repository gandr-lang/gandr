//! Circuit rule instantiation: the two-redex block whose two
//! sequentializations are identified where the rule is applied.
//!
//! The applications are not fabricated. The rule is a circuit rule with a real
//! two-redex body, the two positions are read from that body's own occurrence
//! record, and the two cells arrive as the instantiation of its
//! rewrite-sorted ports; what is under test is the whole path from a written
//! block to an earned identification. The alphabet is the toy one, whose store
//! discharges the convexity conjunct, so every suite here hands the site a
//! supply point that refuses and shows it was never asked.
//!
//! - `an_instantiated_cong2_rule_earns_its_shift_witness` is the earning: two
//!   independent redexes, instantiated by two cells that share no seam, reach
//!   one composite and replay under both orders.
//! - `the_instantiated_applications_carry_the_records_positions` pins that the
//!   positions fired at are the occurrence record's, not the caller's.
//! - `a_genuinely_overlapping_instantiation_is_refused_at_the_application_site`
//!   is the refusal that matters: the same body, instantiated by an overlapping
//!   cell pair, is refused with the guard's own obstruction even though the two
//!   orders reach one term at this instance.
//! - `a_sequential_two_redex_body_is_refused_comparable_positions` refuses the
//!   body whose second redex consumes the first: that is `ρ then ρ′`.
//! - `a_reconvergent_body_resolves_both_occurrences_through_one_binding` keeps
//!   the environment condition off the body: a wire consumed twice is one
//!   rewrite at two positions, resolved through one binding.

use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_computads::CircuitShiftObstruction;
use gandr_theory_computads::ConvexityGrant;
use gandr_theory_computads::RewriteBinding;
use gandr_theory_computads::instantiate_two_redex_rule;
use gandr_theory_deep_inference::ShiftObstruction;
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitFrame;
use gandr_theory_levitation::CircuitNode;
use gandr_theory_levitation::CircuitRedex;
use gandr_theory_levitation::FrameHead;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::redex_occurrences;

use crate::fixture::RefusingSupply;
use crate::fixture::add_s_faces;
use crate::fixture::add_z_faces;
use crate::fixture::cong2_peak;
use crate::fixture::cong2_rule;
use crate::fixture::f_faces;
use crate::fixture::g_faces;
use crate::fixture::recorded_position;
use crate::fixture::rule_over;
use crate::fixture::run;
use crate::fixture::sequential_rule;
use crate::fixture::toy;

#[test]
fn an_instantiated_cong2_rule_earns_its_shift_witness()
{
    let mut store = CellStore::new();
    let f = store.insert(toy(f_faces()));
    let g = store.insert(toy(g_faces()));
    let shift = instantiate_two_redex_rule(
        &store,
        &cong2_rule(),
        &[RewriteBinding::new("p", f), RewriteBinding::new("q", g)],
        &cong2_peak(),
        &RefusingSupply,
    )
    .expect("two independent redexes, instantiated by two cells sharing no seam");
    assert_eq!(
        cong2_peak(),
        shift.witness.peak,
        "the witness records the term the rule was applied to"
    );
    assert_eq!(
        Toy::add(Toy::zero(), Toy::zero()),
        shift.witness.joins_at,
        "both sequentializations reach one composite"
    );
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        shift.witness.convexity,
        "the witness carries the warrant its convexity conjunct was skipped under"
    );
    assert_eq!(
        ConvexityGrant::Discharged,
        shift.convexity,
        "so the refusing supply point was never asked"
    );
    assert_eq!(
        shift.witness.joins_at,
        run(&store, &cong2_peak(), &shift.witness.first_then_second()),
        "p then q reaches the composite"
    );
    assert_eq!(
        shift.witness.joins_at,
        run(&store, &cong2_peak(), &shift.witness.second_then_first()),
        "and so does q then p"
    );
}

#[test]
fn the_instantiated_applications_carry_the_records_positions()
{
    // Nothing in the call names a position, so the two the witness fired at
    // can only have come from the block's own occurrence record.
    let mut store = CellStore::new();
    let f = store.insert(toy(f_faces()));
    let g = store.insert(toy(g_faces()));
    let rule = cong2_rule();
    let occurrences = redex_occurrences(&rule.body).expect("the cong2 wiring unfolds");
    let [ref left, ref right] = *occurrences
    else {
        panic!("the cong2 body unfolds to exactly two occurrences: {occurrences:?}");
    };
    let shift = instantiate_two_redex_rule(
        &store,
        &rule,
        &[RewriteBinding::new("p", f), RewriteBinding::new("q", g)],
        &cong2_peak(),
        &RefusingSupply,
    )
    .expect("the instantiated pair earns its witness");
    assert_eq!(
        (
            recorded_position::<ToyAlphabet>(left),
            recorded_position::<ToyAlphabet>(right)
        ),
        (
            shift.witness.first.at.clone(),
            shift.witness.second.at.clone()
        ),
        "the applications fired at the record's occurrences, in the source reading's order"
    );
    assert_eq!(
        (at![0], at![1]),
        (shift.witness.first.at, shift.witness.second.at),
        "which are the frame's two argument slots"
    );
    assert_eq!(
        (f, g),
        (shift.witness.first.cell, shift.witness.second.cell),
        "and each carries the cell its rewrite port was instantiated by"
    );
}

#[test]
fn a_genuinely_overlapping_instantiation_is_refused_at_the_application_site()
{
    // The same two-redex body, so the record's positions are the same
    // incomparable pair; only the instantiation changed.
    let mut store = CellStore::new();
    let z = store.insert(toy(add_z_faces()));
    let s = store.insert(toy(add_s_faces()));
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
        Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
    );
    let first = CellApp {
        cell: z,
        at: at![0],
    };
    let second = CellApp {
        cell: s,
        at: at![1],
    };
    assert_eq!(
        run(&store, &peak, &[first.clone(), second.clone()]),
        run(&store, &peak, &[second, first]),
        "the two orders do reach one term at this instance"
    );
    let refusal = instantiate_two_redex_rule(
        &store,
        &cong2_rule(),
        &[RewriteBinding::new("p", z), RewriteBinding::new("q", s)],
        &peak,
        &RefusingSupply,
    )
    .expect_err("an overlapping instantiation is refused at the application site");
    let CircuitShiftObstruction::Refused(ref obstruction) = refusal
    else {
        panic!("the refusal is the guard's, carried verbatim: {refusal:?}");
    };
    let ShiftObstruction::GenuineOverlap { ref overlap } = **obstruction
    else {
        panic!("the overlap conjunct refuses this instantiation: {obstruction:?}");
    };
    assert_eq!(
        (z, s),
        (overlap.left, overlap.right),
        "and it carries an overlap of exactly the two instantiating cells"
    );
}

#[test]
fn a_reconvergent_body_resolves_both_occurrences_through_one_binding()
{
    // `*p(-x, +w); *add(-w, -w, +z);`: one redex output feeding both arguments
    // of one frame. The wire is unfolded at each consumption, so the record
    // holds one rewrite at two positions — a repeated port in the body, not a
    // repeated binding.
    let body = CircuitBody::new(
        [
            CircuitNode::Redex(CircuitRedex::new(
                "p",
                FreeTerm::var("x"),
                FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
                "w",
            )),
            CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("add".into()),
                [FreeTerm::var("w"), FreeTerm::var("w")],
                "z",
            )),
        ],
        "z",
    );
    let rule = rule_over("dup", body);
    let occurrences = redex_occurrences(&rule.body).expect("the reconvergent wiring unfolds");
    let [ref left, ref right] = *occurrences
    else {
        panic!("a wire consumed twice is two occurrences: {occurrences:?}");
    };
    assert_eq!(
        (&left.rewrite, &right.rewrite),
        (&"p".into(), &"p".into()),
        "both occurrences are of the one rewrite the body applies"
    );
    let mut store = CellStore::new();
    let f = store.insert(toy(f_faces()));
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    let shift = instantiate_two_redex_rule(
        &store,
        &rule,
        &[RewriteBinding::new("p", f)],
        &peak,
        &RefusingSupply,
    )
    .expect("one binding serves both occurrences of its port");
    assert_eq!(
        (f, f),
        (shift.witness.first.cell, shift.witness.second.cell),
        "both applications carry the single cell the port is bound to"
    );
    assert_eq!(
        (
            recorded_position::<ToyAlphabet>(left),
            recorded_position::<ToyAlphabet>(right)
        ),
        (
            shift.witness.first.at.clone(),
            shift.witness.second.at.clone()
        ),
        "at the record's own two positions"
    );
    assert_ne!(
        shift.witness.first.at, shift.witness.second.at,
        "which stay distinct: reconvergence is one rewrite at two places"
    );
    assert_eq!(
        Toy::add(Toy::zero(), Toy::zero()),
        shift.witness.joins_at,
        "and the two orders reach one composite"
    );
}

#[test]
fn a_sequential_two_redex_body_is_refused_comparable_positions()
{
    // Both occurrences unfold at the frame's first argument, so the record's
    // two positions coincide: sequential composition, refused by the position
    // conjunct rather than identified.
    let mut store = CellStore::new();
    let f = store.insert(toy(f_faces()));
    let g = store.insert(toy(g_faces()));
    assert_eq!(
        Err(CircuitShiftObstruction::Refused(Box::new(
            ShiftObstruction::ComparablePositions {
                order: PositionOrder::Same,
            }
        ))),
        instantiate_two_redex_rule(
            &store,
            &sequential_rule(),
            &[RewriteBinding::new("p", f), RewriteBinding::new("q", g)],
            &cong2_peak(),
            &RefusingSupply,
        ),
        "the record's two positions coincide, and the position conjunct says so"
    );
}
