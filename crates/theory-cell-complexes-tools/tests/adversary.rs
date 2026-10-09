//! Each adversary lies about exactly one thing.
//!
//! These witnesses hold the fixture itself rather than any engine above it: an
//! adversary that drifted into lying about a second law would silently change
//! what every adversarial test over it measures, and nothing else in the tree
//! would notice.

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::IncomparablePositions;
use gandr_theory_cell_complexes_tools::Lying;
use gandr_theory_cell_complexes_tools::NonLocalSplice;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToyPos;

/// The toy position of `path`.
///
/// # Specification
/// trivial.
fn at(path: &[PositionStep]) -> ToyPos
{
    ToyAlphabet::position_at_path(path)
}

/// The delegating wrapper differs from the honest alphabet on the one law it
/// is built to break, and on nothing else asked here.
#[test]
fn the_incomparable_wrapper_breaks_the_position_order_and_keeps_the_match()
{
    let outer = at(&[]);
    let inner = at(&[PositionStep::from(0_usize)]);
    assert_eq!(
        PositionOrder::Encloses,
        ToyAlphabet::position_order(&outer, &inner),
        "the honest alphabet orders a nesting pair"
    );
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<IncomparablePositions> as CellAlphabet>::position_order(&outer, &inner),
        "the wrapper calls the same pair incomparable, which is its whole lie"
    );
    let pattern = Toy::add(Toy::var("x"), Toy::zero());
    let ground = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let mut honest = <ToyAlphabet as CellAlphabet>::Subst::default();
    let mut lying = <Lying<IncomparablePositions> as CellAlphabet>::Subst::default();
    assert_eq!(
        ToyAlphabet::match_cmd(&pattern, &ground, &mut honest),
        <Lying<IncomparablePositions> as CellAlphabet>::match_cmd(&pattern, &ground, &mut lying),
        "and it delegates the match decision unchanged"
    );
    assert_eq!(
        ToyAlphabet::apply_subst(&honest, &pattern),
        <Lying<IncomparablePositions> as CellAlphabet>::apply_subst(&lying, &pattern),
        "with the same bindings behind it"
    );
}

/// The non-local splice resets a binary root's other child and nothing else:
/// a unary root has no sibling to disturb, and reading is the honest read.
#[test]
fn the_non_local_splice_wrapper_breaks_the_splice_and_keeps_the_read()
{
    let left = at(&[PositionStep::from(0_usize)]);
    let binary = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    assert_eq!(
        Ok(Toy::add(Toy::zero(), Toy::succ(Toy::zero()))),
        ToyAlphabet::splice_cmd_at(&binary, &left, Toy::zero()),
        "the honest splice touches only the position it was given"
    );
    assert_eq!(
        Ok(Toy::add(Toy::zero(), Toy::add(Toy::zero(), Toy::zero()))),
        <Lying<NonLocalSplice> as CellAlphabet>::splice_cmd_at(&binary, &left, Toy::zero()),
        "the wrapper also resets the sibling, which is its whole lie"
    );
    let unary = Toy::succ(Toy::succ(Toy::zero()));
    assert_eq!(
        ToyAlphabet::splice_cmd_at(&unary, &left, Toy::zero()),
        <Lying<NonLocalSplice> as CellAlphabet>::splice_cmd_at(&unary, &left, Toy::zero()),
        "a unary root has no sibling, so the two splices agree there"
    );
    assert_eq!(
        ToyAlphabet::subterm_cmd_at(&binary, &left),
        <Lying<NonLocalSplice> as CellAlphabet>::subterm_cmd_at(&binary, &left),
        "and the read at the spliced position is the honest one"
    );
}
