//! A pattern a hundred thousand nodes deep, walked by every operation that
//! reads a whole pattern, on a stack a recursive walk would overflow.

use core::cmp::Ordering;

use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::Node;
use gandr_theory_cell_complexes::NodeRef;
use gandr_theory_cell_complexes::PatternSize;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::Pos;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::match_cmd;
use gandr_theory_cell_complexes::path_order_cmp;
use gandr_theory_cell_complexes::reduction_cmp;
use gandr_theory_cell_complexes::splice_cmd;
use gandr_theory_cell_complexes::subterm_at;
use quenchant_shape::shape::Maybe;

/// The depth of both halves of the deep pattern.
const DEPTH: usize = 100_000;

/// The stack the walk runs on: a recursive walk over [`DEPTH`] levels needs
/// several times more.
const SMALL_STACK: usize = 0x4_0000;

/// `Succ` applied `DEPTH` times to `base`.
///
/// # Specification
/// trivial.
fn succ_tower(base: ProdPat) -> ProdPat
{
    let mut prod = base;
    for _ in 0 .. DEPTH {
        prod = ProdPat::ctor("Succ", [prod]);
    }
    prod
}

/// `S⁻` framed `DEPTH` times around `end`.
///
/// # Specification
/// trivial.
fn frame_tower(end: ConsPat) -> ConsPat
{
    let mut cons = end;
    for _ in 0 .. DEPTH {
        cons = ConsPat::frame("S", cons);
    }
    cons
}

/// The whole walk: build, match, substitute, measure, read, splice, order and
/// drop the deep pattern.
///
/// # Specification
/// - panics: when any step disagrees with the shape it was built to have.
fn walk_the_deep_pattern()
{
    let pattern = CmdPat::cut(
        Polarity::Positive,
        succ_tower(ProdPat::meta("x")),
        frame_tower(ConsPat::meta("alpha")),
    );
    let ground = CmdPat::cut(
        Polarity::Positive,
        succ_tower(ProdPat::ctor("Zero", [])),
        frame_tower(ConsPat::top()),
    );

    let mut subst = Subst::new();
    assert!(
        bool::from(match_cmd(&pattern, &ground, &mut subst)),
        "the deep pattern matches its deep instance"
    );
    assert_eq!(
        ground,
        subst.apply_cmd(&pattern),
        "and the match reproduces it"
    );

    let holes: Vec<&MetaVar> = pattern.metavars().collect();
    assert_eq!(
        vec![&MetaVar::producer("x"), &MetaVar::consumer("alpha")],
        holes,
        "the two holes are found at the bottom of each half"
    );
    let half = DEPTH.checked_add(1).expect("the depth is small");
    let whole = half
        .checked_mul(2)
        .and_then(|both| both.checked_add(1))
        .expect("small");
    assert_eq!(
        PatternSize::from(whole),
        pattern.size(),
        "every node is counted once"
    );

    // The consumer half, then `DEPTH` frames down to the end.
    let bottom = Pos::from_steps(
        core::iter::once(PositionStep::from(1_usize))
            .chain(core::iter::repeat_n(PositionStep::from(0_usize), DEPTH)),
    );
    let Maybe::Present(read) = subterm_at(NodeRef::Cmd(&pattern), &bottom)
    else {
        panic!("the end of the spine is addressable");
    };
    assert_eq!(
        Node::Cons(ConsPat::meta("alpha")),
        read.to_node(),
        "the bottom of the spine is the consumer hole"
    );
    let spliced = splice_cmd(&pattern, &bottom, Node::Cons(ConsPat::top()))
        .expect("a consumer fills a consumer slot");
    assert_eq!(
        ground.consumer(),
        spliced.consumer(),
        "splicing ★ at the bottom grounds the spine"
    );

    let shallow = CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("x"),
        ConsPat::meta("alpha"),
    );
    assert_eq!(
        Ordering::Greater,
        reduction_cmp(&pattern, &shallow),
        "the deep pattern is larger and carries every hole of the shallow one"
    );
    assert_eq!(
        Ordering::Greater,
        path_order_cmp(&pattern, &shallow),
        "the path order agrees"
    );
    assert_eq!(
        Ordering::Less,
        path_order_cmp(&shallow, &pattern),
        "from either side"
    );

    drop(spliced);
    drop(subst);
    drop(ground);
    drop(pattern);
}

#[test]
fn a_deep_pattern_is_matched_ordered_and_dropped_on_a_small_stack()
{
    let walker = std::thread::Builder::new()
        .stack_size(SMALL_STACK)
        .spawn(walk_the_deep_pattern)
        .expect("the walking thread starts");
    walker.join().expect("the walk finishes on the small stack");
}
