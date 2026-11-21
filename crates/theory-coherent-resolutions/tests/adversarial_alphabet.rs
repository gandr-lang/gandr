//! An adversarial alphabet, read through the rewriting step.
//!
//! An alphabet whose splice disturbs a sibling it was not asked about shows
//! that through the step rather than being caught by a shape check the engine
//! does not perform: the engine reads positions and cell contents, and trusts
//! the splice law for everything else.

use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::NonLocalSplice;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::lying_cell;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::rewrite_at;
use quenchant_shape::shape::Maybe;

#[test]
fn the_non_local_splice_alphabet_disturbs_a_sibling_it_was_not_asked_about()
{
    // The lie is in `splice_cmd_at`, so it shows through `rewrite_at`: firing
    // at `[0]` also resets `[1]`, which the honest alphabet leaves as it was.
    let peel = lying_cell::<NonLocalSplice>(Toy::succ(Toy::zero()), Toy::zero());
    let honest_peel = toy_cell(Toy::succ(Toy::zero()), Toy::zero());
    let term = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    let at_left = ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
    assert_eq!(
        Maybe::Present(Toy::add(Toy::zero(), Toy::succ(Toy::zero()))),
        rewrite_at(&honest_peel, &term, &at_left),
        "the honest splice touches only the position it was given"
    );
    assert_eq!(
        Maybe::Present(Toy::add(Toy::zero(), Toy::add(Toy::zero(), Toy::zero()))),
        rewrite_at(&peel, &term, &at_left),
        "and the non-local one resets the sibling as well"
    );
}
