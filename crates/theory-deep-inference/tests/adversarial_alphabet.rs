//! The adversarial alphabets, read through the identity relations.
//!
//! Each wrapper breaks exactly one law the shift guard, the convexity discharge
//! or the content address relies on; these witnesses pin the lie and that it
//! is the only difference, so a refusal obtained over a lying alphabet is
//! attributable to it.

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes_tools::CollidingAddresses;
use gandr_theory_cell_complexes_tools::IncomparablePositions;
use gandr_theory_cell_complexes_tools::Lying;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::WithheldConvexity;
use gandr_theory_cell_complexes_tools::lying_cell;
use gandr_theory_cell_complexes_tools::reoriented_lying_cell;
use gandr_theory_coherent_resolutions::rewrite_at;
use gandr_theory_deep_inference::prim_address;

use crate::fixture::c_cell;

#[test]
fn the_incomparable_positions_alphabet_calls_a_nesting_pair_independent()
{
    // The lie and its exact shape: the honest alphabet reports the enclosing
    // pair, and this one the relation that licenses a shift. `Same` is
    // included, which matters: a primitive depends on its own repeat only
    // because `Same` is not `Incomparable`.
    let root = at![];
    let child = at![0];
    assert_eq!(
        PositionOrder::Encloses,
        ToyAlphabet::position_order(&root, &child),
        "the honest alphabet reports the nesting"
    );
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<IncomparablePositions> as CellAlphabet>::position_order(&root, &child),
        "and the lying one reports the pair as commutable"
    );
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<IncomparablePositions> as CellAlphabet>::position_order(&root, &root),
        "including a position against itself"
    );
}

#[test]
fn the_withheld_convexity_alphabet_declines_to_discharge_the_conjunct()
{
    let honest: CellStore<ToyAlphabet> = CellStore::new();
    let withheld: CellStore<Lying<WithheldConvexity>> = CellStore::new();
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        ToyAlphabet::convexity_discharge(&honest),
        "the toy alphabet discharges the conjunct for every store"
    );
    assert_eq!(
        ConvexityDischarge::ReCheckRequired,
        <Lying<WithheldConvexity> as CellAlphabet>::convexity_discharge(&withheld),
        "and this one withholds the warrant instead"
    );
}

#[test]
fn the_colliding_addresses_alphabet_gives_two_distinct_cells_one_address()
{
    // The lie's whole effect, isolated: the two cells differ, so a store holds
    // both, and their content addresses agree, so the factorization is asked
    // to hold two different primitives under one key.
    let given = lying_cell::<CollidingAddresses>(Toy::succ(Toy::zero()), Toy::zero());
    let derived = reoriented_lying_cell::<CollidingAddresses>(Toy::succ(Toy::zero()), Toy::zero());
    let root = at![];
    assert_ne!(
        given, derived,
        "the two cells are structurally distinct, so one store holds both"
    );
    assert_eq!(
        prim_address(&given, &root),
        prim_address(&derived, &root),
        "and the orientation tag they differ in is invisible to the digest"
    );
    // An honest orientation hash keeps them apart, which makes the collision
    // attributable to this alphabet rather than to the fixture.
    let honest_given = lying_cell::<IncomparablePositions>(Toy::succ(Toy::zero()), Toy::zero());
    let honest_derived =
        reoriented_lying_cell::<IncomparablePositions>(Toy::succ(Toy::zero()), Toy::zero());
    assert_ne!(
        prim_address(&honest_given, &root),
        prim_address(&honest_derived, &root),
        "an honest orientation hash separates them"
    );
}

#[test]
fn a_lying_alphabet_delegates_everything_it_does_not_lie_about()
{
    // Non-vacuity for every fixture built on a lying alphabet: the lie is the
    // only difference. Rewriting reads the subterm, firing permission,
    // matching, substitution and splicing at once, and the content address
    // reads the cell's whole hash.
    let cell = c_cell();
    let lying =
        lying_cell::<IncomparablePositions>(Toy::add(Toy::zero(), Toy::zero()), Toy::zero());
    let term = Toy::add(Toy::add(Toy::zero(), Toy::zero()), Toy::zero());
    let left = at![0];
    assert_eq!(
        rewrite_at(&cell, &term, &left),
        rewrite_at(&lying, &term, &left),
        "the two alphabets rewrite identically"
    );
    assert_eq!(
        prim_address(&cell, &left),
        prim_address(&lying, &left),
        "and one content address serves both, so the tie-break is shared"
    );
    assert_eq!(
        ToyAlphabet::skolemize(&Toy::var("x")),
        <Lying<IncomparablePositions> as CellAlphabet>::skolemize(&Toy::var("x")),
        "and skolemization is the toy alphabet's own, not a re-derivation"
    );
}
