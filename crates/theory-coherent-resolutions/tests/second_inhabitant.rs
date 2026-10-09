//! The engines run over a second alphabet, unmodified.
//!
//! The workspace ships one production alphabet, so a claim that the
//! enumerator, the normalizer and completion are generic over the alphabet is
//! worth what a second inhabitant makes of it. These witnesses drive all three
//! over the toy alphabet, whose terms nest commands, and hold the budgeted
//! decline intact there.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CompletionBudget;
use gandr_theory_coherent_resolutions::CompletionCellBudget;
use gandr_theory_coherent_resolutions::CompletionOutcome;
use gandr_theory_coherent_resolutions::CompletionStepBudget;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::complete;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_coherent_resolutions::normalize;

/// (add-Z): `Add(Zero, x) ~> x`.
///
/// # Specification
/// trivial.
fn add_z() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::add(Toy::zero(), Toy::var("x")), Toy::var("x"))
}

/// (add-S): `Add(Succ(m), n) ~> Succ(Add(m, n))`.
///
/// # Specification
/// trivial.
fn add_s() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::succ(Toy::var("m")), Toy::var("n")),
        Toy::succ(Toy::add(Toy::var("m"), Toy::var("n"))),
    )
}

/// `Add(Zero, x) ~> Add(x, Zero)`: shares (add-Z)'s left-hand side and
/// diverges from it.
///
/// # Specification
/// trivial.
fn add_z_swapped() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::zero(), Toy::var("x")),
        Toy::add(Toy::var("x"), Toy::zero()),
    )
}

/// A completion budget from its three ceilings.
///
/// # Specification
/// trivial.
fn budget(
    steps: CompletionStepBudget,
    cells: CompletionCellBudget,
    norm: NormalizationBudget,
) -> CompletionBudget
{
    CompletionBudget::new(steps, cells, norm)
}

/// Every confluence entry carries the root seam, over an alphabet that has
/// interior command positions.
///
/// The sequent alphabet's only command position is the root, so the same
/// assertion there cannot fail. The toy alphabet nests commands, so interior
/// positions exist and a confluence entry must still carry the root, because
/// the confluence branch unifies whole left-hand sides and never descends. The
/// completeness exception rests on this: a confluence entry at an interior
/// position would be a self-overlap the diagonal exclusion would then drop.
#[test]
fn every_toy_confluence_entry_carries_the_root_seam()
{
    // Two rules whose left-hand sides unify at the root and whose right-hand
    // sides differ, so the pair survives the diagonal exclusion.
    let mut store: CellStore<ToyAlphabet> = CellStore::new();
    store.insert(add_z());
    store.insert(toy_cell(
        Toy::add(Toy::zero(), Toy::var("y")),
        Toy::succ(Toy::var("y")),
    ));
    let interior =
        ToyAlphabet::command_positions(&Toy::add(Toy::succ(Toy::var("m")), Toy::var("n")));
    assert!(
        interior.len() > 1_usize,
        "the toy alphabet has interior command positions, so the root is a real choice"
    );
    let root = ToyAlphabet::root_position();
    let mut seen = 0_usize;
    for overlap in enumerate_overlaps(&store) {
        if overlap.kind == OverlapKind::Confluence {
            seen = seen.saturating_add(1_usize);
            assert_eq!(
                root, overlap.seam,
                "a confluence overlap is a root overlap by construction"
            );
        }
    }
    assert!(
        seen > 0_usize,
        "the fixture produces confluence entries, so the check is not vacuous"
    );
}

#[test]
fn the_enumerator_finds_the_toy_composition_overlap()
{
    let mut store = CellStore::new();
    let zero_rule = store.insert(add_z());
    let succ_rule = store.insert(add_s());
    let overlaps = enumerate_overlaps(&store);
    let composition = overlaps
        .iter()
        .find(|o| o.kind == OverlapKind::Composition && o.left == succ_rule && o.right == zero_rule)
        .expect("add-S's right-hand subterm Add(m, n) unifies with add-Z's left-hand side");
    assert_eq!(
        Toy::add(Toy::succ(Toy::zero()), Toy::var("x")),
        composition.peak,
        "the superposition instantiates m to Zero"
    );
    let composite = composition.composite(&store).expect("the composite exists");
    assert_eq!(
        Toy::succ(Toy::var("x")),
        composite,
        "the fused right-hand side drops the intermediate Add"
    );
    let (_fused, tracelet) = derive_fused(composition, &mut store).expect("the fused cell derives");
    assert!(
        bool::from(tracelet.replay(&store)),
        "the toy fused≡two-step certificate replays"
    );
}

#[test]
fn the_normalizer_runs_over_the_toy_alphabet()
{
    let mut store = CellStore::new();
    store.insert(add_z());
    store.insert(add_s());
    let term = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let out = normalize(&store, &term, NormalizationBudget::from(16_usize));
    assert_eq!(Toy::succ(Toy::zero()), out.normal, "add-S then add-Z");
    assert_eq!(2_usize, out.path.len(), "two steps");
    assert!(!bool::from(out.exhausted), "a normal form was reached");
}

#[test]
fn completion_orients_and_certifies_over_the_toy_alphabet()
{
    // `Add(Zero, x) ~> x` and `Add(Zero, x) ~> Add(x, Zero)` share a left-hand
    // side: a critical pair whose reducts diverge.
    let mut store = CellStore::new();
    store.insert(add_z());
    store.insert(add_z_swapped());
    let outcome = complete(
        store,
        budget(
            CompletionStepBudget::from(64_usize),
            CompletionCellBudget::from(16_usize),
            NormalizationBudget::from(64_usize),
        ),
    );
    let CompletionOutcome::Completed {
        store: completed,
        derived,
        certificates,
    } = outcome
    else {
        panic!("the toy system completes within budget");
    };
    assert_eq!(
        1_usize,
        derived.len(),
        "the divergence oriented into one new cell"
    );
    assert!(
        !certificates.is_empty(),
        "the derived cell joined the original pair"
    );
    assert!(
        certificates
            .iter()
            .all(|tracelet| bool::from(tracelet.replay(&completed))),
        "every toy certificate replays"
    );
}

#[test]
fn a_starved_toy_budget_declines_with_pending()
{
    let mut store = CellStore::new();
    store.insert(add_z());
    store.insert(add_z_swapped());
    let outcome = complete(
        store,
        budget(
            CompletionStepBudget::from(0_usize),
            CompletionCellBudget::from(16_usize),
            NormalizationBudget::from(64_usize),
        ),
    );
    let CompletionOutcome::Declined { pending, .. } = outcome
    else {
        panic!("a zero step budget must decline");
    };
    assert!(!pending.is_empty(), "the pending overlaps are carried");
}
