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
use gandr_theory_coherent_resolutions::Joinability;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::complete;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_coherent_resolutions::interior_overlaps_between;
use gandr_theory_coherent_resolutions::join_critical_pairs;
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

/// Every confluence entry of the store-wide sweep carries the root seam, over
/// an alphabet that has interior command positions.
///
/// The sequent alphabet's only command position is the root, so the same
/// assertion there cannot fail. The toy alphabet nests commands, so interior
/// positions exist and a sweep entry must still carry the root, because the
/// sweep's confluence branch unifies whole left-hand sides and never descends;
/// the interior family is a second pair query, which the sweep's consumers do
/// not schedule.
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
fn interior_overlaps_reach_below_the_root_and_join_or_diverge()
{
    // A successor below an addition, overlapped by a rule on that successor:
    // the peak `Add(Succ(Zero), y)` reduces to `Zero` at the root and to
    // `Add(Zero, y)` at the seam, and no rule joins them.
    let peel = toy_cell(
        Toy::add(Toy::succ(Toy::var("x")), Toy::var("y")),
        Toy::var("x"),
    );
    let drop = toy_cell(Toy::succ(Toy::zero()), Toy::zero());
    let mut divergent: CellStore<ToyAlphabet> = CellStore::new();
    let peel_id = divergent.insert(peel.clone());
    let drop_id = divergent.insert(drop.clone());
    let seam = ToyAlphabet::position_at_path(&[0_usize.into()]);
    let family = interior_overlaps_between((peel_id, &peel), (drop_id, &drop));
    assert_eq!(1, family.len(), "one interior seam unifies");
    let entry = family.first().expect("the entry");
    assert_eq!(
        OverlapKind::Confluence,
        entry.kind,
        "an interior entry is a confluence"
    );
    assert_eq!(seam, entry.seam, "seamed at the successor");
    assert_eq!(
        Toy::add(Toy::succ(Toy::zero()), Toy::var("y")),
        entry.peak,
        "the peak"
    );
    assert_eq!(
        Ok(Toy::add(Toy::zero(), Toy::var("y"))),
        entry.right_reduct(),
        "the right reduct keeps the addition around the contractum"
    );
    assert!(
        interior_overlaps_between((peel_id, &peel), (peel_id, &peel)).is_empty(),
        "the rule does not overlap its own successor"
    );
    assert!(
        enumerate_overlaps(&divergent)
            .iter()
            .all(|overlap| overlap.kind != OverlapKind::Confluence),
        "the root sweep sees no confluence here"
    );
    assert_eq!(
        Joinability::Diverges {
            overlap: entry.clone(),
            left: Toy::zero(),
            right: Toy::add(Toy::zero(), Toy::var("y")),
        },
        join_critical_pairs(&divergent, NormalizationBudget::from(16_usize)),
        "the interior pair diverges"
    );
    // A rule overlapping itself one position down: both reducts are
    // `Succ(x')`, so the pair joins in no step past the two contractions.
    let halve = toy_cell(Toy::succ(Toy::succ(Toy::var("x"))), Toy::var("x"));
    let mut joinable: CellStore<ToyAlphabet> = CellStore::new();
    let halve_id = joinable.insert(halve);
    let Joinability::Joined(certificates) =
        join_critical_pairs(&joinable, NormalizationBudget::from(16_usize))
    else {
        panic!("the self-overlap joins");
    };
    assert_eq!(1, certificates.len(), "one interior pair, the diagonal");
    let certificate = certificates.first().expect("the certificate");
    assert_eq!(
        (halve_id, halve_id, seam.clone()),
        (
            certificate.overlap.left,
            certificate.overlap.right,
            certificate.overlap.seam.clone()
        ),
        "the cell against itself at the successor"
    );
    assert_eq!(
        Some(&seam),
        certificate.path_b.first().map(|step| &step.at),
        "the right path's first step fires at the seam"
    );
    assert_eq!(
        Some(&ToyAlphabet::root_position()),
        certificate.path_a.first().map(|step| &step.at),
        "the left path's first step fires at the root"
    );
    assert!(
        bool::from(certificate.replay(&joinable)),
        "the certificate replays"
    );
    // Left-hand sides whose interior positions are all metavariables overlap
    // nothing below the root.
    let project = toy_cell(Toy::add(Toy::var("a"), Toy::var("b")), Toy::var("a"));
    let mut flat: CellStore<ToyAlphabet> = CellStore::new();
    let project_id = flat.insert(project.clone());
    assert!(
        interior_overlaps_between((project_id, &project), (project_id, &project)).is_empty(),
        "variable positions are skipped"
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
