//! The overlap enumerator, its completeness exception, and the support
//! relation that schedules overlaps into independent batches.

use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::HoleName;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_cell_complexes::frame_defining_cell;
use gandr_theory_coherent_resolutions::CertificateIndex;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::OverlapSupport;
use gandr_theory_coherent_resolutions::PeakLegs;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_coherent_resolutions::overlaps_between;
use gandr_theory_coherent_resolutions::peak_legs;
use quenchant_shape::shape::Maybe;

use crate::fixture::add_s;
use crate::fixture::ground_rule;
use crate::fixture::independent_rule_clusters;
use crate::fixture::schematic_rule;

/// The frame-defining cell (id 0) and (add-S) (id 1).
///
/// # Specification
/// trivial.
fn frame_and_add() -> (CellStore, CellId, CellId)
{
    let mut store = CellStore::new();
    let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
    let add = store.insert(add_s());
    (store, frame, add)
}

/// The composition of the frame-defining cell into (add-S).
///
/// # Specification
/// - panics: when the store has no such overlap, which is a fixture defect.
fn frame_into_add(
    store: &CellStore,
    frame: CellId,
    add: CellId,
) -> Overlap
{
    enumerate_overlaps(store)
        .into_iter()
        .find(|o| o.kind == OverlapKind::Composition && o.left == frame && o.right == add)
        .expect("the frame's right-hand side ⟨Succ(v) | β⟩ unifies with add-S's left-hand side")
}

/// The ground and schematic rule over `f` with the different right-hand sides
/// `p(α)` and `q(α)`: a genuine critical pair.
///
/// # Specification
/// trivial.
fn critical_pair() -> CellStore
{
    let f = Sym::new("f");
    let mut store = CellStore::new();
    store.insert(ground_rule(
        &Sym::new("Zero"),
        &f,
        ConsPat::op("p", [], ConsPat::meta("alpha")),
    ));
    store.insert(schematic_rule(
        &HoleName::new("x"),
        &f,
        ConsPat::op("q", [], ConsPat::meta("alpha")),
    ));
    store
}

/// The confluence entries of the store's overlap family, in its order.
///
/// # Specification
/// trivial.
fn confluence_family(store: &CellStore) -> Vec<Overlap>
{
    enumerate_overlaps(store)
        .into_iter()
        .filter(|overlap| overlap.kind == OverlapKind::Confluence)
        .collect()
}

/// The position of one overlap in an enumerated family.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct InputPosition(usize);

/// The input position of each batch member, per batch.
///
/// # Specification
/// - panics: when a batch member is not in `overlaps`, which the batching
///   contract excludes.
fn batch_input_positions(
    overlaps: &[Overlap],
    batches: &[Vec<Overlap>],
) -> Vec<Vec<InputPosition>>
{
    batches
        .iter()
        .map(|batch| {
            batch
                .iter()
                .map(|member| {
                    overlaps
                        .iter()
                        .position(|candidate| candidate == member)
                        .map(InputPosition)
                        .expect("every batch member came from the input family")
                })
                .collect()
        })
        .collect()
}

#[test]
fn the_frame_and_add_cells_compose_into_the_commutation_cell()
{
    // (Succ⁻-def) then (add-S) compose into the commutation cell
    // ⟨w | Succ⁻(add(n; α))⟩ ~> ⟨w | add(n; Succ⁻(α))⟩.
    let (store, frame, add) = frame_and_add();
    let composition = frame_into_add(&store, frame, add);
    // The unifier identifies the frame's `v` with add-S's `m`; which name
    // survives is the unifier's choice, so the expected terms read it back.
    let w = composition.peak.producer().clone();
    assert!(
        w == ProdPat::meta("v") || w == ProdPat::meta("m"),
        "the peak's producer is the identified hole"
    );
    let expected_peak = CmdPat::cut(
        Polarity::Positive,
        w.clone(),
        ConsPat::frame(
            "Succ",
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        ),
    );
    assert_eq!(
        expected_peak, composition.peak,
        "the peak feeds a Succ⁻ frame into add"
    );
    let expected_composite = CmdPat::cut(
        Polarity::Positive,
        w,
        ConsPat::op(
            "add",
            [ProdPat::meta("n")],
            ConsPat::frame("Succ", ConsPat::meta("alpha")),
        ),
    );
    assert_eq!(
        Ok(expected_composite),
        composition.composite(&store),
        "the composite drops the intermediate Succ, leaving add with the frame pushed in"
    );
}

/// The peak the enumeration omits has legs that coincide.
///
/// The witness for the exception in the completeness claim: the enumeration
/// omits the root diagonal, entitled to only because that peak joins in no
/// steps. This computes both contractions of the diagonal peak and compares
/// them, so a diagonal peak with distinct reducts refutes the exception.
#[test]
fn the_suppressed_diagonal_peak_has_coinciding_legs()
{
    let cell = add_s();
    let (renamed_lhs, renamed_rhs) =
        SequentAlphabet::rename_apart((cell.lhs(), cell.rhs()), (cell.lhs(), cell.rhs()));
    let mut unifier = Subst::new();
    assert!(
        bool::from(SequentAlphabet::unify_cmd(
            cell.lhs(),
            &renamed_lhs,
            &mut unifier
        )),
        "a pattern unifies with its own renaming apart"
    );
    assert_eq!(
        PeakLegs::Coincide,
        peak_legs::<SequentAlphabet>(&unifier, cell.rhs(), &renamed_rhs),
        "the diagonal peak's two contractions are the same term"
    );
}

/// A genuine critical pair's legs differ under the same decision.
///
/// Without this the coincidence witness is satisfied by a decision that
/// answers `Coincide` for everything.
#[test]
fn a_real_critical_pair_has_differing_legs()
{
    let store = critical_pair();
    let confluence = enumerate_overlaps(&store)
        .into_iter()
        .find(|o| o.kind == OverlapKind::Confluence)
        .expect("the two rules overlap at the root");
    let Maybe::Present(left) = store.get(confluence.left)
    else {
        panic!("the left cell is stored");
    };
    assert_eq!(
        PeakLegs::Differ,
        peak_legs::<SequentAlphabet>(
            &confluence.unifier,
            left.rhs(),
            confluence.right_renamed().rhs()
        ),
        "a real critical pair's two contractions are different terms"
    );
}

/// Every confluence entry carries the root seam.
///
/// Structural over the sequent alphabet, whose only command position is the
/// root; the separating form is
/// `tests::second_inhabitant::every_toy_confluence_entry_carries_the_root_seam`,
/// over an alphabet with interior positions.
#[test]
fn every_confluence_entry_carries_the_root_seam()
{
    let store = critical_pair();
    let root = SequentAlphabet::root_position();
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
fn overlaps_are_a_deterministic_family()
{
    let (store, _frame, _add) = frame_and_add();
    let first = enumerate_overlaps(&store);
    let second = enumerate_overlaps(&store);
    assert!(!first.is_empty(), "the fixture overlaps");
    assert_eq!(first, second, "enumeration is deterministic");
}

#[test]
fn the_pair_query_agrees_with_the_store_wide_family()
{
    // The pair query is the store-wide sweep's inner step, so reassembling it
    // pair by pair reproduces the family exactly, the omitted diagonal
    // included.
    let (store, _frame, _add) = frame_and_add();
    let mut reassembled = Vec::new();
    for (left_id, left) in store.iter() {
        for (right_id, right) in store.iter() {
            reassembled.extend(overlaps_between((left_id, left), (right_id, right)));
        }
    }
    assert_eq!(
        enumerate_overlaps(&store),
        reassembled,
        "the pair query is the store-wide family, one ordered pair at a time"
    );
    assert!(
        !reassembled.is_empty(),
        "and the fixture is one that actually overlaps"
    );
}

#[test]
fn overlap_support_batches_are_pairwise_independent()
{
    let store = independent_rule_clusters();
    let support = OverlapSupport::from_store(&store);
    let overlaps = confluence_family(&store);
    let batches = support.batches(&overlaps);
    // Three two-rule clusters over three disjoint operations: the family
    // alternates between the clusters, so a batch takes one overlap from each.
    assert_eq!(
        6_usize,
        overlaps.len(),
        "each cluster's critical pair is enumerated in both directions"
    );
    let mut endpoints: Vec<CellId> = overlaps
        .iter()
        .flat_map(|overlap| [overlap.left, overlap.right])
        .collect();
    endpoints.sort_unstable();
    endpoints.dedup();
    assert_eq!(
        6_usize,
        endpoints.len(),
        "six distinct cells take part in an overlap"
    );
    assert!(
        overlaps.iter().enumerate().all(|(index, left)| {
            overlaps
                .iter()
                .skip(index.saturating_add(1_usize))
                .all(|right| left != right)
        }),
        "the family carries no duplicate entry, so an input position is exact"
    );
    assert_eq!(
        2_usize,
        batches.len(),
        "the six overlaps schedule into exactly two batches"
    );
    assert!(
        batches.iter().all(|batch| batch.len() == 3_usize),
        "each batch holds one overlap from each of the three clusters, so a serialized \
         partition fails here"
    );
    // The flatten identity as positions rather than a length sum: a length
    // sum survives a partition that drops one overlap and duplicates another.
    let positions = batch_input_positions(&overlaps, &batches);
    assert_eq!(
        vec![
            vec![
                InputPosition(0_usize),
                InputPosition(2_usize),
                InputPosition(4_usize)
            ],
            vec![
                InputPosition(1_usize),
                InputPosition(3_usize),
                InputPosition(5_usize)
            ],
        ],
        positions,
        "first-fit takes the family's first, third and fifth members, then its second, \
         fourth and sixth, each batch in input order"
    );
    assert!(
        batches.iter().all(|batch| {
            batch.iter().enumerate().all(|(index, left)| {
                batch
                    .iter()
                    .skip(index.saturating_add(1_usize))
                    .all(|right| bool::from(support.overlaps_are_independent(left, right)))
            })
        }),
        "every batch is pairwise independent under the support relation"
    );
    assert!(
        overlaps.iter().enumerate().all(|(index, left)| {
            overlaps
                .iter()
                .skip(index.saturating_add(1_usize))
                .filter(|right| [right.left, right.right].contains(&left.left))
                .all(|right| !bool::from(support.overlaps_are_independent(left, right)))
        }),
        "two overlaps of one cluster are never independent, so batching is not vacuous"
    );
}

#[test]
fn overlap_support_is_symmetric_and_certificate_memoized()
{
    let (mut store, frame, add) = frame_and_add();
    let support = OverlapSupport::from_store(&store);
    assert!(
        !bool::from(support.independent(frame, add)),
        "the frame and add cells overlap, so they are not independent"
    );
    assert!(
        !bool::from(support.independent(add, frame)),
        "and the query answers the same in the other argument order"
    );
    let composition = frame_into_add(&store, frame, add);
    let (_fused, certificate) =
        derive_fused(&composition, &mut store).expect("the certificate is derived");
    let step_of = |cell: CellId| {
        certificate
            .path_a
            .iter()
            .find(|step| step.cell == cell)
            .cloned()
            .expect("the certificate's two-step path fires the cell")
    };
    let mut frame_certificate = certificate.clone();
    frame_certificate.path_a = vec![step_of(frame)];
    frame_certificate.path_b = vec![step_of(frame)];
    let mut add_certificate = certificate.clone();
    add_certificate.path_a = vec![step_of(add)];
    add_certificate.path_b = vec![step_of(add)];
    let mut primitive = OverlapSupport::from_store(&store);
    let _keys = primitive.add_certificates(&[frame_certificate, add_certificate]);
    assert!(
        !bool::from(primitive.certificates_independent(
            CertificateIndex::from(0_usize),
            CertificateIndex::from(1_usize)
        )),
        "distinct certificates inherit dependence from their cells"
    );

    let mut support = OverlapSupport::from_store(&store);
    let first_keys = support.add_certificates(core::slice::from_ref(&certificate));
    let second_keys = support.add_certificates(core::slice::from_ref(&certificate));
    assert_eq!(
        (
            CertificateIndex::from(0_usize),
            CertificateIndex::from(1_usize)
        ),
        first_keys,
        "the first insertion takes the opening key"
    );
    assert_eq!(
        (
            CertificateIndex::from(1_usize),
            CertificateIndex::from(2_usize)
        ),
        second_keys,
        "and the second takes the next one"
    );
    for key in [0_usize, 1_usize] {
        assert!(
            !bool::from(support.certificates_independent(
                CertificateIndex::from(key),
                CertificateIndex::from(key)
            )),
            "a certificate is never independent of itself"
        );
    }
    assert!(
        !bool::from(support.certificates_independent(
            CertificateIndex::from(1_usize),
            CertificateIndex::from(0_usize)
        )),
        "identical certificates from separate calls depend on each other, in either order"
    );

    let mut batched = OverlapSupport::from_store(&store);
    let batched_keys = batched.add_certificates(&[certificate.clone(), certificate.clone()]);
    let mut split = OverlapSupport::from_store(&store);
    let split_first = split.add_certificates(core::slice::from_ref(&certificate));
    let split_second = split.add_certificates(core::slice::from_ref(&certificate));
    assert_eq!(
        (
            CertificateIndex::from(0_usize),
            CertificateIndex::from(2_usize)
        ),
        batched_keys,
        "one batched call takes the whole half-open key range"
    );
    assert_eq!(
        (first_keys, second_keys),
        (split_first, split_second),
        "and splitting it hands out the same range in two pieces"
    );
    assert_eq!(
        batched, split,
        "support is invariant under call partitioning"
    );
}
