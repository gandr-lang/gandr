//! The engine's certificates and batches, read back through the replay plan.
//!
//! Completion emits certificates and the overlap support schedules critical
//! pairs into batches; neither crate below this one can plan a replay, so the
//! check that both agree with their plans lives here, over the sequent
//! alphabet the engine's own suites use.

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellCount;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::HoleName;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_coherent_resolutions::CompletionBudget;
use gandr_theory_coherent_resolutions::CompletionCellBudget;
use gandr_theory_coherent_resolutions::CompletionOutcome;
use gandr_theory_coherent_resolutions::CompletionStatus;
use gandr_theory_coherent_resolutions::CompletionStepBudget;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::OverlapSupport;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::complete;
use gandr_theory_coherent_resolutions::confluence_tracelet;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_deep_inference::CausalDepth;
use gandr_theory_deep_inference::ReplayLevel;
use gandr_theory_deep_inference::ReplayPlan;
use gandr_theory_deep_inference::ReplayWitness;
use gandr_theory_deep_inference::normalize_certified;
use quenchant_shape::shape::Maybe;

use crate::fixture::run;

/// The position of one overlap in an enumerated family.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct InputPosition(usize);

/// The name-free shape of a completion outcome: whether it completed, the
/// cells it derived, how many certificates it emitted, and how large its store
/// ended up.
#[derive(Debug, Eq, PartialEq)]
struct CompletionShape
{
    /// Whether the run completed.
    completed: CompletionStatus,
    /// The cells the run derived, in derivation order.
    derived: Vec<CellId>,
    /// How many certificates the run emitted.
    certificates: usize,
    /// How large the run left its store.
    store: CellCount,
}

/// A positive surface rule `lhs ~> rhs`.
///
/// # Specification
/// trivial.
fn rule(
    lhs: CmdPat,
    rhs: CmdPat,
) -> Cell
{
    Cell::new(
        lhs,
        rhs,
        Orientation::PolarityDerived,
        CellProvenance::SurfaceRule,
    )
}

/// A rule `⟨K | op(label)⟩ ~> ⟨K | rhs⟩` over the nullary constructor `ctor`.
///
/// # Specification
/// trivial.
fn ground_rule(
    ctor: &Sym,
    op: &Sym,
    label: &HoleName,
    rhs: ConsPat,
) -> Cell
{
    rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor(ctor.clone(), []),
            ConsPat::op(op.clone(), [], ConsPat::meta(label.clone())),
        ),
        CmdPat::cut(Polarity::Positive, ProdPat::ctor(ctor.clone(), []), rhs),
    )
}

/// A rule `⟨binder | op(label)⟩ ~> ⟨binder | rhs⟩` over a producer
/// metavariable.
///
/// # Specification
/// trivial.
fn schematic_rule(
    binder: &HoleName,
    op: &Sym,
    label: &HoleName,
    rhs: ConsPat,
) -> Cell
{
    rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta(binder.clone()),
            ConsPat::op(op.clone(), [], ConsPat::meta(label.clone())),
        ),
        CmdPat::cut(Polarity::Positive, ProdPat::meta(binder.clone()), rhs),
    )
}

/// Two rules over `⟨Zero | f(α)⟩` with divergent right-hand sides: r1
/// `⟨Zero | f(α)⟩ ~> ⟨Zero | α⟩` and r2 `⟨x | f(α)⟩ ~> ⟨x | g(α)⟩`.
///
/// # Specification
/// trivial.
fn overlapping_rules() -> CellStore
{
    let (f, alpha) = (Sym::new("f"), HoleName::new("alpha"));
    let mut store = CellStore::new();
    store.insert(ground_rule(
        &Sym::new("Zero"),
        &f,
        &alpha,
        ConsPat::meta(alpha.clone()),
    ));
    store.insert(schematic_rule(
        &HoleName::new("x"),
        &f,
        &alpha,
        ConsPat::op("g", [], ConsPat::meta(alpha.clone())),
    ));
    store
}

/// Three two-rule clusters over the disjoint operations `f`, `g` and `h`,
/// followed by the `p`-rule every joined pair replays through.
///
/// Each cluster's ground and schematic rule overlap on their own operation
/// and on nothing else, since no right-hand side head (`p`, `q`, `r`) is a
/// left-hand side head except the `p`-rule's own, which pairs with no other
/// left-hand side; so the six critical pairs schedule into two batches of
/// three. The `f` cluster's reducts both reach `p` and then `r`, a two-step
/// derivation; the other two diverge by size. The labels are parameters so the
/// relabelled twin is the same call with different names.
///
/// # Specification
/// trivial.
fn labelled_clusters(
    label: &HoleName,
    binders: [&HoleName; 4],
) -> CellStore
{
    let [f_binder, g_binder, h_binder, p_binder] = binders;
    let reduced = || ConsPat::op("p", [], ConsPat::meta(label.clone()));
    let wrapped = || ConsPat::op("q", [], reduced());
    let (f, g, h, p) = (Sym::new("f"), Sym::new("g"), Sym::new("h"), Sym::new("p"));
    let mut store = CellStore::new();
    store.insert(ground_rule(&Sym::new("Zero"), &f, label, reduced()));
    store.insert(schematic_rule(f_binder, &f, label, reduced()));
    store.insert(ground_rule(&Sym::new("Nil"), &g, label, reduced()));
    store.insert(schematic_rule(g_binder, &g, label, wrapped()));
    store.insert(ground_rule(&Sym::new("Unit"), &h, label, reduced()));
    store.insert(schematic_rule(h_binder, &h, label, wrapped()));
    store.insert(schematic_rule(
        p_binder,
        &p,
        label,
        ConsPat::op("r", [], ConsPat::meta(label.clone())),
    ));
    store
}

/// The scheduling fixture.
///
/// # Specification
/// trivial.
fn independent_rule_clusters() -> CellStore
{
    labelled_clusters(&HoleName::new("alpha"), [
        &HoleName::new("x"),
        &HoleName::new("y"),
        &HoleName::new("z"),
        &HoleName::new("u"),
    ])
}

/// The scheduling fixture with every binder and metavariable label renamed and
/// every constructor and operation symbol held fixed.
///
/// # Specification
/// trivial.
fn relabelled_rule_clusters() -> CellStore
{
    labelled_clusters(&HoleName::new("gamma"), [
        &HoleName::new("w"),
        &HoleName::new("t"),
        &HoleName::new("s"),
        &HoleName::new("n"),
    ])
}

/// The confluence entries of the store's overlap family, in its order: the
/// entries the completion worklist batches.
///
/// # Specification
/// - ensures: exactly the enumerated confluence overlaps, in enumeration order;
///   composition entries are omitted.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the generated scheduling store and its alpha-renamed
///   twin. Ordered comparison with the filtered engine enumeration checks
///   completeness and order; exact batch coordinates reject retaining
///   compositions, dropping confluences or reordering the family.
/// - witness: `tests::oracle::overlap_support_batches_replay_along_their_plans`
#[spec(ensures: |output| enumerate_overlaps(store).iter()
    .filter(|overlap| overlap.kind == OverlapKind::Confluence).eq(output.iter()))]
fn confluence_family(store: &CellStore) -> Vec<Overlap>
{
    enumerate_overlaps(store)
        .into_iter()
        .filter(|overlap| overlap.kind == OverlapKind::Confluence)
        .collect()
}

/// The certificate of `overlap` when its reducts join within a generous
/// budget.
///
/// # Specification
/// - requires: a confluence overlap whose two identifiers belong to `store`.
/// - ensures: the engine's confluence certificate, when the pair joins.
/// - provides: the engine's reason when it does not.
/// - panics: when the overlap is refused outright, which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L1 — confluence entries emitted from the supplied fixture
///   store. Present certificates retain that overlap and replay to their join;
///   absent joins remain typed absences. Planned and sequential replay separate
///   a certificate for another peak from a genuine join of the selected pair.
/// - witness: `tests::oracle::overlap_support_batches_replay_along_their_plans`
#[spec(requires: overlap.kind == OverlapKind::Confluence
    && matches!(store.get(overlap.left), Maybe::Present(_))
    && matches!(store.get(overlap.right), Maybe::Present(_)), ensures: |output| match output {
        Maybe::Present(ref certificate) => certificate.overlap == *overlap && bool::from(certificate.replay(store)),
        Maybe::Absent(_) => true,
    })]
fn joined_certificate(
    overlap: &Overlap,
    store: &CellStore,
) -> Maybe<Tracelet, gandr_theory_coherent_resolutions::confluence_join::Absent>
{
    confluence_tracelet(overlap, store, NormalizationBudget::from(64_usize))
        .expect("a confluence overlap from the store is never refused")
}

/// The certified replay witness of one path of a certificate.
///
/// # Specification
/// - ensures: the certificate's raw peak and join are retained by the witness.
/// - panics: when the path does not replay to the certificate's join, which the
///   engine's certificate contract excludes.
///
/// # Adequacy
/// - hypothesis: L1 — each path of an engine-issued certificate. Raw-boundary
///   equality anchors the witness to that certificate; different recorded legs
///   and their independently replayed plans distinguish replacing one leg with
///   the other or certifying another boundary.
/// - witness: `tests::oracle::every_generated_certificate_matches_its_replay_plan`
#[spec(ensures: |output| output.peak() == &certificate.overlap.peak && output.joins_at() == &certificate.joins_at)]
fn certified(
    store: &CellStore,
    certificate: &Tracelet,
    path: &[gandr_theory_coherent_resolutions::CellApp],
) -> ReplayWitness
{
    normalize_certified(
        store,
        &certificate.overlap.peak,
        &certificate.joins_at,
        path,
    )
    .expect("every certificate path replays into a certified witness")
}

/// The certified replay witness of the fixture's leading critical pair.
///
/// # Specification
/// - ensures: a witness rooted at the first enumerated confluence peak.
/// - panics: when no leading pair exists or it does not join, which is a
///   fixture defect.
///
/// # Adequacy
/// - hypothesis: L1 — the scheduling store and its relabelled twin, each with a
///   joining leading critical pair. The first enumerated peak anchors
///   selection; the twin’s name-free schedule and own skolemized join reject
///   selecting a different cluster or retaining the original names.
/// - witness: `tests::oracle::a_relabelled_twin_schedules_and_replays_identically`
#[spec(ensures: |output| confluence_family(store).first()
    .is_some_and(|leading| output.peak() == &leading.peak))]
fn cluster_replay_witness(store: &CellStore) -> ReplayWitness
{
    let overlaps = confluence_family(store);
    let leading = overlaps
        .first()
        .expect("the fixture enumerates a leading confluence overlap");
    let Maybe::Present(certificate) = joined_certificate(leading, store)
    else {
        panic!("the leading cluster's critical pair joins");
    };
    certified(store, &certificate, &certificate.path_a)
}

/// Replay a plan under exactly its critical-path fuel.
///
/// # Specification
/// - ensures: the term reached by eager replay with exactly the plan's
///   critical-path fuel.
/// - panics: when the plan obstructs or declines its own critical path, which
///   the plan's contract excludes.
///
/// # Adequacy
/// - hypothesis: L2 — certified plans and their issuing stores. The result is
///   checked against sequential replay and against replay one dependency level
///   at a time; exact skolemized joins reject short fuel, skipped levels and
///   retaining raw metavariables.
/// - witness: `tests::oracle::overlap_support_batches_replay_along_their_plans`
/// - witness: `tests::oracle::every_generated_certificate_matches_its_replay_plan`
#[spec(ensures: |output| matches!(plan.replay_with_fuel(store, plan.critical_path()),
    Ok(Maybe::Present(ref reached)) if output == *reached))]
fn planned(
    plan: &ReplayPlan,
    store: &CellStore,
) -> CmdPat
{
    let replayed = plan
        .replay_with_fuel(store, plan.critical_path())
        .expect("critical-path fuel does not obstruct the plan");
    let Maybe::Present(term) = replayed
    else {
        panic!("critical-path fuel completes the plan");
    };
    term
}

/// The input position of each batch member, per batch.
///
/// # Specification
/// - requires: every batch member occurs in `overlaps`.
/// - ensures: the first input position of each member, preserving batch and
///   member order and each batch's cardinality.
/// - panics: when a batch member is not in `overlaps`, which the batching
///   contract excludes.
///
/// # Adequacy
/// - hypothesis: L3 — the generated overlap family, its scheduled batches and a
///   relabelled twin. Exact nested input coordinates and member equality
///   separate a flattened partition, dropped member or wrong input index
///   without depending on metavariable spelling.
/// - witness: `tests::oracle::overlap_support_batches_replay_along_their_plans`
/// - witness: `tests::oracle::a_relabelled_twin_schedules_and_replays_identically`
#[spec(requires: batches.iter().flatten().all(|member| overlaps.contains(member)),
    ensures: |output| output.len() == batches.len()
        && output.iter().zip(batches).all(|(positions, batch)| positions.len() == batch.len()
            && positions.iter().zip(batch).all(|(position, member)|
                overlaps.iter().position(|candidate| candidate == member) == Some(position.0))))]
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

/// The name-free shape of a batch partition: each member's cell endpoints and
/// overlap kind.
///
/// # Specification
/// trivial.
fn batch_shape(batches: &[Vec<Overlap>]) -> Vec<Vec<(CellId, CellId, OverlapKind)>>
{
    batches
        .iter()
        .map(|batch| {
            batch
                .iter()
                .map(|overlap| (overlap.left, overlap.right, overlap.kind))
                .collect()
        })
        .collect()
}

/// The name-free shape of one completion outcome.
///
/// # Specification
/// trivial.
fn completion_shape(outcome: &CompletionOutcome) -> CompletionShape
{
    CompletionShape {
        completed: outcome.is_completed(),
        derived: outcome.derived().to_vec(),
        certificates: outcome.certificates().len(),
        store: outcome.store().len(),
    }
}

/// A completion budget of `steps` critical pairs, `cells` cells and `norm`
/// steps per normalization.
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

#[test]
fn every_generated_certificate_matches_its_replay_plan()
{
    let outcome = complete(
        overlapping_rules(),
        budget(
            CompletionStepBudget::from(64_usize),
            CompletionCellBudget::from(16_usize),
            NormalizationBudget::from(64_usize),
        ),
    );
    let CompletionOutcome::Completed {
        store,
        certificates,
        ..
    } = outcome
    else {
        panic!("the generated fixture completes within budget");
    };
    assert_eq!(
        1_usize,
        certificates.len(),
        "the generated fixture emits its exact one-certificate family"
    );
    for certificate in certificates {
        let witness_a = certified(&store, &certificate, &certificate.path_a);
        let witness_b = certified(&store, &certificate, &certificate.path_b);
        assert_eq!(
            witness_a.joins_at(),
            witness_b.joins_at(),
            "both certificate paths reach the same join"
        );
        let plan_a = witness_a.replay_plan();
        let plan_b = witness_b.replay_plan();
        // The two legs are different derivations of one boundary, one firing
        // the left cell and whatever normalizes its reduct, the other the
        // right, so their plans schedule different cells; the invariant they
        // share is the join they replay to.
        assert_ne!(
            plan_a.levels(),
            plan_b.levels(),
            "the two certificate legs are different derivations of one boundary"
        );
        let planned_a = planned(&plan_a, &store);
        let planned_b = planned(&plan_b, &store);
        // A plan replays the skolemized peak, so it lands on the skolemized
        // join: the certified join still carries the critical pair's
        // metavariables.
        let join = SequentAlphabet::skolemize(&certificate.joins_at);
        assert_eq!(join, planned_a, "the plan of path_a replays to the join");
        assert_eq!(join, planned_b, "and so does the plan of path_b");
    }
}

#[test]
fn a_relabelled_twin_schedules_and_replays_identically()
{
    // The twin renames every binder and metavariable label and fixes every
    // constructor and operation symbol, so nothing name-free about the
    // schedule, the plan or the completion result may move.
    let store = independent_rule_clusters();
    let twin = relabelled_rule_clusters();
    assert_ne!(
        store, twin,
        "the twin is a different store, not the same one twice"
    );
    let overlaps = confluence_family(&store);
    let twin_overlaps = confluence_family(&twin);
    let batches = OverlapSupport::from_store(&store).batches(&overlaps);
    let twin_batches = OverlapSupport::from_store(&twin).batches(&twin_overlaps);
    assert_eq!(
        batch_shape(&batches),
        batch_shape(&twin_batches),
        "relabelling moves no batch boundary and no batch member"
    );
    assert_eq!(
        batch_input_positions(&overlaps, &batches),
        batch_input_positions(&twin_overlaps, &twin_batches),
        "relabelling moves no flatten position"
    );
    let witness = cluster_replay_witness(&store);
    let twin_witness = cluster_replay_witness(&twin);
    let plan = witness.replay_plan();
    let twin_plan = twin_witness.replay_plan();
    // A plan also carries the peak it starts from, the one part of it that
    // spells metavariable labels: the plans agree in their scheduling content
    // and differ as values, because the schedule is name-free and the
    // boundary is not.
    assert_eq!(
        plan.levels(),
        twin_plan.levels(),
        "the twin schedules the same cells at the same positions, level for level"
    );
    assert_eq!(
        plan.critical_path(),
        twin_plan.critical_path(),
        "the twin needs the same critical-path fuel"
    );
    assert_eq!(
        SequentAlphabet::skolemize(witness.joins_at()),
        planned(&plan, &store),
        "the fixture's plan replays to its own certified join"
    );
    assert_eq!(
        SequentAlphabet::skolemize(twin_witness.joins_at()),
        planned(&twin_plan, &twin),
        "the twin's plan replays to its own certified join"
    );
    let ceiling = budget(
        CompletionStepBudget::from(64_usize),
        CompletionCellBudget::from(64_usize),
        NormalizationBudget::from(64_usize),
    );
    assert_eq!(
        completion_shape(&complete(store, ceiling)),
        completion_shape(&complete(twin, ceiling)),
        "and completion derives the same cells and emits the same certificate family for both"
    );
}

#[test]
fn overlap_support_batches_replay_along_their_plans()
{
    // The batches the support relation schedules, carried through to replay:
    // every member whose critical pair joins is certified on both paths, and
    // each plan replays eagerly and level by level to the sequential replay's
    // term, which is the certified join.
    let store = independent_rule_clusters();
    let overlaps = confluence_family(&store);
    let batches = OverlapSupport::from_store(&store).batches(&overlaps);
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
        batch_input_positions(&overlaps, &batches),
        "the `p`-rule leaves the two batches of three the clusters schedule into"
    );
    let mut replayed = 0_usize;
    for member in batches.iter().flatten() {
        let Maybe::Present(certificate) = joined_certificate(member, &store)
        else {
            continue;
        };
        for path in [&certificate.path_a, &certificate.path_b] {
            let witness = certified(&store, &certificate, path);
            let plan = witness.replay_plan();
            assert_eq!(
                2_usize,
                plan.levels().len(),
                "the certified path schedules two dependency levels"
            );
            assert_eq!(
                CausalDepth::from(plan.levels().len()),
                plan.critical_path(),
                "the critical-path fuel is the number of dependency levels"
            );
            assert_eq!(
                witness.canonical_path().len(),
                plan.levels().iter().map(Vec::len).sum::<usize>(),
                "the plan schedules every certified step exactly once"
            );
            let start = SequentAlphabet::skolemize(witness.peak());
            let sequential = run(&store, &start, &witness.canonical_path());
            assert_eq!(
                sequential,
                planned(&plan, &store),
                "eager planned replay reaches the sequential replay's term"
            );
            let mut on_demand = start;
            for level in 0_usize .. plan.levels().len() {
                on_demand = plan
                    .replay_level(&store, &on_demand, ReplayLevel::from(level))
                    .expect("each dependency level replays on demand");
            }
            assert_eq!(
                sequential, on_demand,
                "per-level on-demand replay reaches the sequential replay's term"
            );
            assert_eq!(
                SequentAlphabet::skolemize(witness.joins_at()),
                sequential,
                "and that term is the certified join"
            );
            replayed = replayed.saturating_add(1_usize);
        }
    }
    assert_eq!(
        4_usize, replayed,
        "the `f` cluster joins in both batches, two paths each; the other clusters diverge"
    );
}

/// A consumer composes two certificates and certifies their exact combined
/// path.
#[test]
fn composed_tracelets_replay_and_normalize_through_the_public_algebra()
{
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_decomposition_spaces::compose_directed;
    use gandr_theory_decomposition_spaces::compose_invertible;
    use gandr_theory_decomposition_spaces::pathway::TargetLast;
    use gandr_theory_decomposition_spaces::pathway::target_occurs_only_last;

    let term =
        |name: &str| CmdPat::cut(Polarity::Positive, ProdPat::ctor(name, []), ConsPat::top());
    let mut store = CellStore::<SequentAlphabet>::new();
    let [ab, bc, cd, de] = [("A", "B"), ("B", "C"), ("C", "D"), ("D", "E")].map(|(from, to)| {
        store.insert(Cell::new(
            term(from),
            term(to),
            Orientation::CompletionDerived,
            CellProvenance::DerivedByCompletion,
        ))
    });
    let left_overlap = enumerate_overlaps(&store)
        .into_iter()
        .find(|overlap| {
            overlap.kind == OverlapKind::Composition && overlap.left == ab && overlap.right == bc
        })
        .expect("A to C seam");
    let right_overlap = enumerate_overlaps(&store)
        .into_iter()
        .find(|overlap| {
            overlap.kind == OverlapKind::Composition && overlap.left == cd && overlap.right == de
        })
        .expect("C to E seam");
    let (_, left) = derive_fused(&left_overlap, &mut store).expect("left certificate");
    let (_, right) = derive_fused(&right_overlap, &mut store).expect("right certificate");
    let directed = compose_directed(&left, &right, &store).expect("ground seam is acyclic");
    let invertible = compose_invertible(&left, &right);
    assert_eq!(directed, invertible);
    assert_eq!(directed.overlap.peak, term("A"));
    assert_eq!(directed.joins_at, term("E"));
    assert!(bool::from(directed.replay(&store)));
    let receipt = normalize_certified(
        &store,
        &directed.overlap.peak,
        &directed.joins_at,
        &directed.path_a,
    )
    .expect("composite certifies");
    let expected: Vec<_> = left.path_a.iter().chain(&right.path_a).cloned().collect();
    let (normal_form, order) = receipt.into_parts();
    assert_eq!(normal_form.canonical_path(), Maybe::Present(expected));
    assert_eq!(
        target_occurs_only_last(&order, de),
        TargetLast::HoldsUnderGuard
    );
}
