//! The atom-occurrence flow measured against its neighbours: where the
//! projection agrees with shift equivalence and replay-equivalence and where it
//! does not.
//!
//! The projection's resolution is the alphabet's address vocabulary, and a
//! sequent term has one command position, so the permutation-tile class is
//! empty there; the suite runs on the toy alphabet, whose terms nest commands.
//! Each strictness in the nesting has a fixture here rather than an argument:
//!
//! - the permutation tile's two legs project to one flow, because neither step
//!   touches an occurrence the other created;
//! - shift equivalence is strictly inside flow equality: the guard refuses a
//!   pair whose cells could interfere somewhere, and the projection reads the
//!   instance, where two disjoint images share nothing;
//! - flow equality is strictly inside replay-equivalence, which ignores the
//!   recorded paths;
//! - the containment needs the boundary: one cell fired on two unrelated
//!   instances of its left-hand side gives one flow over two boundaries.
//!
//! A fourth relation is measured beside them: the asynchronous-games
//! quotient, identification by a step-index bijection matching labels and
//! preserving dependence. It is not contained in flow equality (two families
//! separate it), and flow equality sits inside it on the discharge class, so
//! flow equality is strictly finer than the quotient.

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::replay_equivalent;
use gandr_theory_deep_inference::Flow;
use gandr_theory_deep_inference::FlowEnd;
use gandr_theory_deep_inference::FlowEquality;
use gandr_theory_deep_inference::FlowObstruction;
use gandr_theory_deep_inference::FlowVertexIndex;
use gandr_theory_deep_inference::cell_address;
use gandr_theory_deep_inference::derive_shift_equivalence;
use gandr_theory_deep_inference::flows_equal;
use gandr_theory_deep_inference::legs_flow_equal;
use gandr_theory_deep_inference::project_flow;
use gandr_theory_deep_inference::tracelet_flow;
use gandr_theory_deep_inference::tracelets_flow_equal;
use quenchant_shape::shape::Maybe;

use crate::fixture::add_s;
use crate::fixture::add_z;
use crate::fixture::c_cell;
use crate::fixture::cong2_body;
use crate::fixture::cong2_pair;
use crate::fixture::cong2_store;
use crate::fixture::f_cell;
use crate::fixture::fusion_fixture;
use crate::fixture::tracelet_over;

/// Every permutation of the flow's vertex indices, built by insertion.
///
/// The quotient check brute-forces the step-index bijection; no leg here
/// exceeds three steps, so the factorial enumeration is the honest
/// implementation rather than a matching algorithm.
///
/// # Specification
/// - ensures: every bijection of the vertex indices occurs exactly once,
///   including the empty bijection for an empty flow; no order is promised.
/// - panics: none apart from allocation failure.
///
/// # Adequacy
/// - hypothesis: L1 — finite fixture flows of zero through three vertices.
///   Bijection membership, pairwise uniqueness and factorial cardinality
///   validate completeness without assuming enumeration order. Positive
///   relabelings and negative causal shapes expose an omitted permutation or a
///   fabricated match.
/// - witness: `tests::flow::the_games_oracle_separates_missing_labels_and_causal_shapes`
/// - witness: `tests::flow::flow_equality_sits_inside_the_games_quotient_on_the_discharge_class`
#[spec(ensures: |output| {
    let count = flow.labels.len();
    (1_usize ..= count).try_fold(1_usize, usize::checked_mul) == Some(output.len())
        && output.iter().enumerate().all(|(ordinal, permutation)| {
            permutation.len() == count && !output[..ordinal].contains(permutation)
                && permutation.iter().enumerate().all(|(index, vertex)|
                    usize::from(*vertex) < count && !permutation[..index].contains(vertex))
        })
})]
fn index_permutations(flow: &Flow) -> Vec<Vec<FlowVertexIndex>>
{
    let mut permutations: Vec<Vec<FlowVertexIndex>> = vec![Vec::new()];
    for item in 0_usize .. flow.labels.len() {
        let item = FlowVertexIndex::from(item);
        let mut next: Vec<Vec<FlowVertexIndex>> = Vec::new();
        for permutation in &permutations {
            for slot in 0_usize ..= permutation.len() {
                let mut candidate = permutation.clone();
                candidate.insert(slot, item);
                next.push(candidate);
            }
        }
        permutations = next;
    }
    permutations
}

/// Whether `earlier` reaches `later` through the flow's vertex-to-vertex
/// threads: the dependence order the recorded leg induces, read off the
/// projection.
///
/// # Specification
/// - requires: both queried vertices and every vertex endpoint belong to the
///   flow's label list.
/// - ensures: strict reachability by vertex-to-vertex threads, ignoring
///   boundary ends; a vertex does not strictly precede itself.
/// - panics: none apart from allocation failure.
///
/// # Adequacy
/// - hypothesis: L3 — projected acyclic flows with isolated, serial and
///   branching vertices. Forward transitivity, reverse refusal and self-refusal
///   separate direct-edge-only lookup, reversed threads and reflexive
///   reachability; the predicate enforces index validity and the direct-edge
///   boundary.
/// - witness: `tests::flow::the_games_oracle_separates_missing_labels_and_causal_shapes`
#[spec(requires: usize::from(earlier) < flow.labels.len() && usize::from(later) < flow.labels.len()
    && flow.threads.iter().all(|thread| [thread.up, thread.lo].into_iter().all(|end| match end {
        FlowEnd::Vertex { vertex, .. } => usize::from(vertex) < flow.labels.len(),
        FlowEnd::Peak { .. } | FlowEnd::Join => true,
    })), ensures: |output| (earlier != later || !bool::from(output))
    && (earlier == later || !flow.threads.iter().any(|thread| matches!(
        (thread.up, thread.lo),
        (FlowEnd::Vertex { vertex: up, .. }, FlowEnd::Vertex { vertex: lo, .. })
            if up == earlier && lo == later
    )) || bool::from(output)))]
fn depends_before(
    flow: &Flow,
    earlier: FlowVertexIndex,
    later: FlowVertexIndex,
) -> FlowEquality
{
    let mut reached: Vec<FlowVertexIndex> = vec![earlier];
    let mut work: Vec<FlowVertexIndex> = vec![earlier];
    while let Some(current) = work.pop() {
        for thread in &flow.threads {
            let (FlowEnd::Vertex { vertex: up, .. }, FlowEnd::Vertex { vertex: lo, .. }) =
                (thread.up, thread.lo)
            else {
                continue;
            };
            if up == current && !reached.contains(&lo) {
                if lo == later {
                    return FlowEquality::from(true);
                }
                reached.push(lo);
                work.push(lo);
            }
        }
    }
    FlowEquality::from(false)
}

/// Whether two legs are identified by the asynchronous-games quotient: some
/// bijection on step indices matches the position-free cell content of each
/// matched pair and preserves the dependence order both ways.
///
/// `project_flow` emits `labels` in recorded order, so a flow carries the
/// leg's steps indexed exactly as the quotient reads them.
///
/// # Specification
/// - ensures: true exactly when the two vertex sets have a label-preserving
///   bijection preserving strict dependence in both directions. Peak anchors
///   and ports are not part of this relation.
/// - panics: none apart from allocation failure; vertex endpoints must be valid
///   as required by `depends_before`.
///
/// # Adequacy
/// - hypothesis: L3 — projected empty, differently labeled, serial and
///   branching flows, plus permutations of independent steps. The bijection
///   observer and separating counterexamples reject equality by label count
///   alone, one-way dependence preservation and treating empty flows as
///   unequal.
/// - witness: `tests::flow::the_games_oracle_separates_missing_labels_and_causal_shapes`
/// - witness: `tests::flow::the_games_quotient_identifies_a_tile_the_flow_declines_a_canonical_form`
#[spec(ensures: |output| bool::from(output) == (left.labels.len() == right.labels.len()
    && index_permutations(left).iter().any(|permutation| {
        permutation.iter().enumerate().all(|(index, mapped)|
            left.labels.get(index) == right.labels.get(usize::from(*mapped)))
            && permutation.iter().enumerate().all(|(first, mapped_first)|
                permutation.iter().enumerate().all(|(second, mapped_second)|
                    depends_before(left, FlowVertexIndex::from(first), FlowVertexIndex::from(second))
                        == depends_before(right, *mapped_first, *mapped_second)))
    })))]
fn games_equivalent(
    left: &Flow,
    right: &Flow,
) -> FlowEquality
{
    if left.labels.len() != right.labels.len() {
        return FlowEquality::from(false);
    }
    let count = left.labels.len();
    let matched = index_permutations(left).into_iter().any(|permutation| {
        let labels_match = left.labels.iter().enumerate().all(|(index, label)| {
            permutation
                .get(index)
                .and_then(|mapped| right.labels.get(usize::from(*mapped)))
                == Some(label)
        });
        let order_preserved = (0_usize .. count).all(|earlier| {
            (0_usize .. count).all(|later| {
                let mapped_earlier = permutation.get(earlier).copied().unwrap_or_default();
                let mapped_later = permutation.get(later).copied().unwrap_or_default();
                depends_before(
                    left,
                    FlowVertexIndex::from(earlier),
                    FlowVertexIndex::from(later),
                ) == depends_before(right, mapped_earlier, mapped_later)
            })
        });
        labels_match && order_preserved
    });
    FlowEquality::from(matched)
}

/// (dup): `x ~> Add(x, x)`, fired once so that its two copies can each carry
/// an (f) firing.
///
/// # Specification
/// trivial.
fn dup_cell() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::var("x"), Toy::add(Toy::var("x"), Toy::var("x")))
}

/// A one-step certificate over a boundary the caller chooses, both legs
/// recording `step`.
///
/// The carrier's overlap stands for the recorded peak and nothing else: these
/// fixtures are about which boundary a certificate records, not which critical
/// pair produced it.
///
/// # Specification
/// trivial.
fn one_step_certificate(
    peak: &Toy,
    joins_at: &Toy,
    step: &CellApp<ToyAlphabet>,
) -> Tracelet<ToyAlphabet>
{
    tracelet_over(peak, joins_at, vec![step.clone()], vec![step.clone()])
}

/// The guard-refused pair: (add-Z) at the left argument and (add-S) at the
/// right of `Add(Add(Zero, Succ(Zero)), Add(Succ(Zero), Zero))`.
///
/// The two cells overlap, so the shift guard refuses the pair, while their
/// two images in this instance are disjoint.
///
/// # Specification
/// trivial.
fn guard_refused_pair() -> (
    CellStore<ToyAlphabet>,
    Toy,
    CellApp<ToyAlphabet>,
    CellApp<ToyAlphabet>,
)
{
    let mut store = CellStore::new();
    let z = store.insert(add_z());
    let s = store.insert(add_s());
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
        Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
    );
    (
        store,
        peak,
        CellApp {
            cell: z,
            at: at![0],
        },
        CellApp {
            cell: s,
            at: at![1],
        },
    )
}

/// The (add-Z) step at the root, read off the fusion fixture's composition.
///
/// # Specification
/// trivial.
fn add_z_at_root(composition: &Overlap<ToyAlphabet>) -> CellApp<ToyAlphabet>
{
    CellApp {
        cell: composition.right,
        at: at![],
    }
}

#[test]
fn the_two_legs_of_a_permutation_tile_have_one_flow()
{
    // One peak, two sequentializations of one pair of independent steps, one
    // composite. The two legs record the same events in opposite orders and
    // the projection identifies them, which makes flow equality a witness for
    // the shift quotient rather than a restatement of the recorded order.
    let (store, f, g) = cong2_store();
    let peak = cong2_body();
    let (first, second) = cong2_pair(f, g);
    let witness = derive_shift_equivalence(&store, &peak, &first, &second)
        .expect("the cong2 pair earns its shift witness");
    let forward = project_flow(&store, &peak, &witness.first_then_second())
        .expect("f then g is a derivation of the peak");
    let backward = project_flow(&store, &peak, &witness.second_then_first())
        .expect("g then f is a derivation of the peak");
    assert!(
        bool::from(flows_equal(&forward, &backward)),
        "the two sequentializations of a permutation tile project to one flow"
    );
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        forward.convexity,
        "and the flow carries the fence its soundness rests on, as the shift witness does"
    );
}

#[test]
fn the_games_quotient_identifies_two_firings_the_peak_anchor_separates()
{
    // The first separating family: one cell fired at two different positions
    // of one peak is one play to the quotient (one step, one label, no order
    // to preserve), while the flow's peak anchor keeps the two firings apart.
    // The quotient is therefore not contained in flow equality.
    let (store, f, _g) = cong2_store();
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    let left = project_flow(&store, &peak, &[CellApp {
        cell: f,
        at: at![0],
    }])
    .expect("f fires at the left argument");
    let right = project_flow(&store, &peak, &[CellApp {
        cell: f,
        at: at![1],
    }])
    .expect("f fires at the right argument");
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        left.convexity,
        "the pair sits on the discharge class the measurement is scoped to"
    );
    assert!(
        bool::from(games_equivalent(&left, &right)),
        "the step-index bijection matches trivially: one step, one label, an empty order"
    );
    assert!(
        !bool::from(flows_equal(&left, &right)),
        "but the flows differ at the peak anchor, so the quotient is not inside flow equality"
    );
}

#[test]
fn the_games_quotient_identifies_a_tile_the_flow_declines_a_canonical_form()
{
    // The second separating family, on the tile class itself. (dup) duplicates
    // a subterm; firing (f) under each copy yields two vertices at one depth,
    // under one label, consuming nothing from the peak, a tie the canonical
    // form declines rather than orders. The two legs record the very same
    // three steps, so no refinement of the bijection's step vocabulary escapes
    // the separation: the quotient identifies the tile and flow equality
    // declines it.
    let mut store = CellStore::new();
    let dup = store.insert(dup_cell());
    let f = store.insert(f_cell());
    let peak = Toy::succ(Toy::zero());
    let forward_path = vec![
        CellApp {
            cell: dup,
            at: at![],
        },
        CellApp {
            cell: f,
            at: at![0],
        },
        CellApp {
            cell: f,
            at: at![1],
        },
    ];
    let backward_path = vec![
        CellApp {
            cell: dup,
            at: at![],
        },
        CellApp {
            cell: f,
            at: at![1],
        },
        CellApp {
            cell: f,
            at: at![0],
        },
    ];
    let forward = project_flow(&store, &peak, &forward_path)
        .expect("dup then the two f firings is a derivation of the peak");
    let backward = project_flow(&store, &peak, &backward_path)
        .expect("the two f firings commute under the duplicated frame");
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        forward.convexity,
        "the pair sits on the discharge class the measurement is scoped to"
    );
    assert!(
        matches!(forward.canonical(), Maybe::Absent(_))
            && matches!(backward.canonical(), Maybe::Absent(_)),
        "two same-labelled vertices at one depth tie the key, and the tie is refused an order"
    );
    assert!(
        bool::from(games_equivalent(&forward, &backward)),
        "the quotient identifies the two orders of the tile: the bijection exists"
    );
    assert!(
        !bool::from(flows_equal(&forward, &backward)),
        "and the flow declines the identification the quotient makes"
    );
    // The certificate-level reading agrees: a tracelet recording the two
    // orders replays, and its two legs still have no shared canonical form.
    let tracelet = tracelet_over(
        &peak,
        &Toy::add(Toy::zero(), Toy::zero()),
        forward_path,
        backward_path,
    );
    assert!(
        bool::from(tracelet.replay(&store)),
        "both orders are derivations of the recorded boundary"
    );
    assert!(
        !bool::from(
            legs_flow_equal(&tracelet, &store).expect("both legs project and reach the join")
        ),
        "so the certificate-level relation declines the tile the shift witness would license"
    );
}

#[test]
fn flow_equality_sits_inside_the_games_quotient_on_the_discharge_class()
{
    // The containment that survives, checked rather than argued: every
    // flow-equal leg pair this suite builds admits the matching bijection.
    // Equal canonical forms carry the same labels and the same thread
    // structure, and a thread-structure isomorphism is a dependence-preserving
    // step-index bijection; the two separating families above make the
    // containment strict.
    let (store, f, g) = cong2_store();
    let peak = cong2_body();
    let (first, second) = cong2_pair(f, g);
    let witness = derive_shift_equivalence(&store, &peak, &first, &second)
        .expect("the cong2 pair earns its shift witness");
    let forward = project_flow(&store, &peak, &witness.first_then_second())
        .expect("f then g is a derivation of the peak");
    let backward = project_flow(&store, &peak, &witness.second_then_first())
        .expect("g then f is a derivation of the peak");
    assert!(
        bool::from(flows_equal(&forward, &backward)),
        "the permutation tile is flow-equal"
    );
    assert!(
        bool::from(games_equivalent(&forward, &backward)),
        "and the flow-equal pair admits the matching bijection"
    );
    // The guard-refused pair is the suite's other flow-equal leg pair.
    let (store, peak, first, second) = guard_refused_pair();
    let forward = project_flow(&store, &peak, &[first.clone(), second.clone()])
        .expect("add-Z then add-S is a derivation of the peak");
    let backward = project_flow(&store, &peak, &[second, first])
        .expect("add-S then add-Z is a derivation of the peak");
    assert!(
        bool::from(flows_equal(&forward, &backward)),
        "the pair the guard refuses is flow-equal"
    );
    assert!(
        bool::from(games_equivalent(&forward, &backward)),
        "and it too admits the matching bijection"
    );
}

#[test]
fn disjoint_steps_share_no_thread()
{
    // Why the tile's two legs agree: neither step consumes an occurrence the
    // other created, so no thread runs from one vertex to the other and the
    // causal order is empty. This is the projection's independence relation,
    // read off the instance.
    let (store, f, g) = cong2_store();
    let peak = cong2_body();
    let path = [
        CellApp {
            cell: f,
            at: at![0],
        },
        CellApp {
            cell: g,
            at: at![1],
        },
    ];
    let flow = project_flow(&store, &peak, &path).expect("f then g is a derivation of the peak");
    assert_eq!(
        2_usize,
        flow.labels.len(),
        "two cell applications, two vertices"
    );
    assert!(
        !flow.threads.iter().any(|thread| matches!(
            (thread.up, thread.lo),
            (FlowEnd::Vertex { .. }, FlowEnd::Vertex { .. })
        )),
        "no occurrence created by one step is consumed by the other"
    );
    assert!(
        flow.threads.iter().any(|thread| matches!(
            (thread.up, thread.lo),
            (FlowEnd::Peak { .. }, FlowEnd::Join)
        )),
        "and the frame node neither step touches threads straight through"
    );
}

#[test]
fn the_shift_guard_refuses_a_pair_the_projection_identifies()
{
    // The first strictness: two applications at disjoint positions whose two
    // orders reach one term, refused the shift witness because the cells
    // overlap, a question about the alphabet asked whatever this instance did.
    // The projection asks the instance, finds two disjoint match images
    // sharing no occurrence, and licenses the pair. Shift equivalence is
    // therefore strictly inside flow equality.
    let (store, peak, first, second) = guard_refused_pair();
    assert!(
        derive_shift_equivalence(&store, &peak, &first, &second).is_err(),
        "the guard refuses the pair on its overlap conjunct"
    );
    let forward = project_flow(&store, &peak, &[first.clone(), second.clone()])
        .expect("add-Z then add-S is a derivation of the peak");
    let backward = project_flow(&store, &peak, &[second, first])
        .expect("add-S then add-Z is a derivation of the peak");
    assert!(
        bool::from(flows_equal(&forward, &backward)),
        "and the projection identifies the two orders the guard would not"
    );
}

#[test]
fn flow_equality_is_strictly_finer_than_replay_equivalence()
{
    // The second strictness, at one certificate: `derive_fused` builds one
    // boundary whose `path_a` is the two-step derivation and whose `path_b` is
    // the single fused step. It replays, and its two legs carry different
    // vertex label multisets, so no re-indexing makes their flows agree.
    let (mut store, composition) = fusion_fixture();
    let (_fused, tracelet) =
        derive_fused(&composition, &mut store).expect("the fused cell derives");
    assert!(
        bool::from(tracelet.replay(&store)),
        "the certificate replays: both legs reach the recorded join"
    );
    assert!(
        !bool::from(legs_flow_equal(&tracelet, &store).expect("both legs project")),
        "and its two legs have different flows: one boundary, two flows"
    );
}

#[test]
fn replay_equivalent_certificates_can_carry_different_flows()
{
    // The second strictness, between two certificates. Two structurally
    // distinct derivations of one boundary are one certificate under replay
    // identity; their flows differ, because one leg is two steps and the other
    // is one.
    let (mut store, composition) = fusion_fixture();
    let (_fused, fused_derivation) =
        derive_fused(&composition, &mut store).expect("the fused cell derives");
    let two_step_derivation = Tracelet {
        overlap: fused_derivation.overlap.clone(),
        path_a: fused_derivation.path_a.clone(),
        path_b: fused_derivation.path_a.clone(),
        joins_at: fused_derivation.joins_at.clone(),
    };
    assert!(
        bool::from(replay_equivalent(
            &fused_derivation,
            &two_step_derivation,
            &store
        )),
        "the two are one certificate under replay identity"
    );
    assert!(
        !bool::from(
            tracelets_flow_equal(&fused_derivation, &two_step_derivation, &store)
                .expect("both certificates project")
        ),
        "and two flows under the projection, so the two relations do not coincide"
    );
}

#[test]
fn a_certificate_has_its_own_flow()
{
    let (mut store, composition) = fusion_fixture();
    let (_fused, tracelet) =
        derive_fused(&composition, &mut store).expect("the fused cell derives");
    assert!(
        bool::from(
            tracelets_flow_equal(&tracelet, &tracelet, &store).expect("the certificate projects")
        ),
        "the relation is reflexive on a certificate whose legs project"
    );
}

#[test]
fn a_single_step_leg_threads_the_whole_term_through_one_vertex()
{
    // A ground rule whose match image is the whole term: every occurrence is
    // consumed at the one vertex, and every occurrence of the result is created
    // there and reaches the conclusion. No thread bypasses the vertex, because
    // there is no frame.
    let (store, f, _g) = cong2_store();
    let peak = Toy::succ(Toy::zero());
    let flow = project_flow(&store, &peak, &[CellApp { cell: f, at: at![] }])
        .expect("f fires at the root of Succ(Zero)");
    assert_eq!(1_usize, flow.labels.len(), "one vertex");
    assert!(
        flow.threads.iter().all(|thread| matches!(
            thread.up,
            FlowEnd::Peak { .. } | FlowEnd::Vertex { .. }
        ) && matches!(
            thread.lo,
            FlowEnd::Vertex { .. } | FlowEnd::Join
        )),
        "every thread has an end at the vertex or at a boundary"
    );
    assert!(
        !flow.threads.iter().any(|thread| matches!(
            (thread.up, thread.lo),
            (FlowEnd::Peak { .. }, FlowEnd::Join)
        )),
        "and none bypasses it, because the redex covers the whole term"
    );
}

#[test]
fn a_consumed_creation_is_one_thread_between_two_vertices()
{
    // The dependent case: (add-S) at the root creates a `Succ` node with an
    // `Add` beneath it, and (add-Z) then consumes that `Add`. The occurrence
    // the first step created is the one the second destroys, so the thread
    // carrying the dependence runs from vertex to vertex.
    let mut store = CellStore::new();
    let z = store.insert(add_z());
    let s = store.insert(add_s());
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let flow = project_flow(&store, &peak, &[CellApp { cell: s, at: at![] }, CellApp {
        cell: z,
        at: at![0],
    }])
    .expect("add-S then add-Z is a derivation of the peak");
    assert_eq!(2_usize, flow.labels.len(), "two vertices");
    assert!(
        flow.threads.iter().any(|thread| matches!(
            (thread.up, thread.lo),
            (FlowEnd::Vertex { .. }, FlowEnd::Vertex { .. })
        )),
        "the created-and-then-consumed occurrence is a vertex-to-vertex thread"
    );
}

#[test]
fn the_projection_forgets_where_a_cell_fired()
{
    // A vertex is labelled by the cell and not by where it fired. Two legs
    // firing one cell at two positions carry the same label, and what tells
    // them apart is which occurrences their threads touch.
    let (store, f, _g) = cong2_store();
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    let left = project_flow(&store, &peak, &[CellApp {
        cell: f,
        at: at![0],
    }])
    .expect("f fires at the left argument");
    let right = project_flow(&store, &peak, &[CellApp {
        cell: f,
        at: at![1],
    }])
    .expect("f fires at the right argument");
    let Maybe::Present(cell) = store.get(f)
    else {
        panic!("f is stored");
    };
    assert_eq!(
        vec![cell_address(cell)],
        left.labels,
        "the vertex names the cell, not the position"
    );
    assert_eq!(left.labels, right.labels, "and the two legs agree on it");
    assert!(
        !bool::from(flows_equal(&left, &right)),
        "while the threads still tell the two firings apart, at the peak boundary"
    );
}

#[test]
fn equal_flows_over_different_boundaries_are_not_one_certificate()
{
    // The containment, and the regression that fails if the boundary conjunct
    // is dropped. A flow forgets the formula-level arrangement, so one cell
    // fired on two unrelated instances of its left-hand side projects to one
    // flow over two boundaries that transform different things into different
    // things. Comparing the flows alone identifies them and replay-equivalence
    // does not.
    let (store, composition) = fusion_fixture();
    let step = add_z_at_root(&composition);
    let ground = one_step_certificate(&Toy::add(Toy::zero(), Toy::zero()), &Toy::zero(), &step);
    let schematic =
        one_step_certificate(&Toy::add(Toy::zero(), Toy::var("y")), &Toy::var("y"), &step);
    assert!(
        bool::from(ground.replay(&store)) && bool::from(schematic.replay(&store)),
        "both are certificates: add-Z fires on each peak and reaches each recorded join"
    );
    assert!(
        !bool::from(replay_equivalent(&ground, &schematic, &store)),
        "and they are two certificates, because their boundaries differ"
    );
    let ground_flow =
        project_flow(&store, &ground.overlap.peak, &ground.path_a).expect("the leg projects");
    let schematic_flow =
        project_flow(&store, &schematic.overlap.peak, &schematic.path_a).expect("the leg projects");
    assert!(
        bool::from(flows_equal(&ground_flow, &schematic_flow)),
        "their two legs carry one flow, which is what makes this the sharp case"
    );
    assert!(
        !bool::from(
            tracelets_flow_equal(&ground, &schematic, &store).expect("both certificates project")
        ),
        "so the certificate-level relation must separate them on the boundary"
    );
}

#[test]
fn flow_equality_implies_replay_equivalence()
{
    // The containment as a checked implication over every certificate this
    // suite builds: the fused derivation, the two-step presentation of the
    // same boundary, and the two one-step certificates whose flows coincide
    // over different boundaries.
    let (mut store, composition) = fusion_fixture();
    let (_fused, fused_derivation) =
        derive_fused(&composition, &mut store).expect("the fused cell derives");
    let two_step = Tracelet {
        overlap: fused_derivation.overlap.clone(),
        path_a: fused_derivation.path_a.clone(),
        path_b: fused_derivation.path_a.clone(),
        joins_at: fused_derivation.joins_at.clone(),
    };
    let step = add_z_at_root(&composition);
    let ground = one_step_certificate(&Toy::add(Toy::zero(), Toy::zero()), &Toy::zero(), &step);
    let schematic =
        one_step_certificate(&Toy::add(Toy::zero(), Toy::var("y")), &Toy::var("y"), &step);
    let certificates = [fused_derivation, two_step, ground, schematic];
    for left in &certificates {
        for right in &certificates {
            let flow_equal = tracelets_flow_equal(left, right, &store)
                .expect("every certificate in the set projects");
            if bool::from(flow_equal) {
                assert!(
                    bool::from(replay_equivalent(left, right, &store)),
                    "flow equality is inside replay-equivalence, so a positive here forces a \
                     positive there"
                );
            }
        }
    }
}

#[test]
fn a_leg_that_lands_off_the_join_has_no_certificate_flow()
{
    // Every recorded step fires, so the leg is a derivation, of the wrong
    // boundary. A certificate whose leg lands off its recorded join does not
    // replay, and projecting it refuses rather than hand back a flow that
    // would be compared as if it stood for that boundary.
    let (store, composition) = fusion_fixture();
    let strays = one_step_certificate(
        &Toy::add(Toy::zero(), Toy::zero()),
        &Toy::succ(Toy::zero()),
        &add_z_at_root(&composition),
    );
    assert!(
        !bool::from(strays.replay(&store)),
        "the recorded join is not where add-Z lands"
    );
    let obstruction = tracelet_flow(&strays, &store).expect_err("so the certificate is refused");
    assert_eq!(
        FlowObstruction::LegMissesTheJoin {
            reached: Box::new(Toy::zero()),
        },
        obstruction,
        "and the refusal carries where the leg actually landed"
    );
}

#[test]
fn the_games_oracle_separates_missing_labels_and_causal_shapes()
{
    let (store, f, g) = cong2_store();
    let empty = project_flow(&store, &Toy::zero(), &[]).expect("an empty leg projects");
    let one_f = project_flow(&store, &Toy::succ(Toy::zero()), &[CellApp {
        cell: f,
        at: at![],
    }])
    .expect("f fires at its root");
    let one_g = project_flow(&store, &Toy::succ(Toy::succ(Toy::zero())), &[CellApp {
        cell: g,
        at: at![],
    }])
    .expect("g fires at its root");
    assert!(bool::from(games_equivalent(&empty, &empty)));
    assert!(!bool::from(games_equivalent(&empty, &one_f)));
    assert!(!bool::from(games_equivalent(&one_f, &one_g)));

    let mut store = CellStore::new();
    let c = store.insert(c_cell());
    let chain_peak = Toy::add(
        Toy::add(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()),
        Toy::zero(),
    );
    let chain = project_flow(&store, &chain_peak, &[
        CellApp {
            cell: c,
            at: at![0, 0],
        },
        CellApp {
            cell: c,
            at: at![0],
        },
        CellApp { cell: c, at: at![] },
    ])
    .expect("three nested collapses fire in order");
    let fork_peak = Toy::add(
        Toy::add(Toy::zero(), Toy::zero()),
        Toy::add(Toy::zero(), Toy::zero()),
    );
    let fork = project_flow(&store, &fork_peak, &[
        CellApp {
            cell: c,
            at: at![0],
        },
        CellApp {
            cell: c,
            at: at![1],
        },
        CellApp { cell: c, at: at![] },
    ])
    .expect("independent children collapse before their parent");
    assert_eq!(chain.labels, fork.labels);
    assert!(bool::from(depends_before(
        &chain,
        FlowVertexIndex::from(0),
        FlowVertexIndex::from(2)
    )));
    assert!(!bool::from(depends_before(
        &chain,
        FlowVertexIndex::from(2),
        FlowVertexIndex::from(0)
    )));
    assert!(!bool::from(depends_before(
        &chain,
        FlowVertexIndex::from(1),
        FlowVertexIndex::from(1)
    )));
    assert!(!bool::from(games_equivalent(&chain, &fork)));
    assert!(!bool::from(games_equivalent(&fork, &chain)));
}
