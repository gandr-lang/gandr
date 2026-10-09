//! The tracelet normal form differential: generated normal-form-equal
//! derivation pairs, checked against the replay oracle, and the causal order
//! the canonical schedule is a linear extension of.
//!
//! The normal form's load-bearing claim is an implication, normal-form-equal
//! implies replay-equal, and only a differential can attack it, because it is
//! a statement about every pair the quotient identifies. The oracle is
//! [`replay_equivalent`], which re-executes both derivations by ground
//! rewriting; nothing in the normal form participates in its answer.
//!
//! The suite runs on the toy alphabet: a sequent term has one command
//! position, so the shift quotient over the sequent alphabet is empty and a
//! differential over it would exercise nothing.
//!
//! # The kill signal
//!
//! A shift-equivalent, replay-divergent pair is a soundness defect in position
//! or overlap bookkeeping. It surfaces inside `normalize`, which replays its
//! own canonical schedule and refuses with a shifted-schedule obstruction, and
//! in [`every_nf_equal_pair_is_replay_equivalent`], which asserts the
//! implication directly. Both are failures, never skips.
//!
//! # The causal order
//!
//! The generated causal-order shape is a balanced `Add`-tree, whose internal
//! nodes are redexes only once their children have collapsed: several layers,
//! several occupants per layer, and ancestor-descendant dependence. The order
//! laws, the layer antichains, the key's totality and the exchange to the
//! canonical order are properties over it; the three-layer fixture writes the
//! expected edges and layers down in full.
//!
//! The canonical schedule is the causal layering, and three properties check
//! its clauses: the depth is the longest chain strictly below under the
//! transitive closure, every adjacent independent transposition leaves the
//! canonical key sequence fixed, and one rule interned under two identifiers
//! in two stores gives one key sequence and one schedule.
//!
//! # The adversarial fixtures
//!
//! Four of the normal form's failure modes fire only when an alphabet answers
//! what no shipped alphabet can, so their witnesses run over the lying
//! inhabitants of the tools crate, and each also runs the honest derivation so
//! the refusal is attributable to the one lie. A fifth fixture pins a
//! reachability premise: a nested pair that would diverge under a
//! transposition stays dependent only because the overlap enumerator counts a
//! metavariable position as a composition seam.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::CollidingAddresses;
use gandr_theory_cell_complexes_tools::IncomparablePositions;
use gandr_theory_cell_complexes_tools::Lying;
use gandr_theory_cell_complexes_tools::NonLocalSplice;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToyPos;
use gandr_theory_cell_complexes_tools::WithheldConvexity;
use gandr_theory_cell_complexes_tools::lying_cell;
use gandr_theory_cell_complexes_tools::reoriented_lying_cell;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::overlaps_between;
use gandr_theory_coherent_resolutions::replay_equivalent;
use gandr_theory_deep_inference::CausalDepth;
use gandr_theory_deep_inference::DerivationEvent;
use gandr_theory_deep_inference::EventIndex;
use gandr_theory_deep_inference::EventKey;
use gandr_theory_deep_inference::EventOrder;
use gandr_theory_deep_inference::ExchangeObstruction;
use gandr_theory_deep_inference::NormalFormObstruction;
use gandr_theory_deep_inference::PrimCert;
use gandr_theory_deep_inference::PrimId;
use gandr_theory_deep_inference::PrimMultiplicity;
use gandr_theory_deep_inference::ReplayLevel;
use gandr_theory_deep_inference::TraceletNf;
use gandr_theory_deep_inference::TranspositionCount;
use gandr_theory_deep_inference::event_order;
use gandr_theory_deep_inference::nf_equal;
use gandr_theory_deep_inference::normalize;
use gandr_theory_deep_inference::normalize_certified;
use gandr_theory_deep_inference::prim_address;
use gandr_theory_deep_inference::tracelets_nf_equal;
use proptest::prelude::*;
use quenchant_shape::shape::Maybe;

use crate::fixture::add_s;
use crate::fixture::add_z;
use crate::fixture::c_cell;
use crate::fixture::f_cell;
use crate::fixture::nop_cell;
use crate::fixture::run;
use crate::fixture::stored;
use crate::fixture::tracelet_over;

/// The number of pairwise-independent redexes on a generated spine.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RedexCount(usize);

/// The height of the balanced `Add`-tree fixture: `height + 1` causal layers.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TreeHeight(usize);

/// One generated sort key, permuting a causal layer of the tree fixture.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct LayerSortKey(usize);

/// (drop): `Add(Zero, x) ~> Zero`, an erasing rule whose right-hand side
/// forgets the metavariable its left-hand side binds.
///
/// It makes two different peaks reach one join by one schedule, the only way
/// to separate the normal form's boundary from its factorization.
///
/// # Specification
/// trivial.
fn drop_cell() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::add(Toy::zero(), Toy::var("x")), Toy::zero())
}

/// The right-nested spine `Add(r, Add(r, … r))` carrying `count` (f)-redexes
/// at pairwise incomparable positions.
///
/// # Specification
/// trivial.
fn spine(count: RedexCount) -> Toy
{
    let redex = Toy::succ(Toy::zero());
    let mut term = redex.clone();
    for _ in 0_usize .. count.0.saturating_sub(1_usize) {
        term = Toy::add(redex.clone(), term);
    }
    term
}

/// The `count` redex positions of [`spine`], outer to inner: `[1]*i ++ [0]`
/// for every redex but the last, and `[1]*(count-1)` for the last.
///
/// # Specification
/// trivial.
fn spine_positions(count: RedexCount) -> Vec<ToyPos>
{
    let last = count.0.saturating_sub(1_usize);
    let right = PositionStep::from(1_usize);
    let mut out = Vec::with_capacity(count.0);
    for index in 0_usize .. last {
        let mut path = vec![right; index];
        path.push(PositionStep::from(0_usize));
        out.push(ToyAlphabet::position_at_path(&path));
    }
    let tail = vec![right; last];
    out.push(ToyAlphabet::position_at_path(&tail));
    out
}

/// The (f)-only store, its cell identifier, a spine peak, and the canonical
/// schedule over it.
///
/// # Specification
/// trivial.
fn spine_fixture(
    count: RedexCount
) -> (
    CellStore<ToyAlphabet>,
    CellId,
    Toy,
    Vec<CellApp<ToyAlphabet>>,
)
{
    let mut store = CellStore::new();
    let f = store.insert(f_cell());
    let peak = spine(count);
    let schedule = spine_positions(count)
        .into_iter()
        .map(|position| CellApp {
            cell: f,
            at: position,
        })
        .collect();
    (store, f, peak, schedule)
}

/// Normalize a recorded derivation, or fail the test naming the refusal: a
/// shifted-schedule refusal here is the kill signal.
///
/// # Specification
/// - panics: when the derivation is refused a normal form.
fn normalized<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    joins_at: &A::Cmd,
    path: &[CellApp<A>],
) -> TraceletNf<A>
where
    A: CellAlphabet,
{
    match normalize(store, peak, joins_at, path) {
        | Ok(normal) => normal,
        | Err(NormalFormObstruction::ShiftedScheduleDoesNotFire { .. }) => {
            panic!("the kill signal: the canonical schedule does not fire")
        },
        | Err(NormalFormObstruction::ShiftedScheduleMissesTheJoin { .. }) => {
            panic!("the kill signal: the canonical schedule misses the join")
        },
        | Err(_) => panic!("the derivation was refused a normal form"),
    }
}

/// The keys of `order`'s events, in canonical order.
///
/// # Specification
/// trivial.
fn canonical_keys(order: &EventOrder<ToyAlphabet>) -> Vec<EventKey>
{
    order
        .canonical_order()
        .into_iter()
        .filter_map(|index| match order.key(index) {
            | Maybe::Present(key) => Some(key),
            | Maybe::Absent(_) => None,
        })
        .collect()
}

/// The guard-refused pair: (add-Z) at the left argument and (add-S) at the
/// right of `Add(Add(Zero, Succ(Zero)), Add(Succ(Zero), Zero))`, whose two
/// orders reach one term although the cells overlap.
///
/// # Specification
/// trivial.
fn overlapping_pair() -> (
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

/// The generated tree case: a height, and one sort key per redex so each
/// causal layer is permuted independently.
///
/// Permuting within a layer keeps every generated case a firing order: a
/// layer is an antichain, while a deeper node fires before the node enclosing
/// it.
///
/// # Specification
/// trivial.
fn tree_case() -> impl Strategy<Value = (TreeHeight, Vec<LayerSortKey>)>
{
    (0_usize ..= 2_usize).prop_flat_map(|height| {
        let height = TreeHeight(height);
        let redexes = tree_layers(height).iter().fold(0_usize, |running, layer| {
            running.saturating_add(layer.len())
        });
        (
            Just(height),
            proptest::collection::vec((0_usize .. 64_usize).prop_map(LayerSortKey), redexes),
        )
    })
}

/// The balanced tree of `Add` nodes at the given height.
///
/// Every internal node is a (c)-redex once both its children have collapsed
/// to `Zero`, which makes the causal order a tree rather than an antichain.
///
/// # Specification
/// trivial.
fn tree(height: TreeHeight) -> Toy
{
    let mut term = Toy::add(Toy::zero(), Toy::zero());
    for _ in 0_usize .. height.0 {
        term = Toy::add(term.clone(), term);
    }
    term
}

/// The redex positions of [`tree`], grouped into causal layers, deepest first:
/// layer `k` holds every position of length `height - k`.
///
/// # Specification
/// trivial.
fn tree_layers(height: TreeHeight) -> Vec<Vec<ToyPos>>
{
    let mut layers: Vec<Vec<ToyPos>> = Vec::with_capacity(height.0.saturating_add(1_usize));
    let mut length = height.0;
    loop {
        let mut paths: Vec<Vec<PositionStep>> = vec![Vec::new()];
        for _ in 0_usize .. length {
            let mut grown: Vec<Vec<PositionStep>> =
                Vec::with_capacity(paths.len().saturating_mul(2_usize));
            for path in &paths {
                for child in 0_usize ..= 1_usize {
                    let mut extended = path.clone();
                    extended.push(PositionStep::from(child));
                    grown.push(extended);
                }
            }
            paths = grown;
        }
        layers.push(
            paths
                .iter()
                .map(|path| ToyAlphabet::position_at_path(path))
                .collect(),
        );
        let Some(next) = length.checked_sub(1_usize)
        else {
            break;
        };
        length = next;
    }
    layers
}

/// The tree fixture: a store holding (c), the peak, and the redex positions in
/// causal layers, deepest first.
///
/// # Specification
/// trivial.
fn tree_fixture(height: TreeHeight) -> (CellStore<ToyAlphabet>, CellId, Toy, Vec<Vec<ToyPos>>)
{
    let mut store = CellStore::new();
    let c = store.insert(c_cell());
    (store, c, tree(height), tree_layers(height))
}

/// The tree fixture behind an unrelated cell, so the same rule is interned
/// under a different identifier: if any arrival index or handle reached the
/// event key, the two stores would disagree.
///
/// # Specification
/// trivial.
fn tree_fixture_behind_a_decoy(
    height: TreeHeight
) -> (CellStore<ToyAlphabet>, CellId, Toy, Vec<Vec<ToyPos>>)
{
    let mut store = CellStore::new();
    let decoy = store.insert(nop_cell());
    let c = store.insert(c_cell());
    assert_ne!(decoy, c, "the decoy and the rule are distinct cells");
    (store, c, tree(height), tree_layers(height))
}

/// A recorded derivation over the tree fixture, firing each layer in turn and
/// ordering inside a layer by the supplied keys.
///
/// # Specification
/// trivial.
fn tree_path(
    cell: CellId,
    layers: Vec<Vec<ToyPos>>,
    keys: &[LayerSortKey],
) -> Vec<CellApp<ToyAlphabet>>
{
    let mut supply = keys.iter();
    let mut recorded: Vec<CellApp<ToyAlphabet>> = Vec::new();
    for layer in layers {
        let mut keyed: Vec<(LayerSortKey, ToyPos)> = layer
            .into_iter()
            .map(|position| (supply.next().copied().unwrap_or_default(), position))
            .collect();
        keyed.sort_by_key(|entry| entry.0);
        for entry in keyed {
            recorded.push(CellApp { cell, at: entry.1 });
        }
    }
    recorded
}

/// The four-step, three-layer derivation the deterministic fixtures share,
/// each application named by its role.
///
/// (c) overlaps nothing, so dependence is position containment alone:
/// `inner @ [0,0]` and `branch @ [1]` depend on nothing, `middle @ [0]`
/// encloses `inner`, and `root @ []` encloses all three. The layering is
/// `{inner, branch}`, then `{middle}`, then `{root}`.
struct ThreeLayer
{
    /// The store holding (c).
    store: CellStore<ToyAlphabet>,
    /// The identifier (c) took in that store.
    cell: CellId,
    /// The term the derivation starts from.
    peak: Toy,
    /// The term the four steps reach.
    join: Toy,
    /// The innermost application, at `[0,0]`.
    inner: CellApp<ToyAlphabet>,
    /// The application enclosing `inner`, at `[0]`.
    middle: CellApp<ToyAlphabet>,
    /// The application incomparable with both, at `[1]`.
    branch: CellApp<ToyAlphabet>,
    /// The application enclosing all three, at the root.
    root: CellApp<ToyAlphabet>,
}

impl ThreeLayer
{
    /// The recorded derivation `[inner, middle, branch, root]`.
    ///
    /// # Specification
    /// trivial.
    fn recorded(&self) -> Vec<CellApp<ToyAlphabet>>
    {
        vec![
            self.inner.clone(),
            self.middle.clone(),
            self.branch.clone(),
            self.root.clone(),
        ]
    }
}

/// Build the three-layer fixture, running the recorded order to its join.
///
/// # Specification
/// - panics: when the recorded order does not fire, which is a fixture defect.
fn three_layer_fixture() -> ThreeLayer
{
    let mut store = CellStore::new();
    let cell = store.insert(c_cell());
    let peak = Toy::add(
        Toy::add(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()),
        Toy::add(Toy::zero(), Toy::zero()),
    );
    let mut fixture = ThreeLayer {
        store,
        cell,
        peak,
        join: Toy::zero(),
        inner: CellApp {
            cell,
            at: at![0, 0],
        },
        middle: CellApp { cell, at: at![0] },
        branch: CellApp { cell, at: at![1] },
        root: CellApp { cell, at: at![] },
    };
    fixture.join = run(&fixture.store, &fixture.peak, &fixture.recorded());
    fixture
}

#[test]
fn an_overlapping_pair_keeps_its_recorded_order()
{
    // The under-approximation, exhibited: two applications at disjoint
    // positions whose two orders reach one term, which the quotient still
    // refuses to identify because the cell pair overlaps. The normal forms
    // differ while the replay oracle calls the derivations one transformation.
    let (store, peak, first, second) = overlapping_pair();
    let forward = vec![first.clone(), second.clone()];
    let backward = vec![second, first];
    let join = run(&store, &peak, &forward);
    assert_eq!(
        join,
        run(&store, &peak, &backward),
        "the two orders do reach one term at this instance"
    );
    let forward_nf = normalized(&store, &peak, &join, &forward);
    let backward_nf = normalized(&store, &peak, &join, &backward);
    assert!(
        !bool::from(nf_equal(&forward_nf, &backward_nf)),
        "the cells overlap, so no transposition is licensed and the schedules stay apart"
    );
    assert_eq!(
        forward_nf.primitives, backward_nf.primitives,
        "the factorizations agree: it is the schedule the quotient will not merge"
    );
    let a = tracelet_over(&peak, &join, forward.clone(), forward);
    let b = tracelet_over(&peak, &join, backward.clone(), backward);
    assert!(
        bool::from(replay_equivalent(&a, &b, &store)),
        "and the replay oracle identifies them all the same: normal-form-distinct means nothing"
    );
}

#[test]
fn a_two_member_replay_level_reaches_one_term_in_both_permitted_orders()
{
    // A sequent command has one command position, so no two applications share
    // a replay level there; the toy spine's two leaves are genuinely
    // independent.
    let (store, _cell, peak, forward) = spine_fixture(RedexCount(2_usize));
    let backward = vec![forward[1].clone(), forward[0].clone()];
    let join = run(&store, &peak, &forward);
    assert_eq!(
        join,
        run(&store, &peak, &backward),
        "both permitted within-level orders reach the same term"
    );
    let forward_witness = normalize_certified(&store, &peak, &join, &forward)
        .expect("the forward independent order replays");
    let backward_witness = normalize_certified(&store, &peak, &join, &backward)
        .expect("the backward independent order replays");
    let forward_plan = forward_witness.replay_plan();
    let backward_plan = backward_witness.replay_plan();
    assert_eq!(
        CausalDepth::from(1_usize),
        forward_plan.critical_path(),
        "two independent positions occupy one replay level"
    );
    assert_eq!(
        forward_plan.levels().len(),
        backward_plan.levels().len(),
        "both plans preserve the same dependency-level count"
    );
    let level = forward_plan
        .levels()
        .first()
        .expect("the independent level exists");
    assert_eq!(
        2_usize,
        level.len(),
        "the level retains both distinct applications"
    );
    assert_ne!(
        level[0].at, level[1].at,
        "the batch contains two distinct positions rather than one reused position"
    );
    assert_ne!(
        forward, backward,
        "the fixture supplies two distinct permitted within-level orders"
    );
    let Ok(Maybe::Present(forward_reached)) =
        forward_plan.replay_with_fuel(&store, forward_plan.critical_path())
    else {
        panic!("the forward critical-path budget replays the plan");
    };
    let Ok(Maybe::Present(backward_reached)) =
        backward_plan.replay_with_fuel(&store, backward_plan.critical_path())
    else {
        panic!("the backward critical-path budget replays the plan");
    };
    assert_eq!(
        join, forward_reached,
        "forward replay reaches the declared join"
    );
    assert_eq!(
        join, backward_reached,
        "backward replay reaches the declared join"
    );
    assert_eq!(
        forward_witness.normal_form(),
        backward_witness.normal_form(),
        "the certified normal forms agree exactly"
    );
    assert!(
        bool::from(replay_equivalent(
            &tracelet_over(&peak, &join, forward.clone(), forward),
            &tracelet_over(&peak, &join, backward.clone(), backward),
            &store,
        )),
        "the two certificates agree at replay-equivalence"
    );
    assert!(
        matches!(
            forward_plan.replay_level(
                &store,
                &ToyAlphabet::skolemize(&peak),
                ReplayLevel::from(1_usize),
            ),
            Err(NormalFormObstruction::InvalidReplayLevel { .. })
        ),
        "a second level is refused rather than serializing the batch"
    );
}

#[test]
fn a_repeated_primitive_is_graded_by_multiplicity()
{
    // One cell at one position, firing three times: the three occurrences are
    // one primitive graded 3, and the schedule keeps three entries because
    // each repeat depends on the one before it. Three is the smallest grade
    // that separates counting from any implementation that stops after the
    // first repeat.
    let mut store = CellStore::new();
    let z = store.insert(add_z());
    let peak = Toy::add(
        Toy::zero(),
        Toy::add(Toy::zero(), Toy::add(Toy::zero(), Toy::succ(Toy::zero()))),
    );
    let step = CellApp { cell: z, at: at![] };
    let path = vec![step.clone(), step.clone(), step];
    let join = run(&store, &peak, &path);
    assert_eq!(
        Toy::succ(Toy::zero()),
        join,
        "three add-Z steps at the root peel all three frames"
    );
    let normal = normalized(&store, &peak, &join, &path);
    assert_eq!(
        1_usize,
        normal.primitives.len(),
        "the three occurrences are one content-addressed primitive"
    );
    assert_eq!(
        3_usize,
        normal.schedule.len(),
        "and the schedule keeps all three, because a repeat depends on its predecessor"
    );
    let graded = normal
        .primitives
        .values()
        .next()
        .expect("the factorization holds the one primitive");
    assert_eq!(
        PrimMultiplicity::from(3_u32),
        graded.1,
        "the integer grade is the occurrence count"
    );
}

#[test]
fn a_unit_step_is_eliminated_over_the_toy_alphabet()
{
    // A step that fires and moves nothing is dropped, and the derivation
    // carrying it has the same normal form as the one without.
    let mut store = CellStore::new();
    let f = store.insert(f_cell());
    let nop = store.insert(nop_cell());
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let real = CellApp {
        cell: f,
        at: at![0],
    };
    let unit = CellApp {
        cell: nop,
        at: at![1],
    };
    let bare = vec![real.clone()];
    let padded = vec![unit.clone(), real, unit];
    let join = run(&store, &peak, &bare);
    assert_eq!(
        join,
        run(&store, &peak, &padded),
        "the padded derivation reaches the same term"
    );
    let bare_nf = normalized(&store, &peak, &join, &bare);
    let padded_nf = normalized(&store, &peak, &join, &padded);
    assert_eq!(
        1_usize,
        padded_nf.schedule.len(),
        "both unit steps were dropped"
    );
    assert!(
        bool::from(nf_equal(&bare_nf, &padded_nf)),
        "so the padded derivation has the bare one's normal form"
    );
}

#[test]
fn a_reversed_independent_schedule_is_the_canonical_one()
{
    // The deterministic companion to the shuffle property, the case a
    // generator that quietly stopped permuting would leave uncovered.
    let (store, _f, peak, canonical) = spine_fixture(RedexCount(5_usize));
    let join = run(&store, &peak, &canonical);
    let reversed: Vec<CellApp<ToyAlphabet>> = canonical.iter().rev().cloned().collect();
    assert_ne!(
        canonical, reversed,
        "the reversed schedule is a genuinely different recorded order"
    );
    let canonical_nf = normalized(&store, &peak, &join, &canonical);
    let reversed_nf = normalized(&store, &peak, &join, &reversed);
    assert!(
        bool::from(nf_equal(&canonical_nf, &reversed_nf)),
        "and the quotient identifies the two orders"
    );
    assert_eq!(
        5_usize,
        canonical_nf.schedule.len(),
        "with every primitive retained"
    );
}

#[test]
fn a_layered_derivation_keeps_its_dependent_step_last()
{
    // Two layers, so the layering is exercised: (c) overlaps nothing, so the
    // two leaf applications are independent and may permute, while the root
    // application encloses both and cannot move ahead of them.
    let mut store = CellStore::new();
    let c = store.insert(c_cell());
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::zero()),
        Toy::add(Toy::zero(), Toy::zero()),
    );
    let left = CellApp {
        cell: c,
        at: at![0],
    };
    let right = CellApp {
        cell: c,
        at: at![1],
    };
    let root = CellApp { cell: c, at: at![] };
    let forward = vec![left.clone(), right.clone(), root.clone()];
    let backward = vec![right, left, root];
    let join = run(&store, &peak, &forward);
    assert_eq!(Toy::zero(), join, "the three steps collapse the spine");
    assert_eq!(
        join,
        run(&store, &peak, &backward),
        "and the leaf orders agree at this instance"
    );
    let forward_nf = normalized(&store, &peak, &join, &forward);
    let backward_nf = normalized(&store, &peak, &join, &backward);
    assert!(
        bool::from(nf_equal(&forward_nf, &backward_nf)),
        "the two leaf orders are one normal form"
    );
    let root_address = prim_address(stored(&store, c), &at![]);
    assert_eq!(
        Some(&root_address),
        forward_nf.schedule.last(),
        "the enclosing application depends on both leaves, so it stays in the later layer"
    );
    assert_eq!(
        3_usize,
        forward_nf.schedule.len(),
        "and all three primitives survive"
    );
    assert_eq!(
        3_usize,
        forward_nf.primitives.len(),
        "one cell at three distinct positions is three distinct primitives, each graded once"
    );
}

#[test]
fn a_three_layer_derivation_orders_each_layer_by_content_address()
{
    // Three layers, where the depth recurrence stops being a two-valued flag.
    // `root`'s nearest earlier dependence in the recorded order is `branch`,
    // at layer 0, and its first is `inner`, also at layer 0, while its deepest
    // is `middle`, at layer 1. A recurrence taking the nearest or the first
    // dependence instead of the maximum puts `root` beside `middle`, which the
    // address order inside that layer makes observable. With two occupants in
    // layer 0, the declared `(depth, address)` order is observable too, and
    // it must ascend.
    let fixture = three_layer_fixture();
    let ThreeLayer {
        ref store,
        ref peak,
        ref join,
        ref inner,
        ref middle,
        ref branch,
        ref root,
        ..
    } = fixture;
    let recorded = fixture.recorded();
    assert_eq!(&Toy::zero(), join, "the four steps collapse the whole peak");
    let normal = normalized(store, peak, join, &recorded);
    let cell = stored(store, fixture.cell);
    // The fixture separates the maximum from the nearest or first dependence
    // only because the root primitive's address sorts before the middle one's;
    // the ordering is asserted rather than assumed.
    assert!(
        prim_address(cell, &root.at) < prim_address(cell, &middle.at),
        "the fixture needs the root primitive to sort ahead of the middle one"
    );
    assert_eq!(
        4_usize,
        normal.schedule.len(),
        "one cell at four distinct positions is four primitives"
    );
    assert_eq!(
        4_usize,
        normal.primitives.len(),
        "each graded once, so none of them merged"
    );
    assert_eq!(
        Some(&prim_address(cell, &root.at)),
        normal.schedule.get(3_usize),
        "the root application depends on every other, so it is the deepest layer alone"
    );
    assert_eq!(
        Some(&prim_address(cell, &middle.at)),
        normal.schedule.get(2_usize),
        "and the middle layer is the enclosing-but-not-outermost application, alone"
    );
    let layer_zero = normal
        .schedule
        .get(0_usize .. 2_usize)
        .expect("the schedule has four entries");
    let mut expected = vec![
        prim_address(cell, &inner.at),
        prim_address(cell, &branch.at),
    ];
    expected.sort_unstable();
    assert_eq!(
        expected, layer_zero,
        "layer zero holds exactly the two independent applications, in ascending address order"
    );
    // The layer is free: permuting its two occupants leaves one normal form.
    let permuted = vec![branch.clone(), inner.clone(), middle.clone(), root.clone()];
    assert_eq!(
        join,
        &run(store, peak, &permuted),
        "the permuted derivation reaches the same term to begin with"
    );
    let permuted_nf = normalized(store, peak, join, &permuted);
    assert!(
        bool::from(nf_equal(&normal, &permuted_nf)),
        "so the two recorded orders are one normal form"
    );
}

#[test]
fn a_derivation_from_a_different_peak_is_nf_distinct()
{
    // The boundary is part of the normal form. An erasing rule forgets what it
    // matched, so two different peaks reach one join under one schedule: the
    // factorizations and schedules agree and the derivations are still two
    // transformations. An equality comparing only factorization and schedule
    // would identify them, and the replay oracle would not.
    let mut store = CellStore::new();
    let dropper = store.insert(drop_cell());
    let path = vec![CellApp {
        cell: dropper,
        at: at![],
    }];
    let near = Toy::add(Toy::zero(), Toy::zero());
    let far = Toy::add(Toy::zero(), Toy::succ(Toy::zero()));
    let join = Toy::zero();
    assert_ne!(near, far, "the two peaks are genuinely different terms");
    assert_eq!(join, run(&store, &near, &path), "and both reach one join");
    assert_eq!(join, run(&store, &far, &path), "by the same one step");
    let near_nf = normalized(&store, &near, &join, &path);
    let far_nf = normalized(&store, &far, &join, &path);
    assert_eq!(
        near_nf.primitives, far_nf.primitives,
        "the graded factorizations are identical"
    );
    assert_eq!(
        near_nf.schedule, far_nf.schedule,
        "and so are the canonical schedules"
    );
    assert!(
        !bool::from(nf_equal(&near_nf, &far_nf)),
        "so it is the recorded peak alone that keeps them apart"
    );
    let near_cert = tracelet_over(&near, &join, path.clone(), path.clone());
    let far_cert = tracelet_over(&far, &join, path.clone(), path);
    assert!(
        !bool::from(replay_equivalent(&near_cert, &far_cert, &store)),
        "and the replay oracle keeps them apart too: a positive would be unsound"
    );
    assert!(
        !bool::from(tracelets_nf_equal(&store, &near_cert, &far_cert)),
        "so the certificate-level fast path must decline it"
    );
}

#[test]
fn a_certificate_that_does_not_replay_is_not_certified()
{
    // The certificate-level entry point collapses every obstruction to a
    // negative, the kill signals included; the direction of that collapse is
    // what the fast path rests on: a refusal never reads as an acceptance.
    let mut store = CellStore::new();
    let f = store.insert(f_cell());
    let peak = Toy::succ(Toy::zero());
    let join = Toy::zero();
    let fabricated = vec![CellApp {
        cell: f,
        at: at![0],
    }];
    assert!(
        matches!(
            normalize(&store, &peak, &join, &fabricated),
            Err(NormalFormObstruction::StepDoesNotFire { .. })
        ),
        "the recorded step names a position carrying no redex, so it has no normal form"
    );
    let certificate = tracelet_over(&peak, &join, fabricated.clone(), fabricated);
    assert!(
        !bool::from(tracelets_nf_equal(&store, &certificate, &certificate)),
        "so the fast path declines it, even against itself"
    );
}

#[test]
fn a_tracelet_pair_agreeing_only_on_its_first_leg_is_not_certified()
{
    // A tracelet is two derivations of one boundary, so the fast path is a
    // conjunction over both legs: the `path_a` legs here are one derivation and
    // the `path_b` legs the two orders of an overlapping pair.
    let (store, peak, first, second) = overlapping_pair();
    let forward = vec![first.clone(), second.clone()];
    let backward = vec![second, first];
    let join = run(&store, &peak, &forward);
    let left = tracelet_over(&peak, &join, forward.clone(), forward.clone());
    let right = tracelet_over(&peak, &join, forward, backward);
    assert!(
        !bool::from(tracelets_nf_equal(&store, &left, &right)),
        "one agreeing leg is not a certificate: both legs have to agree"
    );
    assert!(
        bool::from(replay_equivalent(&left, &right, &store)),
        "and the replay oracle identifies the pair all the same, so the negative is the \
         under-approximation rather than a claim that they differ"
    );
}

#[test]
fn two_interleaved_dependence_chains_layer_by_depth_and_not_by_position()
{
    // Two chains side by side, which a single chain cannot reach:
    //
    //   a @ [0,0] enclosed by x @ [0]
    //   b @ [1,0] enclosed by y @ [1]
    //
    // with every cross pair incomparable, so the layering is `{a, b}` then
    // `{x, y}`. A recurrence taking the earlier step's recorded index instead
    // of its depth is still a valid topological layering and agrees with every
    // single-chain fixture, but gives the two recorded orders of this one
    // trace class two different schedules. The depth recurrence gives one.
    let mut store = CellStore::new();
    let cell = store.insert(c_cell());
    let branch = Toy::add(Toy::add(Toy::zero(), Toy::zero()), Toy::zero());
    let peak = Toy::add(branch.clone(), branch);
    let left_foot = CellApp {
        cell,
        at: at![0, 0],
    };
    let left_head = CellApp { cell, at: at![0] };
    let right_foot = CellApp {
        cell,
        at: at![1, 0],
    };
    let right_head = CellApp { cell, at: at![1] };
    assert_eq!(
        PositionOrder::EnclosedBy,
        ToyAlphabet::position_order(&left_foot.at, &left_head.at),
        "the left head encloses the left foot, so the pair is dependent"
    );
    assert_eq!(
        PositionOrder::EnclosedBy,
        ToyAlphabet::position_order(&right_foot.at, &right_head.at),
        "and the right head encloses the right foot"
    );
    assert_eq!(
        PositionOrder::Incomparable,
        ToyAlphabet::position_order(&left_foot.at, &right_foot.at),
        "while the two chains' feet are disjoint"
    );
    assert_eq!(
        PositionOrder::Incomparable,
        ToyAlphabet::position_order(&left_head.at, &right_head.at),
        "and so are their heads"
    );
    let recorded = vec![
        left_foot.clone(),
        right_foot.clone(),
        left_head.clone(),
        right_head.clone(),
    ];
    let swapped = vec![right_foot, left_foot, right_head, left_head];
    let join = run(&store, &peak, &recorded);
    assert_eq!(
        Toy::add(Toy::zero(), Toy::zero()),
        join,
        "the four steps collapse both branches"
    );
    assert_eq!(
        join,
        run(&store, &peak, &swapped),
        "and the two recorded orders reach one term to begin with"
    );
    let recorded_nf = normalized(&store, &peak, &join, &recorded);
    let swapped_nf = normalized(&store, &peak, &join, &swapped);
    assert!(
        bool::from(nf_equal(&recorded_nf, &swapped_nf)),
        "the two recorded orders are one trace class, so they are one normal form"
    );
    let resolved = stored(&store, cell);
    let mut feet = vec![
        prim_address(resolved, &at![0, 0]),
        prim_address(resolved, &at![1, 0]),
    ];
    feet.sort_unstable();
    let mut heads = vec![
        prim_address(resolved, &at![0]),
        prim_address(resolved, &at![1]),
    ];
    heads.sort_unstable();
    let expected: Vec<PrimId> = feet.into_iter().chain(heads).collect();
    assert_eq!(
        expected, recorded_nf.schedule,
        "the schedule is layer zero then layer one, each ascending by content address"
    );
}

#[test]
fn an_alphabet_that_calls_nesting_incomparable_trips_the_kill_signal()
{
    // The two-layer fixture verbatim, over an alphabet whose `position_order`
    // answers `Incomparable` for every pair. With the enclosing pair reported
    // as commutable, all three applications land in layer zero and the
    // canonical schedule reaches the root while a leaf is still unreduced, so
    // the root's redex does not exist yet and the replayed schedule fails to
    // fire.
    let mut store: CellStore<Lying<IncomparablePositions>> = CellStore::new();
    let c = store.insert(lying_cell(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()));
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::zero()),
        Toy::add(Toy::zero(), Toy::zero()),
    );
    let left = CellApp {
        cell: c,
        at: at![0],
    };
    let right = CellApp {
        cell: c,
        at: at![1],
    };
    let root = CellApp { cell: c, at: at![] };
    let recorded = vec![left, right, root.clone()];
    let join = run(&store, &peak, &recorded);
    assert_eq!(Toy::zero(), join, "the recorded order collapses the spine");
    // The refusal is the non-firing arm only because the root's content address
    // does not sort last in the flattened layer; asserted rather than assumed.
    let cell = stored(&store, c);
    let root_address = prim_address(cell, &at![]);
    let left_address = prim_address(cell, &at![0]);
    let right_address = prim_address(cell, &at![1]);
    assert!(
        root_address < left_address.max(right_address),
        "the fixture needs the root application not to come last in the flattened layer"
    );
    let refusal = normalize(&store, &peak, &join, &recorded)
        .expect_err("the licensed transposition produces a schedule that cannot fire");
    assert_eq!(
        NormalFormObstruction::ShiftedScheduleDoesNotFire {
            step: Box::new(root)
        },
        refusal,
        "the kill signal names the canonical step that carried no redex"
    );
    // The same derivation over the honest alphabet normalizes, so the refusal
    // is attributable to the alphabet's one lie.
    let mut honest = CellStore::new();
    let honest_c = honest.insert(c_cell());
    let honest_path = vec![
        CellApp {
            cell: honest_c,
            at: at![0],
        },
        CellApp {
            cell: honest_c,
            at: at![1],
        },
        CellApp {
            cell: honest_c,
            at: at![],
        },
    ];
    assert!(
        normalize(&honest, &peak, &join, &honest_path).is_ok(),
        "the honest alphabet keeps the enclosing application last and normalizes"
    );
}

#[test]
fn a_non_local_term_algebra_trips_the_kill_signal_at_the_join()
{
    // Both guard premises hold honestly here: the positions are incomparable
    // and the cell has trivial overlap with itself. The alphabet's splice is
    // what lies, a rewrite at `[i]` also resetting `[1-i]`, so the two
    // applications do not commute although nothing about positions or cell
    // contents can say so. Both orders fire and reach different terms.
    let mut store: CellStore<Lying<NonLocalSplice>> = CellStore::new();
    let c = store.insert(lying_cell(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()));
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::zero()),
        Toy::add(Toy::zero(), Toy::zero()),
    );
    let cell = stored(&store, c);
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<NonLocalSplice> as CellAlphabet>::position_order(&at![0], &at![1]),
        "the positions are honestly incomparable"
    );
    assert!(
        overlaps_between((c, cell), (c, cell)).is_empty(),
        "and the cell has honestly trivial overlap with itself"
    );
    let low = CellApp {
        cell: c,
        at: at![0],
    };
    let high = CellApp {
        cell: c,
        at: at![1],
    };
    // A one-layer schedule is ascending address order, so recording the
    // descending one makes the canonical schedule the transposition.
    let (first, second) = if prim_address(cell, &low.at) < prim_address(cell, &high.at) {
        (high, low)
    }
    else {
        (low, high)
    };
    let recorded = vec![first, second];
    let transposed: Vec<CellApp<Lying<NonLocalSplice>>> = recorded.iter().rev().cloned().collect();
    let join = run(&store, &peak, &recorded);
    let elsewhere = run(&store, &peak, &transposed);
    assert_ne!(
        join, elsewhere,
        "the two orders fire and reach different terms"
    );
    let refusal = normalize(&store, &peak, &join, &recorded)
        .expect_err("the licensed transposition reaches a different join");
    assert_eq!(
        NormalFormObstruction::ShiftedScheduleMissesTheJoin {
            reached: Box::new(elsewhere)
        },
        refusal,
        "the kill signal carries the term the canonical schedule reached"
    );
}

#[test]
fn a_withheld_convexity_warrant_empties_the_shift_quotient()
{
    // Both shipped alphabets discharge the convexity conjunct for every store,
    // so only an alphabet withholding it shows that the normal form asks, that
    // it layers under the answer, and that it records the warrant it used.
    // With the warrant withheld every pair is dependent and the quotient is
    // empty: two orders of a pairwise independent spine stay apart.
    let count = RedexCount(3_usize);
    let mut store: CellStore<Lying<WithheldConvexity>> = CellStore::new();
    let f = store.insert(lying_cell(Toy::succ(Toy::zero()), Toy::zero()));
    let peak = spine(count);
    let recorded: Vec<CellApp<Lying<WithheldConvexity>>> = spine_positions(count)
        .into_iter()
        .map(|position| CellApp {
            cell: f,
            at: position,
        })
        .collect();
    let reversed: Vec<CellApp<Lying<WithheldConvexity>>> = recorded.iter().rev().cloned().collect();
    let join = run(&store, &peak, &recorded);
    assert_eq!(
        join,
        run(&store, &peak, &reversed),
        "the spine's redexes commute semantically, whatever the warrant says"
    );
    let recorded_nf = normalized(&store, &peak, &join, &recorded);
    let reversed_nf = normalized(&store, &peak, &join, &reversed);
    assert_eq!(
        ConvexityDischarge::ReCheckRequired,
        recorded_nf.convexity,
        "the normal form records the warrant it was taken under"
    );
    let cell = stored(&store, f);
    let expected: Vec<PrimId> = recorded
        .iter()
        .map(|step| prim_address(cell, &step.at))
        .collect();
    assert_eq!(
        expected, recorded_nf.schedule,
        "with no warrant no transposition is licensed, so the schedule is the recorded order"
    );
    assert!(
        !bool::from(nf_equal(&recorded_nf, &reversed_nf)),
        "so the two orders are two normal forms: the quotient is empty here"
    );
    // The identical spine over the honest alphabet identifies exactly this
    // pair.
    let mut honest = CellStore::new();
    let honest_f = honest.insert(f_cell());
    let honest_recorded: Vec<CellApp<ToyAlphabet>> = spine_positions(count)
        .into_iter()
        .map(|position| CellApp {
            cell: honest_f,
            at: position,
        })
        .collect();
    let honest_reversed: Vec<CellApp<ToyAlphabet>> =
        honest_recorded.iter().rev().cloned().collect();
    let honest_join = run(&honest, &peak, &honest_recorded);
    let honest_nf = normalized(&honest, &peak, &honest_join, &honest_recorded);
    let honest_reversed_nf = normalized(&honest, &peak, &honest_join, &honest_reversed);
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        honest_nf.convexity,
        "the toy alphabet discharges the conjunct"
    );
    assert!(
        bool::from(nf_equal(&honest_nf, &honest_reversed_nf)),
        "and with the warrant in hand the same two orders are one normal form"
    );
}

#[test]
fn two_primitives_sharing_a_content_address_are_refused_rather_than_merged()
{
    // The address orders and is nowhere the identity witness: two structurally
    // distinct cells whose difference the digest cannot see are two primitives
    // under one key, and the normal form is declined rather than merged.
    // Within one store a content has one identifier, so over the shipped
    // alphabets the arm is dead; it lives once a field of a cell is outside
    // the digest's reach, which the colliding alphabet arranges legally: its
    // orientation tag hashes to nothing.
    let mut store: CellStore<Lying<CollidingAddresses>> = CellStore::new();
    let faces = (
        Toy::add(Toy::zero(), Toy::var("x")),
        Toy::add(Toy::zero(), Toy::succ(Toy::var("x"))),
    );
    let given = store.insert(lying_cell(faces.0.clone(), faces.1.clone()));
    let derived = store.insert(reoriented_lying_cell(faces.0, faces.1));
    assert_ne!(
        given, derived,
        "the store holds the two orientations under two identifiers"
    );
    let first = CellApp {
        cell: given,
        at: at![],
    };
    let second = CellApp {
        cell: derived,
        at: at![],
    };
    let peak = Toy::add(Toy::zero(), Toy::zero());
    let recorded = vec![first.clone(), second.clone()];
    let join = run(&store, &peak, &recorded);
    assert_eq!(
        Toy::add(Toy::zero(), Toy::succ(Toy::succ(Toy::zero()))),
        join,
        "each application wraps the second argument once more, so both fire and both move it"
    );
    let address = prim_address(stored(&store, given), &at![]);
    assert_eq!(
        address,
        prim_address(stored(&store, derived), &at![]),
        "the digest cannot see the orientation the two cells differ in"
    );
    assert_ne!(first, second, "and the two recorded steps are not one step");
    let refusal = normalize(&store, &peak, &join, &recorded)
        .expect_err("two primitives under one address are refused, never merged");
    assert_eq!(
        NormalFormObstruction::ContentAddressCollision {
            address,
            held: Box::new(PrimCert(first)),
            offered: Box::new(PrimCert(second)),
        },
        refusal,
        "the refusal names the shared address and both primitives"
    );
}

#[test]
fn the_metavariable_seam_is_what_keeps_a_diverging_nested_pair_dependent()
{
    // A reachability premise, pinned so it fails when it changes. `swap` and
    // `peel` at nested positions fire in either order and reach different
    // terms, so licensing their transposition would hand the normal form a
    // firing, diverging schedule. Over an alphabet calling every position pair
    // incomparable, only the overlap conjunct keeps them dependent, and it
    // holds because the enumerator treats a metavariable position in a
    // right-hand side as a composition seam. When that changes, the `Ok` below
    // becomes the shifted-schedule-misses-the-join refusal, and this fixture
    // becomes that arm's witness over an honest term algebra.
    let mut store: CellStore<Lying<IncomparablePositions>> = CellStore::new();
    let swap = store.insert(lying_cell(
        Toy::add(Toy::var("x"), Toy::var("y")),
        Toy::add(Toy::var("y"), Toy::var("x")),
    ));
    let peel = store.insert(lying_cell(Toy::succ(Toy::var("m")), Toy::var("m")));
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero())));
    let outer = CellApp {
        cell: swap,
        at: at![],
    };
    let inner = CellApp {
        cell: peel,
        at: at![0],
    };
    let swap_cell = stored(&store, swap);
    let peel_cell = stored(&store, peel);
    let forward = vec![outer.clone(), inner.clone()];
    let backward = vec![inner, outer];
    assert_ne!(
        run(&store, &peak, &forward),
        run(&store, &peak, &backward),
        "the two orders fire and reach different terms"
    );
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<IncomparablePositions> as CellAlphabet>::position_order(&at![], &at![0]),
        "this alphabet reports the nesting pair as commutable"
    );
    assert!(
        !overlaps_between((swap, swap_cell), (peel, peel_cell)).is_empty(),
        "and the enumerator answers a composition overlap at the swap's hole"
    );
    assert!(
        !overlaps_between((peel, peel_cell), (swap, swap_cell)).is_empty(),
        "in the other ordered direction too, at the peel's own hole"
    );
    let (descending, ascending) =
        if prim_address(swap_cell, &at![]) < prim_address(peel_cell, &at![0]) {
            (&backward, &forward)
        }
        else {
            (&forward, &backward)
        };
    let join = run(&store, &peak, descending);
    let normal = normalize(&store, &peak, &join, descending)
        .expect("the overlapping pair keeps its recorded order, so the schedule replays");
    let addresses = |path: &[CellApp<Lying<IncomparablePositions>>]| -> Vec<PrimId> {
        path.iter()
            .map(|step| prim_address(stored(&store, step.cell), &step.at))
            .collect()
    };
    assert_eq!(
        addresses(descending),
        normal.schedule,
        "the recorded order survives, although the ascending address order is the other one"
    );
    assert_ne!(
        addresses(descending),
        addresses(ascending),
        "and the two orders really are two different schedules"
    );
}

#[test]
fn the_dependence_edges_are_the_pairs_the_guard_refuses()
{
    // (c) overlaps nothing, so independence on this fixture is exactly "the
    // two positions are incomparable" and the edges can be written in full.
    let fixture = three_layer_fixture();
    let order = event_order(&fixture.store, &fixture.peak, &fixture.recorded())
        .expect("the derivation replays");
    let inner = EventIndex::from(0_usize);
    let middle = EventIndex::from(1_usize);
    let branch = EventIndex::from(2_usize);
    let root = EventIndex::from(3_usize);
    assert!(
        bool::from(order.depends_directly(middle, inner)),
        "the middle application encloses the inner one"
    );
    assert!(
        !bool::from(order.depends_directly(branch, inner)),
        "the branch application is incomparable with the inner one"
    );
    assert!(
        !bool::from(order.depends_directly(branch, middle)),
        "and with the middle one"
    );
    for earlier in [inner, middle, branch] {
        assert!(
            bool::from(order.depends_directly(root, earlier)),
            "the root application encloses every other"
        );
    }
    assert!(
        bool::from(order.precedes(inner, root)),
        "so the inner application precedes the root one"
    );
    assert!(
        bool::from(order.concurrent(inner, branch)),
        "and the two independent leaves are concurrent"
    );
    assert!(
        !bool::from(order.concurrent(inner, middle)),
        "while a dependent pair is not"
    );
}

#[test]
fn a_three_layer_derivation_gives_three_layers()
{
    let fixture = three_layer_fixture();
    let order = event_order(&fixture.store, &fixture.peak, &fixture.recorded())
        .expect("the derivation replays");
    let layers = order.layers();
    assert_eq!(
        3_usize,
        layers.len(),
        "two independent leaves, then the enclosing middle, then the root"
    );
    let sizes: Vec<usize> = layers.iter().map(Vec::len).collect();
    assert_eq!(
        vec![2_usize, 1_usize, 1_usize],
        sizes,
        "and the widest layer is the deepest one"
    );
    let first = layers.first().expect("there is a first layer");
    assert!(
        first.contains(&EventIndex::from(0_usize)) && first.contains(&EventIndex::from(2_usize)),
        "the first layer is exactly the two applications depending on nothing"
    );
    assert_eq!(
        Some(&vec![EventIndex::from(3_usize)]),
        layers.get(2_usize),
        "and the root application sits alone in the deepest layer"
    );
}

#[test]
fn an_independent_pair_is_reordered_by_licensed_transpositions()
{
    // A non-trivial exchange: the branch application is independent of both
    // applications it moves past, so bringing it to the front costs two
    // licensed adjacent swaps and leaves the dependent inner and middle
    // applications as recorded.
    let fixture = three_layer_fixture();
    let order = event_order(&fixture.store, &fixture.peak, &fixture.recorded())
        .expect("the derivation replays");
    let target = vec![
        EventIndex::from(2_usize),
        EventIndex::from(0_usize),
        EventIndex::from(1_usize),
        EventIndex::from(3_usize),
    ];
    let witness = order
        .exchange_between(&order.recorded_order(), &target)
        .expect("the branch application is independent of both it passes");
    assert_eq!(
        TranspositionCount::from(2_usize),
        witness.transposition_count(),
        "two adjacent swaps carry it to the front"
    );
    assert_eq!(
        Maybe::Present(target),
        witness.apply(&order.recorded_order()),
        "and applying them reproduces the target order"
    );
}

#[test]
fn a_containment_dependent_pair_refuses_its_transposition()
{
    // The exchange kill signal over the toy alphabet, where dependence is
    // position containment rather than the sequent alphabet's single command
    // position.
    let fixture = three_layer_fixture();
    let order = event_order(&fixture.store, &fixture.peak, &fixture.recorded())
        .expect("the derivation replays");
    let inner = EventIndex::from(0_usize);
    let middle = EventIndex::from(1_usize);
    let refusal = order.exchange_between(&order.recorded_order(), &[
        middle,
        inner,
        EventIndex::from(2_usize),
        EventIndex::from(3_usize),
    ]);
    assert_eq!(
        Err(ExchangeObstruction::DependentTransposition {
            earlier: inner,
            later: middle,
        }),
        refusal,
        "the middle application encloses the inner one, so they do not commute"
    );
}

#[test]
fn the_canonical_order_is_the_same_in_two_differently_ordered_stores()
{
    // The rule is interned under a different identifier in each store, and the
    // keys, the order and the emitted schedule all agree; a key that had picked
    // up an arrival index or a store handle would separate them.
    let height = TreeHeight(2_usize);
    let keys = vec![LayerSortKey::default(); 7_usize];
    let (plain, plain_cell, peak, layers) = tree_fixture(height);
    let (decoyed, decoy_cell, decoy_peak, decoy_layers) = tree_fixture_behind_a_decoy(height);
    assert_ne!(
        plain_cell, decoy_cell,
        "the same rule carries two identifiers"
    );
    assert_eq!(peak, decoy_peak, "and the two peaks are one term");
    let recorded = tree_path(plain_cell, layers, &keys);
    let decoy_recorded = tree_path(decoy_cell, decoy_layers, &keys);
    let here = event_order(&plain, &peak, &recorded).expect("the derivation replays");
    let there = event_order(&decoyed, &decoy_peak, &decoy_recorded).expect("and so does its twin");
    assert_eq!(
        7_usize,
        canonical_keys(&here).len(),
        "a height-two tree has seven events, so the comparison is not vacuous"
    );
    assert_eq!(
        canonical_keys(&here),
        canonical_keys(&there),
        "the canonical key sequence is the same in both stores"
    );
    let join = run(&plain, &peak, &recorded);
    assert_eq!(
        normalized(&plain, &peak, &join, &recorded).schedule,
        normalized(&decoyed, &decoy_peak, &join, &decoy_recorded).schedule,
        "and so is the schedule the normalizer emits from it"
    );
}

#[test]
fn the_order_taken_alone_agrees_with_the_normalizers()
{
    // The event order is reachable without a join, and the normalizer layers
    // by the same object rather than a second copy of the relation; if the two
    // diverged the schedules would, and this is where that shows.
    let fixture = three_layer_fixture();
    let recorded = fixture.recorded();
    let order =
        event_order(&fixture.store, &fixture.peak, &recorded).expect("the derivation replays");
    let normal = normalized(&fixture.store, &fixture.peak, &fixture.join, &recorded);
    let addresses: Vec<PrimId> = order
        .canonical_order()
        .into_iter()
        .filter_map(|index| match order.event(index) {
            | Maybe::Present(event) => Some(event.address()),
            | Maybe::Absent(_) => None,
        })
        .collect();
    assert_eq!(
        normal.schedule, addresses,
        "the normal form's schedule is this order's canonical order, flattened"
    );
    let witness = normalize_certified(&fixture.store, &fixture.peak, &fixture.join, &recorded)
        .expect("the derivation normalizes");
    assert_eq!(
        &order,
        witness.event_order(),
        "and the receipt carries that same order"
    );
}

proptest! {
    // Each case pays two replays per derivation plus a quadratic number of
    // independence questions, so the case count is modest by design.
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Any permutation of pairwise-independent redexes normalizes to one normal
    /// form: the shift quotient doing the work it exists for.
    #[test]
    fn a_shuffled_independent_schedule_has_one_normal_form(
        (count, order) in (2_usize ..= 6_usize).prop_flat_map(|count| {
            (Just(count), Just((0 .. count).collect::<Vec<usize>>()).prop_shuffle())
        })
    ) {
        let count = RedexCount(count);
        let (store, _f, peak, canonical) = spine_fixture(count);
        let join = run(&store, &peak, &canonical);
        let shuffled: Vec<CellApp<ToyAlphabet>> =
            order.iter().map(|index| canonical[*index].clone()).collect();
        prop_assert_eq!(
            &join,
            &run(&store, &peak, &shuffled),
            "the permuted schedule reaches the same term to begin with"
        );
        let canonical_nf = normalized(&store, &peak, &join, &canonical);
        let shuffled_nf = normalized(&store, &peak, &join, &shuffled);
        prop_assert!(
            bool::from(nf_equal(&canonical_nf, &shuffled_nf)),
            "the two schedules are one normal form"
        );
        prop_assert_eq!(
            canonical_nf.schedule.len(),
            count.0,
            "and no primitive was lost to the quotient"
        );
    }

    /// The differential: every generated normal-form-equal pair satisfies the
    /// replay oracle, with the antecedent asserted so a generator that stopped
    /// producing such pairs fails rather than passes vacuously.
    #[test]
    fn every_nf_equal_pair_is_replay_equivalent(
        (count, order) in (2_usize ..= 6_usize).prop_flat_map(|count| {
            (Just(count), Just((0 .. count).collect::<Vec<usize>>()).prop_shuffle())
        })
    ) {
        let (store, _f, peak, canonical) = spine_fixture(RedexCount(count));
        let join = run(&store, &peak, &canonical);
        let shuffled: Vec<CellApp<ToyAlphabet>> =
            order.iter().map(|index| canonical[*index].clone()).collect();
        let left = tracelet_over(&peak, &join, canonical.clone(), canonical);
        let right = tracelet_over(&peak, &join, shuffled.clone(), shuffled);
        prop_assert!(
            bool::from(tracelets_nf_equal(&store, &left, &right)),
            "non-vacuity: the generator produces normal-form-equal pairs"
        );
        prop_assert!(
            bool::from(replay_equivalent(&left, &right, &store)),
            "normal-form-equal implies replay-equal; a failure here is the kill signal"
        );
    }
}

proptest! {
    // The generated tree has at most seven events, so the cubic transitivity
    // sweep is bounded well inside a property run.
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Causal precedence is a strict partial order: irreflexive, asymmetric and
    /// transitive, on every generated derivation.
    #[test]
    fn causal_precedence_is_a_strict_partial_order((height, keys) in tree_case()) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let join = run(&store, &peak, &recorded);
        prop_assert_eq!(&Toy::zero(), &join, "the tree collapses, so the layering is a firing order");
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let events = usize::from(order.event_count());
        for left in (0 .. events).map(EventIndex::from) {
            prop_assert!(!bool::from(order.precedes(left, left)), "precedence is irreflexive");
            for right in (0 .. events).map(EventIndex::from) {
                if !bool::from(order.precedes(left, right)) {
                    continue;
                }
                prop_assert!(!bool::from(order.precedes(right, left)), "precedence is asymmetric");
                for far in (0 .. events).map(EventIndex::from) {
                    if bool::from(order.precedes(right, far)) {
                        prop_assert!(bool::from(order.precedes(left, far)), "precedence is transitive");
                    }
                }
            }
        }
    }

    /// Independence is symmetric and irreflexive, on every generated
    /// derivation: an asymmetric relation would make a licensed transposition
    /// change which pairs count as dependent, and depths would stop being a
    /// property of the derivation.
    #[test]
    fn independence_is_symmetric_and_irreflexive((height, keys) in tree_case()) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let events = usize::from(order.event_count());
        for left in (0 .. events).map(EventIndex::from) {
            prop_assert!(!bool::from(order.independent(left, left)), "a step is always dependent on itself");
            for right in (0 .. events).map(EventIndex::from) {
                prop_assert_eq!(
                    order.independent(left, right),
                    order.independent(right, left),
                    "independence does not read the argument order"
                );
            }
        }
    }

    /// Two events at one depth are causally unordered: the theorem that makes a
    /// layer a batch rather than a coincidence of the sort.
    #[test]
    fn events_sharing_a_layer_are_pairwise_concurrent((height, keys) in tree_case()) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        for layer in order.layers() {
            for left in &layer {
                for right in layer.iter().filter(|right| *right != left) {
                    prop_assert!(
                        bool::from(order.concurrent(*left, *right)),
                        "a dependent pair has strictly increasing depth, so a shared depth is an antichain"
                    );
                }
            }
        }
    }

    /// The layers partition the canonical order, in ascending depth.
    #[test]
    fn the_layers_concatenate_to_the_canonical_order((height, keys) in tree_case()) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let mut flattened: Vec<EventIndex> = Vec::new();
        let mut held: Option<CausalDepth> = None;
        for layer in order.layers() {
            prop_assert!(!layer.is_empty(), "a layer is never empty");
            let depth = order.depth(layer[0]);
            if let (Some(previous), Maybe::Present(current)) = (held, depth) {
                prop_assert!(previous < current, "the layers ascend in depth");
            }
            for index in &layer {
                prop_assert_eq!(depth, order.depth(*index), "every event in one layer shares its depth");
            }
            if let Maybe::Present(current) = depth {
                held = Some(current);
            }
            flattened.extend_from_slice(&layer);
        }
        prop_assert_eq!(
            order.canonical_order(),
            flattened,
            "and the layers concatenate to the canonical order"
        );
    }

    /// No two events tie on the canonical sort key, or the canonical order
    /// would depend on the recorded one through the sort's stability.
    #[test]
    fn the_canonical_key_never_ties((height, keys) in tree_case()) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let events = usize::from(order.event_count());
        for left in (0 .. events).map(EventIndex::from) {
            for right in (0 .. events).map(EventIndex::from).filter(|right| *right != left) {
                let same_depth = order.depth(left) == order.depth(right);
                let same_address = order.event(left).map(DerivationEvent::address)
                    == order.event(right).map(DerivationEvent::address);
                prop_assert!(
                    !(same_depth && same_address),
                    "two events sharing both key components would make the sort's stability observable"
                );
            }
        }
    }

    /// An exchange witness performs the rearrangement it describes.
    #[test]
    fn an_exchange_witness_replays_to_its_target_order((height, keys) in tree_case()) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let witness = order
            .exchange_to_canonical()
            .expect("the canonical key is a linear extension of the causal order");
        prop_assert_eq!(
            Maybe::Present(order.canonical_order()),
            witness.apply(&order.recorded_order()),
            "applying the witness to the recorded order gives the canonical one"
        );
        prop_assert_eq!(
            order.recorded_order() == order.canonical_order(),
            witness.transposition_count() == TranspositionCount::from(0_usize),
            "and the witness is empty exactly when the two orders already coincide"
        );
    }

    /// The canonical order is always reachable from the recorded one by
    /// licensed adjacent transpositions, each re-asked of the independence
    /// relation rather than taken on the witness's word: the canonical key is
    /// a linear extension of the causal order, so the normal form stays inside
    /// the trace class.
    #[test]
    fn the_canonical_order_is_always_reachable_by_licensed_transpositions(
        (height, keys) in tree_case()
    ) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let witness = order.exchange_to_canonical().expect(
            "the exchange kill signal: canonicalization transposed a dependent pair, so the \
             canonical key is not a linear extension of the causal order",
        );
        let mut current = order.recorded_order();
        for transposition in witness.transpositions() {
            let below = usize::from(transposition.position());
            let above = below.saturating_add(1_usize);
            prop_assert!(
                bool::from(order.independent(current[below], current[above])),
                "every transposition the witness performs swaps an independent pair"
            );
            current.swap(below, above);
        }
        prop_assert_eq!(order.canonical_order(), current, "and the swaps land on the canonical order");
    }

    /// Depth is the length of the longest dependence chain strictly below the
    /// event under the transitive closure of dependence, which the recurrence
    /// computes over the direct edges.
    #[test]
    fn the_depth_is_the_longest_chain_strictly_below((height, keys) in tree_case()) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let events = usize::from(order.event_count());
        for later in (0 .. events).map(EventIndex::from) {
            let mut longest = 0_usize;
            for earlier in (0 .. events).map(EventIndex::from) {
                if !bool::from(order.precedes(earlier, later)) {
                    continue;
                }
                let Maybe::Present(below) = order.depth(earlier)
                else {
                    continue;
                };
                longest = longest.max(usize::from(below).saturating_add(1_usize));
            }
            prop_assert_eq!(
                Maybe::Present(CausalDepth::from(longest)),
                order.depth(later),
                "the depth is the longest chain strictly below under precedence"
            );
        }
    }

    /// Transposing any adjacent independent pair of the recorded derivation
    /// leaves the canonical key sequence fixed: the canonical order reads only
    /// the labeled causal partial order. Keys rather than indices are compared,
    /// because a transposition renumbers the events.
    #[test]
    fn every_adjacent_independent_transposition_leaves_the_canonical_order_fixed(
        (height, keys) in tree_case()
    ) {
        let (store, cell, peak, layers) = tree_fixture(height);
        let recorded = tree_path(cell, layers, &keys);
        let join = run(&store, &peak, &recorded);
        let order = event_order(&store, &peak, &recorded)
            .expect("the layered derivation replays, so it has an event order");
        let expected = canonical_keys(&order);
        let events = usize::from(order.event_count());
        let mut exercised = 0_usize;
        for below in 0 .. events.saturating_sub(1_usize) {
            let above = below.saturating_add(1_usize);
            if !bool::from(order.independent(EventIndex::from(below), EventIndex::from(above))) {
                continue;
            }
            exercised = exercised.saturating_add(1_usize);
            let mut swapped = recorded.clone();
            swapped.swap(below, above);
            prop_assert_eq!(
                &join,
                &run(&store, &peak, &swapped),
                "an independent transposition reaches the same term to begin with"
            );
            let shifted = event_order(&store, &peak, &swapped)
                .expect("and the transposed derivation has an event order too");
            prop_assert_eq!(
                &expected,
                &canonical_keys(&shifted),
                "so the canonical order reads only the labeled causal order"
            );
        }
        // Every tree above the degenerate one opens with a layer of at least
        // two adjacent independent events, so a run that transposed nothing
        // would be one whose independence relation had gone silent.
        prop_assert!(
            events < 2_usize || exercised > 0_usize,
            "a derivation with more than one event has an adjacent independent pair"
        );
    }
}
