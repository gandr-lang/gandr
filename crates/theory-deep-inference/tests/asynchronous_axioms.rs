//! The asynchronous-graph axioms for the shift quotient: determinism and the
//! cube property, checked against the shift witness as built.
//!
//! An asynchronous graph `(G, ◇)` is a graph `G` with a set `◇` of squares,
//! pairs `(p, q)` of length-2 paths sharing a source and a target, satisfying
//! three properties (Melliès, *Asynchronous Template Games and the Gray Tensor
//! Product of 2-Categories*, LICS 2021):
//!
//! 1. **symmetry**: `p ◇ q` implies `q ◇ p`;
//! 2. **determinism**: `p ◇ q` and `p ◇ q'` imply `q = q'`;
//! 3. **the cube property**: for paths `p = u₁·u₂·u₃` and `q = v₁·v₂·v₃` of
//!    length 3 sharing a source and a target, there are edges `w₃, u₂', v₂'`
//!    and tiles `u₂·u₃ ◇ u₂'·w₃`, `u₁·u₂' ◇ v₁·v₂'`, `v₂'·w₃ ◇ v₂·v₃` if and
//!    only if there are edges `w₁, u₂'', v₂''` and tiles `u₁·u₂ ◇ w₁·u₂''`,
//!    `u₂''·u₃ ◇ v₂''·v₃`, `w₁·v₂'' ◇ v₁·v₂`: the braid relation on permutation
//!    tiles.
//!
//! The pairing is fixed, because the axioms are not invariant under another:
//! a vertex is a term, an edge is one labelled firing `(cell, position)` at a
//! term, and a square is a tile exactly when the shift witness is earned at the
//! shared source with the two paths as its sequentializations.
//!
//! **Determinism holds**: firing is a function of `(cell, term, position)`,
//! and a tile's two paths carry the same two labels transposed, so a 2-path
//! determines its witness and the other path. The cells are not deterministic
//! as a rewrite system, two cells firing at one position, but the guard
//! refuses a pair at one position before any tile exists.
//!
//! **The cube property holds**: the guard reads the store, the two cells and
//! the two positions, never the peak, so a tile at one vertex is a tile
//! wherever both applications still fire, and firing one at an incomparable
//! position leaves the other firing. Both chains then need the same three
//! pairwise tiles. Both verdicts are small-scope exhaustive over the fixture
//! family, with both chains searched over the graph's edges.
//!
//! Both arguments use locality of splicing: rewriting at one position leaves
//! an incomparable position's subterm untouched. Both shipped alphabets
//! satisfy it and a fixture here pins it; an alphabet violating it breaks both
//! axioms silently, which the non-local adversary in the normal-form suite
//! exhibits.

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::rewrite_at;
use gandr_theory_deep_inference::ShiftObstruction;
use gandr_theory_deep_inference::derive_shift_equivalence;
use quenchant_shape::shape::Maybe;

use crate::fixture::fire;
use crate::fixture::run;

/// Whether a searched-for tile or chain of tiles is there.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Presence
{
    /// The graph exhibits it.
    Present,
    /// It is not there.
    Absent,
}

/// One labelled 3-path, its three edges in firing order.
type ThreePath<'path> = (
    &'path CellApp<ToyAlphabet>,
    &'path CellApp<ToyAlphabet>,
    &'path CellApp<ToyAlphabet>,
);

/// One element of `◇`: a pair of 2-paths sharing a source and a target.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Square
{
    /// The first of the two paths.
    path: Vec<CellApp<ToyAlphabet>>,
    /// The path it is tiled with.
    other: Vec<CellApp<ToyAlphabet>>,
}

/// (a): `Add(Succ(Zero), Zero) ~> Zero`.
///
/// # Specification
/// trivial.
fn cube_a() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::add(Toy::succ(Toy::zero()), Toy::zero()), Toy::zero())
}

/// (b): `Add(Zero, Succ(Zero)) ~> Succ(Succ(Zero))`.
///
/// # Specification
/// trivial.
fn cube_b() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
        Toy::succ(Toy::succ(Toy::zero())),
    )
}

/// (c): `Add(Succ(Zero), Succ(Zero)) ~> Succ(Succ(Succ(Zero)))`.
///
/// The three cells are ground on both faces, pairwise non-overlapping, and
/// their reducts match no left-hand side in the store, so the fixture's graph
/// has exactly the edges the fixture puts there.
///
/// # Specification
/// trivial.
fn cube_c() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero())),
        Toy::succ(Toy::succ(Toy::succ(Toy::zero()))),
    )
}

/// (c-into-a): `Add(Succ(Zero), Succ(Zero)) ~> Add(Succ(Zero), Zero)`, whose
/// right-hand side is (a)'s left-hand side, so the pair `(a, c-into-a)`
/// overlaps and is refused the witness: one face of the cube removed.
///
/// # Specification
/// trivial.
fn cube_c_into_a() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero())),
        Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
    )
}

/// The three-redex peak `Add(a-redex, Add(b-redex, c-redex))`.
///
/// # Specification
/// trivial.
fn cube_peak() -> Toy
{
    Toy::add(
        Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
        Toy::add(
            Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
            Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero())),
        ),
    )
}

/// A store holding three cells and their applications at the cube peak's
/// three redexes.
///
/// # Specification
/// trivial.
fn cube_over(
    cells: [Cell<ToyAlphabet>; 3]
) -> (
    CellStore<ToyAlphabet>,
    CellApp<ToyAlphabet>,
    CellApp<ToyAlphabet>,
    CellApp<ToyAlphabet>,
)
{
    let mut store = CellStore::new();
    let [left, middle, right] = cells.map(|cell| store.insert(cell));
    (
        store,
        CellApp {
            cell: left,
            at: at![0],
        },
        CellApp {
            cell: middle,
            at: at![1, 0],
        },
        CellApp {
            cell: right,
            at: at![1, 1],
        },
    )
}

/// The three-cell store and the three applications the cube is built from.
///
/// # Specification
/// trivial.
fn cube_fixture() -> (
    CellStore<ToyAlphabet>,
    CellApp<ToyAlphabet>,
    CellApp<ToyAlphabet>,
    CellApp<ToyAlphabet>,
)
{
    cube_over([cube_a(), cube_b(), cube_c()])
}

/// Every edge out of `term`: one per `(cell, position)` pair that fires.
///
/// # Specification
/// - ensures: exactly one application for every stored-cell and
///   command-position pair that fires at `term`; no other application is
///   returned.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — finite toy terms and fixture stores. The full
///   position/cell grid, successful rewrites and output cardinality validate
///   the edge set without prescribing enumeration order. Cube and branching
///   fixtures separate missing edges, invented firings and duplicated
///   applications.
/// - witness: `tests::asynchronous_axioms::every_permutation_tile_is_symmetric`
/// - witness: `tests::asynchronous_axioms::rewrite_branching_never_reaches_the_tile_set`
#[spec(ensures: |output| {
    let mut count = 0_usize;
    for position in ToyAlphabet::command_positions(term) {
        for (id, cell) in store.iter() {
            if matches!(rewrite_at(cell, term, &position), Maybe::Present(_)) {
                count = count.saturating_add(1);
                if !output.iter().any(|step| step.cell == id && step.at == position) {
                    return false;
                }
            }
        }
    }
    output.len() == count
})]
fn edges_at(
    store: &CellStore<ToyAlphabet>,
    term: &Toy,
) -> Vec<CellApp<ToyAlphabet>>
{
    let mut out = Vec::new();
    for position in ToyAlphabet::command_positions(term) {
        for (id, cell) in store.iter() {
            if matches!(rewrite_at(cell, term, &position), Maybe::Present(_)) {
                out.push(CellApp {
                    cell: id,
                    at: position.clone(),
                });
            }
        }
    }
    out
}

/// Whether the square `(path, other)` out of `vertex` is a permutation tile.
///
/// The tile set has one generator, the shift witness, so this is its
/// definition: the square is a tile exactly when the witness for `path`
/// exists and `other` is its other sequentialization.
///
/// # Specification
/// - ensures: Present exactly when the guard licenses `path` and `other` is
///   that same labelled pair in reverse order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — positive cube tiles, a branching same-position pair and a
///   cube missing one face. Exact label reversal and the guard result
///   distinguish a common endpoint from a licensed tile, and a wrong residual
///   label from the required swap.
/// - witness: `tests::asynchronous_axioms::the_cube_property_holds_for_every_pair_of_three_paths`
/// - witness: `tests::asynchronous_axioms::a_missing_pairwise_tile_removes_both_cube_routes`
#[spec(ensures: |output| (output == Presence::Present) == (other.0 == path.1 && other.1 == path.0
    && derive_shift_equivalence(store, vertex, path.0, path.1).is_ok()))]
fn is_tile(
    store: &CellStore<ToyAlphabet>,
    vertex: &Toy,
    path: (&CellApp<ToyAlphabet>, &CellApp<ToyAlphabet>),
    other: (&CellApp<ToyAlphabet>, &CellApp<ToyAlphabet>),
) -> Presence
{
    let Ok(witness) = derive_shift_equivalence(store, vertex, path.0, path.1)
    else {
        return Presence::Absent;
    };
    if witness.second_then_first() == [other.0.clone(), other.1.clone()] {
        Presence::Present
    }
    else {
        Presence::Absent
    }
}

/// Search for the first chain of the cube property: edges `w₃, u₂', v₂'` with
/// `u₂·u₃ ◇ u₂'·w₃`, `u₁·u₂' ◇ v₁·v₂'`, `v₂'·w₃ ◇ v₂·v₃`.
///
/// # Specification
/// - requires: the first identifier of each input path belongs to `store`.
/// - ensures: Present exactly when the three stated front tiles have a witness
///   among the graph's edges; a present chain makes both paths fire completely
///   to one term.
/// - panics: an unstored first identifier is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L2 — replay of both input paths checks the soundness of a
///   reported route. L3 — all 36 ordered pairs in the finite cube have the
///   exact reversal verdict, and removing one pairwise tile removes the route
///   despite the remaining firings. These observers separate commutation alone
///   from a licensed braid.
/// - witness: `tests::asynchronous_axioms::the_cube_property_holds_for_every_pair_of_three_paths`
/// - witness: `tests::asynchronous_axioms::a_missing_pairwise_tile_removes_both_cube_routes`
#[spec(requires: matches!(store.get(forward.0.cell), Maybe::Present(_))
    && matches!(store.get(backward.0.cell), Maybe::Present(_)), ensures: |output| output == Presence::Absent || {
    let target = |path: ThreePath<'_>| [path.0, path.1, path.2].into_iter()
        .try_fold(peak.clone(), |current, step| {
            let Maybe::Present(cell) = store.get(step.cell) else { return None; };
            match rewrite_at(cell, &current, &step.at) {
                Maybe::Present(next) => Some(next),
                Maybe::Absent(_) => None,
            }
        });
    matches!((target(forward), target(backward)), (Some(left), Some(right)) if left == right)
})]
fn front_chain(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
    forward: ThreePath<'_>,
    backward: ThreePath<'_>,
) -> Presence
{
    let (u1, u2, u3) = forward;
    let (v1, v2, v3) = backward;
    let (Maybe::Present(after_u1), Maybe::Present(after_v1)) =
        (fire(store, peak, u1), fire(store, peak, v1))
    else {
        return Presence::Absent;
    };
    for u2_prime in edges_at(store, &after_u1) {
        let Maybe::Present(after_u2_prime) = fire(store, &after_u1, &u2_prime)
        else {
            continue;
        };
        for w3 in edges_at(store, &after_u2_prime) {
            if is_tile(store, &after_u1, (u2, u3), (&u2_prime, &w3)) != Presence::Present {
                continue;
            }
            for v2_prime in edges_at(store, &after_v1) {
                if is_tile(store, peak, (u1, &u2_prime), (v1, &v2_prime)) != Presence::Present {
                    continue;
                }
                if is_tile(store, &after_v1, (&v2_prime, &w3), (v2, v3)) == Presence::Present {
                    return Presence::Present;
                }
            }
        }
    }
    Presence::Absent
}

/// Search for the second chain of the cube property: edges `w₁, u₂'', v₂''`
/// with `u₁·u₂ ◇ w₁·u₂''`, `u₂''·u₃ ◇ v₂''·v₃`, `w₁·v₂'' ◇ v₁·v₂`.
///
/// # Specification
/// - ensures: Present exactly when the three stated back tiles have a witness
///   among the graph's edges; a present chain makes both input paths fire
///   completely to one term.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the common replay endpoint is independent of the tile
///   search. L3 — the cube’s complete reversal table and missing-face refusal
///   distinguish a reported but unlicensed route, a wrong target permutation
///   and agreement obtained by always refusing.
/// - witness: `tests::asynchronous_axioms::the_cube_property_holds_for_every_pair_of_three_paths`
/// - witness: `tests::asynchronous_axioms::a_missing_pairwise_tile_removes_both_cube_routes`
#[spec(ensures: |output| output == Presence::Absent || {
    let target = |path: ThreePath<'_>| [path.0, path.1, path.2].into_iter()
        .try_fold(peak.clone(), |current, step| {
            let Maybe::Present(cell) = store.get(step.cell) else { return None; };
            match rewrite_at(cell, &current, &step.at) {
                Maybe::Present(next) => Some(next),
                Maybe::Absent(_) => None,
            }
        });
    matches!((target(forward), target(backward)), (Some(left), Some(right)) if left == right)
})]
fn back_chain(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
    forward: ThreePath<'_>,
    backward: ThreePath<'_>,
) -> Presence
{
    let (u1, u2, u3) = forward;
    let (v1, v2, v3) = backward;
    for w1 in edges_at(store, peak) {
        let Maybe::Present(after_w1) = fire(store, peak, &w1)
        else {
            continue;
        };
        for u2_second in edges_at(store, &after_w1) {
            if is_tile(store, peak, (u1, u2), (&w1, &u2_second)) != Presence::Present {
                continue;
            }
            for v2_second in edges_at(store, &after_w1) {
                if is_tile(store, &after_w1, (&u2_second, u3), (&v2_second, v3))
                    != Presence::Present
                {
                    continue;
                }
                if is_tile(store, peak, (&w1, &v2_second), (v1, v2)) == Presence::Present {
                    return Presence::Present;
                }
            }
        }
    }
    Presence::Absent
}

/// Every path of length 3 out of `peak`.
///
/// # Specification
/// - ensures: every length-three firing path from `peak`, without duplicate
///   labelled paths; enumeration order is unspecified.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the finite three-redex cube. Every returned path is
///   replayed from the given peak and duplicates are rejected; the six-path
///   cardinality and exact reversal table establish completeness on this
///   fixture, distinguishing dropped, repeated or non-firing paths.
/// - witness: `tests::asynchronous_axioms::the_cube_property_holds_for_every_pair_of_three_paths`
#[spec(ensures: |output| output.iter().enumerate().all(|(index, path)| !output[..index].contains(path)
    && path.iter().try_fold(peak.clone(), |current, step| {
        let Maybe::Present(cell) = store.get(step.cell) else { return None; };
        match rewrite_at(cell, &current, &step.at) {
            Maybe::Present(next) => Some(next),
            Maybe::Absent(_) => None,
        }
    }).is_some()))]
fn three_paths(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
) -> Vec<[CellApp<ToyAlphabet>; 3]>
{
    let mut out = Vec::new();
    for first in edges_at(store, peak) {
        let Maybe::Present(after_first) = fire(store, peak, &first)
        else {
            continue;
        };
        for second in edges_at(store, &after_first) {
            let Maybe::Present(after_second) = fire(store, &after_first, &second)
            else {
                continue;
            };
            for third in edges_at(store, &after_second) {
                out.push([first.clone(), second.clone(), third]);
            }
        }
    }
    out
}

/// Every square the tile set generates out of `peak`, closed under symmetry.
///
/// # Specification
/// - ensures: exactly the licensed two-step squares, closed under exchange of
///   their paths; duplicate presentations and enumeration order are irrelevant.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — finite cube vertices. Two-step shape, tile validity,
///   symmetry and inclusion of every licensed edge pair check the represented
///   set independently of duplicate presentations. A concrete root tile
///   prevents vacuous determinism, and matching first paths must have matching
///   partners.
/// - witness: `tests::asynchronous_axioms::every_permutation_tile_is_deterministic`
#[spec(ensures: |output| {
    let edges = edges_at(store, peak);
    output.iter().all(|square| square.path.len() == 2 && square.other.len() == 2
        && square.path.first().zip(square.path.get(1))
            .zip(square.other.first().zip(square.other.get(1)))
            .is_some_and(|(path, other)| is_tile(store, peak, path, other) == Presence::Present)
        && output.iter().any(|reverse| reverse.path == square.other && reverse.other == square.path))
        && edges.iter().all(|first| edges.iter().all(|second|
            derive_shift_equivalence(store, peak, first, second).is_err()
                || output.iter().any(|square| square.path.iter().eq([first, second])
                    && square.other.iter().eq([second, first]))))
})]
fn squares_at(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
) -> Vec<Square>
{
    let mut out = Vec::new();
    let edges = edges_at(store, peak);
    for first in &edges {
        for second in &edges {
            let Ok(witness) = derive_shift_equivalence(store, peak, first, second)
            else {
                continue;
            };
            out.push(Square {
                path: witness.first_then_second(),
                other: witness.second_then_first(),
            });
            out.push(Square {
                path: witness.second_then_first(),
                other: witness.first_then_second(),
            });
        }
    }
    out
}

/// Every vertex the given applications reach from `peak`.
///
/// # Specification
/// - requires: the given identifiers belong to `store`, and their reachable
///   graph from `peak` is finite.
/// - ensures: distinct reachable vertices, including `peak`, closed under every
///   successful application in `steps`; order is unspecified.
/// - panics: an unstored identifier is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L1 — the finite cube graph and its stored applications. Root
///   inclusion, uniqueness and closure under the supplied rewrites reject a
///   missing successor or repeated state. The tile sweep checks its twelve
///   licensed ordered pairs; finiteness is a caller obligation, not inferred
///   from term size.
/// - witness: `tests::asynchronous_axioms::every_permutation_tile_is_symmetric`
#[spec(requires: steps.iter().all(|step| matches!(store.get(step.cell), Maybe::Present(_))),
    ensures: |output| output.contains(peak)
        && output.iter().enumerate().all(|(index, vertex)| !output[..index].contains(vertex)
            && steps.iter().all(|step| match fire(store, vertex, step) {
                Maybe::Present(next) => output.contains(&next),
                Maybe::Absent(_) => true,
            })))]
fn fixture_vertices(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
    steps: &[&CellApp<ToyAlphabet>],
) -> Vec<Toy>
{
    let mut out = vec![peak.clone()];
    let mut frontier = vec![peak.clone()];
    while let Some(vertex) = frontier.pop() {
        for step in steps {
            let Maybe::Present(next) = fire(store, &vertex, step)
            else {
                continue;
            };
            if out.contains(&next) {
                continue;
            }
            out.push(next.clone());
            frontier.push(next);
        }
    }
    out
}

#[test]
fn rewrite_branching_never_reaches_the_tile_set()
{
    // Two cells fire at one position and reach different terms, so the cells
    // branch as a rewrite system; the guard's first conjunct refuses such a
    // pair before any square exists, so determinism is never asked about it.
    let mut store = CellStore::new();
    let down = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
    let up = store.insert(toy_cell(
        Toy::succ(Toy::zero()),
        Toy::succ(Toy::succ(Toy::zero())),
    ));
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let left = CellApp {
        cell: down,
        at: at![0],
    };
    let right = CellApp {
        cell: up,
        at: at![0],
    };
    assert_ne!(
        fire(&store, &peak, &left),
        fire(&store, &peak, &right),
        "two cells at one position genuinely branch"
    );
    assert_eq!(
        Err(ShiftObstruction::ComparablePositions {
            order: PositionOrder::Same
        }),
        derive_shift_equivalence(&store, &peak, &left, &right),
        "and the branch is refused a tile"
    );
}

#[test]
fn an_application_survives_an_incomparable_neighbour_verbatim()
{
    // The locality both axiom arguments rest on: rewriting at one position
    // leaves the subterm at an incomparable position identical, so the
    // residual of an application is the application itself.
    let (store, first, second, third) = cube_fixture();
    let peak = cube_peak();
    let Maybe::Present(after) = fire(&store, &peak, &first)
    else {
        panic!("the first application fires");
    };
    for neighbour in [&second, &third] {
        assert_eq!(
            PositionOrder::Incomparable,
            ToyAlphabet::position_order(&first.at, &neighbour.at),
            "the fixture's positions are pairwise incomparable"
        );
        assert_eq!(
            ToyAlphabet::subterm_cmd_at(&peak, &neighbour.at),
            ToyAlphabet::subterm_cmd_at(&after, &neighbour.at),
            "and the neighbour's subterm is untouched by the rewrite"
        );
        assert!(
            matches!(fire(&store, &after, neighbour), Maybe::Present(_)),
            "so the neighbour still fires at its recorded position, unrelabelled"
        );
    }
}

#[test]
fn every_permutation_tile_is_symmetric()
{
    // Axiom 1, checked over the fixture family rather than taken on the
    // guard's construction.
    let (store, first, second, third) = cube_fixture();
    let mut tiles = 0_usize;
    for peak in fixture_vertices(&store, &cube_peak(), &[&first, &second, &third]) {
        for left in edges_at(&store, &peak) {
            for right in edges_at(&store, &peak) {
                let Ok(witness) = derive_shift_equivalence(&store, &peak, &left, &right)
                else {
                    continue;
                };
                let swapped = derive_shift_equivalence(&store, &peak, &right, &left)
                    .expect("the reverse ordered pair earns the witness too");
                assert_eq!(
                    witness.joins_at, swapped.joins_at,
                    "the swapped square joins where the original does"
                );
                assert_eq!(
                    witness.first_then_second(),
                    swapped.second_then_first(),
                    "and the two squares are the same square, transposed"
                );
                tiles = tiles.saturating_add(1_usize);
            }
        }
    }
    // Six ordered pairs at the peak and two at each of the three one-step
    // vertices: the cube's twelve edges, read as ordered pairs.
    assert_eq!(
        12_usize, tiles,
        "the fixture family's tile count, so the sweep is not vacuous"
    );
}

#[test]
fn every_permutation_tile_is_deterministic()
{
    // Axiom 2 as stated: no 2-path is the first component of two squares with
    // different second components.
    let (store, first, second, third) = cube_fixture();
    let initial = cube_peak();
    for peak in fixture_vertices(&store, &initial, &[&first, &second, &third]) {
        let squares = squares_at(&store, &peak);
        if peak == initial {
            assert!(
                squares
                    .iter()
                    .any(|square| square.path.iter().eq([&first, &second])
                        && square.other.iter().eq([&second, &first])),
                "the known root tile is present, independently of duplicate presentations"
            );
        }
        for square in &squares {
            for candidate in squares
                .iter()
                .filter(|candidate| candidate.path == square.path)
            {
                assert_eq!(
                    square.other, candidate.other,
                    "one 2-path is tiled with at most one other 2-path"
                );
            }
        }
    }
}

#[test]
fn the_cube_closes_on_three_pairwise_independent_applications()
{
    // All six interleavings reach one term, and all six faces of the cube are
    // earned witnesses that replay.
    let (store, first, second, third) = cube_fixture();
    let peak = cube_peak();
    let reached = run(&store, &peak, &[
        first.clone(),
        second.clone(),
        third.clone(),
    ]);
    for order in [
        [&first, &second, &third],
        [&first, &third, &second],
        [&second, &first, &third],
        [&second, &third, &first],
        [&third, &first, &second],
        [&third, &second, &first],
    ] {
        let schedule = order.map(Clone::clone);
        assert_eq!(
            reached,
            run(&store, &peak, &schedule),
            "every interleaving of three disjoint applications reaches one term"
        );
    }
    // The six faces: each unordered pair, at the peak and at the vertex the
    // remaining application reaches.
    let mut faces = 0_usize;
    for (left, right, other) in [
        (&first, &second, &third),
        (&first, &third, &second),
        (&second, &third, &first),
    ] {
        let Maybe::Present(beside) = fire(&store, &peak, other)
        else {
            panic!("the remaining application fires");
        };
        for vertex in [peak.clone(), beside] {
            let witness = derive_shift_equivalence(&store, &vertex, left, right)
                .expect("each face of the cube is an earned tile");
            assert!(
                bool::from(witness.replay(&store)),
                "and each face replays rather than being asserted"
            );
            faces = faces.saturating_add(1_usize);
        }
    }
    assert_eq!(6_usize, faces, "a cube has six faces and all six are tiles");
}

#[test]
fn the_cube_property_holds_for_every_pair_of_three_paths()
{
    // Axiom 3 as stated and by search: for every ordered pair of 3-paths out
    // of the peak, the first chain exists exactly when the second does, both
    // looked for among the graph's own edges.
    let (store, first, second, third) = cube_fixture();
    let peak = cube_peak();
    let paths = three_paths(&store, &peak);
    assert_eq!(
        6_usize,
        paths.len(),
        "three pairwise disjoint redexes and nothing else"
    );
    let mut present = 0_usize;
    for forward in &paths {
        for backward in &paths {
            let forward_ref = (&forward[0], &forward[1], &forward[2]);
            let backward_ref = (&backward[0], &backward[1], &backward[2]);
            let front = front_chain(&store, &peak, forward_ref, backward_ref);
            let back = back_chain(&store, &peak, forward_ref, backward_ref);
            let expected = if backward.iter().eq(forward.iter().rev()) {
                Presence::Present
            }
            else {
                Presence::Absent
            };
            assert_eq!(
                (expected, expected),
                (front, back),
                "both braid routes exist exactly for the reversed path"
            );
            if front == Presence::Present {
                present = present.saturating_add(1_usize);
            }
        }
    }
    assert_eq!(
        6_usize, present,
        "and the iff is not vacuous: each path's reversal is reached by both chains"
    );
    let forward = (&first, &second, &third);
    let backward = (&third, &second, &first);
    assert_eq!(
        Presence::Present,
        front_chain(&store, &peak, forward, backward),
        "the first chain reshuffles abc to cba"
    );
    assert_eq!(
        Presence::Present,
        back_chain(&store, &peak, forward, backward),
        "and so does the second, which is the braid relation"
    );
}

#[test]
fn a_missing_pairwise_tile_removes_both_cube_routes()
{
    // With one of the three pairwise tiles refused, the iff still holds, and
    // it holds by both sides vanishing rather than one surviving.
    let (store, first, second, third) = cube_over([cube_a(), cube_b(), cube_c_into_a()]);
    let peak = cube_peak();
    let refusal = derive_shift_equivalence(&store, &peak, &first, &third)
        .expect_err("c-into-a's right-hand side is a's left-hand side, so the pair overlaps");
    assert!(
        matches!(refusal, ShiftObstruction::GenuineOverlap { .. }),
        "and the overlap conjunct is what refuses it"
    );
    assert!(
        derive_shift_equivalence(&store, &peak, &first, &second).is_ok(),
        "the other two pairs are still tiles"
    );
    let Maybe::Present(after_first) = fire(&store, &peak, &first)
    else {
        panic!("the first application fires");
    };
    assert!(
        derive_shift_equivalence(&store, &after_first, &second, &third).is_ok(),
        "including the one at the vertex the first chain uses"
    );
    let forward = (&first, &second, &third);
    let backward = (&third, &second, &first);
    assert_eq!(
        Presence::Absent,
        front_chain(&store, &peak, forward, backward),
        "the first chain cannot be closed without the missing tile"
    );
    assert_eq!(
        Presence::Absent,
        back_chain(&store, &peak, forward, backward),
        "and neither can the second, so the iff holds by both sides vanishing"
    );
}
