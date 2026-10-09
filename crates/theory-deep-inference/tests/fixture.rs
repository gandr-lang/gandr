//! The toy-alphabet cells, stores and drivers the suites share.
//!
//! The toy alphabet nests commands, so a toy term carries two applications at
//! incomparable positions, which no sequent term can. Every fixture here is a
//! first-order rule over `Zero`, `Succ` and `Add`.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_coherent_resolutions::firing;
use gandr_theory_coherent_resolutions::rewrite_at;
use quenchant_shape::shape::Maybe;

/// (f): `Succ(Zero) ~> Zero`, a ground rule that overlaps nothing, not even
/// itself, so any two of its applications at incomparable positions earn the
/// shift witness.
///
/// # Specification
/// trivial.
pub fn f_cell() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::succ(Toy::zero()), Toy::zero())
}

/// (g): `Succ(Succ(Zero)) ~> Zero`.
///
/// Both faces are ground and neither right-hand side offers a seam `f`'s
/// left-hand side unifies with, which is what makes the pair's overlap family
/// empty.
///
/// # Specification
/// trivial.
pub fn g_cell() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::succ(Toy::succ(Toy::zero())), Toy::zero())
}

/// (add-Z): `Add(Zero, x) ~> x`.
///
/// # Specification
/// trivial.
pub fn add_z() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::add(Toy::zero(), Toy::var("x")), Toy::var("x"))
}

/// (add-S): `Add(Succ(m), n) ~> Succ(Add(m, n))`.
///
/// # Specification
/// trivial.
pub fn add_s() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::succ(Toy::var("m")), Toy::var("n")),
        Toy::succ(Toy::add(Toy::var("m"), Toy::var("n"))),
    )
}

/// (c): `Add(Zero, Zero) ~> Zero`, a ground rule overlapping nothing, so
/// dependence between two of its applications is position containment alone.
///
/// # Specification
/// trivial.
pub fn c_cell() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::add(Toy::zero(), Toy::zero()), Toy::zero())
}

/// (nop): `Zero ~> Zero`, a reflexive cell: the unit step the normal form
/// eliminates.
///
/// # Specification
/// trivial.
pub fn nop_cell() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::zero(), Toy::zero())
}

/// The `cong2` store and its two rule identifiers, `f` then `g`.
///
/// # Specification
/// trivial.
pub fn cong2_store() -> (CellStore<ToyAlphabet>, CellId, CellId)
{
    let mut store = CellStore::new();
    let f = store.insert(f_cell());
    let g = store.insert(g_cell());
    (store, f, g)
}

/// The `cong2` body: two redex nodes whiskered into one `Add` frame,
/// `Add(Succ(Zero), Succ(Succ(Zero)))`, with the two redexes at the frame's
/// two argument positions.
///
/// # Specification
/// trivial.
pub fn cong2_body() -> Toy
{
    Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero())))
}

/// The two applications the `cong2` body whiskers: `f` at the left argument,
/// `g` at the right.
///
/// # Specification
/// trivial.
pub fn cong2_pair(
    f: CellId,
    g: CellId,
) -> (CellApp<ToyAlphabet>, CellApp<ToyAlphabet>)
{
    (
        CellApp {
            cell: f,
            at: at![0],
        },
        CellApp {
            cell: g,
            at: at![1],
        },
    )
}

/// The cell `id` names in `store`.
///
/// # Specification
/// - panics: when `store` holds no such cell, which is a fixture defect.
pub fn stored<A>(
    store: &CellStore<A>,
    id: CellId,
) -> &Cell<A>
where
    A: CellAlphabet,
{
    let Maybe::Present(cell) = store.get(id)
    else {
        panic!("the fixture names a stored cell");
    };
    cell
}

/// Fire one recorded step, or report why it does not fire.
///
/// # Specification
/// - ensures: the term after `step`'s cell fires at its recorded position.
/// - provides: the engine's reason when the cell does not fire there.
/// - panics: when `step` names a cell `store` does not hold, which is a fixture
///   defect.
pub fn fire<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    step: &CellApp<A>,
) -> Maybe<A::Cmd, firing::Absent>
where
    A: CellAlphabet,
{
    rewrite_at(stored(store, step.cell), term, &step.at)
}

/// Run a recorded path from `start`, or fail the test.
///
/// Generic over the alphabet so the adversarial suites run the same recorded
/// paths over a lying alphabet as over the toy one.
///
/// # Specification
/// - ensures: the term every step of `path` reaches, fired in order.
/// - panics: when a step names an unstored cell or does not fire at its
///   recorded position, which is a fixture defect.
pub fn run<A>(
    store: &CellStore<A>,
    start: &A::Cmd,
    path: &[CellApp<A>],
) -> A::Cmd
where
    A: CellAlphabet,
{
    let mut current = start.clone();
    for step in path {
        let Maybe::Present(next) = fire(store, &current, step)
        else {
            panic!("the step fires at its recorded position");
        };
        current = next;
    }
    current
}

/// The toy composition overlap `derive_fused` is exercised on, with its store
/// holding (add-Z) then (add-S).
///
/// (add-S)'s right-hand side subterm `Add(m, n)` unifies with (add-Z)'s
/// left-hand side, so the pair composes at a seam.
///
/// # Specification
/// - panics: when the composition is not enumerated, which is a fixture defect.
pub fn fusion_fixture() -> (CellStore<ToyAlphabet>, Overlap<ToyAlphabet>)
{
    let mut store = CellStore::new();
    let z = store.insert(add_z());
    let s = store.insert(add_s());
    let composition = enumerate_overlaps(&store)
        .into_iter()
        .find(|overlap| {
            overlap.kind == OverlapKind::Composition && overlap.left == s && overlap.right == z
        })
        .expect("the composition overlap exists");
    (store, composition)
}

/// A tracelet over a chosen boundary and a chosen pair of paths.
///
/// An [`Overlap`] carries a private renamed leg, so only the enumerator builds
/// one; a certificate over a boundary that is not a critical pair borrows the
/// fusion fixture's overlap as a carrier and overrides its peak. Replay reads
/// the carrier's peak and nothing else of it.
///
/// # Specification
/// trivial.
pub fn tracelet_over(
    peak: &Toy,
    joins_at: &Toy,
    path_a: Vec<CellApp<ToyAlphabet>>,
    path_b: Vec<CellApp<ToyAlphabet>>,
) -> Tracelet<ToyAlphabet>
{
    let (_store, mut overlap) = fusion_fixture();
    overlap.peak = peak.clone();
    Tracelet {
        overlap,
        path_a,
        path_b,
        joins_at: joins_at.clone(),
    }
}
