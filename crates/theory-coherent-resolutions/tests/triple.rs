//! The critical triples of toy cell systems: three steps at one root, a chain
//! of one rule along a word, and two steps apart under one rule.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToySubst;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::CriticalTriple;
use gandr_theory_coherent_resolutions::critical_triples;

/// A store of `cells`, in order.
///
/// # Specification
/// trivial.
fn block(cells: impl IntoIterator<Item = Cell<ToyAlphabet>>) -> CellStore<ToyAlphabet>
{
    let mut store = CellStore::new();
    for cell in cells {
        let _id = store.insert(cell);
    }
    store
}

/// The step of `cell` at the position `path`, with the empty substitution: a
/// step compares by its cell and its position.
///
/// # Specification
/// trivial.
fn step(
    cell: CellId,
    path: &[PositionStep],
) -> CellApp<ToyAlphabet>
{
    CellApp {
        cell,
        at: ToyAlphabet::position_at_path(path),
        subst: ToySubst::default(),
    }
}

/// Asserts that `peak` is `expected` up to a renaming of their
/// metavariables: each matches the other.
///
/// # Specification
/// trivial.
fn assert_renames(
    peak: &Toy,
    expected: &Toy,
)
{
    assert!(
        bool::from(ToyAlphabet::match_cmd(
            peak,
            expected,
            &mut ToySubst::default(),
        )) && bool::from(ToyAlphabet::match_cmd(
            expected,
            peak,
            &mut ToySubst::default(),
        )),
        "the peak {peak:?} is {expected:?} up to a renaming"
    );
}

/// The one triple of `store`.
///
/// # Specification
/// trivial.
fn only(store: &CellStore<ToyAlphabet>) -> CriticalTriple<ToyAlphabet>
{
    let triples = critical_triples(store);
    let [ref triple] = *triples.as_slice()
    else {
        panic!("one triple, over every order of its steps: {triples:?}");
    };
    triple.clone()
}

#[test]
fn three_rules_at_one_root_make_one_triple_over_all_orders()
{
    let store = block([
        toy_cell(Toy::add(Toy::zero(), Toy::var("y")), Toy::var("y")),
        toy_cell(Toy::add(Toy::var("x"), Toy::zero()), Toy::var("x")),
        toy_cell(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()),
    ]);
    let [zero, one, two] = [0_usize, 1, 2].map(CellId::from);
    let triple = only(&store);
    assert_eq!(
        triple.steps,
        [step(zero, &[]), step(one, &[]), step(two, &[])],
        "each two of the three rules make a root pair, and the triple counts once"
    );
    assert_eq!(triple.peak, Toy::add(Toy::zero(), Toy::zero()));
}

#[test]
fn a_rule_that_overlaps_itself_twice_makes_one_chain()
{
    // `succ(succ(x))` overlaps itself one node down. Three copies along
    // `succ⁴(x)` are a chain: the outer two share no node, and the middle one
    // overlaps both, as `aa` does three times along the word `aaaa`.
    let store = block([toy_cell(Toy::succ(Toy::succ(Toy::var("x"))), Toy::var("x"))]);
    let zero = CellId::from(0_usize);
    let below = PositionStep::from(0_usize);
    let triple = only(&store);
    assert_eq!(triple.steps, [
        step(zero, &[]),
        step(zero, &[below]),
        step(zero, &[below, below])
    ]);
    assert_renames(
        &triple.peak,
        &Toy::succ(Toy::succ(Toy::succ(Toy::succ(Toy::var("z"))))),
    );
}

#[test]
fn two_steps_apart_under_one_rule_make_one_triple()
{
    // `succ(Zero)` fits each argument of the first rule's left side. The two
    // inner steps stand apart, and the outer step overlaps each of them.
    let store = block([
        toy_cell(
            Toy::add(Toy::succ(Toy::var("x")), Toy::succ(Toy::var("y"))),
            Toy::zero(),
        ),
        toy_cell(Toy::succ(Toy::zero()), Toy::zero()),
    ]);
    let [zero, one] = [0_usize, 1].map(CellId::from);
    let [left, right] = [0_usize, 1].map(PositionStep::from);
    let triple = only(&store);
    assert_eq!(triple.steps, [
        step(zero, &[]),
        step(one, &[left]),
        step(one, &[right])
    ]);
    assert_eq!(
        triple.peak,
        Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()))
    );
}
