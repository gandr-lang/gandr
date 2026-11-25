//! Completion's certified pairs read against a greedy Morse matching.
//!
//! A Morse matching pairs cells of a complex with their faces. The cells that
//! stay unpaired are the critical cells. The literature on polygraphic
//! resolutions reads the rules and the critical pairs of a convergent
//! presentation as the critical cells of such a collapse. These witnesses test
//! that reading on completion. They build the overlap complex of three corpus
//! rule blocks and match it greedily along the reduction order. Then they
//! compare its critical cells of dimension two with the pairs that completion
//! certifies.
//!
//! The overlap complex has one cell of dimension one for each rule. It has one
//! cell of dimension two for each confluence entry of the overlap enumerator.
//! The two faces of that cell are the two rules of the entry. A composition
//! entry is a path of two steps and not a branching. Thus the complex has no
//! cell for it. `NatUnits` and `NatApart` hold no critical triple. The three
//! triples of `NatAssoc` chain its pairs below the root, the pentagon of
//! associativity among them. The complex reads no entry below the root. Thus
//! it has no cell of dimension three.
//!
//! The critical cells and the certified pairs agree up to the order of each
//! pair. `NatUnits` and `NatApart` have the same left-hand sides. Thus their
//! overlap complexes are equal entry for entry, with an entry for each order
//! of a pair. A matching reads only the complex. It keeps the second entry of
//! each pair critical, since the first entry already connects the two rules.
//! Completion certifies each pair once, with its earlier rule first. On
//! `NatApart` one pair parts, and completion certifies it through the rule
//! that it derives. `NatAssoc` agrees only because completion reads none of
//! its critical pairs. All three of them overlap below the root.
//!
//! # References
//!
//! - `corpus/model/desc/rules-overlap-joinable.gandr` — the block `NatUnits`.
//! - `corpus/pathological/desc/rules-diverge.gandr` — the block `NatApart`.
//! - `corpus/ledger/features/nested-operation-laws.gandr` — the block
//!   `NatAssoc`.

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
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
use gandr_theory_coherent_resolutions::critical_triples;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_coherent_resolutions::interior_overlaps_between;
use quenchant_shape::shape::Maybe;

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

/// The recursion on the first argument: `add (Succ m) n ==> Succ (add m n)`.
///
/// # Specification
/// trivial.
fn successor() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::succ(Toy::var("m")), Toy::var("n")),
        Toy::succ(Toy::add(Toy::var("m"), Toy::var("n"))),
    )
}

/// `NatUnits`: addition with zero a unit on both sides.
///
/// # Specification
/// trivial.
fn nat_units() -> CellStore<ToyAlphabet>
{
    block([
        toy_cell(Toy::add(Toy::zero(), Toy::var("n")), Toy::var("n")),
        toy_cell(Toy::add(Toy::var("m"), Toy::zero()), Toy::var("m")),
        successor(),
    ])
}

/// `NatApart`: addition whose right unit law adds one.
///
/// The surface refuses this block, because its two unit laws part at two
/// values. Completion over the toy alphabet orients that pair instead.
///
/// # Specification
/// trivial.
fn nat_apart() -> CellStore<ToyAlphabet>
{
    block([
        toy_cell(Toy::add(Toy::zero(), Toy::var("n")), Toy::var("n")),
        toy_cell(
            Toy::add(Toy::var("m"), Toy::zero()),
            Toy::succ(Toy::var("m")),
        ),
        successor(),
    ])
}

/// `NatAssoc`: addition with its associativity law.
///
/// # Specification
/// trivial.
fn nat_assoc() -> CellStore<ToyAlphabet>
{
    block([
        toy_cell(Toy::add(Toy::zero(), Toy::var("n")), Toy::var("n")),
        successor(),
        toy_cell(
            Toy::add(Toy::add(Toy::var("m"), Toy::var("n")), Toy::var("k")),
            Toy::add(Toy::var("m"), Toy::add(Toy::var("n"), Toy::var("k"))),
        ),
    ])
}

/// A cell of dimension two: the confluence entry of one rule against another.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Branching
{
    /// The rule whose left-hand side the peak instantiates first.
    left: CellId,
    /// The rule renamed apart and unified with it at the root.
    right: CellId,
}

/// The overlap complex of a store, each cell with the term that orders it.
#[derive(Debug, Eq, PartialEq)]
struct Complex
{
    /// The cells of dimension one: each rule with its left-hand side, in store
    /// order.
    rules: Vec<(CellId, Toy)>,
    /// The cells of dimension two: each confluence entry with its peak, in
    /// enumeration order. The faces of an entry are its two rules.
    branchings: Vec<(Branching, Toy)>,
}

/// The overlap complex of `store`.
///
/// # Specification
/// trivial.
fn complex(store: &CellStore<ToyAlphabet>) -> Complex
{
    Complex {
        rules: store
            .iter()
            .map(|(id, cell)| (id, cell.lhs().clone()))
            .collect(),
        branchings: enumerate_overlaps(store)
            .into_iter()
            .filter(|overlap| overlap.kind == OverlapKind::Confluence)
            .map(|overlap| {
                let cell = Branching {
                    left: overlap.left,
                    right: overlap.right,
                };
                (cell, overlap.peak)
            })
            .collect(),
    }
}

/// `cells` ordered greatest first along the reduction order of their terms.
///
/// The reduction order is partial. The order here is a linear extension of it.
/// A cell stands after every cell whose term is strictly greater. Cells that
/// the reduction order leaves apart keep their order in `cells`.
///
/// # Specification
/// - ensures: the output is a permutation of `cells`, and no cell stands before
///   a cell whose term is strictly greater.
/// - panics: when the strict reduction order has a cycle on the terms of
///   `cells`, which a reduction order never has.
///
/// # Adequacy
/// - hypothesis: L3 — the peaks of `NatUnits` have two strictly greater entries
///   and two equal ones, so a reversed or ignored comparison changes which
///   entries the matching pairs and which it keeps critical.
/// - witness: `tests::collapse::the_matching_keeps_the_two_pairs_completion_certifies_on_nat_units`
#[spec(captures: count = cells.len(), ensures: |output| output.len() == count
    && output.iter().enumerate().all(|(index, &(_, ref term))| output.iter().skip(index).all(|&(_, ref later)|
        ToyAlphabet::reduction_cmp(later, term) != core::cmp::Ordering::Greater)))]
fn descending<T>(cells: Vec<(T, Toy)>) -> Vec<(T, Toy)>
{
    let count = cells.len();
    let mut above = vec![0_usize; count];
    for (index, &(_, ref term)) in cells.iter().enumerate() {
        for &(_, ref against) in &cells {
            if ToyAlphabet::reduction_cmp(against, term) == core::cmp::Ordering::Greater {
                above[index] = above[index].saturating_add(1);
            }
        }
    }
    let mut left: Vec<Option<(T, Toy)>> = cells.into_iter().map(Some).collect();
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let next = (0 .. count)
            .find(|&index| left[index].is_some() && above[index] == 0)
            .expect("the strict reduction order is acyclic");
        let (cell, term) = left[next].take().expect("the cell is not placed yet");
        for (index, held) in left.iter().enumerate() {
            if let Some(&(_, ref other)) = held.as_ref()
                && ToyAlphabet::reduction_cmp(&term, other) == core::cmp::Ordering::Greater
            {
                above[index] = above[index].saturating_sub(1);
            }
        }
        out.push((cell, term));
    }
    out
}

/// The cells a matching leaves unpaired, in each dimension, sorted.
#[derive(Debug, Eq, PartialEq)]
struct Critical
{
    /// The critical cells of dimension one.
    rules: Vec<CellId>,
    /// The critical cells of dimension two.
    branchings: Vec<Branching>,
}

/// The root of `cell`'s tree in the union-find `parents`, each path walked
/// halved on the way.
///
/// # Specification
/// - requires: every identifier in `parents` and `cell` indexes `parents`.
/// - ensures: the root is its own parent.
/// - panics: none under the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — the second entry of each pair of `NatUnits` finds both of
///   its faces under one root. A walk that stops short keeps them apart, and
///   the matching then pairs that entry.
/// - witness: `tests::collapse::the_matching_keeps_the_two_pairs_completion_certifies_on_nat_units`
#[spec(ensures: |output| parents[usize::from(output)] == output)]
fn root(
    parents: &mut [CellId],
    mut cell: CellId,
) -> CellId
{
    while parents[usize::from(cell)] != cell {
        let grandparent = parents[usize::from(parents[usize::from(cell)])];
        parents[usize::from(cell)] = grandparent;
        cell = grandparent;
    }
    cell
}

/// The cells that a greedy Morse matching of `complex` leaves critical, its
/// cells of dimension two visited greatest first along the reduction order of
/// their peaks.
///
/// # Specification
/// trivial.
fn critical(complex: &Complex) -> Critical
{
    matched(complex, &descending(complex.branchings.clone()))
}

/// The cells that the greedy matching of `complex` leaves critical when it
/// visits the cells of dimension two in the order of `ordered`.
///
/// The matching pairs each visited cell with its first unpaired face, greatest
/// first along the reduction order of the left-hand sides, if the pair keeps
/// the matching acyclic. A cell of dimension two has two faces. A new pair
/// closes a gradient cycle exactly when the two faces already lie in one tree
/// of paired cells, and a union-find answers that question.
///
/// # Specification
/// - requires: the rules of `complex` are the identifiers `0 .. n` in order,
///   `ordered` holds the branchings of `complex`, and every face of a branching
///   is a rule of `complex`.
/// - ensures: every critical cell is a cell of `complex`. Each pair removes one
///   cell from each dimension, so the critical cells keep the Euler
///   characteristic of `complex`.
/// - panics: none under the precondition.
/// - intension: the matching reads each incidence once.
///
/// # Adequacy
/// - hypothesis: L3 — on `NatUnits` each unordered pair has two entries, so the
///   second entry of each pair closes a cycle. A matching that ignores
///   acyclicity pairs it, and one that never pairs keeps all four.
/// - witness: `tests::collapse::the_matching_keeps_the_two_pairs_completion_certifies_on_nat_units`
/// - witness: `tests::collapse::nat_apart_certifies_the_pair_that_derives_its_rule_through_that_rule`
#[spec(ensures: |output| output.branchings.iter().all(|cell| complex.branchings.iter().any(|&(held, _)| held == *cell))
    && output.rules.iter().all(|cell| complex.rules.iter().any(|&(held, _)| held == *cell))
    && output.rules.len().saturating_add(complex.branchings.len()) == complex.rules.len().saturating_add(output.branchings.len()))]
fn matched(
    complex: &Complex,
    ordered: &[(Branching, Toy)],
) -> Critical
{
    let lhs = |cell: CellId| &complex.rules[usize::from(cell)].1;
    let mut parents: Vec<CellId> = complex.rules.iter().map(|&(id, _)| id).collect();
    let mut paired = vec![false; complex.rules.len()];
    let mut branchings = Vec::new();
    for &(cell, _) in ordered {
        let (left, right) = (
            root(&mut parents, cell.left),
            root(&mut parents, cell.right),
        );
        if left == right {
            branchings.push(cell);
            continue;
        }
        let faces = match ToyAlphabet::reduction_cmp(lhs(cell.left), lhs(cell.right)) {
            core::cmp::Ordering::Greater => [cell.left, cell.right],
            core::cmp::Ordering::Less => [cell.right, cell.left],
            core::cmp::Ordering::Equal => [cell.left.min(cell.right), cell.left.max(cell.right)],
        };
        match faces.into_iter().find(|&face| !paired[usize::from(face)]) {
            Some(face) => {
                paired[usize::from(face)] = true;
                parents[usize::from(left)] = right;
            },
            None => branchings.push(cell),
        }
    }
    branchings.sort_unstable();
    Critical {
        rules: complex
            .rules
            .iter()
            .map(|&(id, _)| id)
            .filter(|&id| !paired[usize::from(id)])
            .collect(),
        branchings,
    }
}

/// The store that completion leaves, and the entries it certifies, sorted.
///
/// # Specification
/// - requires: completion of `store` ends within an ample budget.
/// - ensures: one entry for each certificate, sorted.
/// - panics: when completion declines.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses pin the certified entries of each block
///   exactly. A lost, added or unsorted entry changes the pinned list.
/// - witness: `tests::collapse::the_matching_keeps_the_two_pairs_completion_certifies_on_nat_units`
/// - witness: `tests::collapse::nat_apart_certifies_the_pair_that_derives_its_rule_through_that_rule`
#[spec(ensures: |output| output.1.is_sorted())]
fn certified(store: CellStore<ToyAlphabet>) -> (CellStore<ToyAlphabet>, Vec<Branching>)
{
    let budget = CompletionBudget::new(
        CompletionStepBudget::from(64_usize),
        CompletionCellBudget::from(16_usize),
        NormalizationBudget::from(64_usize),
    );
    let CompletionOutcome::Completed {
        store,
        certificates,
        ..
    } = complete(store, budget)
    else {
        panic!("the block completes within an ample budget")
    };
    let mut pairs: Vec<Branching> = certificates
        .iter()
        .map(|certificate| Branching {
            left: certificate.overlap.left,
            right: certificate.overlap.right,
        })
        .collect();
    pairs.sort_unstable();
    (store, pairs)
}

/// A branching of the identifiers `left` and `right`.
///
/// # Specification
/// trivial.
fn branching(
    left: CellId,
    right: CellId,
) -> Branching
{
    Branching { left, right }
}

#[test]
fn the_matching_keeps_the_two_pairs_completion_certifies_on_nat_units()
{
    let [zero, one, two] = [0_usize, 1, 2].map(CellId::from);
    let (store, certified) = certified(nat_units());
    let complex = complex(&store);
    assert_eq!(
        complex.branchings.len(),
        4,
        "each of the two unordered pairs has an entry in each direction"
    );
    assert!(
        critical_triples(&store).is_empty(),
        "the unit laws do not overlap each other's successor case"
    );
    assert_eq!(
        certified,
        [branching(zero, one), branching(one, two)],
        "completion certifies each pair once, its earlier rule first"
    );
    let critical = critical(&complex);
    assert_eq!(
        critical,
        Critical {
            rules: vec![one],
            branchings: vec![branching(one, zero), branching(two, one)],
        },
        "the second entry of each pair closes a gradient cycle"
    );
    assert!(
        critical
            .branchings
            .iter()
            .map(|cell| branching(cell.right, cell.left))
            .eq(certified.iter().copied()),
        "the matching keeps one entry of each pair that completion certifies"
    );
}

#[test]
fn nat_apart_certifies_the_pair_that_derives_its_rule_through_that_rule()
{
    let [zero, one, two, three] = [0_usize, 1, 2, 3].map(CellId::from);
    assert_eq!(
        complex(&nat_units()),
        complex(&nat_apart()),
        "the same left-hand sides give the same entries and peaks"
    );
    let (store, certified) = certified(nat_apart());
    let Maybe::Present(derived) = store.get(three)
    else {
        panic!("completion derives a fourth cell")
    };
    assert_eq!(
        (derived.lhs(), derived.rhs()),
        (&Toy::succ(Toy::zero()), &Toy::zero()),
        "the unit laws part at `Succ Zero` and `Zero`, and completion orients that pair"
    );
    assert_eq!(
        certified,
        [branching(zero, one), branching(one, two)],
        "the pair that parts joins through the rule that it derives, so each pair keeps one certificate"
    );
    assert_eq!(
        critical(&complex(&store)),
        Critical {
            rules: vec![one, three],
            branchings: vec![branching(one, zero), branching(two, one)],
        },
        "the matching keeps the critical branchings of `NatUnits`"
    );
}

#[test]
fn nat_assoc_agrees_only_because_completion_reads_none_of_its_pairs()
{
    let [zero, one, two] = [0_usize, 1, 2].map(CellId::from);
    let (store, certified) = certified(nat_assoc());
    let complex = complex(&store);
    assert!(
        complex.branchings.is_empty() && certified.is_empty(),
        "no two left-hand sides unify at the root"
    );
    assert_eq!(
        critical(&complex),
        Critical {
            rules: vec![zero, one, two],
            branchings: Vec::new(),
        },
        "with no branching, every rule stays critical"
    );
    let below: Vec<Branching> = store
        .iter()
        .flat_map(|left| {
            store
                .iter()
                .flat_map(move |right| interior_overlaps_between(left, right))
        })
        .map(|overlap| branching(overlap.left, overlap.right))
        .collect();
    assert_eq!(
        below,
        [
            branching(two, zero),
            branching(two, one),
            branching(two, two)
        ],
        "associativity overlaps each rule below its root"
    );
}
