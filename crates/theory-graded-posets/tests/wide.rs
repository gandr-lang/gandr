//! A poset past one machine word: its order, closures, boundaries and ranks
//! against a naive closure over a full matrix, and its cycle refusal.

use gandr_theory_graded_posets::CellRow;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::Membership;

/// A cell, by its index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Cell(usize);

/// The state of a xorshift sequence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Seed(u64);

impl Seed
{
    /// The next state of the sequence.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Self
    {
        self.0 ^= self.0.wrapping_shl(13);
        self.0 ^= self.0.wrapping_shr(7);
        self.0 ^= self.0.wrapping_shl(17);
        *self
    }

    /// The next index below `count`.
    ///
    /// # Specification
    /// trivial.
    fn below(
        &mut self,
        count: ElementCount,
    ) -> Element
    {
        let word = usize::try_from(self.next().0).expect("a 64-bit target");
        Element::from(word.checked_rem(usize::from(count)).unwrap_or_default())
    }
}

/// A full matrix of pairs: entry `[lower][upper]` says whether `lower` lies
/// below `upper`.
type Matrix = Vec<Vec<Comparison>>;

/// Entry `[lower][upper]` of `matrix`.
///
/// # Specification
/// trivial.
fn at(
    matrix: &Matrix,
    lower: Element,
    upper: Element,
) -> Comparison
{
    matrix
        .get(usize::from(lower))
        .and_then(|row| row.get(usize::from(upper)))
        .copied()
        .unwrap_or(Comparison::NotBelow)
}

/// Random generating pairs on `count` cells, and the hidden chain they follow.
/// Each cell takes a place in a shuffled chain, and a pair is below only when
/// its lower cell's place comes first, about one pair in 32, so the closure
/// has no cycle and its pairs cross words.
///
/// # Specification
/// trivial.
fn random_order(
    count: ElementCount,
    mut seed: Seed,
) -> (Matrix, Vec<Element>)
{
    let cells = usize::from(count);
    let mut chain: Vec<Element> = (0 .. cells).map(Element::from).collect();
    for last in (1 .. cells).rev() {
        let other = usize::from(seed.below(ElementCount::from(last.saturating_add(1))));
        chain.swap(last, other);
    }
    let mut pairs = vec![vec![Comparison::NotBelow; cells]; cells];
    for (place, &lower) in chain.iter().enumerate() {
        for &upper in chain.iter().skip(place.saturating_add(1)) {
            if seed.next().0.trailing_zeros() >= 5 {
                let entry = pairs
                    .get_mut(usize::from(lower))
                    .and_then(|row| row.get_mut(usize::from(upper)))
                    .expect("a pair of cells");
                *entry = Comparison::Below;
            }
        }
    }
    (pairs, chain)
}

/// The reflexive and transitive closure of `pairs`: Warshall's, one entry at a
/// time.
///
/// # Specification
/// trivial.
fn naive_closure(mut pairs: Matrix) -> Matrix
{
    let count = pairs.len();
    for (cell, row) in pairs.iter_mut().enumerate() {
        if let Some(entry) = row.get_mut(cell) {
            *entry = Comparison::Below;
        }
    }
    for pivot in (0 .. count).map(Element::from) {
        for lower in (0 .. count).map(Element::from) {
            if at(&pairs, lower, pivot) != Comparison::Below {
                continue;
            }
            for upper in (0 .. count).map(Element::from) {
                if at(&pairs, pivot, upper) == Comparison::Below {
                    let entry = pairs
                        .get_mut(usize::from(lower))
                        .and_then(|row| row.get_mut(usize::from(upper)))
                        .expect("a pair of cells");
                    *entry = Comparison::Below;
                }
            }
        }
    }
    pairs
}

#[test]
fn a_wide_poset_answers_as_its_naive_closure()
{
    for (count, seed) in [
        (65_usize, 0x9e37_79b9_7f4a_7c15_u64),
        (130, 0x2545_f491_4f6c_dd1d),
    ] {
        let count = ElementCount::from(count);
        let cells = usize::from(count);
        let (pairs, chain) = random_order(count, Seed(seed));
        let poset = GradedPoset::new(
            (0 .. cells).map(Cell).collect(),
            |lower, upper| at(&pairs, Element::from(lower.0), Element::from(upper.0)),
            count,
        )
        .expect("a random order along a chain");
        assert_eq!(poset.count(), count);
        let reach = naive_closure(pairs);
        // The rank along the hidden chain, each cell after every cell below it.
        let mut ranks = vec![Rank::default(); cells];
        for &upper in &chain {
            let rank = (0 .. cells)
                .map(Element::from)
                .filter(|&lower| lower != upper && at(&reach, lower, upper) == Comparison::Below)
                .map(|lower| {
                    usize::from(ranks.get(usize::from(lower)).copied().unwrap_or_default())
                })
                .map(|lower| lower.saturating_add(1))
                .max()
                .unwrap_or_default();
            if let Some(slot) = ranks.get_mut(usize::from(upper)) {
                *slot = Rank::from(rank);
            }
        }
        for upper in (0 .. cells).map(Element::from) {
            let reached = &reach;
            let expected = move || {
                (0 .. cells)
                    .map(Element::from)
                    .filter(move |&lower| at(reached, lower, upper) == Comparison::Below)
            };
            let closure = poset.closure(upper).expect("a cell");
            assert!(
                closure.elements().eq(expected()),
                "{count:?}: the closure of {upper:?}"
            );
            assert_eq!(closure.count(), ElementCount::from(expected().count()));
            let boundary = poset.boundary(upper).expect("a cell");
            let strictly = move || expected().filter(move |&lower| lower != upper);
            assert!(
                boundary.elements().eq(strictly()),
                "{count:?}: the boundary of {upper:?}"
            );
            assert_eq!(boundary.count(), ElementCount::from(strictly().count()));
            assert_eq!(boundary.contains(upper), Membership::Outside);
            for lower in (0 .. cells).map(Element::from) {
                let below = at(&reach, lower, upper);
                assert_eq!(
                    poset.compare(lower, upper),
                    Ok(below),
                    "{count:?}: {lower:?} {upper:?}"
                );
                let inside = if below == Comparison::Below {
                    Membership::Inside
                }
                else {
                    Membership::Outside
                };
                assert_eq!(closure.contains(lower), inside);
            }
            assert_eq!(
                poset.rank(upper),
                Ok(ranks.get(usize::from(upper)).copied().unwrap_or_default())
            );
        }
        let outside = Element::from(cells);
        assert_eq!(
            poset.compare(outside, Element::from(0_usize)),
            Err(DualityError::ElementOutside(outside))
        );
        assert_eq!(
            poset.compare(Element::from(0_usize), outside),
            Err(DualityError::ElementOutside(outside))
        );
        assert_eq!(
            poset.closure(outside).map(CellRow::count),
            Err(DualityError::ElementOutside(outside))
        );
        assert_eq!(
            poset.subcomplexes(Budget::from(1_usize)),
            Err(DualityError::TooManyElements(count)),
            "finite Stone duality's sets hold at most 64 cells"
        );
    }
}

#[test]
fn a_wide_cycle_is_refused_by_its_least_pair()
{
    // A chain of 130 cells, each below the next, and the cell 100 below the
    // cell 70: the cells 70 to 100 lie each below the other, all past the
    // first word, and the least such pair is 70 and 71.
    let refused = GradedPoset::new(
        (0 .. 130).map(Cell).collect(),
        |lower, upper| {
            if lower.0.checked_add(1) == Some(upper.0) || (lower.0, upper.0) == (100, 70) {
                Comparison::Below
            }
            else {
                Comparison::NotBelow
            }
        },
        ElementCount::from(130_usize),
    );
    assert_eq!(
        refused.map(|poset| poset.count()),
        Err(DualityError::Cycle(
            Element::from(70_usize),
            Element::from(71_usize)
        ))
    );
}

#[test]
fn an_inclusion_order_is_the_order_its_pairs_give()
{
    // Random sets of points, the last a repeat of the first, against `new`
    // over strict inclusion: two cells that hold the same points are apart.
    for (cells, points, seed) in [
        (6_usize, 4_usize, 0x1234_5678_9abc_def1_u64),
        (65, 8, 0x0f0e_0d0c_0b0a_0908),
        (130, 70, 0x5668_5668_5668_5668),
    ] {
        let mut seed = Seed(seed);
        let mut sets: Vec<Vec<Membership>> = Vec::with_capacity(cells);
        for _ in 0 .. cells {
            let mut set = Vec::with_capacity(points);
            for _ in 0 .. points {
                set.push(if seed.next().0 & 1 == 0 {
                    Membership::Inside
                }
                else {
                    Membership::Outside
                });
            }
            sets.push(set);
        }
        let first = sets.first().cloned().expect("a cell");
        if let Some(last) = sets.last_mut() {
            *last = first;
        }
        let within = |lower: &[Membership], upper: &[Membership]| {
            lower
                .iter()
                .zip(upper)
                .all(|(&inner, &outer)| inner == Membership::Outside || outer == Membership::Inside)
        };
        let count = ElementCount::from(cells);
        let by_pairs = GradedPoset::new(
            sets.clone(),
            |lower, upper| {
                if lower != upper && within(lower, upper) {
                    Comparison::Below
                }
                else {
                    Comparison::NotBelow
                }
            },
            count,
        )
        .expect("strict inclusion is an order");
        let by_inclusion = GradedPoset::by_inclusion(
            sets,
            ElementCount::from(points),
            |set, point| {
                set.get(usize::from(point))
                    .copied()
                    .unwrap_or(Membership::Outside)
            },
            count,
        )
        .expect("inclusion is an order");
        for cell in (0 .. cells).map(Element::from) {
            let inclusion = by_inclusion.closure(cell).expect("a cell");
            let pairs = by_pairs.closure(cell).expect("a cell");
            assert!(
                inclusion.elements().eq(pairs.elements()),
                "{cells} cells: {cell:?}"
            );
            assert_eq!(by_inclusion.rank(cell), by_pairs.rank(cell));
        }
        let (first, last) = (
            Element::from(0_usize),
            Element::from(cells.saturating_sub(1)),
        );
        assert_eq!(by_inclusion.compare(first, last), Ok(Comparison::NotBelow));
        assert_eq!(by_inclusion.compare(last, first), Ok(Comparison::NotBelow));
    }
}
