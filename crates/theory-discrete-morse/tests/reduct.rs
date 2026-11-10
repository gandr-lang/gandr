//! The reduct of a complex along its greedy matching: the homology that it
//! keeps, the order of its critical cells, the walk of its gradient and its
//! refusals.
//!
//! The homology over the rationals of a chain complex is, in each rank, the
//! number of cells less the ranks of the boundaries out of it and into it.
//! The suite computes both sides by exact elimination over the integers, so a
//! wrong sign on a gradient path changes a rank.

use alloc::collections::BTreeMap;
use core::convert::Infallible;
use core::fmt::Debug;

use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Count;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::MorseError;
use gandr_theory_discrete_morse::Place;
use gandr_theory_discrete_morse::Reduct;
use gandr_theory_discrete_morse::Standing;
use gandr_theory_discrete_morse::collapse;
use gandr_theory_discrete_morse::greedy;
use gandr_theory_discrete_morse::reduct;
use gandr_theory_graded_posets::Rank;

use crate::simplices::A;
use crate::simplices::AB;
use crate::simplices::AC;
use crate::simplices::B;
use crate::simplices::BC;
use crate::simplices::C;
use crate::simplices::D;
use crate::simplices::FILLED;
use crate::simplices::Facets;
use crate::simplices::Forged;
use crate::simplices::HOLLOW;
use crate::simplices::Refused;
use crate::simplices::Triangle;

/// A chain complex over the integers: the rank of each cell, and each entry
/// of its boundary.
#[derive(Debug, Default)]
struct Chains
{
    /// The rank of each cell, by its place.
    ranks: Vec<Rank>,
    /// Each entry of the boundary: the cell, the face and the incidence.
    entries: Vec<(Place, Place, Incidence)>,
}

impl Chains
{
    /// The chains of the complex of `cells`, each face by its place in the
    /// list.
    ///
    /// # Specification
    /// trivial.
    fn of<C>(
        complex: &mut C,
        cells: &[C::Cell],
    ) -> Self
    where
        C: Complex,
        C::Fault: Debug,
    {
        let mut chains = Self::default();
        let places: BTreeMap<&C::Cell, usize> = cells
            .iter()
            .enumerate()
            .map(|(at, cell)| (cell, at))
            .collect();
        let mut faces = Vec::new();
        for (at, cell) in cells.iter().enumerate() {
            faces.clear();
            complex.faces(cell, &mut faces).expect("the complex reads");
            let mut rank = Rank::default();
            for &(ref face, incidence) in &faces {
                let below = places.get(face).copied().expect("each face is listed");
                let lower = chains.ranks.get(below).copied().expect("a face before it");
                rank = Rank::from(usize::from(lower).saturating_add(1));
                chains
                    .entries
                    .push((Place::from(at), Place::from(below), incidence));
            }
            chains.ranks.push(rank);
        }
        chains
    }

    /// The chains of `reduct`: its critical cells and their Morse
    /// boundaries.
    ///
    /// # Specification
    /// trivial.
    fn reduced<Cell>(reduct: &Reduct<Cell>) -> Self
    {
        let mut chains = Self::default();
        for at in (0 .. reduct.cells().len()).map(Place::from) {
            chains
                .ranks
                .push(reduct.rank(at).expect("a rank for each cell"));
            for &(face, incidence) in reduct.boundary(at) {
                chains.entries.push((at, face, incidence));
            }
        }
        chains
    }

    /// The highest rank of a cell.
    ///
    /// # Specification
    /// trivial.
    fn top(&self) -> Rank
    {
        self.ranks.iter().copied().max().unwrap_or_default()
    }

    /// The rational Betti numbers, from rank zero through `top`.
    ///
    /// # Specification
    /// trivial.
    fn betti(
        &self,
        top: Rank,
    ) -> Vec<Count>
    {
        (0 ..= usize::from(top))
            .map(|rank| {
                let cells = self
                    .ranks
                    .iter()
                    .filter(|&&held| usize::from(held) == rank)
                    .count();
                let out = usize::from(self.boundary_rank(Rank::from(rank)));
                let into = usize::from(self.boundary_rank(Rank::from(rank.saturating_add(1))));
                Count::from(
                    cells
                        .checked_sub(out)
                        .and_then(|rest| rest.checked_sub(into))
                        .expect("the ranks fit the cells"),
                )
            })
            .collect()
    }

    /// The rank over the rationals of the boundary from the cells of `rank`
    /// to the cells one rank down.
    ///
    /// # Specification
    /// trivial.
    fn boundary_rank(
        &self,
        rank: Rank,
    ) -> Count
    {
        let Some(lower) = usize::from(rank).checked_sub(1)
        else {
            return Count::default();
        };
        let mut rows = vec![None; self.ranks.len()];
        let mut columns = vec![None; self.ranks.len()];
        let (mut row_count, mut column_count) = (0_usize, 0_usize);
        for ((&held, row), column) in self.ranks.iter().zip(&mut rows).zip(&mut columns) {
            if usize::from(held) == lower {
                *row = Some(row_count);
                row_count = row_count.saturating_add(1);
            }
            else if held == rank {
                *column = Some(column_count);
                column_count = column_count.saturating_add(1);
            }
        }
        let mut matrix = vec![vec![0_i128; column_count]; row_count];
        for &(cell, face, incidence) in &self.entries {
            let row = rows.get(usize::from(face)).copied().flatten();
            let column = columns.get(usize::from(cell)).copied().flatten();
            if let (Some(row), Some(column)) = (row, column) {
                let entry = matrix
                    .get_mut(row)
                    .and_then(|values| values.get_mut(column))
                    .expect("an entry inside the matrix");
                *entry = entry
                    .checked_add(i128::from(i64::from(incidence)))
                    .expect("a small entry");
            }
        }
        let mut found = 0_usize;
        for column in 0 .. column_count {
            let Some(offset) = matrix
                .iter()
                .skip(found)
                .position(|values| values.get(column).is_some_and(|&value| value != 0))
            else {
                continue;
            };
            matrix.swap(found, found.checked_add(offset).expect("a row"));
            let (head, tail) = matrix.split_at_mut(found.checked_add(1).expect("a row"));
            let pivot = head.last().expect("the pivot row");
            let lead = pivot.get(column).copied().expect("the pivot");
            for values in tail.iter_mut() {
                let factor = values.get(column).copied().unwrap_or_default();
                if factor == 0 {
                    continue;
                }
                for (value, &from) in values.iter_mut().zip(pivot.iter()) {
                    *value = value
                        .checked_mul(lead)
                        .zip(from.checked_mul(factor))
                        .and_then(|(scaled, taken)| scaled.checked_sub(taken))
                        .expect("a small entry");
                }
                let mut divisor = 0_i128;
                for &value in values.iter() {
                    let mut larger = divisor;
                    let mut smaller = value.checked_abs().expect("a small entry");
                    while smaller != 0 {
                        let rest = larger.checked_rem(smaller).expect("a divisor");
                        larger = smaller;
                        smaller = rest;
                    }
                    divisor = larger;
                }
                if divisor > 1 {
                    for value in values.iter_mut() {
                        *value = value.checked_div(divisor).expect("a divisor");
                    }
                }
            }
            found = found.checked_add(1).expect("a rank");
        }
        Count::from(found)
    }
}

/// The homology of the complex of `cells`, after the check that the reduct
/// along its greedy matching has the same homology from its critical cells
/// alone.
///
/// # Specification
/// trivial.
fn kept<C>(
    complex: &mut C,
    cells: &[C::Cell],
) -> Vec<Count>
where
    C: Complex,
    C::Fault: Debug,
{
    let budget = Budget::from(cells.len());
    let matching = greedy(complex, cells).expect("the complex reads");
    let checked = collapse(&mut matching.on(complex), cells, budget).expect("the complex reads");
    assert_eq!(checked.faults(), Faults::default());
    let reduced = reduct(&mut matching.on(complex), cells, budget).expect("the reduct");
    assert_eq!(reduced.cells().len(), matching.critical().count());
    let whole = Chains::of(complex, cells);
    let top = whole.top();
    let homology = whole.betti(top);
    assert_eq!(Chains::reduced(&reduced).betti(top), homology);
    homology
}

#[test]
fn each_complex_has_the_homology_of_its_reduct()
{
    let (zero, one, two) = (Count::from(0), Count::from(1), Count::from(2));
    for weight in [1_i64, 2_i64] {
        let mut hollow = Triangle { weight };
        assert_eq!(kept(&mut hollow, &HOLLOW), Vec::from([one, one]));
        let mut filled = Triangle { weight };
        assert_eq!(kept(&mut filled, &FILLED), Vec::from([one, zero, zero]));
    }
    let mut sphere = Facets::sphere();
    let cells = sphere.cells();
    assert_eq!(kept(&mut sphere, &cells), Vec::from([one, zero, one]));
    let mut plane = Facets::projective_plane();
    let cells = plane.cells();
    assert_eq!(kept(&mut plane, &cells), Vec::from([one, zero, zero]));
    let mut torus = Facets::torus();
    let cells = torus.cells();
    assert_eq!(kept(&mut torus, &cells), Vec::from([one, two, one]));
}

#[test]
fn the_critical_cells_run_by_rank_and_then_by_place()
{
    // The hollow triangle and a vertex `d` listed after its edges: `c`, the
    // edge `ac` and `d` stay critical in list order, and the reduct puts the
    // two vertices first.
    let mut complex = Facets(Vec::from([AB, AC, BC, D]));
    let cells = [A, B, C, AB, AC, BC, D];
    let matching = greedy(&mut complex, &cells).expect("the complex reads");
    assert_eq!(matching.critical().copied().collect::<Vec<_>>(), [C, AC, D]);
    let reduced = reduct(
        &mut matching.on(&mut complex),
        &cells,
        Budget::from(cells.len()),
    )
    .expect("the reduct");
    assert_eq!(reduced.cells(), [C, D, AC]);
    assert_eq!(
        (0 .. 3)
            .map(|at| reduced.rank(Place::from(at)))
            .collect::<Vec<_>>(),
        [
            Some(Rank::from(0_usize)),
            Some(Rank::from(0_usize)),
            Some(Rank::from(1_usize))
        ]
    );
    assert!(reduced.boundary(Place::from(2)).is_empty());
}

#[test]
fn the_walk_of_the_critical_edge_runs_around_the_circle()
{
    let mut complex = Triangle::default();
    let matching = greedy(&mut complex, &HOLLOW).expect("the triangle reads");
    let reduced = reduct(
        &mut matching.on(&mut complex),
        &HOLLOW,
        Budget::from(HOLLOW.len()),
    )
    .expect("the reduct");
    assert_eq!(reduced.cells(), [C, AC]);
    // The edge `ac` runs down to `a`, up to `ab`, down to `b`, up to `bc` and
    // down to `c`. That path cancels the face `c` of `ac`, so the boundary is
    // empty: the circle keeps one class in each rank.
    assert_eq!(reduced.walk(Place::from(1)), [
        Place::from(0),
        Place::from(1)
    ]);
    assert!(reduced.boundary(Place::from(1)).is_empty());
    assert!(reduced.walk(Place::from(0)).is_empty());
    assert!(reduced.walk(Place::from(2)).is_empty());
    assert!(reduced.boundary(Place::from(2)).is_empty());
    assert_eq!(reduced.rank(Place::from(1)), Some(Rank::from(1_usize)));
    assert_eq!(reduced.rank(Place::from(2)), None);
}

#[test]
fn a_walk_past_its_budget_is_refused()
{
    // The walk from the edge `ac` reaches the two redundant vertices.
    let mut complex = Triangle::default();
    let matching = greedy(&mut complex, &HOLLOW).expect("the triangle reads");
    assert_eq!(
        reduct(&mut matching.on(&mut complex), &HOLLOW, Budget::from(1)).map(|_| ()),
        Err(MorseError::PastBudget(Budget::from(1)))
    );
    assert_eq!(
        reduct(&mut matching.on(&mut complex), &HOLLOW, Budget::from(2)).map(|_| ()),
        Ok(())
    );
}

/// A cell of the ridge.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Ridge
{
    /// The vertex that the first edge pairs with.
    Low,
    /// The vertex that stays critical.
    High,
    /// The edge that pairs with the low vertex.
    First,
    /// The edge that stays critical.
    Second,
}

/// Two vertices and two edges between them. Each edge holds one vertex at
/// the incidence one and the other at the largest integer.
#[derive(Debug)]
struct Ridges;

impl Complex for Ridges
{
    type Cell = Ridge;
    type Fault = Infallible;

    /// Every cell lies in the complex.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        _: &Ridge,
    ) -> Result<Standing, Infallible>
    {
        Ok(Standing::Inside)
    }

    /// The two vertices of each edge, and no face of a vertex.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &Ridge,
        faces: &mut Vec<(Ridge, Incidence)>,
    ) -> Result<(), Infallible>
    {
        let (one, most) = (Incidence::from(1_i64), Incidence::from(i64::MAX));
        match *cell {
            Ridge::First => faces.extend([(Ridge::Low, one), (Ridge::High, most)]),
            Ridge::Second => faces.extend([(Ridge::Low, most), (Ridge::High, one)]),
            Ridge::Low | Ridge::High => {},
        }
        Ok(())
    }
}

#[test]
fn a_sum_past_the_integers_is_refused()
{
    // The second edge carries the largest integer through the low vertex and
    // up the first edge, onto the high vertex at the largest integer again.
    let mut complex = Ridges;
    let cells = [Ridge::Low, Ridge::High, Ridge::First, Ridge::Second];
    let matching = greedy(&mut complex, &cells).expect("the ridge reads");
    assert_eq!(matching.critical().copied().collect::<Vec<_>>(), [
        Ridge::High,
        Ridge::Second
    ]);
    assert_eq!(
        reduct(
            &mut matching.on(&mut complex),
            &cells,
            Budget::from(cells.len())
        )
        .map(|_| ()),
        Err(MorseError::Overflow)
    );
}

#[test]
fn a_fault_of_the_scheme_is_given_back_as_its_own()
{
    let mut scheme = Forged {
        refuses: [C].to_vec(),
        ..Forged::default()
    };
    assert_eq!(
        reduct(&mut scheme, &FILLED, Budget::from(FILLED.len())).map(|_| ()),
        Err(MorseError::Complex(Refused(C)))
    );
}
