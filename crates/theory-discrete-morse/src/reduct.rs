//! The reduct of a complex along an acyclic matching: the complex of its
//! critical cells, with the boundary that the gradient paths give.
//!
//! A gradient path from a critical cell runs down to one of its faces. From a
//! redundant face it runs up to the face's partner, and then down to another
//! face of the partner. It ends at a critical face. A collapsible face has no
//! partner above it, so a path that reaches one ends there and adds nothing.
//! The Morse boundary of a critical cell sums the weight of each path that
//! ends at a critical face. The weight of a path is the product of the
//! incidences along it. A step up along a pair multiplies by the negative of
//! the inverse of the pair's incidence, and a unit is its own inverse.
//!
//! The walk from a critical cell reads each redundant cell that its paths
//! reach once. It puts each of them after every cell whose paths reach it,
//! which the acyclic gradient allows. Then it sums the weight that reaches
//! each cell once, in that order, and carries it on to the faces of the
//! cell's partner. So no path is followed twice.
//!
//! # References
//!
//! - `Curry-2015-discrete_morse_theory_computing_cellular_sheaf_cohomology` —
//!   exemplar: Definition 2.4 and Theorem 2.6 reduce a complex along a matching
//!   whose pairs are invertible, and the reduct keeps the cohomology. Justin
//!   Curry, Robert Ghrist and Vidit Nanda, "Discrete Morse Theory for Computing
//!   Cellular Sheaf Cohomology", _Foundations of Computational Mathematics_ 16,
//!   2016, `arXiv:1312.6454`.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_graded_posets::Rank;

use crate::collapse::Budget;
use crate::collapse::Class;
use crate::collapse::Count;
use crate::collapse::Scheme;
use crate::complex::Incidence;
use crate::error::MorseError;
use crate::gradient::Mark;
use crate::gradient::Place;

/// The reduct of a complex along an acyclic matching: its critical cells in
/// the canonical order, the Morse boundary of each, and the walk of the
/// gradient from each.
///
/// # Specification
/// - ensures: one rank, one boundary and one walk for each critical cell. The
///   cells run by rank, and by their place in the given list within a rank.
///   Each face of a boundary is the place of a critical cell one rank down, at
///   most once and in place order, with an incidence that is not zero.
/// - provides: the critical cells, their ranks, their boundaries and their
///   walks.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`reduct`]'s,
///   which makes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reduct<Cell>
{
    /// The critical cells, by rank and then by place in the given list.
    cells: Vec<Cell>,
    /// The rank of each critical cell, in the same order.
    ranks: Vec<Rank>,
    /// Where the boundary of each critical cell starts in `faces`, and one
    /// bound past the last.
    bounds: Vec<Count>,
    /// The Morse boundary of each critical cell in turn: each face by its
    /// place in `cells`, with its incidence.
    faces: Vec<(Place, Incidence)>,
    /// Where the walk from each critical cell starts in `walks`, and one bound
    /// past the last.
    reaches: Vec<Count>,
    /// The redundant cells that each walk sums in turn, by their place in the
    /// given list.
    walks: Vec<Place>,
}

impl<Cell> Reduct<Cell>
{
    /// The critical cells, by rank and then by place in the given list.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(&self) -> &[Cell]
    {
        &self.cells
    }

    /// The rank of the critical cell at `at`, or nothing past the cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rank(
        &self,
        at: Place,
    ) -> Option<Rank>
    {
        self.ranks.get(usize::from(at)).copied()
    }

    /// The Morse boundary of the critical cell at `at`: each critical face by
    /// its place in [`Reduct::cells`], with its incidence. It is empty past
    /// the cells.
    ///
    /// # Specification
    /// - ensures: empty past the cells.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the homology of each test complex reads from the
    ///   boundaries of its reduct, so a lost face or a wrong sign changes a
    ///   rank.
    /// - witness: `tests::reduct::each_complex_has_the_homology_of_its_reduct`
    #[spec(ensures: |ret| ret.is_empty() || usize::from(at) < self.cells.len())]
    #[inline]
    #[must_use]
    pub fn boundary(
        &self,
        at: Place,
    ) -> &[(Place, Incidence)]
    {
        span(&self.bounds, &self.faces, at)
    }

    /// The walk from the critical cell at `at`: each redundant cell that its
    /// paths reach, by its place in the given list, each after every cell
    /// whose paths reach it. It is empty past the cells.
    ///
    /// # Specification
    /// - ensures: empty past the cells.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the hollow triangle's critical edge walks its two
    ///   redundant vertices, the vertex nearer the edge first.
    /// - witness: `tests::reduct::the_walk_of_the_critical_edge_runs_around_the_circle`
    #[spec(ensures: |ret| ret.is_empty() || usize::from(at) < self.cells.len())]
    #[inline]
    #[must_use]
    pub fn walk(
        &self,
        at: Place,
    ) -> &[Place]
    {
        span(&self.reaches, &self.walks, at)
    }
}

/// The entries of the item at `at` in a list split by `bounds`: empty past
/// the bounds.
///
/// # Specification
/// trivial.
fn span<'list, Entry>(
    bounds: &[Count],
    entries: &'list [Entry],
    at: Place,
) -> &'list [Entry]
{
    let start = bounds.get(usize::from(at)).copied().map(usize::from);
    let end = usize::from(at)
        .checked_add(1)
        .and_then(|next| bounds.get(next))
        .copied()
        .map(usize::from);
    start
        .zip(end)
        .and_then(|(start, end)| entries.get(start .. end))
        .unwrap_or(&[])
}

/// The faces and the partners of the listed cells, as each walk reads them.
#[derive(Debug)]
struct Gradient
{
    /// Each listed cell's partner one rank up, where the cell is redundant.
    ups: Vec<Option<Place>>,
    /// Where each listed cell's faces start in `below`, and one bound past
    /// the last.
    starts: Vec<Count>,
    /// Each listed cell's faces in the list, by place, with their incidence.
    below: Vec<(Place, Incidence)>,
}

impl Gradient
{
    /// The faces of the listed cell at `cell`, with their incidence.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &self,
        cell: Place,
    ) -> &[(Place, Incidence)]
    {
        span(&self.starts, &self.below, cell)
    }

    /// The partner of the listed cell at `cell`, where it is redundant.
    ///
    /// # Specification
    /// trivial.
    fn up(
        &self,
        cell: Place,
    ) -> Option<Place>
    {
        self.ups.get(usize::from(cell)).copied().flatten()
    }
}

/// What one walk holds, kept from walk to walk so that no walk allocates
/// once the buffers have grown.
#[derive(Debug)]
struct Walk
{
    /// The weight that reaches each listed cell.
    weights: Vec<Incidence>,
    /// Each listed cell's state in the walk's ordering.
    marks: Vec<Mark>,
    /// The cells whose weight or mark the walk changes.
    touched: Vec<Place>,
    /// The ordering's path, each cell with the next face of its partner.
    stack: Vec<(Place, Count)>,
    /// The redundant cells in the order the ordering leaves them, each after
    /// every cell that its paths reach.
    order: Vec<Place>,
    /// The redundant cells that the walk reaches.
    visited: Count,
}

impl Walk
{
    /// Adds `weight` to the weight that reaches `cell`.
    ///
    /// # Specification
    /// - ensures: the cell's weight grows by `weight`, and the cell is recorded
    ///   as touched.
    /// - fails: a sum past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MorseError::Overflow`]: the sum passes the 64-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path that carries the largest integer onto a face
    ///   of a large incidence passes the integers.
    /// - witness: `tests::reduct::a_sum_past_the_integers_is_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(MorseError::Overflow)))]
    fn add<Fault>(
        &mut self,
        cell: Place,
        weight: Incidence,
    ) -> Result<(), MorseError<Fault>>
    {
        let slot = self
            .weights
            .get_mut(usize::from(cell))
            .ok_or(MorseError::Overflow)?;
        *slot = slot.plus(weight).ok_or(MorseError::Overflow)?;
        self.touched.push(cell);
        Ok(())
    }

    /// Opens `cell` on the ordering's path, as one more redundant cell the
    /// walk reaches.
    ///
    /// # Specification
    /// - ensures: the cell is open and on the path, and the walk counts it.
    /// - fails: a walk that would reach more than `budget` redundant cells is
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MorseError::PastBudget`]: the walk reaches more than `budget`
    ///   redundant cells.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a budget one short of the longest walk refuses it,
    ///   and the exact budget does not.
    /// - witness: `tests::reduct::a_walk_past_its_budget_is_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(MorseError::PastBudget(past)) if past == budget))]
    fn open<Fault>(
        &mut self,
        cell: Place,
        budget: Budget,
    ) -> Result<(), MorseError<Fault>>
    {
        if usize::from(self.visited) >= usize::from(budget) {
            return Err(MorseError::PastBudget(budget));
        }
        self.visited = self.visited.one_more();
        if let Some(mark) = self.marks.get_mut(usize::from(cell)) {
            *mark = Mark::Open;
        }
        self.touched.push(cell);
        self.stack.push((cell, Count::default()));
        Ok(())
    }

    /// Orders the redundant cells that the paths from the redundant cell
    /// `start` reach, each after every cell that its own paths reach.
    ///
    /// # Specification
    /// - requires: `start` is redundant and the walk has not reached it; the
    ///   gradient is acyclic.
    /// - ensures: each redundant cell reached is in the order once, after each
    ///   redundant cell that a path from it reaches.
    /// - fails: a walk past `budget` redundant cells is refused.
    /// - panics: none.
    /// - executable: none — the ensures is a statement about every path of the
    ///   gradient, and the call holds no second search to check it against.
    /// - intension: one depth-first search with an explicit stack, which reads
    ///   each partner's faces once.
    ///
    /// # Errors
    /// - [`MorseError::PastBudget`]: the walk reaches more than `budget`
    ///   redundant cells.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the homology of each test complex is the homology of
    ///   its reduct, so a weight summed before every path reaches it changes a
    ///   rank.
    /// - witness: `tests::reduct::each_complex_has_the_homology_of_its_reduct`
    fn order<Fault>(
        &mut self,
        gradient: &Gradient,
        start: Place,
        budget: Budget,
    ) -> Result<(), MorseError<Fault>>
    {
        self.open(start, budget)?;
        while let Some(top) = self.stack.last_mut() {
            let (node, next) = *top;
            top.1 = next.one_more();
            let face = gradient
                .up(node)
                .and_then(|partner| gradient.faces(partner).get(usize::from(next)))
                .map(|&(face, _)| face);
            let Some(face) = face
            else {
                if let Some(mark) = self.marks.get_mut(usize::from(node)) {
                    *mark = Mark::Done;
                }
                self.order.push(node);
                let _left = self.stack.pop();
                continue;
            };
            if face == node || gradient.up(face).is_none() {
                continue;
            }
            if self.marks.get(usize::from(face)) == Some(&Mark::Unseen) {
                self.open(face, budget)?;
            }
        }
        Ok(())
    }
}

/// The reduct of the complex of `cells` along the matching that `scheme`
/// gives: its critical cells, the Morse boundary of each, and the walk of the
/// gradient from each.
///
/// # Specification
/// - requires: `scheme` is an acyclic matching on `cells`, as
///   [`collapse`](crate::collapse) finds with no fault and as
///   [`greedy`](crate::greedy) makes one. `cells` lists each cell of the
///   complex once, each after its faces, and each partner lies in the list.
/// - ensures: the cells of the reduct are the critical cells among `cells`, by
///   rank and then by place. The rank of a cell is one more than the rank of
///   its first face in the list, and zero for a cell with no face there. The
///   boundary of a critical cell sums the weight of each gradient path from it
///   to a critical face, and it lists each face whose sum is not zero. Each
///   walk lists each redundant cell it reaches once, after each cell whose
///   paths reach it.
/// - fails: the scheme's own fault comes back as [`MorseError::Complex`]. A
///   walk that reaches more than `budget` redundant cells is refused with
///   [`MorseError::PastBudget`], never cut short. A sum past the 64-bit
///   integers is refused with [`MorseError::Overflow`].
/// - panics: none.
/// - intension: the class and the faces of each listed cell are read once. Each
///   walk reads the faces of each partner it reaches twice: once to order the
///   redundant cells, and once to sum. It holds one weight for each cell it
///   reaches and allocates nothing for a path.
///
/// # Errors
/// - [`MorseError::Complex`]: the scheme refuses a cell.
/// - [`MorseError::PastBudget`]: a walk reaches more than `budget` redundant
///   cells.
/// - [`MorseError::Overflow`]: a sum passes the 64-bit integers.
///
/// # Adequacy
/// - hypothesis: L2 — the reduct of each test complex along its greedy matching
///   has the complex's homology over the rationals: the hollow and the filled
///   triangle at the weights one and two, the sphere, the projective plane and
///   the torus. L3 — a vertex listed after the edges separates the canonical
///   order from the list order; a budget one short of the longest walk refuses
///   it, and the exact budget does not; a sum past the integers is refused; a
///   failing scheme gives its fault back.
/// - witness: `tests::reduct::each_complex_has_the_homology_of_its_reduct`
/// - witness: `tests::reduct::the_critical_cells_run_by_rank_and_then_by_place`
/// - witness: `tests::reduct::a_walk_past_its_budget_is_refused`
/// - witness: `tests::reduct::a_sum_past_the_integers_is_refused`
/// - witness: `tests::reduct::a_fault_of_the_scheme_is_given_back_as_its_own`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reduct| reduct.ranks.len() == reduct.cells.len()
    && reduct.bounds.len() == reduct.cells.len().saturating_add(1)
    && reduct.reaches.len() == reduct.bounds.len()))]
#[inline]
pub fn reduct<S>(
    scheme: &mut S,
    cells: &[S::Cell],
    budget: Budget,
) -> Result<Reduct<S::Cell>, MorseError<S::Fault>>
where
    S: Scheme,
{
    let count = cells.len();
    let mut places: BTreeMap<S::Cell, Place> = BTreeMap::new();
    for (at, cell) in cells.iter().enumerate() {
        let _first = places
            .entry(cell.clone())
            .or_insert_with(|| Place::from(at));
    }
    let mut gradient = Gradient {
        ups: Vec::with_capacity(count),
        starts: Vec::with_capacity(count.saturating_add(1)),
        below: Vec::new(),
    };
    gradient.starts.push(Count::default());
    let mut ranks: Vec<Rank> = Vec::with_capacity(count);
    let mut critical: Vec<Place> = Vec::new();
    let mut read: Vec<(S::Cell, Incidence)> = Vec::new();
    for (at, cell) in cells.iter().enumerate() {
        let up = match scheme.class(cell)? {
            Class::Critical => {
                critical.push(Place::from(at));
                None
            },
            Class::Redundant(partner) => places.get(&partner).copied(),
            Class::Collapsible(_) => None,
        };
        gradient.ups.push(up);
        read.clear();
        scheme.faces(cell, &mut read)?;
        let mut rank = None;
        for &(ref face, incidence) in &read {
            let Some(&place) = places.get(face)
            else {
                continue;
            };
            if rank.is_none() {
                rank = Some(
                    ranks
                        .get(usize::from(place))
                        .map_or_else(Rank::default, |&below| {
                            Rank::from(usize::from(below).saturating_add(1))
                        }),
                );
            }
            gradient.below.push((place, incidence));
        }
        ranks.push(rank.unwrap_or_default());
        gradient.starts.push(Count::from(gradient.below.len()));
    }
    critical.sort_by_key(|&place| ranks.get(usize::from(place)).copied().unwrap_or_default());
    let mut slots: Vec<Option<Place>> = vec![None; count];
    for (slot, &place) in critical.iter().enumerate() {
        if let Some(held) = slots.get_mut(usize::from(place)) {
            *held = Some(Place::from(slot));
        }
    }
    let mut walk = Walk {
        weights: vec![Incidence::default(); count],
        marks: vec![Mark::Unseen; count],
        touched: Vec::new(),
        stack: Vec::new(),
        order: Vec::new(),
        visited: Count::default(),
    };
    let mut reduct = Reduct {
        cells: Vec::with_capacity(critical.len()),
        ranks: Vec::with_capacity(critical.len()),
        bounds: Vec::with_capacity(critical.len().saturating_add(1)),
        faces: Vec::new(),
        reaches: Vec::with_capacity(critical.len().saturating_add(1)),
        walks: Vec::new(),
    };
    reduct.bounds.push(Count::default());
    reduct.reaches.push(Count::default());
    let mut boundary: Vec<(Place, Incidence)> = Vec::new();
    for &cell in &critical {
        walk.visited = Count::default();
        for &(face, incidence) in gradient.faces(cell) {
            walk.add(face, incidence)?;
            if gradient.up(face).is_some()
                && walk.marks.get(usize::from(face)) == Some(&Mark::Unseen)
            {
                walk.order(&gradient, face, budget)?;
            }
        }
        for index in (0 .. walk.order.len()).rev() {
            let Some(&lower) = walk.order.get(index)
            else {
                continue;
            };
            let weight = walk
                .weights
                .get(usize::from(lower))
                .copied()
                .unwrap_or_default();
            let Some(partner) = gradient.up(lower)
            else {
                continue;
            };
            if weight == Incidence::default() {
                continue;
            }
            let faces = gradient.faces(partner);
            let pair = faces
                .iter()
                .find(|&&(face, _)| face == lower)
                .map_or_else(Incidence::default, |&(_, incidence)| incidence);
            let carried = weight
                .times(pair)
                .and_then(Incidence::negated)
                .ok_or(MorseError::Overflow)?;
            for &(face, incidence) in faces {
                if face == lower {
                    continue;
                }
                walk.add(face, carried.times(incidence).ok_or(MorseError::Overflow)?)?;
            }
        }
        boundary.clear();
        for &touched in &walk.touched {
            let Some(&Some(slot)) = slots.get(usize::from(touched))
            else {
                continue;
            };
            if let Some(weight) = walk.weights.get_mut(usize::from(touched))
                && *weight != Incidence::default()
            {
                boundary.push((slot, *weight));
                *weight = Incidence::default();
            }
        }
        boundary.sort_unstable_by_key(|&(slot, _)| slot);
        for &touched in &walk.touched {
            if let Some(weight) = walk.weights.get_mut(usize::from(touched)) {
                *weight = Incidence::default();
            }
            if let Some(mark) = walk.marks.get_mut(usize::from(touched)) {
                *mark = Mark::Unseen;
            }
        }
        walk.touched.clear();
        reduct.faces.extend_from_slice(&boundary);
        reduct.bounds.push(Count::from(reduct.faces.len()));
        reduct.walks.extend(walk.order.iter().rev());
        reduct.reaches.push(Count::from(reduct.walks.len()));
        walk.order.clear();
        if let Some(listed) = cells.get(usize::from(cell)) {
            reduct.cells.push(listed.clone());
        }
        reduct
            .ranks
            .push(ranks.get(usize::from(cell)).copied().unwrap_or_default());
    }
    Ok(reduct)
}
