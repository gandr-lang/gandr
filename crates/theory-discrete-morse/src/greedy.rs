//! The greedy acyclic matching on a finite complex, and a matching read as a
//! scheme.
//!
//! The greedy matching reads the cells in the caller's order, each cell after
//! its faces. It pairs each free cell with the first free cell above it at the
//! incidence one or minus one. It keeps a pair only if the gradient stays
//! acyclic. The gradient runs down from each cell to its faces and up along
//! each pair. Before a pair, the gradient is acyclic, so the pair closes a
//! cycle exactly when a path runs from the upper cell down to the lower one by
//! another edge.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::collapse::Class;
use crate::collapse::Scheme;
use crate::complex::Complex;
use crate::complex::Incidence;
use crate::complex::Invertibility;
use crate::complex::Standing;
use crate::gradient::Mark;
use crate::gradient::Place;

/// A matching on a finite list of cells: the class of each cell in the list.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Matching<Cell>
{
    /// The cells, in the caller's order.
    cells: Vec<Cell>,
    /// The class of each cell, in the same order.
    classes: Vec<Class<Cell>>,
    /// The place of each cell in the list.
    places: BTreeMap<Cell, Place>,
}

impl<Cell> Matching<Cell>
where
    Cell: Clone + Ord,
{
    /// The cells, in the caller's order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(&self) -> &[Cell]
    {
        &self.cells
    }

    /// The class of each cell, in the order of [`Matching::cells`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn classes(&self) -> &[Class<Cell>]
    {
        &self.classes
    }

    /// The class of `cell`: its class in the list, or critical for a cell
    /// that the list does not hold, since no pair holds it.
    ///
    /// # Specification
    /// - ensures: a listed cell's class is its entry in [`Matching::classes`],
    ///   and an unlisted cell is critical.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a listed vertex, a listed edge and a cell past the
    ///   list separate the three answers.
    /// - witness: `tests::greedy::a_cell_the_list_does_not_hold_is_critical`
    #[spec(ensures: |ref ret| self.places.contains_key(cell) || *ret == Class::Critical)]
    #[inline]
    #[must_use]
    pub fn class(
        &self,
        cell: &Cell,
    ) -> Class<Cell>
    {
        self.places
            .get(cell)
            .and_then(|place| self.classes.get(usize::from(*place)))
            .map_or(Class::Critical, Clone::clone)
    }

    /// The critical cells, in the order of [`Matching::cells`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn critical(&self) -> impl Iterator<Item = &Cell>
    {
        self.cells
            .iter()
            .zip(&self.classes)
            .filter(|&(_, class)| *class == Class::Critical)
            .map(|(cell, _)| cell)
    }

    /// The matching read as a scheme over `complex`, so that
    /// [`collapse()`](crate::collapse()) checks it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn on<'matching, C>(
        &'matching self,
        complex: &'matching mut C,
    ) -> Matched<'matching, C>
    where
        C: Complex<Cell = Cell>,
    {
        Matched {
            complex,
            matching: self,
        }
    }
}

/// A matching read as a scheme over its complex.
#[derive(Debug)]
pub struct Matched<'matching, C>
where
    C: Complex,
{
    /// The complex the matching pairs the cells of.
    complex: &'matching mut C,
    /// The matching.
    matching: &'matching Matching<C::Cell>,
}

impl<C> Complex for Matched<'_, C>
where
    C: Complex,
{
    type Cell = C::Cell;
    type Fault = C::Fault;

    /// Whether `cell` lies in the complex.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn standing(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Standing, Self::Fault>
    {
        self.complex.standing(cell)
    }

    /// Push each face of `cell` onto `faces`, with its incidence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn faces(
        &mut self,
        cell: &Self::Cell,
        faces: &mut Vec<(Self::Cell, Incidence)>,
    ) -> Result<(), Self::Fault>
    {
        self.complex.faces(cell, faces)
    }
}

impl<C> Scheme for Matched<'_, C>
where
    C: Complex,
{
    /// The class of `cell` under the matching.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn class(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Class<Self::Cell>, Self::Fault>
    {
        Ok(self.matching.class(cell))
    }
}

/// Where the greedy matching holds a cell.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Pairing
{
    /// No pair holds the cell yet.
    Free,
    /// The cell is a face of the cell at this place.
    Up(Place),
    /// The cell at this place is a face of the cell.
    Down(Place),
}

/// Whether a path runs from one cell to another.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// A path runs.
    Reaches,
    /// No path runs.
    Apart,
}

/// The faces of each cell inside a list, and the pairs that a greedy matching
/// keeps so far.
#[derive(Debug)]
struct Greedy
{
    /// The places of each cell's faces that the list holds.
    below: Vec<Vec<Place>>,
    /// The places of the cells that hold each cell as a face at the incidence
    /// one or minus one, in list order.
    above: Vec<Vec<Place>>,
    /// Where the matching holds each cell.
    pairing: Vec<Pairing>,
    /// Each cell's state in the current search.
    marks: Vec<Mark>,
    /// The search's path.
    stack: Vec<Place>,
}

impl Greedy
{
    /// Whether a gradient path runs from `upper` to `lower` by an edge other
    /// than the face edge from `upper` to `lower`.
    ///
    /// # Specification
    /// - requires: `upper` holds `lower` as a face, and the pairs so far keep
    ///   the gradient acyclic.
    /// - ensures: [`Reach::Reaches`] exactly when such a path runs, so a pair
    ///   of the two closes a cycle.
    /// - panics: none.
    /// - executable: none — the ensures is a statement about every path of the
    ///   gradient, and the call holds no second search to check it against.
    /// - intension: one depth-first search with an explicit stack, which reads
    ///   each cell and each edge at most once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the hollow triangle, three vertices and three edges,
    ///   pairs two edges and leaves the third critical, since its pair would
    ///   close a cycle.
    /// - witness: `tests::greedy::the_hollow_triangle_keeps_one_vertex_and_one_edge_critical`
    fn reaches(
        &mut self,
        upper: Place,
        lower: Place,
    ) -> Reach
    {
        self.marks.fill(Mark::Unseen);
        self.stack.clear();
        self.stack.push(upper);
        if let Some(mark) = self.marks.get_mut(usize::from(upper)) {
            *mark = Mark::Done;
        }
        while let Some(node) = self.stack.pop() {
            let pairing = self
                .pairing
                .get(usize::from(node))
                .copied()
                .unwrap_or(Pairing::Free);
            let up = match pairing {
                Pairing::Up(partner) => Some(partner),
                Pairing::Free | Pairing::Down(_) => None,
            };
            let faces = self
                .below
                .get(usize::from(node))
                .map_or(&[][..], Vec::as_slice);
            for next in up.into_iter().chain(faces.iter().copied()) {
                if pairing == Pairing::Down(next) || (node == upper && next == lower) {
                    continue;
                }
                if next == lower {
                    return Reach::Reaches;
                }
                if let Some(mark) = self.marks.get_mut(usize::from(next))
                    && *mark == Mark::Unseen
                {
                    *mark = Mark::Done;
                    self.stack.push(next);
                }
            }
        }
        Reach::Apart
    }
}

/// The greedy acyclic matching on the finite complex of `cells`.
///
/// # Specification
/// - requires: `cells` lists each cell once, each after its faces, and the
///   faces of a listed cell that matter lie in the list.
/// - ensures: each pair holds a listed cell and a listed face of it at the
///   incidence one or minus one, and the gradient of the pairs is acyclic. The
///   cells are read in the given order, and each pairs with the first free cell
///   above it that keeps the gradient acyclic.
/// - provides: the class of each listed cell.
/// - fails: with the complex's own fault, when it cannot read the faces of a
///   listed cell.
/// - panics: none.
/// - intension: the faces of each cell are read once. Each candidate pair takes
///   one search of the gradient, so the cost is O(n · c · (n + e)) for `n`
///   cells, `c` candidates above each, and `e` faces.
///
/// # Errors
/// - [`Complex::Fault`]: the complex cannot read the faces of a listed cell.
///
/// # Adequacy
/// - hypothesis: L2 — `collapse` checks each greedy matching of the suite and
///   finds no fault. L3 — a triangle leaves one vertex critical, and the hollow
///   triangle leaves one vertex and one edge critical. A face at the incidence
///   two pairs with nothing.
/// - witness: `tests::greedy::the_triangle_matches_onto_one_vertex`
/// - witness: `tests::greedy::the_hollow_triangle_keeps_one_vertex_and_one_edge_critical`
/// - witness: `tests::greedy::a_face_at_the_incidence_two_stays_unpaired`
/// - witness: `tests::euler::the_two_counts_agree_where_every_boundary_is_a_sphere`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |matching| matching.classes.len() == cells.len()))]
#[inline]
pub fn greedy<C>(
    complex: &mut C,
    cells: &[C::Cell],
) -> Result<Matching<C::Cell>, C::Fault>
where
    C: Complex,
{
    let count = cells.len();
    let mut places: BTreeMap<C::Cell, Place> = BTreeMap::new();
    for (at, cell) in cells.iter().enumerate() {
        let _first = places
            .entry(cell.clone())
            .or_insert_with(|| Place::from(at));
    }
    let mut greedy = Greedy {
        below: vec![Vec::new(); count],
        above: vec![Vec::new(); count],
        pairing: vec![Pairing::Free; count],
        marks: vec![Mark::Unseen; count],
        stack: Vec::with_capacity(count),
    };
    let mut faces: Vec<(C::Cell, Incidence)> = Vec::new();
    for (at, cell) in cells.iter().enumerate() {
        faces.clear();
        complex.faces(cell, &mut faces)?;
        for &(ref face, incidence) in &faces {
            let Some(&lower) = places.get(face)
            else {
                continue;
            };
            if let Some(row) = greedy.below.get_mut(at) {
                row.push(lower);
            }
            if incidence.invertibility() == Invertibility::Invertible
                && let Some(row) = greedy.above.get_mut(usize::from(lower))
            {
                row.push(Place::from(at));
            }
        }
    }
    for lower in (0 .. count).map(Place::from) {
        if greedy.pairing.get(usize::from(lower)) != Some(&Pairing::Free) {
            continue;
        }
        let candidates = greedy
            .above
            .get(usize::from(lower))
            .cloned()
            .unwrap_or_default();
        for upper in candidates {
            if greedy.pairing.get(usize::from(upper)) != Some(&Pairing::Free) {
                continue;
            }
            if greedy.reaches(upper, lower) == Reach::Reaches {
                continue;
            }
            if let Some(slot) = greedy.pairing.get_mut(usize::from(lower)) {
                *slot = Pairing::Up(upper);
            }
            if let Some(slot) = greedy.pairing.get_mut(usize::from(upper)) {
                *slot = Pairing::Down(lower);
            }
            break;
        }
    }
    let classes = greedy
        .pairing
        .iter()
        .map(|&pairing| match pairing {
            Pairing::Free => Class::Critical,
            Pairing::Up(partner) => cells
                .get(usize::from(partner))
                .map_or(Class::Critical, |cell| Class::Redundant(cell.clone())),
            Pairing::Down(partner) => cells
                .get(usize::from(partner))
                .map_or(Class::Critical, |cell| Class::Collapsible(cell.clone())),
        })
        .collect();
    Ok(Matching {
        cells: cells.to_vec(),
        classes,
        places,
    })
}
