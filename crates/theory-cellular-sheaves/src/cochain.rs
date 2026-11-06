//! The cochains of a sheaf over the rationals, its coboundaries and its
//! cohomology.
//!
//! The cochains of degree `d` are the sections on the cells of rank `d`: one
//! rational for each entry of each such cell's stalk, the cells in cell order.
//! The coboundary from degree `d` sends a cochain to the cells of rank
//! `d + 1`. At each such cell it adds the restriction of the cochain at each
//! face of rank `d`, with the sign that the face's incidence gives. The
//! coboundary from degree `d + 1` after it is zero exactly when the
//! incidences are those of a complex, and the crate checks this. The
//! cohomology of degree `d` is the kernel of the coboundary from `d` less the
//! image of the coboundary into `d`, and the crate gives its dimension.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Element;

use crate::error::SheafError;
use crate::index::Dimension;
use crate::index::Entry;
use crate::index::Incidence;
use crate::index::Slot;
use crate::matrix::Matrix;
use crate::matrix::Rational;
use crate::sheaf::Sheaf;

/// The cochain complex of a sheaf with an orientation: the dimension of the
/// cochains of each degree and the coboundary from each degree to the next.
///
/// # Specification
/// - ensures: one slot for each cell of the complex, each cell of the sheaf or
///   each critical cell of a reduction; one dimension for each degree from zero
///   to the highest rank; one coboundary for each degree below the highest,
///   with the next degree's dimension as its rows and its own as its columns;
///   each two coboundaries in turn compose to zero.
/// - provides: the coboundaries and the cohomology.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   `CochainComplex::assembled`'s, which makes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CochainComplex
{
    /// Where each cell's entries start in the cochains of its rank, in cell
    /// order.
    slots: Vec<Slot>,
    /// The dimension of the cochains of each degree.
    dimensions: Vec<Dimension>,
    /// The coboundary from each degree to the next.
    coboundaries: Vec<Matrix>,
}

impl<Cell> Sheaf<Cell>
{
    /// The cochain complex of this sheaf over the rationals, each face's sign
    /// the incidence that `orientation` gives it.
    ///
    /// # Specification
    /// - ensures: the coboundary from degree `d` holds, at the row of each
    ///   entry of a cell of rank `d + 1` and the column of the entry its map
    ///   reads from each face of rank `d`, the sign of that face's incidence,
    ///   and zero elsewhere; each two coboundaries in turn compose to zero.
    /// - fails: incidences whose coboundaries do not compose to zero are
    ///   refused by the lower degree.
    /// - panics: none.
    /// - intension: `orientation` is called once for each pair of a cell and a
    ///   face one rank below it, the cells in cell order and each cell's faces
    ///   in cell order.
    ///
    /// # Errors
    /// - [`SheafError::NotAComplex`]: the coboundaries from a degree and the
    ///   next compose to a map that is not zero.
    /// - [`SheafError::Overflow`]: a product passes the integers.
    /// - [`SheafError::CellOutside`], [`SheafError::EntryOutside`]: unreachable
    ///   for a sheaf `Sheaf::new` makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every level of both towers, whose cohomology reads
    ///   from the coboundaries; L3 — a square with every incidence positive is
    ///   refused, and with the incidences of its boundary it is admitted.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    /// - witness: `tests::cochains::a_square_oriented_as_a_complex_is_contractible`
    /// - witness: `tests::cochains::a_square_with_every_incidence_positive_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |complex| complex.slots.len() == self.poset().cells().len()
        && complex.coboundaries.len() == complex.dimensions.len().saturating_sub(1)))]
    #[inline]
    pub fn cochains<Orient>(
        &self,
        mut orientation: Orient,
    ) -> Result<CochainComplex, SheafError>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
    {
        let cells = self.poset().cells();
        let mut ranks = Vec::with_capacity(cells.len());
        for cell in (0 .. cells.len()).map(Element::from) {
            let rank = self.poset().rank(cell).map_err(SheafError::Poset)?;
            ranks.push(rank);
        }
        let degrees = ranks
            .iter()
            .map(|&rank| usize::from(rank).saturating_add(1))
            .max()
            .unwrap_or(0);
        let mut dimensions = vec![Dimension::default(); degrees];
        let mut slots = Vec::with_capacity(cells.len());
        for (cell, &rank) in ranks.iter().enumerate() {
            let cell = Element::from(cell);
            let width = self.width(cell)?;
            let dimension = dimensions
                .get_mut(usize::from(rank))
                .ok_or(SheafError::CellOutside(cell))?;
            slots.push(Slot::from(usize::from(*dimension)));
            *dimension =
                Dimension::from(usize::from(*dimension).saturating_add(usize::from(width)));
        }
        let mut coboundaries = Vec::with_capacity(degrees.saturating_sub(1));
        for pair in dimensions.windows(2) {
            if let [columns, rows] = *pair {
                coboundaries.push(Matrix::zero(rows, columns)?);
            }
        }
        for (cell, (upper_cell, &rank)) in cells.iter().zip(&ranks).enumerate() {
            let cell = Element::from(cell);
            let Some(degree) = usize::from(rank).checked_sub(1)
            else {
                continue;
            };
            let boundary = self.poset().boundary(cell).map_err(SheafError::Poset)?;
            let width = self.width(cell)?;
            let row_start = slots
                .get(usize::from(cell))
                .copied()
                .ok_or(SheafError::CellOutside(cell))?;
            for face in boundary.elements() {
                if ranks
                    .get(usize::from(face))
                    .map(|&face_rank| usize::from(face_rank))
                    != Some(degree)
                {
                    continue;
                }
                let face_cell = cells
                    .get(usize::from(face))
                    .ok_or(SheafError::CellOutside(face))?;
                let sign = Rational::of_incidence(orientation(face_cell, upper_cell));
                let column_start = slots
                    .get(usize::from(face))
                    .copied()
                    .ok_or(SheafError::CellOutside(face))?;
                let coboundary = coboundaries
                    .get_mut(degree)
                    .ok_or(SheafError::CellOutside(cell))?;
                for entry in (0 .. usize::from(width)).map(Entry::from) {
                    let read = self.read(face, cell, entry)?;
                    let row = usize::from(row_start).saturating_add(usize::from(entry));
                    let column = usize::from(column_start).saturating_add(usize::from(read));
                    coboundary.add(Slot::from(row), Slot::from(column), sign)?;
                }
            }
        }
        CochainComplex::assembled(slots, dimensions, coboundaries)
    }
}

impl CochainComplex
{
    /// The cochain complex of `slots`, `dimensions` and `coboundaries`, once
    /// each two coboundaries in turn compose to zero.
    ///
    /// # Specification
    /// - requires: one coboundary for each degree below the highest, with the
    ///   next degree's dimension as its rows and its own as its columns.
    /// - ensures: the complex holds the three lists as given.
    /// - fails: two coboundaries in turn whose composite is not zero are
    ///   refused by the lower degree.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::NotAComplex`]: the coboundaries from a degree and the
    ///   next compose to a map that is not zero.
    /// - [`SheafError::Overflow`]: a product passes the integers.
    /// - [`SheafError::ShapeMismatch`]: two coboundaries do not chain,
    ///   unreachable for the shapes the crate builds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a square with every incidence positive is refused,
    ///   and with the incidences of its boundary it is admitted; L2 — the
    ///   reduct of every level of both towers is admitted.
    /// - witness: `tests::cochains::a_square_with_every_incidence_positive_is_refused`
    /// - witness: `tests::cochains::a_square_oriented_as_a_complex_is_contractible`
    /// - witness: `tests::towers::every_level_of_both_towers_keeps_its_cohomology_on_its_reduct`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::NotAComplex(_) | SheafError::Overflow | SheafError::ShapeMismatch)))]
    pub(crate) fn assembled(
        slots: Vec<Slot>,
        dimensions: Vec<Dimension>,
        coboundaries: Vec<Matrix>,
    ) -> Result<Self, SheafError>
    {
        for (degree, pair) in coboundaries.windows(2).enumerate() {
            if let [ref lower, ref upper] = *pair {
                let composite = upper.product(lower)?;
                if composite != Matrix::zero(composite.rows(), composite.columns())? {
                    return Err(SheafError::NotAComplex(Rank::from(degree)));
                }
            }
        }
        Ok(Self {
            slots,
            dimensions,
            coboundaries,
        })
    }

    /// The coboundary from degree `degree` to the next.
    ///
    /// # Specification
    /// - provides: the matrix with the next degree's cochains as its rows and
    ///   this degree's as its columns.
    /// - fails: a degree at or past the highest rank is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::DegreeOutside`]: no cell has rank `degree + 1`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's level of four points has a coboundary of
    ///   four rows and four columns, and none from degree one.
    /// - witness: `tests::towers::the_circles_level_of_four_points_has_the_rationals_in_degrees_zero_and_one`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(SheafError::DegreeOutside(degree)))]
    #[inline]
    pub fn coboundary(
        &self,
        degree: Rank,
    ) -> Result<&Matrix, SheafError>
    {
        self.coboundaries
            .get(usize::from(degree))
            .ok_or(SheafError::DegreeOutside(degree))
    }

    /// The dimension of the cochains of degree `degree`: zero past the
    /// highest rank.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn dimension(
        &self,
        degree: Rank,
    ) -> Dimension
    {
        self.dimensions
            .get(usize::from(degree))
            .copied()
            .unwrap_or_default()
    }

    /// The number of degrees: one more than the highest rank, or zero with no
    /// cell.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn degrees(&self) -> Rank
    {
        Rank::from(self.dimensions.len())
    }

    /// Where a cell's entries start in the cochains of its rank.
    ///
    /// # Specification
    /// - provides: the slot `Sheaf::cochains` gave `cell`.
    /// - fails: a cell past the poset is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: `cell` lies past the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pull-back of both towers is written at the
    ///   slots of its two levels.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(SheafError::CellOutside(cell)))]
    pub(crate) fn slot(
        &self,
        cell: Element,
    ) -> Result<Slot, SheafError>
    {
        self.slots
            .get(usize::from(cell))
            .copied()
            .ok_or(SheafError::CellOutside(cell))
    }

    /// The coboundary from `degree`, or the zero map from that degree's
    /// cochains to the next degree's where no coboundary starts there.
    ///
    /// # Specification
    /// - ensures: the next degree's dimension as its rows and this degree's as
    ///   its columns.
    /// - fails: a shape past the machine word is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: unreachable for a complex of at most 64
    ///   cells of reasonable width.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the top degree of each level of both towers maps
    ///   through the zero map, so a wrong shape refuses the square.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |matrix| matrix.columns() == self.dimension(degree)))]
    pub(crate) fn coboundary_or_zero(
        &self,
        degree: Rank,
    ) -> Result<Matrix, SheafError>
    {
        if let Some(coboundary) = self.coboundaries.get(usize::from(degree)) {
            return Ok(coboundary.clone());
        }
        let next = Rank::from(usize::from(degree).saturating_add(1));
        Matrix::zero(self.dimension(next), self.dimension(degree))
    }

    /// The cohomology over the rationals, by degree.
    ///
    /// # Specification
    /// - ensures: the dimension of degree `d` is the dimension of its cochains,
    ///   less the rank of the coboundary from `d`, less the rank of the
    ///   coboundary into `d`.
    /// - fails: elimination past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: an entry passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every level of both towers, the interval's with the
    ///   rationals in degree zero alone and the circle's in degrees zero and
    ///   one; L3 — the square oriented as a complex has the rationals in degree
    ///   zero alone.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    /// - witness: `tests::cochains::a_square_oriented_as_a_complex_is_contractible`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |cohomology| cohomology.dimensions.len() == self.dimensions.len()))]
    #[inline]
    pub fn cohomology(&self) -> Result<Cohomology, SheafError>
    {
        let mut ranks = Vec::with_capacity(self.coboundaries.len());
        for coboundary in &self.coboundaries {
            ranks.push(coboundary.rank()?);
        }
        let mut dimensions = Vec::with_capacity(self.dimensions.len());
        for (degree, &cochains) in self.dimensions.iter().enumerate() {
            let out = ranks.get(degree).copied().unwrap_or_default();
            let into = degree
                .checked_sub(1)
                .and_then(|lower| ranks.get(lower).copied())
                .unwrap_or_default();
            let dimension = usize::from(cochains)
                .saturating_sub(usize::from(out))
                .saturating_sub(usize::from(into));
            dimensions.push(Dimension::from(dimension));
        }
        Ok(Cohomology { dimensions })
    }
}

/// The cohomology of a sheaf over the rationals: the dimension of each degree.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cohomology
{
    /// The dimension of each degree, from zero to the highest rank.
    dimensions: Vec<Dimension>,
}

impl Cohomology
{
    /// The dimension of degree `degree`: zero past the highest rank, where no
    /// cochain lives.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn dimension(
        &self,
        degree: Rank,
    ) -> Dimension
    {
        self.dimensions
            .get(usize::from(degree))
            .copied()
            .unwrap_or_default()
    }
}
