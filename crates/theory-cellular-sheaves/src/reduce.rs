//! The reduction of a sheaf along a compatible matching, and its cochains on
//! the critical cells.
//!
//! A matching pairs some cells, each with a face one rank down. It is
//! compatible with a sheaf when the map from each pair's face to its cell,
//! with the sign of the face's incidence, is invertible. An entry map is
//! invertible when the two stalks have one width and the map reads each entry
//! once. Its inverse then reads each entry back, with the same sign. Curry,
//! Ghrist and Nanda reduce the cochains along a compatible matching. By
//! Sköldberg's theorem, the cochains on the critical cells alone have the
//! sheaf's cohomology.
//!
//! The reduced coboundary from a critical cell to a critical cell one rank up
//! sums over the gradient paths between them. A path runs down from the upper
//! cell to a face. From a redundant face it runs up to the face's partner,
//! through the negative of the inverse of the pair's signed map, and then down
//! to another face of the partner. Each path adds the product of the signed
//! maps along it. The Morse crate's walk gives the redundant faces of each
//! critical cell in an order where each comes after every cell whose paths
//! reach it. So the reduction sums the block that reaches each face once.
//!
//! # References
//!
//! - `Curry-2015-discrete_morse_theory_computing_cellular_sheaf_cohomology` —
//!   exemplar: Definition 2.4 makes a matching compatible with a sheaf when
//!   each matched map is invertible, and Theorem 2.6 reduces the cochains along
//!   it with the same cohomology. Justin Curry, Robert Ghrist and Vidit Nanda,
//!   "Discrete Morse Theory for Computing Cellular Sheaf Cohomology",
//!   _Foundations of Computational Mathematics_ 16, 2016, `arXiv:1312.6454`.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_discrete_morse as morse;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Matching;
use gandr_theory_discrete_morse::MorseError;
use gandr_theory_discrete_morse::Place;
use gandr_theory_discrete_morse::Standing;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::Membership;

use crate::cochain::CochainComplex;
use crate::error::SheafError;
use crate::index::Dimension;
use crate::index::Entry;
use crate::index::Incidence;
use crate::index::Slot;
use crate::index::Width;
use crate::matrix::Matrix;
use crate::matrix::Rational;
use crate::sheaf::Sheaf;

/// A sheaf's poset as a complex over the integers: the faces of a cell are
/// the cells one rank down in its boundary, each with the incidence that an
/// orientation gives.
///
/// The greedy matching on it pairs a face with a cell only where the
/// incidence is one or minus one. Where each stalk holds one entry, each such
/// map is invertible, so the matching is compatible.
#[derive(Debug)]
pub struct Oriented<'sheaf, Cell, Orient>
{
    /// The sheaf whose poset the complex reads.
    sheaf: &'sheaf Sheaf<Cell>,
    /// The incidence of each face in each cell one rank above it.
    orientation: Orient,
}

impl<Cell, Orient> Complex for Oriented<'_, Cell, Orient>
where
    Orient: FnMut(&Cell, &Cell) -> Incidence,
{
    type Cell = Element;
    type Fault = SheafError;

    /// Whether `cell` is a cell of the sheaf's poset: below its count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn standing(
        &mut self,
        cell: &Element,
    ) -> Result<Standing, SheafError>
    {
        if usize::from(*cell) < self.sheaf.poset().cells().len() {
            Ok(Standing::Inside)
        }
        else {
            Ok(Standing::Outside)
        }
    }

    /// Push each cell of the boundary of `cell` one rank down onto `faces`,
    /// in cell order, each with the incidence that the orientation gives.
    ///
    /// # Specification
    /// - ensures: each face lies one rank below `cell`, once, in cell order.
    /// - fails: a cell past the poset is refused by name.
    /// - panics: none.
    /// - intension: the orientation is called once for each face.
    ///
    /// # Errors
    /// - [`SheafError::Poset`]: `cell` lies past the poset.
    /// - [`SheafError::CellOutside`]: unreachable for a poset that
    ///   `GradedPoset::new` makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the greedy matching on every level of both towers
    ///   reads its faces, and each reduct keeps the level's cohomology.
    /// - witness: `tests::towers::every_level_of_both_towers_keeps_its_cohomology_on_its_reduct`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::Poset(_) | SheafError::CellOutside(_))))]
    #[inline]
    fn faces(
        &mut self,
        cell: &Element,
        faces: &mut Vec<(Element, morse::Incidence)>,
    ) -> Result<(), SheafError>
    {
        let sheaf = self.sheaf;
        let poset = sheaf.poset();
        let rank = poset.rank(*cell).map_err(SheafError::Poset)?;
        let upper = poset
            .cells()
            .get(usize::from(*cell))
            .ok_or(SheafError::CellOutside(*cell))?;
        for face in poset.boundary(*cell).map_err(SheafError::Poset)?.elements() {
            let below = poset.rank(face).map_err(SheafError::Poset)?;
            if usize::from(below).saturating_add(1) != usize::from(rank) {
                continue;
            }
            let lower = poset
                .cells()
                .get(usize::from(face))
                .ok_or(SheafError::CellOutside(face))?;
            faces.push((face, integral((self.orientation)(lower, upper))));
        }
        Ok(())
    }
}

/// The integer of an incidence: one, minus one or zero.
///
/// # Specification
/// trivial.
fn integral(incidence: Incidence) -> morse::Incidence
{
    morse::Incidence::from(match incidence {
        Incidence::Positive => 1_i64,
        Incidence::Negative => -1_i64,
        Incidence::Zero => 0_i64,
    })
}

/// The factor that a step up a pair and down to another face of the partner
/// adds: the negative of the pair's sign times the face's sign, since a sign
/// is its own inverse.
///
/// # Specification
/// trivial.
const fn carried(
    pair: Incidence,
    face: Incidence,
) -> Rational
{
    match (pair, face) {
        (Incidence::Zero, _) | (_, Incidence::Zero) => Rational::of_incidence(Incidence::Zero),
        (Incidence::Positive, Incidence::Positive) | (Incidence::Negative, Incidence::Negative) => {
            Rational::of_incidence(Incidence::Negative)
        },
        (Incidence::Positive, Incidence::Negative) | (Incidence::Negative, Incidence::Positive) => {
            Rational::of_incidence(Incidence::Positive)
        },
    }
}

/// The cochains of a sheaf reduced along a compatible matching: the critical
/// cells, and the cochains on them alone.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reduced
{
    /// The critical cells, by rank and then by cell.
    cells: Vec<Element>,
    /// The cochains on the critical cells, each cell's slot by its place in
    /// `cells`.
    cochains: CochainComplex,
}

impl Reduced
{
    /// The critical cells, by rank and then by cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(&self) -> &[Element]
    {
        &self.cells
    }

    /// The cochains on the critical cells, whose cohomology is the sheaf's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cochains(&self) -> &CochainComplex
    {
        &self.cochains
    }
}

/// Whether an entry of a stalk is read yet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Read
{
    /// No entry of the map reads it yet.
    Unread,
    /// An entry of the map reads it.
    Taken,
}

/// The block from a critical cell's stalk to the stalk of each face that its
/// paths reach, kept from walk to walk so that no walk allocates once the
/// buffer has grown.
#[derive(Debug)]
struct Blocks
{
    /// The width of the critical cell's stalk: the rows of each block.
    rows: Width,
    /// Where each cell's block starts in `values`, with the width of its
    /// stalk, for each cell that the walk reaches.
    starts: Vec<Option<(Slot, Width)>>,
    /// The blocks, one after the other, each row by row.
    values: Vec<Rational>,
    /// The cells whose block the walk holds, in the order it reaches them.
    touched: Vec<Element>,
}

impl Blocks
{
    /// Starts the blocks of a walk from a critical cell of width `rows`.
    ///
    /// # Specification
    /// trivial.
    fn clear(
        &mut self,
        rows: Width,
    )
    {
        for &cell in &self.touched {
            if let Some(start) = self.starts.get_mut(usize::from(cell)) {
                *start = None;
            }
        }
        self.touched.clear();
        self.values.clear();
        self.rows = rows;
    }

    /// The place of the entry at `row` and `column` of `cell`'s block, which
    /// is made of zeros when the walk has not reached the cell.
    ///
    /// # Specification
    /// - ensures: the place lies inside the values.
    /// - fails: a cell past the poset, or a block past the machine word, is
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: `cell` lies past the poset.
    /// - [`SheafError::Overflow`]: the block passes the machine word.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every reduced coboundary of both towers and of the
    ///   twisted circle is written through it.
    /// - witness: `tests::reduce::a_twisted_circle_keeps_its_cohomology_on_its_reduct`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |place| usize::from(*place) < self.values.len()))]
    fn place(
        &mut self,
        cell: Element,
        columns: Width,
        row: Entry,
        column: Entry,
    ) -> Result<Slot, SheafError>
    {
        let start = self
            .starts
            .get_mut(usize::from(cell))
            .ok_or(SheafError::CellOutside(cell))?;
        let (start, width) = if let Some(held) = *start {
            held
        }
        else {
            let size = usize::from(self.rows)
                .checked_mul(usize::from(columns))
                .ok_or(SheafError::Overflow)?;
            let held = (Slot::from(self.values.len()), columns);
            *start = Some(held);
            self.values
                .resize(self.values.len().saturating_add(size), Rational::ZERO);
            self.touched.push(cell);
            held
        };
        offset(start, self.rows, width, row, column).ok_or(SheafError::ShapeMismatch)
    }

    /// The entry at `row` and `column` of `cell`'s block: zero when the walk
    /// has not reached the cell.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        cell: Element,
        row: Entry,
        column: Entry,
    ) -> Rational
    {
        self.starts
            .get(usize::from(cell))
            .copied()
            .flatten()
            .and_then(|(start, width)| offset(start, self.rows, width, row, column))
            .and_then(|place| self.values.get(usize::from(place)))
            .copied()
            .unwrap_or(Rational::ZERO)
    }

    /// Adds `value` to the entry at `row` and `column` of `cell`'s block,
    /// whose columns are the entries of a stalk of width `columns`.
    ///
    /// # Specification
    /// - ensures: the entry grows by `value`, and no other entry changes.
    /// - fails: a sum past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: the sum passes the integers.
    /// - [`SheafError::CellOutside`], [`SheafError::ShapeMismatch`]:
    ///   unreachable for the cells and entries a walk reads.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every reduced coboundary of both towers and of the
    ///   twisted circle is summed through it.
    /// - witness: `tests::reduce::a_twisted_circle_keeps_its_cohomology_on_its_reduct`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::Overflow | SheafError::CellOutside(_) | SheafError::ShapeMismatch)))]
    fn add(
        &mut self,
        cell: Element,
        columns: Width,
        row: Entry,
        column: Entry,
        value: Rational,
    ) -> Result<(), SheafError>
    {
        let place = self.place(cell, columns, row, column)?;
        let entry = self
            .values
            .get_mut(usize::from(place))
            .ok_or(SheafError::ShapeMismatch)?;
        *entry = entry.plus(value)?;
        Ok(())
    }
}

/// The place of the entry at `row` and `column` of a block that starts at
/// `start`, with `rows` rows and `columns` columns: nothing past its shape or
/// past the machine word.
///
/// # Specification
/// trivial.
fn offset(
    start: Slot,
    rows: Width,
    columns: Width,
    row: Entry,
    column: Entry,
) -> Option<Slot>
{
    if usize::from(row) >= usize::from(rows) || usize::from(column) >= usize::from(columns) {
        return None;
    }
    let within = usize::from(row)
        .checked_mul(usize::from(columns))?
        .checked_add(usize::from(column))?;
    within.checked_add(usize::from(start)).map(Slot::from)
}

impl<Cell> Sheaf<Cell>
{
    /// This sheaf's poset as a complex over the integers, each face with the
    /// incidence that `orientation` gives, so that the greedy matching reads
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn oriented<Orient>(
        &self,
        orientation: Orient,
    ) -> Oriented<'_, Cell, Orient>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
    {
        Oriented {
            sheaf: self,
            orientation,
        }
    }

    /// The cochains of this sheaf reduced along `matching`, each face's sign
    /// the incidence that `orientation` gives: the cochains on the critical
    /// cells alone, whose cohomology is the sheaf's.
    ///
    /// # Specification
    /// - requires: `matching` is acyclic on [`Sheaf::oriented`], as the greedy
    ///   matching on it is, and the incidences are those of a complex.
    /// - ensures: the cells are the critical cells, by rank and then by cell.
    ///   The reduced coboundary from a critical cell to a critical cell one
    ///   rank up sums the product of the signed maps along each gradient path
    ///   between them, and a step up a pair takes the negative of the inverse
    ///   of its signed map. Each two reduced coboundaries in turn compose to
    ///   zero.
    /// - fails: a pair whose signed map is not invertible is refused by its two
    ///   cells, before any walk. A walk past `budget` redundant cells is
    ///   refused, never cut short.
    /// - panics: none.
    /// - intension: `orientation` is called once for each pair of the matching,
    ///   once for each face as the walk reads the complex, and once for each
    ///   face that a sum reads. A walk sums the block that reaches each face
    ///   once, one rational for each entry of the critical cell's stalk and
    ///   each entry of the face's stalk.
    ///
    /// # Errors
    /// - [`SheafError::NotInvertible`]: a pair's signed map is not invertible.
    /// - [`SheafError::PastBudget`]: a walk reaches more than `budget`
    ///   redundant cells.
    /// - [`SheafError::NotAComplex`]: the reduced coboundaries from a degree
    ///   and the next compose to a map that is not zero.
    /// - [`SheafError::Overflow`]: a sum passes the integers.
    /// - [`SheafError::CellOutside`], [`SheafError::Poset`]: a matched cell
    ///   lies past the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every level of both towers keeps its cohomology on
    ///   its reduct, the interval's from one vertex and the circle's from one
    ///   vertex and one edge; the circle with stalks of two entries and a swap
    ///   on one edge keeps its cohomology at each level. L3 — a loop's zero
    ///   incidence and a stalk of another width are each refused by their pair;
    ///   a budget of none refuses the first walk.
    /// - witness: `tests::towers::every_level_of_both_towers_keeps_its_cohomology_on_its_reduct`
    /// - witness: `tests::reduce::a_twisted_circle_keeps_its_cohomology_on_its_reduct`
    /// - witness: `tests::reduce::a_matched_map_that_is_not_invertible_is_refused_by_its_pair`
    /// - witness: `tests::reduce::a_walk_past_its_budget_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |reduced| reduced.cells.len() <= self.poset().cells().len()))]
    #[inline]
    pub fn reduce<Orient>(
        &self,
        matching: &Matching<Element>,
        mut orientation: Orient,
        budget: Budget,
    ) -> Result<Reduced, SheafError>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
    {
        let poset = self.poset();
        let count = poset.cells().len();
        let mut taken: Vec<Read> = Vec::new();
        for (lower, class) in matching.cells().iter().zip(matching.classes()) {
            if let Class::Redundant(upper) = *class {
                self.invertible(*lower, upper, &mut orientation, &mut taken)?;
            }
        }
        let mut ranks: Vec<Rank> = Vec::with_capacity(count);
        for cell in (0 .. count).map(Element::from) {
            ranks.push(poset.rank(cell).map_err(SheafError::Poset)?);
        }
        let mut cells: Vec<Element> = (0 .. count).map(Element::from).collect();
        cells.sort_by_key(|&cell| ranks.get(usize::from(cell)).copied().unwrap_or_default());
        let reduct = {
            let mut complex = self.oriented(&mut orientation);
            morse::reduct(&mut matching.on(&mut complex), &cells, budget).map_err(|error| {
                match error {
                    MorseError::Complex(fault) => fault,
                    MorseError::PastBudget(past) => SheafError::PastBudget(past),
                    MorseError::Overflow => SheafError::Overflow,
                }
            })?
        };
        let degrees = ranks
            .iter()
            .map(|&rank| usize::from(rank).saturating_add(1))
            .max()
            .unwrap_or(0);
        let mut dimensions = vec![Dimension::default(); degrees];
        let mut slots = Vec::with_capacity(reduct.cells().len());
        let mut places: Vec<Option<Place>> = vec![None; count];
        for (at, &cell) in reduct.cells().iter().enumerate() {
            let rank = ranks
                .get(usize::from(cell))
                .copied()
                .ok_or(SheafError::CellOutside(cell))?;
            let dimension = dimensions
                .get_mut(usize::from(rank))
                .ok_or(SheafError::CellOutside(cell))?;
            slots.push(Slot::from(usize::from(*dimension)));
            *dimension = Dimension::from(
                usize::from(*dimension).saturating_add(usize::from(self.width(cell)?)),
            );
            if let Some(place) = places.get_mut(usize::from(cell)) {
                *place = Some(Place::from(at));
            }
        }
        let mut coboundaries = Vec::with_capacity(degrees.saturating_sub(1));
        for pair in dimensions.windows(2) {
            if let [columns, rows] = *pair {
                coboundaries.push(Matrix::zero(rows, columns)?);
            }
        }
        let mut blocks = Blocks {
            rows: Width::default(),
            starts: vec![None; count],
            values: Vec::new(),
            touched: Vec::new(),
        };
        for (at, &upper) in reduct.cells().iter().enumerate() {
            let rank = ranks
                .get(usize::from(upper))
                .copied()
                .ok_or(SheafError::CellOutside(upper))?;
            let Some(degree) = usize::from(rank).checked_sub(1)
            else {
                continue;
            };
            let width = self.width(upper)?;
            blocks.clear(width);
            self.start(
                upper,
                Rank::from(degree),
                &ranks,
                &mut orientation,
                &mut blocks,
            )?;
            for &place in reduct.walk(Place::from(at)) {
                let Some(&lower) = cells.get(usize::from(place))
                else {
                    continue;
                };
                if let Class::Redundant(partner) = matching.class(&lower) {
                    self.carry(lower, partner, &ranks, &mut orientation, &mut blocks)?;
                }
            }
            let row_start = slots
                .get(at)
                .copied()
                .ok_or(SheafError::CellOutside(upper))?;
            let coboundary = coboundaries
                .get_mut(degree)
                .ok_or(SheafError::CellOutside(upper))?;
            for &face in &blocks.touched {
                let Some(&Some(face_at)) = places.get(usize::from(face))
                else {
                    continue;
                };
                let column_start = slots
                    .get(usize::from(face_at))
                    .copied()
                    .ok_or(SheafError::CellOutside(face))?;
                let columns = self.width(face)?;
                for row in (0 .. usize::from(width)).map(Entry::from) {
                    for column in (0 .. usize::from(columns)).map(Entry::from) {
                        let value = blocks.at(face, row, column);
                        if value == Rational::ZERO {
                            continue;
                        }
                        coboundary.add(
                            Slot::from(usize::from(row_start).saturating_add(usize::from(row))),
                            Slot::from(
                                usize::from(column_start).saturating_add(usize::from(column)),
                            ),
                            value,
                        )?;
                    }
                }
            }
        }
        Ok(Reduced {
            cells: reduct.cells().to_vec(),
            cochains: CochainComplex::assembled(slots, dimensions, coboundaries)?,
        })
    }

    /// Checks that the map from `lower` to `upper`, with the sign of
    /// `lower`'s incidence, is invertible.
    ///
    /// # Specification
    /// - ensures: the map is invertible: `lower` is a face of `upper` one rank
    ///   down, its incidence is not zero, the two stalks have one width, and
    ///   the map reads each entry once.
    /// - fails: any other pair is refused by its two cells.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::NotInvertible`]: the signed map is not invertible.
    /// - [`SheafError::CellOutside`], [`SheafError::Poset`]: a cell lies past
    ///   the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a loop's zero incidence and a stalk of another width
    ///   are each refused by their pair, and every pair of both towers passes.
    /// - witness: `tests::reduce::a_matched_map_that_is_not_invertible_is_refused_by_its_pair`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::NotInvertible { .. } | SheafError::CellOutside(_) | SheafError::Poset(_))))]
    fn invertible<Orient>(
        &self,
        lower: Element,
        upper: Element,
        orientation: &mut Orient,
        taken: &mut Vec<Read>,
    ) -> Result<(), SheafError>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
    {
        let refused = SheafError::NotInvertible { lower, upper };
        let poset = self.poset();
        let (Some(lower_cell), Some(upper_cell)) = (
            poset.cells().get(usize::from(lower)),
            poset.cells().get(usize::from(upper)),
        )
        else {
            return Err(refused);
        };
        let face = poset
            .boundary(upper)
            .map_err(SheafError::Poset)?
            .contains(lower);
        let below = poset.rank(lower).map_err(SheafError::Poset)?;
        let above = poset.rank(upper).map_err(SheafError::Poset)?;
        if face != Membership::Inside || usize::from(below).saturating_add(1) != usize::from(above)
        {
            return Err(refused);
        }
        if orientation(lower_cell, upper_cell) == Incidence::Zero {
            return Err(refused);
        }
        let width = self.width(upper)?;
        if self.width(lower)? != width {
            return Err(refused);
        }
        taken.clear();
        taken.resize(usize::from(width), Read::Unread);
        for entry in (0 .. usize::from(width)).map(Entry::from) {
            let read = self.read(lower, upper, entry)?;
            let slot = taken.get_mut(usize::from(read)).ok_or(refused)?;
            if *slot == Read::Taken {
                return Err(refused);
            }
            *slot = Read::Taken;
        }
        Ok(())
    }

    /// Starts the blocks of the walk from the critical cell `upper` at its
    /// own faces of rank `degree`: each face's signed map.
    ///
    /// # Specification
    /// - ensures: the block of each face holds, at the row of each entry of
    ///   `upper`'s stalk and the column of the entry that its map reads, the
    ///   sign of the face's incidence.
    /// - fails: a sum past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a sum passes the integers.
    /// - [`SheafError::CellOutside`], [`SheafError::Poset`],
    ///   [`SheafError::EntryOutside`], [`SheafError::ShapeMismatch`]:
    ///   unreachable for a sheaf that `Sheaf::new` makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every level of both towers and of the twisted circle,
    ///   whose reduced coboundaries start here.
    /// - witness: `tests::reduce::a_twisted_circle_keeps_its_cohomology_on_its_reduct`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::Overflow | SheafError::CellOutside(_) | SheafError::Poset(_) | SheafError::EntryOutside { .. } | SheafError::ShapeMismatch)))]
    fn start<Orient>(
        &self,
        upper: Element,
        degree: Rank,
        ranks: &[Rank],
        orientation: &mut Orient,
        blocks: &mut Blocks,
    ) -> Result<(), SheafError>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
    {
        let poset = self.poset();
        let upper_cell = poset
            .cells()
            .get(usize::from(upper))
            .ok_or(SheafError::CellOutside(upper))?;
        let width = self.width(upper)?;
        for face in poset.boundary(upper).map_err(SheafError::Poset)?.elements() {
            if ranks.get(usize::from(face)) != Some(&degree) {
                continue;
            }
            let face_cell = poset
                .cells()
                .get(usize::from(face))
                .ok_or(SheafError::CellOutside(face))?;
            let sign = orientation(face_cell, upper_cell);
            if sign == Incidence::Zero {
                continue;
            }
            let columns = self.width(face)?;
            let value = Rational::of_incidence(sign);
            for row in (0 .. usize::from(width)).map(Entry::from) {
                let column = self.read(face, upper, row)?;
                blocks.add(face, columns, row, column, value)?;
            }
        }
        Ok(())
    }

    /// Carries the block that reaches the redundant cell `lower` up to its
    /// partner `partner` and down to each other face of the partner.
    ///
    /// # Specification
    /// - requires: the map from `lower` to `partner` is invertible, and the
    ///   walk has summed every path that reaches `lower`.
    /// - ensures: the block of each other face of the partner grows by the
    ///   block of `lower`, times the negative of the inverse of the pair's
    ///   signed map, times the face's signed map.
    /// - fails: a sum past the integers is refused.
    /// - panics: none.
    /// - intension: one pass over each entry of the critical cell's stalk and
    ///   each entry of the partner's stalk, for each face of the partner.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a sum passes the integers.
    /// - [`SheafError::CellOutside`], [`SheafError::Poset`],
    ///   [`SheafError::EntryOutside`], [`SheafError::ShapeMismatch`]:
    ///   unreachable for a sheaf that `Sheaf::new` makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the circle's reduct at each level from one, and the
    ///   twisted circle's, whose edges cancel along the walk only where the
    ///   inverse reads each entry back.
    /// - witness: `tests::reduce::a_twisted_circle_keeps_its_cohomology_on_its_reduct`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::Overflow | SheafError::CellOutside(_) | SheafError::Poset(_) | SheafError::EntryOutside { .. } | SheafError::ShapeMismatch)))]
    fn carry<Orient>(
        &self,
        lower: Element,
        partner: Element,
        ranks: &[Rank],
        orientation: &mut Orient,
        blocks: &mut Blocks,
    ) -> Result<(), SheafError>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
    {
        let poset = self.poset();
        let rows = blocks.rows;
        let (Some(lower_cell), Some(partner_cell)) = (
            poset.cells().get(usize::from(lower)),
            poset.cells().get(usize::from(partner)),
        )
        else {
            return Err(SheafError::CellOutside(partner));
        };
        let pair = orientation(lower_cell, partner_cell);
        let degree = ranks.get(usize::from(lower)).copied();
        let width = self.width(partner)?;
        for face in poset
            .boundary(partner)
            .map_err(SheafError::Poset)?
            .elements()
        {
            if face == lower || ranks.get(usize::from(face)).copied() != degree {
                continue;
            }
            let face_cell = poset
                .cells()
                .get(usize::from(face))
                .ok_or(SheafError::CellOutside(face))?;
            let sign = orientation(face_cell, partner_cell);
            let factor = carried(pair, sign);
            if factor == Rational::ZERO {
                continue;
            }
            let columns = self.width(face)?;
            for entry in (0 .. usize::from(width)).map(Entry::from) {
                let from = self.read(lower, partner, entry)?;
                let onto = self.read(face, partner, entry)?;
                for row in (0 .. usize::from(rows)).map(Entry::from) {
                    let value = blocks.at(lower, row, from);
                    if value == Rational::ZERO {
                        continue;
                    }
                    blocks.add(face, columns, row, onto, factor.times(value)?)?;
                }
            }
        }
        Ok(())
    }
}
