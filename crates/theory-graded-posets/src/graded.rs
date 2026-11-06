//! Finite graded posets whose cells are data, the lattice of their
//! subcomplexes, and its spectrum read back as the poset.
//!
//! A cell carries data of the caller's type, and an order on that data says
//! which cell lies below which. The cells below a cell are its boundary. The
//! cell with its boundary is its closure, held as a row of words, one bit for
//! each cell. A subcomplex is a set of cells that holds the boundary of each
//! of its cells, so it is a down-set of the order. The subcomplexes form a
//! finite distributive lattice under union and intersection. The
//! join-irreducible subcomplexes are the closures of the cells, so the
//! spectrum of that lattice is the poset again.
//!
//! A poset of at most 64 cells keeps one word for each cell, as finite Stone
//! duality's [`FinitePoset`](gandr_theory_stone_duality::FinitePoset) does. A
//! wider poset keeps one word for each 64 cells in each row, up to the count
//! its caller states. The crate enumerates the subcomplexes and reads the
//! spectrum through finite Stone duality, so those two stay within 64 cells.
//! It adds the cells as data, the rank and the two maps that show the spectrum
//! is the poset.
//!
//! The rank of a cell is the length of the longest chain of cells below it,
//! so it rises strictly along the order. The face poset of a shape need not
//! raise the rank by exactly one at each cover: a side of a square that holds
//! a corner as a cell has rank one, and the opposite side, which holds no
//! corner, has rank zero. The crate does not ask for that.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::Membership;
use gandr_theory_stone_duality::MonotoneMap;
use gandr_theory_stone_duality::SetRing;
use gandr_theory_stone_duality::Spectrum;

use crate::rows::CellOrder;
use crate::rows::CellRow;

/// The rank of a cell: the length of the longest chain of cells below it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rank(usize);

impl From<usize> for Rank
{
    /// Wraps the length of a chain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Rank> for usize
{
    /// Unwraps the length of a chain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Rank) -> Self
    {
        value.0
    }
}

/// A finite graded poset: each cell's data, its closure as a row of words, and
/// its rank, in cell order.
///
/// # Specification
/// - ensures: the cells, the bit rows and the ranks hold one entry for each
///   cell; a cell's rank is one more than the greatest rank in its boundary,
///   and zero when its boundary is empty.
/// - provides: the order, the boundary, the rank, the lattice of subcomplexes
///   and its spectrum.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`GradedPoset::new`]'s, which makes it.
///
/// # Adequacy
/// - hypothesis: L2 — every face family over up to three points and the four
///   corpus shapes, against a naive enumeration of the subcomplexes, separate a
///   lost cell or a wrong order; L3 — the square's sides separate a rank read
///   as the closure's size.
/// - witness: `tests::subcomplexes::every_small_face_family_reads_back_from_its_subcomplexes`
/// - witness: `tests::graded::a_square_ranks_its_cells_by_their_longest_chain`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GradedPoset<Cell>
{
    /// Each cell's data, in cell order.
    cells: Vec<Cell>,
    /// The order: each cell's closure as a row of words.
    order: CellOrder,
    /// Each cell's rank, in cell order.
    ranks: Vec<Rank>,
}

impl<Cell> GradedPoset<Cell>
{
    /// The graded poset on `cells` that `below` orders: it puts the first
    /// cell below the second.
    ///
    /// # Specification
    /// - ensures: the order is the least order that holds each pair `below`
    ///   puts below, and each cell's rank is the length of the longest chain
    ///   below it.
    /// - fails: more cells than `most` are refused by their count, before
    ///   `below` is called; two distinct cells that the order puts each below
    ///   the other are refused by the least such pair.
    /// - panics: none.
    /// - intension: `below` is called once for each ordered pair of distinct
    ///   cells. The closure takes one pass over the rows for each cell, a word
    ///   at a time. The ranks take one pass over the cells by the size of their
    ///   closure, which puts each cell after the cells below it.
    ///
    /// # Errors
    /// - [`DualityError::TooManyElements`]: more cells than `most`.
    /// - [`DualityError::Cycle`]: two distinct cells lie each below the other.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every face family over up to three points, and random
    ///   orders on 65 and 130 cells against a naive closure, separate a lost
    ///   pair; L3 — one cell past `most`, refused with `below` never called,
    ///   and two equal faces separate the refusals.
    /// - witness: `tests::subcomplexes::every_small_face_family_reads_back_from_its_subcomplexes`
    /// - witness: `tests::graded::a_poset_past_the_cell_budget_is_refused_uncomputed`
    /// - witness: `tests::wide::a_wide_poset_answers_as_its_naive_closure`
    /// - witness: `tests::graded::two_cells_each_below_the_other_are_refused`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref poset) => poset.ranks.len() == poset.cells.len()
            && poset.order.count() == ElementCount::from(poset.cells.len()),
        Err(error) => matches!(error, DualityError::TooManyElements(_) | DualityError::Cycle(_, _)),
    })]
    #[inline]
    pub fn new<Below>(
        cells: Vec<Cell>,
        below: Below,
        most: ElementCount,
    ) -> Result<Self, DualityError>
    where
        Below: FnMut(&Cell, &Cell) -> Comparison,
    {
        if cells.len() > usize::from(most) {
            return Err(DualityError::TooManyElements(ElementCount::from(
                cells.len(),
            )));
        }
        let order = CellOrder::new(&cells, below)?;
        let ranks = ranks(&order)?;
        Ok(Self {
            cells,
            order,
            ranks,
        })
    }

    /// The graded poset on `cells` ordered by inclusion of the points each
    /// holds, of `points` points: a cell lies below another when the other
    /// holds each of its points and the two differ in a point.
    ///
    /// # Specification
    /// - ensures: the order is [`GradedPoset::new`]'s with `below` the strict
    ///   inclusion of the cells' points, so two cells that hold the same points
    ///   are apart; each cell's rank is the length of the longest chain below
    ///   it.
    /// - fails: more cells than `most` are refused by their count, before
    ///   `holds` is called.
    /// - panics: none.
    /// - intension: `holds` is called once for each cell and point, and no pair
    ///   of cells is compared. A cell's row meets the row of the cells that
    ///   lack each point the cell lacks, one word at a time, so the build reads
    ///   `⌈n / 64⌉` words for each cell and point. Inclusion is an order, so
    ///   the rows need no closure and no cycle check.
    ///
    /// # Errors
    /// - [`DualityError::TooManyElements`]: more cells than `most`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — random sets of points on 6, 65 and 130 cells, with
    ///   repeated sets, against [`GradedPoset::new`] over strict inclusion,
    ///   separate a lost pair, a bit in the wrong word and two equal sets read
    ///   as a cycle; L3 — one cell past `most`, refused with `holds` never
    ///   called, separates the refusal.
    /// - witness: `tests::wide::an_inclusion_order_is_the_order_its_pairs_give`
    /// - witness: `tests::graded::a_poset_past_the_cell_budget_is_refused_uncomputed`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref poset) => poset.ranks.len() == poset.cells.len()
            && poset.order.count() == ElementCount::from(poset.cells.len()),
        Err(error) => matches!(error, DualityError::TooManyElements(_)),
    })]
    #[inline]
    pub fn by_inclusion<Holds>(
        cells: Vec<Cell>,
        points: ElementCount,
        holds: Holds,
        most: ElementCount,
    ) -> Result<Self, DualityError>
    where
        Holds: FnMut(&Cell, Element) -> Membership,
    {
        if cells.len() > usize::from(most) {
            return Err(DualityError::TooManyElements(ElementCount::from(
                cells.len(),
            )));
        }
        let order = CellOrder::by_inclusion(&cells, points, holds)?;
        let ranks = ranks(&order)?;
        Ok(Self {
            cells,
            order,
            ranks,
        })
    }

    /// The number of cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count(&self) -> ElementCount
    {
        self.order.count()
    }

    /// Each cell's data, in cell order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(&self) -> &[Cell]
    {
        &self.cells
    }

    /// Whether `lower` lies below `upper`: whether the closure of `upper`
    /// holds `lower`.
    ///
    /// # Specification
    /// - ensures: [`Comparison::Below`] exactly when the order puts `lower`
    ///   below `upper`, each cell below itself.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `lower` or `upper` is at or past the
    ///   count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every corpus shape's face poset, against inclusion of
    ///   the faces, and random orders on 65 and 130 cells, against a naive
    ///   closure, separate a pair read from the wrong word.
    /// - witness: `tests::subcomplexes::every_corpus_shape_reads_its_face_poset_back_from_its_subcomplexes`
    /// - witness: `tests::wide::a_wide_poset_answers_as_its_naive_closure`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(DualityError::ElementOutside(_))))]
    #[inline]
    pub fn compare(
        &self,
        lower: Element,
        upper: Element,
    ) -> Result<Comparison, DualityError>
    {
        if usize::from(lower) >= self.cells.len() {
            return Err(DualityError::ElementOutside(lower));
        }
        Ok(match self.order.row(upper)?.contains(lower) {
            Membership::Inside => Comparison::Below,
            Membership::Outside => Comparison::NotBelow,
        })
    }

    /// The closure of a cell: the cell and its boundary.
    ///
    /// # Specification
    /// - provides: the row the order holds for `cell`.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the closures of every face family over up to three
    ///   points are the spectrum's points.
    /// - witness: `tests::subcomplexes::every_small_face_family_reads_back_from_its_subcomplexes`
    #[spec(ensures: |ref ret| match *ret {
        Ok(closure) => closure.contains(cell) == Membership::Inside,
        Err(error) => error == DualityError::ElementOutside(cell),
    })]
    #[inline]
    pub fn closure(
        &self,
        cell: Element,
    ) -> Result<CellRow<'_>, DualityError>
    {
        self.order.row(cell)
    }

    /// The boundary of a cell: every cell strictly below it.
    ///
    /// # Specification
    /// - ensures: the boundary is the closure without the cell.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the square's whole cell holds every other cell in its
    ///   boundary, and a side holds the corner or nothing.
    /// - witness: `tests::graded::a_square_ranks_its_cells_by_their_longest_chain`
    #[spec(ensures: |ref ret| match *ret {
        Ok(boundary) => boundary.contains(cell) == Membership::Outside,
        Err(error) => error == DualityError::ElementOutside(cell),
    })]
    #[inline]
    pub fn boundary(
        &self,
        cell: Element,
    ) -> Result<CellRow<'_>, DualityError>
    {
        Ok(self.order.row(cell)?.without(cell))
    }

    /// The rank of a cell: the length of the longest chain of cells below it.
    ///
    /// # Specification
    /// - provides: the rank [`GradedPoset::new`] computed for `cell`.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the square's cells have ranks zero, one and two, and
    ///   its two kinds of side differ.
    /// - witness: `tests::graded::a_square_ranks_its_cells_by_their_longest_chain`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(DualityError::ElementOutside(cell)))]
    #[inline]
    pub fn rank(
        &self,
        cell: Element,
    ) -> Result<Rank, DualityError>
    {
        self.ranks
            .get(usize::from(cell))
            .copied()
            .ok_or(DualityError::ElementOutside(cell))
    }

    /// The lattice of subcomplexes: each set of cells that holds the boundary
    /// of each of its cells.
    ///
    /// # Specification
    /// - ensures: the members are exactly the down-sets of the order, in
    ///   increasing order of their bits.
    /// - fails: a lattice past `budget` members is refused, and so is a poset
    ///   of more than 64 cells, whose sets finite Stone duality does not hold.
    /// - panics: none.
    /// - intension: finite Stone duality's enumeration of down-sets, linear in
    ///   the number of subcomplexes times the number of cells, after one copy
    ///   of the order into one-word rows.
    ///
    /// # Errors
    /// - [`DualityError::PastBudget`]: the poset has more than `budget`
    ///   subcomplexes.
    /// - [`DualityError::TooManyElements`]: the poset has more than 64 cells.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every face family over up to three points and the
    ///   four corpus shapes, against the sets that hold the closure of each of
    ///   their cells, separate a lost or a doubled subcomplex; L3 — a budget
    ///   one short of the square's 21 subcomplexes separates the refusal.
    /// - witness: `tests::subcomplexes::every_corpus_shape_reads_its_face_poset_back_from_its_subcomplexes`
    /// - witness: `tests::graded::a_lattice_past_its_budget_is_refused`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref lattice) => lattice.carrier() == self.count() && lattice.members().len() <= usize::from(budget),
        Err(error) => error == DualityError::PastBudget(budget) || matches!(error, DualityError::TooManyElements(_)),
    })]
    #[inline]
    pub fn subcomplexes(
        &self,
        budget: Budget,
    ) -> Result<SetRing, DualityError>
    {
        self.order.narrow()?.down_sets(budget)
    }

    /// The lattice of subcomplexes, its spectrum, and the two monotone maps
    /// between the spectrum and the poset that show the spectrum is the poset.
    ///
    /// # Specification
    /// - ensures: the points of the spectrum are the closures of the cells, in
    ///   increasing order of their bits; the map to the cells sends each point
    ///   to the cell whose closure it is, and the map from the cells is its
    ///   inverse, so both maps keep the order.
    /// - fails: a lattice past `budget` members is refused, and so is a poset
    ///   of more than 64 cells.
    /// - panics: none.
    /// - intension: the closures sorted by their bits name each point's cell,
    ///   so no point is searched for.
    ///
    /// # Errors
    /// - [`DualityError::PastBudget`]: the poset has more than `budget`
    ///   subcomplexes.
    /// - [`DualityError::TooManyElements`]: the poset has more than 64 cells.
    /// - [`DualityError::ImageCount`], [`DualityError::NotMonotone`],
    ///   [`DualityError::ElementOutside`]: unreachable for a poset
    ///   [`GradedPoset::new`] makes, since its join-irreducible subcomplexes
    ///   are the closures of its cells.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every face family over up to three points and the
    ///   four corpus shapes, against the join-irreducible subcomplexes computed
    ///   from their definition, separate a lost cell or a reversed order.
    /// - witness: `tests::subcomplexes::every_small_face_family_reads_back_from_its_subcomplexes`
    /// - witness: `tests::subcomplexes::every_corpus_shape_reads_its_face_poset_back_from_its_subcomplexes`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |read| read.spectrum.points().len() == self.cells.len()
        && read.to_cells.images().len() == self.cells.len()
        && read.from_cells.images().len() == self.cells.len()))]
    #[inline]
    pub fn read_back(
        &self,
        budget: Budget,
    ) -> Result<ReadBack, DualityError>
    {
        let order = self.order.narrow()?;
        let subcomplexes = order.down_sets(budget)?;
        let spectrum = subcomplexes.spectrum()?;
        let count = self.cells.len();
        let mut by_closure = Vec::with_capacity(count);
        for cell in 0 .. count {
            let closure = order.below(Element::from(cell))?;
            by_closure.push((closure, Element::from(cell)));
        }
        by_closure.sort_unstable();
        let mut inverse = vec![Element::default(); count];
        for (point, &(_, cell)) in by_closure.iter().enumerate() {
            let slot = inverse
                .get_mut(usize::from(cell))
                .ok_or(DualityError::ElementOutside(cell))?;
            *slot = Element::from(point);
        }
        let images = by_closure.into_iter().map(|(_, cell)| cell).collect();
        let to_cells = MonotoneMap::new(spectrum.poset(), &order, images)?;
        let from_cells = MonotoneMap::new(&order, spectrum.poset(), inverse)?;
        Ok(ReadBack {
            subcomplexes,
            spectrum,
            to_cells,
            from_cells,
        })
    }
}

/// The rank of each cell of `order`: one more than the greatest rank in its
/// boundary, and zero for an empty boundary.
///
/// # Specification
/// - ensures: one rank for each cell, rising strictly along the order.
/// - fails: only on a broken invariant of the order.
/// - panics: none.
/// - intension: a cell strictly below another has a strictly smaller closure,
///   so the cells taken by the size of their closure come after every cell
///   below them, and each rank is read once it is final.
///
/// # Errors
/// - [`DualityError::ElementOutside`]: unreachable for an order
///   [`GradedPoset::new`] makes.
///
/// # Adequacy
/// - hypothesis: L3 — the square's sides separate a rank read as the size of
///   the closure from the longest chain.
/// - witness: `tests::graded::a_square_ranks_its_cells_by_their_longest_chain`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ranks| ElementCount::from(ranks.len()) == order.count()))]
fn ranks(order: &CellOrder) -> Result<Vec<Rank>, DualityError>
{
    let count = usize::from(order.count());
    let mut by_size = Vec::with_capacity(count);
    for cell in (0 .. count).map(Element::from) {
        by_size.push((order.row(cell)?.count(), cell));
    }
    by_size.sort_unstable();
    let mut ranks = vec![Rank::default(); count];
    for &(_, cell) in &by_size {
        let closure = order.row(cell)?;
        let mut rank = 0_usize;
        for lower in closure.elements() {
            if lower != cell {
                let lower_rank = ranks
                    .get(usize::from(lower))
                    .ok_or(DualityError::ElementOutside(lower))?;
                rank = rank.max(lower_rank.0.saturating_add(1));
            }
        }
        let slot = ranks
            .get_mut(usize::from(cell))
            .ok_or(DualityError::ElementOutside(cell))?;
        *slot = Rank(rank);
    }
    Ok(ranks)
}

/// The lattice of subcomplexes of a graded poset, its spectrum, and the two
/// monotone maps that show the spectrum is the poset.
///
/// # Specification
/// - ensures: the two maps are inverse to each other and both keep the order.
/// - provides: the lattice, the spectrum and both maps.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`GradedPoset::read_back`]'s, which makes it.
///
/// # Adequacy
/// - hypothesis: L2 — every face family over up to three points and the four
///   corpus shapes separate a map that is not one to one.
/// - witness: `tests::subcomplexes::every_small_face_family_reads_back_from_its_subcomplexes`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReadBack
{
    /// The lattice of subcomplexes.
    subcomplexes: SetRing,
    /// Its join-irreducible members, ordered by inclusion.
    spectrum: Spectrum,
    /// Each point of the spectrum to the cell whose closure it is.
    to_cells: MonotoneMap,
    /// Each cell to the point that is its closure.
    from_cells: MonotoneMap,
}

impl ReadBack
{
    /// The lattice of subcomplexes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn subcomplexes(&self) -> &SetRing
    {
        &self.subcomplexes
    }

    /// The spectrum of the lattice: its join-irreducible members, the
    /// closures of the cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn spectrum(&self) -> &Spectrum
    {
        &self.spectrum
    }

    /// The map from the spectrum to the poset: each point to the cell whose
    /// closure it is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn to_cells(&self) -> &MonotoneMap
    {
        &self.to_cells
    }

    /// The map from the poset to the spectrum: each cell to its closure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn from_cells(&self) -> &MonotoneMap
    {
        &self.from_cells
    }
}
