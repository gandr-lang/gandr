//! The order of a graded poset as rows of words: each cell's closure holds one
//! bit for each cell, sixty-four cells to a word.
//!
//! A poset of at most 64 cells keeps one word for each cell, as finite Stone
//! duality's [`FinitePoset`] does. A poset of `n` cells keeps `⌈n / 64⌉` words
//! for each cell, so no width of the order is fixed.
//!
//! An order that pairs of cells state is closed by Warshall's closure, one
//! word at a time, and its cycle refusal names the pair that
//! [`FinitePoset::new`] names. An order by inclusion of points compares no
//! pair: the cells below a cell are the cells that lack each point it lacks,
//! so its row is the meet of one row for each such point. Inclusion is an
//! order, so those rows need no closure and no cycle check.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::FinitePoset;
use gandr_theory_stone_duality::Membership;

/// The bits one word of a row holds.
const WORD: usize = 64;

/// Where a row holds a bit: the word, and the bit's mask in that word.
#[derive(Clone, Copy, Debug)]
struct Place
{
    /// The word of the row.
    word: usize,
    /// The bit's mask in the word.
    bit: u64,
}

impl Place
{
    /// The place of the bit for `index`.
    ///
    /// # Specification
    /// trivial.
    fn of(index: Element) -> Self
    {
        let index = usize::from(index);
        Self {
            word: index.checked_div(WORD).unwrap_or_default(),
            bit: index
                .checked_rem(WORD)
                .and_then(|bit| u32::try_from(bit).ok())
                .and_then(|bit| 1_u64.checked_shl(bit))
                .unwrap_or_default(),
        }
    }
}

/// Rows of bits of one width, the rows one after another.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Rows
{
    /// The words of each row: one for each 64 bits, rounded up.
    stride: usize,
    /// The rows' words.
    words: Vec<u64>,
}

impl Rows
{
    /// `count` rows of `width` bits, each bit clear.
    ///
    /// # Specification
    /// trivial.
    fn new(
        count: ElementCount,
        width: ElementCount,
    ) -> Result<Self, DualityError>
    {
        let stride = usize::from(width).div_ceil(WORD);
        let size = usize::from(count)
            .checked_mul(stride)
            .ok_or(DualityError::TooManyElements(count))?;
        Ok(Self {
            stride,
            words: vec![0_u64; size],
        })
    }

    /// Row `at` as a set of cells, or the empty set past the rows.
    ///
    /// # Specification
    /// trivial.
    fn view(
        &self,
        at: Element,
    ) -> CellRow<'_>
    {
        let start = usize::from(at).saturating_mul(self.stride);
        CellRow {
            words: self
                .words
                .get(start .. start.saturating_add(self.stride))
                .unwrap_or_default(),
            without: None,
        }
    }

    /// Set the first `width` bits of row `at`, and clear the rest.
    ///
    /// # Specification
    /// trivial.
    fn fill(
        &mut self,
        at: Element,
        width: ElementCount,
    )
    {
        let start = usize::from(at).saturating_mul(self.stride);
        let last = Place::of(Element::from(usize::from(width)));
        let Some(row) = self
            .words
            .get_mut(start .. start.saturating_add(self.stride))
        else {
            return;
        };
        for (word, into) in row.iter_mut().enumerate() {
            *into = match word.cmp(&last.word) {
                core::cmp::Ordering::Less => u64::MAX,
                core::cmp::Ordering::Equal => last.bit.wrapping_sub(1),
                core::cmp::Ordering::Greater => 0,
            };
        }
    }

    /// Meet row `at` with row `row` of `other`, a word at a time.
    ///
    /// # Specification
    /// trivial.
    fn meet(
        &mut self,
        at: Element,
        other: &Self,
        row: Element,
    )
    {
        let start = usize::from(at).saturating_mul(self.stride);
        let from = usize::from(row).saturating_mul(other.stride);
        let (Some(into), Some(from)) = (
            self.words
                .get_mut(start .. start.saturating_add(self.stride)),
            other.words.get(from .. from.saturating_add(other.stride)),
        )
        else {
            return;
        };
        for (into, &from) in into.iter_mut().zip(from) {
            *into &= from;
        }
    }

    /// Rows `left` and `right` compared word by word.
    ///
    /// # Specification
    /// trivial.
    fn order(
        &self,
        left: Element,
        right: Element,
    ) -> core::cmp::Ordering
    {
        self.view(left).words.cmp(self.view(right).words)
    }

    /// Set the bit for `index` in row `at`.
    ///
    /// # Specification
    /// trivial.
    fn put(
        &mut self,
        at: Element,
        index: Element,
    )
    {
        let place = Place::of(index);
        let word = usize::from(at)
            .saturating_mul(self.stride)
            .saturating_add(place.word);
        if place.word < self.stride
            && let Some(word) = self.words.get_mut(word)
        {
            *word |= place.bit;
        }
    }

    /// Clear the bit for `index` in row `at`.
    ///
    /// # Specification
    /// trivial.
    fn clear(
        &mut self,
        at: Element,
        index: Element,
    )
    {
        let place = Place::of(index);
        let word = usize::from(at)
            .saturating_mul(self.stride)
            .saturating_add(place.word);
        if place.word < self.stride
            && let Some(word) = self.words.get_mut(word)
        {
            *word &= !place.bit;
        }
    }

    /// Whether row `at` sets the bit for `index`.
    ///
    /// # Specification
    /// trivial.
    fn holds(
        &self,
        at: Element,
        index: Element,
    ) -> Membership
    {
        self.view(at).sets(index)
    }
}

/// The order of a graded poset: each cell's closure as a row of words, the
/// rows in cell order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellOrder
{
    /// The number of cells.
    count: ElementCount,
    /// Each cell's closure, one bit for each cell.
    rows: Rows,
}

impl CellOrder
{
    /// The order on `cells` that the pairs `below` puts below close to.
    ///
    /// # Specification
    /// - ensures: each cell's row holds the cell and each cell that a chain of
    ///   pairs `below` puts below it, and nothing else.
    /// - fails: two distinct cells that the closure puts each below the other
    ///   are refused by the least such pair, as [`FinitePoset::new`] refuses
    ///   them; rows past the address space are refused by the count.
    /// - panics: none.
    /// - intension: `below` is called once for each ordered pair of distinct
    ///   cells, in the order of the one-word build. The closure takes one pass
    ///   over the rows for each cell, a word at a time, and allocates nothing
    ///   past the rows.
    ///
    /// # Errors
    /// - [`DualityError::Cycle`]: two distinct cells lie each below the other.
    /// - [`DualityError::TooManyElements`]: the rows' words overflow `usize`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — random orders on 65 and 130 cells, against a naive
    ///   closure, separate a lost pair, a bit in the wrong word and a missed
    ///   cycle; L3 — two equal faces separate the least pair.
    /// - witness: `tests::wide::a_wide_poset_answers_as_its_naive_closure`
    /// - witness: `tests::wide::a_wide_cycle_is_refused_by_its_least_pair`
    /// - witness: `tests::graded::two_cells_each_below_the_other_are_refused`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref order) => order.count == ElementCount::from(cells.len()),
        Err(error) => matches!(error, DualityError::Cycle(..) | DualityError::TooManyElements(_)),
    })]
    pub fn new<Cell, Below>(
        cells: &[Cell],
        mut below: Below,
    ) -> Result<Self, DualityError>
    where
        Below: FnMut(&Cell, &Cell) -> Comparison,
    {
        let count = ElementCount::from(cells.len());
        let mut rows = Rows::new(count, count)?;
        let stride = rows.stride;
        if stride != 0 {
            for (cell, row) in rows.words.chunks_exact_mut(stride).enumerate() {
                let place = Place::of(Element::from(cell));
                if let Some(word) = row.get_mut(place.word) {
                    *word |= place.bit;
                }
            }
            for (lower, lower_cell) in cells.iter().enumerate() {
                let place = Place::of(Element::from(lower));
                for (upper, (upper_cell, row)) in cells
                    .iter()
                    .zip(rows.words.chunks_exact_mut(stride))
                    .enumerate()
                {
                    if lower != upper
                        && below(lower_cell, upper_cell) == Comparison::Below
                        && let Some(word) = row.get_mut(place.word)
                    {
                        *word |= place.bit;
                    }
                }
            }
        }
        let mut order = Self { count, rows };
        order.close();
        order.acyclic()?;
        Ok(order)
    }

    /// The order on `cells` by inclusion of the `points` points each holds.
    ///
    /// # Specification
    /// - ensures: each cell's row holds the cell and each cell whose points it
    ///   holds and that differs from it in a point, and nothing else.
    /// - fails: rows past the address space are refused by the count.
    /// - panics: none.
    /// - intension: `holds` is called once for each cell and point, and no pair
    ///   of cells is compared. A cell's row starts as every cell and meets the
    ///   row of the cells that lack each point the cell lacks, a word at a
    ///   time. The cells that hold the same points are found by one sort of
    ///   their points and set apart.
    ///
    /// # Errors
    /// - [`DualityError::TooManyElements`]: the rows' words overflow `usize`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — random sets of points on 6, 65 and 130 cells, over 4,
    ///   8 and 70 points and with repeated sets, against the order that strict
    ///   inclusion of the pairs gives, separate a lost pair, a bit in the wrong
    ///   word and two equal sets read as a cycle.
    /// - witness: `tests::wide::an_inclusion_order_is_the_order_its_pairs_give`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |order| order.count == ElementCount::from(cells.len())))]
    pub fn by_inclusion<Cell, Holds>(
        cells: &[Cell],
        points: ElementCount,
        mut holds: Holds,
    ) -> Result<Self, DualityError>
    where
        Holds: FnMut(&Cell, Element) -> Membership,
    {
        let count = ElementCount::from(cells.len());
        // Each cell's points, and for each point the cells that lack it.
        let mut held = Rows::new(count, points)?;
        let mut lacking = Rows::new(points, count)?;
        for (cell, data) in cells.iter().enumerate() {
            let cell = Element::from(cell);
            for point in (0 .. usize::from(points)).map(Element::from) {
                match holds(data, point) {
                    Membership::Inside => held.put(cell, point),
                    Membership::Outside => lacking.put(point, cell),
                }
            }
        }
        let mut rows = Rows::new(count, count)?;
        for cell in (0 .. cells.len()).map(Element::from) {
            rows.fill(cell, count);
            for point in (0 .. usize::from(points)).map(Element::from) {
                if held.holds(cell, point) == Membership::Outside {
                    rows.meet(cell, &lacking, point);
                }
            }
        }
        // Cells that hold the same points hold each other; set them apart.
        let mut by_points: Vec<Element> = (0 .. cells.len()).map(Element::from).collect();
        by_points.sort_unstable_by(|&left, &right| held.order(left, right).then(left.cmp(&right)));
        for same in by_points
            .chunk_by(|&left, &right| held.order(left, right) == core::cmp::Ordering::Equal)
        {
            for &cell in same {
                for &other in same {
                    if other != cell {
                        rows.clear(cell, other);
                    }
                }
            }
        }
        Ok(Self { count, rows })
    }

    /// Close the rows under the order: Warshall's closure, with each pivot's
    /// row joined into each other row that holds the pivot.
    ///
    /// # Specification
    /// trivial.
    fn close(&mut self)
    {
        let stride = self.rows.stride;
        if stride == 0 {
            return;
        }
        for pivot in (0 .. usize::from(self.count)).map(Element::from) {
            let place = Place::of(pivot);
            let start = usize::from(pivot).saturating_mul(stride);
            let Some((before, rest)) = self.rows.words.split_at_mut_checked(start)
            else {
                break;
            };
            let Some((through, after)) = rest.split_at_mut_checked(stride)
            else {
                break;
            };
            for row in before
                .chunks_exact_mut(stride)
                .chain(after.chunks_exact_mut(stride))
            {
                if row
                    .get(place.word)
                    .is_some_and(|&held| held & place.bit != 0)
                {
                    for (into, &from) in row.iter_mut().zip(through.iter()) {
                        *into |= from;
                    }
                }
            }
        }
    }

    /// Refuse a closed order that puts two distinct cells each below the
    /// other, naming the least such pair as [`FinitePoset::new`] names it.
    ///
    /// # Specification
    /// trivial.
    fn acyclic(&self) -> Result<(), DualityError>
    {
        for upper in (0 .. usize::from(self.count)).map(Element::from) {
            for lower in self.row(upper)?.elements() {
                if lower >= upper {
                    break;
                }
                if self.rows.holds(lower, upper) == Membership::Inside {
                    return Err(DualityError::Cycle(lower, upper));
                }
            }
        }
        Ok(())
    }

    /// The number of cells.
    ///
    /// # Specification
    /// trivial.
    pub const fn count(&self) -> ElementCount
    {
        self.count
    }

    /// The closure of `cell`: its row.
    ///
    /// # Specification
    /// trivial.
    pub fn row(
        &self,
        cell: Element,
    ) -> Result<CellRow<'_>, DualityError>
    {
        if usize::from(cell) >= usize::from(self.count) {
            return Err(DualityError::ElementOutside(cell));
        }
        Ok(self.rows.view(cell))
    }

    /// The order as finite Stone duality's one-word poset.
    ///
    /// # Specification
    /// trivial.
    pub fn narrow(&self) -> Result<FinitePoset, DualityError>
    {
        let mut relation = Vec::new();
        for upper in (0 .. usize::from(self.count)).map(Element::from) {
            for lower in self.row(upper)?.elements() {
                if lower != upper {
                    relation.push((lower, upper));
                }
            }
        }
        FinitePoset::new(self.count, &relation)
    }
}

/// A set of cells of a graded poset, read off its order: a cell's closure, or
/// its boundary. Bit `i mod 64` of word `⌊i / 64⌋` stands for the cell `i`.
///
/// # Specification
/// - ensures: the row holds the cells whose bits are set, less the cell a
///   boundary leaves out.
/// - provides: membership, the cells in order, their count, and the meet with a
///   set of the first 64 cells.
/// - panics: none.
/// - executable: none — a view of the order's words; each method states what it
///   reads.
///
/// # Adequacy
/// - hypothesis: L2 — random orders on 65 and 130 cells, against a naive
///   closure, separate a cell read from the wrong word and a boundary that
///   keeps its own cell.
/// - witness: `tests::wide::a_wide_poset_answers_as_its_naive_closure`
#[derive(Clone, Copy, Debug)]
pub struct CellRow<'poset>
{
    /// The row's words.
    words: &'poset [u64],
    /// The cell the row leaves out: a boundary's own cell.
    without: Option<Element>,
}

impl<'poset> CellRow<'poset>
{
    /// The row without `cell`: the boundary of the cell whose closure it is.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn without(
        self,
        cell: Element,
    ) -> Self
    {
        Self {
            words: self.words,
            without: Some(cell),
        }
    }

    /// Whether the row's words set the bit of `cell`, whatever it leaves out.
    ///
    /// # Specification
    /// trivial.
    fn sets(
        self,
        cell: Element,
    ) -> Membership
    {
        let place = Place::of(cell);
        if self
            .words
            .get(place.word)
            .is_some_and(|&word| word & place.bit != 0)
        {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether the row holds `cell`.
    ///
    /// # Specification
    /// - ensures: [`Membership::Inside`] exactly for a cell whose bit is set
    ///   and that the row does not leave out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`CellRow`].
    /// - witness: `tests::wide::a_wide_poset_answers_as_its_naive_closure`
    #[spec(ensures: |ref ret| self.without != Some(cell) || *ret == Membership::Outside)]
    #[must_use]
    #[inline]
    pub fn contains(
        self,
        cell: Element,
    ) -> Membership
    {
        if self.without == Some(cell) {
            Membership::Outside
        }
        else {
            self.sets(cell)
        }
    }

    /// The cells of the row, in increasing order.
    ///
    /// # Specification
    /// - ensures: exactly the cells that [`CellRow::contains`] holds, each
    ///   once, in increasing order.
    /// - panics: none.
    /// - executable: none — the cells come as a lazy iterator, and a predicate
    ///   over them would consume it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`CellRow`].
    /// - witness: `tests::wide::a_wide_poset_answers_as_its_naive_closure`
    #[inline]
    pub fn elements(self) -> impl Iterator<Item = Element> + 'poset
    {
        let without = self.without;
        self.words
            .iter()
            .enumerate()
            .flat_map(|(at, &word)| Bits {
                rest: word,
                base: at.saturating_mul(WORD),
            })
            .filter(move |&cell| without != Some(cell))
    }

    /// The number of cells the row holds.
    ///
    /// # Specification
    /// - ensures: the number of cells [`CellRow::elements`] gives, at most the
    ///   row's bits.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`CellRow`].
    /// - witness: `tests::wide::a_wide_poset_answers_as_its_naive_closure`
    #[spec(ensures: |ref ret| usize::from(*ret) <= self.words.len().saturating_mul(WORD))]
    #[must_use]
    #[inline]
    pub fn count(self) -> ElementCount
    {
        let set: usize = self
            .words
            .iter()
            .map(|word| usize::try_from(word.count_ones()).unwrap_or_default())
            .sum();
        let left_out = self
            .without
            .filter(|&cell| self.sets(cell) == Membership::Inside)
            .map_or(0, |_cell| 1);
        ElementCount::from(set.saturating_sub(left_out))
    }

    /// The cells of the row that `set` holds, `set` a set of the first 64
    /// cells.
    ///
    /// # Specification
    /// - ensures: the cells below 64 that both the row and `set` hold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two edges between the same two points overlap at two
    ///   least cells, which the sheaf reads through this meet, and a meet that
    ///   keeps a boundary's own cell would lose them.
    /// - witness: `tests::sheaf::an_overlap_with_two_least_cells_compares_at_each`
    #[spec(ensures: |ref ret| ret.elements().all(|cell| set.contains(cell) == Membership::Inside
        && self.contains(cell) == Membership::Inside))]
    #[must_use]
    #[inline]
    pub fn meet(
        self,
        set: ElementSet,
    ) -> ElementSet
    {
        let first = self.words.first().copied().unwrap_or_default();
        let left_out = self
            .without
            .map(Place::of)
            .filter(|place| place.word == 0)
            .map_or(0, |place| place.bit);
        ElementSet::from(first & u64::from(set) & !left_out)
    }
}

/// The set bits of one word of a row, as cells, in increasing order.
struct Bits
{
    /// The bits not yet read.
    rest: u64,
    /// The cell of the word's lowest bit.
    base: usize,
}

impl Iterator for Bits
{
    type Item = Element;

    /// The next set bit's cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Element>
    {
        if self.rest == 0 {
            return None;
        }
        let low = usize::try_from(self.rest.trailing_zeros()).unwrap_or_default();
        self.rest &= self.rest.wrapping_sub(1);
        Some(Element::from(self.base.saturating_add(low)))
    }
}
