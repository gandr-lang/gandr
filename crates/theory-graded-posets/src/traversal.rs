//! Kessler's traversal of a molecule, and the key that names a molecule up to
//! isomorphism.
//!
//! A caller orients a graded poset: each face one rank below a cell lies on
//! the input side of the cell or on its output side. A molecule is an oriented
//! graded poset that pasting and atoms build from the point. Isomorphism of
//! oriented graded posets is as hard as graph isomorphism. On a molecule, the
//! traversal marks each cell in an order that only the structure of the poset
//! fixes. The key writes the input and output faces of each cell as places in
//! that order, rank by rank. Two molecules have equal keys exactly when they
//! are isomorphic.
//!
//! The traversal keeps a stack of closed sets. Each set is held by its
//! maximal cells, so the closure rows are never copied. At each step, the set
//! on top is the focus. A focus whose cells are all marked leaves the stack.
//! A focus whose input boundary holds an unmarked cell pushes that boundary.
//! A focus that is the closure of one cell marks the cell, and then pushes its
//! output boundary. Any other focus pushes the closure of one cell: the input
//! coface in the focus of the earliest marked cell one rank below its top.
//!
//! The traversal makes no choice. It refuses a poset at the first step that
//! no molecule reaches, so a key never depends on the numbering of the cells.
//! Equal keys give a bijection that keeps each face and its side, so the two
//! posets are isomorphic.
//!
//! # References
//!
//! - `Kessler-2025-computational_aspects_rewriting_higherdimensional_diagrams`
//!   — dependency: § 2.4.2, Procedure 2.4.8 and Examples 2.4.9 to 2.4.11, the
//!   traversal and its orders. § 2.4.3, Theorem 2.4.21, its bound.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::Membership;

use crate::graded::GradedPoset;
use crate::graded::Rank;
use crate::rows::Union;

/// The side of a cell that a face one rank below it lies on.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Face
{
    /// The face lies on the input side of the cell, as the source of an edge
    /// does.
    Input,
    /// The face lies on the output side of the cell, as the target of an edge
    /// does.
    Output,
}

/// A cell's place among the cells of its rank, in the order that the
/// traversal marks them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Place(usize);

impl From<usize> for Place
{
    /// Wraps a position among the cells of one rank.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Place> for usize
{
    /// Unwraps a position among the cells of one rank.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Place) -> Self
    {
        value.0
    }
}

/// Why the traversal refuses a poset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraversalError
{
    /// The poset is not a molecule, and the traversal stops at this cell: a
    /// cell whose faces one rank below it do not span its boundary, a marked
    /// cell with two input cofaces in the focus, or the first unmarked cell of
    /// a focus that no marked cell enters.
    NotAMolecule(Element),
    /// The graded poset refused to read a cell.
    Poset(DualityError),
}

impl From<DualityError> for TraversalError
{
    /// Wraps the poset's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: DualityError) -> Self
    {
        Self::Poset(error)
    }
}

impl fmt::Display for TraversalError
{
    /// Renders the refusal and the cell it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::NotAMolecule(cell) => write!(
                f,
                "the traversal stops at cell {}: the poset is not a molecule",
                usize::from(cell)
            ),
            Self::Poset(error) => write!(f, "the poset refused: {error}"),
        }
    }
}

impl core::error::Error for TraversalError
{
}

/// The faces one rank below each cell, with their sides, and the input
/// cofaces one rank above each cell.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Hasse
{
    /// Each cell's rank, in cell order.
    ranks: Vec<Rank>,
    /// Where the faces of each cell start in `faces`, and one past the last.
    face_starts: Vec<usize>,
    /// The faces one rank below each cell, with their sides, cell after cell.
    faces: Vec<(Element, Face)>,
    /// Where the input cofaces of each cell start in `input_cofaces`, and one
    /// past the last.
    coface_starts: Vec<usize>,
    /// The cells that hold each cell as an input face, cell after cell.
    input_cofaces: Vec<Element>,
    /// The cells that no cell holds as a face, in cell order.
    maximal: Vec<Element>,
}

impl Hasse
{
    /// The rank of `cell`.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        &self,
        cell: Element,
    ) -> Rank
    {
        self.ranks
            .get(usize::from(cell))
            .copied()
            .unwrap_or_default()
    }

    /// The faces one rank below `cell`, with their sides.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &self,
        cell: Element,
    ) -> &[(Element, Face)]
    {
        let at = usize::from(cell);
        match (
            self.face_starts.get(at),
            self.face_starts.get(at.saturating_add(1)),
        ) {
            (Some(&start), Some(&end)) => self.faces.get(start .. end).unwrap_or_default(),
            (Some(_) | None, _) => &[],
        }
    }

    /// The cells that hold `cell` as an input face.
    ///
    /// # Specification
    /// trivial.
    fn input_cofaces(
        &self,
        cell: Element,
    ) -> &[Element]
    {
        let at = usize::from(cell);
        match (
            self.coface_starts.get(at),
            self.coface_starts.get(at.saturating_add(1)),
        ) {
            (Some(&start), Some(&end)) => self.input_cofaces.get(start .. end).unwrap_or_default(),
            (Some(_) | None, _) => &[],
        }
    }
}

/// The cells of a molecule in the order that the traversal marks them, with
/// the faces of each cell.
///
/// # Specification
/// - ensures: the order holds each cell of the poset once, and each cell's
///   place is its position among the marked cells of its rank.
/// - provides: the order and the key.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`GradedPoset::traverse`]'s, which makes it.
///
/// # Adequacy
/// - hypothesis: L3 — the orders that the thesis prints for its Examples 2.4.10
///   and 2.4.11 separate a step taken out of turn.
/// - witness: `tests::traversal::the_traversal_marks_the_cells_of_examples_2_4_10_and_2_4_11_in_the_printed_order`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Traversal
{
    /// The cells, in the order that the traversal marks them.
    order: Vec<Element>,
    /// The cells of each rank, in the order that the traversal marks them.
    by_rank: Vec<Vec<Element>>,
    /// Each cell's place among the cells of its rank, in cell order.
    places: Vec<Place>,
    /// The faces and cofaces that the traversal reads.
    hasse: Hasse,
}

impl Traversal
{
    /// The cells, in the order that the traversal marks them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn order(&self) -> &[Element]
    {
        &self.order
    }

    /// The key of the molecule: rank by rank, and in traversal order within a
    /// rank, the places of each cell's input faces and of its output faces.
    ///
    /// # Specification
    /// - ensures: one entry for each cell, each list of places in increasing
    ///   order. Two traversals give equal keys exactly when a bijection of
    ///   their cells keeps each face and its side.
    /// - panics: none.
    /// - intension: one pass over the faces, and a sort of each cell's input
    ///   places and of its output places.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the face data that the thesis prints for its Example
    ///   2.4.4, whose names are traversal places, separates a face written by
    ///   its cell and not by its place; the two molecules of its Example 2.4.9,
    ///   which the face counts do not tell apart, separate a key that forgets
    ///   which face a cell holds; a copy numbered in another order separates a
    ///   key read in cell order.
    /// - witness: `tests::traversal::the_key_of_example_2_1_4_is_the_face_data_the_thesis_prints`
    /// - witness: `tests::traversal::the_two_molecules_of_example_2_4_9_have_the_same_face_counts_and_different_keys`
    /// - witness: `tests::traversal::a_molecule_numbered_in_another_order_has_the_same_key`
    #[spec(ensures: |ref ret| ret.ends.len() == self.order.len()
        && ret.counts.iter().sum::<usize>() == self.order.len())]
    #[inline]
    #[must_use]
    pub fn key(&self) -> Key
    {
        let mut counts = Vec::with_capacity(self.by_rank.len());
        let mut ends = Vec::with_capacity(self.order.len());
        let mut places = Vec::with_capacity(self.hasse.faces.len());
        let place = |cell: Element| {
            self.places
                .get(usize::from(cell))
                .copied()
                .unwrap_or_default()
        };
        for cells in &self.by_rank {
            counts.push(cells.len());
            for &cell in cells {
                let faces = self.hasse.faces(cell);
                let start = places.len();
                places.extend(
                    faces
                        .iter()
                        .filter(|&&(_, side)| side == Face::Input)
                        .map(|&(face, _)| place(face)),
                );
                let middle = places.len();
                places.extend(
                    faces
                        .iter()
                        .filter(|&&(_, side)| side == Face::Output)
                        .map(|&(face, _)| place(face)),
                );
                let end = places.len();
                if let Some(inputs) = places.get_mut(start .. middle) {
                    inputs.sort_unstable();
                }
                if let Some(outputs) = places.get_mut(middle .. end) {
                    outputs.sort_unstable();
                }
                ends.push((middle, end));
            }
        }
        Key {
            counts,
            ends,
            places,
        }
    }
}

/// The key of a molecule: the faces of each cell as places in traversal
/// order.
///
/// The key holds, rank by rank and in traversal order within a rank, the
/// places of each cell's input faces and of its output faces. Two molecules
/// have equal keys exactly when they are isomorphic.
///
/// # Specification
/// - ensures: one entry for each cell, and the counts of the ranks sum to the
///   entries.
/// - provides: each cell's rank and the places of its faces.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`Traversal::key`]'s, which makes it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Traversal::key`].
/// - witness: `tests::traversal::the_key_of_example_2_1_4_is_the_face_data_the_thesis_prints`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Key
{
    /// The number of cells of each rank, from rank zero.
    counts: Vec<usize>,
    /// For each cell, where its input places end in `places`, and where its
    /// output places end. Its input places start where the cell before it
    /// ends.
    ends: Vec<(usize, usize)>,
    /// The places of each cell's input faces and of its output faces, each
    /// list in increasing order.
    places: Vec<Place>,
}

impl Key
{
    /// Each cell of the key, rank by rank and in traversal order: its rank,
    /// the places of its input faces and the places of its output faces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn cells(&self) -> impl Iterator<Item = (Rank, &[Place], &[Place])> + '_
    {
        let mut start = 0_usize;
        self.counts
            .iter()
            .enumerate()
            .flat_map(|(rank, &count)| core::iter::repeat_n(Rank::from(rank), count))
            .zip(&self.ends)
            .map(move |(rank, &(middle, end))| {
                let inputs = self.places.get(start .. middle).unwrap_or_default();
                let outputs = self.places.get(middle .. end).unwrap_or_default();
                start = end;
                (rank, inputs, outputs)
            })
    }
}

impl<Cell> GradedPoset<Cell>
{
    /// Kessler's traversal of this poset, each face one rank below a cell on
    /// the side that `orient` gives: it takes the face first and the cell
    /// second.
    ///
    /// # Specification
    /// - ensures: each cell is marked once, in the order of Procedure 2.4.8.
    ///   The order depends only on the faces and their sides, never on the
    ///   numbering of the cells.
    /// - fails: a poset that is not a molecule is refused at the first step
    ///   that no molecule reaches. A cell whose faces one rank below it do not
    ///   span its boundary is refused before the traversal starts. A marked
    ///   cell with two input cofaces in the focus is refused. The first
    ///   unmarked cell is refused where no marked cell enters the focus, and
    ///   where the run ends with a cell unmarked.
    /// - panics: none.
    /// - intension: `orient` is called once for each face. The faces one rank
    ///   below each cell, and the union of their closures a word at a time,
    ///   take one pass over the rows. Marks only grow, so each frame on the
    ///   stack keeps cursors that only move on: its first unmarked maximal
    ///   cell, whether its input boundary is marked, and where the search for
    ///   the next cell goes on. A stamp of a cell stands in place of a set. On
    ///   a molecule each set is pushed at most once (Lemma 2.4.17). On any
    ///   poset the stack only grows between two marks, so the run ends.
    ///
    /// # Errors
    /// - [`TraversalError::NotAMolecule`]: the poset is not a molecule, and the
    ///   traversal stops at the cell it names.
    /// - [`TraversalError::Poset`]: unreachable for a poset that
    ///   [`GradedPoset::new`] makes, since each cell it reads is below the
    ///   count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the orders that the thesis prints for its Examples
    ///   2.4.10 and 2.4.11 separate a step taken out of turn; two parallel
    ///   edges, two points and a cover that skips a rank each separate a
    ///   refusal at the cell where a molecule's traversal goes on.
    /// - witness: `tests::traversal::the_traversal_marks_the_cells_of_examples_2_4_10_and_2_4_11_in_the_printed_order`
    /// - witness: `tests::traversal::a_poset_that_is_not_a_molecule_is_refused_at_the_cell_where_the_traversal_stops`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref traversal) => ElementCount::from(traversal.order().len()) == self.count(),
        Err(error) => matches!(error, TraversalError::NotAMolecule(_) | TraversalError::Poset(_)),
    })]
    #[inline]
    pub fn traverse<Orient>(
        &self,
        mut orient: Orient,
    ) -> Result<Traversal, TraversalError>
    where
        Orient: FnMut(&Cell, &Cell) -> Face,
    {
        let hasse = self.hasse(&mut orient)?;
        self.spanned(&hasse)?;
        let mut walk = Walk::new(&hasse);
        walk.run()?;
        let Walk {
            order,
            by_rank,
            places,
            ..
        } = walk;
        Ok(Traversal {
            order,
            by_rank,
            places,
            hasse,
        })
    }

    /// The faces one rank below each cell, each on the side that `orient`
    /// gives, and the input cofaces and the maximal cells they imply.
    ///
    /// # Specification
    /// trivial.
    fn hasse<Orient>(
        &self,
        orient: &mut Orient,
    ) -> Result<Hasse, DualityError>
    where
        Orient: FnMut(&Cell, &Cell) -> Face,
    {
        let count = usize::from(self.count());
        let mut ranks = Vec::with_capacity(count);
        for cell in (0 .. count).map(Element::from) {
            ranks.push(self.rank(cell)?);
        }
        let mut face_starts = Vec::with_capacity(count.saturating_add(1));
        let mut faces = Vec::new();
        let mut cofaces = vec![0_usize; count];
        let mut inputs = vec![0_usize; count];
        for (at, &rank) in ranks.iter().enumerate() {
            face_starts.push(faces.len());
            let cell = Element::from(at);
            let upper = self
                .cells()
                .get(at)
                .ok_or(DualityError::ElementOutside(cell))?;
            for lower in self.boundary(cell)?.elements() {
                let below = ranks.get(usize::from(lower)).copied().unwrap_or_default();
                if usize::from(below).saturating_add(1) != usize::from(rank) {
                    continue;
                }
                let face = self
                    .cells()
                    .get(usize::from(lower))
                    .ok_or(DualityError::ElementOutside(lower))?;
                let side = orient(face, upper);
                faces.push((lower, side));
                if let Some(slot) = cofaces.get_mut(usize::from(lower)) {
                    *slot = slot.saturating_add(1);
                }
                if side == Face::Input
                    && let Some(slot) = inputs.get_mut(usize::from(lower))
                {
                    *slot = slot.saturating_add(1);
                }
            }
        }
        face_starts.push(faces.len());
        let mut coface_starts = Vec::with_capacity(count.saturating_add(1));
        let mut total = 0_usize;
        for &taken in &inputs {
            coface_starts.push(total);
            total = total.saturating_add(taken);
        }
        coface_starts.push(total);
        let mut next = coface_starts.clone();
        let mut input_cofaces = vec![Element::default(); total];
        for (at, window) in face_starts.windows(2).enumerate() {
            let [start, end] = *window
            else {
                continue;
            };
            for &(face, side) in faces.get(start .. end).unwrap_or_default() {
                if side == Face::Input
                    && let Some(slot) = next.get_mut(usize::from(face))
                {
                    if let Some(entry) = input_cofaces.get_mut(*slot) {
                        *entry = Element::from(at);
                    }
                    *slot = slot.saturating_add(1);
                }
            }
        }
        let maximal = cofaces
            .iter()
            .enumerate()
            .filter(|&(_, &above)| above == 0)
            .map(|(at, _)| Element::from(at))
            .collect();
        Ok(Hasse {
            ranks,
            face_starts,
            faces,
            coface_starts,
            input_cofaces,
            maximal,
        })
    }

    /// Refuses the first cell whose faces one rank below it do not span its
    /// boundary: a cover that skips a rank, which no molecule holds.
    ///
    /// # Specification
    /// trivial.
    fn spanned(
        &self,
        hasse: &Hasse,
    ) -> Result<(), TraversalError>
    {
        let mut union = Union::new(self.count());
        for cell in (0 .. usize::from(self.count())).map(Element::from) {
            union.clear();
            for &(face, _) in hasse.faces(cell) {
                self.closure(face)?.join_into(&mut union);
            }
            if union.count() != self.boundary(cell)?.count() {
                return Err(TraversalError::NotAMolecule(cell));
            }
        }
        Ok(())
    }
}

/// A closed set on the stack of the traversal, held by its maximal cells.
/// Marks only grow, so each cursor of a frame only moves on.
#[derive(Clone, Copy, Debug)]
struct Frame
{
    /// Where its maximal cells start in `members`. They run to the start of
    /// the frame above it, or to the end of `members`.
    start: usize,
    /// The stamp that its top cells hold in `owner`, unless it is the closure
    /// of one cell.
    id: Stamp,
    /// Its top rank.
    top: Rank,
    /// The first of its maximal cells that can be unmarked: each cell before
    /// it is marked.
    unmarked: usize,
    /// Whether its input boundary is marked. A push of the boundary returns
    /// only when the boundary is marked, so the frame computes it once.
    lower: Membership,
    /// Where the search for the next cell goes on, among the marked cells one
    /// rank below its top. A cell that the search passes has no unmarked input
    /// coface in the frame, and it never gets one.
    scan: usize,
}

/// The state of one run of the traversal.
struct Walk<'hasse>
{
    /// The faces and cofaces of the poset.
    hasse: &'hasse Hasse,
    /// Whether the traversal has marked each cell, in cell order.
    marked: Vec<Membership>,
    /// The marked cells, in the order of their marks.
    order: Vec<Element>,
    /// The marked cells of each rank, in the order of their marks.
    by_rank: Vec<Vec<Element>>,
    /// Each marked cell's place among the cells of its rank, in cell order.
    places: Vec<Place>,
    /// The closed sets on the stack, the focus last.
    stack: Vec<Frame>,
    /// The maximal cells of each closed set on the stack, set after set.
    members: Vec<Element>,
    /// The maximal cells of a set that the current step pushes.
    pushed: Vec<Element>,
    /// The stamp of the frame whose top cells hold each cell. Only one frame
    /// of each rank that is not the closure of one cell is on the stack, so
    /// the stamps of two live frames never meet.
    owner: Vec<usize>,
    /// The last stamp at which each cell was an output face of the focus.
    outputs: Vec<usize>,
    /// The last stamp at which each cell was taken into a set.
    taken: Vec<usize>,
    /// The last stamp given out. No cell holds a stamp at first.
    stamp: usize,
}

impl<'hasse> Walk<'hasse>
{
    /// A run over `hasse` with no cell marked and the whole poset on the
    /// stack, held by its maximal cells.
    ///
    /// # Specification
    /// trivial.
    fn new(hasse: &'hasse Hasse) -> Self
    {
        let count = hasse.ranks.len();
        let ranks = hasse
            .ranks
            .iter()
            .map(|&rank| usize::from(rank))
            .max()
            .map_or(0, |top| top.saturating_add(1));
        let mut walk = Self {
            hasse,
            marked: vec![Membership::Outside; count],
            order: Vec::with_capacity(count),
            by_rank: vec![Vec::new(); ranks],
            places: vec![Place::default(); count],
            stack: Vec::new(),
            members: Vec::with_capacity(count),
            pushed: hasse.maximal.clone(),
            owner: vec![0; count],
            outputs: vec![0; count],
            taken: vec![0; count],
            stamp: 0,
        };
        walk.push_pushed();
        walk
    }

    /// Whether `cell` is marked.
    ///
    /// # Specification
    /// trivial.
    fn marked(
        &self,
        cell: Element,
    ) -> Membership
    {
        self.marked
            .get(usize::from(cell))
            .copied()
            .unwrap_or(Membership::Inside)
    }

    /// A fresh stamp, which no cell holds.
    ///
    /// # Specification
    /// trivial.
    fn fresh(&mut self) -> Stamp
    {
        self.stamp = self.stamp.saturating_add(1);
        Stamp(self.stamp)
    }

    /// Runs the traversal until the stack is empty, and refuses a poset where
    /// a cell is left unmarked.
    ///
    /// # Specification
    /// trivial.
    fn run(&mut self) -> Result<(), TraversalError>
    {
        while let Some(&frame) = self.stack.last() {
            let (unmarked, count) = {
                let members = self.members.get(frame.start ..).unwrap_or_default();
                let mut unmarked = frame.unmarked;
                while members
                    .get(unmarked)
                    .is_some_and(|&cell| self.marked(cell) == Membership::Inside)
                {
                    unmarked = unmarked.saturating_add(1);
                }
                (unmarked, members.len())
            };
            if unmarked >= count {
                self.pop();
                continue;
            }
            let frame = Frame { unmarked, ..frame };
            if usize::from(frame.top) > 0 && frame.lower == Membership::Outside {
                let lower = self.input_boundary(frame);
                self.update(Frame {
                    lower: Membership::Inside,
                    ..frame
                });
                if lower == Marked::Unfinished {
                    self.push_pushed();
                    continue;
                }
            }
            else {
                self.update(frame);
            }
            if count == 1 {
                let cell = self.members.get(frame.start).copied().unwrap_or_default();
                self.mark(cell);
                self.pop();
                if self.output_boundary(cell) == Marked::Unfinished {
                    self.push_pushed();
                }
                continue;
            }
            let cell = self.next_atom(frame)?;
            self.pushed.clear();
            self.pushed.push(cell);
            self.push_pushed();
        }
        self.marked
            .iter()
            .position(|&mark| mark == Membership::Outside)
            .map_or(Ok(()), |at| {
                Err(TraversalError::NotAMolecule(Element::from(at)))
            })
    }

    /// Puts the maximal cells of the input boundary of `frame` in `pushed`:
    /// the input faces of its top cells that no top cell holds as an output
    /// face, and its maximal cells below the top. Answers whether each of
    /// them is marked.
    ///
    /// # Specification
    /// trivial.
    fn input_boundary(
        &mut self,
        frame: Frame,
    ) -> Marked
    {
        let Stamp(stamp) = self.fresh();
        let &mut Self {
            hasse,
            ref marked,
            ref members,
            ref mut pushed,
            ref mut outputs,
            ref mut taken,
            ..
        } = self;
        let focus = members.get(frame.start ..).unwrap_or_default();
        pushed.clear();
        let mut every = Marked::Every;
        let mut take = |cell: Element| {
            pushed.push(cell);
            if marked.get(usize::from(cell)) == Some(&Membership::Outside) {
                every = Marked::Unfinished;
            }
        };
        for &cell in focus.iter().filter(|&&cell| hasse.rank(cell) == frame.top) {
            for &(face, side) in hasse.faces(cell) {
                if side == Face::Output
                    && let Some(slot) = outputs.get_mut(usize::from(face))
                {
                    *slot = stamp;
                }
            }
        }
        for &cell in focus {
            if hasse.rank(cell) != frame.top {
                take(cell);
                continue;
            }
            for &(face, side) in hasse.faces(cell) {
                let at = usize::from(face);
                if side == Face::Input
                    && outputs.get(at) != Some(&stamp)
                    && let Some(slot) = taken.get_mut(at)
                    && *slot != stamp
                {
                    *slot = stamp;
                    take(face);
                }
            }
        }
        every
    }

    /// Puts the output faces of `cell` in `pushed`: the maximal cells of its
    /// output boundary. Answers whether each of them is marked.
    ///
    /// # Specification
    /// trivial.
    fn output_boundary(
        &mut self,
        cell: Element,
    ) -> Marked
    {
        let &mut Self {
            hasse,
            ref marked,
            ref mut pushed,
            ..
        } = self;
        pushed.clear();
        let mut every = Marked::Every;
        for &(face, side) in hasse.faces(cell) {
            if side == Face::Output {
                pushed.push(face);
                if marked.get(usize::from(face)) == Some(&Membership::Outside) {
                    every = Marked::Unfinished;
                }
            }
        }
        every
    }

    /// The cell whose closure `frame` pushes: the input coface in the frame
    /// of the earliest marked cell one rank below its top that has an
    /// unmarked one.
    ///
    /// # Specification
    /// trivial.
    fn next_atom(
        &mut self,
        frame: Frame,
    ) -> Result<Element, TraversalError>
    {
        let Stamp(id) = frame.id;
        let mut scan = frame.scan;
        let found = {
            let below = usize::from(frame.top)
                .checked_sub(1)
                .and_then(|rank| self.by_rank.get(rank))
                .map_or_default(Vec::as_slice);
            let mut found = Ok(None);
            while let Some(&face) = below.get(scan) {
                let mut inside = self
                    .hasse
                    .input_cofaces(face)
                    .iter()
                    .copied()
                    .filter(|&coface| self.owner.get(usize::from(coface)) == Some(&id));
                let first = inside.next();
                if inside.next().is_some() {
                    found = Err(TraversalError::NotAMolecule(face));
                    break;
                }
                if let Some(coface) = first
                    && self.marked(coface) == Membership::Outside
                {
                    found = Ok(Some(coface));
                    break;
                }
                scan = scan.saturating_add(1);
            }
            found
        };
        self.update(Frame { scan, ..frame });
        if let Some(cell) = found? {
            return Ok(cell);
        }
        let unmarked = self
            .members
            .get(frame.start.saturating_add(frame.unmarked))
            .copied()
            .unwrap_or_default();
        Err(TraversalError::NotAMolecule(unmarked))
    }

    /// Marks `cell`, last in the order and last among the cells of its rank.
    ///
    /// # Specification
    /// trivial.
    fn mark(
        &mut self,
        cell: Element,
    )
    {
        let at = usize::from(cell);
        if let Some(slot) = self.marked.get_mut(at) {
            *slot = Membership::Inside;
        }
        self.order.push(cell);
        if let Some(cells) = self.by_rank.get_mut(usize::from(self.hasse.rank(cell))) {
            if let Some(slot) = self.places.get_mut(at) {
                *slot = Place(cells.len());
            }
            cells.push(cell);
        }
    }

    /// Pushes the set whose maximal cells `pushed` holds. Its top cells take
    /// the frame's stamp, unless it is the closure of one cell.
    ///
    /// # Specification
    /// trivial.
    fn push_pushed(&mut self)
    {
        let Stamp(id) = self.fresh();
        let top = self
            .pushed
            .iter()
            .map(|&cell| self.hasse.rank(cell))
            .max()
            .unwrap_or_default();
        if self.pushed.len() != 1 {
            for &cell in &self.pushed {
                if self.hasse.rank(cell) == top
                    && let Some(slot) = self.owner.get_mut(usize::from(cell))
                {
                    *slot = id;
                }
            }
        }
        self.stack.push(Frame {
            start: self.members.len(),
            id: Stamp(id),
            top,
            unmarked: 0,
            lower: Membership::Outside,
            scan: 0,
        });
        self.members.extend_from_slice(&self.pushed);
    }

    /// Writes `frame` over the focus.
    ///
    /// # Specification
    /// trivial.
    fn update(
        &mut self,
        frame: Frame,
    )
    {
        if let Some(focus) = self.stack.last_mut() {
            *focus = frame;
        }
    }

    /// Pops the focus.
    ///
    /// # Specification
    /// trivial.
    fn pop(&mut self)
    {
        if let Some(frame) = self.stack.pop() {
            self.members.truncate(frame.start);
        }
    }
}

/// A stamp of one step or of one frame: a cell that holds it belongs to the
/// set that the step builds, or to the top of the frame.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Stamp(usize);

/// Whether each cell of a set that a step builds is marked.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Marked
{
    /// Each cell of the set is marked.
    Every,
    /// Some cell of the set is not marked.
    Unfinished,
}
