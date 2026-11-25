//! A matching on a list of cells, and the matching read as a scheme over a
//! complex.
//!
//! The greedy search builds a matching on a finite complex, and a caller
//! states a matching pair by pair. A Tietze move is a stated matching of one
//! pair. [`Matched`] reads a matching over any complex. It gives the class
//! that the matching states, and it reads every other question from the
//! complex: whether a cell lies in it, the faces of a cell, whether a face can
//! pair with a cell, and the composites when the complex states them.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;

use crate::collapse::Class;
use crate::collapse::Scheme;
use crate::complex::Complex;
use crate::complex::Incidence;
use crate::complex::Invertibility;
use crate::complex::Standing;
use crate::equivalence::Closure;
use crate::equivalence::Composites;
use crate::equivalence::Definition;
use crate::equivalence::Images;
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
    /// The matching that gives each of `cells` the class at its place in
    /// `classes`, with `places` the place of each cell: the greedy search's
    /// answer.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn listed(
        cells: Vec<Cell>,
        classes: Vec<Class<Cell>>,
        places: BTreeMap<Cell, Place>,
    ) -> Self
    {
        Self {
            cells,
            classes,
            places,
        }
    }

    /// The matching that `pairs` states: each redundant cell with its partner
    /// one dimension up. The list holds each cell that a pair names, in the
    /// order of its first pair, and every other cell is critical.
    ///
    /// A Tietze move is a stated matching of one pair: the move removes a
    /// generator with the relation that defines it. Nothing trusts a stated
    /// matching: [`collapse()`](crate::collapse()) checks it on its complex.
    ///
    /// # Specification
    /// - ensures: the list holds each cell that a pair names once. A cell that
    ///   two pairs name keeps the class that the last of them gives.
    /// - panics: none.
    /// - intension: O(p log p) for `p` pairs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an edge that two pairs name, first as a partner and
    ///   then as a redundant cell, keeps the second class, and the check finds
    ///   the first redundant cell unpaired.
    /// - witness: `tests::matching::a_cell_that_two_stated_pairs_name_keeps_the_last_class`
    #[spec(ensures: |ret| ret.classes.len() == ret.cells.len() && ret.places.len() == ret.cells.len())]
    #[inline]
    #[must_use]
    pub fn stated<Pairs>(pairs: Pairs) -> Self
    where
        Pairs: IntoIterator<Item = (Cell, Cell)>,
    {
        let mut matching = Self {
            cells: Vec::new(),
            classes: Vec::new(),
            places: BTreeMap::new(),
        };
        for (redundant, partner) in pairs {
            matching.state(redundant.clone(), Class::Redundant(partner.clone()));
            matching.state(partner, Class::Collapsible(redundant));
        }
        matching
    }

    /// Give `cell` the class `class`: in its place when the list holds it, or
    /// at the end of the list.
    ///
    /// # Specification
    /// trivial.
    fn state(
        &mut self,
        cell: Cell,
        class: Class<Cell>,
    )
    {
        if let Some(&place) = self.places.get(&cell) {
            if let Some(slot) = self.classes.get_mut(usize::from(place)) {
                *slot = class;
            }
            return;
        }
        let _fresh = self
            .places
            .insert(cell.clone(), Place::from(self.cells.len()));
        self.cells.push(cell);
        self.classes.push(class);
    }

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

/// A matching read as a scheme over its complex. The matching gives the class
/// of each cell, and the complex answers every other question.
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

    /// Whether the complex lets `face` pair with `cell`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pairing(
        &mut self,
        face: &Self::Cell,
        cell: &Self::Cell,
        incidence: Incidence,
    ) -> Result<Invertibility, Self::Fault>
    {
        self.complex.pairing(face, cell, incidence)
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

impl<C> Composites for Matched<'_, C>
where
    C: Composites,
{
    type Composite = C::Composite;
    type Witness = C::Witness;

    /// The composite of `cell` alone in the complex.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Self::Composite, Self::Fault>
    {
        self.complex.generator(cell)
    }

    /// The identity on `composite` in the complex.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn identity(
        &mut self,
        composite: &Self::Composite,
    ) -> Result<Self::Composite, Self::Fault>
    {
        self.complex.identity(composite)
    }

    /// Push each cell of `composite` onto `cells`, as the complex reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generators(
        &mut self,
        composite: &Self::Composite,
        cells: &mut Vec<Self::Cell>,
    ) -> Result<(), Self::Fault>
    {
        self.complex.generators(composite, cells)
    }

    /// `composite` with the images in place, as the complex substitutes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn substitute(
        &mut self,
        composite: &Self::Composite,
        images: &Images<'_, Self::Cell, Self::Composite>,
    ) -> Result<Self::Composite, Self::Fault>
    {
        self.complex.substitute(composite, images)
    }

    /// `witness` carried along the images, as the complex carries it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carry(
        &mut self,
        witness: &Self::Witness,
        images: &Images<'_, Self::Cell, Self::Composite>,
    ) -> Result<Self::Witness, Self::Fault>
    {
        self.complex.carry(witness, images)
    }

    /// The vertical composite of `first` and then `second` in the complex.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Result<Self::Witness, Self::Fault>
    {
        self.complex.compose(first, second)
    }

    /// The witness at `composite` that the complex whiskers from `witnesses`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn whisker(
        &mut self,
        composite: &Self::Composite,
        witnesses: &Images<'_, Self::Cell, Self::Witness>,
    ) -> Result<Option<Self::Witness>, Self::Fault>
    {
        self.complex.whisker(composite, witnesses)
    }

    /// The complex's definition of `redundant` by `partner`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn definition(
        &mut self,
        redundant: &Self::Cell,
        partner: &Self::Cell,
    ) -> Result<Definition<Self::Composite, Self::Witness>, Self::Fault>
    {
        self.complex.definition(redundant, partner)
    }

    /// Whether `witness` runs from `source` to `target` in the complex.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn replays(
        &mut self,
        witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Result<Closure, Self::Fault>
    {
        self.complex.replays(witness, source, target)
    }

    /// The complex's inclusion of the critical cell `cell`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn conjugate(
        &mut self,
        cell: &Self::Cell,
        witnesses: &Images<'_, Self::Cell, Self::Witness>,
    ) -> Result<Self::Composite, Self::Fault>
    {
        self.complex.conjugate(cell, witnesses)
    }
}
