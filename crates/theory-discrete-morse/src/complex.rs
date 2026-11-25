//! The complex that a matching pairs the cells of: the caller's cells, the
//! faces of each cell, and the incidence of each face.

use alloc::vec::Vec;

use anodized::spec;

wrapper! {
    /// The incidence of a face in the boundary of a cell: the integer with
    /// which the boundary counts the face.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Incidence(i64);
}

/// Whether an incidence is a unit of the integers.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Invertibility
{
    /// The incidence is one or minus one, so a matching can pair the face
    /// with its cell.
    Invertible,
    /// The incidence is another integer, so no matching pairs the face with
    /// its cell.
    NotInvertible,
}

impl Incidence
{
    /// Whether the incidence is one or minus one.
    ///
    /// # Specification
    /// - ensures: [`Invertibility::Invertible`] exactly for one and minus one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one, minus one, zero and two separate the two units
    ///   from the other integers.
    /// - witness: `tests::complex::only_one_and_minus_one_are_invertible`
    #[spec(ensures: |ret| (ret == Invertibility::Invertible) == (self.0 == 1_i64 || self.0 == -1_i64))]
    #[inline]
    #[must_use]
    pub fn invertibility(self) -> Invertibility
    {
        if self.0 == 1_i64 || self.0 == -1_i64 {
            Invertibility::Invertible
        }
        else {
            Invertibility::NotInvertible
        }
    }

    /// The sum of two incidences, or nothing past the 64-bit integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn plus(
        self,
        other: Self,
    ) -> Option<Self>
    {
        match self.0.checked_add(other.0) {
            Some(sum) => Some(Self(sum)),
            None => None,
        }
    }

    /// The product of two incidences, or nothing past the 64-bit integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn times(
        self,
        other: Self,
    ) -> Option<Self>
    {
        match self.0.checked_mul(other.0) {
            Some(product) => Some(Self(product)),
            None => None,
        }
    }

    /// The negated incidence, or nothing past the 64-bit integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn negated(self) -> Option<Self>
    {
        match self.0.checked_neg() {
            Some(negated) => Some(Self(negated)),
            None => None,
        }
    }
}

/// Whether a cell lies in a complex.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Standing
{
    /// The cell lies in the complex.
    Inside,
    /// The cell type holds the value, and the complex does not: a degenerate
    /// tuple, or an index past the count.
    Outside,
}

/// A cell complex as a matching reads it: the caller's cells, the faces of
/// each cell one dimension down, and the incidence of each face.
///
/// The trait names no storage, so a caller adapts whatever it holds. A bar
/// complex can build its cells as it reads them, and a graded poset reads its
/// bit rows.
pub trait Complex
{
    /// A cell of the complex.
    type Cell: Clone + Ord;

    /// Why the complex cannot answer, such as a budget it runs out of.
    type Fault;

    /// Whether `cell` lies in the complex.
    ///
    /// # Specification
    /// - provides: [`Standing::Inside`] for a cell of the complex, and
    ///   [`Standing::Outside`] for each other value of the cell type.
    /// - fails: with the caller's fault, when the complex cannot decide.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot decide.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the poset's last cell and the cell at its count
    ///   separate the two standings. The witness covers the poset in this
    ///   crate, not each implementation outside it.
    /// - witness: `tests::poset::a_cell_past_the_count_lies_outside_the_poset`
    fn standing(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Standing, Self::Fault>;

    /// Push each face of `cell` onto `faces`, with its incidence.
    ///
    /// # Specification
    /// - requires: `cell` lies in the complex.
    /// - ensures: each face of `cell` is pushed once, after the entries that
    ///   `faces` held before. A face lies one dimension below `cell`.
    /// - fails: with the caller's fault, when the complex cannot read the
    ///   faces.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot read the faces.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a square's sides and its whole cell separate a face
    ///   one rank down from a cell lower still. The witness covers the poset in
    ///   this crate, not each implementation outside it.
    /// - witness: `tests::poset::the_faces_of_a_cell_lie_one_rank_down`
    fn faces(
        &mut self,
        cell: &Self::Cell,
        faces: &mut Vec<(Self::Cell, Incidence)>,
    ) -> Result<(), Self::Fault>;

    /// Whether `face` can pair with `cell`, where `incidence` is the
    /// incidence of `face` in the boundary of `cell`.
    ///
    /// A pair removes the face, and the cell defines it from its other faces.
    /// Over the integers, a unit incidence is enough. A complex whose cells
    /// compose in context asks more: the face occurs once, with no context. An
    /// occurrence under a context has the incidence one and defines nothing.
    ///
    /// # Specification
    /// - requires: `face` is a face of `cell`.
    /// - ensures: the default answers [`Incidence::invertibility`] of
    ///   `incidence`. A complex that states its own condition answers
    ///   [`Invertibility::NotInvertible`] for each pair outside it.
    /// - fails: with the caller's fault, when the complex cannot decide.
    /// - panics: none.
    /// - executable: none — an implementation replaces the condition; the
    ///   default is one call of [`Incidence::invertibility`].
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot decide.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an incidence of two pairs no cells under the default.
    ///   A complex that refuses an occurrence under a context refuses its pair,
    ///   although the incidence is one.
    /// - witness: `tests::collapse::an_incidence_of_two_pairs_no_cells`
    /// - witness: `tests::equivalence::a_pair_under_a_context_is_refused_at_the_incidence_one`
    #[inline]
    fn pairing(
        &mut self,
        face: &Self::Cell,
        cell: &Self::Cell,
        incidence: Incidence,
    ) -> Result<Invertibility, Self::Fault>
    {
        let _ = (face, cell);
        Ok(incidence.invertibility())
    }
}
