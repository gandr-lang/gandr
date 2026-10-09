//! The cell store: structurally deduplicated, insertion-addressed oriented
//! 2-cells over a [`CellAlphabet`], each with its derived metadata.
//!
//! A [`Cell`] is an oriented rewrite `lhs ~> rhs` between two command
//! patterns of the alphabet `A`, with an orientation tag (`A::Orientation`:
//! how the direction was fixed), a provenance tag (`A::Provenance`: where the
//! cell came from), and metadata (`A::Meta`) derived from the two faces at
//! construction by [`CellAlphabet::derive_meta`], never declared.
//!
//! The store ([`CellStore`]) deduplicates on structural identity — [`Eq`] over
//! the whole cell — and hands out dense [`CellId`]s in insertion order, so
//! iteration is deterministic. A [`CellId`] is an indexed-store identity:
//! cloning a store or appending to it preserves every id, while rebuilding
//! the same cells in another order does not. Deduplication reads no address,
//! generation or session state, and that still does not make a [`CellId`] a
//! portable content address: a persistence or transport format must never
//! serialize one, and carries the cell's content instead, resolved back to a
//! local id by content lookup.

use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::alphabet::CellAlphabet;
use crate::boundary::CellCount;
use crate::boundary::CellStoreEmptyStatus;
use crate::sequent::SequentAlphabet;

/// An oriented 2-cell over the alphabet `A`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Cell<A: CellAlphabet = SequentAlphabet>
{
    /// The left-hand side, the redex pattern.
    lhs: A::Cmd,
    /// The right-hand side, the contractum pattern.
    rhs: A::Cmd,
    /// How the orientation was fixed.
    orient: A::Orientation,
    /// Where the cell came from.
    provenance: A::Provenance,
    /// The metadata derived from the two faces.
    meta: A::Meta,
}

impl<A: CellAlphabet> Cell<A>
{
    /// A cell from its two faces, orientation and provenance; the metadata is
    /// derived from both faces, its invertibility read from the provenance.
    ///
    /// # Specification
    /// - ensures: the cell's metadata is `A::derive_meta(&lhs, &rhs,
    ///   A::completion_certificate(&provenance))`, and no accessor can change
    ///   it afterwards.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sequent cells at every provenance retain both faces
    ///   and tags. Exact metadata observations separate certificate provenance
    ///   from ordinary cells and distinguish lost faces or incorrect counts.
    /// - witness: `sequent::tests::completion_cells_are_invertible_certificates`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output.meta == A::derive_meta(
        &output.lhs, &output.rhs, A::completion_certificate(&output.provenance)
    ))]
    pub fn new(
        lhs: A::Cmd,
        rhs: A::Cmd,
        orient: A::Orientation,
        provenance: A::Provenance,
    ) -> Self
    {
        let invertible = A::completion_certificate(&provenance);
        let meta = A::derive_meta(&lhs, &rhs, invertible);
        Self {
            lhs,
            rhs,
            orient,
            provenance,
            meta,
        }
    }

    /// The left-hand side, the redex pattern.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lhs(&self) -> &A::Cmd
    {
        &self.lhs
    }

    /// The right-hand side, the contractum pattern.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rhs(&self) -> &A::Cmd
    {
        &self.rhs
    }

    /// How the orientation was fixed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn orient(&self) -> A::Orientation
    {
        self.orient
    }

    /// Where the cell came from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn provenance(&self) -> A::Provenance
    {
        self.provenance
    }

    /// The metadata derived from the two faces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn meta(&self) -> &A::Meta
    {
        &self.meta
    }
}

/// A dense cell identifier: an insertion-order index into one [`CellStore`].
///
/// An identifier is tied to the store that issued it: clones and append-only
/// extensions keep the assignment, a permutation may bind it to a different
/// cell, and no format carries one across a process boundary.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellId(usize);

impl From<usize> for CellId
{
    /// Wraps the primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<CellId> for usize
{
    /// Unwraps the primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: CellId) -> Self
    {
        value.0
    }
}

quenchant_shape::reason_enum! {
    /// Why a store holds no cell under an identifier.
    pub mod cell_lookup {
        /// The reason the lookup finds nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// This store never issued the identifier.
            Unissued,
        }
    }
}

/// A structurally deduplicated, insertion-ordered collection of cells.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CellStore<A: CellAlphabet = SequentAlphabet>
{
    /// The cells in insertion order; the index is the [`CellId`].
    cells: Vec<Cell<A>>,
}

impl<A: CellAlphabet> CellStore<A>
{
    /// An empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self { cells: Vec::new() }
    }

    /// Inserts a cell, deduplicating on structural identity, and returns its
    /// identifier.
    ///
    /// # Specification
    /// - ensures: a cell structurally equal to one already present — same
    ///   faces, orientation, provenance and metadata — returns that cell's
    ///   identifier and leaves the store as it was; any other cell is appended
    ///   under the next identifier.
    /// - panics: none.
    /// - intension: `economy:` a linear scan per insertion; a content index
    ///   replaces it once a store's size is measured to matter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty store, a duplicate and cells differing in
    ///   each identity component separate reuse from append. Exact identifiers,
    ///   contents and counts reject false equality, overwriting and
    ///   duplication.
    /// - witness: `sequent::tests::the_store_dedups_on_structural_identity`
    #[inline]
    #[spec(
        captures: [
            entry_count = self.cells.len(),
            entry_id = self.cells.iter().position(|held| *held == cell),
        ],
        ensures: |output| output.0 == entry_id.unwrap_or(entry_count)
            && self.cells.len() == entry_count.saturating_add(usize::from(entry_id.is_none())),
    )]
    pub fn insert(
        &mut self,
        cell: Cell<A>,
    ) -> CellId
    {
        if let Some(index) = self.cells.iter().position(|existing| *existing == cell) {
            return CellId(index);
        }
        let id = CellId(self.cells.len());
        self.cells.push(cell);
        id
    }

    /// The cell under `id`.
    ///
    /// # Specification
    /// - ensures: the cell [`CellStore::insert`] returned `id` for.
    /// - provides: [`cell_lookup::Absent::Unissued`] for an identifier this
    ///   store never issued.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and populated stores are observed at issued
    ///   identifiers, the next identifier and `usize::MAX`. Exact cell values
    ///   and absence reasons reject shifted lookup and a weakened bound.
    /// - witness: `sequent::tests::the_store_dedups_on_structural_identity`
    #[inline]
    #[spec(ensures: |output| match output {
        Maybe::Present(cell) => self.cells.iter().enumerate()
            .any(|(index, held)| index == id.0 && held == cell),
        Maybe::Absent(_) => id.0 >= self.cells.len(),
    })]
    pub fn get(
        &self,
        id: CellId,
    ) -> Maybe<&Cell<A>, cell_lookup::Absent>
    {
        match self.cells.get(id.0) {
            | Some(cell) => Maybe::Present(cell),
            | None => Maybe::Absent(cell_lookup::Absent::Unissued),
        }
    }

    /// The number of cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> CellCount
    {
        CellCount::from(self.cells.len())
    }

    /// Whether the store holds no cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> CellStoreEmptyStatus
    {
        CellStoreEmptyStatus::from(self.cells.is_empty())
    }

    /// The cells with their identifiers, in insertion order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (CellId, &Cell<A>)>
    {
        self.cells
            .iter()
            .enumerate()
            .map(|(index, cell)| (CellId(index), cell))
    }
}
