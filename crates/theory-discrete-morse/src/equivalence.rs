//! The equivalence of a complex with its reduct, on the complex's own
//! composites: the collapse, the inclusion, and a witness for each inverse
//! law.
//!
//! An acyclic matching removes each redundant cell with its partner. The
//! partner defines the redundant cell. Its other faces make a composite in
//! the cell's place, with their context, and the partner is a witness from
//! the cell to that composite. The collapse `φ` puts each definition in the
//! place of its cell, in gradient order, and sends each partner to an
//! identity. The inclusion `ι` sends a critical cell to its own composite,
//! conjugated by the witnesses of its removed faces. So `φ ∘ ι` is the
//! identity on the critical cells. The witnesses take each removed cell to
//! `ι ∘ φ` of it.
//!
//! The composites and the witnesses are the complex's own: paths and squares
//! for a graph, whiskered terms and their cells for a polygraph. A composite
//! lives in the free (n,1)-category on the cells, never in a group of chains.
//! Integer chains are one instance, the abelianisation, and
//! [`Abelian`](crate::Abelian) reads any scheme so. An equivalence on its
//! complex is a [`Reduction`], so two collapses compose in
//! sequence.
//!
//! # References
//!
//! - `Doré-2023-computing_spaces_type_theory` — exemplar: §§ 3.5–3.6 send a
//!   vertex to its sink, a matched edge to the identity path and an unmatched
//!   edge to the edge between the sinks. The inclusion sends that edge to the
//!   composite of the inverse gradient path, the edge and the other gradient
//!   path, and both inverse proofs are squares. [`Equivalence`] is that pair of
//!   maps, generic in the complex.
//! - `Ara-2025-polygraphs_rewriting_higher_categories` — dependency: § 7.4.6
//!   replaces a collapsible cell by a composite in the free (n,1)-category,
//!   with its context. §§ 7.5.4–7.5.6 ask well-founded relations of a
//!   collapsible part, and choose a cell that occurs once with no whiskers.
//!   [`Composites::definition`] is the replacement, and [`Complex::pairing`] is
//!   the choice.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::collapse::Budget;
use crate::collapse::Count;
use crate::collapse::Faults;
use crate::collapse::Scheme;
use crate::collapse::collapse;
use crate::complex::Complex;
use crate::error::MorseError;
use crate::gradient::Mark;
use crate::gradient::Place;
use crate::reduction::Answer;
use crate::reduction::Reduction;

/// Whether a witness closes: its boundary runs from the one composite to the
/// other.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Closure
{
    /// The witness runs from the source to the target.
    Closes,
    /// The witness runs elsewhere.
    Open,
}

/// The definition of a redundant cell by its partner: the composite that
/// takes the cell's place, and the witness from the cell to it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition<Composite, Witness>
{
    /// The composite of the partner's other faces, in their context.
    pub replacement: Composite,
    /// The partner read as a cell from the redundant cell to the
    /// replacement.
    pub witness: Witness,
}

/// Which cell of a removal a slot holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side
{
    /// The redundant cell, or a critical cell in the images of an inclusion.
    Redundant,
    /// Its partner one dimension up.
    Partner,
}

/// Where a removed cell stands: the place of its removal, and its side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot
{
    /// The place of the removal in gradient order, or of the critical cell.
    place: Place,
    /// Which cell of the removal it is.
    side: Side,
}

/// The images that a substitution reads: each mapped cell with what takes its
/// place. A cell with no image stands for itself.
#[derive(Debug)]
pub struct Images<'images, Cell, Image>
{
    /// The slot of each mapped cell.
    slots: &'images BTreeMap<Cell, Slot>,
    /// The image of each redundant or critical cell, by its place.
    redundant: &'images [Image],
    /// The image of each partner, by the place of its removal.
    partners: &'images [Image],
}

impl<'images, Cell, Image> Images<'images, Cell, Image>
where
    Cell: Ord,
{
    /// The image of `cell`, or nothing where the cell stands for itself.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(
        &self,
        cell: &Cell,
    ) -> Option<&'images Image>
    {
        let slot = self.slots.get(cell)?;
        let images = match slot.side {
            Side::Redundant => self.redundant,
            Side::Partner => self.partners,
        };
        images.get(usize::from(slot.place))
    }
}

/// A scheme whose cells compose: the free (n,1)-category on its cells, as the
/// complex holds it, with the cells between composites one dimension up.
pub trait Composites: Scheme
{
    /// A composite of cells: a path in a graph, or a whiskered term in a
    /// polygraph.
    type Composite: Clone + Eq;

    /// A cell between two composites: a path between two vertices, a square,
    /// a filler or a 4-cell.
    type Witness: Clone;

    /// The composite of `cell` alone.
    ///
    /// # Specification
    /// - requires: `cell` lies in the complex.
    /// - provides: the generator that `cell` names, with its own boundary.
    /// - fails: with the complex's fault, when it cannot read the cell.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot read the cell.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the graph `two` gives each vertex its identity path
    ///   and each edge its one-step path. The witness covers the complexes in
    ///   this crate's suite, not each implementation outside it.
    /// - witness: `tests::equivalence::the_graph_two_collapses_onto_one_vertex_and_one_loop`
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Self::Composite, Self::Fault>;

    /// The identity one dimension up on `composite`: the image of a partner,
    /// whose redundant cell takes the place `composite` gives it.
    ///
    /// # Specification
    /// - provides: the identity cell on `composite`, as a composite.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot build the identity.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the matched edge of `two` goes to the identity path
    ///   at its sink. The witness covers the complexes in this crate's suite.
    /// - witness: `tests::equivalence::the_graph_two_collapses_onto_one_vertex_and_one_loop`
    fn identity(
        &mut self,
        composite: &Self::Composite,
    ) -> Result<Self::Composite, Self::Fault>;

    /// Push each cell that occurs in `composite` onto `cells`, its context
    /// included.
    ///
    /// # Specification
    /// - ensures: each cell that occurs in `composite` is pushed at least once,
    ///   after the entries that `cells` held before.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot read the composite.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition that names its own cell is refused as a
    ///   cycle, which reads the cells of the replacement.
    /// - witness: `tests::equivalence::a_definition_through_its_own_cell_is_circular`
    fn generators(
        &mut self,
        composite: &Self::Composite,
        cells: &mut Vec<Self::Cell>,
    ) -> Result<(), Self::Fault>;

    /// `composite` with each cell that `images` maps replaced by its image, in
    /// its context.
    ///
    /// # Specification
    /// - ensures: a composite with no cell that `images` maps comes back
    ///   unchanged.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot put an image in its place.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — through the abelianisation, the collapse of each
    ///   critical boundary is the Morse boundary of the reduct, so a lost image
    ///   or a wrong sign changes a face.
    /// - witness: `tests::equivalence::the_abelianisation_gives_the_morse_boundary_of_the_reduct`
    fn substitute(
        &mut self,
        composite: &Self::Composite,
        images: &Images<'_, Self::Cell, Self::Composite>,
    ) -> Result<Self::Composite, Self::Fault>;

    /// `witness` with each cell that `images` maps replaced by its image, in
    /// its context: a witness carried along a collapse or an inclusion.
    ///
    /// # Specification
    /// - ensures: a witness with no cell that `images` maps comes back
    ///   unchanged.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot put an image in its place.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witness of the second collapse of the triangle,
    ///   carried by the first inclusion, runs from `c` to `a` in the triangle.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    fn carry(
        &mut self,
        witness: &Self::Witness,
        images: &Images<'_, Self::Cell, Self::Composite>,
    ) -> Result<Self::Witness, Self::Fault>;

    /// The vertical composite of `first` and then `second`.
    ///
    /// # Specification
    /// - requires: `second` starts where `first` ends.
    /// - provides: one witness from the start of `first` to the end of
    ///   `second`.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot compose the witnesses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witness of `b` in the composed collapse of the
    ///   triangle runs to `a`, and the composite replays.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Result<Self::Witness, Self::Fault>;

    /// The witness at `composite` that `witnesses` gives at its cells, or
    /// nothing where no cell of `composite` has one.
    ///
    /// # Specification
    /// - provides: a witness from `composite` to the composite with each cell
    ///   that has a witness carried to that witness's end.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot whisker the witnesses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witness of `false` in `two` is the path to its
    ///   sink, which the loop's inclusion reads.
    /// - witness: `tests::equivalence::the_graph_two_collapses_onto_one_vertex_and_one_loop`
    fn whisker(
        &mut self,
        composite: &Self::Composite,
        witnesses: &Images<'_, Self::Cell, Self::Witness>,
    ) -> Result<Option<Self::Witness>, Self::Fault>;

    /// The definition of `redundant` by `partner`: the composite of the
    /// partner's other faces in the cell's place, and the partner read as a
    /// witness.
    ///
    /// The definition is a search, and nothing trusts it: the replay checks
    /// its witness.
    ///
    /// # Specification
    /// - requires: the scheme pairs `redundant` with `partner`.
    /// - provides: a replacement, and a witness that should run from the
    ///   redundant cell to it.
    /// - fails: with the complex's fault, when the partner defines nothing.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the partner defines no replacement.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the edge `false → true` of `two` defines `false` as
    ///   `true`, and a search that gives another witness is refused at replay.
    /// - witness: `tests::equivalence::a_forged_witness_is_refused_by_name`
    fn definition(
        &mut self,
        redundant: &Self::Cell,
        partner: &Self::Cell,
    ) -> Result<Definition<Self::Composite, Self::Witness>, Self::Fault>;

    /// Whether `witness` runs from `source` to `target`.
    ///
    /// # Specification
    /// - provides: [`Closure::Closes`] when the boundary of `witness` runs from
    ///   `source` to `target`, and [`Closure::Open`] otherwise.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot read the witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witness of `two` closes, and a path that stops at
    ///   `false` does not.
    /// - witness: `tests::equivalence::a_forged_witness_is_refused_by_name`
    fn replays(
        &mut self,
        witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Result<Closure, Self::Fault>;

    /// The inclusion of the critical cell `cell`: its own composite,
    /// conjugated by the witnesses of its removed faces, which `witnesses`
    /// gives.
    ///
    /// # Specification
    /// - provides: a composite of the complex whose boundary is the inclusion
    ///   of the collapsed boundary of `cell`.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the complex cannot compose the conjugate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the inclusion of the loop of `two` is the composite
    ///   of its two edges, a loop at `true`.
    /// - witness: `tests::equivalence::the_graph_two_collapses_onto_one_vertex_and_one_loop`
    fn conjugate(
        &mut self,
        cell: &Self::Cell,
        witnesses: &Images<'_, Self::Cell, Self::Witness>,
    ) -> Result<Self::Composite, Self::Fault>;
}

/// One removal of an acyclic matching: a redundant cell, its partner, and the
/// definition of the cell by the partner.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Removal<Cell, Composite, Witness>
{
    /// The redundant cell.
    redundant: Cell,
    /// Its partner one dimension up.
    partner: Cell,
    /// The definition of the redundant cell by the partner.
    definition: Definition<Composite, Witness>,
}

impl<Cell, Composite, Witness> Removal<Cell, Composite, Witness>
{
    /// The redundant cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn redundant(&self) -> &Cell
    {
        &self.redundant
    }

    /// The partner one dimension up.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn partner(&self) -> &Cell
    {
        &self.partner
    }

    /// The definition of the redundant cell by the partner.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn definition(&self) -> &Definition<Composite, Witness>
    {
        &self.definition
    }
}

/// The equivalence of a complex with its reduct along an acyclic matching,
/// on the complex's composites.
///
/// The value holds no complex, so a caller keeps it, and reads it on its
/// complex through [`Equivalence::on`]. The critical cells are the cells that
/// `ι` includes. The removals run in gradient order: the replacement of each
/// removal holds no removed cell of a later one.
///
/// # Specification
/// - ensures: the slots name each removed cell once, and each slot's place is a
///   removal.
/// - provides: the critical cells and the removals in gradient order.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`equivalence`]'s,
///   which makes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Equivalence<Cell, Composite, Witness>
{
    /// The given cells that the matching keeps critical, in the given order.
    critical: Vec<Cell>,
    /// The removals in gradient order.
    removals: Vec<Removal<Cell, Composite, Witness>>,
    /// The slot of each removed cell.
    slots: BTreeMap<Cell, Slot>,
}

/// The collapse `φ` of an equivalence: the image of each removed cell.
#[derive(Debug)]
struct Projection<'equivalence, Cell, Composite>
{
    /// The slot of each removed cell.
    slots: &'equivalence BTreeMap<Cell, Slot>,
    /// The image of each redundant cell, by the place of its removal.
    redundant: Vec<Composite>,
    /// The image of each partner, by the place of its removal.
    partners: Vec<Composite>,
}

impl<Cell, Composite> Projection<'_, Cell, Composite>
where
    Cell: Ord,
{
    /// The images, as a substitution reads them.
    ///
    /// # Specification
    /// trivial.
    fn images(&self) -> Images<'_, Cell, Composite>
    {
        Images {
            slots: self.slots,
            redundant: &self.redundant,
            partners: &self.partners,
        }
    }
}

/// The witnesses of `ι ∘ φ` of an equivalence, one at each redundant cell.
#[derive(Debug)]
struct Sections<'equivalence, Cell, Witness>
{
    /// The slot of each removed cell.
    slots: &'equivalence BTreeMap<Cell, Slot>,
    /// The witness of each redundant cell, by the place of its removal.
    witnesses: Vec<Witness>,
}

impl<Cell, Witness> Sections<'_, Cell, Witness>
where
    Cell: Ord,
{
    /// The witnesses, as a whiskering reads them: one for each redundant
    /// cell, and none for a partner.
    ///
    /// # Specification
    /// trivial.
    fn images(&self) -> Images<'_, Cell, Witness>
    {
        Images {
            slots: self.slots,
            redundant: &self.witnesses,
            partners: &[],
        }
    }
}

impl<Cell, Composite, Witness> Equivalence<Cell, Composite, Witness>
where
    Cell: Clone + Ord,
    Composite: Clone + Eq,
    Witness: Clone,
{
    /// The given cells that the matching keeps critical, in the given order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn critical(&self) -> &[Cell]
    {
        &self.critical
    }

    /// The removals in gradient order: each replacement holds no removed cell
    /// of a later removal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn removals(&self) -> &[Removal<Cell, Composite, Witness>]
    {
        &self.removals
    }

    /// `φ` of each removed cell, built once in gradient order.
    ///
    /// The image of a redundant cell is its replacement, with each removed
    /// cell inside it replaced by its own image. The image of a partner is the
    /// identity on the image of its redundant cell.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot substitute or build an
    ///   identity.
    fn projection<S>(
        &self,
        scheme: &mut S,
    ) -> Result<Projection<'_, Cell, Composite>, Refusal<Cell, S::Fault>>
    where
        S: Composites<Cell = Cell, Composite = Composite, Witness = Witness>,
    {
        let mut redundant = Vec::with_capacity(self.removals.len());
        let mut partners = Vec::with_capacity(self.removals.len());
        for removal in &self.removals {
            let images = Images {
                slots: &self.slots,
                redundant: &redundant,
                partners: &partners,
            };
            let image = scheme
                .substitute(&removal.definition.replacement, &images)
                .map_err(MorseError::Complex)?;
            let identity = scheme.identity(&image).map_err(MorseError::Complex)?;
            redundant.push(image);
            partners.push(identity);
        }
        Ok(Projection {
            slots: &self.slots,
            redundant,
            partners,
        })
    }

    /// The witness of `ι ∘ φ` at each redundant cell, built once in gradient
    /// order: its own witness, then the witnesses of the removed cells in its
    /// replacement, whiskered.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot whisker or compose a witness.
    fn sections<S>(
        &self,
        scheme: &mut S,
    ) -> Result<Sections<'_, Cell, Witness>, Refusal<Cell, S::Fault>>
    where
        S: Composites<Cell = Cell, Composite = Composite, Witness = Witness>,
    {
        let mut witnesses = Vec::with_capacity(self.removals.len());
        for removal in &self.removals {
            let images = Images {
                slots: &self.slots,
                redundant: &witnesses,
                partners: &[],
            };
            let onward = scheme
                .whisker(&removal.definition.replacement, &images)
                .map_err(MorseError::Complex)?;
            let witness = match onward {
                Some(ref onward) => scheme
                    .compose(&removal.definition.witness, onward)
                    .map_err(MorseError::Complex)?,
                None => removal.definition.witness.clone(),
            };
            witnesses.push(witness);
        }
        Ok(Sections {
            slots: &self.slots,
            witnesses,
        })
    }

    /// The equivalence read on `scheme`, the complex it was built on, as a
    /// [`Reduction`] from the complex of `cells` to its critical cells.
    ///
    /// The read builds `φ` of each removed cell, the witness of `ι ∘ φ` at
    /// each redundant cell, and `ι` of each critical cell, each once.
    ///
    /// # Specification
    /// - requires: `scheme` and `cells` are the complex and the cells that the
    ///   equivalence was built on.
    /// - ensures: one image for each removed cell, one witness for each
    ///   redundant cell and one inclusion for each critical cell.
    /// - fails: the complex's own fault comes back as [`Refusal::Morse`].
    /// - panics: none.
    /// - intension: one substitution, one identity and one whiskering for each
    ///   removal, and one conjugation for each critical cell, each reading only
    ///   what the read built before it.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot substitute, build an identity,
    ///   whisker, compose or conjugate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `false` in `two` goes to the identity path at `true`,
    ///   and the inclusion of the loop is the composite of the two edges. L2 —
    ///   through the abelianisation, each critical boundary collapses to the
    ///   Morse boundary.
    /// - witness: `tests::equivalence::the_graph_two_collapses_onto_one_vertex_and_one_loop`
    /// - witness: `tests::equivalence::the_abelianisation_gives_the_morse_boundary_of_the_reduct`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |bound| bound.included.len() == self.critical.len()))]
    #[inline]
    pub fn on<'bound, S>(
        &'bound self,
        scheme: &'bound mut S,
        cells: &'bound [Cell],
        budget: Budget,
    ) -> Result<Bound<'bound, S>, Refusal<Cell, S::Fault>>
    where
        S: Composites<Cell = Cell, Composite = Composite, Witness = Witness>,
    {
        let projection = self.projection(scheme)?;
        let sections = self.sections(scheme)?;
        let mut included = Vec::with_capacity(self.critical.len());
        let mut critical = BTreeMap::new();
        for (at, cell) in self.critical.iter().enumerate() {
            included.push(
                scheme
                    .conjugate(cell, &sections.images())
                    .map_err(MorseError::Complex)?,
            );
            let _first = critical.insert(cell.clone(), Slot {
                place: Place::from(at),
                side: Side::Redundant,
            });
        }
        Ok(Bound {
            equivalence: self,
            scheme,
            cells,
            budget,
            projection,
            sections,
            critical,
            included,
        })
    }

    /// Check the equivalence against `scheme` on `cells`: the matching, each
    /// witness, the gradient order, and the round trip `φ ∘ ι`.
    ///
    /// The replay runs [`collapse`](crate::collapse()) and refuses any fault.
    /// The removals must be the pairs that its walk reaches, and the critical
    /// cells its critical cells. Each witness must run from its redundant cell
    /// to its replacement. Each replacement holds no removed cell of a later
    /// removal. The image of each redundant cell holds no removed cell. `φ`
    /// after `ι` gives each critical cell's own composite in the reduct back.
    ///
    /// # Specification
    /// - requires: `cells` lists the cells the equivalence was built on.
    /// - ensures: `Ok` exactly when every check holds.
    /// - fails: the first check that fails comes back by name: a cycle, an
    ///   unpaired cell, a partner outside the complex, a pair outside the
    ///   complex's condition, a removal the matching does not hold, a forged
    ///   witness, a replacement out of gradient order, an image that holds a
    ///   removed cell, or a critical cell that `φ ∘ ι` moves. The complex's own
    ///   fault and a walk past `budget` come back as [`Refusal::Morse`].
    /// - panics: none.
    /// - executable: none — the body is the predicate.
    /// - intension: one collapse check, then one witness replay, one read of a
    ///   replacement's cells and one substitution for each removal, and one
    ///   conjugation and two substitutions for each critical cell.
    ///
    /// # Errors
    /// - [`Refusal::Cycle`], [`Refusal::Unpaired`], [`Refusal::Outside`],
    ///   [`Refusal::Unpairable`]: the matching is no acyclic matching.
    /// - [`Refusal::Unmatched`]: the equivalence and the matching differ.
    /// - [`Refusal::Forged`]: a witness does not close.
    /// - [`Refusal::Circular`]: a replacement holds a later removed cell.
    /// - [`Refusal::Unclosed`]: an image holds a removed cell.
    /// - [`Refusal::Unretracted`]: `φ ∘ ι` moves a critical cell.
    /// - [`Refusal::Morse`]: the complex's fault, or a walk past `budget`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the equivalence of `two` replays, and a forged
    ///   witness is refused by name. The abelianisation of each test complex
    ///   replays, and so does each collapse of the triangle composed.
    /// - witness: `tests::equivalence::the_graph_two_collapses_onto_one_vertex_and_one_loop`
    /// - witness: `tests::equivalence::a_forged_witness_is_refused_by_name`
    /// - witness: `tests::equivalence::the_abelianisation_gives_the_morse_boundary_of_the_reduct`
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    #[inline]
    pub fn replay<'cells, Cells, S>(
        &self,
        scheme: &mut S,
        cells: Cells,
        budget: Budget,
    ) -> Result<(), Refusal<Cell, S::Fault>>
    where
        S: Composites<Cell = Cell, Composite = Composite, Witness = Witness>,
        Cell: 'cells,
        Cells: IntoIterator<Item = &'cells Cell>,
    {
        let checked = collapse(scheme, cells, budget)?;
        refuse(checked.faults())?;
        matched(checked.critical(), &self.critical)?;
        if checked.pairs().len() != self.removals.len() {
            let missing = checked
                .pairs()
                .iter()
                .map(|&(ref redundant, _)| redundant)
                .find(|redundant| !self.slots.contains_key(*redundant))
                .or_else(|| self.removals.first().map(|removal| &removal.redundant));
            return Err(Refusal::Unmatched(missing.cloned()));
        }
        for &(ref redundant, ref partner) in checked.pairs() {
            let held = self
                .slots
                .get(redundant)
                .filter(|slot| slot.side == Side::Redundant)
                .and_then(|slot| self.removals.get(usize::from(slot.place)))
                .is_some_and(|removal| removal.partner == *partner);
            if !held {
                return Err(Refusal::Unmatched(Some(redundant.clone())));
            }
        }
        let mut cells = Vec::new();
        for (at, removal) in self.removals.iter().enumerate() {
            let source = scheme
                .generator(&removal.redundant)
                .map_err(MorseError::Complex)?;
            let closure = scheme
                .replays(
                    &removal.definition.witness,
                    &source,
                    &removal.definition.replacement,
                )
                .map_err(MorseError::Complex)?;
            if closure == Closure::Open {
                return Err(Refusal::Forged(removal.redundant.clone()));
            }
            cells.clear();
            scheme
                .generators(&removal.definition.replacement, &mut cells)
                .map_err(MorseError::Complex)?;
            for cell in &cells {
                if let Some(slot) = self.slots.get(cell)
                    && usize::from(slot.place) >= at
                {
                    return Err(Refusal::Circular(removal.redundant.clone()));
                }
            }
        }
        let projection = self.projection(scheme)?;
        for (removal, image) in self.removals.iter().zip(&projection.redundant) {
            cells.clear();
            scheme
                .generators(image, &mut cells)
                .map_err(MorseError::Complex)?;
            for cell in &cells {
                if self.slots.contains_key(cell) {
                    return Err(Refusal::Unclosed(removal.redundant.clone()));
                }
            }
        }
        let sections = self.sections(scheme)?;
        for cell in &self.critical {
            let included = scheme
                .conjugate(cell, &sections.images())
                .map_err(MorseError::Complex)?;
            let back = scheme
                .substitute(&included, &projection.images())
                .map_err(MorseError::Complex)?;
            let generator = scheme.generator(cell).map_err(MorseError::Complex)?;
            let own = scheme
                .substitute(&generator, &projection.images())
                .map_err(MorseError::Complex)?;
            if back != own {
                return Err(Refusal::Unretracted(cell.clone()));
            }
        }
        Ok(())
    }
}

/// Nothing when two lists of cells are equal, or [`Refusal::Unmatched`] at
/// the cell of the first place where they differ.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - [`Refusal::Unmatched`]: the lists differ, at the cell named, or in their
///   length alone.
pub fn matched<Cell, Fault>(
    found: &[Cell],
    held: &[Cell],
) -> Result<(), Refusal<Cell, Fault>>
where
    Cell: Clone + Eq,
{
    if found == held {
        return Ok(());
    }
    let at = found
        .iter()
        .zip(held)
        .position(|(found, held)| found != held)
        .unwrap_or_else(|| found.len().min(held.len()));
    Err(Refusal::Unmatched(
        found.get(at).or_else(|| held.get(at)).cloned(),
    ))
}

/// An equivalence read on the complex it was built on: a [`Reduction`] from
/// the complex of its cells to its critical cells.
#[derive(Debug)]
pub struct Bound<'bound, S>
where
    S: Composites,
{
    /// The equivalence read.
    equivalence: &'bound Equivalence<S::Cell, S::Composite, S::Witness>,
    /// The complex it was built on.
    scheme: &'bound mut S,
    /// The cells it was built on.
    cells: &'bound [S::Cell],
    /// The budget of the walk that its replay runs.
    budget: Budget,
    /// `φ` of each removed cell.
    projection: Projection<'bound, S::Cell, S::Composite>,
    /// The witness of `ι ∘ φ` at each redundant cell.
    sections: Sections<'bound, S::Cell, S::Witness>,
    /// The place of each critical cell in `included`.
    critical: BTreeMap<S::Cell, Slot>,
    /// `ι` of each critical cell, by its place among the critical cells.
    included: Vec<S::Composite>,
}

impl<S> Reduction for Bound<'_, S>
where
    S: Composites,
{
    type Cell = S::Cell;
    type Composite = S::Composite;
    type Fault = S::Fault;
    type Witness = S::Witness;

    /// The cells the equivalence was built on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> &[Self::Cell]
    {
        self.cells
    }

    /// The critical cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn target(&self) -> &[Self::Cell]
    {
        &self.equivalence.critical
    }

    /// The complex's composite of `cell`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Answer<Self, Self::Composite>
    {
        Ok(self.scheme.generator(cell).map_err(MorseError::Complex)?)
    }

    /// Each removed cell of `composite` replaced by its image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        Ok(self
            .scheme
            .substitute(composite, &self.projection.images())
            .map_err(MorseError::Complex)?)
    }

    /// Each critical cell of `composite` replaced by its inclusion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        let images = Images {
            slots: &self.critical,
            redundant: &self.included,
            partners: &[],
        };
        Ok(self
            .scheme
            .substitute(composite, &images)
            .map_err(MorseError::Complex)?)
    }

    /// The witnesses of the redundant cells of `composite`, whiskered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn section(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        Ok(self
            .scheme
            .whisker(composite, &self.sections.images())
            .map_err(MorseError::Complex)?)
    }

    /// None: `φ ∘ ι` is the identity by construction.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn retraction(
        &mut self,
        _composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        Ok(None)
    }

    /// `witness` with each critical cell replaced by its inclusion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        let images = Images {
            slots: &self.critical,
            redundant: &self.included,
            partners: &[],
        };
        Ok(self
            .scheme
            .carry(witness, &images)
            .map_err(MorseError::Complex)?)
    }

    /// `witness` with each removed cell replaced by its image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        Ok(self
            .scheme
            .carry(witness, &self.projection.images())
            .map_err(MorseError::Complex)?)
    }

    /// The complex's composite of `first` and then `second`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        Ok(self
            .scheme
            .compose(first, second)
            .map_err(MorseError::Complex)?)
    }

    /// Whether the complex replays `witness` from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn closes(
        &mut self,
        witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Answer<Self, Closure>
    {
        Ok(self
            .scheme
            .replays(witness, source, target)
            .map_err(MorseError::Complex)?)
    }

    /// [`Equivalence::replay`] on the complex and the cells it was built on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn replay(&mut self) -> Answer<Self, ()>
    {
        self.equivalence
            .replay(self.scheme, self.cells, self.budget)
    }
}

/// Why a scheme gives no equivalence, or a reduction does not replay.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refusal<Cell, Fault>
{
    /// The gradient of the matching closes this many cycles.
    Cycle(Count),
    /// This many cells whose partner does not name them back.
    Unpaired(Count),
    /// This many partners that do not lie in the complex.
    Outside(Count),
    /// This many pairs that the complex's pairing condition refuses.
    Unpairable(Count),
    /// The equivalence and the matching, or two composed reductions, differ
    /// at this cell, or in their count alone.
    Unmatched(Option<Cell>),
    /// The witness at this cell does not close.
    Forged(Cell),
    /// The replacement of this redundant cell holds itself or a later removed
    /// cell, so the definitions run in a cycle.
    Circular(Cell),
    /// The image of this redundant cell still holds a removed cell.
    Unclosed(Cell),
    /// `φ` after `ι` moves this critical cell.
    Unretracted(Cell),
    /// The complex's own fault, or a walk past its budget.
    Morse(MorseError<Fault>),
}

impl<Cell, Fault> From<MorseError<Fault>> for Refusal<Cell, Fault>
{
    /// Wraps the collapse's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: MorseError<Fault>) -> Self
    {
        Self::Morse(error)
    }
}

/// The faults of a check as the refusal of the first that is not zero, or
/// nothing for an acyclic matching.
///
/// # Specification
/// trivial.
fn refuse<Cell, Fault>(faults: Faults) -> Result<(), Refusal<Cell, Fault>>
{
    let zero = Count::default();
    if faults.cycles != zero {
        return Err(Refusal::Cycle(faults.cycles));
    }
    if faults.unpaired != zero {
        return Err(Refusal::Unpaired(faults.unpaired));
    }
    if faults.outside != zero {
        return Err(Refusal::Outside(faults.outside));
    }
    if faults.uninvertible != zero {
        return Err(Refusal::Unpairable(faults.uninvertible));
    }
    Ok(())
}

/// The equivalence that the composites of a scheme give.
pub type EquivalenceOf<S> =
    Equivalence<<S as Complex>::Cell, <S as Composites>::Composite, <S as Composites>::Witness>;

/// One removal on the composites of a scheme.
type RemovalOf<S> =
    Removal<<S as Complex>::Cell, <S as Composites>::Composite, <S as Composites>::Witness>;

/// The equivalence of the complex of `cells` with its reduct along the
/// matching that `scheme` gives.
///
/// The build runs [`collapse`](crate::collapse()) and refuses any fault. It
/// reads the definition of each pair that the walk reaches, and puts the
/// removals in gradient order. The definitions are a search: the build trusts
/// none of them, and [`Equivalence::replay`] checks them.
///
/// # Specification
/// - requires: each given cell lies in the complex.
/// - ensures: the critical cells are the given cells that the scheme calls
///   critical, in the given order. One removal for each pair that the walk
///   reaches, each after every removal that its replacement holds a cell of.
/// - fails: a fault of the matching comes back by name. A replacement that
///   holds its own cell, or a cycle of replacements, is refused as
///   [`Refusal::Circular`]. The complex's own fault and a walk past `budget`
///   come back as [`Refusal::Morse`].
/// - panics: none.
/// - intension: one collapse check, one definition and one read of its cells
///   for each pair, and one depth-first search over the removals that reads
///   each removal and each dependency once.
///
/// # Errors
/// - [`Refusal::Cycle`], [`Refusal::Unpaired`], [`Refusal::Outside`],
///   [`Refusal::Unpairable`]: the matching is no acyclic matching.
/// - [`Refusal::Circular`]: the definitions run in a cycle.
/// - [`Refusal::Morse`]: the complex's fault, or a walk past `budget`.
///
/// # Adequacy
/// - hypothesis: L3 — the graph `two` matched at `false` keeps `true` and the
///   edge `true → false`. A matching of both vertices closes a cycle, and a
///   definition through its own cell is circular. A matching with no pair keeps
///   every cell.
/// - witness: `tests::equivalence::the_graph_two_collapses_onto_one_vertex_and_one_loop`
/// - witness: `tests::equivalence::a_matching_with_a_cycle_is_refused_by_name`
/// - witness: `tests::equivalence::a_definition_through_its_own_cell_is_circular`
/// - witness: `tests::equivalence::a_matching_with_no_pair_gives_the_identity`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |done| done.slots.len() <= done.removals.len().saturating_mul(2)))]
#[inline]
pub fn equivalence<'cells, Cells, S>(
    scheme: &mut S,
    cells: Cells,
    budget: Budget,
) -> Result<EquivalenceOf<S>, Refusal<S::Cell, S::Fault>>
where
    S: Composites,
    S::Cell: 'cells,
    Cells: IntoIterator<Item = &'cells S::Cell>,
{
    let checked = collapse(scheme, cells, budget)?;
    refuse(checked.faults())?;
    let (critical, pairs) = checked.into_parts();
    let mut found: Vec<Option<RemovalOf<S>>> = Vec::with_capacity(pairs.len());
    let mut slots: BTreeMap<S::Cell, Slot> = BTreeMap::new();
    for (redundant, partner) in pairs {
        let definition = scheme
            .definition(&redundant, &partner)
            .map_err(MorseError::Complex)?;
        let place = Place::from(found.len());
        let _first = slots.insert(redundant.clone(), Slot {
            place,
            side: Side::Redundant,
        });
        let _first = slots.insert(partner.clone(), Slot {
            place,
            side: Side::Partner,
        });
        found.push(Some(Removal {
            redundant,
            partner,
            definition,
        }));
    }
    let order = gradient_order(scheme, &found, &slots)?;
    let mut removals = Vec::with_capacity(found.len());
    for place in order {
        if let Some(removal) = found.get_mut(usize::from(place)).and_then(Option::take) {
            removals.push(removal);
        }
    }
    for (at, removal) in removals.iter().enumerate() {
        for cell in [&removal.redundant, &removal.partner] {
            if let Some(slot) = slots.get_mut(cell) {
                slot.place = Place::from(at);
            }
        }
    }
    Ok(Equivalence {
        critical,
        removals,
        slots,
    })
}

/// The places of the removals in gradient order: each after every removal
/// whose cell its replacement holds.
///
/// # Specification
/// - requires: `slots` names each removal's cells by the removal's place in
///   `found`.
/// - ensures: each place once, after the places it depends on.
/// - fails: a replacement that holds its own cell, or a cycle of replacements,
///   is refused as [`Refusal::Circular`] at a redundant cell on the cycle.
/// - panics: none.
/// - executable: none — the ensures is a statement about every path of the
///   graph of the definitions, and the call holds no second search to check it
///   against.
/// - intension: one read of each replacement's cells, then one depth-first
///   search with an explicit stack.
///
/// # Errors
/// - [`Refusal::Circular`]: the definitions run in a cycle.
/// - [`Refusal::Morse`]: the complex cannot read a replacement.
///
/// # Adequacy
/// - hypothesis: L3 — a definition through its own cell is refused, and the
///   definitions of each test complex order.
/// - witness: `tests::equivalence::a_definition_through_its_own_cell_is_circular`
/// - witness: `tests::equivalence::the_abelianisation_gives_the_morse_boundary_of_the_reduct`
fn gradient_order<S>(
    scheme: &mut S,
    found: &[Option<RemovalOf<S>>],
    slots: &BTreeMap<S::Cell, Slot>,
) -> Result<Vec<Place>, Refusal<S::Cell, S::Fault>>
where
    S: Composites,
{
    let mut starts: Vec<Count> = Vec::with_capacity(found.len().saturating_add(1));
    let mut below: Vec<Place> = Vec::new();
    let mut cells: Vec<S::Cell> = Vec::new();
    starts.push(Count::default());
    for removal in found.iter().flatten() {
        cells.clear();
        scheme
            .generators(&removal.definition.replacement, &mut cells)
            .map_err(MorseError::Complex)?;
        below.extend(
            cells
                .iter()
                .filter_map(|cell| slots.get(cell))
                .map(|slot| slot.place),
        );
        starts.push(Count::from(below.len()));
    }
    let mut marks = vec![Mark::Unseen; found.len()];
    let mut order = Vec::with_capacity(found.len());
    let mut stack: Vec<(Place, Count)> = Vec::new();
    for start in 0 .. found.len() {
        if marks.get(start) != Some(&Mark::Unseen) {
            continue;
        }
        if let Some(mark) = marks.get_mut(start) {
            *mark = Mark::Open;
        }
        stack.push((Place::from(start), Count::default()));
        while let Some(&mut (node, ref mut next)) = stack.last_mut() {
            let first = starts.get(usize::from(node)).copied().map(usize::from);
            let end = starts
                .get(usize::from(node).saturating_add(1))
                .copied()
                .map(usize::from);
            let target = first
                .zip(end)
                .and_then(|(first, end)| below.get(first .. end))
                .and_then(|targets| targets.get(usize::from(*next)))
                .copied();
            let Some(target) = target
            else {
                if let Some(mark) = marks.get_mut(usize::from(node)) {
                    *mark = Mark::Done;
                }
                order.push(node);
                let _left = stack.pop();
                continue;
            };
            *next = next.one_more();
            match marks.get(usize::from(target)).copied() {
                Some(Mark::Open) => {
                    let cell = found
                        .get(usize::from(target))
                        .and_then(Option::as_ref)
                        .map(|removal| removal.redundant.clone());
                    return Err(Refusal::Unmatched(None).or_circular(cell));
                },
                Some(Mark::Unseen) => {
                    if let Some(mark) = marks.get_mut(usize::from(target)) {
                        *mark = Mark::Open;
                    }
                    stack.push((target, Count::default()));
                },
                Some(Mark::Done) | None => {},
            }
        }
    }
    Ok(order)
}

impl<Cell, Fault> Refusal<Cell, Fault>
{
    /// [`Refusal::Circular`] at `cell`, or this refusal where there is no cell.
    ///
    /// # Specification
    /// trivial.
    fn or_circular(
        self,
        cell: Option<Cell>,
    ) -> Self
    {
        cell.map_or(self, Refusal::Circular)
    }
}
