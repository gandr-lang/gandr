//! The diagram normal form: when two presentations denote one diagram.
//!
//! # What this module decides
//!
//! A [`Wiring`] is a presentation. Its wires and generators are numbered, and
//! two presentations that differ only in that numbering denote one diagram.
//! The relation is cospan isomorphism over the port bijection: a renumbering of
//! wires and generators that preserves every label, every arity and every
//! ordered port list, and commutes with both legs of the interface position by
//! position. [`canonicalize`] picks one representative of each class, the
//! [`CanonicalDiagram`], and [`same_diagram`] decides the relation by comparing
//! representatives.
//!
//! This is the diagram normal form, a property of the representation. It is
//! not the rewriting normal form, which runs a rule system to completion and is
//! a property of the theory; nothing here rewrites.
//!
//! # The edge orientation
//!
//! A canonical linearization of a diagram can cut it at a vertex — pick a
//! generator, recurse into the pieces its removal leaves, a corolla
//! decomposition — or at an edge — pick a wire, recurse into the two sides its
//! removal leaves. The two are the extremes of one family, with mixed styles
//! between them. This module takes the edge orientation, as a traversal:
//!
//! - **Monogamy makes the edge cut choice-free.** A wire has at most one
//!   producer and at most one consumer, so the two sides of a removed wire are
//!   told apart by direction: step to the producer, then to the consumer.
//!   Removing a generator leaves one piece per port, and sequencing those
//!   pieces needs an order the corolla shape does not supply.
//! - **The order a vertex cut would borrow is the port order**, which the edge
//!   traversal already consumes, so a corolla decomposition would do the edge
//!   orientation's work with an extra vertex choice on top.
//! - **The boundary is a list of wires**, so the anchoring datum an interface
//!   carries is already an edge datum and the traversal seeds on it directly.
//! - **A traversal owes no confluence argument.** A decomposition shape
//!   produced by rewriting toward a normal form must show the rewriting
//!   confluent, and for the cut symmetry it is not. Here a deterministic
//!   traversal produces the form, so there is no rewriting relation: uniqueness
//!   is by construction rather than by convergence.
//!
//! A generator whose ports are not totally ordered would move the choice
//! toward a mixed style, because the edge traversal would then need a
//! tie-break of its own; every generator here orders its ports.
//!
//! # The procedure
//!
//! [`canonicalize`] renumbers a diagram's wires and generators in the one
//! order the traversal admits, and returns the renumbered diagram with the
//! [`Relabelling`] that produced it.
//!
//! 1. **Anchor on the boundary.** Canonical wire numbers `0, 1, 2, …` go to the
//!    declared input ports in order, then to the declared output ports in
//!    order, skipping a wire already numbered. An isomorphism of diagrams with
//!    interface commutes with the legs, so it fixes boundary positions, and
//!    numbering by position is invariant.
//! 2. **Drain.** A cursor walks the numbered wires in canonical order. At each
//!    wire it visits the producer and then the consumer; visiting a generator
//!    takes the next canonical generator number and numbers its unnumbered
//!    ports, sources in port order and then targets in port order. No step
//!    chooses, so the numbering is a function of the diagram and its boundary.
//! 3. **Seed the components the boundary never reaches.** A component with no
//!    boundary port has no anchor, so its seed is chosen inside it: every
//!    member is tried, each trial yields one linearization because the drain is
//!    choice-free, and the least linearization wins. The anchorless components
//!    are then committed in the order of their winning linearizations. Both
//!    choices minimize over the diagram's own content, so both are invariants
//!    of the diagram rather than of its presentation.
//!
//! Both comparisons read the whole linearization. A seed's first record is its
//! own label and arity and nothing else, so two members sharing those tie on
//! it, and a comparison stopping there would fall back on listing position.
//! Ties of the whole linearization happen exactly between isomorphic seeds or
//! isomorphic components, and they are broken by position, so the relabelling
//! is not an invariant of the diagram; the form is, because committing either
//! of two tied candidates first lays down the same records at the same numbers.
//!
//! # A traversal, not a search
//!
//! Graph canonicalization is expensive because at each step it must consider
//! every candidate for the next vertex. Here a generator's image is forced by
//! any one of its wires, so one seed fixes a whole component. A component with
//! a boundary port costs one traversal; an anchorless component of `k`
//! generators costs `k` traversals, `O(k²)` in that component, and no search.
//!
//! # What the procedure rests on
//!
//! Two of [`Wiring::assemble`]'s refusal families are premises here; the third
//! is not.
//!
//! - **Monogamy** ([`WiringObstruction::FanIn`], [`WiringObstruction::FanOut`])
//!   makes the drain choice-free, and makes a [`Wiring`] a faithful index at
//!   all: its incidence maps are single-valued, so a wire with two producers
//!   could only be recorded by losing one, and a canon over a lossy index would
//!   identify diagrams that differ.
//! - **Boundary honesty**, both halves of it.
//!   - _Every open wire is declared_ ([`WiringObstruction::UndeclaredInput`],
//!     [`WiringObstruction::UndeclaredOutput`]), which makes the numbering
//!     total. Every wire is a generator port or an open wire, and an isolated
//!     wire, a port of nothing, is numbered only because both legs must declare
//!     it.
//!   - _A declared port is open_
//!     ([`WiringObstruction::BoundaryInputIsProduced`],
//!     [`WiringObstruction::BoundaryOutputIsConsumed`]), which makes the
//!     drain's producer-before-consumer order unobservable: when the cursor
//!     reaches a wire, at most one of its two sides is still unvisited. A
//!     boundary wire lacks a producer or a consumer, and an interior wire was
//!     numbered while visiting a generator on one of its sides.
//! - **Acyclicity** ([`WiringObstruction::DirectedCycle`]) is not a premise.
//!   The matcher's convexity discharge needs an acyclic target; the traversal
//!   here terminates on its visited sets and is canonical for the same reason
//!   with or without a cycle. No cyclic [`Wiring`] is constructible, so that is
//!   argued rather than tested.
//!
//! # Presentation-order invariance
//!
//! The claim [`canonicalize`] makes is a theorem about every pair of
//! presentations, not a property of the fixtures: if a renumbering `φ` of wires
//! and generators carries a diagram `A` onto a diagram `B`, preserving labels
//! and ordered ports and commuting with both legs, then `A` and `B` have equal
//! forms. Run the two traversals side by side. The boundary step numbers the
//! wire at each leg position, and `φ` sends `A`'s wire there to `B`'s. The
//! drain at the `n`-th numbered wire visits its producer and consumer, which
//! `φ` carries to the producer and consumer of `B`'s `n`-th numbered wire, and
//! numbers ports in an order `φ` preserves. So after every step `B`'s numbering
//! is `A`'s transported along `φ`, and the records agree. On anchorless
//! components `φ` carries each member's trial onto its image's trial with equal
//! records, so the minima, the component order and every tie agree.
//!
//! The converse is the witness: a form is the image of its diagram under the
//! returned [`Relabelling`], which [`Relabelling::verify`] checks is an
//! isomorphism, so two diagrams with one form are isomorphic through it.
//!
//! # Evidence, not an equality shortcut
//!
//! [`same_diagram`] answers with evidence on both arms. Two diagrams that
//! denote one diagram come back as their shared form with both relabellings,
//! the two halves of the isomorphism between them, each checkable by
//! [`Relabelling::verify`]; two that do not come back with the first place
//! their forms part. Nothing leaves this module as a bare verdict a consumer
//! would have to trust.
//!
//! # What this module does not do
//!
//! - **Rewrite.** The rewriting normal form belongs to the engines that run a
//!   rule system to completion; this module decides presentation equality and
//!   stops there.
//! - **Canonicalize construction terms.** A circuit also has a reading as a
//!   term built from merger and contraction, and a canonical form of those
//!   terms is a different object at a different layer. That the two canons
//!   agree is not assumed here, and nothing here establishes it.
//! - **Intern.** A canonical form is a map key — [`CanonicalDiagram`] is
//!   [`Ord`] and [`Hash`], and holds no address, stamp or session state — but
//!   minting identities from it waits until the form is shown to agree with the
//!   construction-term reading.
//! - **Decide fan-in.** The spider normal form for diagrams whose wires combine
//!   is outside the monogamous fragment this view admits.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::interface::ComponentIndex;
use crate::interface::Edge;
use crate::interface::EdgeCount;
use crate::interface::Generator;
use crate::interface::Interface;
use crate::interface::Wire;
use crate::interface::WireCount;
use crate::interface::Wiring;
use crate::interface::WiringObstruction;

wrapper! {
    /// A position in an ordered port list: a generator's sources or targets,
    /// or one leg of an interface.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PortPosition(usize);
}

wrapper! {
    /// How many ports an ordered port list holds.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PortCount(usize);
}

/// Which side of an ordered port list a datum sits on.
///
/// One vocabulary for two uses, because they are one distinction: a
/// generator's sources are the wires it consumes and its targets the wires it
/// produces, and an interface's inputs are the wires the diagram consumes from
/// outside and its outputs the wires it produces to outside.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Leg
{
    /// The consumed side: a generator's sources, or an interface's inputs.
    Input,
    /// The produced side: a generator's targets, or an interface's outputs.
    Output,
}

quenchant_shape::reason_enum! {
    /// Why a relabelling maps a wire nowhere.
    pub mod relabelled_wire {
        /// The reason the lookup finds no image.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The wire is outside the relabelling's domain.
            Unmapped,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a relabelling maps a generator nowhere.
    pub mod relabelled_generator {
        /// The reason the lookup finds no image.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The generator is outside the relabelling's domain.
            Unmapped,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why two canonical forms have no divergence.
    mod form_divergence {
        /// The reason no difference is reported.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The two forms are equal.
            Equal,
        }
    }
}

/// A diagram in its canonical numbering: the normal form.
///
/// A value exists only because [`canonicalize`] produced it, so its numbering
/// is the one the traversal admits, and its derived [`Eq`] is diagram
/// identity: two presentations of one diagram reach equal forms and two
/// different diagrams reach different ones. A [`Wiring`]'s own [`Eq`] is
/// presentation identity. The derived [`Ord`] and [`Hash`] make a form a map
/// key; the order is total and fixed and means nothing beyond that.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CanonicalDiagram
{
    /// How many wires the diagram declares.
    wires: WireCount,
    /// The interface, in canonical wire numbers and declared port order.
    boundary: Interface,
    /// The generator records, in canonical order and canonical wire numbers.
    generators: Box<[Generator]>,
}

impl CanonicalDiagram
{
    /// How many wires the form declares.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wire_count(&self) -> WireCount
    {
        self.wires
    }

    /// How many generators the form holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn edge_count(&self) -> EdgeCount
    {
        EdgeCount::from(self.generators.len())
    }

    /// The interface, in canonical wire numbers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn boundary(&self) -> &Interface
    {
        &self.boundary
    }

    /// The generator records, in canonical order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generators(&self) -> &[Generator]
    {
        &self.generators
    }

    /// Reads the form back as a diagram.
    ///
    /// # Specification
    /// - ensures: a [`Wiring`] whose wire count, generators in order and
    ///   interface are the form's, so canonicalizing it returns this form with
    ///   the identity relabelling.
    /// - provides: the way back from a form to a diagram, so a caller can match
    ///   against a form or check that canonicalization is idempotent.
    /// - fails: [`WiringObstruction`] when the form is outside the fragment. A
    ///   form [`canonicalize`] produced renumbers a diagram
    ///   [`Wiring::assemble`] accepted, and renumbering preserves every
    ///   condition it checks, so no form fails; the signature stays fallible
    ///   because the reassembly runs those checks rather than assuming them.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`WiringObstruction`]: whatever [`Wiring::assemble`] refuses, which no
    ///   form [`canonicalize`] produced reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every fixture's form is read back, reassembled under
    ///   the fragment's checks and canonicalized again, and the second
    ///   canonicalization must return the same form with the identity
    ///   relabelling on wires and on generators, which is the fixed-point law.
    /// - witness: `normal_form::tests::canonicalization_is_idempotent`
    #[spec(ensures: |ref result| result.as_ref().is_ok_and(|wiring| wiring.wire_count() == self.wires && wiring.generators() == &*self.generators && wiring.boundary() == &self.boundary))]
    #[inline]
    pub fn to_wiring(&self) -> Result<Wiring, WiringObstruction>
    {
        Wiring::assemble(self.wires, self.generators.to_vec(), self.boundary.clone())
    }
}

/// A renumbering of one diagram onto a canonical form: the evidence that the
/// form is the diagram's.
///
/// The witness records where each wire and each generator went and claims
/// nothing. Everything that makes it a diagram isomorphism is checked by
/// [`Relabelling::verify`] against the two sides it relates, so the trust sits
/// in the verifier and not in the producer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Relabelling
{
    /// Where each wire of the source diagram went.
    wires: BTreeMap<Wire, Wire>,
    /// Where each generator of the source diagram went.
    generators: BTreeMap<Edge, Edge>,
}

impl Relabelling
{
    /// Where `wire` went.
    ///
    /// # Specification
    /// - provides: [`relabelled_wire::Absent::Unmapped`] when `wire` is not in
    ///   the relabelling's domain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the identity relabelling after canonicalization
    ///   exposes every mapped wire, and a first-past lookup exposes typed
    ///   absence. Returning another image or inventing a missing entry differs;
    ///   lookup does not certify the map.
    /// - witness: `normal_form::tests::canonicalization_is_idempotent`
    /// - witness: `normal_form::tests::relabelling_observers_refuse_missing_positions`
    #[spec(ensures: |ref result| match *result { Maybe::Present(image) => self.wires.get(&wire) == Some(&image), Maybe::Absent(relabelled_wire::Absent::Unmapped) => !self.wires.contains_key(&wire) })]
    #[inline]
    pub fn image_of_wire(
        &self,
        wire: Wire,
    ) -> Maybe<Wire, relabelled_wire::Absent>
    {
        match self.wires.get(&wire) {
            | Some(image) => Maybe::Present(*image),
            | None => Maybe::Absent(relabelled_wire::Absent::Unmapped),
        }
    }

    /// Where the generator at `edge` went.
    ///
    /// # Specification
    /// - provides: [`relabelled_generator::Absent::Unmapped`] when `edge` is
    ///   not in the relabelling's domain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the identity relabelling after canonicalization
    ///   exposes every generator image, and a first-past lookup exposes typed
    ///   absence. Shifting an image or admitting a foreign position differs;
    ///   certification belongs to verify.
    /// - witness: `normal_form::tests::canonicalization_is_idempotent`
    /// - witness: `normal_form::tests::relabelling_observers_refuse_missing_positions`
    #[spec(ensures: |ref result| match *result { Maybe::Present(image) => self.generators.get(&edge) == Some(&image), Maybe::Absent(relabelled_generator::Absent::Unmapped) => !self.generators.contains_key(&edge) })]
    #[inline]
    pub fn image_of_generator(
        &self,
        edge: Edge,
    ) -> Maybe<Edge, relabelled_generator::Absent>
    {
        match self.generators.get(&edge) {
            | Some(image) => Maybe::Present(*image),
            | None => Maybe::Absent(relabelled_generator::Absent::Unmapped),
        }
    }

    /// How many wires the relabelling maps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn mapped_wires(&self) -> WireCount
    {
        WireCount::from(self.wires.len())
    }

    /// How many generators the relabelling maps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn mapped_generators(&self) -> EdgeCount
    {
        EdgeCount::from(self.generators.len())
    }

    /// Checks that this relabelling is an isomorphism from `source` onto
    /// `form`.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when the wire map is a bijection from `source`'s
    ///   wires onto `form`'s, the generator map is a bijection from `source`'s
    ///   generators onto `form`'s, every generator's label and ordered ports
    ///   are carried across position by position, and both interface legs
    ///   commute position by position. A key outside `source` is refused by
    ///   counting: the counts agree and the map is total on `source`, so an
    ///   extra key's image is out of range or already taken.
    /// - provides: the isomorphism between a diagram and its form as something
    ///   a caller checks rather than trusts, which is what keeps
    ///   [`same_diagram`] from being an unguarded equality.
    /// - fails: [`RelabellingDefect`] naming the wire, generator, leg or
    ///   position that fails, the first in the order below.
    /// - panics: none.
    /// - intension: the conditions are decided in a fixed order — the wire
    ///   counts, the generator counts; per mapped wire in order its range and
    ///   then its injectivity; the wire map's totality; the same three for the
    ///   generator map; per source generator in order its label, then its
    ///   sources (arity, then each position), then its targets; the input leg,
    ///   then the output leg (arity, then each position). Each port is checked
    ///   by comparing the image of the declared wire with the form's wire at
    ///   the same position, so a witness cannot pass by permuting ports.
    ///
    /// # Errors
    /// - [`RelabellingDefect::WireCountMismatch`]: the two sides declare
    ///   different numbers of wires.
    /// - [`RelabellingDefect::EdgeCountMismatch`]: the two sides hold different
    ///   numbers of generators.
    /// - [`RelabellingDefect::WireImageOutOfRange`]: a wire's image is not a
    ///   wire of the form.
    /// - [`RelabellingDefect::WireImageReused`]: two wires share an image.
    /// - [`RelabellingDefect::WireUnmapped`]: a wire of the source has no
    ///   image.
    /// - [`RelabellingDefect::GeneratorImageOutOfRange`]: a generator's image
    ///   is not a generator of the form.
    /// - [`RelabellingDefect::GeneratorImageReused`]: two generators share an
    ///   image.
    /// - [`RelabellingDefect::GeneratorUnmapped`]: a generator of the source
    ///   has no image.
    /// - [`RelabellingDefect::LabelMismatch`]: a generator's image carries
    ///   another label.
    /// - [`RelabellingDefect::ArityMismatch`]: a generator's image has another
    ///   number of ports on one leg.
    /// - [`RelabellingDefect::PortMismatch`]: a port's image is not the image
    ///   generator's port at that position.
    /// - [`RelabellingDefect::BoundaryArityMismatch`]: an interface leg has
    ///   another number of ports.
    /// - [`RelabellingDefect::BoundaryMismatch`]: an interface port's image is
    ///   not the form's port at that position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — this is the validator every L1 claim of the module
    ///   rests on, so each refusal is separated by a hand-built defect failing
    ///   only it, asserted by its exact variant and payload: a form of another
    ///   size, an image one past the range, a shared image and an unmapped
    ///   entry for each map; a relabelled record, an extra port and a wrong
    ///   port on each leg of a generator; a wrong arity and a wrong port on
    ///   each interface leg. The acceptance arm runs on every fixture the
    ///   module canonicalizes, and on every generated diagram and its
    ///   permutation.
    /// - witness: `normal_form::tests::the_verifier_refuses_a_defective_wire_map`
    /// - witness: `normal_form::tests::the_verifier_refuses_a_defective_generator_map`
    /// - witness: `normal_form::tests::the_verifier_refuses_a_record_that_does_not_correspond`
    /// - witness: `normal_form::tests::the_verifier_refuses_a_boundary_that_does_not_commute`
    /// - witness: `normal_form::tests::canonicalization_is_total_and_its_witness_verifies`
    /// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
    #[spec(ensures: |ref result| match *result {
        Ok(()) => (source).wire_count() == (form).wire_count() && (source).edge_count() == (form).edge_count()
    && (self).wires.len() == usize::from((source).wire_count()) && (self).generators.len() == (source).generators().len()
    && (self).wires.iter().all(|(wire, image)| usize::from(*wire) < usize::from((source).wire_count()) && usize::from(*image) < usize::from((form).wire_count())
        && (self).wires.range(..*wire).all(|(_, prior)| prior != image))
    && (self).generators.iter().all(|(edge, image)| usize::from(*edge) < (source).generators().len() && usize::from(*image) < (form).generators().len()
        && (self).generators.range(..*edge).all(|(_, prior)| prior != image))
    && (source).generators().iter().enumerate().all(|entry| (self).generators.get(&Edge::from(entry.0)).and_then(|image| (form).generators().get(usize::from(*image))).is_some_and(|found|
        entry.1.label() == found.label() && [(entry.1.sources(), found.sources()), (entry.1.targets(), found.targets())].into_iter().all(|(declared, actual)|
            declared.len() == actual.len() && declared.iter().zip(actual).all(|(wire, image)| (self).wires.get(wire) == Some(image)))))
    && [((source).boundary().inputs(), (form).boundary().inputs()), ((source).boundary().outputs(), (form).boundary().outputs())].into_iter().all(|(declared, found)|
        declared.len() == found.len() && declared.iter().zip(found).all(|(wire, image)| (self).wires.get(wire) == Some(image))),
        Err(RelabellingDefect::WireCountMismatch { source: first, form: second }) => first == source.wire_count() && second == form.wire_count() && first != second,
        Err(RelabellingDefect::EdgeCountMismatch { source: first, form: second }) => first == source.edge_count() && second == form.edge_count() && first != second,
        Err(RelabellingDefect::WireImageOutOfRange { wire, image }) => self.wires.get(&wire) == Some(&image) && usize::from(image) >= usize::from(form.wire_count()),
        Err(RelabellingDefect::WireImageReused { wire, image, bound }) => bound < wire && self.wires.get(&wire) == Some(&image) && self.wires.get(&bound) == Some(&image),
        Err(RelabellingDefect::WireUnmapped { wire }) => usize::from(wire) < usize::from(source.wire_count()) && !self.wires.contains_key(&wire),
        Err(RelabellingDefect::GeneratorImageOutOfRange { at, image }) => self.generators.get(&at) == Some(&image) && usize::from(image) >= form.generators().len(),
        Err(RelabellingDefect::GeneratorImageReused { at, image, bound }) => bound < at && self.generators.get(&at) == Some(&image) && self.generators.get(&bound) == Some(&image),
        Err(RelabellingDefect::GeneratorUnmapped { at }) => usize::from(at) < source.generators().len() && !self.generators.contains_key(&at),
        Err(RelabellingDefect::LabelMismatch { at, image }) => self.generators.get(&at) == Some(&image) && source.generators().get(usize::from(at)).zip(form.generators().get(usize::from(image))).is_some_and(|(from, to)| from.label() != to.label()),
        Err(RelabellingDefect::ArityMismatch { at, image, leg, declared, found }) => source.generators().get(usize::from(at)).zip(form.generators().get(usize::from(image))).is_some_and(|(from, to)| {
            let (first, second) = match leg { Leg::Input => (from.sources(), to.sources()), Leg::Output => (from.targets(), to.targets()) };
            usize::from(declared) == first.len() && usize::from(found) == second.len() && declared != found
        }),
        Err(RelabellingDefect::PortMismatch { at, image, leg, position }) => source.generators().get(usize::from(at)).zip(form.generators().get(usize::from(image))).is_some_and(|(from, to)| {
            let (first, second) = match leg { Leg::Input => (from.sources(), to.sources()), Leg::Output => (from.targets(), to.targets()) };
            first.get(usize::from(position)).is_some_and(|wire| self.wires.get(wire) != second.get(usize::from(position)))
        }),
        Err(RelabellingDefect::BoundaryArityMismatch { leg, declared, found }) => {
            let (first, second) = match leg { Leg::Input => (source.boundary().inputs(), form.boundary().inputs()), Leg::Output => (source.boundary().outputs(), form.boundary().outputs()) };
            usize::from(declared) == first.len() && usize::from(found) == second.len() && declared != found
        },
        Err(RelabellingDefect::BoundaryMismatch { leg, position }) => {
            let (first, second) = match leg { Leg::Input => (source.boundary().inputs(), form.boundary().inputs()), Leg::Output => (source.boundary().outputs(), form.boundary().outputs()) };
            first.get(usize::from(position)).is_some_and(|wire| self.wires.get(wire) != second.get(usize::from(position)))
        },
    })]
    #[inline]
    pub fn verify(
        &self,
        source: &Wiring,
        form: &CanonicalDiagram,
    ) -> Result<(), RelabellingDefect>
    {
        if source.wire_count() != form.wire_count() {
            return Err(RelabellingDefect::WireCountMismatch {
                source: source.wire_count(),
                form: form.wire_count(),
            });
        }
        if source.edge_count() != form.edge_count() {
            return Err(RelabellingDefect::EdgeCountMismatch {
                source: source.edge_count(),
                form: form.edge_count(),
            });
        }
        let mut wire_preimage: BTreeMap<Wire, Wire> = BTreeMap::new();
        for (wire, image) in &self.wires {
            if usize::from(*image) >= usize::from(form.wire_count()) {
                return Err(RelabellingDefect::WireImageOutOfRange {
                    wire: *wire,
                    image: *image,
                });
            }
            if let Some(bound) = wire_preimage.insert(*image, *wire) {
                return Err(RelabellingDefect::WireImageReused {
                    wire: *wire,
                    image: *image,
                    bound,
                });
            }
        }
        for wire in source.wire_count().wires() {
            if !self.wires.contains_key(&wire) {
                return Err(RelabellingDefect::WireUnmapped { wire });
            }
        }
        let mut edge_preimage: BTreeMap<Edge, Edge> = BTreeMap::new();
        for (at, image) in &self.generators {
            if usize::from(*image) >= usize::from(form.edge_count()) {
                return Err(RelabellingDefect::GeneratorImageOutOfRange {
                    at: *at,
                    image: *image,
                });
            }
            if let Some(bound) = edge_preimage.insert(*image, *at) {
                return Err(RelabellingDefect::GeneratorImageReused {
                    at: *at,
                    image: *image,
                    bound,
                });
            }
        }
        for position in 0 .. usize::from(source.edge_count()) {
            let at = Edge::from(position);
            if !self.generators.contains_key(&at) {
                return Err(RelabellingDefect::GeneratorUnmapped { at });
            }
        }
        for (position, generator) in source.generators().iter().enumerate() {
            let at = Edge::from(position);
            // The totality and range passes above make both lookups succeed;
            // a miss is still reported as the defect it would be.
            let Some(image) = self.generators.get(&at).copied()
            else {
                return Err(RelabellingDefect::GeneratorUnmapped { at });
            };
            let Some(record) = form.generators().get(usize::from(image))
            else {
                return Err(RelabellingDefect::GeneratorImageOutOfRange { at, image });
            };
            if record.label() != generator.label() {
                return Err(RelabellingDefect::LabelMismatch { at, image });
            }
            let sources = PortRecords {
                declared: generator.sources(),
                found: record.sources(),
            };
            self.check_ports(sources, at, image, Leg::Input)?;
            let targets = PortRecords {
                declared: generator.targets(),
                found: record.targets(),
            };
            self.check_ports(targets, at, image, Leg::Output)?;
        }
        let inputs = PortRecords {
            declared: source.boundary().inputs(),
            found: form.boundary().inputs(),
        };
        self.check_boundary(inputs, Leg::Input)?;
        let outputs = PortRecords {
            declared: source.boundary().outputs(),
            found: form.boundary().outputs(),
        };
        self.check_boundary(outputs, Leg::Output)?;
        Ok(())
    }

    /// Checks one generator's ports on one leg against its image's.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when the two lists have one length and the found
    ///   list holds the image of each declared port at the same position.
    /// - fails: [`RelabellingDefect::ArityMismatch`] on a length difference;
    ///   [`RelabellingDefect::PortMismatch`] at the first position whose image
    ///   disagrees.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`RelabellingDefect::ArityMismatch`]: the lists differ in length.
    /// - [`RelabellingDefect::PortMismatch`]: a declared port's image is not
    ///   the found port at its position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an extra source, an extra target, a wrong source and
    ///   a wrong target each fail only this check, asserted with the leg and
    ///   the position.
    /// - witness: `normal_form::tests::the_verifier_refuses_a_record_that_does_not_correspond`
    #[spec(ensures: |ref result| match *result {
        Ok(()) => ports.declared.len() == ports.found.len() && ports.declared.iter().zip(ports.found).all(|(wire, found)| self.wires.get(wire) == Some(found)),
        Err(RelabellingDefect::ArityMismatch { at: source, image: target, leg: side, declared, found }) => source == at && target == image && side == leg && usize::from(declared) == ports.declared.len() && usize::from(found) == ports.found.len() && declared != found,
        Err(RelabellingDefect::PortMismatch { at: source, image: target, leg: side, position }) => source == at && target == image && side == leg && ports.declared.len() == ports.found.len()
            && ports.declared.get(usize::from(position)).is_some_and(|wire| self.wires.get(wire) != ports.found.get(usize::from(position)))
            && ports.declared.iter().zip(ports.found).take(usize::from(position)).all(|(wire, found)| self.wires.get(wire) == Some(found)),
        Err(_) => false,
    })]
    fn check_ports(
        &self,
        ports: PortRecords<'_>,
        at: Edge,
        image: Edge,
        leg: Leg,
    ) -> Result<(), RelabellingDefect>
    {
        if ports.declared.len() != ports.found.len() {
            return Err(RelabellingDefect::ArityMismatch {
                at,
                image,
                leg,
                declared: PortCount::from(ports.declared.len()),
                found: PortCount::from(ports.found.len()),
            });
        }
        for (position, wire) in ports.declared.iter().enumerate() {
            if self.wires.get(wire) != ports.found.get(position) {
                return Err(RelabellingDefect::PortMismatch {
                    at,
                    image,
                    leg,
                    position: PortPosition::from(position),
                });
            }
        }
        Ok(())
    }

    /// Checks that one interface leg commutes with the relabelling.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when the two legs have one length and the form's
    ///   leg holds the image of each declared port at the same position, which
    ///   is what commuting with the cospan's leg means.
    /// - fails: [`RelabellingDefect::BoundaryArityMismatch`] on a length
    ///   difference; [`RelabellingDefect::BoundaryMismatch`] at the first
    ///   position whose image disagrees.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`RelabellingDefect::BoundaryArityMismatch`]: the legs differ in
    ///   length.
    /// - [`RelabellingDefect::BoundaryMismatch`]: a declared port's image is
    ///   not the form's port at its position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wide input leg, a narrow output leg, a wrong input
    ///   port and a wrong output port each fail only this check, asserted with
    ///   the leg and the position.
    /// - witness: `normal_form::tests::the_verifier_refuses_a_boundary_that_does_not_commute`
    #[spec(ensures: |ref result| match *result {
        Ok(()) => ports.declared.len() == ports.found.len() && ports.declared.iter().zip(ports.found).all(|(wire, found)| self.wires.get(wire) == Some(found)),
        Err(RelabellingDefect::BoundaryArityMismatch { leg: side, declared, found }) => side == leg && usize::from(declared) == ports.declared.len() && usize::from(found) == ports.found.len() && declared != found,
        Err(RelabellingDefect::BoundaryMismatch { leg: side, position }) => side == leg && ports.declared.len() == ports.found.len()
            && ports.declared.get(usize::from(position)).is_some_and(|wire| self.wires.get(wire) != ports.found.get(usize::from(position)))
            && ports.declared.iter().zip(ports.found).take(usize::from(position)).all(|(wire, found)| self.wires.get(wire) == Some(found)),
        Err(_) => false,
    })]
    fn check_boundary(
        &self,
        ports: PortRecords<'_>,
        leg: Leg,
    ) -> Result<(), RelabellingDefect>
    {
        if ports.declared.len() != ports.found.len() {
            return Err(RelabellingDefect::BoundaryArityMismatch {
                leg,
                declared: PortCount::from(ports.declared.len()),
                found: PortCount::from(ports.found.len()),
            });
        }
        for (position, wire) in ports.declared.iter().enumerate() {
            if self.wires.get(wire) != ports.found.get(position) {
                return Err(RelabellingDefect::BoundaryMismatch {
                    leg,
                    position: PortPosition::from(position),
                });
            }
        }
        Ok(())
    }
}

/// One ordered port list of the source beside the list it should map onto.
#[derive(Clone, Copy, Debug)]
struct PortRecords<'record>
{
    /// The source's ports, in source numbers.
    declared: &'record [Wire],
    /// The form's ports at the same place, in canonical numbers.
    found: &'record [Wire],
}

/// Why a [`Relabelling`] is not an isomorphism onto the form it was checked
/// against.
///
/// Every variant names the wire, generator, leg or position that fails, so a
/// refusal says where the witness breaks and not only that it does.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RelabellingDefect
{
    /// The two sides declare different numbers of wires, so no bijection
    /// between their wires exists.
    WireCountMismatch
    {
        /// What the source declares.
        source: WireCount,
        /// What the form declares.
        form: WireCount,
    },
    /// The two sides hold different numbers of generators.
    EdgeCountMismatch
    {
        /// What the source holds.
        source: EdgeCount,
        /// What the form holds.
        form: EdgeCount,
    },
    /// A wire's image is not a wire of the form.
    WireImageOutOfRange
    {
        /// The wire whose image is out of range.
        wire: Wire,
        /// The out-of-range image.
        image: Wire,
    },
    /// Two wires share an image, so the wire map is not injective.
    WireImageReused
    {
        /// The wire whose image collides.
        wire: Wire,
        /// The shared image.
        image: Wire,
        /// The wire that reached it first.
        bound: Wire,
    },
    /// A wire of the source has no image, so the wire map is not total.
    WireUnmapped
    {
        /// The unmapped wire.
        wire: Wire,
    },
    /// A generator's image is not a generator of the form.
    GeneratorImageOutOfRange
    {
        /// The generator whose image is out of range.
        at: Edge,
        /// The out-of-range image.
        image: Edge,
    },
    /// Two generators share an image, so the generator map is not injective.
    GeneratorImageReused
    {
        /// The generator whose image collides.
        at: Edge,
        /// The shared image.
        image: Edge,
        /// The generator that reached it first.
        bound: Edge,
    },
    /// A generator of the source has no image, so the generator map is not
    /// total.
    GeneratorUnmapped
    {
        /// The unmapped generator.
        at: Edge,
    },
    /// A generator's image carries another label.
    LabelMismatch
    {
        /// The source generator.
        at: Edge,
        /// Its image.
        image: Edge,
    },
    /// A generator's image has another number of ports on one leg.
    ArityMismatch
    {
        /// The source generator.
        at: Edge,
        /// Its image.
        image: Edge,
        /// Which leg.
        leg: Leg,
        /// How many ports the source declares there.
        declared: PortCount,
        /// How many the image holds.
        found: PortCount,
    },
    /// A port's image is not the image generator's port at the same position,
    /// so the map preserves neither incidence nor port order there.
    PortMismatch
    {
        /// The source generator.
        at: Edge,
        /// Its image.
        image: Edge,
        /// Which leg.
        leg: Leg,
        /// Which position.
        position: PortPosition,
    },
    /// An interface leg has another number of ports, so the interfaces differ.
    BoundaryArityMismatch
    {
        /// Which leg.
        leg: Leg,
        /// How many ports the source declares.
        declared: PortCount,
        /// How many the form declares.
        found: PortCount,
    },
    /// An interface port's image is not the form's port at the same position,
    /// so the map does not commute with the cospan's legs.
    BoundaryMismatch
    {
        /// Which leg.
        leg: Leg,
        /// Which position.
        position: PortPosition,
    },
}

impl core::fmt::Display for RelabellingDefect
{
    /// Names the refused condition.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            | Self::WireCountMismatch { .. } => "the two sides declare different numbers of wires",
            | Self::EdgeCountMismatch { .. } => {
                "the two sides hold different numbers of generators"
            },
            | Self::WireImageOutOfRange { .. } => "a wire's image is not a wire of the form",
            | Self::WireImageReused { .. } => "two wires share an image",
            | Self::WireUnmapped { .. } => "a wire of the source has no image",
            | Self::GeneratorImageOutOfRange { .. } => {
                "a generator's image is not a generator of the form"
            },
            | Self::GeneratorImageReused { .. } => "two generators share an image",
            | Self::GeneratorUnmapped { .. } => "a generator of the source has no image",
            | Self::LabelMismatch { .. } => "a generator's image carries another label",
            | Self::ArityMismatch { .. } => "a generator's image has another arity on one leg",
            | Self::PortMismatch { .. } => {
                "a port's image is not the image's port at that position"
            },
            | Self::BoundaryArityMismatch { .. } => "an interface leg has another arity",
            | Self::BoundaryMismatch { .. } => {
                "an interface port's image is not the form's port at that position"
            },
        })
    }
}

impl core::error::Error for RelabellingDefect
{
}

/// What [`canonicalize`] produced: the normal form and the relabelling that
/// reaches it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Canonicalization
{
    /// The normal form.
    form: CanonicalDiagram,
    /// The renumbering that produced it.
    relabelling: Relabelling,
}

impl Canonicalization
{
    /// The normal form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> &CanonicalDiagram
    {
        &self.form
    }

    /// The renumbering that produced the form, as a checkable witness.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relabelling(&self) -> &Relabelling
    {
        &self.relabelling
    }

    /// The form and the relabelling, taken apart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (CanonicalDiagram, Relabelling)
    {
        (self.form, self.relabelling)
    }
}

/// Two diagrams that denote one diagram, with the evidence that they do.
///
/// The evidence is the shared form with both relabellings, not a composed
/// isomorphism between the two inputs: travel from the left diagram to the
/// form, then back along the right relabelling to the right diagram. Composing
/// the halves is a caller's business, and a caller that wants only the verdict
/// never pays for it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SharedCanon
{
    /// The form both diagrams canonicalize to.
    form: CanonicalDiagram,
    /// The left diagram's relabelling onto it.
    left: Relabelling,
    /// The right diagram's relabelling onto it.
    right: Relabelling,
}

impl SharedCanon
{
    /// The form both diagrams canonicalize to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> &CanonicalDiagram
    {
        &self.form
    }

    /// The left diagram's relabelling onto the shared form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> &Relabelling
    {
        &self.left
    }

    /// The right diagram's relabelling onto the shared form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> &Relabelling
    {
        &self.right
    }
}

/// Where two diagrams' canonical forms first differ.
///
/// A negative verdict is evidence too: it says what separates the two
/// diagrams, not only that something does.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DiagramDivergence
{
    /// They declare different numbers of wires.
    WireCount
    {
        /// The left diagram's count.
        left: WireCount,
        /// The right diagram's count.
        right: WireCount,
    },
    /// They hold different numbers of generators.
    GeneratorCount
    {
        /// The left diagram's count.
        left: EdgeCount,
        /// The right diagram's count.
        right: EdgeCount,
    },
    /// One interface leg has different arities.
    BoundaryArity
    {
        /// Which leg.
        leg: Leg,
        /// The left diagram's arity.
        left: PortCount,
        /// The right diagram's arity.
        right: PortCount,
    },
    /// One interface leg carries different canonical wires at one position.
    BoundaryPort
    {
        /// Which leg.
        leg: Leg,
        /// Which position.
        position: PortPosition,
        /// The left form's wire there.
        left: Wire,
        /// The right form's wire there.
        right: Wire,
    },
    /// The canonical generator records differ, first at this position.
    Generator
    {
        /// The canonical position that differs.
        at: Edge,
    },
}

/// Whether two diagrams denote one diagram, with the evidence either way.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DiagramEquality
{
    /// They do: the shared form with both relabellings.
    Same(SharedCanon),
    /// They do not: where their canonical forms part.
    Distinct(DiagramDivergence),
}

/// Renumbers a diagram in the one order the traversal admits.
///
/// # Specification
/// - requires: nothing beyond `diagram` being a [`Wiring`], whose constructor
///   has established monogamy, boundary honesty and acyclicity. The first two
///   are premises of the procedure; acyclicity is not.
/// - ensures: every wire and every generator of `diagram` is numbered exactly
///   once; the form's interface is the declared interface in canonical numbers;
///   the relabelling is an isomorphism from `diagram` onto the form; and the
///   form depends only on the diagram up to cospan isomorphism — two diagrams
///   related by a label- and port-preserving renumbering that commutes with
///   both interface legs reach equal forms.
/// - provides: the diagram normal form as a value whose [`Eq`], [`Ord`] and
///   [`Hash`] are diagram identity, with the witness that makes the form
///   checkable rather than asserted.
/// - panics: none.
/// - intension: the input leg is numbered first and then the output leg; a
///   cursor then drains the numbered wires in canonical order, visiting each
///   wire's producer before its consumer and numbering each visited generator's
///   sources before its targets; components with no boundary port are seeded by
///   their least linearization and committed in the order of those
///   linearizations, ties broken by listing position. A component with a
///   boundary port costs one traversal; an anchorless component of `k`
///   generators costs `k`.
///
/// # Adequacy
/// - hypothesis: L1 — the returned relabelling is verified against the diagram
///   and the form on every fixture, rather than compared with a predicted
///   numbering, and on every generated diagram and a random renumbering and
///   relisting of it. L2 — a differential against an independent
///   cospan-isomorphism oracle that searches generator bijections. L3 — the
///   ordering promises, each separated by a fixture where reversing it changes
///   the form: boundary before interior; anchoring before minimizing, on a
///   spine whose labels sort against its boundary; sources before targets; the
///   least linearization compared past its first record, both for the seed
///   inside one component and for the order of components; two isomorphic
///   anchorless components, where the form is invariant while the relabelling
///   varies; the isolated wire, the empty diagram and port-free generators;
///   idempotence; and the key law that equal forms hash alike and that
///   presentations of one diagram collapse to one map key.
/// - witness: `normal_form::tests::canonicalization_is_total_and_its_witness_verifies`
/// - witness: `normal_form::tests::a_presentation_permutation_has_one_canonical_form`
/// - witness: `normal_form::tests::canonicalization_is_idempotent`
/// - witness: `normal_form::tests::the_canon_agrees_with_the_cospan_isomorphism_oracle`
/// - witness: `normal_form::tests::a_component_with_no_boundary_port_is_seeded_by_minimizing`
/// - witness: `normal_form::tests::components_with_no_boundary_port_are_committed_in_canonical_order`
/// - witness: `normal_form::tests::the_least_linearization_is_compared_past_its_first_record`
/// - witness: `normal_form::tests::two_isomorphic_anchorless_components_still_have_one_form`
/// - witness: `normal_form::tests::the_boundary_is_numbered_before_the_interior`
/// - witness: `normal_form::tests::an_anchored_component_is_ordered_by_the_boundary_and_not_by_its_labels`
/// - witness: `normal_form::tests::a_visited_hyperedge_numbers_its_sources_before_its_targets`
/// - witness: `normal_form::tests::an_isolated_wire_is_numbered_from_the_boundary_alone`
/// - witness: `normal_form::tests::presentations_of_one_diagram_collapse_to_one_key`
/// - witness: `normal_form::tests::equal_canonical_forms_hash_alike`
/// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
#[spec(ensures: |ref result| (diagram).wire_count() == (result.form).wire_count() && (diagram).edge_count() == (result.form).edge_count()
    && (result.relabelling).wires.len() == usize::from((diagram).wire_count()) && (result.relabelling).generators.len() == (diagram).generators().len()
    && (result.relabelling).wires.iter().all(|(wire, image)| usize::from(*wire) < usize::from((diagram).wire_count()) && usize::from(*image) < usize::from((result.form).wire_count())
        && (result.relabelling).wires.range(..*wire).all(|(_, prior)| prior != image))
    && (result.relabelling).generators.iter().all(|(edge, image)| usize::from(*edge) < (diagram).generators().len() && usize::from(*image) < (result.form).generators().len()
        && (result.relabelling).generators.range(..*edge).all(|(_, prior)| prior != image))
    && (diagram).generators().iter().enumerate().all(|entry| (result.relabelling).generators.get(&Edge::from(entry.0)).and_then(|image| (result.form).generators().get(usize::from(*image))).is_some_and(|found|
        entry.1.label() == found.label() && [(entry.1.sources(), found.sources()), (entry.1.targets(), found.targets())].into_iter().all(|(declared, actual)|
            declared.len() == actual.len() && declared.iter().zip(actual).all(|(wire, image)| (result.relabelling).wires.get(wire) == Some(image)))))
    && [((diagram).boundary().inputs(), (result.form).boundary().inputs()), ((diagram).boundary().outputs(), (result.form).boundary().outputs())].into_iter().all(|(declared, found)|
        declared.len() == found.len() && declared.iter().zip(found).all(|(wire, image)| (result.relabelling).wires.get(wire) == Some(image))))]
#[inline]
#[must_use]
pub fn canonicalize(diagram: &Wiring) -> Canonicalization
{
    let mut state = Linearization::new(diagram);
    let boundary = diagram.boundary();
    for wire in boundary.inputs().iter().chain(boundary.outputs()) {
        state.assign_wire(*wire);
    }
    state.drain();
    // A cost guard and nothing else: with every generator visited, every
    // component's lowest member is already numbered, so the seed search finds
    // nothing, and `<=` here is an equivalent program.
    if EdgeCount::from(state.visited.len()) < diagram.edge_count() {
        for seed in anchorless_seeds(&state) {
            state.visit(seed);
            state.drain();
        }
    }
    state.into_canonicalization()
}

/// Decides whether two diagrams denote one diagram.
///
/// # Specification
/// - ensures: [`DiagramEquality::Same`] exactly when the two are related by a
///   renumbering of wires and generators that preserves labels, arities,
///   incidence and port order and commutes with both interface legs — cospan
///   isomorphism over the port bijection — carrying the shared form and each
///   diagram's relabelling onto it; otherwise [`DiagramEquality::Distinct`]
///   naming the first place the canonical forms part.
/// - provides: the decision with evidence on both arms, so neither verdict is a
///   bare bit.
/// - panics: none.
/// - intension: the differences are reported in the order wire count, generator
///   count, input-leg arity, output-leg arity, input-leg ports, output-leg
///   ports, generator records. The first four are invariant under renumbering
///   and are compared on the two diagrams before either is canonicalized; the
///   rest are compared on the forms.
///
/// # Adequacy
/// - hypothesis: L2 — the verdict is checked against an independent
///   cospan-isomorphism oracle over every ordered pair of every fixture, with
///   both verdicts independently checked on hand-classified diagrams. L3 — each
///   negative arm is separated by a pair differing in exactly the datum its
///   variant names, and the four identifications a coarser canon would wrongly
///   admit — a permuted interface leg, a permuted port list on one generator,
///   one label worn at two sorts, and one generator multiset wired two ways —
///   are each refused at the record or port where they part.
/// - witness: `normal_form::tests::the_canon_agrees_with_the_cospan_isomorphism_oracle`
/// - witness: `normal_form::tests::a_presentation_permutation_has_one_canonical_form`
/// - witness: `normal_form::tests::same_diagram_locates_a_count_difference`
/// - witness: `normal_form::tests::same_diagram_locates_a_boundary_difference`
/// - witness: `normal_form::tests::same_diagram_locates_a_hyperedge_difference`
/// - witness: `normal_form::tests::the_canon_separates_a_permuted_boundary`
/// - witness: `normal_form::tests::the_canon_separates_a_permuted_port_list`
/// - witness: `normal_form::tests::the_canon_separates_a_label_worn_at_two_sorts`
/// - witness: `normal_form::tests::the_canon_separates_one_generator_multiset_wired_two_ways`
/// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
/// - boundary: the predicate checks both positive isomorphisms and the negative
///   payload's invariant counts or canonical position; the oracle and located
///   differences establish negative canonical-record provenance.
#[spec(ensures: |ref result| match *result {
    DiagramEquality::Same(ref shared) => (left).wire_count() == (shared.form).wire_count() && (left).edge_count() == (shared.form).edge_count()
    && (shared.left).wires.len() == usize::from((left).wire_count()) && (shared.left).generators.len() == (left).generators().len()
    && (shared.left).wires.iter().all(|(wire, image)| usize::from(*wire) < usize::from((left).wire_count()) && usize::from(*image) < usize::from((shared.form).wire_count())
        && (shared.left).wires.range(..*wire).all(|(_, prior)| prior != image))
    && (shared.left).generators.iter().all(|(edge, image)| usize::from(*edge) < (left).generators().len() && usize::from(*image) < (shared.form).generators().len()
        && (shared.left).generators.range(..*edge).all(|(_, prior)| prior != image))
    && (left).generators().iter().enumerate().all(|entry| (shared.left).generators.get(&Edge::from(entry.0)).and_then(|image| (shared.form).generators().get(usize::from(*image))).is_some_and(|found|
        entry.1.label() == found.label() && [(entry.1.sources(), found.sources()), (entry.1.targets(), found.targets())].into_iter().all(|(declared, actual)|
            declared.len() == actual.len() && declared.iter().zip(actual).all(|(wire, image)| (shared.left).wires.get(wire) == Some(image)))))
    && [((left).boundary().inputs(), (shared.form).boundary().inputs()), ((left).boundary().outputs(), (shared.form).boundary().outputs())].into_iter().all(|(declared, found)|
        declared.len() == found.len() && declared.iter().zip(found).all(|(wire, image)| (shared.left).wires.get(wire) == Some(image)))
        && (right).wire_count() == (shared.form).wire_count() && (right).edge_count() == (shared.form).edge_count()
    && (shared.right).wires.len() == usize::from((right).wire_count()) && (shared.right).generators.len() == (right).generators().len()
    && (shared.right).wires.iter().all(|(wire, image)| usize::from(*wire) < usize::from((right).wire_count()) && usize::from(*image) < usize::from((shared.form).wire_count())
        && (shared.right).wires.range(..*wire).all(|(_, prior)| prior != image))
    && (shared.right).generators.iter().all(|(edge, image)| usize::from(*edge) < (right).generators().len() && usize::from(*image) < (shared.form).generators().len()
        && (shared.right).generators.range(..*edge).all(|(_, prior)| prior != image))
    && (right).generators().iter().enumerate().all(|entry| (shared.right).generators.get(&Edge::from(entry.0)).and_then(|image| (shared.form).generators().get(usize::from(*image))).is_some_and(|found|
        entry.1.label() == found.label() && [(entry.1.sources(), found.sources()), (entry.1.targets(), found.targets())].into_iter().all(|(declared, actual)|
            declared.len() == actual.len() && declared.iter().zip(actual).all(|(wire, image)| (shared.right).wires.get(wire) == Some(image)))))
    && [((right).boundary().inputs(), (shared.form).boundary().inputs()), ((right).boundary().outputs(), (shared.form).boundary().outputs())].into_iter().all(|(declared, found)|
        declared.len() == found.len() && declared.iter().zip(found).all(|(wire, image)| (shared.right).wires.get(wire) == Some(image))),
    DiagramEquality::Distinct(DiagramDivergence::WireCount { left: first, right: second }) => first == left.wire_count() && second == right.wire_count() && first != second,
    DiagramEquality::Distinct(DiagramDivergence::GeneratorCount { left: first, right: second }) => first == left.edge_count() && second == right.edge_count() && first != second,
    DiagramEquality::Distinct(DiagramDivergence::BoundaryArity { leg, left: first, right: second }) => {
        let (mine, theirs) = match leg { Leg::Input => (left.boundary().inputs(), right.boundary().inputs()), Leg::Output => (left.boundary().outputs(), right.boundary().outputs()) };
        usize::from(first) == mine.len() && usize::from(second) == theirs.len() && first != second
    },
    DiagramEquality::Distinct(DiagramDivergence::BoundaryPort { leg, position, left: first, right: second }) => first != second && Outline::of_wiring(left) == Outline::of_wiring(right)
        && usize::from(first) < usize::from(left.wire_count()) && usize::from(second) < usize::from(right.wire_count())
        && usize::from(position) < match leg { Leg::Input => left.boundary().inputs().len(), Leg::Output => left.boundary().outputs().len() },
    DiagramEquality::Distinct(DiagramDivergence::Generator { at }) => Outline::of_wiring(left) == Outline::of_wiring(right) && usize::from(at) < left.generators().len(),
})]
#[inline]
#[must_use]
pub fn same_diagram(
    left: &Wiring,
    right: &Wiring,
) -> DiagramEquality
{
    if let Maybe::Present(divergence) =
        Outline::of_wiring(left).divergence(Outline::of_wiring(right))
    {
        return DiagramEquality::Distinct(divergence);
    }
    let (form, left) = canonicalize(left).into_parts();
    let (other, right) = canonicalize(right).into_parts();
    match divergence_of(&form, &other) {
        | Maybe::Present(divergence) => DiagramEquality::Distinct(divergence),
        | Maybe::Absent(form_divergence::Absent::Equal) => {
            DiagramEquality::Same(SharedCanon { form, left, right })
        },
    }
}

/// What every renumbering of a diagram preserves: its counts and the arity of
/// each interface leg.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Outline
{
    /// How many wires the diagram declares.
    wires: WireCount,
    /// How many generators it holds.
    edges: EdgeCount,
    /// How many input ports it declares.
    inputs: PortCount,
    /// How many output ports it declares.
    outputs: PortCount,
}

impl Outline
{
    /// The outline of a presentation.
    ///
    /// # Specification
    /// trivial.
    fn of_wiring(diagram: &Wiring) -> Self
    {
        Self {
            wires: diagram.wire_count(),
            edges: diagram.edge_count(),
            inputs: PortCount::from(diagram.boundary().inputs().len()),
            outputs: PortCount::from(diagram.boundary().outputs().len()),
        }
    }

    /// The outline of a canonical form.
    ///
    /// # Specification
    /// trivial.
    fn of_form(form: &CanonicalDiagram) -> Self
    {
        Self {
            wires: form.wire_count(),
            edges: form.edge_count(),
            inputs: PortCount::from(form.boundary().inputs().len()),
            outputs: PortCount::from(form.boundary().outputs().len()),
        }
    }

    /// Where two outlines first differ.
    ///
    /// # Specification
    /// - ensures: the first difference in the order wire count, generator
    ///   count, input-leg arity, output-leg arity, carrying both sides' values.
    /// - provides: [`form_divergence::Absent::Equal`] when the outlines agree.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wire-count difference, a generator-count difference
    ///   at equal wire counts, an input-arity difference and an output-arity
    ///   difference behind equal input arities are each reported by their own
    ///   variant with both values.
    /// - witness: `normal_form::tests::same_diagram_locates_a_count_difference`
    /// - witness: `normal_form::tests::same_diagram_locates_a_boundary_difference`
    #[spec(ensures: |ref result| match *result {
        Maybe::Absent(form_divergence::Absent::Equal) => self == other,
        Maybe::Present(DiagramDivergence::WireCount { left, right }) => left == self.wires && right == other.wires && left != right,
        Maybe::Present(DiagramDivergence::GeneratorCount { left, right }) => self.wires == other.wires && left == self.edges && right == other.edges && left != right,
        Maybe::Present(DiagramDivergence::BoundaryArity { leg, left, right }) => self.wires == other.wires && self.edges == other.edges && left != right && match leg {
            Leg::Input => left == self.inputs && right == other.inputs,
            Leg::Output => self.inputs == other.inputs && left == self.outputs && right == other.outputs,
        },
        Maybe::Present(_) => false,
    })]
    fn divergence(
        self,
        other: Self,
    ) -> Maybe<DiagramDivergence, form_divergence::Absent>
    {
        if self.wires != other.wires {
            return Maybe::Present(DiagramDivergence::WireCount {
                left: self.wires,
                right: other.wires,
            });
        }
        if self.edges != other.edges {
            return Maybe::Present(DiagramDivergence::GeneratorCount {
                left: self.edges,
                right: other.edges,
            });
        }
        if self.inputs != other.inputs {
            return Maybe::Present(DiagramDivergence::BoundaryArity {
                leg: Leg::Input,
                left: self.inputs,
                right: other.inputs,
            });
        }
        if self.outputs != other.outputs {
            return Maybe::Present(DiagramDivergence::BoundaryArity {
                leg: Leg::Output,
                left: self.outputs,
                right: other.outputs,
            });
        }
        Maybe::Absent(form_divergence::Absent::Equal)
    }
}

/// Where two canonical forms first differ.
///
/// # Specification
/// - ensures: the first difference in the order of [`Outline::divergence`],
///   then the input leg's ports, the output leg's ports, and the generator
///   records, each position by position.
/// - provides: [`form_divergence::Absent::Equal`] exactly when the two forms
///   are equal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a port difference on the output leg, a record difference
///   at the first, second and third canonical position, and the equal forms of
///   every isomorphic fixture pair separate the arms; the oracle differential
///   checks that no unequal pair is reported equal.
/// - witness: `normal_form::tests::the_canon_separates_a_permuted_boundary`
/// - witness: `normal_form::tests::the_canon_separates_a_permuted_port_list`
/// - witness: `normal_form::tests::same_diagram_locates_a_hyperedge_difference`
/// - witness: `normal_form::tests::the_canon_agrees_with_the_cospan_isomorphism_oracle`
#[spec(ensures: |ref result| match *result {
    Maybe::Absent(form_divergence::Absent::Equal) => left == right,
    Maybe::Present(DiagramDivergence::WireCount { left: first, right: second }) => first == left.wire_count() && second == right.wire_count() && first != second,
    Maybe::Present(DiagramDivergence::GeneratorCount { left: first, right: second }) => left.wire_count() == right.wire_count() && first == left.edge_count() && second == right.edge_count() && first != second,
    Maybe::Present(DiagramDivergence::BoundaryArity { leg, left: first, right: second }) => left.wire_count() == right.wire_count() && left.edge_count() == right.edge_count() && first != second && match leg {
        Leg::Input => usize::from(first) == left.boundary().inputs().len() && usize::from(second) == right.boundary().inputs().len(),
        Leg::Output => left.boundary().inputs().len() == right.boundary().inputs().len() && usize::from(first) == left.boundary().outputs().len() && usize::from(second) == right.boundary().outputs().len(),
    },
    Maybe::Present(DiagramDivergence::BoundaryPort { leg, position, left: first, right: second }) => Outline::of_form(left) == Outline::of_form(right) && first != second && {
        let (mine, theirs) = match leg { Leg::Input => (left.boundary().inputs(), right.boundary().inputs()), Leg::Output => (left.boundary().outputs(), right.boundary().outputs()) };
        (leg == Leg::Input || left.boundary().inputs() == right.boundary().inputs()) && mine.get(usize::from(position)) == Some(&first) && theirs.get(usize::from(position)) == Some(&second)
            && mine.iter().zip(theirs).take(usize::from(position)).all(|pair| pair.0 == pair.1)
    },
    Maybe::Present(DiagramDivergence::Generator { at }) => Outline::of_form(left) == Outline::of_form(right) && left.boundary() == right.boundary()
        && left.generators().get(usize::from(at)).zip(right.generators().get(usize::from(at))).is_some_and(|(mine, theirs)| mine != theirs)
        && left.generators().iter().zip(right.generators()).take(usize::from(at)).all(|pair| pair.0 == pair.1),
})]
fn divergence_of(
    left: &CanonicalDiagram,
    right: &CanonicalDiagram,
) -> Maybe<DiagramDivergence, form_divergence::Absent>
{
    if let Maybe::Present(divergence) = Outline::of_form(left).divergence(Outline::of_form(right)) {
        return Maybe::Present(divergence);
    }
    let legs = [
        (
            Leg::Input,
            left.boundary().inputs(),
            right.boundary().inputs(),
        ),
        (
            Leg::Output,
            left.boundary().outputs(),
            right.boundary().outputs(),
        ),
    ];
    for (leg, mine, theirs) in legs {
        let ports = mine.iter().copied().zip(theirs.iter().copied());
        for (position, (wire, other)) in ports.enumerate() {
            if wire != other {
                return Maybe::Present(DiagramDivergence::BoundaryPort {
                    leg,
                    position: PortPosition::from(position),
                    left: wire,
                    right: other,
                });
            }
        }
    }
    let records = left.generators().iter().zip(right.generators());
    for (position, (record, other)) in records.enumerate() {
        if record != other {
            return Maybe::Present(DiagramDivergence::Generator {
                at: Edge::from(position),
            });
        }
    }
    Maybe::Absent(form_divergence::Absent::Equal)
}

/// The seeds of the components the boundary never reaches, in commit order.
///
/// # Specification
/// - requires: `anchored` has numbered the boundary and drained, so every
///   component holding a boundary port is wholly visited.
/// - ensures: one seed per component `anchored` has not visited: the member
///   whose trial linearization is least, the lowest-positioned among equal
///   ones; the seeds ordered by their winning linearizations, equal ones by
///   seed position.
/// - provides: the only choice the canon makes, made by minimizing over the
///   component's own members.
/// - panics: none.
/// - intension: one trial traversal per member of each anchorless component,
///   each compared record by record over its whole length.
///
/// # Adequacy
/// - hypothesis: L3 — a closed two-generator component reached from either end,
///   two closed components listed either way round, a closed chain whose two
///   interior generators tie on their first record, two components whose
///   winners tie on their first record, and two isomorphic components
///   interleaved in the listing separate the seed minimization, the component
///   order and the whole-linearization comparison from every weaker reading. L1
///   — generated diagrams biased toward anchorless components and port-free
///   generators canonicalize alike under random relisting.
/// - witness: `normal_form::tests::a_component_with_no_boundary_port_is_seeded_by_minimizing`
/// - witness: `normal_form::tests::components_with_no_boundary_port_are_committed_in_canonical_order`
/// - witness: `normal_form::tests::the_least_linearization_is_compared_past_its_first_record`
/// - witness: `normal_form::tests::two_isomorphic_anchorless_components_still_have_one_form`
/// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
/// - boundary: the predicate checks the drained boundary, unvisited membership
///   and uniqueness. The witnesses establish one least seed per component and
///   their global order without allocating a second set of trial traversals.
#[spec(requires: anchored.cursor == anchored.wire_order.len()
    && anchored.diagram.boundary().inputs().iter().chain(anchored.diagram.boundary().outputs()).all(|wire| anchored.wire_image.contains_key(wire)),
ensures: |ref seeds| seeds.is_empty() == (anchored.edge_image.len() == anchored.diagram.generators().len())
    && seeds.iter().enumerate().all(|entry| usize::from(*entry.1) < anchored.diagram.generators().len() && !anchored.edge_image.contains_key(entry.1)
        && !seeds.iter().take(entry.0).any(|prior| prior == entry.1)))]
fn anchorless_seeds(anchored: &Linearization<'_>) -> Vec<Edge>
{
    let diagram = anchored.diagram;
    let components = diagram.components();
    let mut winners: Vec<(Edge, Linearization<'_>)> = Vec::new();
    for index in 0 .. usize::from(components.count()) {
        let Maybe::Present(members) = components.members(ComponentIndex::from(index))
        else {
            continue;
        };
        // A component is visited whole or not at all, so its lowest member
        // stands for it.
        if let Some(first) = members.first()
            && anchored.edge_image.contains_key(first)
        {
            continue;
        }
        let mut best: Option<(Edge, Linearization<'_>)> = None;
        for seed in members.iter().copied() {
            let mut trial = Linearization::new(diagram);
            trial.visit(seed);
            trial.drain();
            let improves = best
                .as_ref()
                .is_none_or(|incumbent| trial.compare_records(&incumbent.1).is_lt());
            if improves {
                best = Some((seed, trial));
            }
        }
        if let Some(winner) = best {
            winners.push(winner);
        }
    }
    winners.sort_by(|left, right| {
        left.1
            .compare_records(&right.1)
            .then_with(|| left.0.cmp(&right.0))
    });
    winners.into_iter().map(|winner| winner.0).collect()
}

/// The canonical numbering of one diagram as the traversal builds it.
///
/// Nothing in it chooses: every number it hands out is forced by the order the
/// boundary and the port lists fix. The one choice the canon makes, the seed
/// of a component with no boundary port, is made outside it by minimizing over
/// the component's members.
struct Linearization<'diagram>
{
    /// The diagram being numbered.
    diagram: &'diagram Wiring,
    /// Where each numbered wire went.
    wire_image: BTreeMap<Wire, Wire>,
    /// The numbered wires in canonical order: the inverse of `wire_image`, and
    /// the queue the drain walks.
    wire_order: Vec<Wire>,
    /// Where each visited generator went.
    edge_image: BTreeMap<Edge, Edge>,
    /// The visited generators in canonical order: the inverse of `edge_image`.
    visited: Vec<&'diagram Generator>,
    /// How many of `wire_order`'s wires the drain has explored.
    cursor: usize,
}

impl<'diagram> Linearization<'diagram>
{
    /// An empty numbering of `diagram`.
    ///
    /// # Specification
    /// trivial.
    fn new(diagram: &'diagram Wiring) -> Self
    {
        Self {
            diagram,
            wire_image: BTreeMap::new(),
            wire_order: Vec::with_capacity(usize::from(diagram.wire_count())),
            edge_image: BTreeMap::new(),
            visited: Vec::with_capacity(usize::from(diagram.edge_count())),
            cursor: 0,
        }
    }

    /// Numbers `wire`, unless it is numbered already.
    ///
    /// # Specification
    /// - ensures: `wire` has a canonical number afterwards; a wire already
    ///   numbered keeps its number, which is what lets both interface legs name
    ///   one wire.
    /// - provides: the only place a canonical wire number is minted, so the
    ///   numbering is dense and in discovery order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an isolated wire declared on both legs is numbered
    ///   once, and the boundary fixtures pin the first numbers to the input leg
    ///   and then the output leg.
    /// - witness: `normal_form::tests::an_isolated_wire_is_numbered_from_the_boundary_alone`
    /// - witness: `normal_form::tests::the_boundary_is_numbered_before_the_interior`
    #[spec(captures: [prior = self.wire_image.get(&wire).copied(), count = self.wire_order.len()],
    ensures: |_| self.wire_order.len() == count.saturating_add(usize::from(prior.is_none()))
        && self.wire_image.get(&wire) == Some(&prior.unwrap_or_else(|| Wire::from(count)))
        && (prior.is_some() || self.wire_order.last() == Some(&wire))
        && self.wire_order.iter().enumerate().all(|entry| self.wire_image.get(entry.1) == Some(&Wire::from(entry.0))))]
    fn assign_wire(
        &mut self,
        wire: Wire,
    )
    {
        if self.wire_image.contains_key(&wire) {
            return;
        }
        self.wire_image
            .insert(wire, Wire::from(self.wire_order.len()));
        self.wire_order.push(wire);
    }

    /// Numbers the generator at `edge` and its ports, unless it is numbered
    /// already.
    ///
    /// # Specification
    /// - requires: `edge` is a generator position of the diagram.
    /// - ensures: the generator has a canonical number afterwards, and every
    ///   wire it names is numbered, its sources in port order before its
    ///   targets in port order.
    /// - provides: the step that makes the traversal port-order-driven.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a generator reached through its first source with its
    ///   second source and its target both unnumbered is the one shape where
    ///   the sources-before-targets order is observable, and its form is
    ///   pinned.
    /// - witness: `normal_form::tests::a_visited_hyperedge_numbers_its_sources_before_its_targets`
    #[spec(requires: usize::from(edge) < self.diagram.generators().len(),
    captures: [prior = self.edge_image.get(&edge).copied(), count = self.visited.len()],
    ensures: |_| self.visited.len() == count.saturating_add(usize::from(prior.is_none()))
        && self.edge_image.get(&edge) == Some(&prior.unwrap_or_else(|| Edge::from(count)))
        && self.diagram.generators().get(usize::from(edge)).is_some_and(|generator|
            generator.sources().iter().chain(generator.targets()).all(|wire| self.wire_image.contains_key(wire))
            && self.visited.get(usize::from(prior.unwrap_or_else(|| Edge::from(count)))).is_some_and(|seen| core::ptr::eq(core::ptr::from_ref(*seen), core::ptr::from_ref(generator)))))]
    fn visit(
        &mut self,
        edge: Edge,
    )
    {
        if self.edge_image.contains_key(&edge) {
            return;
        }
        // Every caller passes a position read from the diagram's own incidence
        // or components, so the lookup finds the generator.
        let Maybe::Present(generator) = self.diagram.generator(edge)
        else {
            return;
        };
        for wire in generator.sources().iter().chain(generator.targets()) {
            self.assign_wire(*wire);
        }
        self.edge_image.insert(edge, Edge::from(self.visited.len()));
        self.visited.push(generator);
    }

    /// Visits everything the numbered wires reach.
    ///
    /// # Specification
    /// - ensures: every numbered wire has had its producer and its consumer
    ///   visited, so no numbered wire leads to an unvisited generator.
    /// - provides: the closure step that lets one seed determine a whole
    ///   component.
    /// - panics: none.
    /// - intension: an explicit cursor over the growing canonical wire order,
    ///   so the walk never recurses on the diagram's size; it ends because a
    ///   wire enters the order once and the cursor only advances. The producer
    ///   is visited before the consumer, an order no form can observe: when the
    ///   cursor reaches a wire at most one of its sides is unvisited.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a spine whose boundary reaches the generator its
    ///   labels sort last separates draining from the boundary from seeding by
    ///   minimization, and the chain and branching fixtures pin the traversal
    ///   order of their interior generators.
    /// - witness: `normal_form::tests::an_anchored_component_is_ordered_by_the_boundary_and_not_by_its_labels`
    /// - witness: `normal_form::tests::the_boundary_is_numbered_before_the_interior`
    #[spec(requires: self.cursor <= self.wire_order.len(),
    ensures: |_| self.cursor == self.wire_order.len() && self.wire_order.iter().all(|wire|
        match self.diagram.producer_of(*wire) { Maybe::Present(edge) => self.edge_image.contains_key(&edge), Maybe::Absent(_) => true }
        && match self.diagram.consumer_of(*wire) { Maybe::Present(edge) => self.edge_image.contains_key(&edge), Maybe::Absent(_) => true }))]
    fn drain(&mut self)
    {
        let diagram = self.diagram;
        while let Some(wire) = self.wire_order.get(self.cursor).copied() {
            self.cursor = self.cursor.saturating_add(1);
            if let Maybe::Present(edge) = diagram.producer_of(wire) {
                self.visit(edge);
            }
            if let Maybe::Present(edge) = diagram.consumer_of(wire) {
                self.visit(edge);
            }
        }
    }

    /// The canonical numbers of an ordered port list.
    ///
    /// # Specification
    /// - requires: every wire of `ports` is numbered.
    /// - ensures: their canonical numbers in the same order.
    /// - panics: none.
    /// - executable: none — the backend lowers the body to a closure whose
    ///   return type cannot name this opaque iterator, even for requires-only
    ///   instrumentation; changing the iterator signature is outside this
    ///   contract.
    /// - intension: an unnumbered wire is skipped rather than guessed at, so
    ///   the list comes out short and [`Relabelling::verify`] reports an arity
    ///   difference; the requirement holds at every call site.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — boundary and hyperedge port-order witnesses observe
    ///   the emitted mapped sequence through the final form, while idempotence
    ///   checks all canonical positions. Dropping a mapped port or reordering
    ///   the stream differs; callers provide fully numbered ports.
    /// - witness: `normal_form::tests::the_boundary_is_numbered_before_the_interior`
    /// - witness: `normal_form::tests::a_visited_hyperedge_numbers_its_sources_before_its_targets`
    /// - witness: `normal_form::tests::canonicalization_is_idempotent`
    fn images<'walk>(
        &'walk self,
        ports: &'walk [Wire],
    ) -> impl Iterator<Item = Wire> + 'walk
    {
        ports
            .iter()
            .filter_map(|wire| self.wire_image.get(wire).copied())
    }

    /// Compares two linearizations by the records they lay down.
    ///
    /// # Specification
    /// - requires: both have drained.
    /// - ensures: the lexicographic order of the two record sequences, each
    ///   record the visited generator's label, then its sources' canonical
    ///   numbers, then its targets', a shorter sequence first when one is a
    ///   prefix of the other; [`core::cmp::Ordering::Equal`] exactly when the
    ///   two lay down identical records. This is the order of the generator
    ///   lists the two would emit, read without materializing them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — seeds that tie on their first record and part later,
    ///   inside one component and across two, are ordered by the later record;
    ///   isomorphic components compare equal and leave the form invariant.
    /// - witness: `normal_form::tests::the_least_linearization_is_compared_past_its_first_record`
    /// - witness: `normal_form::tests::two_isomorphic_anchorless_components_still_have_one_form`
    /// - witness: `normal_form::tests::record_comparison_resolves_equal_prefixes_by_length`
    #[spec(requires: self.cursor == self.wire_order.len() && other.cursor == other.wire_order.len(),
    ensures: |order| order == self.visited.iter().zip(&other.visited).find_map(|(mine, theirs)| {
        let difference = mine.label().cmp(theirs.label())
            .then_with(|| self.images(mine.sources()).cmp(other.images(theirs.sources())))
            .then_with(|| self.images(mine.targets()).cmp(other.images(theirs.targets())));
        difference.is_ne().then_some(difference)
    }).unwrap_or_else(|| self.visited.len().cmp(&other.visited.len())))]
    fn compare_records(
        &self,
        other: &Self,
    ) -> core::cmp::Ordering
    {
        for (mine, theirs) in self.visited.iter().zip(other.visited.iter()) {
            let order = mine
                .label()
                .cmp(theirs.label())
                .then_with(|| {
                    self.images(mine.sources())
                        .cmp(other.images(theirs.sources()))
                })
                .then_with(|| {
                    self.images(mine.targets())
                        .cmp(other.images(theirs.targets()))
                });
            if order.is_ne() {
                return order;
            }
        }
        self.visited.len().cmp(&other.visited.len())
    }

    /// The form and the relabelling this numbering has reached.
    ///
    /// # Specification
    /// - requires: every wire and generator of the diagram is numbered.
    /// - ensures: the form declares as many wires as were numbered, holds one
    ///   record per visited generator in canonical order with its ports in
    ///   canonical numbers, and carries the interface in canonical numbers; the
    ///   relabelling is the two numberings.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every fixture and generated presentation verifies its
    ///   returned isomorphism, and recanonicalization yields the same form with
    ///   identity maps. Losing a numbering, changing a port or interchanging
    ///   the maps breaks the certificate; only complete internal numberings are
    ///   converted.
    /// - witness: `normal_form::tests::canonicalization_is_total_and_its_witness_verifies`
    /// - witness: `normal_form::tests::canonicalization_is_idempotent`
    /// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
    #[spec(requires: self.wire_order.len() == usize::from(self.diagram.wire_count()) && self.visited.len() == self.diagram.generators().len(),
    captures: [source = self.diagram], ensures: |ref result| (source).wire_count() == (result.form).wire_count() && (source).edge_count() == (result.form).edge_count()
        && (result.relabelling).wires.len() == usize::from((source).wire_count()) && (result.relabelling).generators.len() == (source).generators().len()
        && (result.relabelling).wires.iter().all(|(wire, image)| usize::from(*wire) < usize::from((source).wire_count()) && usize::from(*image) < usize::from((result.form).wire_count())
            && (result.relabelling).wires.range(..*wire).all(|(_, prior)| prior != image))
        && (result.relabelling).generators.iter().all(|(edge, image)| usize::from(*edge) < (source).generators().len() && usize::from(*image) < (result.form).generators().len()
            && (result.relabelling).generators.range(..*edge).all(|(_, prior)| prior != image))
        && (source).generators().iter().enumerate().all(|entry| (result.relabelling).generators.get(&Edge::from(entry.0)).and_then(|image| (result.form).generators().get(usize::from(*image))).is_some_and(|found|
            entry.1.label() == found.label() && [(entry.1.sources(), found.sources()), (entry.1.targets(), found.targets())].into_iter().all(|(declared, actual)|
                declared.len() == actual.len() && declared.iter().zip(actual).all(|(wire, image)| (result.relabelling).wires.get(wire) == Some(image)))))
        && [((source).boundary().inputs(), (result.form).boundary().inputs()), ((source).boundary().outputs(), (result.form).boundary().outputs())].into_iter().all(|(declared, found)|
            declared.len() == found.len() && declared.iter().zip(found).all(|(wire, image)| (result.relabelling).wires.get(wire) == Some(image))))]
    fn into_canonicalization(self) -> Canonicalization
    {
        let boundary = self.diagram.boundary();
        let interface = Interface::new(
            self.images(boundary.inputs()).collect::<Box<[Wire]>>(),
            self.images(boundary.outputs()).collect::<Box<[Wire]>>(),
        );
        let generators = self
            .visited
            .iter()
            .map(|generator| {
                Generator::new(
                    generator.label().clone(),
                    self.images(generator.sources()).collect::<Box<[Wire]>>(),
                    self.images(generator.targets()).collect::<Box<[Wire]>>(),
                )
            })
            .collect::<Box<[Generator]>>();
        Canonicalization {
            form: CanonicalDiagram {
                wires: WireCount::from(self.wire_order.len()),
                boundary: interface,
                generators,
            },
            relabelling: Relabelling {
                wires: self.wire_image,
                generators: self.edge_image,
            },
        }
    }
}

#[cfg(test)]
mod tests;
