//! The strata: graphical species over the site, their terms at the
//! catalogue's shapes, and an equivalence of species as the finite certificate
//! it is, at every degree whose Segal condition is certified.
//!
//! # The strata
//!
//! Stratum `n` is the shapes of degree at most `n`. The shapes of degree at
//! most one are the empty shape and the corollas: one vertex, its legs and no
//! inner wire, the point `•` among them. A corolla's [`Profile`] is its input
//! and output leg counts. [`SegalStratum::certify`] admits a catalogue's
//! stratum of degree `n` when the [`corolla`] condition holds over the
//! catalogue's site — the point is a shape, its only raising endomorphism is
//! its identity, and each point of every shape is reached by one inclusion of
//! the point — and, above degree one, when every shape of degree two to `n` is
//! the colimit of its corollas along its grafting pushouts, the [`segal`]
//! condition over the [`Cocones::Admitted`] families. The stratum holds each
//! corolla with its automorphisms and each shape of degree two to `n` with its
//! [`Cocone`]. A catalogue a condition fails on is refused as
//! [`Uncertified::Condition`] with the failing shape and the degree of the
//! condition that fails. Degree zero, and a degree above every shape of the
//! catalogue, are refused as [`Uncertified::Degree`].
//!
//! # Species and their terms
//!
//! A [`Species`] is the alphabet: finitely many generators at each profile.
//! An [`Element`] at a corolla is a generator of the corolla's profile with
//! its ports attached to the corolla's legs: `inputs[i]` is the port the
//! `i`-th input leg, in wire order, attaches to, and `outputs` likewise. The
//! elements at a profile are enumerated generator first, then the input
//! attachments and the output attachments, each permutation in lexicographic
//! order; [`ElementIndex`] is a position in that order. A corolla's
//! automorphisms permute its legs and act on its elements by restriction: the
//! symmetric-group action the site forgets from its shapes, carried here by
//! the elements as the crate's documentation says it is.
//!
//! The terms at a shape are its [`Labelling`]s: one element per vertex, the
//! vertex's legs read in the shape's wire order. They are the product of the
//! elements at the vertices' corollas — the strict Segal condition, which the
//! free algebra on a species satisfies by construction — enumerated with the
//! first vertex most significant. Restriction along a map whose every vertex
//! image is one vertex reads each vertex's label back from its image through
//! the map's wire images.
//!
//! # Equivalence, and its two readings
//!
//! Every statement here fixes its alphabet and its quantifier range. The
//! range is the shapes of the stratum's catalogue, so a statement proved here
//! holds of every shape at the catalogue's bound and says nothing past it. The
//! alphabet at degree `n` is the stratum's probes: the raising maps out of its
//! corollas and its shapes of degree two to `n` that send each vertex to one
//! vertex, into any shape of the catalogue. At degree one they are the
//! corollas' automorphisms and their inclusions at the vertices of larger
//! shapes; above it, the stratum's shapes' automorphisms, their inclusions
//! into larger shapes and the contractions that fuse their legs. The
//! substitutions that send a vertex to a sub-graph and the deletions are
//! outside the alphabet: along them a label becomes a composite operation, or
//! the empty diagram, which the species does not hold.
//!
//! An [`Equivalence`] is generated, not enumerated: at each corolla the
//! species inhabit, a [`Bijection`] between the two sides' elements whose
//! forward table commutes with every automorphism of the corolla.
//! [`Equivalence::check`] decides that by a finite conjunction of equalities
//! and refuses the first failure as a [`Defect`] naming its corolla, its
//! automorphism and its element. Two readings connect it with the terms:
//!
//! - [`Equivalence::extend`] is `ua : Equiv a b → Terms a ≅ Terms b`. At each
//!   shape of the catalogue it is the product of the corolla tables over the
//!   vertices, natural along every probe of the stratum: an equivalence of
//!   species is a natural isomorphism of the free algebras.
//! - [`restrict`] is the corolla restriction of `ua-desc : Terms a ≅ Terms b →
//!   a ≅ b`. It takes a [`Natural`] family of bijections at every shape of the
//!   catalogue, checks naturality along the corollas' probes, and returns the
//!   family's values at the corollas as an equivalence of species. Its
//!   postcondition is the Segal half: the family is the extension of what it
//!   restricts to and natural along every probe of the stratum, so the corolla
//!   values determine everything. A family that is a bijection at every shape
//!   but not natural is refused at the first map and element it fails at.
//!
//! # Decisions
//!
//! - **The generated certificate.** The stored object is one table pair per
//!   inhabited corolla, and naturality up to degree `n` is the automorphism
//!   condition alone. The alternative, a table at every shape with naturality
//!   checked everywhere, is what [`restrict`] accepts as input and reduces to
//!   the generated form. Reversal: a stratum whose shapes are not the products
//!   of their corollas, where the corolla values do not determine a family.
//! - **The corollas generate every certified stratum.** At a certified stratum
//!   each shape of degree two to `n` is the colimit of its corollas, so its
//!   probes add no condition the corollas' probes do not: [`restrict`] checks
//!   the corollas' probes, and naturality along the rest is its postcondition.
//!   The alternative holds a shape that is no colimit as a further generator,
//!   with its own table in the certificate; the stratum refuses it instead.
//!   Reversal: a site whose Segal condition fails at a shape a consumer needs.
//! - **Degree zero is refused.** Below degree one the stratum holds no corolla,
//!   so the only species at it has no generator and its one equivalence is
//!   empty. The alternative certifies it with every corolla past it. Reversal:
//!   a consumer that names the stratum of the empty shape.
//! - **A degree past the catalogue is refused.** The catalogue at size `b`
//!   holds a shape of every degree to `b`, the `b` points, and none above, so a
//!   stratum named by a higher degree would claim a Segal condition at no shape
//!   the bound enumerates. Reversal: none at a finite bound.
//!
//! [`segal`]: crate::segal()

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::Wire;
use quenchant_shape::shape::Maybe;

use crate::catalogue::Catalogue;
use crate::catalogue::ShapeIndex;
use crate::conditions::Site;
use crate::conditions::corolla;
use crate::degree::Degree;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::outcome::Outcome;
use crate::outcome::Verdict;
use crate::segal::Cocone;
use crate::segal::Cocones;
use crate::segal::walk;
use crate::shape::End;
use crate::shape::Shape;

wrapper! {
    /// How many ports one side of a generator has.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PortCount(usize);
}

wrapper! {
    /// How many generators a species holds at one profile.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct GeneratorCount(usize);
}

wrapper! {
    /// A generator's position among the species' generators of its profile.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct GeneratorIndex(usize);
}

wrapper! {
    /// One port of a generator, numbered from zero on its side.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Port(usize);
}

wrapper! {
    /// A position in the enumeration of the elements at a corolla or of the
    /// labellings of a shape.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ElementIndex(usize);
}

quenchant_shape::reason_enum! {
    /// Why a stratum holds no corolla at a profile.
    pub mod stratum_corolla {
        /// The reason the lookup finds no corolla.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The corolla's size is past the catalogue's bound.
            PastTheBound,
        }
    }
}

/// The arity of a corolla or of a vertex: its input legs and its output legs.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Profile
{
    /// The input legs.
    pub inputs: PortCount,
    /// The output legs.
    pub outputs: PortCount,
}

/// The wires a vertex consumes and the wires it produces, each in the shape's
/// wire order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Legs
{
    /// The wires the vertex consumes.
    inputs: Vec<Wire>,
    /// The wires the vertex produces.
    outputs: Vec<Wire>,
}

impl Legs
{
    /// The legs of `vertex` in `shape`.
    ///
    /// # Specification
    /// - ensures: the wires whose consumer is `vertex`, then those whose
    ///   producer is, each in wire order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the binary corolla's two inputs and one output, and
    ///   the graft's inner wire read as an output of its constant and an input
    ///   of its operation, each fix the element counts asserted.
    /// - witness: `tests::stratum::the_corolla_stratum_is_certified_at_degree_one`
    /// - witness: `tests::stratum::restriction_reflects_a_natural_isomorphism_to_its_species`
    #[spec(ensures: |ref legs| legs.inputs.iter().all(|wire| shape.ends().get(usize::from(*wire)).is_some_and(|ends| ends.consumer() == End::Vertex(vertex)))
        && legs.outputs.iter().all(|wire| shape.ends().get(usize::from(*wire)).is_some_and(|ends| ends.producer() == End::Vertex(vertex))))]
    pub fn of(
        shape: &Shape,
        vertex: Edge,
    ) -> Self
    {
        let mut legs = Self::default();
        for (index, ends) in shape.ends().iter().enumerate() {
            if ends.consumer() == End::Vertex(vertex) {
                legs.inputs.push(Wire::from(index));
            }
            if ends.producer() == End::Vertex(vertex) {
                legs.outputs.push(Wire::from(index));
            }
        }
        legs
    }

    /// The profile the legs make.
    ///
    /// # Specification
    /// trivial.
    pub fn profile(&self) -> Profile
    {
        Profile {
            inputs: PortCount(self.inputs.len()),
            outputs: PortCount(self.outputs.len()),
        }
    }
}

/// How a map that sends a vertex to one vertex reads the legs of its image:
/// for each input leg of the vertex, in wire order, the position of its image
/// among the image vertex's input legs, and likewise for the outputs.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Relabelling
{
    /// The input positions.
    inputs: Vec<usize>,
    /// The output positions.
    outputs: Vec<usize>,
}

impl Relabelling
{
    /// How `map`, sending a vertex whose legs are `legs` to one vertex, reads
    /// that vertex's legs.
    ///
    /// # Specification
    /// - requires: `map` is a map of the class sending the vertex to one
    ///   vertex, so its wire images of the vertex's legs are that vertex's
    ///   legs.
    /// - ensures: each leg's position is the number of the same side's images
    ///   below its own: its rank among the image vertex's legs in wire order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the swap of a binary corolla's inputs acts on its
    ///   elements by exchanging the two attachments, and an inclusion at a
    ///   graft reads the vertex's inner wire at its rank.
    /// - witness: `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`
    /// - witness: `tests::stratum::restriction_reflects_a_natural_isomorphism_to_its_species`
    #[spec(ensures: |ref relabelling| relabelling.inputs.len() == legs.inputs.len() && relabelling.outputs.len() == legs.outputs.len())]
    fn of(
        map: &SiteMap,
        legs: &Legs,
    ) -> Self
    {
        let rank = |side: &[Wire]| -> Vec<usize> {
            let images: Vec<Option<Wire>> = side
                .iter()
                .map(|wire| map.wires().get(usize::from(*wire)).copied())
                .collect();
            images
                .iter()
                .map(|image| images.iter().filter(|other| *other < image).count())
                .collect()
        };
        Self {
            inputs: rank(&legs.inputs),
            outputs: rank(&legs.outputs),
        }
    }
}

/// An element of a species at a corolla, or the label of one vertex.
///
/// A generator of the profile with its ports attached to the legs: `inputs[i]`
/// is the port the `i`-th input leg in wire order attaches to.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Element
{
    /// The generator.
    generator: GeneratorIndex,
    /// The port each input leg attaches to.
    inputs: Box<[Port]>,
    /// The port each output leg attaches to.
    outputs: Box<[Port]>,
}

impl Element
{
    /// The element of `generator` with the given attachments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        generator: GeneratorIndex,
        inputs: Vec<Port>,
        outputs: Vec<Port>,
    ) -> Self
    {
        Self {
            generator,
            inputs: inputs.into_boxed_slice(),
            outputs: outputs.into_boxed_slice(),
        }
    }

    /// The generator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generator(&self) -> GeneratorIndex
    {
        self.generator
    }

    /// The port each input leg attaches to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn inputs(&self) -> &[Port]
    {
        &self.inputs
    }

    /// The port each output leg attaches to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outputs(&self) -> &[Port]
    {
        &self.outputs
    }

    /// The element read back along `relabelling`.
    ///
    /// # Specification
    /// - ensures: the same generator, each leg attached to the port the leg at
    ///   its relabelled position held.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the input swap exchanges the attachments of a binary
    ///   operation's element and fixes a constant's.
    /// - witness: `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`
    #[spec(ensures: |ref read| read.generator == self.generator
        && read.inputs.iter().zip(&relabelling.inputs).all(|(port, &position)| self.inputs.get(position) == Some(port)))]
    fn restricted(
        &self,
        relabelling: &Relabelling,
    ) -> Self
    {
        let read = |ports: &[Port], positions: &[usize]| -> Box<[Port]> {
            positions
                .iter()
                .filter_map(|&position| ports.get(position).copied())
                .collect()
        };
        Self {
            generator: self.generator,
            inputs: read(&self.inputs, &relabelling.inputs),
            outputs: read(&self.outputs, &relabelling.outputs),
        }
    }
}

/// The terms of a species at a shape: one element per vertex, in vertex
/// order, each read against its vertex's legs.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Labelling(Box<[Element]>);

impl Labelling
{
    /// The label of each vertex, in vertex order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn labels(&self) -> &[Element]
    {
        &self.0
    }
}

/// Every permutation of the ports `0 .. count`, in lexicographic order.
///
/// # Specification
/// - ensures: each permutation once, in increasing order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the binary corolla holds two elements per generator, the
///   identity attachment first.
/// - witness: `tests::stratum::the_corolla_stratum_is_certified_at_degree_one`
#[spec(ensures: |ref all| all.iter().zip(all.iter().skip(1)).all(|(first, second)| first < second)
    && all.iter().all(|permutation| permutation.len() == usize::from(count)))]
fn permutations(count: PortCount) -> Vec<Box<[Port]>>
{
    let mut partial: Vec<Vec<Port>> = vec![Vec::new()];
    let mut used: BTreeSet<Port> = BTreeSet::new();
    for _ in 0 .. count.0 {
        let mut longer = Vec::new();
        for prefix in &partial {
            used.clear();
            used.extend(prefix.iter().copied());
            for port in (0 .. count.0).map(Port).filter(|port| !used.contains(port)) {
                let mut extended = prefix.clone();
                extended.push(port);
                longer.push(extended);
            }
        }
        partial = longer;
    }
    partial.into_iter().map(Vec::into_boxed_slice).collect()
}

/// A graphical species: finitely many generators at each profile.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Species
{
    /// The generator count at each inhabited profile.
    generators: BTreeMap<Profile, GeneratorCount>,
}

impl Species
{
    /// The species with `generators` at each profile; a profile counted zero
    /// is dropped.
    ///
    /// # Specification
    /// - ensures: the inhabited profiles and their counts, no profile counted
    ///   zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a profile given zero generators holds no element.
    /// - witness: `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref species| species.generators.values().all(|count| usize::from(*count) != 0))]
    pub fn new(mut generators: BTreeMap<Profile, GeneratorCount>) -> Self
    {
        generators.retain(|_, count| count.0 != 0);
        Self { generators }
    }

    /// The generators at `profile`, zero when it holds none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count(
        &self,
        profile: Profile,
    ) -> GeneratorCount
    {
        self.generators.get(&profile).copied().unwrap_or_default()
    }

    /// The inhabited profiles with their counts, in profile order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn profiles(&self) -> impl Iterator<Item = (Profile, GeneratorCount)>
    {
        self.generators
            .iter()
            .map(|(&profile, &count)| (profile, count))
    }

    /// The elements at a corolla of `profile`, in their enumeration order.
    ///
    /// # Specification
    /// - ensures: for each generator of the profile, each input attachment,
    ///   each output attachment, one element; strictly increasing, so an
    ///   element's index is its position under binary search.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one binary generator holds two elements at its
    ///   corolla and a constant one; two binary generators hold four.
    /// - witness: `tests::stratum::the_corolla_stratum_is_certified_at_degree_one`
    /// - witness: `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref elements| elements.iter().zip(elements.iter().skip(1)).all(|(first, second)| first < second)
        && elements.iter().all(|element| element.generator < GeneratorIndex(usize::from(self.count(profile)))))]
    pub fn elements(
        &self,
        profile: Profile,
    ) -> Vec<Element>
    {
        let inputs = permutations(profile.inputs);
        let outputs = permutations(profile.outputs);
        let mut elements = Vec::new();
        for generator in (0 .. usize::from(self.count(profile))).map(GeneratorIndex) {
            for input in &inputs {
                for output in &outputs {
                    elements.push(Element {
                        generator,
                        inputs: input.clone(),
                        outputs: output.clone(),
                    });
                }
            }
        }
        elements
    }

    /// The terms at `shape`: every labelling of its vertices, the first vertex
    /// most significant.
    ///
    /// # Specification
    /// - ensures: one element per vertex, each at the profile of that vertex's
    ///   legs; strictly increasing, so a labelling's index is its position
    ///   under binary search. A shape with a vertex the species does not
    ///   inhabit has none; the empty shape has the one empty labelling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the graft of a constant into a binary operation has
    ///   one labelling per element of the operation, and a shape with a vertex
    ///   of an uninhabited profile has none.
    /// - witness: `tests::stratum::restriction_reflects_a_natural_isomorphism_to_its_species`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref labellings| labellings.iter().zip(labellings.iter().skip(1)).all(|(first, second)| first < second)
        && labellings.iter().all(|labelling| labelling.0.len() == usize::from(shape.vertex_count())))]
    pub fn labellings(
        &self,
        shape: &Shape,
    ) -> Vec<Labelling>
    {
        let mut partial: Vec<Vec<Element>> = vec![Vec::new()];
        for vertex in shape.vertices() {
            let elements = self.elements(Legs::of(shape, vertex).profile());
            let mut longer = Vec::with_capacity(partial.len().saturating_mul(elements.len()));
            for prefix in &partial {
                for element in &elements {
                    let mut extended = prefix.clone();
                    extended.push(element.clone());
                    longer.push(extended);
                }
            }
            partial = longer;
        }
        partial
            .into_iter()
            .map(|labels| Labelling(labels.into_boxed_slice()))
            .collect()
    }
}

/// A bijection's image of each element, by position: entry `i` is the
/// position of the image of the `i`-th element.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Table(Box<[ElementIndex]>);

impl Table
{
    /// The table with the given images.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(images: Vec<ElementIndex>) -> Self
    {
        Self(images.into_boxed_slice())
    }

    /// The image of each element, by position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn images(&self) -> &[ElementIndex]
    {
        &self.0
    }

    /// The image of the element at `position`, when the table reaches it.
    ///
    /// # Specification
    /// trivial.
    fn image(
        &self,
        position: ElementIndex,
    ) -> Option<ElementIndex>
    {
        self.0.get(position.0).copied()
    }
}

/// The two directions of a bijection at one corolla or one shape.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Bijection
{
    /// From the source side's elements to the target side's.
    pub forward: Table,
    /// From the target side's elements to the source side's.
    pub backward: Table,
}

impl Bijection
{
    /// Whether the two tables are mutually inverse between the `terms` on each
    /// side.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when both tables have an entry per term and the
    ///   backward table returns every element the forward one sends; at equal
    ///   finite counts that makes each the other's inverse.
    /// - fails: [`Defect::Tables`] at `shape` for a table of another length,
    ///   [`Defect::NotInverse`] at the first element the backward table does
    ///   not return.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Defect`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a forward table sending two elements to one is
    ///   refused at the second of them.
    /// - witness: `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`
    #[spec(ensures: |ret| match ret {
        | Ok(()) => self.forward.0.len() == terms.len() && self.backward.0.len() == terms.len(),
        | Err(Defect::Tables { shape: found }) => found == shape,
        | Err(Defect::NotInverse { shape: found, element }) => found == shape && element.0 < terms.len(),
        | Err(_) => false,
    })]
    fn inverse<Term>(
        &self,
        shape: ShapeIndex,
        terms: &[Term],
    ) -> Result<(), Defect>
    {
        let count = terms.len();
        if self.forward.0.len() != count || self.backward.0.len() != count {
            return Err(Defect::Tables { shape });
        }
        for element in (0 .. count).map(ElementIndex) {
            let returned = self
                .forward
                .image(element)
                .and_then(|image| self.backward.image(image));
            if returned != Some(element) {
                return Err(Defect::NotInverse { shape, element });
            }
        }
        Ok(())
    }
}

/// Why a stratum is not certified.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Uncertified
{
    /// The degree asked for is zero, below the corollas, or above every shape
    /// of the catalogue.
    Degree
    {
        /// The degree asked for.
        degree: Degree,
    },
    /// A condition the stratum rests on fails over the catalogue: the corolla
    /// condition, at degree one, or the Segal condition at a shape of degree
    /// two or more.
    Condition
    {
        /// The first shape it fails at.
        witness: Shape,
        /// The degree whose condition fails: one for the corolla condition,
        /// the witness's own for the Segal condition.
        degree: Degree,
    },
}

/// Why two species, or a family of bijections, are no equivalence at the
/// stratum.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Defect
{
    /// A generator's corolla is larger than the catalogue's bound.
    PastTheBound
    {
        /// The generator's profile.
        profile: Profile,
    },
    /// The two sides have different numbers of elements at a shape.
    Cardinality
    {
        /// The shape.
        shape: ShapeIndex,
    },
    /// A shape's tables are missing, unexpected, or of the wrong length.
    Tables
    {
        /// The shape.
        shape: ShapeIndex,
    },
    /// The backward table does not return an element the forward one sends.
    NotInverse
    {
        /// The shape.
        shape: ShapeIndex,
        /// The element on the source side.
        element: ElementIndex,
    },
    /// The forward tables do not commute with restriction along a map of the
    /// alphabet.
    NotNatural
    {
        /// The corolla the map leaves.
        corolla: ShapeIndex,
        /// The shape the map reaches.
        shape: ShapeIndex,
        /// The map.
        map: SiteMap,
        /// The element, at the shape, on the source side.
        element: ElementIndex,
    },
}

/// One corolla of a certified stratum.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Corolla
{
    /// Its position in the catalogue.
    index: ShapeIndex,
    /// Its legs.
    legs: Legs,
    /// Its automorphisms.
    automorphisms: Vec<SiteMap>,
}

impl Corolla
{
    /// Its position in the catalogue.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn index(&self) -> ShapeIndex
    {
        self.index
    }

    /// Its input and output leg counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn profile(&self) -> Profile
    {
        self.legs.profile()
    }

    /// Its automorphisms: the maps of the class from it to itself whose image
    /// is its vertex, its identity among them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn automorphisms(&self) -> &[SiteMap]
    {
        &self.automorphisms
    }
}

/// Whether `map` is in the alphabet: raising, every vertex sent to one
/// vertex.
///
/// # Specification
/// trivial.
fn included(map: &SiteMap) -> Membership
{
    let single = map
        .images()
        .iter()
        .all(|image| usize::from(image.count()) == 1);
    if map.raising() == Membership::Inside && single {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// The stratum of a degree over a catalogue whose site passes the corolla
/// condition and, above degree one, the Segal condition to that degree.
#[derive(Clone, Debug)]
pub struct SegalStratum<'catalogue>
{
    /// The catalogue.
    catalogue: &'catalogue Catalogue,
    /// The degree.
    degree: Degree,
    /// Its corollas, in catalogue order.
    corollas: Vec<Corolla>,
    /// Its shapes of degree two to its degree, each with its cocone, in
    /// catalogue order.
    cocones: Vec<Cocone>,
}

impl<'catalogue> SegalStratum<'catalogue>
{
    /// The stratum of `degree` over `catalogue`, when it is certified.
    ///
    /// # Specification
    /// - ensures: on success, every shape of degree one in the catalogue, in
    ///   catalogue order, with its automorphisms, and every shape of degree two
    ///   to `degree`, in catalogue order, with its [`Cocone`].
    /// - fails: [`Uncertified::Degree`] for degree zero;
    ///   [`Uncertified::Condition`] with the first failing shape and degree one
    ///   when the [`corolla`] condition fails over the catalogue's site;
    ///   [`Uncertified::Degree`] for a degree above every shape of the
    ///   catalogue; [`Uncertified::Condition`] with the first failing shape and
    ///   its degree when the [`segal`] condition over [`Cocones::Admitted`]
    ///   fails to `degree`.
    /// - panics: none.
    /// - intension: the Segal condition reads, for each shape of degree two to
    ///   `degree`, every hom set out of it and out of its corollas into the
    ///   catalogue's shapes; at degree one only the site's corolla condition is
    ///   read.
    ///
    /// # Errors
    /// - [`Uncertified`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — at size five the corolla stratum is certified with
    ///   its corollas pinned, the swap among the binary corolla's
    ///   automorphisms, and degree two with its nineteen shapes' cocones; at
    ///   size four degree three holds the closed chain's one graft; degree zero
    ///   and a degree past the catalogue are refused by their degree, and the
    ///   catalogue at size zero, which lacks the point, by the empty shape at
    ///   degree one.
    /// - witness: `tests::stratum::the_corolla_stratum_is_certified_at_degree_one`
    /// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
    ///
    /// [`segal`]: crate::segal()
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        | Ok(ref stratum) => stratum.degree == degree && stratum.corollas.iter().all(|corolla| {
            matches!(catalogue.shape(corolla.index), Maybe::Present(shape) if Degree::of(shape) == Degree::from(1_usize))
        }) && stratum.cocones.iter().all(|cocone| {
            matches!(catalogue.shape(cocone.shape()), Maybe::Present(shape) if Degree::of(shape) > Degree::from(1_usize) && Degree::of(shape) <= degree)
        }),
        | Err(Uncertified::Degree { degree: refused }) => refused == degree && (degree == Degree::default() || catalogue.shapes().iter().all(|shape| Degree::of(shape) < degree)),
        | Err(Uncertified::Condition { ref witness, degree: failing }) => failing <= degree
            && (failing == Degree::from(1_usize) || Degree::of(witness) == failing),
    })]
    pub fn certify(
        catalogue: &'catalogue Catalogue,
        degree: Degree,
    ) -> Result<Self, Uncertified>
    {
        let one = Degree::from(1_usize);
        if degree < one {
            return Err(Uncertified::Degree { degree });
        }
        if let Outcome::Fails { witness, .. } = corolla(&Site::new(catalogue)) {
            return Err(Uncertified::Condition {
                witness,
                degree: one,
            });
        }
        if catalogue
            .shapes()
            .iter()
            .all(|shape| Degree::of(shape) < degree)
        {
            return Err(Uncertified::Degree { degree });
        }
        let (outcome, cocones) = walk(catalogue, degree, Cocones::Admitted);
        if let Outcome::Fails { witness, .. } = outcome {
            return Err(Uncertified::Condition {
                degree: Degree::of(&witness.shape),
                witness: witness.shape,
            });
        }
        let mut corollas = Vec::new();
        for (index, shape) in catalogue.entries() {
            if Degree::of(shape) != one {
                continue;
            }
            let automorphisms = match catalogue.maps(index, index) {
                Maybe::Present(maps) => maps
                    .iter()
                    .filter(|map| included(map) == Membership::Inside)
                    .cloned()
                    .collect(),
                Maybe::Absent(_) => Vec::new(),
            };
            corollas.push(Corolla {
                index,
                legs: Legs::of(shape, Edge::from(0_usize)),
                automorphisms,
            });
        }
        Ok(Self {
            catalogue,
            degree,
            corollas,
            cocones,
        })
    }

    /// The degree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn degree(&self) -> Degree
    {
        self.degree
    }

    /// The shapes of degree two to the stratum's degree, each with its
    /// cocone, in catalogue order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cocones(&self) -> &[Cocone]
    {
        &self.cocones
    }

    /// The catalogue.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn catalogue(&self) -> &'catalogue Catalogue
    {
        self.catalogue
    }

    /// The corollas, in catalogue order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn corollas(&self) -> &[Corolla]
    {
        &self.corollas
    }

    /// The corolla of `profile`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn corolla(
        &self,
        profile: Profile,
    ) -> Maybe<&Corolla, stratum_corolla::Absent>
    {
        self.corollas
            .iter()
            .find(|corolla| corolla.profile() == profile)
            .map_or(
                Maybe::Absent(stratum_corolla::Absent::PastTheBound),
                Maybe::Present,
            )
    }
}

/// The elements of both sides at one corolla and the bijection between them.
#[derive(Clone, Copy, Debug)]
struct Sides<'data>
{
    /// The source side's elements.
    source: &'data [Element],
    /// The target side's elements.
    target: &'data [Element],
    /// The bijection.
    bijection: &'data Bijection,
}

/// An equivalence of species at a certified stratum, generated on its
/// inhabited corollas.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Equivalence
{
    /// The bijection at each inhabited corolla, by catalogue position.
    components: BTreeMap<ShapeIndex, Bijection>,
}

impl Equivalence
{
    /// The equivalence `components` state between `source` and `target`, when
    /// it is one.
    ///
    /// # Specification
    /// - requires: nothing; every failure is a refusal.
    /// - ensures: on success, a bijection at exactly the corollas the two
    ///   species inhabit, whose forward table commutes with restriction along
    ///   every automorphism of its corolla at every element. The backward
    ///   table, the forward one's inverse, commutes with them too.
    /// - fails: [`Defect::PastTheBound`] for a profile either species inhabits
    ///   whose corolla is past the catalogue's bound; then, corolla by corolla
    ///   in catalogue order, [`Defect::Cardinality`] when the two sides'
    ///   element counts differ, [`Defect::Tables`] for a component missing at
    ///   an inhabited corolla or present at another, [`Defect::NotInverse`],
    ///   and [`Defect::NotNatural`] at the first automorphism and element the
    ///   forward table does not commute at.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Defect`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the input swap of one binary generator and the
    ///   identity are equivalences; exchanging two binary generators at one
    ///   attachment alone is refused at the swap, a forward table that is not
    ///   injective as not inverse, unequal counts as a cardinality, and a
    ///   generator of five legs at size five as past the bound.
    /// - witness: `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        | Ok(ref equivalence) => equivalence.components.keys().all(|index| {
            stratum.corollas.iter().any(|corolla| corolla.index == *index && usize::from(sides.0.count(corolla.profile())) != 0)
        }),
        | Err(Defect::PastTheBound { profile }) => matches!(stratum.corolla(profile), Maybe::Absent(_)),
        | Err(_) => true,
    })]
    pub fn check(
        stratum: &SegalStratum<'_>,
        sides: (&Species, &Species),
        mut components: BTreeMap<ShapeIndex, Bijection>,
    ) -> Result<Self, Defect>
    {
        for (profile, _) in sides.0.profiles().chain(sides.1.profiles()) {
            if let Maybe::Absent(_) = stratum.corolla(profile) {
                return Err(Defect::PastTheBound { profile });
            }
        }
        let mut checked = BTreeMap::new();
        for corolla in &stratum.corollas {
            let shape = corolla.index;
            let source = sides.0.elements(corolla.profile());
            let target = sides.1.elements(corolla.profile());
            if source.len() != target.len() {
                return Err(Defect::Cardinality { shape });
            }
            if source.is_empty() {
                continue;
            }
            let Some(bijection) = components.remove(&shape)
            else {
                return Err(Defect::Tables { shape });
            };
            bijection.inverse(shape, &source)?;
            let paired = Sides {
                source: &source,
                target: &target,
                bijection: &bijection,
            };
            for automorphism in &corolla.automorphisms {
                let relabelling = Relabelling::of(automorphism, &corolla.legs);
                if let Some(element) = paired.first_uncommuting(&relabelling, &relabelling) {
                    return Err(Defect::NotNatural {
                        corolla: shape,
                        shape,
                        map: automorphism.clone(),
                        element,
                    });
                }
            }
            checked.insert(shape, bijection);
        }
        if let Some((&shape, _)) = components.iter().next() {
            return Err(Defect::Tables { shape });
        }
        Ok(Self {
            components: checked,
        })
    }

    /// The bijection at each inhabited corolla, by catalogue position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn components(&self) -> &BTreeMap<ShapeIndex, Bijection>
    {
        &self.components
    }

    /// `ua`: the natural isomorphism of the free algebras this equivalence is,
    /// at every shape of the stratum's catalogue.
    ///
    /// # Specification
    /// - requires: the equivalence was checked at `stratum` between `sides`.
    /// - ensures: one bijection per shape of the catalogue, in catalogue order;
    ///   at a shape, each labelling goes to the labelling whose label at every
    ///   vertex is that vertex's label under the corolla table of its profile,
    ///   the vertex's legs read in wire order onto the corolla's. Naturality
    ///   makes the reading independent of which inclusion identifies them, and
    ///   the family is natural along every probe of the stratum.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the input swap extends at the graft of a constant
    ///   into a binary operation to the swap of the operation's label, and
    ///   [`restrict`] returns the equivalence from its extension; at degree two
    ///   the extension commutes with the contraction of two disjoint corollas
    ///   into their graft.
    /// - witness: `tests::stratum::restriction_reflects_a_natural_isomorphism_to_its_species`
    /// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref natural| natural.components.len() == stratum.catalogue.shapes().len()
        && probed(stratum, sides, natural) == Verdict::Holds)]
    pub fn extend(
        &self,
        stratum: &SegalStratum<'_>,
        sides: (&Species, &Species),
    ) -> Natural
    {
        let mut corollas: BTreeMap<Profile, (Vec<Element>, Vec<Element>, &Bijection)> =
            BTreeMap::new();
        for corolla in &stratum.corollas {
            if let Some(bijection) = self.components.get(&corolla.index) {
                corollas.insert(
                    corolla.profile(),
                    (
                        sides.0.elements(corolla.profile()),
                        sides.1.elements(corolla.profile()),
                        bijection,
                    ),
                );
            }
        }
        let carry = |labelling: &Labelling, shape: &Shape, onto: &[Labelling], forward: bool| {
            let mut labels = Vec::with_capacity(labelling.0.len());
            for (vertex, label) in shape.vertices().zip(labelling.0.iter()) {
                let &(ref source, ref target, bijection) =
                    corollas.get(&Legs::of(shape, vertex).profile())?;
                let (from, to, table) = if forward {
                    (source, target, &bijection.forward)
                }
                else {
                    (target, source, &bijection.backward)
                };
                let image = table.image(ElementIndex(from.binary_search(label).ok()?))?;
                labels.push(to.get(image.0)?.clone());
            }
            onto.binary_search(&Labelling(labels.into_boxed_slice()))
                .ok()
                .map(ElementIndex)
        };
        let mut components = Vec::with_capacity(stratum.catalogue.shapes().len());
        for shape in stratum.catalogue.shapes() {
            let source = sides.0.labellings(shape);
            let target = sides.1.labellings(shape);
            let forward = source
                .iter()
                .filter_map(|labelling| carry(labelling, shape, &target, true))
                .collect();
            let backward = target
                .iter()
                .filter_map(|labelling| carry(labelling, shape, &source, false))
                .collect();
            components.push(Bijection {
                forward: Table::new(forward),
                backward: Table::new(backward),
            });
        }
        Natural {
            components: components.into_boxed_slice(),
        }
    }
}

impl Sides<'_>
{
    /// The first source element at which the forward table does not commute
    /// with reading the source along `before` and the target along `after`.
    ///
    /// # Specification
    /// - ensures: the least `i` such that the image of element `i` read along
    ///   `after` is not the image of element `i` read along `before`, or either
    ///   is missing from its enumeration; `None` when every element commutes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exchanging two binary generators at one attachment
    ///   fails at the first element, and the input swap commutes everywhere.
    /// - witness: `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`
    #[spec(ensures: |ret| ret.is_none_or(|element| element.0 < self.source.len()))]
    fn first_uncommuting(
        &self,
        before: &Relabelling,
        after: &Relabelling,
    ) -> Option<ElementIndex>
    {
        (0 .. self.source.len()).map(ElementIndex).find(|&element| {
            let left = self
                .source
                .get(element.0)
                .and_then(|label| self.source.binary_search(&label.restricted(before)).ok())
                .and_then(|read| self.bijection.forward.image(ElementIndex(read)));
            let right = self
                .bijection
                .forward
                .image(element)
                .and_then(|image| self.target.get(image.0))
                .and_then(|label| self.target.binary_search(&label.restricted(after)).ok())
                .map(ElementIndex);
            left.is_none() || left != right
        })
    }
}

/// A family of bijections between two species' terms, one at every shape of a
/// catalogue: a candidate isomorphism of the free algebras at the stratum.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Natural
{
    /// The bijection at each shape, by catalogue position.
    components: Box<[Bijection]>,
}

impl Natural
{
    /// The family with `components`, one per shape in catalogue order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(components: Vec<Bijection>) -> Self
    {
        Self {
            components: components.into_boxed_slice(),
        }
    }

    /// The bijection at each shape, by catalogue position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn components(&self) -> &[Bijection]
    {
        &self.components
    }
}

/// Whether `natural` commutes with restriction along every probe of
/// `stratum`: each raising map out of one of its corollas or its shapes of
/// degree two to its degree that sends every vertex to one vertex, into any
/// shape of the catalogue.
///
/// # Specification
/// - ensures: [`Verdict::Holds`] exactly when, for every probe `f : P → K` and
///   every labelling of `K` on the source side, the forward table at `P` sends
///   its restriction along `f` to the restriction along `f` of its image under
///   the forward table at `K`; [`Verdict::Fails`] at a missing table or an
///   image past its labellings.
/// - panics: none.
/// - executable: none — it is the predicate the postconditions of
///   [`Equivalence::extend`] and [`restrict`] evaluate, and a clause on it
///   would restate its body.
///
/// # Adequacy
/// - hypothesis: L3 — the swap's extension at degree two commutes with the
///   contraction of two disjoint corollas into their graft, and the family with
///   the identity at the graft does not.
/// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
fn probed(
    stratum: &SegalStratum<'_>,
    sides: (&Species, &Species),
    natural: &Natural,
) -> Verdict
{
    let catalogue = stratum.catalogue;
    let sources = stratum
        .corollas
        .iter()
        .map(Corolla::index)
        .chain(stratum.cocones.iter().map(Cocone::shape));
    let mut legs: Vec<Legs> = Vec::new();
    for source in sources {
        let (Maybe::Present(form), Some(at_source)) = (
            catalogue.shape(source),
            natural.components.get(usize::from(source)),
        )
        else {
            return Verdict::Fails;
        };
        legs.clear();
        legs.extend(form.vertices().map(|vertex| Legs::of(form, vertex)));
        let read = (sides.0.labellings(form), sides.1.labellings(form));
        for (target, shape) in catalogue.entries() {
            let (Maybe::Present(maps), Some(at_target)) = (
                catalogue.maps(source, target),
                natural.components.get(usize::from(target)),
            )
            else {
                return Verdict::Fails;
            };
            let onto = (sides.0.labellings(shape), sides.1.labellings(shape));
            for map in maps
                .iter()
                .filter(|map| included(map) == Membership::Inside)
            {
                let restricted = |labelling: &Labelling, terms: &[Labelling]| {
                    let mut labels = Vec::with_capacity(legs.len());
                    for (vertex, legs) in form.vertices().zip(&legs) {
                        let image = map.image(vertex).members().next()?;
                        let label = labelling.0.get(usize::from(image))?;
                        labels.push(label.restricted(&Relabelling::of(map, legs)));
                    }
                    terms
                        .binary_search(&Labelling(labels.into_boxed_slice()))
                        .ok()
                        .map(ElementIndex)
                };
                for (position, labelling) in onto.0.iter().enumerate() {
                    let left = restricted(labelling, &read.0)
                        .and_then(|element| at_source.forward.image(element));
                    let right = at_target
                        .forward
                        .image(ElementIndex(position))
                        .and_then(|image| onto.1.get(image.0))
                        .and_then(|image| restricted(image, &read.1));
                    if left.is_none() || left != right {
                        return Verdict::Fails;
                    }
                }
            }
        }
    }
    Verdict::Holds
}

/// `ua-desc`'s corolla restriction: the equivalence of species a natural
/// isomorphism of the free algebras restricts to.
///
/// # Specification
/// - requires: nothing; every failure is a refusal.
/// - ensures: on success, the family's bijections at the corollas the species
///   inhabit, checked as an [`Equivalence`], and the family is that
///   equivalence's [`Equivalence::extend`], natural along every probe of the
///   stratum: the corolla values determine the family at every shape of the
///   catalogue, and the Segal condition the stratum certifies is why the probes
///   of its shapes of degree two or more add no check.
/// - fails: [`Defect::Tables`] at the first shape with no bijection, or past
///   the last shape when the family has more; then, shape by shape in catalogue
///   order, [`Defect::Cardinality`] and [`Defect::NotInverse`]; then, corolla
///   by corolla and shape by shape, [`Defect::NotNatural`] at the first probe
///   out of a corolla and labelling where the family's forward tables do not
///   commute with restriction; and [`Equivalence::check`]'s refusals.
/// - panics: none.
///
/// # Errors
/// - [`Defect`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the extension of the input swap restricts to the swap;
///   the same family with the identity at the graft, a bijection at every
///   shape, is refused at the inclusion of the binary corolla into the graft,
///   at degree one and at degree two alike.
/// - witness: `tests::stratum::restriction_reflects_a_natural_isomorphism_to_its_species`
/// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
#[inline]
#[spec(ensures: |ref ret| match *ret {
    | Ok(ref equivalence) => equivalence.extend(stratum, sides) == *natural && probed(stratum, sides, natural) == Verdict::Holds,
    | Err(_) => true,
})]
pub fn restrict(
    stratum: &SegalStratum<'_>,
    sides: (&Species, &Species),
    natural: &Natural,
) -> Result<Equivalence, Defect>
{
    let catalogue = stratum.catalogue;
    let mut terms = Vec::with_capacity(catalogue.shapes().len());
    for (shape, form) in catalogue.entries() {
        let Some(bijection) = natural.components.get(usize::from(shape))
        else {
            return Err(Defect::Tables { shape });
        };
        let source = sides.0.labellings(form);
        let target = sides.1.labellings(form);
        if source.len() != target.len() {
            return Err(Defect::Cardinality { shape });
        }
        bijection.inverse(shape, &source)?;
        terms.push((source, target));
    }
    if natural.components.len() > catalogue.shapes().len() {
        return Err(Defect::Tables {
            shape: ShapeIndex::from(catalogue.shapes().len()),
        });
    }
    let mut components = BTreeMap::new();
    for corolla in &stratum.corollas {
        let Some(at_corolla) = natural.components.get(usize::from(corolla.index))
        else {
            continue;
        };
        let source_elements = sides.0.elements(corolla.profile());
        let target_elements = sides.1.elements(corolla.profile());
        for (shape, pair) in terms.iter().enumerate() {
            let (source, target) = (&pair.0, &pair.1);
            let shape = ShapeIndex::from(shape);
            let Some(bijection) = natural.components.get(usize::from(shape))
            else {
                continue;
            };
            let Maybe::Present(maps) = catalogue.maps(corolla.index, shape)
            else {
                continue;
            };
            for map in maps
                .iter()
                .filter(|map| included(map) == Membership::Inside)
            {
                let relabelling = Relabelling::of(map, &corolla.legs);
                let Some(vertex) = map.image(Edge::from(0_usize)).members().next()
                else {
                    continue;
                };
                let read = |labelling: Option<&Labelling>, elements: &[Element]| {
                    let label = labelling?.0.get(usize::from(vertex))?;
                    elements
                        .binary_search(&label.restricted(&relabelling))
                        .ok()
                        .map(ElementIndex)
                };
                let uncommuting = (0 .. source.len()).map(ElementIndex).find(|&element| {
                    let left = read(source.get(element.0), &source_elements)
                        .and_then(|restricted| at_corolla.forward.image(restricted));
                    let right = read(
                        bijection
                            .forward
                            .image(element)
                            .and_then(|image| target.get(image.0)),
                        &target_elements,
                    );
                    left.is_none() || left != right
                });
                if let Some(element) = uncommuting {
                    return Err(Defect::NotNatural {
                        corolla: corolla.index,
                        shape,
                        map: map.clone(),
                        element,
                    });
                }
            }
        }
        if !source_elements.is_empty() {
            components.insert(corolla.index, at_corolla.clone());
        }
    }
    Equivalence::check(stratum, sides, components)
}
