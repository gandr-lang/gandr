//! The diagram view: wires, generators, the interface a rewrite is taken
//! relative to, the validated [`Wiring`], and the seam datum that stands where
//! a position stood.
//!
//! # Diagrams with interfaces
//!
//! A circuit rewrite rewrites a diagram *with an interface*: the interface of
//! a diagram is the coproduct of its input and output ports, and the rewriting
//! theory this view serves — convex double-pushout rewriting of monogamous
//! acyclic hypergraphs with interfaces — states every result relative to it.
//! The hypergraph's nodes are [`Wire`]s and its hyperedges are [`Generator`]s,
//! addressed by [`Edge`] position; the naming follows the theory because every
//! condition this module enforces is stated there.
//!
//! # The fragment's hypotheses are invariants of the type
//!
//! [`Wiring::assemble`] is the only constructor of a [`Wiring`], and it refuses
//! anything outside the fragment the theory quantifies over:
//!
//! - **monogamy**: in-degree and out-degree at most one on every wire, so a
//!   wire is never combined (fan-in) or copied (fan-out);
//! - **mono boundary legs**: neither port list repeats a wire;
//! - **declared open ports**: a boundary input has no producer, a boundary
//!   output has no consumer, and every wire with no producer or no consumer is
//!   declared on the matching leg;
//! - **acyclicity**: no directed cycle.
//!
//! Each refusal is a [`WiringObstruction`] naming the wire or generator that
//! caused it. Checking at construction rather than at match time is what makes
//! the hypotheses of every quoted theorem — the convex correspondence, the
//! uniqueness of boundary complements, and the automatic convexity of a
//! strongly connected match over an acyclic target — properties no caller can
//! route around.
//!
//! # The seam is a pair of partial bijections
//!
//! A match into a tree is addressed by one path of child indices. A match into
//! a circuit is addressed by where the pattern's interface lands on the
//! target's wires, the input half and the output half kept apart: a [`Seam`] is
//! that pair, and a [`PartialBijection`] is one half.
//!
//! # A derived index, not a carrier
//!
//! A [`Wiring`] is the matcher's working view of a diagram. It holds nothing a
//! diagram's port-bijection representation does not already hold, and nothing
//! in this crate reads a wiring back out as a term.

pub mod spine;

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

wrapper! {
    /// A wire: one node of the hypergraph a diagram reads as, addressed by its
    /// index below the diagram's [`WireCount`].
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Wire(usize);
}

wrapper! {
    /// A hyperedge: one generator occurrence, addressed by its position in the
    /// diagram's generator list.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Edge(usize);
}

wrapper! {
    /// How many wires a diagram declares.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct WireCount(usize);
}

wrapper! {
    /// How many generator occurrences a diagram holds.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct EdgeCount(usize);
}

wrapper! {
    /// How many pairs a [`PartialBijection`] carries.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PairCount(usize);
}

wrapper! {
    /// Which weakly connected component of a diagram a query names.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ComponentIndex(usize);
}

wrapper! {
    /// How many weakly connected components a diagram's generators fall into.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ComponentCount(usize);
}

impl WireCount
{
    /// Whether `wire` is one of the wires this count declares.
    ///
    /// # Specification
    /// - ensures: [`Declaration::Declared`] exactly when `wire`'s index is
    ///   below the count.
    /// - panics: none.
    #[inline]
    fn declares(
        self,
        wire: Wire,
    ) -> Declaration
    {
        if wire.0 < self.0 {
            Declaration::Declared
        }
        else {
            Declaration::Undeclared
        }
    }

    /// The declared wires, in index order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn wires(self) -> impl Iterator<Item = Wire>
    {
        (0 .. self.0).map(Wire)
    }
}

/// Whether a wire lies below a diagram's wire count.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Declaration
{
    /// The wire is one of the diagram's.
    Declared,
    /// The wire is at or past the count.
    Undeclared,
}

/// A generator's name: the box's label in the picture.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GeneratorName(Box<str>);

impl GeneratorName
{
    /// A generator name from any name convertible into one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(name: N) -> Self
    where
        N: Into<Self>,
    {
        name.into()
    }
}

impl From<&str> for GeneratorName
{
    /// The name spelled by `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.into())
    }
}

impl From<String> for GeneratorName
{
    /// The name spelled by `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: String) -> Self
    {
        Self(name.into_boxed_str())
    }
}

impl AsRef<str> for GeneratorName
{
    /// The name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl core::fmt::Display for GeneratorName
{
    /// Writes the name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The syntactic role a generator's name is worn in.
///
/// A name alone does not identify a generator: the sequent alphabet's
/// constructor `K` and an operation spelled `K` are two different boxes, in
/// general of one arity, so a label that forgot the role would let a pattern's
/// producer match a target's consumer frame. A diagram with no such distinction
/// to make uses [`GeneratorSort::Value`] throughout.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GeneratorSort
{
    /// A value-side generator: the sequent alphabet's constructor `K(p̄)`.
    Value,
    /// An operation frame: the sequent alphabet's `f(p̄; c)`.
    Operation,
    /// A return-side constructor frame: the sequent alphabet's `K⁻(c)`.
    Return,
    /// A closed terminal: the sequent alphabet's `★`, a generator consuming a
    /// wire and producing none, never an open port.
    Terminal,
    /// An applied rewrite: a declared circuit rule fired in a body. A rewrite
    /// and an operation of one spelling are two different boxes.
    Rewrite,
}

/// The label a generator carries: a name together with the role it is worn
/// in.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GeneratorLabel
{
    /// The generator's name.
    name: GeneratorName,
    /// The role the name is worn in.
    sort: GeneratorSort,
}

impl GeneratorLabel
{
    /// A label from a name and a role.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        name: N,
        sort: GeneratorSort,
    ) -> Self
    where
        N: Into<GeneratorName>,
    {
        Self {
            name: name.into(),
            sort,
        }
    }

    /// The generator's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> &GeneratorName
    {
        &self.name
    }

    /// The role the name is worn in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sort(&self) -> GeneratorSort
    {
        self.sort
    }
}

/// One generator occurrence: its label and its ordered ports.
///
/// Port order is carried rather than quotiented: no symmetry acts within a
/// generator, so ordering its ports gives nothing up, and an embedding
/// preserves it. The derived order is lexicographic on
/// `(label, sources, targets)`, an order on presentations and never a claim
/// about diagrams.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Generator
{
    /// The label this occurrence carries.
    label: GeneratorLabel,
    /// The ordered source wires: the generator's inputs.
    sources: Box<[Wire]>,
    /// The ordered target wires: the generator's outputs.
    targets: Box<[Wire]>,
}

impl Generator
{
    /// A generator occurrence from its label and its two ordered port lists.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<Sources, Targets>(
        label: GeneratorLabel,
        sources: Sources,
        targets: Targets,
    ) -> Self
    where
        Sources: Into<Box<[Wire]>>,
        Targets: Into<Box<[Wire]>>,
    {
        Self {
            label,
            sources: sources.into(),
            targets: targets.into(),
        }
    }

    /// The label this occurrence carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn label(&self) -> &GeneratorLabel
    {
        &self.label
    }

    /// The ordered source wires.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sources(&self) -> &[Wire]
    {
        &self.sources
    }

    /// The ordered target wires.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn targets(&self) -> &[Wire]
    {
        &self.targets
    }
}

/// The discrete boundary a rewrite is taken relative to: the interface.
///
/// Both lists are ordered. [`Wiring::assemble`] refuses a list that repeats a
/// wire, which is the mono-leg half of monogamy.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Interface
{
    /// The ordered input ports: wires no generator produces.
    inputs: Box<[Wire]>,
    /// The ordered output ports: wires no generator consumes.
    outputs: Box<[Wire]>,
}

impl Interface
{
    /// An interface from its two ordered port lists.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<Inputs, Outputs>(
        inputs: Inputs,
        outputs: Outputs,
    ) -> Self
    where
        Inputs: Into<Box<[Wire]>>,
        Outputs: Into<Box<[Wire]>>,
    {
        Self {
            inputs: inputs.into(),
            outputs: outputs.into(),
        }
    }

    /// The ordered input ports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn inputs(&self) -> &[Wire]
    {
        &self.inputs
    }

    /// The ordered output ports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outputs(&self) -> &[Wire]
    {
        &self.outputs
    }
}

/// A refused extension of a [`PartialBijection`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BijectionClash
{
    /// The source wire is already mapped, and not to this image.
    SourceBound
    {
        /// The source wire the extension names.
        source: Wire,
        /// Where the source already goes.
        bound: Wire,
    },
    /// The image wire is already reached by a different source, so extending
    /// would stop the map being injective.
    ImageBound
    {
        /// The image wire the extension names.
        image: Wire,
        /// The source that already reaches it.
        bound: Wire,
    },
}

impl core::fmt::Display for BijectionClash
{
    /// Names the refusal.
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
            | Self::SourceBound { .. } => "the source wire is already mapped to another image",
            | Self::ImageBound { .. } => "the image wire is already reached by another source",
        })
    }
}

impl core::error::Error for BijectionClash
{
}

quenchant_shape::reason_enum! {
    /// Why a partial bijection maps a source wire nowhere.
    pub mod wire_image {
        /// The reason the lookup finds no image.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The wire is outside the map's domain.
            Unmapped,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no source of a partial bijection reaches an image wire.
    pub mod wire_preimage {
        /// The reason the lookup finds no source.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The wire is outside the map's range.
            Unreached,
        }
    }
}

/// A partial bijection on wires: one half of the seam datum.
///
/// Injective by construction: [`PartialBijection::extend`] refuses a pair that
/// would identify two sources, and leaves the map as it was.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct PartialBijection
{
    /// Source wire to image wire.
    forward: BTreeMap<Wire, Wire>,
    /// Image wire back to source wire, which is what makes injectivity
    /// checkable per extension.
    backward: BTreeMap<Wire, Wire>,
}

impl PartialBijection
{
    /// The empty partial bijection.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Where `source` goes.
    ///
    /// # Specification
    /// - provides: [`wire_image::Absent::Unmapped`] when `source` is not in the
    ///   map's domain.
    /// - panics: none.
    #[inline]
    pub fn image_of(
        &self,
        source: Wire,
    ) -> Maybe<Wire, wire_image::Absent>
    {
        match self.forward.get(&source) {
            | Some(image) => Maybe::Present(*image),
            | None => Maybe::Absent(wire_image::Absent::Unmapped),
        }
    }

    /// The source that reaches `image`.
    ///
    /// # Specification
    /// - provides: [`wire_preimage::Absent::Unreached`] when `image` is not in
    ///   the map's range.
    /// - panics: none.
    #[inline]
    pub fn preimage_of(
        &self,
        image: Wire,
    ) -> Maybe<Wire, wire_preimage::Absent>
    {
        match self.backward.get(&image) {
            | Some(source) => Maybe::Present(*source),
            | None => Maybe::Absent(wire_preimage::Absent::Unreached),
        }
    }

    /// How many pairs the map carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pair_count(&self) -> PairCount
    {
        PairCount(self.forward.len())
    }

    /// The pairs `(source, image)`, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn pairs(&self) -> impl Iterator<Item = (Wire, Wire)>
    {
        self.forward.iter().map(|(source, image)| (*source, *image))
    }

    /// The restriction of the map to `ports`: one half of a [`Seam`].
    ///
    /// # Specification
    /// - ensures: exactly the pairs whose source is one of `ports` and is
    ///   mapped. Injectivity is inherited from this map, so the restriction
    ///   cannot fail.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the restriction is the seam a search issues, and the
    ///   certificate reader re-derives it from the wire map and compares; a
    ///   restriction that kept a non-port pair or dropped a mapped port is
    ///   refused as a forged seam on a search's own certificates.
    /// - witness: `matching::tests::an_embedding_carries_its_seam_as_a_pair_of_partial_bijections`
    /// - witness: `matching::tests::the_searches_certificates_verify_against_their_own_diagrams`
    #[inline]
    #[must_use]
    pub fn restricted_to(
        &self,
        ports: &[Wire],
    ) -> Self
    {
        let mut forward: BTreeMap<Wire, Wire> = BTreeMap::new();
        let mut backward: BTreeMap<Wire, Wire> = BTreeMap::new();
        for port in ports {
            if let Some(image) = self.forward.get(port) {
                forward.insert(*port, *image);
                backward.insert(*image, *port);
            }
        }
        Self { forward, backward }
    }

    /// Extends the map with the pair `(source, image)`.
    ///
    /// # Specification
    /// - ensures: a pair already present is accepted and changes nothing; a
    ///   pair whose source and image are both unbound is added.
    /// - fails: [`BijectionClash::SourceBound`] when `source` already maps
    ///   elsewhere; [`BijectionClash::ImageBound`] when another source already
    ///   reaches `image`. A refusal leaves the map as it was.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BijectionClash::SourceBound`]: `source` is mapped to another image.
    /// - [`BijectionClash::ImageBound`]: `image` is reached by another source.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh pair, its idempotent repeat, a re-bound
    ///   source and a re-used image separate the four outcomes, each refusal
    ///   asserted with its payload and the map asserted unchanged after both.
    /// - witness: `interface::tests::a_partial_bijection_stays_injective`
    #[inline]
    pub fn extend(
        &mut self,
        source: Wire,
        image: Wire,
    ) -> Result<(), BijectionClash>
    {
        if let Some(bound) = self.forward.get(&source).copied() {
            if bound == image {
                return Ok(());
            }
            return Err(BijectionClash::SourceBound { source, bound });
        }
        if let Some(bound) = self.backward.get(&image).copied() {
            return Err(BijectionClash::ImageBound { image, bound });
        }
        self.forward.insert(source, image);
        self.backward.insert(image, source);
        Ok(())
    }
}

/// The seam datum: where a pattern's interface lands on a target, as a pair
/// of partial bijections.
///
/// The input half and the output half are kept apart because the two halves
/// play different roles in the span a rewrite is.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Seam
{
    /// The input half: the pattern's input ports to their images.
    inputs: PartialBijection,
    /// The output half: the pattern's output ports to their images.
    outputs: PartialBijection,
}

impl Seam
{
    /// A seam from its two halves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        inputs: PartialBijection,
        outputs: PartialBijection,
    ) -> Self
    {
        Self { inputs, outputs }
    }

    /// The input half.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn inputs(&self) -> &PartialBijection
    {
        &self.inputs
    }

    /// The output half.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outputs(&self) -> &PartialBijection
    {
        &self.outputs
    }
}

/// A refused [`Wiring`]: the condition of the fragment the diagram fails, with
/// the wire or generator that fails it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum WiringObstruction
{
    /// A generator names a wire the diagram does not declare.
    UnknownWire
    {
        /// The out-of-range wire.
        wire: Wire,
        /// The generator that names it.
        at: Edge,
    },
    /// The boundary names a wire the diagram does not declare.
    UnknownBoundaryWire
    {
        /// The out-of-range wire.
        wire: Wire,
    },
    /// One wire is produced twice: in-degree two, the combining fan-in the
    /// fragment excludes.
    ///
    /// The two producers may be one generator naming the wire at two target
    /// ports; `first` and `second` are then equal.
    FanIn
    {
        /// The doubly produced wire.
        wire: Wire,
        /// The generator that produced it first.
        first: Edge,
        /// The generator that produced it again.
        second: Edge,
    },
    /// One wire is consumed twice: out-degree two, the copy the fragment
    /// excludes.
    ///
    /// The two consumers may be one generator naming the wire at two source
    /// ports; `first` and `second` are then equal.
    FanOut
    {
        /// The doubly consumed wire.
        wire: Wire,
        /// The generator that consumed it first.
        first: Edge,
        /// The generator that consumed it again.
        second: Edge,
    },
    /// A boundary list names one wire twice, so its leg is not mono.
    RepeatedBoundaryPort
    {
        /// The repeated wire.
        wire: Wire,
    },
    /// A boundary input is produced by a generator, so it is not open.
    BoundaryInputIsProduced
    {
        /// The wire declared as an input.
        wire: Wire,
        /// The generator that produces it.
        by: Edge,
    },
    /// A boundary output is consumed by a generator, so it is not open.
    BoundaryOutputIsConsumed
    {
        /// The wire declared as an output.
        wire: Wire,
        /// The generator that consumes it.
        by: Edge,
    },
    /// A wire no generator produces is not declared as an input, so the
    /// interface would lose a port.
    ///
    /// The refusal carries the matcher's convexity discharge as well as the
    /// interface's honesty: the discharge reads every image input back as the
    /// image of a declared pattern input, and an undeclared open wire would be
    /// an image input no connectivity test asked about.
    UndeclaredInput
    {
        /// The undeclared open wire.
        wire: Wire,
    },
    /// A wire no generator consumes is not declared as an output.
    UndeclaredOutput
    {
        /// The undeclared open wire.
        wire: Wire,
    },
    /// The diagram has a directed cycle, outside the acyclic fragment every
    /// theorem the matcher quotes quantifies over.
    DirectedCycle
    {
        /// A generator the cycle runs through.
        through: Edge,
    },
}

impl core::fmt::Display for WiringObstruction
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
            | Self::UnknownWire { .. } => "a generator names a wire the diagram does not declare",
            | Self::UnknownBoundaryWire { .. } => {
                "the boundary names a wire the diagram does not declare"
            },
            | Self::FanIn { .. } => "a wire is produced twice",
            | Self::FanOut { .. } => "a wire is consumed twice",
            | Self::RepeatedBoundaryPort { .. } => "a boundary list names a wire twice",
            | Self::BoundaryInputIsProduced { .. } => "a boundary input is produced by a generator",
            | Self::BoundaryOutputIsConsumed { .. } => {
                "a boundary output is consumed by a generator"
            },
            | Self::UndeclaredInput { .. } => "a wire no generator produces is not an input port",
            | Self::UndeclaredOutput { .. } => "a wire no generator consumes is not an output port",
            | Self::DirectedCycle { .. } => "the diagram has a directed cycle",
        })
    }
}

impl core::error::Error for WiringObstruction
{
}

quenchant_shape::reason_enum! {
    /// Why a diagram holds no generator at a position.
    pub mod generator_lookup {
        /// The reason the lookup finds no generator.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The position is at or past the diagram's generator count.
            OutOfRange,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no generator produces a wire.
    pub mod wire_producer {
        /// The reason the wire has no producer.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The wire is a boundary input port.
            BoundaryInput,
            /// The wire is not one of the diagram's.
            OutOfRange,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no generator consumes a wire.
    pub mod wire_consumer {
        /// The reason the wire has no consumer.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The wire is a boundary output port.
            BoundaryOutput,
            /// The wire is not one of the diagram's.
            OutOfRange,
        }
    }
}

/// One diagram with an interface, inside the monogamous acyclic fragment.
///
/// A value exists only because [`Wiring::assemble`] proved the diagram is in
/// the fragment. Both halves of that proof are load-bearing for the matcher:
/// monogamy makes the search choice-free after one seed per component, and
/// acyclicity is the hypothesis under which a strongly connected pattern's
/// match is convex without a sweep.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Wiring
{
    /// The generator occurrences, addressed by [`Edge`] position.
    generators: Box<[Generator]>,
    /// The discrete boundary.
    boundary: Interface,
    /// How many wires the diagram declares.
    wires: WireCount,
    /// The generator that produces each produced wire.
    producer: BTreeMap<Wire, Edge>,
    /// The generator that consumes each consumed wire.
    consumer: BTreeMap<Wire, Edge>,
}

impl Wiring
{
    /// Assembles a diagram with an interface, or refuses it.
    ///
    /// # Specification
    /// - ensures: the wiring holds `generators` in order, `boundary` and
    ///   `wires`; it is monogamous (in-degree and out-degree at most one on
    ///   every wire, both boundary legs mono), boundary-honest (an input has no
    ///   producer, an output no consumer, and every wire with no producer or no
    ///   consumer is declared on that leg), and acyclic.
    /// - fails: [`WiringObstruction`] naming the first failed condition and the
    ///   wire or generator that fails it.
    /// - panics: none.
    /// - intension: the conditions are decided in a fixed order — per generator
    ///   in position order its sources then its targets (range, then degree);
    ///   the input leg, then the output leg (range, repetition, openness); per
    ///   wire in index order an undeclared input, then an undeclared output;
    ///   acyclicity last, the one condition that is not local. A diagram
    ///   failing several is refused by the earliest.
    ///
    /// # Errors
    /// - [`WiringObstruction::UnknownWire`]: a generator port names a wire at
    ///   or past `wires`.
    /// - [`WiringObstruction::FanOut`]: a wire is a source twice.
    /// - [`WiringObstruction::FanIn`]: a wire is a target twice.
    /// - [`WiringObstruction::UnknownBoundaryWire`]: a port names a wire at or
    ///   past `wires`.
    /// - [`WiringObstruction::RepeatedBoundaryPort`]: a leg repeats a wire.
    /// - [`WiringObstruction::BoundaryInputIsProduced`]: an input has a
    ///   producer.
    /// - [`WiringObstruction::BoundaryOutputIsConsumed`]: an output has a
    ///   consumer.
    /// - [`WiringObstruction::UndeclaredInput`]: a wire with no producer is no
    ///   input.
    /// - [`WiringObstruction::UndeclaredOutput`]: a wire with no consumer is no
    ///   output.
    /// - [`WiringObstruction::DirectedCycle`]: a directed cycle runs through
    ///   the named generator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refusal is separated by a diagram failing only
    ///   it, asserted by its exact variant and payload: an out-of-range wire
    ///   named by a source, by a target and by either boundary leg, each at the
    ///   first index past the count; a fan-in and a fan-out by two generators
    ///   and by one generator repeating a port; a repeat on either leg; a
    ///   produced input and a consumed output; an undeclared open wire on
    ///   either side; a cycle through one generator, through two, and one with
    ///   a generator downstream of it listed first, so the named generator is
    ///   on the cycle. L1 — an assembled wiring answers its incidence queries
    ///   consistently with the generators it was given.
    /// - witness: `interface::tests::an_assembled_wiring_answers_its_incidence`
    /// - witness: `interface::tests::the_wiring_refuses_an_out_of_range_generator_wire`
    /// - witness: `interface::tests::the_wiring_refuses_an_out_of_range_boundary_wire`
    /// - witness: `interface::tests::the_wiring_refuses_a_fan_in`
    /// - witness: `interface::tests::the_wiring_refuses_a_fan_out`
    /// - witness: `interface::tests::the_wiring_refuses_a_repeated_port_on_one_generator`
    /// - witness: `interface::tests::the_wiring_refuses_a_repeated_boundary_port`
    /// - witness: `interface::tests::the_wiring_refuses_a_produced_boundary_input`
    /// - witness: `interface::tests::the_wiring_refuses_a_consumed_boundary_output`
    /// - witness: `interface::tests::the_wiring_refuses_an_undeclared_open_wire`
    /// - witness: `interface::tests::the_wiring_refuses_an_undeclared_open_input`
    /// - witness: `interface::tests::the_wiring_refuses_a_self_looping_generator`
    /// - witness: `interface::tests::the_wiring_refuses_a_directed_cycle`
    #[inline]
    pub fn assemble(
        wires: WireCount,
        generators: Vec<Generator>,
        boundary: Interface,
    ) -> Result<Self, WiringObstruction>
    {
        let mut producer: BTreeMap<Wire, Edge> = BTreeMap::new();
        let mut consumer: BTreeMap<Wire, Edge> = BTreeMap::new();
        for (index, generator) in generators.iter().enumerate() {
            let edge = Edge(index);
            for wire in generator.sources.iter().copied() {
                if wires.declares(wire) == Declaration::Undeclared {
                    return Err(WiringObstruction::UnknownWire { wire, at: edge });
                }
                if let Some(first) = consumer.insert(wire, edge) {
                    return Err(WiringObstruction::FanOut {
                        wire,
                        first,
                        second: edge,
                    });
                }
            }
            for wire in generator.targets.iter().copied() {
                if wires.declares(wire) == Declaration::Undeclared {
                    return Err(WiringObstruction::UnknownWire { wire, at: edge });
                }
                if let Some(first) = producer.insert(wire, edge) {
                    return Err(WiringObstruction::FanIn {
                        wire,
                        first,
                        second: edge,
                    });
                }
            }
        }
        let mut inputs: BTreeSet<Wire> = BTreeSet::new();
        for wire in boundary.inputs.iter().copied() {
            if wires.declares(wire) == Declaration::Undeclared {
                return Err(WiringObstruction::UnknownBoundaryWire { wire });
            }
            if !inputs.insert(wire) {
                return Err(WiringObstruction::RepeatedBoundaryPort { wire });
            }
            if let Some(by) = producer.get(&wire).copied() {
                return Err(WiringObstruction::BoundaryInputIsProduced { wire, by });
            }
        }
        let mut outputs: BTreeSet<Wire> = BTreeSet::new();
        for wire in boundary.outputs.iter().copied() {
            if wires.declares(wire) == Declaration::Undeclared {
                return Err(WiringObstruction::UnknownBoundaryWire { wire });
            }
            if !outputs.insert(wire) {
                return Err(WiringObstruction::RepeatedBoundaryPort { wire });
            }
            if let Some(by) = consumer.get(&wire).copied() {
                return Err(WiringObstruction::BoundaryOutputIsConsumed { wire, by });
            }
        }
        for wire in wires.wires() {
            if !producer.contains_key(&wire) && !inputs.contains(&wire) {
                return Err(WiringObstruction::UndeclaredInput { wire });
            }
            if !consumer.contains_key(&wire) && !outputs.contains(&wire) {
                return Err(WiringObstruction::UndeclaredOutput { wire });
            }
        }
        check_acyclic(&generators, &producer, &consumer)?;
        Ok(Self {
            generators: generators.into_boxed_slice(),
            boundary,
            wires,
            producer,
            consumer,
        })
    }

    /// The generator occurrences, addressed by [`Edge`] position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generators(&self) -> &[Generator]
    {
        &self.generators
    }

    /// The generator at `edge`.
    ///
    /// # Specification
    /// - provides: [`generator_lookup::Absent::OutOfRange`] when `edge` is at
    ///   or past the generator count.
    /// - panics: none.
    #[inline]
    pub fn generator(
        &self,
        edge: Edge,
    ) -> Maybe<&Generator, generator_lookup::Absent>
    {
        match self.generators.get(edge.0) {
            | Some(generator) => Maybe::Present(generator),
            | None => Maybe::Absent(generator_lookup::Absent::OutOfRange),
        }
    }

    /// The discrete boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn boundary(&self) -> &Interface
    {
        &self.boundary
    }

    /// How many wires the diagram declares.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wire_count(&self) -> WireCount
    {
        self.wires
    }

    /// How many generator occurrences the diagram holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn edge_count(&self) -> EdgeCount
    {
        EdgeCount(self.generators.len())
    }

    /// The generator that produces `wire`.
    ///
    /// # Specification
    /// - provides: [`wire_producer::Absent::BoundaryInput`] for a declared wire
    ///   no generator produces, which boundary honesty makes an input port;
    ///   [`wire_producer::Absent::OutOfRange`] for a wire the diagram does not
    ///   declare.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a produced wire, an input port and a wire past the
    ///   count separate the three answers.
    /// - witness: `interface::tests::an_assembled_wiring_answers_its_incidence`
    #[inline]
    pub fn producer_of(
        &self,
        wire: Wire,
    ) -> Maybe<Edge, wire_producer::Absent>
    {
        if let Some(edge) = self.producer.get(&wire) {
            return Maybe::Present(*edge);
        }
        match self.wires.declares(wire) {
            | Declaration::Declared => Maybe::Absent(wire_producer::Absent::BoundaryInput),
            | Declaration::Undeclared => Maybe::Absent(wire_producer::Absent::OutOfRange),
        }
    }

    /// The generator that consumes `wire`.
    ///
    /// # Specification
    /// - provides: [`wire_consumer::Absent::BoundaryOutput`] for a declared
    ///   wire no generator consumes, which boundary honesty makes an output
    ///   port; [`wire_consumer::Absent::OutOfRange`] for a wire the diagram
    ///   does not declare.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a consumed wire, an output port and a wire past the
    ///   count separate the three answers.
    /// - witness: `interface::tests::an_assembled_wiring_answers_its_incidence`
    #[inline]
    pub fn consumer_of(
        &self,
        wire: Wire,
    ) -> Maybe<Edge, wire_consumer::Absent>
    {
        if let Some(edge) = self.consumer.get(&wire) {
            return Maybe::Present(*edge);
        }
        match self.wires.declares(wire) {
            | Declaration::Declared => Maybe::Absent(wire_consumer::Absent::BoundaryOutput),
            | Declaration::Undeclared => Maybe::Absent(wire_consumer::Absent::OutOfRange),
        }
    }

    /// The diagram's weakly connected components over generator adjacency.
    ///
    /// Two generators are adjacent when one produces a wire the other
    /// consumes. The relation is the undirected one, so a component is a piece
    /// of the picture with no wire leaving it. The matcher takes one seed per
    /// component.
    ///
    /// # Specification
    /// - ensures: every generator position appears in exactly one component;
    ///   components are ordered by their lowest-positioned member, and each
    ///   component's members are in ascending position order; a diagram with no
    ///   generator has no component.
    /// - panics: none.
    /// - intension: an explicit frontier over generators, each pushed once;
    ///   discovery runs in ascending position order, which makes the emitted
    ///   order deterministic.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the partition is validated against its diagram (every
    ///   position covered once, members ascending) rather than against a
    ///   predicted answer. L3 — the two adjacency directions are separated by a
    ///   join reachable only forwards from the seed and one reachable only
    ///   backwards, and a port-free generator is its own component, so two
    ///   points of one label stay two addressable components.
    /// - witness: `interface::tests::the_components_partition_the_generators`
    /// - witness: `interface::tests::a_component_joins_through_a_shared_wire_in_both_directions`
    /// - witness: `interface::tests::a_port_free_generator_is_its_own_component`
    #[inline]
    #[must_use]
    pub fn components(&self) -> Components
    {
        let count = self.generators.len();
        let mut placed: Vec<Placement> = alloc::vec![Placement::Unplaced; count];
        let mut members: Vec<Edge> = Vec::with_capacity(count);
        let mut ends: Vec<usize> = Vec::new();
        let mut frontier: Vec<Edge> = Vec::new();
        for index in 0 .. count {
            if place(&mut placed, Edge(index)) == Placement::Placed {
                continue;
            }
            let start = members.len();
            frontier.push(Edge(index));
            while let Some(current) = frontier.pop() {
                members.push(current);
                let Some(generator) = self.generators.get(current.0)
                else {
                    continue;
                };
                for wire in &generator.sources {
                    if let Some(neighbour) = self.producer.get(wire).copied()
                        && place(&mut placed, neighbour) == Placement::Unplaced
                    {
                        frontier.push(neighbour);
                    }
                }
                for wire in &generator.targets {
                    if let Some(neighbour) = self.consumer.get(wire).copied()
                        && place(&mut placed, neighbour) == Placement::Unplaced
                    {
                        frontier.push(neighbour);
                    }
                }
            }
            if let Some(component) = members.get_mut(start ..) {
                component.sort_unstable();
            }
            ends.push(members.len());
        }
        Components {
            members: members.into_boxed_slice(),
            ends: ends.into_boxed_slice(),
        }
    }
}

/// Whether a generator has been placed in a component yet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Placement
{
    /// No component holds it yet.
    Unplaced,
    /// A component holds it.
    Placed,
}

/// Marks `edge` placed and reports whether it already was.
///
/// # Specification
/// - ensures: `edge` is placed afterwards; returns its placement before the
///   call. A position outside `placed` reports [`Placement::Placed`], so a walk
///   never pushes it.
/// - panics: none.
fn place(
    placed: &mut [Placement],
    edge: Edge,
) -> Placement
{
    match placed.get_mut(edge.0) {
        | Some(slot) => core::mem::replace(slot, Placement::Placed),
        | None => Placement::Placed,
    }
}

quenchant_shape::reason_enum! {
    /// Why a component index names no component.
    pub mod component_lookup {
        /// The reason the lookup finds no members.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The index is at or past the component count.
            OutOfRange,
        }
    }
}

/// A diagram's generators, partitioned into weakly connected components.
///
/// Built only by [`Wiring::components`], so a value is a partition of exactly
/// one diagram's generator positions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Components
{
    /// Every member, component by component, each component ascending.
    members: Box<[Edge]>,
    /// The end of each component's run in `members`, in component order.
    ends: Box<[usize]>,
}

impl Components
{
    /// How many components the diagram's generators fall into.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count(&self) -> ComponentCount
    {
        ComponentCount(self.ends.len())
    }

    /// The members of one component, in ascending position order.
    ///
    /// # Specification
    /// - provides: [`component_lookup::Absent::OutOfRange`] when `component` is
    ///   at or past the count.
    /// - panics: none.
    #[inline]
    pub fn members(
        &self,
        component: ComponentIndex,
    ) -> Maybe<&[Edge], component_lookup::Absent>
    {
        let start = match component.0.checked_sub(1) {
            | Some(previous) => self.ends.get(previous).copied(),
            | None => Some(0),
        };
        let end = self.ends.get(component.0).copied();
        let run = start
            .zip(end)
            .and_then(|(start, end)| self.members.get(start .. end));
        match run {
            | Some(members) => Maybe::Present(members),
            | None => Maybe::Absent(component_lookup::Absent::OutOfRange),
        }
    }
}

/// The acyclicity check: Kahn's algorithm over generators, then a walk back
/// from an unsettled generator to one on a cycle.
///
/// # Specification
/// - requires: `producer` and `consumer` are the incidence maps of
///   `generators`.
/// - ensures: success exactly when every generator settles, which is exactly
///   when the diagram has no directed cycle.
/// - fails: [`WiringObstruction::DirectedCycle`] naming a generator on a cycle:
///   the walk starts at the lowest-positioned unsettled generator and steps to
///   the producer of its first source whose producer is unsettled until it
///   revisits a generator, which is on a cycle. An unsettled generator that
///   only reads a cycle's output is never named.
/// - panics: none.
/// - intension: linear in the diagram's ports.
///
/// # Errors
/// [`WiringObstruction::DirectedCycle`] when a directed cycle exists.
fn check_acyclic(
    generators: &[Generator],
    producer: &BTreeMap<Wire, Edge>,
    consumer: &BTreeMap<Wire, Edge>,
) -> Result<(), WiringObstruction>
{
    let mut waiting: Vec<usize> = Vec::with_capacity(generators.len());
    for generator in generators {
        let count = generator
            .sources
            .iter()
            .filter(|wire| producer.contains_key(*wire))
            .count();
        waiting.push(count);
    }
    let mut ready: Vec<Edge> = Vec::new();
    for (index, count) in waiting.iter().enumerate() {
        if *count == 0 {
            ready.push(Edge(index));
        }
    }
    while let Some(edge) = ready.pop() {
        let Some(generator) = generators.get(edge.0)
        else {
            continue;
        };
        for wire in &generator.targets {
            let Some(next) = consumer.get(wire).copied()
            else {
                continue;
            };
            let Some(count) = waiting.get_mut(next.0)
            else {
                continue;
            };
            *count = count.saturating_sub(1);
            if *count == 0 {
                ready.push(next);
            }
        }
    }
    let Some(start) = waiting.iter().position(|count| *count > 0)
    else {
        return Ok(());
    };
    let mut visited: BTreeSet<Edge> = BTreeSet::new();
    let mut current = Edge(start);
    while visited.insert(current) {
        let Some(generator) = generators.get(current.0)
        else {
            break;
        };
        let unsettled = generator.sources.iter().find_map(|wire| {
            producer
                .get(wire)
                .copied()
                .filter(|edge| waiting.get(edge.0).is_some_and(|count| *count > 0))
        });
        let Some(previous) = unsettled
        else {
            break;
        };
        current = previous;
    }
    Err(WiringObstruction::DirectedCycle { through: current })
}

#[cfg(test)]
mod tests
{
    use super::*;

    /// A value-sorted generator label.
    ///
    /// # Specification
    /// trivial.
    fn value<N>(name: N) -> GeneratorLabel
    where
        N: Into<GeneratorName>,
    {
        GeneratorLabel::new(name, GeneratorSort::Value)
    }

    /// `f: (0) -> (1)` followed by `g: (1) -> (2)`, open at both ends.
    ///
    /// # Specification
    /// trivial.
    fn two_step() -> Result<Wiring, WiringObstruction>
    {
        Wiring::assemble(
            WireCount::from(3),
            alloc::vec![
                Generator::new(value("f"), wires![0], wires![1]),
                Generator::new(value("g"), wires![1], wires![2]),
            ],
            Interface::new(wires![0], wires![2]),
        )
    }

    #[test]
    fn an_assembled_wiring_answers_its_incidence()
    {
        let wiring = two_step().expect("the two-step diagram is monogamous and acyclic");
        assert_eq!(
            EdgeCount::from(2),
            wiring.edge_count(),
            "the diagram holds both generators"
        );
        assert_eq!(
            WireCount::from(3),
            wiring.wire_count(),
            "and declares all three wires"
        );
        assert_eq!(
            Maybe::Absent(wire_producer::Absent::BoundaryInput),
            wiring.producer_of(Wire::from(0)),
            "the input wire is produced by nothing, because it is an input port"
        );
        assert_eq!(
            Maybe::Present(Edge::from(0)),
            wiring.consumer_of(Wire::from(0)),
            "and consumed by the first generator"
        );
        assert_eq!(
            Maybe::Present(Edge::from(0)),
            wiring.producer_of(Wire::from(1)),
            "the middle wire runs from the first generator"
        );
        assert_eq!(
            Maybe::Present(Edge::from(1)),
            wiring.consumer_of(Wire::from(1)),
            "into the second"
        );
        assert_eq!(
            Maybe::Absent(wire_consumer::Absent::BoundaryOutput),
            wiring.consumer_of(Wire::from(2)),
            "and the output wire is consumed by nothing, because it is an output port"
        );
        assert_eq!(
            Maybe::Absent(wire_producer::Absent::OutOfRange),
            wiring.producer_of(Wire::from(3)),
            "a wire past the count is no input port: it is not the diagram's"
        );
        assert_eq!(
            Maybe::Absent(wire_consumer::Absent::OutOfRange),
            wiring.consumer_of(Wire::from(3)),
            "nor an output port"
        );
        assert_eq!(
            Maybe::Absent(generator_lookup::Absent::OutOfRange),
            wiring.generator(Edge::from(2)),
            "and a position past the generator count holds nothing"
        );
    }

    #[test]
    fn the_wiring_refuses_a_fan_in()
    {
        let refusal = Wiring::assemble(
            WireCount::from(3),
            alloc::vec![
                Generator::new(value("f"), wires![0], wires![2]),
                Generator::new(value("g"), wires![1], wires![2]),
            ],
            Interface::new(wires![0, 1], wires![2]),
        )
        .expect_err("in-degree two is the fan-in the fragment excludes");
        assert_eq!(
            WiringObstruction::FanIn {
                wire: Wire::from(2),
                first: Edge::from(0),
                second: Edge::from(1),
            },
            refusal,
            "the refusal names the doubly produced wire and both producers"
        );
    }

    #[test]
    fn the_wiring_refuses_a_fan_out()
    {
        let refusal = Wiring::assemble(
            WireCount::from(3),
            alloc::vec![
                Generator::new(value("f"), wires![0], wires![1]),
                Generator::new(value("g"), wires![0], wires![2]),
            ],
            Interface::new(wires![0], wires![1, 2]),
        )
        .expect_err("out-degree two is the copy the fragment excludes");
        assert_eq!(
            WiringObstruction::FanOut {
                wire: Wire::from(0),
                first: Edge::from(0),
                second: Edge::from(1),
            },
            refusal,
            "the refusal names the copied wire and both consumers"
        );
    }

    #[test]
    fn the_wiring_refuses_an_out_of_range_generator_wire()
    {
        // Both port lists are checked, at the first index past a one-wire
        // diagram: a distant index would leave `<` weakened to `<=` alive.
        let bad_source = Wiring::assemble(
            WireCount::from(1),
            alloc::vec![Generator::new(value("f"), wires![1], wires![0])],
            Interface::default(),
        )
        .expect_err("a source naming an undeclared wire is out of range");
        assert_eq!(
            WiringObstruction::UnknownWire {
                wire: Wire::from(1),
                at: Edge::from(0),
            },
            bad_source,
            "the refusal names the wire and the generator that named it"
        );
        let bad_target = Wiring::assemble(
            WireCount::from(1),
            alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
            Interface::default(),
        )
        .expect_err("and so is a target naming one");
        assert_eq!(
            WiringObstruction::UnknownWire {
                wire: Wire::from(1),
                at: Edge::from(0),
            },
            bad_target,
            "with the target side named the same way"
        );
    }

    #[test]
    fn the_wiring_refuses_an_out_of_range_boundary_wire()
    {
        let bad_input = Wiring::assemble(
            WireCount::from(1),
            Vec::new(),
            Interface::new(wires![1], wires![0]),
        )
        .expect_err("an input port outside the wire range is not a port of this diagram");
        assert_eq!(
            WiringObstruction::UnknownBoundaryWire {
                wire: Wire::from(1)
            },
            bad_input,
            "the refusal names the out-of-range input port"
        );
        let bad_output = Wiring::assemble(
            WireCount::from(1),
            Vec::new(),
            Interface::new(wires![0], wires![1]),
        )
        .expect_err("nor is an output port outside it");
        assert_eq!(
            WiringObstruction::UnknownBoundaryWire {
                wire: Wire::from(1)
            },
            bad_output,
            "and the output leg is checked as well as the input leg"
        );
    }

    #[test]
    fn the_wiring_refuses_a_repeated_port_on_one_generator()
    {
        // One generator naming a wire at two ports is in-degree or out-degree
        // two just as two generators are; the refusal names the one generator
        // twice rather than inventing a second.
        let repeated_source = Wiring::assemble(
            WireCount::from(2),
            alloc::vec![Generator::new(value("f"), wires![0, 0], wires![1])],
            Interface::new(wires![0], wires![1]),
        )
        .expect_err("a wire consumed at two ports of one generator is a copy");
        assert_eq!(
            WiringObstruction::FanOut {
                wire: Wire::from(0),
                first: Edge::from(0),
                second: Edge::from(0),
            },
            repeated_source,
            "the refusal names the one generator as both consumers"
        );
        let repeated_target = Wiring::assemble(
            WireCount::from(2),
            alloc::vec![Generator::new(value("f"), wires![0], wires![1, 1])],
            Interface::new(wires![0], wires![1]),
        )
        .expect_err("and a wire produced at two of its ports is a fan-in");
        assert_eq!(
            WiringObstruction::FanIn {
                wire: Wire::from(1),
                first: Edge::from(0),
                second: Edge::from(0),
            },
            repeated_target,
            "reported the same way on the produced side"
        );
    }

    #[test]
    fn the_wiring_refuses_a_repeated_boundary_port()
    {
        let on_the_input_leg = Wiring::assemble(
            WireCount::from(1),
            Vec::new(),
            Interface::new(wires![0, 0], wires![0]),
        )
        .expect_err("a repeated port is a leg that is not mono");
        assert_eq!(
            WiringObstruction::RepeatedBoundaryPort {
                wire: Wire::from(0)
            },
            on_the_input_leg,
            "the refusal names the repeated port"
        );
        let on_the_output_leg = Wiring::assemble(
            WireCount::from(1),
            Vec::new(),
            Interface::new(wires![0], wires![0, 0]),
        )
        .expect_err("both legs are mono, so the output leg is checked too");
        assert_eq!(
            WiringObstruction::RepeatedBoundaryPort {
                wire: Wire::from(0)
            },
            on_the_output_leg,
            "and the output leg's repeat is refused the same way"
        );
    }

    #[test]
    fn the_wiring_refuses_a_produced_boundary_input()
    {
        let refusal = Wiring::assemble(
            WireCount::from(2),
            alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
            Interface::new(wires![0, 1], wires![1]),
        )
        .expect_err("an input with a producer is not an open port");
        assert_eq!(
            WiringObstruction::BoundaryInputIsProduced {
                wire: Wire::from(1),
                by: Edge::from(0),
            },
            refusal,
            "the refusal names the port and the generator that produces it"
        );
    }

    #[test]
    fn the_wiring_refuses_a_consumed_boundary_output()
    {
        let refusal = Wiring::assemble(
            WireCount::from(2),
            alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
            Interface::new(wires![0], wires![0, 1]),
        )
        .expect_err("an output with a consumer is not an open port");
        assert_eq!(
            WiringObstruction::BoundaryOutputIsConsumed {
                wire: Wire::from(0),
                by: Edge::from(0),
            },
            refusal,
            "the refusal names the port and the generator that consumes it"
        );
    }

    #[test]
    fn the_wiring_refuses_an_undeclared_open_wire()
    {
        let refusal = Wiring::assemble(
            WireCount::from(2),
            alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
            Interface::new(wires![0], Vec::new()),
        )
        .expect_err("an open output the interface does not declare is a lost port");
        assert_eq!(
            WiringObstruction::UndeclaredOutput {
                wire: Wire::from(1)
            },
            refusal,
            "the refusal names the wire the interface would have lost"
        );
    }

    #[test]
    fn the_wiring_refuses_an_undeclared_open_input()
    {
        // The input side carries more than interface honesty: the convexity
        // discharge reads every image input back as the image of a declared
        // input port, so an undeclared open input would be one no connectivity
        // test asked about.
        let refusal = Wiring::assemble(
            WireCount::from(2),
            alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
            Interface::new(Vec::new(), wires![1]),
        )
        .expect_err("an open input the interface does not declare is a lost port");
        assert_eq!(
            WiringObstruction::UndeclaredInput {
                wire: Wire::from(0)
            },
            refusal,
            "the refusal names the wire the interface would have lost"
        );
    }

    #[test]
    fn the_wiring_refuses_a_self_looping_generator()
    {
        // A cycle of length one leaves exactly one generator unsettled, so a
        // settled count compared with anything but equality would admit it.
        let refusal = Wiring::assemble(
            WireCount::from(1),
            alloc::vec![Generator::new(value("f"), wires![0], wires![0])],
            Interface::default(),
        )
        .expect_err("a self-loop leaves the acyclic fragment");
        assert_eq!(
            WiringObstruction::DirectedCycle {
                through: Edge::from(0)
            },
            refusal,
            "the refusal names the generator the one-step cycle runs through"
        );
    }

    #[test]
    fn the_wiring_refuses_a_directed_cycle()
    {
        let refusal = Wiring::assemble(
            WireCount::from(2),
            alloc::vec![
                Generator::new(value("f"), wires![0], wires![1]),
                Generator::new(value("g"), wires![1], wires![0]),
            ],
            Interface::default(),
        )
        .expect_err("a two-generator loop leaves the acyclic fragment");
        assert_eq!(
            WiringObstruction::DirectedCycle {
                through: Edge::from(0)
            },
            refusal,
            "the refusal names a generator the cycle runs through"
        );
        // `h` reads the loop's second output and is listed first. It never
        // settles, and it is not on the cycle: the named generator is.
        let downstream_first = Wiring::assemble(
            WireCount::from(4),
            alloc::vec![
                Generator::new(value("h"), wires![2], wires![3]),
                Generator::new(value("f"), wires![0], wires![1, 2]),
                Generator::new(value("g"), wires![1], wires![0]),
            ],
            Interface::new(Vec::new(), wires![3]),
        )
        .expect_err("a loop with a reader below it leaves the acyclic fragment");
        assert_eq!(
            WiringObstruction::DirectedCycle {
                through: Edge::from(1)
            },
            downstream_first,
            "the named generator is on the cycle, not merely below it"
        );
    }

    #[test]
    fn the_components_partition_the_generators()
    {
        // Validated against the diagram rather than a predicted partition:
        // every position appears in exactly one component, members ascending.
        let wiring = Wiring::assemble(
            WireCount::from(5),
            alloc::vec![
                Generator::new(value("f"), wires![0], wires![1]),
                Generator::new(value("g"), wires![2], wires![3]),
                Generator::new(value("h"), wires![1], wires![4]),
            ],
            Interface::new(wires![0, 2], wires![3, 4]),
        )
        .expect("two components, one of two generators and one of one");
        let components = wiring.components();
        assert_eq!(
            ComponentCount::from(2),
            components.count(),
            "`f` and `h` share wire 1; `g` shares nothing"
        );
        let mut seen: BTreeSet<Edge> = BTreeSet::new();
        for index in 0 .. usize::from(components.count()) {
            let Maybe::Present(members) = components.members(ComponentIndex::from(index))
            else {
                panic!("a component below the count has members");
            };
            assert!(!members.is_empty(), "no component is empty");
            assert!(
                members.is_sorted_by(|left, right| left < right),
                "members are in ascending position order"
            );
            for member in members {
                assert!(seen.insert(*member), "no generator is in two components");
            }
        }
        assert_eq!(
            usize::from(wiring.edge_count()),
            seen.len(),
            "and every generator is in one"
        );
        assert_eq!(
            Maybe::Present(&edges![0, 2][..]),
            components.members(ComponentIndex::from(0)),
            "the first component holds the lowest-positioned generator"
        );
        assert_eq!(
            Maybe::Present(&edges![1][..]),
            components.members(ComponentIndex::from(1)),
            "and the second is the separate one"
        );
        assert_eq!(
            Maybe::Absent(component_lookup::Absent::OutOfRange),
            components.members(ComponentIndex::from(2)),
            "a component index at the count names nothing"
        );
    }

    #[test]
    fn a_component_joins_through_a_shared_wire_in_both_directions()
    {
        // Seeding at position 0 makes exactly one direction load-bearing in
        // each fixture: forwards (a target's consumer) in the first, backwards
        // (a source's producer) in the second.
        let forwards = two_step().expect("the seed's target is the second generator's source");
        assert_eq!(
            ComponentCount::from(1),
            forwards.components().count(),
            "the consumer-of-a-target direction joins them"
        );
        let backwards = Wiring::assemble(
            WireCount::from(3),
            alloc::vec![
                Generator::new(value("g"), wires![1], wires![2]),
                Generator::new(value("f"), wires![0], wires![1]),
            ],
            Interface::new(wires![0], wires![2]),
        )
        .expect("the same diagram with the generators listed the other way round");
        assert_eq!(
            ComponentCount::from(1),
            backwards.components().count(),
            "the producer-of-a-source direction joins them"
        );
    }

    #[test]
    fn a_port_free_generator_is_its_own_component()
    {
        // A point is adjacent to nothing, so it is a singleton component, and
        // two points of one label stay two addressable components.
        let wiring = Wiring::assemble(
            WireCount::from(0),
            alloc::vec![
                Generator::new(value("a"), Vec::new(), Vec::new()),
                Generator::new(value("a"), Vec::new(), Vec::new()),
            ],
            Interface::default(),
        )
        .expect("two port-free generators are a diagram");
        let components = wiring.components();
        assert_eq!(
            ComponentCount::from(2),
            components.count(),
            "equal labels do not make one component"
        );
        assert_eq!(
            Maybe::Present(&edges![0][..]),
            components.members(ComponentIndex::from(0)),
            "each is a singleton"
        );
        assert_eq!(
            Maybe::Present(&edges![1][..]),
            components.members(ComponentIndex::from(1)),
            "in position order"
        );
        let empty = Wiring::assemble(WireCount::from(0), Vec::new(), Interface::default())
            .expect("the empty diagram is a diagram");
        assert_eq!(
            ComponentCount::from(0),
            empty.components().count(),
            "and a diagram with no generator has no component"
        );
    }

    #[test]
    fn a_partial_bijection_stays_injective()
    {
        let mut map = PartialBijection::new();
        assert_eq!(
            Ok(()),
            map.extend(Wire::from(0), Wire::from(7)),
            "the first pair is free"
        );
        assert_eq!(
            Ok(()),
            map.extend(Wire::from(0), Wire::from(7)),
            "and repeating it is idempotent rather than a clash"
        );
        assert_eq!(
            Err(BijectionClash::SourceBound {
                source: Wire::from(0),
                bound: Wire::from(7),
            }),
            map.extend(Wire::from(0), Wire::from(8)),
            "re-binding a source is refused and names where it already goes"
        );
        assert_eq!(
            Err(BijectionClash::ImageBound {
                image: Wire::from(7),
                bound: Wire::from(0),
            }),
            map.extend(Wire::from(1), Wire::from(7)),
            "re-using an image is refused and names what already reaches it"
        );
        assert_eq!(
            PairCount::from(1),
            map.pair_count(),
            "neither refusal left a partial extension behind"
        );
        assert_eq!(
            Maybe::Present(Wire::from(7)),
            map.image_of(Wire::from(0)),
            "the accepted pair is readable forwards"
        );
        assert_eq!(
            Maybe::Present(Wire::from(0)),
            map.preimage_of(Wire::from(7)),
            "and backwards"
        );
        assert_eq!(
            Maybe::Absent(wire_image::Absent::Unmapped),
            map.image_of(Wire::from(1)),
            "the refused source stays unmapped"
        );
        assert_eq!(
            Maybe::Absent(wire_preimage::Absent::Unreached),
            map.preimage_of(Wire::from(8)),
            "and the refused image unreached"
        );
    }
}
