//! Shapes: the carrier's wirings read as graphs, without stick components.
//!
//! A [`Shape`] keeps, per wire, where its two ends attach, and forgets the
//! generator labels, the order of a generator's ports and the order of the
//! interface. Every shape is admitted by [`Wiring::assemble`] and has no stick
//! component: a wire open at both ends is the carrier's identity wire, the unit
//! of contraction, and both constructors refuse it by naming the wire.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::WiringObstruction;

wrapper! {
    /// A shape's size: its vertices plus its wires, the measure the suites
    /// bound and order their cases by.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ShapeSize(usize);
}

wrapper! {
    /// How many points, vertices with no incident wire, a shape holds.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PointCount(usize);
}

/// The most vertices a shape holds: a vertex set is one machine word.
const MAX_VERTICES: usize = 64;

/// Where one end of a wire attaches.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum End
{
    /// The end is open: the wire is a port of the shape at this end.
    Open,
    /// The end attaches to a vertex.
    Vertex(Edge),
}

/// The two ends of one wire: the vertex producing it and the vertex
/// consuming it, either of which may be open.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ends
{
    /// The producing end.
    producer: End,
    /// The consuming end.
    consumer: End,
}

impl Ends
{
    /// The ends of a wire from its producing and consuming end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        producer: End,
        consumer: End,
    ) -> Self
    {
        Self { producer, consumer }
    }

    /// The producing end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn producer(self) -> End
    {
        self.producer
    }

    /// The consuming end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn consumer(self) -> End
    {
        self.consumer
    }

    /// Which of the four kinds of wire these ends make.
    ///
    /// # Specification
    /// - ensures: a stick has both ends open, an input leg only its producer,
    ///   an output leg only its consumer, and an inner wire neither; so the
    ///   kind is a stick or an input leg exactly when the producer is open, and
    ///   a stick or an output leg exactly when the consumer is open.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four combinations of open and attached ends, each
    ///   asserted to its exact kind, and a shape holding one wire of each
    ///   admitted kind counted per kind; a swapped arm changes one assertion.
    /// - witness: `tests::shapes::wire_kinds_follow_the_open_ends`
    #[inline]
    #[must_use]
    #[spec(ensures: |kind| [
        matches!(kind, WireKind::Stick | WireKind::InputLeg) == matches!(self.producer, End::Open),
        matches!(kind, WireKind::Stick | WireKind::OutputLeg) == matches!(self.consumer, End::Open),
    ])]
    pub const fn kind(self) -> WireKind
    {
        match (self.producer, self.consumer) {
            | (End::Open, End::Open) => WireKind::Stick,
            | (End::Open, End::Vertex(_)) => WireKind::InputLeg,
            | (End::Vertex(_), End::Open) => WireKind::OutputLeg,
            | (End::Vertex(_), End::Vertex(_)) => WireKind::Inner,
        }
    }
}

/// The four kinds of wire, by which ends are open.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum WireKind
{
    /// Open at both ends: the identity wire, a stick component on its own,
    /// which no shape holds.
    Stick,
    /// Open at its producing end: an input port of the shape.
    InputLeg,
    /// Open at its consuming end: an output port of the shape.
    OutputLeg,
    /// Attached at both ends.
    Inner,
}

/// Whether a vertex has any incident wire.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum VertexKind
{
    /// No wire attaches to it: the arity-zero corolla's vertex.
    Point,
    /// At least one wire attaches to it.
    Ported,
}

/// Why a shape could not be formed.
///
/// # Specification
/// - provides: the refusal names the vertex count, the wire or the carrier
///   refusal that decided it, so a caller can point at the offending part.
/// - executable: none — a refusal on its own lacks the ends or the wiring it
///   was decided against; the constructors' predicates check each variant
///   against their inputs.
///
/// # Adequacy
/// - hypothesis: L3 — each variant is produced by an input failing only it and
///   asserted with its exact payload, and the precedence between a stick and an
///   absent vertex is observed in both orders.
/// - witness: `tests::shapes::the_constructor_refuses_by_variant`
/// - witness: `tests::shapes::a_stick_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ShapeObstruction
{
    /// More vertices than one vertex set holds.
    TooManyVertices
    {
        /// The vertex count asked for.
        vertices: EdgeCount,
    },
    /// A wire end names a vertex the shape does not have.
    UnknownVertex
    {
        /// The wire whose end names it.
        wire: Wire,
        /// The vertex named.
        vertex: Edge,
    },
    /// A wire is open at both ends: a stick component, the carrier's identity
    /// wire, which is not a shape.
    Stick
    {
        /// The stick.
        wire: Wire,
    },
    /// A generator of the read wiring names a wire the wiring does not
    /// declare, which an assembled wiring never does.
    UnknownWire
    {
        /// The wire named.
        wire: Wire,
    },
    /// The carrier refused the wiring the shape presents.
    Carrier(WiringObstruction),
}

impl fmt::Display for ShapeObstruction
{
    /// Names the refusal.
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
            | Self::TooManyVertices { .. } => f.write_str("more vertices than a vertex set holds"),
            | Self::UnknownVertex { .. } => f.write_str("a wire end names an absent vertex"),
            | Self::Stick { wire } => {
                write!(f, "wire {} is a stick component", usize::from(wire))
            },
            | Self::UnknownWire { .. } => f.write_str("a generator names an undeclared wire"),
            | Self::Carrier(ref refusal) => write!(f, "the carrier refused the shape: {refusal}"),
        }
    }
}

impl core::error::Error for ShapeObstruction
{
}

/// A wiring read as a graph before admission: a vertex count and the ends of
/// each wire, sticks included.
///
/// The site's clauses are stated on graphs; a [`Shape`] is a graph the
/// constructors admitted. The crate keeps this view private, so the only
/// objects on its surface are stick-free.
#[derive(Clone, Copy, Debug)]
pub struct Graph<'data>
{
    /// How many vertices the graph has.
    vertices: EdgeCount,
    /// The ends of each wire, in wire order.
    ends: &'data [Ends],
}

impl<'data> Graph<'data>
{
    /// The graph over `vertices` vertices whose wires have `ends`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        vertices: EdgeCount,
        ends: &'data [Ends],
    ) -> Self
    {
        Self { vertices, ends }
    }

    /// How many vertices the graph has.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn vertex_count(self) -> EdgeCount
    {
        self.vertices
    }

    /// How many wires the graph has.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn wire_count(self) -> WireCount
    {
        WireCount::from(self.ends.len())
    }

    /// The ends of every wire, in wire order.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn ends(self) -> &'data [Ends]
    {
        self.ends
    }

    /// The vertices, in order.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn vertices(self) -> impl Iterator<Item = Edge>
    {
        (0 .. usize::from(self.vertices)).map(Edge::from)
    }
}

/// The ends of every wire of `wiring`, each end the generator that produces
/// or consumes it, sticks included: the graph a wiring presents before
/// admission.
///
/// # Specification
/// - ensures: one entry per declared wire, in wire order; an entry's producer
///   is open exactly when the wire is a boundary input, and its consumer
///   exactly when it is a boundary output.
/// - fails: a generator names an undeclared wire, which an assembled wiring
///   never does.
/// - panics: none.
///
/// # Errors
/// - [`ShapeObstruction::UnknownWire`]: a generator port names a wire past the
///   wiring's count.
///
/// # Adequacy
/// - hypothesis: L3 — a wiring with an inner wire, a leg of each kind and a
///   port-free generator reads to the ends written by hand; a bare wire reads
///   as a stick, observed through the constructor's refusal and the negatives,
///   which read their sticks this way.
/// - witness: `tests::shapes::a_wiring_reads_back_as_its_shape`
/// - witness: `tests::shapes::a_stick_is_refused_by_name`
/// - witness: `negatives::sticks_as_objects_admit_no_degree`
#[spec(ensures: |ref result| match *result {
    Ok(ref ends) => ends.len() == usize::from(wiring.wire_count())
        && ends.iter().enumerate().all(|entry| {
            let wire = Wire::from(entry.0);
            matches!(entry.1.producer, End::Open) == wiring.boundary().inputs().contains(&wire)
                && matches!(entry.1.consumer, End::Open) == wiring.boundary().outputs().contains(&wire)
        }),
    Err(ShapeObstruction::UnknownWire { wire }) => usize::from(wire) >= usize::from(wiring.wire_count()),
    Err(_) => false,
})]
pub fn presented(wiring: &Wiring) -> Result<Vec<Ends>, ShapeObstruction>
{
    let mut ends = vec![Ends::new(End::Open, End::Open); usize::from(wiring.wire_count())];
    for (index, generator) in wiring.generators().iter().enumerate() {
        let vertex = End::Vertex(Edge::from(index));
        for wire in generator.sources().iter().copied() {
            let slot = ends
                .get_mut(usize::from(wire))
                .ok_or(ShapeObstruction::UnknownWire { wire })?;
            slot.consumer = vertex;
        }
        for wire in generator.targets().iter().copied() {
            let slot = ends
                .get_mut(usize::from(wire))
                .ok_or(ShapeObstruction::UnknownWire { wire })?;
            slot.producer = vertex;
        }
    }
    Ok(ends)
}

/// The first stick among `ends`, in wire order.
///
/// # Specification
/// - ensures: `Err` names the least wire whose ends are both open; `Ok` when
///   there is none.
/// - fails: a stick component.
/// - panics: none.
///
/// # Errors
/// - [`ShapeObstruction::Stick`]: the first stick.
///
/// # Adequacy
/// - hypothesis: L3 — a lone stick, a stick after a corolla's legs and two
///   sticks, asserted by the wire named, separate a missed stick and a later
///   one named first.
/// - witness: `tests::shapes::a_stick_is_refused_by_name`
#[spec(ensures: |result| match result {
    Ok(()) => ends.iter().all(|wire| wire.kind() != WireKind::Stick),
    Err(ShapeObstruction::Stick { wire }) => ends.get(usize::from(wire)).is_some_and(|stick| stick.kind() == WireKind::Stick)
        && ends.iter().take(usize::from(wire)).all(|earlier| earlier.kind() != WireKind::Stick),
    Err(_) => false,
})]
fn refuse_sticks(ends: &[Ends]) -> Result<(), ShapeObstruction>
{
    match ends.iter().position(|wire| wire.kind() == WireKind::Stick) {
        | Some(index) => Err(ShapeObstruction::Stick {
            wire: Wire::from(index),
        }),
        | None => Ok(()),
    }
}

/// A shape: the graph one carrier wiring presents, with no stick component.
/// The default is the empty shape `∅`, the external product's unit.
///
/// # Specification
/// - ensures: no wire is open at both ends, every vertex an end names is below
///   the vertex count, and the wiring [`Shape::to_wiring`] presents is admitted
///   by [`Wiring::assemble`].
/// - provides: the objects of the site.
/// - panics: none.
/// - executable: none — a type carries no runtime predicate; every
///   constructor's postcondition checks the invariant on the value it returns.
///
/// # Adequacy
/// - hypothesis: L2 — the per-size class counts of the enumeration are pinned
///   against counts derived from an independent enumerator, and every
///   constructor refusal, the stick among them, is observed by its variant.
/// - witness: `tests::shapes::the_enumeration_counts_match_an_independent_count`
/// - witness: `tests::shapes::the_constructor_refuses_by_variant`
/// - witness: `tests::shapes::a_stick_is_refused_by_name`
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Shape
{
    /// How many vertices the shape has.
    vertices: EdgeCount,
    /// The ends of each wire, in wire order.
    ends: Box<[Ends]>,
}

/// A shape's isomorphism class: the least relabelling of its wire ends over
/// all orders of its vertices.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ShapeKey
{
    /// How many vertices the class's shapes have.
    vertices: EdgeCount,
    /// The sorted wire ends under the least vertex order.
    ends: Box<[Ends]>,
}

impl Shape
{
    /// The shape a list of wire ends presents, admitted by the carrier.
    ///
    /// # Specification
    /// - ensures: on success the shape holds exactly `vertices` and `ends`.
    /// - fails: more than 64 vertices; then, wire by wire in order, an end
    ///   naming a vertex at or past `vertices` or a wire open at both ends;
    ///   last, a wiring the carrier refuses, which for a list of ends is a
    ///   directed cycle.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeObstruction::TooManyVertices`]: `vertices` exceeds 64.
    /// - [`ShapeObstruction::UnknownVertex`]: an end names an absent vertex.
    /// - [`ShapeObstruction::Stick`]: a wire is open at both ends.
    /// - [`ShapeObstruction::Carrier`]: the carrier refused the wiring.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one input per refusal asserted with its payload, the
    ///   absent vertex and the stick each placed before the other, and an
    ///   admitted shape read back unchanged.
    /// - witness: `tests::shapes::the_constructor_refuses_by_variant`
    /// - witness: `tests::shapes::a_stick_is_refused_by_name`
    /// - witness: `tests::shapes::a_wiring_reads_back_as_its_shape`
    #[inline]
    #[spec(captures: [given = ends.clone()], ensures: |ref result| match *result {
        Ok(ref shape) => shape.vertices == vertices && *shape.ends == *given.as_slice()
            && shape.ends.iter().all(|wire| wire.kind() != WireKind::Stick),
        Err(ShapeObstruction::TooManyVertices { vertices: asked }) => asked == vertices && usize::from(asked) > MAX_VERTICES,
        Err(ShapeObstruction::UnknownVertex { wire, vertex }) => usize::from(vertex) >= usize::from(vertices)
            && given.get(usize::from(wire)).is_some_and(|named| named.producer == End::Vertex(vertex) || named.consumer == End::Vertex(vertex)),
        Err(ShapeObstruction::Stick { wire }) => given.get(usize::from(wire)).is_some_and(|named| named.kind() == WireKind::Stick),
        Err(ShapeObstruction::Carrier(refusal)) => matches!(refusal, WiringObstruction::DirectedCycle { .. }),
        Err(ShapeObstruction::UnknownWire { .. }) => false,
    })]
    pub fn from_ends(
        vertices: EdgeCount,
        ends: Vec<Ends>,
    ) -> Result<Self, ShapeObstruction>
    {
        if usize::from(vertices) > MAX_VERTICES {
            return Err(ShapeObstruction::TooManyVertices { vertices });
        }
        for (index, wire_ends) in ends.iter().enumerate() {
            let wire = Wire::from(index);
            for end in [wire_ends.producer, wire_ends.consumer] {
                if let End::Vertex(vertex) = end
                    && usize::from(vertex) >= usize::from(vertices)
                {
                    return Err(ShapeObstruction::UnknownVertex { wire, vertex });
                }
            }
            if wire_ends.kind() == WireKind::Stick {
                return Err(ShapeObstruction::Stick { wire });
            }
        }
        let shape = Self {
            vertices,
            ends: ends.into_boxed_slice(),
        };
        shape.to_wiring().map_err(ShapeObstruction::Carrier)?;
        Ok(shape)
    }

    /// The shape a carrier wiring presents.
    ///
    /// # Specification
    /// - ensures: one vertex per generator in generator order, one wire per
    ///   declared wire in wire order, each end the generator that produces or
    ///   consumes it.
    /// - fails: more than 64 generators, or a wire that is both a boundary
    ///   input and a boundary output, a bare wire with no operation on it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeObstruction::TooManyVertices`]: the wiring holds more
    ///   generators than a vertex set holds.
    /// - [`ShapeObstruction::Stick`]: the first wire no generator touches.
    /// - [`ShapeObstruction::UnknownWire`]: a generator names an undeclared
    ///   wire, which an assembled wiring never does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wiring with an inner wire, a leg of each kind and a
    ///   port-free generator reads back to the ends written by hand; the
    ///   identity wire and a corolla beside it are refused at their stick, and
    ///   a wiring of 65 generators by its count.
    /// - witness: `tests::shapes::a_wiring_reads_back_as_its_shape`
    /// - witness: `tests::shapes::a_stick_is_refused_by_name`
    /// - witness: `tests::shapes::the_constructor_refuses_by_variant`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(ref shape) => shape.vertices == wiring.edge_count()
            && shape.ends.len() == usize::from(wiring.wire_count())
            && shape.ends.iter().all(|wire| wire.kind() != WireKind::Stick),
        Err(ShapeObstruction::TooManyVertices { vertices }) => vertices == wiring.edge_count()
            && usize::from(vertices) > MAX_VERTICES,
        Err(ShapeObstruction::Stick { wire }) => wiring.boundary().inputs().contains(&wire)
            && wiring.boundary().outputs().contains(&wire),
        Err(_) => false,
    })]
    pub fn read(wiring: &Wiring) -> Result<Self, ShapeObstruction>
    {
        let vertices = wiring.edge_count();
        if usize::from(vertices) > MAX_VERTICES {
            return Err(ShapeObstruction::TooManyVertices { vertices });
        }
        let ends = presented(wiring)?;
        refuse_sticks(&ends)?;
        Ok(Self {
            vertices,
            ends: ends.into_boxed_slice(),
        })
    }

    /// The carrier wiring presenting this shape, every generator labelled
    /// alike.
    ///
    /// # Specification
    /// - ensures: as [`Shape::to_labelled_wiring`] with one label for every
    ///   vertex, so the wiring reads back as this shape.
    /// - fails: the carrier's refusal, verbatim.
    /// - panics: none.
    ///
    /// # Errors
    /// Any [`WiringObstruction`] [`Wiring::assemble`] returns; a directed
    /// cycle is the one a list of ends can present.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reading the presented wiring back gives the shape,
    ///   and a self-loop is refused by the carrier's cycle refusal.
    /// - witness: `tests::shapes::a_wiring_reads_back_as_its_shape`
    /// - witness: `tests::shapes::the_constructor_refuses_by_variant`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |wiring| presented(wiring).is_ok_and(|ends| *ends == *self.ends)))]
    pub fn to_wiring(&self) -> Result<Wiring, WiringObstruction>
    {
        self.to_labelled_wiring(|_| GeneratorLabel::new("v", GeneratorSort::Value))
    }

    /// The carrier wiring presenting this shape, vertex `v` labelled
    /// `label(v)`.
    ///
    /// # Specification
    /// - ensures: generator `v` carries `label(v)`, consumes in wire order the
    ///   wires whose consumer is `v`, and produces those whose producer is `v`;
    ///   the interface lists the wires open at their producer as inputs and
    ///   those open at their consumer as outputs, in wire order.
    /// - fails: the carrier's refusal, verbatim.
    /// - panics: none.
    ///
    /// # Errors
    /// Any [`WiringObstruction`] [`Wiring::assemble`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Shape::to_wiring`], and the labelled scalars of
    ///   the units suite read their labels back.
    /// - witness: `tests::shapes::a_wiring_reads_back_as_its_shape`
    /// - witness: `tests::units::scalars_are_counted_and_labelled`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |wiring| {
        wiring.edge_count() == self.vertices
            && usize::from(wiring.wire_count()) == self.ends.len()
            && wiring.boundary().inputs().len() == self.ends.iter().filter(|wire| wire.producer == End::Open).count()
            && wiring.boundary().outputs().len() == self.ends.iter().filter(|wire| wire.consumer == End::Open).count()
    }))]
    pub fn to_labelled_wiring<Label>(
        &self,
        label: Label,
    ) -> Result<Wiring, WiringObstruction>
    where
        Label: Fn(Edge) -> GeneratorLabel,
    {
        let mut generators: Vec<Generator> = Vec::with_capacity(usize::from(self.vertices));
        for vertex in self.vertices() {
            let sources: Vec<Wire> = self.wires_where(|ends| ends.consumer == End::Vertex(vertex));
            let targets: Vec<Wire> = self.wires_where(|ends| ends.producer == End::Vertex(vertex));
            generators.push(Generator::new(label(vertex), sources, targets));
        }
        let inputs: Vec<Wire> = self.wires_where(|ends| ends.producer == End::Open);
        let outputs: Vec<Wire> = self.wires_where(|ends| ends.consumer == End::Open);
        Wiring::assemble(
            WireCount::from(self.ends.len()),
            generators,
            Interface::new(inputs, outputs),
        )
    }

    /// The wires whose ends satisfy `keep`, in wire order.
    ///
    /// # Specification
    /// trivial.
    fn wires_where<Keep>(
        &self,
        keep: Keep,
    ) -> Vec<Wire>
    where
        Keep: Fn(&Ends) -> bool,
    {
        self.ends
            .iter()
            .enumerate()
            .filter(|entry| keep(entry.1))
            .map(|entry| Wire::from(entry.0))
            .collect()
    }

    /// The shape as a graph, the form the site's clauses are stated on.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn graph(&self) -> Graph<'_>
    {
        Graph::new(self.vertices, &self.ends)
    }

    /// How many vertices the shape has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn vertex_count(&self) -> EdgeCount
    {
        self.vertices
    }

    /// How many wires the shape has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn wire_count(&self) -> WireCount
    {
        WireCount::from(self.ends.len())
    }

    /// The ends of every wire, in wire order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ends(&self) -> &[Ends]
    {
        &self.ends
    }

    /// The vertices, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn vertices(&self) -> impl Iterator<Item = Edge>
    {
        (0 .. usize::from(self.vertices)).map(Edge::from)
    }

    /// The shape's size: vertices plus wires.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn size(&self) -> ShapeSize
    {
        ShapeSize(usize::from(self.vertices).saturating_add(self.ends.len()))
    }

    /// Whether `vertex` has an incident wire.
    ///
    /// # Specification
    /// - ensures: [`VertexKind::Point`] exactly when no end names `vertex`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point among ported vertices, a vertex touched only
    ///   by an output and a shape of points alone, each asserted to its kind or
    ///   count, separate the two arms.
    /// - witness: `tests::shapes::points_are_the_vertices_no_wire_touches`
    #[inline]
    #[must_use]
    #[spec(ensures: |kind| (kind == VertexKind::Point) == self.ends.iter().all(|ends| {
        ends.producer != End::Vertex(vertex) && ends.consumer != End::Vertex(vertex)
    }))]
    pub fn vertex_kind(
        &self,
        vertex: Edge,
    ) -> VertexKind
    {
        let touched = self.ends.iter().any(|ends| {
            ends.producer == End::Vertex(vertex) || ends.consumer == End::Vertex(vertex)
        });
        if touched {
            VertexKind::Ported
        }
        else {
            VertexKind::Point
        }
    }

    /// The points, in vertex order.
    ///
    /// # Specification
    /// - ensures: exactly the vertices of kind [`VertexKind::Point`], least
    ///   first; with the vertices some end names they make up every vertex.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Shape::vertex_kind`]: a point among ported
    ///   vertices is listed alone, three points are listed together, and a
    ///   corolla has none.
    /// - witness: `tests::shapes::points_are_the_vertices_no_wire_touches`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref points| [
        points.is_sorted(),
        points.iter().all(|point| self.vertex_kind(*point) == VertexKind::Point),
        points.len().saturating_add(self.ends.iter()
            .flat_map(|ends| [ends.producer, ends.consumer])
            .filter_map(|end| match end { End::Open => None, End::Vertex(vertex) => Some(vertex) })
            .collect::<BTreeSet<Edge>>().len()) == usize::from(self.vertices),
    ])]
    pub fn points(&self) -> Vec<Edge>
    {
        self.vertices()
            .filter(|vertex| self.vertex_kind(*vertex) == VertexKind::Point)
            .collect()
    }

    /// How many points the shape holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn point_count(&self) -> PointCount
    {
        PointCount(self.points().len())
    }

    /// How many wires of `kind` the shape has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count_of(
        &self,
        kind: WireKind,
    ) -> WireCount
    {
        WireCount::from(self.ends.iter().filter(|ends| ends.kind() == kind).count())
    }

    /// The point-free core: the shape with its points removed and the other
    /// vertices renumbered in order.
    ///
    /// # Specification
    /// - ensures: the core has no point, the same wires in the same order, and
    ///   as many vertices as the shape has ported vertices.
    /// - fails: the carrier's refusal, which a sub-shape of an admitted shape
    ///   never meets.
    /// - panics: none.
    ///
    /// # Errors
    /// Any [`ShapeObstruction`] [`Shape::from_ends`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every shape at the bound is checked to be its core
    ///   beside its points, and no other point-free shape is; a corolla beside
    ///   two points has the corolla as its core.
    /// - witness: `tests::point_count::every_shape_is_its_core_beside_its_points`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().is_ok_and(|core| {
        usize::from(core.point_count()) == 0
            && core.ends.len() == self.ends.len()
            && core.ends.iter().zip(self.ends.iter()).all(|pair| pair.0.kind() == pair.1.kind())
            && usize::from(core.vertices).saturating_add(usize::from(self.point_count())) == usize::from(self.vertices)
    }))]
    pub fn core(&self) -> Result<Self, ShapeObstruction>
    {
        let mut renumbered: BTreeMap<Edge, Edge> = BTreeMap::new();
        for vertex in self.vertices() {
            if self.vertex_kind(vertex) == VertexKind::Ported {
                let next = Edge::from(renumbered.len());
                renumbered.insert(vertex, next);
            }
        }
        let rename = |end: End| match end {
            | End::Open => End::Open,
            | End::Vertex(vertex) => {
                End::Vertex(renumbered.get(&vertex).copied().unwrap_or(vertex))
            },
        };
        let ends: Vec<Ends> = self
            .ends
            .iter()
            .map(|ends| Ends::new(rename(ends.producer), rename(ends.consumer)))
            .collect();
        Self::from_ends(EdgeCount::from(renumbered.len()), ends)
    }

    /// The shape beside `count` further points, numbered after its own
    /// vertices.
    ///
    /// # Specification
    /// - ensures: the same wires, and `count` more vertices, none touched.
    /// - fails: the result would exceed 64 vertices.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeObstruction::TooManyVertices`]: the shape's vertices and
    ///   `count` exceed 64.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Shape::core`], whose decomposition check
    ///   rebuilds every shape this way; L3 — a corolla beside two points keys
    ///   as the hand-built shape, and sixty-five points are refused by count.
    /// - witness: `tests::point_count::every_shape_is_its_core_beside_its_points`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(ref whole) => *whole.ends == *self.ends
            && usize::from(whole.vertices) == usize::from(self.vertices).saturating_add(usize::from(count))
            && usize::from(whole.point_count()) == usize::from(self.point_count()).saturating_add(usize::from(count)),
        Err(ShapeObstruction::TooManyVertices { vertices }) => usize::from(vertices) > MAX_VERTICES
            && usize::from(vertices) == usize::from(self.vertices).saturating_add(usize::from(count)),
        Err(_) => false,
    })]
    pub fn beside_points(
        &self,
        count: PointCount,
    ) -> Result<Self, ShapeObstruction>
    {
        let vertices = usize::from(self.vertices).saturating_add(count.0);
        Self::from_ends(EdgeCount::from(vertices), self.ends.to_vec())
    }

    /// The shape's isomorphism class.
    ///
    /// # Specification
    /// - ensures: two shapes have equal keys exactly when a bijection of
    ///   vertices carries one multiset of wire ends onto the other; the key
    ///   keeps the vertex count and the multiset of wire kinds, its ends are
    ///   sorted, and they are no greater than the shape's own ends sorted.
    /// - panics: none.
    /// - intension: tries every order of the vertices, so the cost is the
    ///   vertex count's factorial times the wires' sorting cost.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the per-size class counts the enumeration reaches by
    ///   deduplicating on keys are pinned against counts derived from an
    ///   independent enumerator; L3 — a relabelled presentation keys alike and
    ///   a moved leg keys apart.
    /// - witness: `tests::shapes::the_enumeration_counts_match_an_independent_count`
    /// - witness: `tests::shapes::a_relabelled_shape_keys_alike`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref key| [
        key.vertices == self.vertices,
        key.ends.is_sorted(),
        {
            let mut own: Vec<Ends> = self.ends.to_vec();
            own.sort_unstable();
            *key.ends <= *own
        },
        {
            let mut kinds: Vec<WireKind> = key.ends.iter().map(|wire| wire.kind()).collect();
            let mut own: Vec<WireKind> = self.ends.iter().map(|wire| wire.kind()).collect();
            kinds.sort_unstable();
            own.sort_unstable();
            kinds == own
        },
    ])]
    pub fn key(&self) -> ShapeKey
    {
        let vertices = usize::from(self.vertices);
        let relabel = |order: &[usize]| -> Box<[Ends]> {
            let rename = |end: End| match end {
                | End::Open => End::Open,
                | End::Vertex(vertex) => End::Vertex(Edge::from(
                    order.get(usize::from(vertex)).copied().unwrap_or(0),
                )),
            };
            let mut ends: Vec<Ends> = self
                .ends
                .iter()
                .map(|ends| Ends::new(rename(ends.producer), rename(ends.consumer)))
                .collect();
            ends.sort_unstable();
            ends.into_boxed_slice()
        };
        let mut order: Vec<usize> = (0 .. vertices).collect();
        let mut best = relabel(&order);
        let mut counters: Vec<usize> = vec![0; vertices];
        let mut level: usize = 1;
        while level < vertices {
            let counter = counters.get(level).copied().unwrap_or(level);
            if counter < level {
                if level.is_multiple_of(2) {
                    order.swap(0, level);
                }
                else {
                    order.swap(counter, level);
                }
                let candidate = relabel(&order);
                if candidate < best {
                    best = candidate;
                }
                if let Some(slot) = counters.get_mut(level) {
                    *slot = counter.saturating_add(1);
                }
                level = 1;
            }
            else {
                if let Some(slot) = counters.get_mut(level) {
                    *slot = 0;
                }
                level = level.saturating_add(1);
            }
        }
        ShapeKey {
            vertices: self.vertices,
            ends: best,
        }
    }
}

impl fmt::Display for Shape
{
    /// Writes the vertex count and each wire as producer to consumer, an
    /// open end written `·`: `[2v; ·→0, 0→1]`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "[{}v;", usize::from(self.vertices))?;
        for (index, ends) in self.ends.iter().enumerate() {
            let separator = if index == 0 { " " } else { ", " };
            write!(
                f,
                "{separator}{}→{}",
                EndLabel(ends.producer),
                EndLabel(ends.consumer)
            )?;
        }
        f.write_str("]")
    }
}

/// One end, written as its vertex number or `·` when open.
#[repr(transparent)]
struct EndLabel(End);

impl fmt::Display for EndLabel
{
    /// Writes the vertex number, or `·` for an open end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            | End::Open => f.write_str("·"),
            | End::Vertex(vertex) => write!(f, "{}", usize::from(vertex)),
        }
    }
}

/// Every shape of size at most `bound`, one per isomorphism class, ordered by
/// size and then by key.
///
/// # Specification
/// - ensures: each class of stick-free shapes the carrier admits with at most
///   `bound` vertices plus wires appears exactly once, in strictly increasing
///   order of size and then key.
/// - fails: a bound past 64 vertices.
/// - panics: none.
/// - intension: every multiset of non-stick wire ends over `v` vertices is
///   presented to the carrier, which refuses the cyclic ones; the survivors are
///   deduplicated on [`Shape::key`].
///
/// # Errors
/// - [`ShapeObstruction::TooManyVertices`]: the bound reaches 65 vertices.
///
/// # Adequacy
/// - hypothesis: L2 — the class counts for bounds zero to six (1, 2, 5, 12, 31,
///   81, 223) are derived from an independent enumerator's counts of all
///   shapes, sticks included (1, 3, 8, 20, 51, 132, 355): a shape is a
///   stick-free shape beside its sticks, so the stick-free classes of size at
///   most `n` are as many as all classes of size exactly `n`. A lost, doubled
///   or stick-bearing class changes a count.
/// - witness: `tests::shapes::the_enumeration_counts_match_an_independent_count`
#[inline]
#[spec(ensures: |ref result| match *result {
    Ok(ref shapes) => shapes.iter().all(|shape| shape.size() <= bound && shape.count_of(WireKind::Stick) == WireCount::from(0_usize))
        && shapes.iter().zip(shapes.iter().skip(1)).all(|pair| (pair.0.size(), pair.0.key()) < (pair.1.size(), pair.1.key())),
    Err(ShapeObstruction::TooManyVertices { vertices }) => usize::from(vertices) > MAX_VERTICES && usize::from(vertices) <= usize::from(bound),
    Err(_) => false,
})]
pub fn shapes_up_to(bound: ShapeSize) -> Result<Vec<Shape>, ShapeObstruction>
{
    let mut classes: BTreeMap<ShapeKey, Shape> = BTreeMap::new();
    for vertices in 0 ..= bound.0 {
        let wires = bound.0.saturating_sub(vertices);
        let kinds = end_pairs(EdgeCount::from(vertices));
        for width in 0 ..= wires {
            let mut cursor: Vec<usize> = vec![0; width];
            loop {
                let ends: Vec<Ends> = cursor
                    .iter()
                    .filter_map(|kind| kinds.get(*kind).copied())
                    .collect();
                match Shape::from_ends(EdgeCount::from(vertices), ends) {
                    | Ok(shape) => {
                        classes.entry(shape.key()).or_insert(shape);
                    },
                    | Err(ShapeObstruction::Carrier(WiringObstruction::DirectedCycle {
                        ..
                    })) => {},
                    | Err(refusal) => return Err(refusal),
                }
                let Some(position) = cursor
                    .iter()
                    .rposition(|kind| kind.saturating_add(1) < kinds.len())
                else {
                    break;
                };
                let next = cursor.get(position).copied().unwrap_or(0).saturating_add(1);
                for slot in cursor.iter_mut().skip(position) {
                    *slot = next;
                }
            }
        }
    }
    let mut shapes: Vec<Shape> = classes.into_values().collect();
    shapes.sort_by_cached_key(|shape| (shape.size(), shape.key()));
    Ok(shapes)
}

/// Every pair of ends over `vertices` vertices except a stick and a vertex
/// feeding itself.
///
/// # Specification
/// - ensures: each pair of ends whose producer or consumer is a vertex, other
///   than a vertex to itself, once: `(v + 1)² − v − 1` pairs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the enumeration built on these pairs is pinned per bound
///   against the derived independent counts; a pair lost or a stick kept
///   changes a count.
/// - witness: `tests::shapes::the_enumeration_counts_match_an_independent_count`
#[spec(ensures: |ref pairs| [
    pairs.iter().all(|pair| pair.kind() != WireKind::Stick
        && !matches!((pair.producer, pair.consumer), (End::Vertex(left), End::Vertex(right)) if left == right)),
    pairs.len() == usize::from(vertices).saturating_add(1).saturating_pow(2).saturating_sub(usize::from(vertices)).saturating_sub(1),
])]
fn end_pairs(vertices: EdgeCount) -> Vec<Ends>
{
    let ends: Vec<End> = core::iter::once(End::Open)
        .chain((0 .. usize::from(vertices)).map(|vertex| End::Vertex(Edge::from(vertex))))
        .collect();
    let mut pairs: Vec<Ends> = Vec::new();
    for producer in ends.iter().copied() {
        for consumer in ends.iter().copied() {
            let self_loop = matches!((producer, consumer), (End::Vertex(left), End::Vertex(right)) if left == right);
            let stick = producer == End::Open && consumer == End::Open;
            if !self_loop && !stick {
                pairs.push(Ends::new(producer, consumer));
            }
        }
    }
    pairs
}
