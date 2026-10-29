//! Diagrams over a shape: a cell at each vertex, whose boundary colours the
//! vertex's legs, and the check that the cells meet along the inner wires.
//!
//! A diagram over a shape holds one cell per vertex, in vertex order. A cell's
//! [`Boundary`] lists a colour for each input leg and each output leg of its
//! vertex, each side in the shape's wire order, as a [`Labelling`] reads the
//! legs. On a chain the colours are the objects a 1-cell runs between, and an
//! inner wire is the object two composable cells share. [`fills`] admits a
//! diagram when each cell has its vertex's profile and, along each inner
//! wire, the producer's colour and the consumer's colour are alike. The
//! caller compares colours, so a checker compares its objects by its own
//! conversion. [`fills`] answers the diagram's own boundary: the colours at
//! the shape's open wires, the source and target of the composite. A diagram
//! it refuses is named by its first defect as [`Unfilled`].
//!
//! [`Labelling`]: crate::Labelling

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Wire;

use crate::shape::End;
use crate::shape::Shape;
use crate::stratum::Legs;
use crate::stratum::PortCount;
use crate::stratum::Profile;

/// A cell's boundary: the colour of each input leg and each output leg of the
/// vertex it fills, each side in the shape's wire order.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Boundary<Colour>
{
    /// The input legs' colours.
    inputs: Vec<Colour>,
    /// The output legs' colours.
    outputs: Vec<Colour>,
}

impl<Colour> Boundary<Colour>
{
    /// The boundary with `inputs` and `outputs`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        inputs: Vec<Colour>,
        outputs: Vec<Colour>,
    ) -> Self
    {
        Self { inputs, outputs }
    }

    /// The input legs' colours.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn inputs(&self) -> &[Colour]
    {
        &self.inputs
    }

    /// The output legs' colours.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn outputs(&self) -> &[Colour]
    {
        &self.outputs
    }

    /// The profile the boundary makes: its input and output colour counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn profile(&self) -> Profile
    {
        Profile {
            inputs: PortCount::from(self.inputs.len()),
            outputs: PortCount::from(self.outputs.len()),
        }
    }
}

/// Why a diagram does not fill a shape.
///
/// # Specification
/// - provides: the refusal names the cell count, the vertex or the wire that
///   decided it.
/// - executable: none — a refusal on its own lacks the shape and the cells;
///   [`fills`]'s predicate checks each variant against them.
///
/// # Adequacy
/// - hypothesis: L3 — each variant is produced by a diagram failing only it and
///   asserted with its exact payload.
/// - witness: `tests::chains::a_diagram_that_does_not_fill_its_chain_is_named`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Unfilled
{
    /// The diagram holds another number of cells than the shape has vertices.
    Cells
    {
        /// The shape's vertex count.
        vertices: EdgeCount,
        /// The diagram's cell count.
        cells: EdgeCount,
    },
    /// A cell has another profile than its vertex.
    Profile
    {
        /// The vertex.
        vertex: Edge,
        /// The vertex's profile.
        expected: Profile,
        /// The cell's profile.
        found: Profile,
    },
    /// An inner wire's producer and consumer colour it apart.
    Wire
    {
        /// The wire.
        wire: Wire,
    },
}

impl fmt::Display for Unfilled
{
    /// Names the defect.
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
            Self::Cells { vertices, cells } => write!(
                f,
                "the diagram holds {} cells over {} vertices",
                usize::from(cells),
                usize::from(vertices)
            ),
            Self::Profile { vertex, .. } => write!(
                f,
                "the cell at vertex {} has another profile than its vertex",
                usize::from(vertex)
            ),
            Self::Wire { wire } => write!(
                f,
                "the cells colour wire {} apart at its two ends",
                usize::from(wire)
            ),
        }
    }
}

impl core::error::Error for Unfilled
{
}

/// Whether `cells`, one per vertex of `shape`, fill it, with their boundary.
///
/// # Specification
/// - ensures: on success, one cell per vertex, each with its vertex's profile,
///   the two colours of each inner wire `alike`, and the answer the colours at
///   the open wires in wire order: an open input's consumer colour and an open
///   output's producer colour.
/// - fails: the cell count first, then the first vertex whose cell has another
///   profile, then the first inner wire whose producer's colour and consumer's
///   colour are not `alike`.
/// - panics: none.
/// - intension: one pass over the vertices' legs and one over the wires.
///
/// # Errors
/// - [`Unfilled::Cells`]: the cell count differs from the vertex count.
/// - [`Unfilled::Profile`]: a cell's leg counts differ from its vertex's.
/// - [`Unfilled::Wire`]: an inner wire's two colours are not `alike`.
///
/// # Adequacy
/// - hypothesis: L3 — the 3-chain filled by three composable cells answers
///   their outer objects; a cell short, a cell of another profile and a middle
///   object that disagrees are each refused with their payload.
/// - witness: `tests::chains::a_composable_diagram_fills_its_chain`
/// - witness: `tests::chains::a_diagram_that_does_not_fill_its_chain_is_named`
#[inline]
#[spec(ensures: |ref result| match *result {
    Ok(ref boundary) => cells.len() == usize::from(shape.vertex_count())
        && boundary.inputs.len() == shape.ends().iter().filter(|ends| ends.producer() == End::Open).count()
        && boundary.outputs.len() == shape.ends().iter().filter(|ends| ends.consumer() == End::Open).count(),
    Err(Unfilled::Cells { vertices, cells: count }) => vertices == shape.vertex_count()
        && usize::from(count) == cells.len() && count != vertices,
    Err(Unfilled::Profile { vertex, expected, found }) => expected != found
        && cells.get(usize::from(vertex)).is_some_and(|cell| cell.profile() == found),
    Err(Unfilled::Wire { wire }) => shape.ends().get(usize::from(wire))
        .is_some_and(|ends| ends.producer() != End::Open && ends.consumer() != End::Open),
})]
pub fn fills<'cells, Colour, Alike>(
    shape: &Shape,
    cells: &'cells [Boundary<Colour>],
    mut alike: Alike,
) -> Result<Boundary<&'cells Colour>, Unfilled>
where
    Alike: FnMut(&Colour, &Colour) -> bool,
{
    if cells.len() != usize::from(shape.vertex_count()) {
        return Err(Unfilled::Cells {
            vertices: shape.vertex_count(),
            cells: EdgeCount::from(cells.len()),
        });
    }
    let wires = shape.ends().len();
    let mut consumed: Vec<Option<&Colour>> = vec![None; wires];
    let mut produced: Vec<Option<&Colour>> = vec![None; wires];
    for (vertex, cell) in shape.vertices().zip(cells) {
        let legs = Legs::of(shape, vertex);
        let (expected, found) = (legs.profile(), cell.profile());
        if expected != found {
            return Err(Unfilled::Profile {
                vertex,
                expected,
                found,
            });
        }
        for (side, colours, slots) in [
            (legs.inputs(), &cell.inputs, &mut consumed),
            (legs.outputs(), &cell.outputs, &mut produced),
        ] {
            for (wire, colour) in side.iter().zip(colours) {
                if let Some(slot) = slots.get_mut(usize::from(*wire)) {
                    *slot = Some(colour);
                }
            }
        }
    }
    let mut boundary = Boundary::new(Vec::new(), Vec::new());
    for (index, ends) in produced.into_iter().zip(consumed).enumerate() {
        match ends {
            (Some(left), Some(right)) => {
                if !alike(left, right) {
                    return Err(Unfilled::Wire {
                        wire: Wire::from(index),
                    });
                }
            },
            (None, Some(right)) => boundary.inputs.push(right),
            (Some(left), None) => boundary.outputs.push(left),
            (None, None) => {},
        }
    }
    Ok(boundary)
}
