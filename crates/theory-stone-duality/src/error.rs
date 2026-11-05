//! The typed refusals of the duality's constructions.

use core::fmt;

use crate::free::Vertex;
use crate::index::Budget;
use crate::index::Element;
use crate::index::ElementCount;
use crate::index::Generator;
use crate::index::GeneratorCount;

/// A malformed input to one of the duality's constructions, named by the
/// index it concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DualityError
{
    /// A lattice or a cube would have more generators than one machine word
    /// holds.
    TooManyGenerators(GeneratorCount),
    /// A generator lies at or past the count of its lattice.
    GeneratorOutside(Generator),
    /// A cube would have more vertices than one machine word holds.
    TooWide(GeneratorCount),
    /// A vertex lies outside its cube.
    VertexOutside(Vertex),
    /// A truth table holds at the first vertex and fails at the second, which
    /// is above it.
    TableNotMonotone(Vertex, Vertex),
    /// A map of cubes sends the first vertex above the image of the second,
    /// which is above it.
    CubeMapNotMonotone(Vertex, Vertex),
    /// A map or a homomorphism holds another number of images than its source
    /// needs.
    ImageCount,
    /// A poset or a carrier would have more elements than one machine word
    /// holds.
    TooManyElements(ElementCount),
    /// An element lies at or past the count of its poset or carrier.
    ElementOutside(Element),
    /// A relation puts each of two distinct elements below the other.
    Cycle(Element, Element),
    /// A map sends the first element above the image of the second, which is
    /// above it.
    NotMonotone(Element, Element),
    /// The images of the principal down-sets name no least element for this
    /// element of the source.
    NoLeastImage(Element),
    /// The image of this element's principal down-set is not the preimage of
    /// that down-set under the map the images name.
    NotHomomorphism(Element),
    /// An enumeration passes its budget.
    PastBudget(Budget),
}

impl fmt::Display for DualityError
{
    /// Renders the refusal and the index it names.
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
            Self::TooManyGenerators(count) => {
                write!(f, "{} generators past one machine word", usize::from(count))
            },
            Self::GeneratorOutside(generator) => {
                write!(
                    f,
                    "generator {} outside its lattice",
                    usize::from(generator)
                )
            },
            Self::TooWide(axes) => {
                write!(
                    f,
                    "a cube on {} axes past one machine word",
                    usize::from(axes)
                )
            },
            Self::VertexOutside(vertex) => {
                write!(f, "vertex {:#b} outside its cube", u64::from(vertex))
            },
            Self::TableNotMonotone(lower, upper) => write!(
                f,
                "table holds at {:#b} and fails at {:#b} above it",
                u64::from(lower),
                u64::from(upper)
            ),
            Self::CubeMapNotMonotone(lower, upper) => write!(
                f,
                "map does not keep {:#b} below {:#b}",
                u64::from(lower),
                u64::from(upper)
            ),
            Self::ImageCount => f.write_str("images and source differ in number"),
            Self::TooManyElements(count) => {
                write!(f, "{} elements past one machine word", usize::from(count))
            },
            Self::ElementOutside(element) => {
                write!(f, "element {} outside its poset", usize::from(element))
            },
            Self::Cycle(first, second) => write!(
                f,
                "elements {} and {} each below the other",
                usize::from(first),
                usize::from(second)
            ),
            Self::NotMonotone(lower, upper) => write!(
                f,
                "map does not keep element {} below element {}",
                usize::from(lower),
                usize::from(upper)
            ),
            Self::NoLeastImage(element) => {
                write!(f, "no least image for element {}", usize::from(element))
            },
            Self::NotHomomorphism(element) => write!(
                f,
                "image of the down-set of element {} is no preimage",
                usize::from(element)
            ),
            Self::PastBudget(budget) => {
                write!(f, "enumeration past its budget of {}", usize::from(budget))
            },
        }
    }
}

impl core::error::Error for DualityError
{
}
