//! The degree: vertices plus inner wires, into the naturals.

use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::EdgeCount;

use crate::shape::End;
use crate::shape::Shape;
use crate::shape::WireKind;

wrapper! {
    /// A shape's degree: its vertices, points included, plus its inner
    /// wires.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Degree(usize);
}

impl Degree
{
    /// The degree of `shape`.
    ///
    /// # Specification
    /// - ensures: the vertex count plus the number of wires attached at both
    ///   ends; legs count nothing, so a corolla of any arity has degree one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shape with an inner wire, a leg of each kind and a
    ///   point, a corolla and the closed chain, each asserted to its value,
    ///   separate a counted leg, a lost point and a lost inner wire.
    /// - witness: `tests::shapes::the_degree_counts_vertices_and_inner_wires`
    #[inline]
    #[must_use]
    #[spec(ensures: |degree| degree.0 == usize::from(shape.vertex_count()).saturating_add(
        shape.ends().iter().filter(|ends| ends.producer() != End::Open && ends.consumer() != End::Open).count()
    ))]
    pub fn of(shape: &Shape) -> Self
    {
        Self(
            usize::from(shape.vertex_count())
                .saturating_add(usize::from(shape.count_of(WireKind::Inner))),
        )
    }

    /// The degree raised by `count`: the degree of a shape beside `count`
    /// further points.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn raised_by(
        self,
        count: EdgeCount,
    ) -> Self
    {
        Self(self.0.saturating_add(usize::from(count)))
    }
}

impl fmt::Display for Degree
{
    /// Writes the number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}
