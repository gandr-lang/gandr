//! The degree: vertices plus inner wires, into the naturals.
//!
//! # The degree
//!
//! `Degree::of` counts a shape's vertices, points included, plus its inner
//! wires: the graphical categories' degree `|Vt| + |Edge_i|`, valued in the
//! naturals. Isomorphisms preserve it, every other raising map strictly raises
//! it and every other lowering map strictly lowers it. The contraction `p ⊔ q →
//! p→q` raises it from two to three by the inner wire it creates; the
//! substitution `C(1,1) → p→q` from one to three. Vertices plus every wire is
//! no degree: it keeps `C(1,1) → p→q` at three.

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

    /// The highest degree of any of `shapes`, zero when there is none.
    ///
    /// # Specification
    /// - ensures: no shape's degree exceeds it, and it is zero or some shape's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the magma's sub-site at size seven tops out at five,
    ///   the binary vertex fed by two constants, and the wirings it is cut from
    ///   reach seven.
    /// - witness: `tests::profiles::the_magma_stratum_names_its_vacuous_degrees`
    #[spec(ensures: |top| shapes.iter().all(|shape| Self::of(shape).0 <= top.0)
        && (top.0 == 0 || shapes.iter().any(|shape| Self::of(shape).0 == top.0)))]
    pub(crate) fn top(shapes: &[Shape]) -> Self
    {
        shapes.iter().map(Self::of).max().unwrap_or_default()
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
