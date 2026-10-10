//! The point-count grade: every shape is its point-free core beside its
//! points, and the grounded shapes are the zero stratum.

use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;

use crate::catalogue::Catalogue;
use crate::outcome::CaseCount;
use crate::outcome::Outcome;
use crate::outcome::Tally;
use crate::outcome::Verdict;
use crate::shape::End;
use crate::shape::PointCount;
use crate::shape::Shape;

/// Whether every shape decomposes uniquely as its core beside its points.
///
/// # Specification
/// - ensures: holds exactly when every shape `G` with `p` points has a
///   point-free core `C` with `C ⊔ •ᵖ ≅ G`, and no other point-free shape `H`
///   and count `q` in the catalogue give `H ⊔ •^q ≅ G`, after one case per
///   shape; the first failing shape otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per shape, are pinned
///   at the bound; L3 — a corolla beside two points has the corolla as its core
///   and is rebuilt from it.
/// - witness: `tests::point_count::every_shape_is_its_core_beside_its_points`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => cases == CaseCount::from(catalogue.shapes().len()),
    Outcome::Fails { .. } => true,
})]
pub fn core_decomposition(catalogue: &Catalogue) -> Outcome<Shape>
{
    let mut tally = Tally::default();
    for shape in catalogue.shapes() {
        tally.count();
        if decomposes(catalogue, shape) == Verdict::Fails {
            return tally.fails(shape.clone());
        }
    }
    tally.holds()
}

/// The decomposition clauses at one shape.
///
/// # Specification
/// - ensures: [`Verdict::Holds`] exactly when the shape's core has no point,
///   rebuilds the shape beside its points, and is the only point-free shape of
///   the catalogue that does so with any count of points.
/// - panics: none.
/// - executable: none — the clauses quantify over the catalogue exactly as the
///   body does; the outcome's case count and verdict observe them.
///
/// # Adequacy
/// - hypothesis: L2 — as [`core_decomposition`].
/// - witness: `tests::point_count::every_shape_is_its_core_beside_its_points`
fn decomposes(
    catalogue: &Catalogue,
    shape: &Shape,
) -> Verdict
{
    let points = shape.point_count();
    let Ok(core) = shape.core()
    else {
        return Verdict::Fails;
    };
    let rebuilt = core
        .beside_points(points)
        .is_ok_and(|whole| whole.key() == shape.key());
    let key = shape.key();
    let unique = catalogue
        .shapes()
        .iter()
        .filter(|other| usize::from(other.point_count()) == 0)
        .all(|other| {
            (0 ..= usize::from(shape.size())).all(|extra| {
                let matches = other
                    .beside_points(PointCount::from(extra))
                    .is_ok_and(|whole| whole.key() == key);
                !matches || (other.key() == core.key() && extra == usize::from(points))
            })
        });
    let decomposed = usize::from(core.point_count()) == 0 && rebuilt && unique;
    if decomposed {
        Verdict::Holds
    }
    else {
        Verdict::Fails
    }
}

/// Whether the grounded shapes, every vertex on some wire, are exactly the
/// shapes without points.
///
/// # Specification
/// - ensures: holds exactly when, for every shape, the vertices some wire end
///   names are all its vertices if and only if its point count is zero, after
///   one case per shape; the first failing shape otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per shape, are pinned
///   at the bound; the counter-example check rejects a shape whose grounding
///   and point count agree.
/// - witness: `tests::point_count::grounded_shapes_are_the_zero_stratum`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => cases == CaseCount::from(catalogue.shapes().len()),
    Outcome::Fails { ref witness, .. } => witness.vertices().all(|vertex| witness.ends().iter().any(|ends| {
        ends.producer() == End::Vertex(vertex) || ends.consumer() == End::Vertex(vertex)
    })) != (usize::from(witness.point_count()) == 0),
})]
pub fn grounded_stratum(catalogue: &Catalogue) -> Outcome<Shape>
{
    let mut tally = Tally::default();
    for shape in catalogue.shapes() {
        tally.count();
        let named: BTreeSet<Edge> = shape
            .ends()
            .iter()
            .flat_map(|ends| [ends.producer(), ends.consumer()])
            .filter_map(|end| match end {
                | End::Open => None,
                | End::Vertex(vertex) => Some(vertex),
            })
            .collect();
        let grounded = named.len() == usize::from(shape.vertex_count());
        if grounded != (usize::from(shape.point_count()) == 0) {
            return tally.fails(shape.clone());
        }
    }
    tally.holds()
}
