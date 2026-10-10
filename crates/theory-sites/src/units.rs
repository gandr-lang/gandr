//! The external product and its unit: the finite check that the empty
//! diagram is the one weak unit, a cancellable pseudo-idempotent, among
//! closed labelled diagrams.
//!
//! The external product of two wirings sets them side by side. A scalar is a
//! closed diagram, the value a presheaf holds at the point. A
//! pseudo-idempotent `e` has `e ⊗ e ≅ e`; it is cancellable when `e ⊗ -` and
//! `- ⊗ e` are injective on isomorphism classes, the finite shadow of their
//! being equivalences.

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::ToString as _;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_circuit_algebras::CanonicalDiagram;
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
use gandr_theory_circuit_algebras::canonicalize;

use crate::catalogue::Catalogue;
use crate::outcome::CaseCount;
use crate::outcome::Outcome;
use crate::outcome::Tally;
use crate::outcome::Verdict;
use crate::shape::End;
use crate::shape::Ends;
use crate::shape::Shape;
use crate::shape::ShapeObstruction;
use crate::shape::WireKind;

wrapper! {
    /// The most generators a scalar of the universe holds.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct GeneratorBound(usize);
}

/// The external product: `left` beside `right`, `right`'s wires numbered
/// after `left`'s, `left`'s ports listed first.
///
/// # Specification
/// - ensures: the generators of `left` then those of `right` with their wires
///   shifted by `left`'s wire count, and each port list the concatenation of
///   the two.
/// - fails: the carrier's refusal, which two admitted wirings side by side
///   never meet.
/// - panics: none.
///
/// # Errors
/// Any [`WiringObstruction`] [`Wiring::assemble`] returns.
///
/// # Adequacy
/// - hypothesis: L3 — the product of a corolla and a bare wire is the wiring
///   written by hand, and the empty wiring is a two-sided unit on it.
/// - witness: `tests::units::the_external_product_sets_wirings_side_by_side`
#[inline]
#[spec(ensures: |ref result| result.as_ref().is_ok_and(|merged| {
    usize::from(merged.wire_count()) == usize::from(left.wire_count()).saturating_add(usize::from(right.wire_count()))
        && merged.generators().len() == left.generators().len().saturating_add(right.generators().len())
        && merged.boundary().inputs().len() == left.boundary().inputs().len().saturating_add(right.boundary().inputs().len())
        && merged.boundary().outputs().len() == left.boundary().outputs().len().saturating_add(right.boundary().outputs().len())
}))]
pub fn merge(
    left: &Wiring,
    right: &Wiring,
) -> Result<Wiring, WiringObstruction>
{
    let offset = usize::from(left.wire_count());
    let shift = |wires: &[Wire]| -> Vec<Wire> {
        wires
            .iter()
            .map(|wire| Wire::from(usize::from(*wire).saturating_add(offset)))
            .collect()
    };
    let mut generators: Vec<Generator> = left.generators().to_vec();
    generators.extend(right.generators().iter().map(|generator| {
        Generator::new(
            generator.label().clone(),
            shift(generator.sources()),
            shift(generator.targets()),
        )
    }));
    let mut inputs: Vec<Wire> = left.boundary().inputs().to_vec();
    inputs.extend(shift(right.boundary().inputs()));
    let mut outputs: Vec<Wire> = left.boundary().outputs().to_vec();
    outputs.extend(shift(right.boundary().outputs()));
    Wiring::assemble(
        WireCount::from(offset.saturating_add(usize::from(right.wire_count()))),
        generators,
        Interface::new(inputs, outputs),
    )
}

/// A label of the scalar signature: two arity-zero generators `c` and `d`,
/// a source `u : (;1)` and a sink `k : (1;)`.
///
/// # Specification
/// trivial.
fn scalar_label(
    shape: &Shape,
    vertex: Edge,
    first_points: EdgeCount,
) -> GeneratorLabel
{
    let produces = shape
        .ends()
        .iter()
        .any(|ends| ends.producer() == End::Vertex(vertex));
    let consumes = shape
        .ends()
        .iter()
        .any(|ends| ends.consumer() == End::Vertex(vertex));
    let name = match (produces, consumes) {
        | (true, _) => "u",
        | (false, true) => "k",
        | (false, false) if usize::from(vertex) < usize::from(first_points) => "c",
        | (false, false) => "d",
    };
    GeneratorLabel::new(name, GeneratorSort::Value)
}

/// Every closed diagram over the scalar signature with at most `bound`
/// generators, one per isomorphism class: `cᵃ dᵇ (u→k)ᵐ` with
/// `a + b + 2m ≤ bound`.
///
/// # Specification
/// - ensures: one wiring per triple `(a, b, m)`, each closed, none with more
///   than `bound` generators, the empty wiring among them.
/// - fails: the carrier's refusal, which these wirings never meet.
/// - panics: none.
///
/// # Errors
/// Any [`ShapeObstruction`] building the shapes returns.
///
/// # Adequacy
/// - hypothesis: L3 — the class count at four generators is pinned at
///   twenty-two and the labels of the closed chain are read back.
/// - witness: `tests::units::scalars_are_counted_and_labelled`
#[inline]
#[spec(ensures: |ref result| result.as_ref().is_ok_and(|wirings| {
    wirings.iter().all(|wiring| wiring.boundary().inputs().is_empty() && wiring.boundary().outputs().is_empty()
        && usize::from(wiring.edge_count()) <= bound.0)
        && wirings.iter().any(|wiring| usize::from(wiring.edge_count()) == 0)
}))]
pub fn scalars(bound: GeneratorBound) -> Result<Vec<Wiring>, ShapeObstruction>
{
    let mut found: Vec<Wiring> = Vec::new();
    for chains in (0 ..= bound.0).take_while(|chains| chains.saturating_mul(2) <= bound.0) {
        let room = bound.0.saturating_sub(chains.saturating_mul(2));
        for points in 0 ..= room {
            for firsts in 0 ..= points {
                let ends: Vec<Ends> = (0 .. chains)
                    .map(|chain| {
                        let producer = points.saturating_add(chain.saturating_mul(2));
                        Ends::new(
                            End::Vertex(Edge::from(producer)),
                            End::Vertex(Edge::from(producer.saturating_add(1))),
                        )
                    })
                    .collect();
                let vertices = points.saturating_add(chains.saturating_mul(2));
                let shape = Shape::from_ends(EdgeCount::from(vertices), ends)?;
                let wiring = shape
                    .to_labelled_wiring(|vertex| {
                        scalar_label(&shape, vertex, EdgeCount::from(firsts))
                    })
                    .map_err(ShapeObstruction::Carrier)?;
                found.push(wiring);
            }
        }
    }
    Ok(found)
}

/// The wiring of `shape` with each vertex labelled by its arity, so that
/// isomorphic labelled diagrams are isomorphic shapes.
///
/// # Specification
/// - ensures: vertex `v` with `i` inputs and `o` outputs is labelled
///   `g{i}.{o}`.
/// - fails: the carrier's refusal, which an admitted shape never meets.
/// - panics: none.
///
/// # Errors
/// Any [`WiringObstruction`] [`Wiring::assemble`] returns.
///
/// # Adequacy
/// - hypothesis: L2 — the two-sided-unit run labels every shape at the bound
///   this way; a label that disagrees with the generator's arity trips the
///   postcondition there.
/// - witness: `tests::units::the_empty_diagram_is_the_only_unit`
#[inline]
#[spec(ensures: |ref result| result.as_ref().is_ok_and(|wiring| {
    wiring.edge_count() == shape.vertex_count()
        && wiring.generators().iter().all(|generator| {
            generator.label().name().to_string() == format!("g{}.{}", generator.sources().len(), generator.targets().len())
        })
}))]
pub fn labelled_by_arity(shape: &Shape) -> Result<Wiring, WiringObstruction>
{
    shape.to_labelled_wiring(|vertex| {
        let inputs = shape
            .ends()
            .iter()
            .filter(|ends| ends.consumer() == End::Vertex(vertex))
            .count();
        let outputs = shape
            .ends()
            .iter()
            .filter(|ends| ends.producer() == End::Vertex(vertex))
            .count();
        GeneratorLabel::new(format!("g{inputs}.{outputs}"), GeneratorSort::Value)
    })
}

/// The outcomes of the unit check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnitOutcomes
{
    /// How many scalar classes the universe holds.
    pub scalars: CaseCount,
    /// The cancellable pseudo-idempotents found, as shapes.
    pub units: Vec<Shape>,
    /// Whether the first unit found is a two-sided unit on every labelled
    /// diagram of the catalogue.
    pub two_sided: Outcome<Shape>,
    /// Whether the universe without the empty diagram holds no cancellable
    /// pseudo-idempotent.
    pub content: Outcome<Shape>,
}

/// The unit check over the scalars of at most `bound` generators, the unit
/// checked on every shape of `diagrams` labelled by arity.
///
/// # Specification
/// - ensures: `units` lists exactly the scalars `e` with `e ⊗ e ≅ e` and `e ⊗
///   -`, `- ⊗ e` injective on the universe's classes, each a closed shape;
///   `two_sided` holds, after one case per diagram, when the first of them
///   composes on either side of every labelled diagram to that diagram, and
///   fails at the empty shape when there is none; `content` fails at the first
///   non-empty scalar that is a cancellable pseudo-idempotent of the universe
///   without the empty diagram.
/// - fails: a scalar or diagram the carrier refuses, which none is.
/// - panics: none.
///
/// # Errors
/// Any [`ShapeObstruction`] building or reading a diagram returns.
///
/// # Adequacy
/// - hypothesis: L2 — the pinned outcomes at four generators: twenty-two
///   scalars, one unit, the empty diagram, two-sided over every diagram at the
///   bound, and no unit without it.
/// - witness: `tests::units::the_empty_diagram_is_the_only_unit`
#[inline]
#[spec(ensures: |ref result| result.as_ref().is_ok_and(|outcomes| {
    outcomes.units.iter().all(|unit| unit.ends().iter().all(|ends| ends.kind() == WireKind::Inner))
        && match outcomes.two_sided {
            Outcome::Holds { cases } => !outcomes.units.is_empty() && cases == CaseCount::from(diagrams.shapes().len()),
            Outcome::Fails { .. } => true,
        }
}))]
pub fn unit_property(
    bound: GeneratorBound,
    diagrams: &Catalogue,
) -> Result<UnitOutcomes, ShapeObstruction>
{
    let universe = scalars(bound)?;
    let with_empty: Vec<&Wiring> = universe.iter().collect();
    let without_empty: Vec<&Wiring> = universe
        .iter()
        .filter(|wiring| usize::from(wiring.edge_count()) != 0)
        .collect();
    let mut units: Vec<Shape> = Vec::new();
    let mut unit_wiring: Vec<&Wiring> = Vec::new();
    for wiring in &with_empty {
        if is_unit(wiring, &with_empty)? == Verdict::Holds {
            units.push(Shape::read(wiring)?);
            unit_wiring.push(wiring);
        }
    }
    let mut content_tally = Tally::default();
    let mut content: Option<Outcome<Shape>> = None;
    for wiring in &without_empty {
        content_tally.count();
        if is_unit(wiring, &without_empty)? == Verdict::Holds {
            content = Some(content_tally.fails(Shape::read(wiring)?));
            break;
        }
    }
    let two_sided = match unit_wiring.first() {
        | Some(unit) => two_sided(unit, diagrams)?,
        | None => Tally::default().fails(Shape::default()),
    };
    Ok(UnitOutcomes {
        scalars: CaseCount::from(universe.len()),
        units,
        two_sided,
        content: content.unwrap_or_else(|| content_tally.holds()),
    })
}

/// Whether `unit` is a cancellable pseudo-idempotent of the sub-universe
/// `members`.
///
/// # Specification
/// - ensures: [`Verdict::Holds`] exactly when `unit ⊗ unit` has `unit`'s
///   canonical form and `unit ⊗ -`, `- ⊗ unit` send distinct members to
///   distinct canonical forms.
/// - fails: the carrier's refusal of a product, which two admitted wirings
///   never meet.
/// - panics: none.
///
/// # Errors
/// - [`ShapeObstruction::Carrier`]: a product the carrier refused.
///
/// # Adequacy
/// - hypothesis: L2 — among twenty-two scalars exactly the empty diagram holds,
///   and without it none does; a check that admits a non-idempotent or a
///   non-cancellable scalar finds a second unit.
/// - witness: `tests::units::the_empty_diagram_is_the_only_unit`
#[spec(ensures: |ref result| match *result {
    Ok(Verdict::Holds) => merge(unit, unit).is_ok_and(|square| canonicalize(&square).form() == canonicalize(unit).form()),
    Ok(Verdict::Fails) => true,
    Err(_) => false,
})]
fn is_unit(
    unit: &Wiring,
    members: &[&Wiring],
) -> Result<Verdict, ShapeObstruction>
{
    let square = merge(unit, unit).map_err(ShapeObstruction::Carrier)?;
    if canonicalize(&square).form() != canonicalize(unit).form() {
        return Ok(Verdict::Fails);
    }
    let mut left: BTreeSet<CanonicalDiagram> = BTreeSet::new();
    let mut right: BTreeSet<CanonicalDiagram> = BTreeSet::new();
    for other in members {
        let before = merge(unit, other).map_err(ShapeObstruction::Carrier)?;
        let after = merge(other, unit).map_err(ShapeObstruction::Carrier)?;
        if !left.insert(canonicalize(&before).form().clone())
            || !right.insert(canonicalize(&after).form().clone())
        {
            return Ok(Verdict::Fails);
        }
    }
    Ok(Verdict::Holds)
}

/// Whether `unit` is a two-sided unit on every shape of `diagrams`
/// labelled by arity.
///
/// # Specification
/// - ensures: holds, after one case per shape, exactly when `unit ⊗ D` and `D ⊗
///   unit` have `D`'s canonical form for every labelled diagram `D`; the first
///   failing shape otherwise.
/// - fails: the carrier's refusal of a labelled diagram or a product, which
///   admitted wirings never meet.
/// - panics: none.
///
/// # Errors
/// - [`ShapeObstruction::Carrier`]: a wiring the carrier refused.
///
/// # Adequacy
/// - hypothesis: L2 — the empty diagram is two-sided over every diagram at the
///   bound, with the case count pinned through the unit check.
/// - witness: `tests::units::the_empty_diagram_is_the_only_unit`
#[spec(ensures: |ref result| match *result {
    Ok(Outcome::Holds { cases }) => cases == CaseCount::from(diagrams.shapes().len()),
    Ok(Outcome::Fails { .. }) => true,
    Err(_) => false,
})]
fn two_sided(
    unit: &Wiring,
    diagrams: &Catalogue,
) -> Result<Outcome<Shape>, ShapeObstruction>
{
    let mut tally = Tally::default();
    for shape in diagrams.shapes() {
        tally.count();
        let wiring = labelled_by_arity(shape).map_err(ShapeObstruction::Carrier)?;
        let form = canonicalize(&wiring).form().clone();
        let before = merge(unit, &wiring).map_err(ShapeObstruction::Carrier)?;
        let after = merge(&wiring, unit).map_err(ShapeObstruction::Carrier)?;
        if *canonicalize(&before).form() != form || *canonicalize(&after).form() != form {
            return Ok(tally.fails(shape.clone()));
        }
    }
    Ok(tally.holds())
}
