//! `compose[n, k](chain(m), (c₁, …, cₘ))`: the composite of a chain of paths at
//! a certified stratum of the chain sub-site.
//!
//! # The rule
//!
//! The head names the degree `n` and the bound `k`. The rule certifies the
//! stratum of degree `n` over [`gandr_theory_sites::Catalogue::chains`] at
//! `k`, through the table [`crate::ua`] holds, and reads `chain(m)` as a
//! shape of it: the chain of `m` vertices lies in the catalogue, size
//! `2m + 1 ≤ k`, and the stratum reaches its degree `2m − 1 ≤ n`. One cell
//! reads no stratum, since the corolla is its own composite. Each cell
//! synthesises a path type `Path(A, xᵢ₋₁, xᵢ)`, a cell written as a call
//! running first as a scrutinee does. Its two endpoints colour the chain's
//! legs at the cell's vertex, and [`fills`] admits the diagram when each
//! inner wire's two colours convert. The composite then has the type its
//! realisation synthesises, the fold the lowering made, `Path(A, x₀, xₘ)`. A
//! cell of the unknown type colours its legs with no endpoint, which meets
//! any.
//!
//! The bridge erases a returned composite to its realisation, and any other
//! composite to the value its realisation returns. The realisation is
//! synthesised as the chain written with `then` is, so the kernel replays
//! the terms that chain gives it.
//!
//! The chains take a budget ([`chain_budget`]): a stratum whose catalogue
//! holds more chains is refused by the budget's name, never left to run.
//!
//! # Level two
//!
//! `compose[n, k](chain(m, (a₁, …, aₘ)), cells)` names the level-two shape
//! `[m](a₁, …, aₘ)`, an object of the wreath of the chains at `k` over
//! themselves. The rule reads level two at the stratum through
//! [`Strata::level_two`], the wreath and its certificate held in the strata a
//! context holds, and finds the object in the wreath within degree `n`. An
//! object of degree one or less reads no stratum, as one cell does. Column
//! `i` holds `aᵢ` 2-cells, or one 1-cell when `aᵢ` is zero. The 2-cells of
//! a column meet along their 1-cells as a chain's cells do, and the columns
//! meet along their points, each column's ends its 2-cells' carrier's. The
//! realisation folds each column by `then` one layer up, and the columns by
//! the whiskers the filler generator lifts by, so the whisker `[2](1, 0)` is
//! the right whisker.
//!
//! A refusal names its defect: [`CheckRefusal::ComposeUncertified`] for the
//! stratum, [`CheckRefusal::ComposeNotAShape`] for the pasting and
//! [`CheckRefusal::ComposeDoesNotFill`] for the cells, at the
//! [`Seam`] the defect sits in.
//!
//! # Decisions
//!
//! - **The chain sub-site, not the wirings.** The chains at bound 7 certify in
//!   a tenth of a millisecond over five shapes, and the wirings take seven
//!   seconds over 631 classes. Composition at dimension one reads only chains,
//!   so the rule names [`Family::Chains`]. Reversal: a pasting past the chains,
//!   the wreath's levels, names the catalogue that holds it.
//! - **Endpoints meet by conversion.** [`fills`] leaves the colour comparison
//!   to its caller, and the checker compares two endpoints as a stay compares
//!   them: one node, one syntax, or the normaliser's conversion. The
//!   realisation's check then meets them again where the kernel replays it. The
//!   alternative, syntax alone, refuses a composite whose middle object is
//!   written two ways. Reversal: a recorded dialogue per inner wire, when the
//!   kernel reads the diagram rather than its fold.
//! - **Level two fills as two levels of chains.** A level-two shape's cells are
//!   checked as each column's chain and then the outer chain, rather than as
//!   one diagram of the wreath's object. The wreath certifies the shape, and
//!   the chains' filling is the check a composite of the shape owes. Reversal:
//!   a pasting whose cells meet other than column by column, a level past two.
//! - **The whiskers are the generator's.** The horizontal fold uses the
//!   transports the filler generator lifts by, so a level-two composite and a
//!   filler over the same shape agree by syntax. Reversal: a whisker
//!   `math.path` writes as `ap`, if the two whiskers are related by a stated
//!   conversion.
//! - **A budget on the chains.** The chain catalogue's cost grows with the
//!   chains it holds faster than any stratum a check waits on: a bound holding
//!   the 7-chain certifies in under half a second, one holding the 8-chain in
//!   eight seconds. The budget refuses the stratum by name before its catalogue
//!   is built. Reversal: the chains' Segal condition decided by the spine,
//!   without the catalogue's enumeration.
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — exemplar: unbiased
//!   composition is a term former at a certified stratum, its realisation the
//!   cells' composite.
//! - Charles Rezk. "A Model for the Homotopy Theory of Homotopy Theory."
//!   _Transactions of the American Mathematical Society_ 353, 3 (2001), pages
//!   973–1007. `doi:10.1090/S0002-9947-00-02653-2` — the Segal condition, under
//!   which a chain's composite is determined by its cells.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::compose::Column;
use gandr_core_term::compose::Composite;
use gandr_core_term::compose::Heights;
use gandr_core_term::compose::Pasting;
use gandr_core_term::compose::Seam;
use gandr_theory_sites::Boundary;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::Level;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeBudget;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::fills;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::conversion::Agreement;
use crate::refusal::CheckRefusal;
use crate::ua::Strata;
use crate::ua::StratumAt;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

/// One end of a cell, as the diagram colours it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Endpoint
{
    /// The endpoint the cell's path type names.
    Known(ValueId),
    /// A cell of the unknown type, whose endpoints meet any.
    Unknown,
}

/// The shape `composite` names, read at its certified stratum: a chain, or a
/// level-two shape's outer chain of columns.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the chain of the pasting's cell count, or of a level-two shape's
///   column count. Past one cell, the chain lies in
///   [`gandr_theory_sites::Catalogue::chains`] at the bound, and the stratum at
///   the degree certifies and reaches the chain's degree. A level-two shape of
///   degree two or more is an object of the wreath of the chains at the bound,
///   level two certifies at the degree, and the object's degree reaches no
///   further.
/// - fails: [`CheckRefusal::ComposeNotAShape`] for the chain of no cell or of
///   more than a shape holds, a chain past the bound or the degree, or a
///   level-two shape no object of the wreath or past the degree;
///   [`CheckRefusal::ComposeUncertified`] for a stratum the source refuses.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a 3-chain at degree 5 over bound 7 is admitted. A degree
///   past the catalogue, a chain past the bound, a chain past the degree, the
///   chain of no cell and a bound past the chain budget are each refused by
///   name. One cell at an uncertified stratum is admitted. The whisker at
///   degree 4 over bound 9 is admitted, and refused past its degree and past
///   its bound.
/// - witness: `compose::tests::a_composite_refuses_each_defect_by_name`
/// - witness: `compose::tests::one_cell_reads_no_stratum`
/// - witness: `compose::tests::a_level_two_shape_is_read_at_level_two`
#[spec(ensures: |ref ret| match *ret {
    | Ok(ref shape) => match composite.pasting {
        Pasting::Chain { cells } => usize::from(shape.vertex_count()) == usize::from(cells),
        Pasting::Columns { heights } => usize::from(shape.vertex_count()) == heights.columns().count(),
    },
    | Err(CheckRefusal::ComposeNotAShape { at: site, pasting }) => site == at && pasting == composite.pasting,
    | Err(CheckRefusal::ComposeUncertified { at: site, .. }) => site == at,
    | Err(_) => false,
})]
pub fn admit(
    strata: &mut Strata,
    at: ValueId,
    composite: Composite,
) -> Result<Shape, CheckRefusal>
{
    let not_a_shape = CheckRefusal::ComposeNotAShape {
        at,
        pasting: composite.pasting,
    };
    let written = StratumAt {
        bound: composite.stratum.bound,
        degree: composite.stratum.degree,
    };
    let heights = match composite.pasting {
        Pasting::Chain { cells } => {
            let Ok(shape) = Shape::chain(usize::from(cells).into())
            else {
                return Err(not_a_shape);
            };
            if usize::from(shape.vertex_count()) == 1 {
                return Ok(shape);
            }
            let stratum = strata
                .certified(&Family::Chains, written, chain_budget())
                .map_err(|stratum| CheckRefusal::ComposeUncertified { at, stratum })?;
            if !stratum.catalogue().shapes().contains(&shape)
                || Degree::of(&shape) > stratum.degree()
            {
                return Err(not_a_shape);
            }
            return Ok(shape);
        },
        Pasting::Columns { heights } => heights,
    };
    let mut columns = Vec::new();
    for height in heights.columns() {
        let column = if usize::from(height) == 0 {
            Shape::default()
        }
        else {
            Shape::chain(usize::from(height).into()).map_err(|_refused| not_a_shape)?
        };
        columns.push(column);
    }
    let outer = Shape::chain(columns.len().into()).map_err(|_refused| not_a_shape)?;
    let object = WreathShape::new(outer.clone(), columns).map_err(|_refused| not_a_shape)?;
    let degree = <Wreath<Catalogue> as Level>::degree(&object);
    if degree < Degree::from(2_usize) {
        return Ok(outer);
    }
    let stratum = strata
        .level_two(written)
        .map_err(|stratum| CheckRefusal::ComposeUncertified { at, stratum })?;
    if matches!(stratum.wreath().find(&object), Maybe::Absent(_)) || degree > stratum.degree() {
        return Err(not_a_shape);
    }
    Ok(outer)
}

/// The chain shapes a composite's catalogue may hold before its stratum is
/// refused: the empty shape, the point and the chains to seven cells.
///
/// economy: the chains at bound 15, to the 7-chain, certify degree 13 in under
/// half a second; bound 17 adds the 8-chain and takes eight seconds; bound 19
/// runs past half an hour. The budget refuses bound 17 at its tenth shape,
/// before any hom set is built.
///
/// # Specification
/// trivial.
#[must_use]
pub fn chain_budget() -> ShapeBudget
{
    ShapeBudget::from(9_usize)
}

/// The outer endpoints of `cells`, one per vertex of `shape`, when they fill
/// it along `seam`.
///
/// # Specification
/// - requires: `cells` stand under the judgement's binders.
/// - ensures: [`fills`] admits the cells, an inner wire's two endpoints meeting
///   when either is [`Endpoint::Unknown`] or the two convert; the answer is the
///   chain's open input's colour and its open output's.
/// - fails: [`CheckRefusal::ComposeDoesNotFill`] at `seam`, naming the first
///   defect [`fills`] finds; a conversion's own refusal; a machine invariant
///   for a shape whose boundary is no one input and one output.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — three composable cells answer their outer endpoints, a
///   cell short is refused by the count, and a middle endpoint that does not
///   convert is refused at its wire.
/// - witness: `compose::tests::composable_cells_fill_their_chain`
/// - witness: `compose::tests::a_composite_refuses_each_defect_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ComposeDoesNotFill { at: site, seam: held, .. }) => site == at && held == seam,
    | Ok(_) | Err(_) => true,
})]
pub fn fill(
    context: &CheckingContext<'_>,
    (at, seam): (ValueId, Seam),
    shape: &Shape,
    cells: &[Boundary<Endpoint>],
) -> Result<(Endpoint, Endpoint), CheckRefusal>
{
    let mut fault = Ok(());
    let filled = fills(shape, cells, |left, right| match (*left, *right) {
        (Endpoint::Known(left), Endpoint::Known(right)) => {
            match crate::flow::convertible(context, left, right) {
                Ok(agreement) => agreement == Agreement::Convertible,
                Err(refusal) => {
                    fault = Err(refusal);
                    false
                },
            }
        },
        (Endpoint::Unknown, _) | (_, Endpoint::Unknown) => true,
    });
    fault?;
    let boundary =
        filled.map_err(|defect| CheckRefusal::ComposeDoesNotFill { at, seam, defect })?;
    match (boundary.inputs(), boundary.outputs()) {
        (&[&start], &[&end]) => Ok((start, end)),
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// One cell of a level-two composite as its type reads: the carrier and the
/// two endpoints of its path type, or a cell of the unknown type.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CellReading
{
    /// `Path(carrier, left, right)`.
    Known
    {
        /// The type the endpoints inhabit.
        carrier: ValueTypeId,
        /// The left endpoint.
        left: ValueId,
        /// The right endpoint.
        right: ValueId,
    },
    /// A cell of the unknown type, whose endpoints meet any.
    Unknown,
}

/// Whether `cells` fill the level-two shape of `heights`, `outer` its chain
/// of columns: each column's 2-cells meet along their 1-cells, and the
/// columns along their points.
///
/// # Specification
/// - requires: `cells` stand under the judgement's binders, in column order,
///   one per 2-cell and one per empty column.
/// - ensures: every column of two 2-cells or more fills its chain at its
///   [`Seam::Column`], its 2-cells' endpoints the 1-cells; then the columns
///   fill `outer` at [`Seam::Outer`], each column's endpoints its 2-cells'
///   carrier's, or its 1-cell's own.
/// - fails: as [`fill`] at each seam, the columns first; a machine invariant
///   for cells of another count, or a 2-cell whose carrier is no path type.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the horizontal composite's two 2-cells fill it, and a
///   second column starting where the first does not end is refused at the
///   outer seam, a column's 2-cells that do not meet at the column's.
/// - witness: `compose::tests::a_level_two_shape_is_read_at_level_two`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ComposeDoesNotFill { at: site, .. }) => site == at,
    | Ok(()) | Err(_) => true,
})]
pub fn fill_columns(
    context: &CheckingContext<'_>,
    at: ValueId,
    (heights, outer): (Heights, &Shape),
    cells: &[CellReading],
) -> Result<(), CheckRefusal>
{
    let ends = |reading: CellReading| match reading {
        CellReading::Known { left, right, .. } => {
            cell(Endpoint::Known(left), Endpoint::Known(right))
        },
        CellReading::Unknown => cell(Endpoint::Unknown, Endpoint::Unknown),
    };
    let mut columns = Vec::new();
    let mut vertical = Vec::new();
    let mut rest = cells;
    for (position, height) in heights.columns().enumerate() {
        let (held, tail) = rest
            .split_at_checked(usize::from(height).max(1))
            .ok_or(CheckRefusal::MachineInvariant)?;
        rest = tail;
        let &first = held.first().ok_or(CheckRefusal::MachineInvariant)?;
        if usize::from(height) == 0 {
            columns.push(ends(first));
            continue;
        }
        if usize::from(height) > 1 {
            let chain = Shape::chain(usize::from(height).into())
                .map_err(|_refused| CheckRefusal::MachineInvariant)?;
            vertical.clear();
            vertical.extend(held.iter().map(|&reading| ends(reading)));
            let column =
                Column::try_from(position).map_err(|_wide| CheckRefusal::MachineInvariant)?;
            let seam = Seam::Column(column);
            let _ends = fill(context, (at, seam), &chain, &vertical)?;
        }
        columns.push(match first {
            CellReading::Known { carrier, .. } => {
                let ValueTypeView::Path { left, right, .. } =
                    value_type_view(context.arena(), carrier)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                cell(Endpoint::Known(left), Endpoint::Known(right))
            },
            CellReading::Unknown => ends(first),
        });
    }
    if !rest.is_empty() {
        return Err(CheckRefusal::MachineInvariant);
    }
    let _ends = fill(context, (at, Seam::Outer), outer, &columns)?;
    Ok(())
}

/// The diagram cell of a path from `left` to `right`: one input leg and one
/// output leg.
///
/// # Specification
/// trivial.
pub fn cell(
    left: Endpoint,
    right: Endpoint,
) -> Boundary<Endpoint>
{
    Boundary::new(Vec::from([left]), Vec::from([right]))
}
