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
//! A refusal names its defect: [`CheckRefusal::ComposeUncertified`] for the
//! stratum, [`CheckRefusal::ComposeNotAShape`] for the pasting and
//! [`CheckRefusal::ComposeDoesNotFill`] for the cells.
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
use gandr_core_term::compose::Composite;
use gandr_core_term::compose::Pasting;
use gandr_theory_sites::Boundary;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::Shape;
use gandr_theory_sites::fills;

use crate::context::CheckingContext;
use crate::conversion::Agreement;
use crate::refusal::CheckRefusal;
use crate::ua::Strata;
use crate::ua::StratumAt;

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

/// The shape `composite` names, read at its certified stratum.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the chain of the pasting's cell count. Past one cell, the chain
///   lies in [`gandr_theory_sites::Catalogue::chains`] at the bound, and the
///   stratum at the degree certifies and reaches the chain's degree.
/// - fails: [`CheckRefusal::ComposeNotAShape`] for the chain of no cell or of
///   more than a shape holds, or a chain past the bound or the degree;
///   [`CheckRefusal::ComposeUncertified`] for a stratum the table refuses.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a 3-chain at degree 5 over bound 7 is admitted. A degree
///   past the catalogue, a chain past the bound, a chain past the degree and
///   the chain of no cell are each refused by name. One cell at an uncertified
///   stratum is admitted.
/// - witness: `compose::tests::a_composite_refuses_each_defect_by_name`
/// - witness: `compose::tests::one_cell_reads_no_stratum`
#[spec(ensures: |ref ret| match *ret {
    | Ok(ref shape) => match composite.pasting {
        Pasting::Chain { cells } => usize::from(shape.vertex_count()) == usize::from(cells),
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
    let Pasting::Chain { cells } = composite.pasting;
    let Ok(shape) = Shape::chain(usize::from(cells).into())
    else {
        return Err(not_a_shape);
    };
    if usize::from(shape.vertex_count()) == 1 {
        return Ok(shape);
    }
    let stratum = strata
        .certified(
            &Family::Chains,
            StratumAt {
                bound: composite.stratum.bound,
                degree: composite.stratum.degree,
            },
            gandr_theory_sites::ShapeBudget::EVERY,
        )
        .map_err(|stratum| CheckRefusal::ComposeUncertified { at, stratum })?;
    if !stratum.catalogue().shapes().contains(&shape) || Degree::of(&shape) > stratum.degree() {
        return Err(not_a_shape);
    }
    Ok(shape)
}

/// The outer endpoints of `cells`, one per vertex of `shape`, when they fill
/// it.
///
/// # Specification
/// - requires: `cells` stand under the judgement's binders.
/// - ensures: [`fills`] admits the cells, an inner wire's two endpoints meeting
///   when either is [`Endpoint::Unknown`] or the two convert; the answer is the
///   chain's open input's colour and its open output's.
/// - fails: [`CheckRefusal::ComposeDoesNotFill`] naming the first defect
///   [`fills`] finds; a conversion's own refusal; a machine invariant for a
///   shape whose boundary is no one input and one output.
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
    | Err(CheckRefusal::ComposeDoesNotFill { at: site, .. }) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub fn fill(
    context: &CheckingContext<'_>,
    at: ValueId,
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
    let boundary = filled.map_err(|defect| CheckRefusal::ComposeDoesNotFill { at, defect })?;
    match (boundary.inputs(), boundary.outputs()) {
        (&[&start], &[&end]) => Ok((start, end)),
        _ => Err(CheckRefusal::MachineInvariant),
    }
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
