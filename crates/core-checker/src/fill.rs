//! `fill[n, k](chain(m), t, (d₁, …, dₘ))`: the filler generator `t ↑ X` over
//! a chain of paths at a certified stratum.
//!
//! # The rule
//!
//! The head names the degree `n` and the bound `k`, certified over the chain
//! sub-site as [`crate::compose`] certifies a composite's. `t` is a curried
//! function of the chain's `m` cells, `(c₁ : A₁) => … => (cₘ : Aₘ) => Path(P,
//! u, v)`, its sides `u` and `v` composites of the cells. Each `dᵢ` is the
//! `i`-th cell, of type `Aᵢ`, or a path between two such cells, one path layer
//! deeper than `Aᵢ`: the cells of `X`. The family of `X` is the former of
//! that layer. A `Path` cell has its instance here, and a `Flow` cell or a
//! bridge is refused [`CheckRefusal::GeneratorFamilyUnsupported`] with the
//! unit that lands its instance.
//!
//! The square is Catt's: from `t[X⁻] then (v ↑ X)` to `(u ↑ X) then t[X⁺]`,
//! `X⁻` and `X⁺` the cells of `X` read at their left and right ends. A side's
//! lift is built over its composite structure: a cell of `X` lifts as its path,
//! any other cell stays, and a composite whose one half lifts is that half
//! whiskered by the other, the action of composing with it, as `math.path`
//! writes `whiskerLeft` and `whiskerRight`. A composite both of whose halves
//! lift is the right whisker then the left.
//!
//! The filler is the family's own induction: based path induction on each
//! path of `X` in vertex order, the outermost first, with base `here(t[X⁻])`
//! once every path is `here`. The rule checks the induction against the
//! square and records it as the node's decision ([`crate::nested::Nesting::
//! Filled`]); the elaboration stands the node as that induction, so the
//! second judgement, evaluation and the kernel read an ordinary term. A
//! filler over `here` cells reduces to `here`.
//!
//! A refusal names its defect: [`CheckRefusal::FillUncertified`] for the
//! stratum, `compose`'s own refusals for a pasting or cells that do not fill
//! the chain, [`CheckRefusal::NoFiller`] for sides that are no composites of
//! the cells, an `X` of no cell, or a square asked for that is not the
//! generator's, and [`CheckRefusal::GeneratorFamilyUnsupported`] for a family
//! with no instance.
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — exemplar: the filler
//!   generator indexed by the cell family, its `Path` instance the family's
//!   induction.
//! - `vault:01a18572-6e13-7412-bc74-aa6a24d157c4` — exemplar: `t ↑ X` as the
//!   dependent action of `t` on the paths of `X`.
//! - Thibaut Benjamin, Ioannis Markakis, Wilfred Offord, Chiara Sarti and Jamie
//!   Vicary. "Naturality for Higher-Dimensional Path Types." (2025).
//!   `arXiv:2501.11620` — `t ↑ X` and its square; Example 1.3, the associator's
//!   naturality.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::TrackingIssue;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::identity;
use gandr_core_term::identity::Whisker;
use gandr_kernel_term::DeBruijnIndex;

use crate::compose::Endpoint;
use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

/// A cell family the generator has no instance for yet.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UnsupportedFamily
{
    /// Directed cells, `Flow`.
    Flow,
    /// Bridges.
    Bridge,
}

impl UnsupportedFamily
{
    /// The unit that lands the family's instance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tracking(self) -> TrackingIssue
    {
        match self {
            Self::Flow => TrackingIssue::DIRECTED_FILLER,
            Self::Bridge => TrackingIssue::BRIDGE_FILLER,
        }
    }
}

/// What the rule derives for a fill: the square it synthesises and the
/// induction that fills it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Realisation
{
    /// The square, a path between two paths of paths.
    pub square: ValueTypeId,
    /// The induction, a computation returning the filler.
    pub realised: ComputationId,
}

/// How many path layers a type holds, the outermost first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Layers(usize);

/// How many cells a chain holds, or how many of its binders stand open.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Cells(usize);

/// A cell's place in the chain, in vertex order from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Position(usize);

/// One cell of the fill, as the rule reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cell
{
    /// A cell of the chain, standing as itself.
    Plain(ValueId),
    /// A cell of `X`: a path from `lo` to `hi`.
    Lifted
    {
        /// The cell at the path's left end.
        lo: ValueId,
        /// The cell at its right end.
        hi: ValueId,
        /// The path.
        path: ValueId,
    },
}

/// A node of a side's composite tree: a cell, or the composite of two nodes,
/// each child after its parent.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side
{
    /// The cell at this position, in vertex order from zero.
    Leaf(usize),
    /// The composite of the two nodes at these positions, the first first.
    Composite(usize, usize),
}

/// A side's composite tree node with the span of cells it composes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Spanned
{
    /// The node.
    side: Side,
    /// The first cell it composes.
    first: usize,
    /// The last cell it composes.
    last: usize,
}

/// One node of a side read at an assignment: its two ends and its lift.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Read
{
    /// The side with every cell of `X` at its left end.
    lo: ValueId,
    /// The side with every cell of `X` at its right end.
    hi: ValueId,
    /// The path from `lo` to `hi`, when the side meets `X`.
    lift: Option<ValueId>,
}

/// The chain the cells fill, read in the fill's own context.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Chain
{
    /// The carrier the cells' paths inhabit.
    carrier: ValueTypeId,
    /// The `m + 1` vertices, in order.
    vertices: Vec<ValueId>,
}

/// Derive the square and the induction of the fill at `at`, its generator's
/// type first in `types` and its cells' after it.
///
/// # Specification
/// - requires: `at` is a fill; `types` are the type its generator's computation
///   returns and the types its cells synthesised, in that order, all under the
///   judgement's binders.
/// - ensures: the square `t ↑ X` fills over the stratum the node names, and the
///   induction realising it, both under the judgement's binders.
/// - fails: as the module states; [`CheckRefusal::ShapeMismatch`] for a
///   generator that is no curried function of the cells into a path type, or a
///   cell neither of its domain's type nor a path one layer deeper;
///   [`CheckRefusal::ComposeNotAShape`] for a level-two shape whose columns are
///   not the cells of `X`, a column of one 2-cell each and an empty column each
///   other cell; a machine invariant for a node that is no fill or types of
///   another count.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a free path between two cells' first fills its square by
///   induction, from `u` at the path's left end to `v` at its right; sides that
///   are no composites, an `X` of no cell, an uncertified stratum and a `Flow`
///   cell are each refused by name. The whisker names `X` by its columns, and a
///   column at a plain cell or of two 2-cells is refused by name.
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
/// - witness: `fill::tests::a_fill_refuses_each_defect_by_name`
/// - witness: `fill::tests::a_level_two_fill_names_x_by_its_columns`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::FillUncertified { at: site, .. } | CheckRefusal::NoFiller { at: site, .. } | CheckRefusal::GeneratorFamilyUnsupported { at: site, .. }) => site == at,
    | Ok(_) | Err(_) => true,
})]
#[inline]
pub fn realise(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    types: &[ValueTypeId],
) -> Result<Realisation, CheckRefusal>
{
    let Some(&Value::Fill {
        composite,
        generator,
        ref cells,
    }) = context.arena().value(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let written = cells.to_vec();
    let shape = crate::compose::admit(context.strata_mut(), at, composite).map_err(|refusal| {
        if let CheckRefusal::ComposeUncertified { stratum, .. } = refusal {
            CheckRefusal::FillUncertified { at, stratum }
        }
        else {
            refusal
        }
    })?;
    let (&generator_type, cell_types) =
        types.split_first().ok_or(CheckRefusal::MachineInvariant)?;
    if cell_types.len() != written.len() {
        return Err(CheckRefusal::MachineInvariant);
    }
    let (domains, sides) = telescope(context, at, generator_type, Cells(written.len()))?;
    let mut read = Vec::with_capacity(written.len());
    let mut diagram = Vec::with_capacity(written.len());
    let mut carrier = None;
    for ((&cell, &found), &wanted) in written.iter().zip(cell_types).zip(&domains) {
        let (held, (path_carrier, left, right)) = classify(context, at, cell, found, wanted)?;
        carrier.get_or_insert(path_carrier);
        read.push(held);
        diagram.push(crate::compose::cell(
            Endpoint::Known(left),
            Endpoint::Known(right),
        ));
    }
    // A level-two shape names the cells of `X`: a column of one 2-cell each,
    // and an empty column each other cell.
    if let gandr_core_term::compose::Pasting::Columns { heights } = composite.pasting
        && (heights.columns().count() != read.len()
            || !heights.columns().zip(&read).all(|(height, cell)| {
                matches!(
                    (usize::from(height), cell),
                    (0, &Cell::Plain(_)) | (1, &Cell::Lifted { .. })
                )
            }))
    {
        return Err(CheckRefusal::ComposeNotAShape {
            at,
            pasting: composite.pasting,
        });
    }
    let (Endpoint::Known(start), _) = crate::compose::fill(
        context,
        (at, gandr_core_term::compose::Seam::Outer),
        &shape,
        &diagram,
    )?
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let carrier = carrier.ok_or(CheckRefusal::MachineInvariant)?;
    let mut vertices = Vec::with_capacity(read.len().saturating_add(1));
    vertices.push(start);
    for boundary in &diagram {
        let &[Endpoint::Known(end)] = boundary.outputs()
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        vertices.push(end);
    }
    let chain = Chain { carrier, vertices };
    let lowered: Vec<ValueId> = read
        .iter()
        .map(|cell| match *cell {
            Cell::Plain(value) | Cell::Lifted { lo: value, .. } => value,
        })
        .collect();
    let no_filler = |context: &mut CheckingContext<'_>| {
        let arena = context.arena_mut();
        CheckRefusal::NoFiller {
            at,
            left: instantiated(arena, sides.0, &lowered),
            right: instantiated(arena, sides.1, &lowered),
            stratum: composite.stratum,
        }
    };
    let arena = context.arena();
    let (Some(u), Some(v)) = (
        composite_of(arena, sides.0, Cells(read.len())),
        composite_of(arena, sides.1, Cells(read.len())),
    )
    else {
        return Err(no_filler(context));
    };
    let lifted: Vec<usize> = read
        .iter()
        .enumerate()
        .filter_map(|(index, cell)| matches!(cell, Cell::Lifted { .. }).then_some(index))
        .collect();
    if lifted.is_empty() {
        return Err(no_filler(context));
    }
    let builder = Builder {
        generator,
        chain: &chain,
        u: &u,
        v: &v,
    };
    let arena = context.arena_mut();
    let square = builder.square(arena, Binders::NONE, &read);
    let lowest = builder.applied(arena, Binders::NONE, &lowered);
    let mut base = arena.value_here(lowest);
    let mut realised = None;
    for &position in lifted.iter().rev() {
        let Some(&Cell::Lifted { lo, path, .. }) = read.get(position)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let transport = builder.induction(arena, &read, (Position(position), lo, path), base)?;
        base = arena.value_returned(transport);
        realised = Some(transport);
    }
    let realised = realised.ok_or(CheckRefusal::MachineInvariant)?;
    Ok(Realisation { square, realised })
}

/// Read `generator`, a value type, as a curried function of `count` cells:
/// each cell's domain's path layers, and the two sides of the path type its
/// last returner names, under the cells' binders.
///
/// # Specification
/// - requires: `generator` stands under the judgement's binders.
/// - ensures: one layer count per cell, and the sides `u` and `v` of the path
///   type the last returner names, scoped under `count` binders, the first cell
///   outermost; the binders opened to read them are closed again.
/// - fails: [`CheckRefusal::ShapeMismatch`] for a layer that is no thunk of an
///   arrow into a pure returner, or a result that is no path type; a
///   conversion's own refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
#[spec(captures: depth = context.depth(Zone::Intuitionistic), ensures: context.depth(Zone::Intuitionistic) == depth)]
fn telescope(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    generator: ValueTypeId,
    count: Cells,
) -> Result<(Vec<Layers>, (ValueId, ValueId)), CheckRefusal>
{
    let mut opened = Cells(0);
    let read = curried(context, at, generator, count, &mut opened);
    let mut closed = Ok(());
    for _ in 0 .. opened.0 {
        if context.binders().close(Zone::Intuitionistic).is_err() {
            closed = Err(CheckRefusal::MachineInvariant);
        }
    }
    closed?;
    read
}

/// The walk [`telescope`] closes the binders of, counting each it opens in
/// `opened`.
///
/// # Specification
/// - requires: as [`telescope`].
/// - ensures: as [`telescope`], with `opened` binders left open.
/// - fails: as [`telescope`].
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
#[spec(captures: before = *opened, ensures: *opened >= before)]
fn curried(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    generator: ValueTypeId,
    count: Cells,
    opened: &mut Cells,
) -> Result<(Vec<Layers>, (ValueId, ValueId)), CheckRefusal>
{
    let mut domains = Vec::with_capacity(count.0);
    let mut current = generator;
    for _ in 0 .. count.0 {
        let head = context.whnf_value_type(current)?;
        let not_a_function = CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            wanted: ExpectedShape::Arrow,
            found: TypeNode::Value(head),
        };
        let ValueTypeView::Thunk(arrow) = value_type_view(context.arena(), head)?
        else {
            return Err(not_a_function);
        };
        let arrow = context.whnf_comp_type(arrow)?;
        let (domain, codomain) = match comp_type_view(context.arena(), arrow)? {
            CompTypeView::Pi { domain, codomain } => (domain, codomain),
            CompTypeView::Arrow { domain, codomain } => {
                let arena = context.arena_mut();
                let lifted = gandr_core_term::shift_comp_type(arena, codomain, Binders::ONE);
                (domain, lifted.settle(arena))
            },
            CompTypeView::Returner { .. }
            | CompTypeView::With(..)
            | CompTypeView::Element { .. }
            | CompTypeView::Codata { .. }
            | CompTypeView::Unknown => return Err(not_a_function),
        };
        domains.push(layers(context, domain)?);
        context.binders().open(Zone::Intuitionistic, domain);
        opened.0 = opened.0.saturating_add(1);
        let returned = context.whnf_comp_type(codomain)?;
        current = match comp_type_view(context.arena(), returned)? {
            CompTypeView::Returner { result, effects }
                if effects.purity() == gandr_core_term::effect::Purity::Pure =>
            {
                result
            },
            CompTypeView::Returner { .. }
            | CompTypeView::With(..)
            | CompTypeView::Arrow { .. }
            | CompTypeView::Pi { .. }
            | CompTypeView::Element { .. }
            | CompTypeView::Codata { .. }
            | CompTypeView::Unknown => return Err(not_a_function),
        };
    }
    let head = context.whnf_value_type(current)?;
    let ValueTypeView::Path { left, right, .. } = value_type_view(context.arena(), head)?
    else {
        return Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            wanted: ExpectedShape::Path,
            found: TypeNode::Value(head),
        });
    };
    Ok((domains, (left, right)))
}

/// How many path layers `ty` holds: a path, a flow or a bridge counts one and
/// its carrier's layers.
///
/// # Specification
/// - requires: `ty` stands under the judgement's binders.
/// - ensures: the count of nested path, flow and bridge formers, each read in
///   weak head form, the outermost first.
/// - fails: a conversion's own refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
#[spec(captures: depth = context.depth(Zone::Intuitionistic), ensures: context.depth(Zone::Intuitionistic) == depth)]
fn layers(
    context: &mut CheckingContext<'_>,
    ty: ValueTypeId,
) -> Result<Layers, CheckRefusal>
{
    let mut count = 0_usize;
    let mut current = ty;
    loop {
        let head = context.whnf_value_type(current)?;
        let (ValueTypeView::Path { carrier, .. }
        | ValueTypeView::Flow { carrier, .. }
        | ValueTypeView::Bridge { carrier, .. }) = value_type_view(context.arena(), head)?
        else {
            return Ok(Layers(count));
        };
        count = count.saturating_add(1);
        current = carrier;
    }
}

/// Read the cell `cell` of type `found` against its domain's `wanted` layers:
/// a cell of the chain, or a cell of `X` one layer deeper.
///
/// # Specification
/// - requires: `cell` and `found` stand under the judgement's binders.
/// - ensures: the cell as read, and the carrier and the two ends of the chain
///   cell it is or lifts.
/// - fails: [`CheckRefusal::GeneratorFamilyUnsupported`] for a lifted cell that
///   is a flow or a bridge; [`CheckRefusal::ShapeMismatch`] for a cell that is
///   no path at its domain's depth or one deeper; a conversion's own refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_fill_refuses_each_defect_by_name`
#[spec(ensures: |ret| !matches!(ret, Err(CheckRefusal::GeneratorFamilyUnsupported { cell: named, .. }) if named != cell))]
fn classify(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    cell: ValueId,
    found: ValueTypeId,
    wanted: Layers,
) -> Result<(Cell, (ValueTypeId, ValueId, ValueId)), CheckRefusal>
{
    let not_a_cell = |found| CheckRefusal::ShapeMismatch {
        at: TermNode::Value(cell),
        wanted: ExpectedShape::Path,
        found: TypeNode::Value(found),
    };
    let depth = layers(context, found)?;
    let head = context.whnf_value_type(found)?;
    if depth == wanted {
        let ValueTypeView::Path {
            carrier,
            left,
            right,
        } = value_type_view(context.arena(), head)?
        else {
            return Err(not_a_cell(head));
        };
        return Ok((Cell::Plain(cell), (carrier, left, right)));
    }
    if depth != Layers(wanted.0.saturating_add(1)) {
        return Err(not_a_cell(head));
    }
    let view = value_type_view(context.arena(), head)?;
    if let ValueTypeView::Flow { .. } = view {
        return Err(CheckRefusal::GeneratorFamilyUnsupported {
            at,
            cell,
            family: UnsupportedFamily::Flow,
        });
    }
    if let ValueTypeView::Bridge { .. } = view {
        return Err(CheckRefusal::GeneratorFamilyUnsupported {
            at,
            cell,
            family: UnsupportedFamily::Bridge,
        });
    }
    let ValueTypeView::Path {
        carrier: inner,
        left: lo,
        right: hi,
    } = view
    else {
        return Err(not_a_cell(head));
    };
    let inner = context.whnf_value_type(inner)?;
    let ValueTypeView::Path {
        carrier,
        left,
        right,
    } = value_type_view(context.arena(), inner)?
    else {
        return Err(not_a_cell(inner));
    };
    Ok((Cell::Lifted { lo, hi, path: cell }, (carrier, left, right)))
}

/// The composite tree of `side`, scoped under the `count` cells' binders: its
/// nodes, each child after its parent, with the span each composes.
///
/// # Specification
/// - requires: `side` is scoped under `count` binders, the first cell
///   outermost.
/// - ensures: the tree whose leaves are the cells `side` reads and whose
///   composites are its transports, its `compose` nodes and the composite a
///   `then` returns, a composite of more than two cells nested to the left,
///   when every composite joins two consecutive spans and the root spans every
///   cell; nothing otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `c₁ then c₂` reads as the composite of the two cells, and
///   a side that mentions no cell reads as none.
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
/// - witness: `fill::tests::a_fill_refuses_each_defect_by_name`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|tree| tree.first().is_some_and(|root| root.first == 0 && root.last.saturating_add(1) == count.0)))]
fn composite_of(
    arena: &CoreArena,
    side: ValueId,
    count: Cells,
) -> Option<Vec<Spanned>>
{
    let mut values: Vec<Option<ValueId>> = Vec::from([Some(side)]);
    let mut sides: Vec<Option<Side>> = Vec::from([None]);
    let mut index = 0_usize;
    while index < values.len() {
        if let Some(Some(value)) = values.get(index).copied() {
            let node = arena.value(value)?;
            let read = if let Value::Variable {
                zone: Zone::Intuitionistic,
                index: bound,
            } = *node
            {
                let bound = usize::try_from(u32::from(bound)).ok()?;
                if bound >= count.0 {
                    return None;
                }
                Side::Leaf(count.0.saturating_sub(1).saturating_sub(bound))
            }
            else if let Value::Returned(composite) = *node {
                // `c₁ then c₂` returns the binary composite (#4057), read as
                // the `compose` node it returns.
                if let Some(&Computation::Return(returned)) = arena.computation(composite)
                    && let Some(&Value::Compose { .. }) = arena.value(returned)
                {
                    values.get_mut(index)?.replace(returned);
                    continue;
                }
                let &Computation::PathTransport {
                    motive,
                    path: second,
                    value: first,
                } = arena.computation(composite)?
                else {
                    return None;
                };
                let &ValueType::Path { right, .. } = arena.value_type(motive)?
                else {
                    return None;
                };
                if arena.value(right)
                    != Some(&Value::Variable {
                        zone: Zone::Intuitionistic,
                        index: DeBruijnIndex::from(0_u32),
                    })
                {
                    return None;
                }
                let next = values.len();
                values.extend([Some(first), Some(second)]);
                sides.extend([None, None]);
                Side::Composite(next, next.saturating_add(1))
            }
            else if let Value::Compose { ref cells, .. } = *node {
                let (&head, rest) = cells.split_first()?;
                let Some((&last, middle)) = rest.split_last()
                else {
                    values.get_mut(index)?.replace(head);
                    continue;
                };
                let mut left = values.len();
                values.push(Some(head));
                sides.push(None);
                for &cell in middle {
                    let right = values.len();
                    values.extend([Some(cell), None]);
                    sides.extend([None, Some(Side::Composite(left, right))]);
                    left = right.saturating_add(1);
                }
                let right = values.len();
                values.push(Some(last));
                sides.push(None);
                Side::Composite(left, right)
            }
            else {
                return None;
            };
            *sides.get_mut(index)? = Some(read);
        }
        index = index.saturating_add(1);
    }
    spanned(&sides, count)
}

/// The spans of `sides`, each child after its parent, read children first.
///
/// # Specification
/// - requires: every child index is greater than its parent's.
/// - ensures: each node with the first and the last cell it composes, when
///   every composite joins consecutive spans and the root spans all `count`
///   cells; nothing otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`composite_of`].
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|tree| tree.len() == sides.len()))]
fn spanned(
    sides: &[Option<Side>],
    count: Cells,
) -> Option<Vec<Spanned>>
{
    let mut spans: Vec<Option<(usize, usize)>> = Vec::from_iter(sides.iter().map(|_| None));
    for (index, side) in sides.iter().enumerate().rev() {
        let span = match (*side)? {
            Side::Leaf(cell) => (cell, cell),
            Side::Composite(first, second) => {
                let (start, middle) = (*spans.get(first)?)?;
                let (next, end) = (*spans.get(second)?)?;
                if middle.saturating_add(1) != next {
                    return None;
                }
                (start, end)
            },
        };
        *spans.get_mut(index)? = Some(span);
    }
    let tree: Option<Vec<Spanned>> = sides
        .iter()
        .zip(&spans)
        .map(|(side, span)| {
            let (first, last) = (*span)?;
            Some(Spanned {
                side: (*side)?,
                first,
                last,
            })
        })
        .collect();
    let tree = tree?;
    let root = tree.first()?;
    (root.first == 0 && root.last.saturating_add(1) == count.0).then_some(tree)
}

/// `side`, scoped under one binder per value of `values`, with each binder
/// replaced by its value: the side at those cells, for a refusal to name.
///
/// # Specification
/// - requires: `side` is scoped under `values.len()` binders, the first
///   outermost, and each value stands where the side's binders do not.
/// - ensures: the side with every binder instantiated.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_fill_refuses_each_defect_by_name`
#[spec(ensures: |ret| values.is_empty() == (ret == side) || arena.value(ret).is_some())]
fn instantiated(
    arena: &mut CoreArena,
    side: ValueId,
    values: &[ValueId],
) -> ValueId
{
    let mut held = side;
    for (outer, &value) in values.iter().enumerate().rev() {
        let outer = Binders::from(u32::try_from(outer).unwrap_or(u32::MAX));
        let lifted = gandr_core_term::shift_value(arena, value, outer).settle(arena);
        held = gandr_core_term::instantiate_value(arena, held, lifted);
    }
    held
}

/// What builds the square and its induction from the generator, the chain
/// and the two sides' trees.
struct Builder<'chain>
{
    /// The computation returning `t`, in the fill's own context.
    generator: ComputationId,
    /// The chain, in the fill's own context.
    chain: &'chain Chain,
    /// The tree of `t`'s left side.
    u: &'chain [Spanned],
    /// The tree of `t`'s right side.
    v: &'chain [Spanned],
}

impl Builder<'_>
{
    /// The square at `cells`, every value read `shift` binders past the fill's
    /// own context.
    ///
    /// # Specification
    /// - requires: `cells` stand `shift` binders past the fill's context.
    /// - ensures: `Path(Path(P, u⁻, v⁺), t⁻ then (v ↑ X), (u ↑ X) then t⁺)` for
    ///   `P` the path between the chain's ends.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
    #[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&ValueType::Path { .. })))]
    fn square(
        &self,
        arena: &mut CoreArena,
        shift: Binders,
        cells: &[Cell],
    ) -> ValueTypeId
    {
        let carrier = lift_type(arena, self.chain.carrier, shift);
        let vertices: Vec<ValueId> = self
            .chain
            .vertices
            .iter()
            .map(|&vertex| lift_value(arena, vertex, shift))
            .collect();
        let (lo, hi): (Vec<ValueId>, Vec<ValueId>) = cells
            .iter()
            .map(|cell| match *cell {
                Cell::Plain(value) => (value, value),
                Cell::Lifted { lo, hi, .. } => (lo, hi),
            })
            .unzip();
        let (start, end) = (
            vertices
                .first()
                .copied()
                .unwrap_or_else(|| arena.value_unit()),
            vertices
                .last()
                .copied()
                .unwrap_or_else(|| arena.value_unit()),
        );
        let composites = arena.value_type_path(carrier, start, end);
        let t_lo = self.applied(arena, shift, &lo);
        let t_hi = self.applied(arena, shift, &hi);
        let u = lifted(arena, carrier, &vertices, self.u, cells);
        let v = lifted(arena, carrier, &vertices, self.v, cells);
        let u_up = u.lift.unwrap_or_else(|| arena.value_here(u.lo));
        let v_up = v.lift.unwrap_or_else(|| arena.value_here(v.lo));
        let source = identity::then(arena, composites, u.lo, t_lo, v_up);
        let source = arena.value_returned(source);
        let target = identity::then(arena, composites, u.lo, u_up, t_hi);
        let target = arena.value_returned(target);
        let sides = arena.value_type_path(composites, u.lo, v.hi);
        arena.value_type_path(sides, source, target)
    }

    /// `t` applied to `cells`, each standing `shift` binders past the fill's
    /// own context: the value its last application returns.
    ///
    /// # Specification
    /// - requires: `cells` stand `shift` binders past the fill's context.
    /// - ensures: `⟨force ⟨… force ⟨t⟩ c₁ …⟩ cₘ⟩`, `t` the generator's
    ///   computation lifted past `shift` binders.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
    #[spec(ensures: |ret| matches!(arena.value(ret), Some(&Value::Returned(_))))]
    fn applied(
        &self,
        arena: &mut CoreArena,
        shift: Binders,
        cells: &[ValueId],
    ) -> ValueId
    {
        let generator =
            gandr_core_term::shift_computation_under(arena, self.generator, Binders::NONE, shift)
                .settle(arena);
        let mut function = arena.value_returned(generator);
        for &cell in cells {
            let forced = arena.computation_force(function);
            let applied = arena.computation_application(forced, cell);
            function = arena.value_returned(applied);
        }
        function
    }

    /// The based path induction on the cell of `X` at `position`, from `lo`
    /// along `path`, its base `base`: the earlier cells of `X` at their left
    /// ends and `here`, the later at their paths.
    ///
    /// # Specification
    /// - requires: `base` fills the square with this cell and every earlier
    ///   cell of `X` at its left end and `here`, in the fill's own context.
    /// - ensures: the telescope transport along `path` and `here(path)` from
    ///   `here(lo)`, its motive the square with this cell's right end and path
    ///   bound.
    /// - fails: a machine invariant for a position that is no cell of `X`.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
    #[spec(ensures: |ret| ret.as_ref().is_err_and(|refusal| *refusal == CheckRefusal::MachineInvariant) || ret.as_ref().is_ok_and(|realised| matches!(arena.computation(*realised), Some(&Computation::TelescopeTransport { .. }))))]
    fn induction(
        &self,
        arena: &mut CoreArena,
        cells: &[Cell],
        (position, lo, path): (Position, ValueId, ValueId),
        base: ValueId,
    ) -> Result<ComputationId, CheckRefusal>
    {
        let two = Binders::from(2_u32);
        let moving = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let over = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let mut bound = Vec::with_capacity(cells.len());
        for (index, cell) in cells.iter().enumerate() {
            bound.push(match *cell {
                Cell::Plain(value) => Cell::Plain(lift_value(arena, value, two)),
                Cell::Lifted { lo: low, .. } if index < position.0 => {
                    let low = lift_value(arena, low, two);
                    let reflexive = arena.value_here(low);
                    Cell::Lifted {
                        lo: low,
                        hi: low,
                        path: reflexive,
                    }
                },
                Cell::Lifted { lo: low, .. } if index == position.0 => Cell::Lifted {
                    lo: lift_value(arena, low, two),
                    hi: moving,
                    path: over,
                },
                Cell::Lifted {
                    lo: low,
                    hi,
                    path: along,
                } => Cell::Lifted {
                    lo: lift_value(arena, low, two),
                    hi: lift_value(arena, hi, two),
                    path: lift_value(arena, along, two),
                },
            });
        }
        let square = self.square(arena, two, &bound);
        let returned = arena.comp_type_returner(square);
        let domain = self.cell_type(arena, position)?;
        let lifted_domain = lift_type(arena, domain, Binders::ONE);
        let lifted_lo = lift_value(arena, lo, Binders::ONE);
        let moving = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let based = arena.value_type_path(lifted_domain, lifted_lo, moving);
        let inner = arena.comp_type_pi(based, returned);
        let motive = arena.comp_type_pi(domain, inner);
        let start = arena.value_here(lo);
        let along = arena.value_here(path);
        Ok(arena.computation_telescope_transport(motive, path, start, along, base))
    }

    /// The type of the chain's cell at `position`, in the fill's own context.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Path(A, xᵢ, xᵢ₊₁)` for the cell's two vertices.
    /// - fails: a machine invariant for a position past the chain.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
    #[spec(ensures: |ret| ret.is_err() || matches!(arena.value_type(*ret.as_ref().unwrap_or(&self.chain.carrier)), Some(&ValueType::Path { .. })))]
    fn cell_type(
        &self,
        arena: &mut CoreArena,
        position: Position,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let (&left, &right) = self
            .chain
            .vertices
            .get(position.0)
            .zip(self.chain.vertices.get(position.0.saturating_add(1)))
            .ok_or(CheckRefusal::MachineInvariant)?;
        Ok(arena.value_type_path(self.chain.carrier, left, right))
    }
}

/// A side's tree read at `cells`: each node's two ends and its lift, children
/// first, the root's answered.
///
/// # Specification
/// - requires: `carrier`, `vertices` and `cells` stand in one context; `tree`'s
///   leaves name cells of `cells`.
/// - ensures: the root's ends, `then` folds of its cells' ends, and its lift: a
///   lifted cell's path, a composite with one lifted half that half whiskered
///   by the other, both lifted halves the right whisker then the left, and
///   nothing for a side that meets no cell of `X`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
#[spec(ensures: |ret| arena.value(ret.lo).is_some() && arena.value(ret.hi).is_some())]
fn lifted(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
    vertices: &[ValueId],
    tree: &[Spanned],
    cells: &[Cell],
) -> Read
{
    let unit = arena.value_unit();
    let mut reads: Vec<Read> = Vec::from_iter(tree.iter().map(|_| Read {
        lo: unit,
        hi: unit,
        lift: None,
    }));
    for (index, node) in tree.iter().enumerate().rev() {
        let read = match node.side {
            Side::Leaf(cell) => match cells.get(cell) {
                Some(&Cell::Plain(value)) => Read {
                    lo: value,
                    hi: value,
                    lift: None,
                },
                Some(&Cell::Lifted { lo, hi, path }) => Read {
                    lo,
                    hi,
                    lift: Some(path),
                },
                None => Read {
                    lo: unit,
                    hi: unit,
                    lift: None,
                },
            },
            Side::Composite(first, second) => {
                let left = reads.get(first).copied().unwrap_or(Read {
                    lo: unit,
                    hi: unit,
                    lift: None,
                });
                let right = reads.get(second).copied().unwrap_or(left);
                let start = vertices.get(node.first).copied().unwrap_or(unit);
                let end = vertices
                    .get(node.last.saturating_add(1))
                    .copied()
                    .unwrap_or(unit);
                let lo = identity::then(arena, carrier, start, left.lo, right.lo);
                let lo = arena.value_returned(lo);
                let hi = identity::then(arena, carrier, start, left.hi, right.hi);
                let hi = arena.value_returned(hi);
                let ends = (carrier, start, end);
                let lift = match (left.lift, right.lift) {
                    (None, None) => None,
                    (Some(alpha), None) => Some(identity::whisker(
                        arena,
                        ends,
                        (left.lo, right.lo),
                        Whisker::Right,
                        alpha,
                    )),
                    (None, Some(beta)) => Some(identity::whisker(
                        arena,
                        ends,
                        (left.lo, right.lo),
                        Whisker::Left,
                        beta,
                    )),
                    (Some(alpha), Some(beta)) => {
                        let first = identity::whisker(
                            arena,
                            ends,
                            (left.lo, right.lo),
                            Whisker::Right,
                            alpha,
                        );
                        let second = identity::whisker(
                            arena,
                            ends,
                            (left.hi, right.lo),
                            Whisker::Left,
                            beta,
                        );
                        let composites = arena.value_type_path(carrier, start, end);
                        let both = identity::then(arena, composites, lo, first, second);
                        Some(arena.value_returned(both))
                    },
                };
                Read { lo, hi, lift }
            },
        };
        if let Some(slot) = reads.get_mut(index) {
            *slot = read;
        }
    }
    reads.first().copied().unwrap_or(Read {
        lo: unit,
        hi: unit,
        lift: None,
    })
}

/// `value` read `amount` binders deeper.
///
/// # Specification
/// trivial.
fn lift_value(
    arena: &mut CoreArena,
    value: ValueId,
    amount: Binders,
) -> ValueId
{
    gandr_core_term::shift_value(arena, value, amount).settle(arena)
}

/// `ty` read `amount` binders deeper.
///
/// # Specification
/// trivial.
fn lift_type(
    arena: &mut CoreArena,
    ty: ValueTypeId,
    amount: Binders,
) -> ValueTypeId
{
    gandr_core_term::shift_value_type(arena, ty, amount).settle(arena)
}
