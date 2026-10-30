//! `fill[n, k](chain(m), t, d)`: the filler generator `t ↑ X` over a chain of
//! paths at a certified stratum.
//!
//! # The rule
//!
//! The head names the degree `n` and the bound `k`, certified over the chain
//! sub-site as [`crate::compose`] certifies a composite's. `d` lists the
//! chain's `m` cells, `(d₁, …, dₘ)`, or its whole pasting context in Catt's
//! order, `(x₀, x₁, d₁, …, xₘ, dₘ)`: the first vertex, then each later vertex
//! and the cell that ends there. The count tells the two apart. `t` is a
//! curried function of the entries `d` lists into a path type: of dimension
//! two, `Path(P, u, v)` with its sides `u` and `v` composites of the cells, or
//! of dimension one, a path between the chain's two ends.
//!
//! Each entry is of its domain's type, or a path between two such entries one
//! path layer deeper: the entries of `X`. The family of `X` is the former of
//! that layer. A `Path` entry has its instance here, and a `Flow` entry or a
//! bridge is refused [`CheckRefusal::GeneratorFamilyUnsupported`] with the
//! unit that lands its instance. A vertex of `X` needs each cell beside it in
//! `X` and a generator of dimension one, Catt's conditions on the set. A cell
//! of `X` beside a vertex of `X` is a square, its path type running from `c⁻
//! then y→` to `x→ then c⁺`, each `then` absent at a vertex outside `X`.
//!
//! The square is Catt's: from `t[X⁻] then (v ↑ X)` to `(u ↑ X) then t[X⁺]`,
//! `X⁻` and `X⁺` the entries of `X` read at their left and right ends. Of
//! dimension one, `u` and `v` are the chain's two ends, each lifting as its
//! path in `X` and as `here` outside it. Of dimension two, a side's lift is
//! built over its composite structure: a cell of `X` lifts as its path, any
//! other cell stays, and a composite whose one half lifts is that half
//! whiskered by the other, the action of composing with it, as `math.path`
//! writes `whiskerLeft` and `whiskerRight`. A composite both of whose halves
//! lift is the right whisker then the left.
//!
//! The filler is the family's own induction, with base `here(t[X⁻])` once
//! every path is `here`, by `then`'s unit laws. Each vertex path of `X`
//! inducts first, in vertex order, its motive a function of every cell of
//! `X`'s right end and path, whose types mention the vertex. Inside, with each
//! vertex at `here`, a cell's square reads as a based path, and based path
//! induction runs on each cell of `X` in vertex order, the outermost first.
//! The rule checks the induction against the square and records it three ways
//! (`CheckingContext::record_fill`): as the node's decision
//! ([`crate::nested::Nesting::Filled`]), so the elaboration stands the node as
//! that induction; in the lowered chain evaluation reads, so the fill computes
//! to its induction wherever it stands; and in the natives, so a fill in a
//! type crosses to the kernel as the value its induction returns. A filler
//! over `here` cells reduces to `here`, in a type as in a term.
//!
//! A refusal names its defect: [`CheckRefusal::FillUncertified`] for the
//! stratum, `compose`'s own refusals for a pasting or cells that do not fill
//! the chain, [`CheckRefusal::NoFiller`] for sides that are no composites of
//! the cells, an `X` of no cell, a vertex of `X` beside a cell outside it or
//! under a generator of dimension two, a cell's square whose sides are no
//! whiskers of its vertices' paths, or a square asked for that is not the
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
//! - `vault:01a178aa-5f59-7323-a77d-6f8114cedbba` — lineage: § The filler ban —
//!   the machine adjoins no cell, so a fill computes to its induction wherever
//!   it stands.
//! - Thibaut Benjamin, Ioannis Markakis, Wilfred Offord, Chiara Sarti and Jamie
//!   Vicary. "Naturality for Higher-Dimensional Path Types." (2025).
//!   `arXiv:2501.11620` — `t ↑ X` and its square, the conditions on `X`;
//!   Examples 1.1 to 1.3, the composite's naturality in a cell and in its whole
//!   context, and the associator's.

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
use gandr_core_term::compose::Pasting;
use gandr_core_term::identity;
use gandr_core_term::identity::Whisker;
use gandr_core_term::ua::Stratum;
use gandr_kernel_term::DeBruijnIndex;

use crate::compose::Endpoint;
use crate::context::CheckingContext;
use crate::conversion::Agreement;
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

/// A vertex's place in the chain, from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Vertex(usize);

/// An entry of `X`'s rank among the vertices of `X` or among its cells, in
/// vertex order from zero; or how many of the vertices' inductions stand
/// outside a point.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Rank(usize);

/// How the fill lists its entries.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Listing
{
    /// One entry per cell of the chain or of a level-two shape, its vertices
    /// fixed.
    Cells,
    /// A chain's pasting context in Catt's order, `x₀, x₁, c₁, …, xₘ, cₘ`:
    /// the first vertex, then each later vertex and the cell ending there. A
    /// chain of `m` cells lists it in its `2m + 1` entries.
    Pasting,
}

/// What an entry of the fill is, by its index in the chain from zero.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Entry
{
    /// The vertex at this index.
    Vertex(usize),
    /// The cell at this index, from the vertex at it to the next.
    Cell(usize),
}

impl Listing
{
    /// What the entry at `position` is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each entry a cell when the cells are listed; in the pasting
    ///   context, `0` the first vertex, an odd position the vertex after it,
    ///   and an even one past zero the cell ending at the vertex before it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cells listed, and the pasting context of one
    ///   cell, read their vertices and their cells in place.
    /// - witness: `fill::tests::a_cell_of_dimension_one_fills_its_square_by_induction`
    /// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
    #[spec(ensures: |ret| self == Self::Pasting || ret == Entry::Cell(position.0))]
    fn entry(
        self,
        position: Position,
    ) -> Entry
    {
        match self {
            Self::Cells => Entry::Cell(position.0),
            Self::Pasting if position.0.is_multiple_of(2) && position.0 > 0 => {
                Entry::Cell(position.0.div_ceil(2).saturating_sub(1))
            },
            Self::Pasting => Entry::Vertex(position.0.div_ceil(2)),
        }
    }

    /// Where the vertex at `vertex` stands among the entries, when they list
    /// it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing when the cells are listed; in the pasting context,
    ///   `0` for the first vertex and `2i - 1` for the `i`-th after it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::entry`].
    /// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
    #[spec(ensures: |ret| ret.is_none_or(|place| self.entry(place) == Entry::Vertex(vertex.0)))]
    fn vertex(
        self,
        vertex: Vertex,
    ) -> Option<Position>
    {
        match self {
            Self::Cells => None,
            Self::Pasting => Some(Position(vertex.0.saturating_mul(2).saturating_sub(1))),
        }
    }
}

/// What an entry is to the induction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Role
{
    /// An entry outside `X`, which no induction moves.
    Fixed,
    /// A vertex of `X`, at this rank among them in vertex order.
    Vertex(usize),
    /// A cell of `X`, at this rank among them in vertex order.
    Cell(usize),
}

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

/// What the generator's path relates.
#[derive(Clone, Copy, Debug)]
enum Generated<'tree>
{
    /// A cell of dimension two: its sides are composites of the chain's
    /// cells.
    Composites
    {
        /// The tree of `t`'s left side.
        u: &'tree [Spanned],
        /// The tree of `t`'s right side.
        v: &'tree [Spanned],
    },
    /// A cell of dimension one: a path between the chain's two ends.
    Ends,
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
    /// The `m + 1` vertices, in order, each of `X` at its left end.
    vertices: Vec<ValueId>,
}

/// A generator's type read as a curried function of the fill's entries into
/// a path type.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Curried
{
    /// Each entry's domain's path layers, in order.
    domains: Vec<Layers>,
    /// The path layers of the type the last returner names.
    result: Layers,
    /// That path type's two sides, scoped under the entries' binders.
    sides: (ValueId, ValueId),
}

/// Derive the square and the induction of the fill at `at`, its generator's
/// type first in `types` and its entries' after it.
///
/// # Specification
/// - requires: `at` is a fill; `types` are the type its generator's computation
///   returns and the types its entries synthesised, in that order, all under
///   the judgement's binders.
/// - ensures: the square `t ↑ X` fills over the stratum the node names, and the
///   induction realising it, both under the judgement's binders.
/// - fails: as the module states; [`CheckRefusal::ShapeMismatch`] for a
///   generator that is no curried function of the entries into a path type, or
///   an entry neither of its domain's type nor a path one layer deeper;
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
///   induction, from `u` at the path's left end to `v` at its right, under a
///   generator of dimension two and of dimension one. Paths between the
///   vertices of one cell and a square over that cell fill theirs. Sides that
///   are no composites, an `X` of no cell, an uncertified stratum, a `Flow`
///   cell, a vertex of `X` beside a cell outside it and a cell's square whose
///   side is no whisker of its vertex's path are each refused by name. The
///   whisker names `X` by its columns, and a column at a plain cell or of two
///   2-cells is refused by name.
/// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
/// - witness: `fill::tests::a_cell_of_dimension_one_fills_its_square_by_induction`
/// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
/// - witness: `fill::tests::a_fill_refuses_each_defect_by_name`
/// - witness: `fill::tests::a_set_that_is_no_pasting_context_is_refused`
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
    let (&generator_type, entry_types) =
        types.split_first().ok_or(CheckRefusal::MachineInvariant)?;
    if entry_types.len() != written.len() {
        return Err(CheckRefusal::MachineInvariant);
    }
    let listing = match composite.pasting {
        Pasting::Chain { cells: count }
            if written.len() == usize::from(count).saturating_mul(2).saturating_add(1) =>
        {
            Listing::Pasting
        },
        Pasting::Chain { .. } | Pasting::Columns { .. } => Listing::Cells,
    };
    let Curried {
        domains,
        result,
        sides,
    } = telescope(context, at, generator_type, Cells(written.len()))?;
    let mut read = Vec::with_capacity(written.len());
    let mut ends = Vec::with_capacity(written.len());
    let mut carrier = None;
    let mut cell_layers = None;
    for (index, ((&entry, &found), &wanted)) in
        written.iter().zip(entry_types).zip(&domains).enumerate()
    {
        match listing.entry(Position(index)) {
            Entry::Vertex(_) => read.push(classify_vertex(context, at, entry, found, wanted)?),
            Entry::Cell(_) => {
                let (held, (path_carrier, left, right)) =
                    classify(context, at, entry, found, wanted)?;
                carrier.get_or_insert(path_carrier);
                cell_layers.get_or_insert(wanted);
                read.push(held);
                ends.push((left, right));
            },
        }
    }
    let (carrier, cell_layers) = carrier
        .zip(cell_layers)
        .ok_or(CheckRefusal::MachineInvariant)?;
    let refusal = (at, sides, composite.stratum);
    let diagram: Vec<_> = match listing {
        Listing::Cells => ends
            .iter()
            .map(|&(left, right)| {
                crate::compose::cell(Endpoint::Known(left), Endpoint::Known(right))
            })
            .collect(),
        Listing::Pasting => {
            bordered(context, refusal, &mut read)?;
            let corners: Vec<ValueId> = (0 ..= ends.len())
                .filter_map(|vertex| listing.vertex(Vertex(vertex)))
                .filter_map(|place| read.get(place.0))
                .map(|cell| match *cell {
                    Cell::Plain(value) | Cell::Lifted { lo: value, .. } => value,
                })
                .collect();
            corners
                .windows(2)
                .map(|pair| match *pair {
                    [left, right] => {
                        crate::compose::cell(Endpoint::Known(left), Endpoint::Known(right))
                    },
                    _ => crate::compose::cell(Endpoint::Unknown, Endpoint::Unknown),
                })
                .collect()
        },
    };
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
    let mut vertices = Vec::with_capacity(diagram.len().saturating_add(1));
    vertices.push(start);
    for boundary in &diagram {
        let &[Endpoint::Known(end)] = boundary.outputs()
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        vertices.push(end);
    }
    let chain = Chain { carrier, vertices };
    let trees = if result == cell_layers {
        None
    }
    else if result == Layers(cell_layers.0.saturating_add(1)) && listing == Listing::Cells {
        let arena = context.arena();
        let (Some(u), Some(v)) = (
            composite_of(arena, sides.0, Cells(read.len())),
            composite_of(arena, sides.1, Cells(read.len())),
        )
        else {
            return Err(refused(context.arena_mut(), refusal, &read));
        };
        Some((u, v))
    }
    else {
        return Err(refused(context.arena_mut(), refusal, &read));
    };
    let generated = match trees {
        Some((ref u, ref v)) => Generated::Composites { u, v },
        None => Generated::Ends,
    };
    let mut roles = Vec::with_capacity(read.len());
    let mut vertices_of_x = Vec::new();
    let mut cells_of_x = Vec::new();
    for (index, cell) in read.iter().enumerate() {
        roles.push(match (*cell, listing.entry(Position(index))) {
            (Cell::Plain(_), Entry::Vertex(_) | Entry::Cell(_)) => Role::Fixed,
            (Cell::Lifted { .. }, Entry::Vertex(_)) => {
                vertices_of_x.push(Position(index));
                Role::Vertex(vertices_of_x.len().saturating_sub(1))
            },
            (Cell::Lifted { .. }, Entry::Cell(_)) => {
                cells_of_x.push(Position(index));
                Role::Cell(cells_of_x.len().saturating_sub(1))
            },
        });
    }
    if cells_of_x.is_empty() {
        return Err(refused(context.arena_mut(), refusal, &read));
    }
    let builder = Builder {
        generator,
        chain: &chain,
        listing,
        generated,
    };
    let arena = context.arena_mut();
    let square = builder.square(arena, Binders::NONE, &read);
    let realised = builder.realised(arena, (&read, &roles), (&vertices_of_x, &cells_of_x))?;
    Ok(Realisation { square, realised })
}

/// Read `generator`, a value type, as a curried function of `count` entries:
/// each entry's domain's path layers, the path layers of the type its last
/// returner names, and that path type's two sides, under the entries' binders.
///
/// # Specification
/// - requires: `generator` stands under the judgement's binders.
/// - ensures: one layer count per entry, the result's layer count, and the
///   sides of the path type the last returner names, scoped under `count`
///   binders, the first entry outermost; the binders opened to read them are
///   closed again.
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
) -> Result<Curried, CheckRefusal>
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
) -> Result<Curried, CheckRefusal>
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
    let result = layers(context, head)?;
    Ok(Curried {
        domains,
        result,
        sides: (left, right),
    })
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
    let (inner, lo, hi) = lifted_path(context, at, cell, head)?;
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

/// Read the vertex `vertex` of type `found` against its domain's `wanted`
/// layers: a vertex of the chain, or a vertex of `X` one layer deeper.
///
/// # Specification
/// - requires: `vertex` and `found` stand under the judgement's binders.
/// - ensures: the vertex as read: itself at its domain's depth, or a path
///   between two vertices one deeper.
/// - fails: as [`lifted_path`] for a lifted vertex;
///   [`CheckRefusal::ShapeMismatch`] for a vertex at any other depth; a
///   conversion's own refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
#[spec(ensures: |ret| !matches!(ret, Err(CheckRefusal::GeneratorFamilyUnsupported { cell: named, .. }) if named != vertex))]
fn classify_vertex(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    vertex: ValueId,
    found: ValueTypeId,
    wanted: Layers,
) -> Result<Cell, CheckRefusal>
{
    let depth = layers(context, found)?;
    if depth == wanted {
        return Ok(Cell::Plain(vertex));
    }
    let head = context.whnf_value_type(found)?;
    if depth != Layers(wanted.0.saturating_add(1)) {
        return Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(vertex),
            wanted: ExpectedShape::Path,
            found: TypeNode::Value(head),
        });
    }
    let (_, lo, hi) = lifted_path(context, at, vertex, head)?;
    Ok(Cell::Lifted {
        lo,
        hi,
        path: vertex,
    })
}

/// The path type `head` is, the weak head of a lifted entry's type: its
/// carrier and its two ends.
///
/// # Specification
/// - requires: `head` is `entry`'s type in weak head form.
/// - ensures: the carrier and the two ends of a path type.
/// - fails: [`CheckRefusal::GeneratorFamilyUnsupported`] for a flow or a
///   bridge; [`CheckRefusal::ShapeMismatch`] for any other type.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_fill_refuses_each_defect_by_name`
#[spec(ensures: |ret| !matches!(ret, Err(CheckRefusal::GeneratorFamilyUnsupported { cell: named, .. }) if named != entry))]
fn lifted_path(
    context: &CheckingContext<'_>,
    at: ValueId,
    entry: ValueId,
    head: ValueTypeId,
) -> Result<(ValueTypeId, ValueId, ValueId), CheckRefusal>
{
    let view = value_type_view(context.arena(), head)?;
    if let ValueTypeView::Flow { .. } = view {
        return Err(CheckRefusal::GeneratorFamilyUnsupported {
            at,
            cell: entry,
            family: UnsupportedFamily::Flow,
        });
    }
    if let ValueTypeView::Bridge { .. } = view {
        return Err(CheckRefusal::GeneratorFamilyUnsupported {
            at,
            cell: entry,
            family: UnsupportedFamily::Bridge,
        });
    }
    let ValueTypeView::Path {
        carrier,
        left,
        right,
    } = view
    else {
        return Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(entry),
            wanted: ExpectedShape::Path,
            found: TypeNode::Value(head),
        });
    };
    Ok((carrier, left, right))
}

/// Read each cell of `X` in the pasting context `read` against its two
/// vertices: beside a vertex of `X` the cell is a square whose sides are its
/// ends whiskered by the vertices' paths, and it stands as those ends.
///
/// # Specification
/// - requires: `read` lists a pasting context in the judgement's context;
///   `sides` are the generator's, scoped under one binder per entry.
/// - ensures: each cell of `X` whose right vertex is in `X` at its left side's
///   first half, and whose left vertex is in `X` at its right side's second
///   half; every other entry as it stood.
/// - fails: [`CheckRefusal::NoFiller`] for a cell outside `X` beside a vertex
///   of `X`, or a side that is no whisker of its vertex's path; a conversion's
///   own refusal; a machine invariant for a context missing a vertex.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
/// - witness: `fill::tests::a_set_that_is_no_pasting_context_is_refused`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::NoFiller { at: site, .. }) => site == at,
    | Ok(()) | Err(_) => true,
})]
fn bordered(
    context: &mut CheckingContext<'_>,
    (at, sides, stratum): (ValueId, (ValueId, ValueId), Stratum),
    read: &mut [Cell],
) -> Result<(), CheckRefusal>
{
    for index in 0 .. read.len() {
        let Entry::Cell(cell) = Listing::Pasting.entry(Position(index))
        else {
            continue;
        };
        let (start, end) = Listing::Pasting
            .vertex(Vertex(cell))
            .zip(Listing::Pasting.vertex(Vertex(cell.saturating_add(1))))
            .and_then(|(start, end)| read.get(start.0).copied().zip(read.get(end.0).copied()))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let Some(&Cell::Lifted { lo, hi, path }) = read.get(index)
        else {
            if matches!(start, Cell::Lifted { .. }) || matches!(end, Cell::Lifted { .. }) {
                return Err(refused(context.arena_mut(), (at, sides, stratum), read));
            }
            continue;
        };
        let lo = match end {
            Cell::Lifted { path: along, .. } => unwhiskered(context, lo, along, Whisker::Right)?,
            Cell::Plain(_) => Some(lo),
        };
        let hi = match start {
            Cell::Lifted { path: along, .. } => unwhiskered(context, hi, along, Whisker::Left)?,
            Cell::Plain(_) => Some(hi),
        };
        let (Some(lo), Some(hi)) = (lo, hi)
        else {
            return Err(refused(context.arena_mut(), (at, sides, stratum), read));
        };
        if let Some(slot) = read.get_mut(index) {
            *slot = Cell::Lifted { lo, hi, path };
        }
    }
    Ok(())
}

/// The half of `side` a whisker by `along` leaves: `q` for `side` read as `q
/// then along` when `moving` is [`Whisker::Right`], and as `along then q` when
/// it is [`Whisker::Left`].
///
/// # Specification
/// - requires: `side` and `along` stand in the judgement's context.
/// - ensures: `q` when `side` is a binary composite whose other half converts
///   with `along`; nothing otherwise.
/// - fails: a conversion's own refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
/// - witness: `fill::tests::a_set_that_is_no_pasting_context_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |half| half.is_none_or(|half| half != side)))]
fn unwhiskered(
    context: &CheckingContext<'_>,
    side: ValueId,
    along: ValueId,
    moving: Whisker,
) -> Result<Option<ValueId>, CheckRefusal>
{
    let Some((first, second)) = halves(context.arena(), side)
    else {
        return Ok(None);
    };
    let (kept, whiskered) = match moving {
        Whisker::Right => (first, second),
        Whisker::Left => (second, first),
    };
    let agreement = crate::flow::convertible(context, whiskered, along)?;
    Ok((agreement == Agreement::Convertible).then_some(kept))
}

/// The two halves of `side` when it is a binary composite: the `compose` node
/// a `then` returns, a `compose` node of two cells, or the transport `then`
/// stands as.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `(first, second)` for `side` read as `first then second`; nothing
///   for any other value.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
#[spec(ensures: |ret| ret.is_none_or(|(first, second)| first != side && second != side))]
fn halves(
    arena: &CoreArena,
    side: ValueId,
) -> Option<(ValueId, ValueId)>
{
    let mut current = side;
    if let Some(&Value::Returned(composite)) = arena.value(side) {
        if let Some(&Computation::Return(returned)) = arena.computation(composite) {
            current = returned;
        }
        else if let Some(&Computation::PathTransport {
            motive,
            path: second,
            value: first,
        }) = arena.computation(composite)
            && let Some(&ValueType::Path { right, .. }) = arena.value_type(motive)
            && arena.value(right)
                == Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(0_u32),
                })
        {
            return Some((first, second));
        }
    }
    let Some(&Value::Compose { ref cells, .. }) = arena.value(current)
    else {
        return None;
    };
    <[ValueId; 2]>::try_from(&**cells).ok().map(Into::into)
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

/// The refusal of the fill at `at` with no filler: the generator's `sides` at
/// the left ends of `read`, over `stratum`.
///
/// # Specification
/// - requires: `sides` are scoped under one binder per entry of `read`.
/// - ensures: [`CheckRefusal::NoFiller`] at `at`, naming the sides at `X⁻`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::a_fill_refuses_each_defect_by_name`
/// - witness: `fill::tests::a_set_that_is_no_pasting_context_is_refused`
#[spec(ensures: |ret| matches!(ret, CheckRefusal::NoFiller { at: site, .. } if site == at))]
fn refused(
    arena: &mut CoreArena,
    (at, sides, stratum): (ValueId, (ValueId, ValueId), Stratum),
    read: &[Cell],
) -> CheckRefusal
{
    let lowered: Vec<ValueId> = read
        .iter()
        .map(|cell| match *cell {
            Cell::Plain(value) | Cell::Lifted { lo: value, .. } => value,
        })
        .collect();
    CheckRefusal::NoFiller {
        at,
        left: instantiated(arena, sides.0, &lowered),
        right: instantiated(arena, sides.1, &lowered),
        stratum,
    }
}

/// The entries `cells` read `level` binders past the fill's own context,
/// inside the bases of the first `done` vertex inductions: those vertices at
/// `here`, and each cell of `X` the variables the innermost base binds for it.
///
/// # Specification
/// - requires: `roles` gives each entry of `cells` its role; `span` binders,
///   two per cell of `X`, close the `level` past the fill's context when `done`
///   is past zero.
/// - ensures: one entry per entry of `cells`: a vertex of `X` ranked below
///   `done` at its left end and `here`; inside an induction, a cell of `X` at
///   the variables [`telescoped`] names; every other entry lifted.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
#[spec(ensures: |ret| ret.len() == cells.len())]
fn state(
    arena: &mut CoreArena,
    (cells, roles): (&[Cell], &[Role]),
    level: Binders,
    (done, span): (Rank, Binders),
) -> Vec<Cell>
{
    let mut held = Vec::with_capacity(cells.len());
    for (&cell, &role) in cells.iter().zip(roles) {
        held.push(match (cell, role) {
            (Cell::Plain(value), Role::Fixed | Role::Vertex(_) | Role::Cell(_)) => {
                Cell::Plain(lift_value(arena, value, level))
            },
            (Cell::Lifted { lo, .. }, Role::Vertex(rank)) if rank < done.0 => {
                let lo = lift_value(arena, lo, level);
                let path = arena.value_here(lo);
                Cell::Lifted { lo, hi: lo, path }
            },
            (Cell::Lifted { lo, .. }, Role::Cell(rank)) if done.0 > 0 => {
                let (hi, path) = telescoped(arena, span, Rank(rank));
                Cell::Lifted {
                    lo: lift_value(arena, lo, level),
                    hi,
                    path,
                }
            },
            (Cell::Lifted { lo, hi, path }, Role::Fixed | Role::Vertex(_) | Role::Cell(_)) => {
                Cell::Lifted {
                    lo: lift_value(arena, lo, level),
                    hi: lift_value(arena, hi, level),
                    path: lift_value(arena, path, level),
                }
            },
        });
    }
    held
}

/// The variables a telescope of `span` binders, two per cell of `X`, binds
/// for the cell ranked `rank`, read past the whole telescope: its right end
/// and its path.
///
/// # Specification
/// trivial.
fn telescoped(
    arena: &mut CoreArena,
    span: Binders,
    rank: Rank,
) -> (ValueId, ValueId)
{
    let taken = u32::try_from(rank.0.saturating_mul(2)).unwrap_or(u32::MAX);
    let right = u32::from(span).saturating_sub(taken).saturating_sub(1);
    (
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(right)),
        arena.value_variable(
            Zone::Intuitionistic,
            DeBruijnIndex::from(right.saturating_sub(1)),
        ),
    )
}

/// The entry at `entry` of `cells` read past a vertex induction's two
/// binders and `extra` of its telescope's, the vertex at `moving` bound by
/// the motive.
///
/// # Specification
/// - requires: `cells` stand in one context; `moving` is a vertex of `X`.
/// - ensures: the moving vertex at its left end lifted, its right end the
///   variable `extra + 1` and its path the variable `extra`; any other entry
///   lifted past `2 + extra` binders.
/// - fails: a machine invariant for an entry past `cells`.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`realise`].
/// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
#[spec(ensures: |ret| ret.is_ok() == (entry.0 < cells.len()))]
fn reached(
    arena: &mut CoreArena,
    cells: &[Cell],
    (entry, moving): (Position, Position),
    extra: Binders,
) -> Result<Cell, CheckRefusal>
{
    let past = Binders::from(2_u32).beyond(extra);
    let cell = cells
        .get(entry.0)
        .copied()
        .ok_or(CheckRefusal::MachineInvariant)?;
    Ok(match cell {
        Cell::Plain(value) => Cell::Plain(lift_value(arena, value, past)),
        Cell::Lifted { lo, .. } if entry == moving => Cell::Lifted {
            lo: lift_value(arena, lo, past),
            hi: arena.value_variable(
                Zone::Intuitionistic,
                DeBruijnIndex::from(u32::from(extra.deeper())),
            ),
            path: arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(u32::from(extra))),
        },
        Cell::Lifted { lo, hi, path } => Cell::Lifted {
            lo: lift_value(arena, lo, past),
            hi: lift_value(arena, hi, past),
            path: lift_value(arena, path, past),
        },
    })
}

/// An entry read as a node of a side: its two ends and its path, when it is
/// of `X`.
///
/// # Specification
/// trivial.
const fn reach(cell: Cell) -> Read
{
    match cell {
        Cell::Plain(value) => Read {
            lo: value,
            hi: value,
            lift: None,
        },
        Cell::Lifted { lo, hi, path } => Read {
            lo,
            hi,
            lift: Some(path),
        },
    }
}

/// What builds the square and its induction from the generator, the chain,
/// how the fill lists its entries and what the generator relates.
struct Builder<'chain>
{
    /// The computation returning `t`, in the fill's own context.
    generator: ComputationId,
    /// The chain, in the fill's own context.
    chain: &'chain Chain,
    /// How the fill lists its entries.
    listing: Listing,
    /// What `t`'s path relates.
    generated: Generated<'chain>,
}

impl Builder<'_>
{
    /// The square at `cells`, every value read `shift` binders past the fill's
    /// own context.
    ///
    /// # Specification
    /// - requires: `cells` stand `shift` binders past the fill's context.
    /// - ensures: `Path(Path(P, u⁻, v⁺), t⁻ then (v ↑ X), (u ↑ X) then t⁺)`: of
    ///   dimension two, `P` the path between the chain's ends and `u`, `v` the
    ///   generator's sides; of dimension one, `P` the carrier and `u`, `v` the
    ///   chain's two ends.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
    /// - witness: `fill::tests::a_cell_of_dimension_one_fills_its_square_by_induction`
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
        let t_lo = self.applied(arena, shift, &lo);
        let t_hi = self.applied(arena, shift, &hi);
        let (composites, u, v) = match self.generated {
            Generated::Composites { u, v } => {
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
                (
                    arena.value_type_path(carrier, start, end),
                    lifted(arena, carrier, &vertices, u, cells),
                    lifted(arena, carrier, &vertices, v, cells),
                )
            },
            Generated::Ends => {
                let last = vertices.len().saturating_sub(1);
                (
                    carrier,
                    self.end(arena, &vertices, cells, Vertex(0)),
                    self.end(arena, &vertices, cells, Vertex(last)),
                )
            },
        };
        let u_up = u.lift.unwrap_or_else(|| arena.value_here(u.lo));
        let v_up = v.lift.unwrap_or_else(|| arena.value_here(v.lo));
        let source = identity::then(arena, composites, u.lo, t_lo, v_up);
        let source = arena.value_returned(source);
        let target = identity::then(arena, composites, u.lo, u_up, t_hi);
        let target = arena.value_returned(target);
        let sides = arena.value_type_path(composites, u.lo, v.hi);
        arena.value_type_path(sides, source, target)
    }

    /// The chain's vertex at `vertex` read at `cells`: its two ends and its
    /// path when the fill lists it in `X`, the fixed vertex of `vertices`
    /// otherwise.
    ///
    /// # Specification
    /// - requires: `vertices` and `cells` stand in one context.
    /// - ensures: the listed entry read as [`reach`] reads it, or the vertex
    ///   standing as itself; the unit for a vertex past the chain.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_cell_of_dimension_one_fills_its_square_by_induction`
    /// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
    #[spec(ensures: |ret| arena.value(ret.lo).is_some() && arena.value(ret.hi).is_some())]
    fn end(
        &self,
        arena: &mut CoreArena,
        vertices: &[ValueId],
        cells: &[Cell],
        vertex: Vertex,
    ) -> Read
    {
        let listed = self
            .listing
            .vertex(vertex)
            .and_then(|place| cells.get(place.0).copied());
        if let Some(cell) = listed {
            return reach(cell);
        }
        let value = vertices
            .get(vertex.0)
            .copied()
            .unwrap_or_else(|| arena.value_unit());
        reach(Cell::Plain(value))
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
    /// along `path`, its base `base`: the earlier entries of `X` at their left
    /// ends and `here`, the later at their paths.
    ///
    /// # Specification
    /// - requires: `cells` and `base` stand `shift` binders past the fill's
    ///   context; every vertex of `X` is at `here`; `base` fills the square
    ///   with this cell and every earlier cell of `X` at its left end and
    ///   `here`.
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
    /// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
    #[spec(ensures: |ret| ret.as_ref().is_err_and(|refusal| *refusal == CheckRefusal::MachineInvariant) || ret.as_ref().is_ok_and(|realised| matches!(arena.computation(*realised), Some(&Computation::TelescopeTransport { .. }))))]
    fn induction(
        &self,
        arena: &mut CoreArena,
        (shift, cells): (Binders, &[Cell]),
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
        let square = self.square(arena, shift.beyond(two), &bound);
        let returned = arena.comp_type_returner(square);
        let domain = self.cell_type(arena, shift, position)?;
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

    /// The based path induction on the vertex of `X` at `position`, from its
    /// left end along its path, its base `base`: a function of every cell of
    /// `X`'s right end and path, whose types mention the vertex.
    ///
    /// # Specification
    /// - requires: `cells` and `base` stand `level` binders past the fill's
    ///   context, the vertices of `X` before this one at `here`; `lifted` are
    ///   the cells of `X` in order; `base` is the function with this vertex at
    ///   `here`.
    /// - ensures: the telescope transport along the vertex's path and its
    ///   `here` from `here(lo)`, its motive the thunk of the function from each
    ///   cell of `X`'s right end and square into the square, this vertex bound.
    /// - fails: a machine invariant for a position that is no vertex of `X`, or
    ///   a cell of `X` the listing does not place.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
    #[spec(ensures: |ret| ret.as_ref().is_err_and(|refusal| *refusal == CheckRefusal::MachineInvariant) || ret.as_ref().is_ok_and(|realised| matches!(arena.computation(*realised), Some(&Computation::TelescopeTransport { .. }))))]
    fn vertex_induction(
        &self,
        arena: &mut CoreArena,
        (level, cells): (Binders, &[Cell]),
        (position, lifted): (Position, &[Position]),
        base: ValueId,
    ) -> Result<ComputationId, CheckRefusal>
    {
        let Some(&Cell::Lifted { lo, path, .. }) = cells.get(position.0)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let two = Binders::from(2_u32);
        let span = Binders::from(u32::try_from(lifted.len().saturating_mul(2)).unwrap_or(u32::MAX));
        let mut bound = Vec::with_capacity(cells.len());
        for index in 0 .. cells.len() {
            bound.push(reached(arena, cells, (Position(index), position), span)?);
        }
        for (rank, &cell) in lifted.iter().enumerate() {
            let Some(&Cell::Lifted { lo: low, .. }) = cells.get(cell.0)
            else {
                return Err(CheckRefusal::MachineInvariant);
            };
            let (hi, along) = telescoped(arena, span, Rank(rank));
            let low = lift_value(arena, low, two.beyond(span));
            let slot = bound
                .get_mut(cell.0)
                .ok_or(CheckRefusal::MachineInvariant)?;
            *slot = Cell::Lifted {
                lo: low,
                hi,
                path: along,
            };
        }
        let square = self.square(arena, level.beyond(two).beyond(span), &bound);
        let mut codomain = arena.comp_type_returner(square);
        for (rank, &cell) in lifted.iter().enumerate().rev() {
            let (Entry::Cell(index), Some(&Cell::Lifted { lo: low, .. })) =
                (self.listing.entry(cell), cells.get(cell.0))
            else {
                return Err(CheckRefusal::MachineInvariant);
            };
            let (start, end) = self
                .listing
                .vertex(Vertex(index))
                .zip(self.listing.vertex(Vertex(index.saturating_add(1))))
                .ok_or(CheckRefusal::MachineInvariant)?;
            let ends_at = Binders::from(u32::try_from(rank.saturating_mul(2)).unwrap_or(u32::MAX));
            let square_at = ends_at.deeper();
            let carrier = lift_type(
                arena,
                self.chain.carrier,
                level.beyond(two).beyond(square_at),
            );
            let left = reach(reached(arena, cells, (start, position), square_at)?);
            let right = reach(reached(arena, cells, (end, position), square_at)?);
            let low = lift_value(arena, low, two.beyond(square_at));
            let moved = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let left_up = left.lift.unwrap_or_else(|| arena.value_here(left.lo));
            let right_up = right.lift.unwrap_or_else(|| arena.value_here(right.lo));
            let outer = arena.value_type_path(carrier, left.lo, right.hi);
            let source = identity::then(arena, carrier, left.lo, low, right_up);
            let source = arena.value_returned(source);
            let target = identity::then(arena, carrier, left.lo, left_up, moved);
            let target = arena.value_returned(target);
            let filled = arena.value_type_path(outer, source, target);
            codomain = arena.comp_type_pi(filled, codomain);
            let carrier = lift_type(arena, self.chain.carrier, level.beyond(two).beyond(ends_at));
            let left = reach(reached(arena, cells, (start, position), ends_at)?);
            let right = reach(reached(arena, cells, (end, position), ends_at)?);
            let ends = arena.value_type_path(carrier, left.hi, right.hi);
            codomain = arena.comp_type_pi(ends, codomain);
        }
        let thunked = arena.value_type_thunk(codomain);
        let returned = arena.comp_type_returner(thunked);
        let domain = lift_type(arena, self.chain.carrier, level);
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

    /// The induction filling the square at `cells`: each vertex of `X` in
    /// order, the outermost first, then each cell of `X` in order inside the
    /// innermost vertex's base.
    ///
    /// # Specification
    /// - requires: `cells` stand in the fill's own context; `roles` gives each
    ///   its role; `vertices` and `lifted` are the vertices and the cells of
    ///   `X` in order.
    /// - ensures: the inductions on the cells of `X`, base `here(t[X⁻])`,
    ///   inside one thunked function of the cells' right ends and paths per
    ///   vertex of `X`, each applied to the cells' ends and paths outside it.
    /// - fails: a machine invariant for no cell of `X`.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
    /// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
    #[spec(ensures: |ret| ret.as_ref().is_ok() || ret.as_ref().is_err_and(|refusal| *refusal == CheckRefusal::MachineInvariant))]
    fn realised(
        &self,
        arena: &mut CoreArena,
        (cells, roles): (&[Cell], &[Role]),
        (vertices, lifted): (&[Position], &[Position]),
    ) -> Result<ComputationId, CheckRefusal>
    {
        let width = u32::try_from(lifted.len().saturating_mul(2)).unwrap_or(u32::MAX);
        let depth_of = |done: usize| {
            Binders::from(width.saturating_mul(u32::try_from(done).unwrap_or(u32::MAX)))
        };
        let span = Binders::from(width);
        let innermost = depth_of(vertices.len());
        let held = state(
            arena,
            (cells, roles),
            innermost,
            (Rank(vertices.len()), span),
        );
        let lowered: Vec<ValueId> = held
            .iter()
            .map(|cell| match *cell {
                Cell::Plain(value) | Cell::Lifted { lo: value, .. } => value,
            })
            .collect();
        let lowest = self.applied(arena, innermost, &lowered);
        let mut base = arena.value_here(lowest);
        let mut body = None;
        for &position in lifted.iter().rev() {
            let Some(&Cell::Lifted { lo, path, .. }) = held.get(position.0)
            else {
                return Err(CheckRefusal::MachineInvariant);
            };
            let transport =
                self.induction(arena, (innermost, &held), (position, lo, path), base)?;
            base = arena.value_returned(transport);
            body = Some(transport);
        }
        let mut body = body.ok_or(CheckRefusal::MachineInvariant)?;
        for (done, &position) in vertices.iter().enumerate().rev() {
            for _ in 0 .. width {
                body = arena.computation_lambda(body);
            }
            let function = arena.value_thunk(body);
            let level = depth_of(done);
            let held = state(arena, (cells, roles), level, (Rank(done), span));
            let transport =
                self.vertex_induction(arena, (level, &held), (position, lifted), function)?;
            let returned = arena.value_returned(transport);
            let mut applied = arena.computation_force(returned);
            for &cell in lifted {
                let Some(&Cell::Lifted { hi, path, .. }) = held.get(cell.0)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let partial = arena.computation_application(applied, hi);
                applied = arena.computation_application(partial, path);
            }
            body = applied;
        }
        Ok(body)
    }

    /// The type of the chain's cell at `position`, read `shift` binders past
    /// the fill's own context.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Path(A, xᵢ, xᵢ₊₁)` for the cell's two vertices, each of `X`
    ///   at its left end.
    /// - fails: a machine invariant for a position that is no cell of the
    ///   chain.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`realise`].
    /// - witness: `fill::tests::a_free_cell_fills_its_square_by_induction`
    /// - witness: `fill::tests::vertex_paths_fill_their_square_by_induction`
    #[spec(ensures: |ret| ret.is_err() || matches!(arena.value_type(*ret.as_ref().unwrap_or(&self.chain.carrier)), Some(&ValueType::Path { .. })))]
    fn cell_type(
        &self,
        arena: &mut CoreArena,
        shift: Binders,
        position: Position,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let Entry::Cell(index) = self.listing.entry(position)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let (&left, &right) = self
            .chain
            .vertices
            .get(index)
            .zip(self.chain.vertices.get(index.saturating_add(1)))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let carrier = lift_type(arena, self.chain.carrier, shift);
        let left = lift_value(arena, left, shift);
        let right = lift_value(arena, right, shift);
        Ok(arena.value_type_path(carrier, left, right))
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
