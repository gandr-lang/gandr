//! What a judgement reported of an item, kept as content beside its
//! checkpoint, and its seat in an edited arena.
//!
//! # The parts
//!
//! A judgement elaborates a body when it decides a computation that the body
//! writes where it reads a value. Then the report keeps each decision, each
//! node that the elaboration built again beside the node it was built from,
//! each bind minted for a run, and each value carried across a map between
//! models. A suspended verdict keeps the equations that it waits on, the holes
//! they block on and the waiting declarations that it read.
//!
//! # Three places
//!
//! Each node of a report stands at one place:
//!
//! - a node of the written item, at its place in the item's walk
//!   ([`Place::Written`]); this place is exact, so the projection tries it
//!   first;
//! - a node of the judged body, at its place in the body's table that the entry
//!   keeps ([`Place::Judged`]);
//! - any other node, a body between two rebuilds say, at its place in one table
//!   that the report keeps for all such nodes ([`Place::Outside`]).
//!
//! A table merges equal nodes, so two equal nodes of the judged body share one
//! place, and a seat mints them as one node.
//!
//! # Order
//!
//! The checker orders the decisions, the crossings and the equations by their
//! arena ids, and an edited arena gives other ids. So the content keeps each of
//! them in the order of its places, and a seat builds the checker's order from
//! the ids that it mints.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_checker::NestedElaboration;
use gandr_core_checker::Nesting;
use gandr_core_checker::elaboration::Equation;
use gandr_core_checker::elaboration::Suspension;
use gandr_core_term::Carried;
use gandr_core_term::CoreArena;
use gandr_core_term::CrossedOperand;
use gandr_core_term::Crossing;
use gandr_core_term::ValueId;
use gandr_core_term::effect::Purity;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::Discovery;
use crate::boundary::ItemOrdinal;
use crate::boundary::OutsideIndex;
use crate::content::ArenaNode;
use crate::content::Minted;
use crate::content::Placer;
use crate::content::Sites;
use crate::content::TablePlace;
use crate::content::TypeContent;
use crate::content::place;
use crate::content::seating;
use crate::entry::written;
use crate::failure::comp_type_of;
use crate::failure::computation_of;
use crate::failure::type_arena_node;
use crate::failure::type_node_of;
use crate::failure::value_of;
use crate::failure::value_type_of;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;
use crate::support::SupportedNode;

quenchant_shape::reason_enum! {
    /// Why a checkpoint keeps no report of its item.
    pub mod reported {
        /// The reason no report is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The judgement reported neither an elaboration nor a suspension
            /// of the item, or the maker of the checkpoint kept no report.
            Unreported,
            /// The item is opaque: no pass adopts or takes its checkpoint, so
            /// no seat reads the report that it would keep.
            Opaque,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a report keeps no elaboration.
    pub mod nesting {
        /// The reason no elaboration is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The judgement elaborated no nested computation of the body.
            Unnested,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a report keeps no suspension.
    pub mod waiting {
        /// The reason no suspension is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The verdict is not suspended.
            Unsuspended,
        }
    }
}

/// Where a node of a report stands.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Place
{
    /// The node at this place of the item's walk.
    Written(Discovery),
    /// The node at this place of the judged body's table.
    Judged(TablePlace),
    /// The node that the report's own table keeps at this root.
    Outside(OutsideIndex),
}

/// How the judgement decided one nested computation, its fill placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NestingContent
{
    /// Suspended, as a written thunk is.
    Suspended,
    /// Run before its region.
    Ran(Purity),
    /// Run purely where a type after it reads it.
    Returned,
    /// A fill, standing as the value that this induction returns.
    Filled(Place),
}

/// What a crossing's map is applied to after its carriers, placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum OperandContent
{
    /// The crossed value itself.
    Itself,
    /// A value standing for it.
    Standing(Place),
    /// The record that updates the crossed value.
    Overlaid(Place),
}

/// A crossing that the value bridge recorded at a value, placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CrossingContent
{
    /// The map's item, absent where the value stands as its operand.
    pub by: Maybe<Reference, ()>,
    /// The values the map is applied to before the crossed value, outermost
    /// first.
    pub carriers: Vec<Place>,
    /// What the map is applied to after its carriers.
    pub operand: OperandContent,
}

/// What elaborating one body's nested computations did, each node placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ElaborationContent
{
    /// Each nested computation and written run beside its decision, in the
    /// order of their places.
    pub decisions: Vec<(Place, NestingContent)>,
    /// Each rebuilt node beside the node it was built from, in rebuild order.
    pub carried: Vec<(Place, Place)>,
    /// Each run beside the bind minted for it, in minting order.
    pub binds: Vec<(Place, Place)>,
    /// Each value carried by a map between models beside its crossing, in the
    /// order of their places.
    pub crossings: Vec<(Place, CrossingContent)>,
}

/// One pending conversion equation, placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EquationContent
{
    /// The owed item at the flex head.
    pub hole: Reference,
    /// The flex side.
    pub flex: Place,
    /// The rigid side.
    pub rigid: Place,
}

/// What a suspended declaration waits on, placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SuspensionContent
{
    /// The type the waiting declaration supplies.
    pub declared: Place,
    /// The pending equations, in the order of their places.
    pub equations: Vec<EquationContent>,
    /// The holes owed when the suspension was recorded, in position order.
    pub blockers: Vec<Reference>,
    /// The waiting declarations to resume first, in position order.
    pub dependencies: Vec<Reference>,
}

/// The elaboration and the suspension of a report, seated in an arena.
type SeatedParts = (
    Maybe<NestedElaboration, nesting::Absent>,
    Maybe<Suspension, waiting::Absent>,
);

/// What a judgement reported of one item, each node placed.
///
/// The report keeps the elaboration of the body's nested computations and the
/// suspension of the item's verdict. Each node stands in the item's walk, in
/// the judged body's table or in the report's own table.
///
/// # Specification
/// - executable: none — this declaration has no call boundary; the judgement
///   whose report it reads is external.
///
/// # Adequacy
/// - hypothesis: L3 — the reports of an elaborated item and of a suspended item
///   read back from bytes, seat in their program and project again to the
///   reports kept.
/// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ReportContent
{
    /// The elaboration of the body's nested computations.
    elaboration: Maybe<ElaborationContent, nesting::Absent>,
    /// What the suspended verdict waits on.
    suspension: Maybe<SuspensionContent, waiting::Absent>,
    /// The table of the nodes that neither the item's walk nor the judged
    /// body holds.
    outside: Vec<SupportedNode>,
    /// The place in `outside` of each such node, by its index.
    roots: Vec<TablePlace>,
}

/// The elaboration and the suspension of a report, seated in an edited arena,
/// beside the judged body that the seat minted to place them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SeatedReport
{
    /// The elaboration of the body's nested computations.
    elaboration: Maybe<NestedElaboration, nesting::Absent>,
    /// What the suspended verdict waits on.
    suspension: Maybe<Suspension, waiting::Absent>,
    /// The judged body, minted, when the entry keeps it.
    body: Maybe<ValueId, written::Absent>,
}

/// The places of the nodes a projection reads, beside the arena nodes that
/// the report's own table is built from.
///
/// # Specification
/// trivial.
struct Placing<'sites, 'body, 'layout>
{
    /// The item's walk.
    sites: &'sites Sites,
    /// The places of the judged body's table, when the entry keeps its body.
    body: Option<&'body Placer>,
    /// The layout that names each item a report reads.
    layout: &'layout Layout,
    /// The index of each node outside the item and the body placed so far.
    indices: BTreeMap<ArenaNode, OutsideIndex>,
    /// Each node outside the item and the body, by its index.
    roots: Vec<ArenaNode>,
}

impl Placing<'_, '_, '_>
{
    /// The place of `node`.
    ///
    /// # Specification
    /// - ensures: the node's discovery when the item's walk reached it; else
    ///   its place in the judged body's table when that table holds it; else
    ///   the index of its root in the report's own table, which one node takes
    ///   once.
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    fn place(
        &mut self,
        node: ArenaNode,
    ) -> Place
    {
        if let Maybe::Present(discovery) = self.sites.discovery(node) {
            return Place::Written(discovery);
        }
        if let Some(place) = self.body.and_then(|body| body.place(node)) {
            return Place::Judged(place);
        }
        let next = OutsideIndex::from(self.roots.len());
        let index = *self.indices.entry(node).or_insert(next);
        if index == next {
            self.roots.push(node);
        }
        Place::Outside(index)
    }

    /// The content of `elaboration`.
    ///
    /// # Specification
    /// - ensures: every node placed; the carried pairs and the binds in their
    ///   order, placed before the decisions and the crossings, which
    ///   [`ReportContent::of`] then puts in the order of their places.
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    fn elaboration(
        &mut self,
        elaboration: &NestedElaboration,
    ) -> ElaborationContent
    {
        let carried = elaboration
            .carried()
            .iter()
            .map(|&carried| {
                let (from, to) = carried_nodes(carried);
                (self.place(from), self.place(to))
            })
            .collect();
        let binds = elaboration
            .binds()
            .iter()
            .map(|&(run, bind)| {
                (
                    self.place(ArenaNode::Value(run)),
                    self.place(ArenaNode::Computation(bind)),
                )
            })
            .collect();
        let decisions: Vec<(Place, NestingContent)> = elaboration
            .decisions()
            .iter()
            .map(|(&value, &nesting)| {
                let decided = match nesting {
                    Nesting::Suspended => NestingContent::Suspended,
                    Nesting::Ran(purity) => NestingContent::Ran(purity),
                    Nesting::Returned => NestingContent::Returned,
                    Nesting::Filled(fill) => {
                        NestingContent::Filled(self.place(ArenaNode::Computation(fill)))
                    },
                };
                (self.place(ArenaNode::Value(value)), decided)
            })
            .collect();
        let crossings: Vec<(Place, CrossingContent)> = elaboration
            .crossings()
            .iter()
            .map(|(&value, crossing)| {
                let carriers = crossing
                    .carriers
                    .iter()
                    .map(|&carrier| self.place(ArenaNode::Value(carrier)))
                    .collect();
                let operand = match crossing.operand {
                    CrossedOperand::Itself => OperandContent::Itself,
                    CrossedOperand::Standing(standing) => {
                        OperandContent::Standing(self.place(ArenaNode::Value(standing)))
                    },
                    CrossedOperand::Overlaid(overlay) => {
                        OperandContent::Overlaid(self.place(ArenaNode::Value(overlay)))
                    },
                };
                let by = match crossing.by {
                    Maybe::Present(constant) => Maybe::Present(self.layout.resolve(constant)),
                    Maybe::Absent(()) => Maybe::Absent(()),
                };
                (self.place(ArenaNode::Value(value)), CrossingContent {
                    by,
                    carriers,
                    operand,
                })
            })
            .collect();
        ElaborationContent {
            decisions,
            carried,
            binds,
            crossings,
        }
    }
}

impl ReportContent
{
    /// The report of an item whose judgement gave `elaboration` and
    /// `suspension`, each node read in `arena` through `layout`: a node of the
    /// item placed by `sites`, a node of the judged body by `body`.
    ///
    /// # Specification
    /// - requires: `sites` is the item's walk in `arena`, and `body` holds the
    ///   places of the judged body's table when the entry keeps the body.
    /// - ensures: `reported::Absent::Unreported` when the judgement reported
    ///   neither part; otherwise each part as content, every node at the first
    ///   place that holds it.
    /// - panics: none.
    /// - executable: none — a predicate would place every node again, which the
    ///   witness does through a seat.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    pub(crate) fn of(
        (arena, layout): (&CoreArena, &Layout),
        (sites, body): (&Sites, Option<&Placer>),
        (elaboration, suspension): (Option<&NestedElaboration>, Option<&Suspension>),
    ) -> Maybe<Self, reported::Absent>
    {
        if elaboration.is_none() && suspension.is_none() {
            return Maybe::Absent(reported::Absent::Unreported);
        }
        let mut placing = Placing {
            sites,
            body,
            layout,
            indices: BTreeMap::new(),
            roots: Vec::new(),
        };
        let elaboration = elaboration
            .map_or(Maybe::Absent(nesting::Absent::Unnested), |elaboration| {
                Maybe::Present(placing.elaboration(elaboration))
            });
        let suspension =
            suspension.map_or(Maybe::Absent(waiting::Absent::Unsuspended), |suspension| {
                let declared = placing.place(ArenaNode::ValueType(suspension.declared().id()));
                let equations: Vec<EquationContent> = suspension
                    .equations()
                    .iter()
                    .map(|equation| EquationContent {
                        hole: layout.resolve(equation.hole()),
                        flex: placing.place(type_arena_node(equation.flex())),
                        rigid: placing.place(type_arena_node(equation.rigid())),
                    })
                    .collect();
                Maybe::Present(SuspensionContent {
                    declared,
                    equations,
                    blockers: suspension
                        .blockers()
                        .iter()
                        .map(|&hole| layout.resolve(hole))
                        .collect(),
                    dependencies: suspension
                        .dependencies()
                        .iter()
                        .map(|&waiting| layout.resolve(waiting))
                        .collect(),
                })
            });
        let (outside, places) = crate::content::tabled_roots(arena, layout, &placing.roots);
        let (roots, remap) = merged(places);
        let mut content = Self {
            elaboration,
            suspension,
            outside,
            roots,
        };
        if let Some(remap) = remap {
            content.places_mut(&mut |place| {
                if let Place::Outside(ref mut index) = *place
                    && let Some(&to) = remap.get(usize::from(*index))
                {
                    *index = to;
                }
            });
        }
        content.sort();
        Maybe::Present(content)
    }

    /// Hand each place of the report to `visit`.
    ///
    /// # Specification
    /// trivial.
    fn places_mut(
        &mut self,
        visit: &mut impl FnMut(&mut Place),
    )
    {
        if let Maybe::Present(ref mut elaboration) = self.elaboration {
            for &mut (ref mut at, ref mut decided) in &mut elaboration.decisions {
                visit(at);
                if let NestingContent::Filled(ref mut fill) = *decided {
                    visit(fill);
                }
            }
            for &mut (ref mut from, ref mut to) in elaboration
                .carried
                .iter_mut()
                .chain(elaboration.binds.iter_mut())
            {
                visit(from);
                visit(to);
            }
            for &mut (ref mut at, ref mut crossing) in &mut elaboration.crossings {
                visit(at);
                crossing.carriers.iter_mut().for_each(&mut *visit);
                match crossing.operand {
                    OperandContent::Itself => {},
                    OperandContent::Standing(ref mut standing) => visit(standing),
                    OperandContent::Overlaid(ref mut overlay) => visit(overlay),
                }
            }
        }
        if let Maybe::Present(ref mut suspension) = self.suspension {
            visit(&mut suspension.declared);
            for equation in &mut suspension.equations {
                visit(&mut equation.flex);
                visit(&mut equation.rigid);
            }
        }
    }

    /// Put the decisions, the crossings and the equations in the order of
    /// their places, each once: two nodes of one content at one place seat as
    /// one node.
    ///
    /// # Specification
    /// trivial.
    fn sort(&mut self)
    {
        if let Maybe::Present(ref mut elaboration) = self.elaboration {
            elaboration.decisions.sort_unstable();
            elaboration.decisions.dedup();
            elaboration
                .crossings
                .sort_by(|left, right| left.0.cmp(&right.0));
            elaboration.crossings.dedup();
        }
        if let Maybe::Present(ref mut suspension) = self.suspension {
            suspension.equations.sort_unstable();
            suspension.equations.dedup();
        }
    }

    /// The elaboration that the report keeps, or why it keeps none.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn elaboration(&self) -> Maybe<&ElaborationContent, nesting::Absent>
    {
        match self.elaboration {
            Maybe::Present(ref elaboration) => Maybe::Present(elaboration),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The suspension that the report keeps, or why it keeps none.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn suspension(&self) -> Maybe<&SuspensionContent, waiting::Absent>
    {
        match self.suspension {
            Maybe::Present(ref suspension) => Maybe::Present(suspension),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The table of the nodes that neither the item's walk nor the judged body
    /// holds, beside the place of each such node in it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn outside(&self) -> (&[SupportedNode], &[TablePlace])
    {
        (&self.outside, &self.roots)
    }

    /// The report of these parts, as the decoder reassembles it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn from_parts(
        (elaboration, suspension): (
            Maybe<ElaborationContent, nesting::Absent>,
            Maybe<SuspensionContent, waiting::Absent>,
        ),
        (outside, roots): (Vec<SupportedNode>, Vec<TablePlace>),
    ) -> Self
    {
        Self {
            elaboration,
            suspension,
            outside,
            roots,
        }
    }

    /// Seat the report in `arena`, constants placed through `layout`: a node
    /// of the item at its place in `walk`, the item's walk in the edited
    /// program, and a node of the judged body at its place in `body`, the
    /// body's table minted there.
    ///
    /// # Specification
    /// - requires: `walk` is the item's walk in `arena`, and `body` holds the
    ///   judged body minted in `arena` when the entry keeps the body.
    /// - ensures: on success, the elaboration and the suspension whose
    ///   projection through the same places is this report; the decisions, the
    ///   crossings and the equations in the order of the minted ids.
    /// - fails: [`seating::Absent::Unwalked`] for a place past the walk;
    ///   [`seating::Absent::Unplaceable`] for a table place that no mint
    ///   reached; [`seating::Absent::IllSorted`] for a node of the wrong sort;
    ///   [`seating::Absent::Unplaced`] for an item the layout does not hold;
    ///   and otherwise as the mint of the report's own table fails.
    /// - panics: none.
    /// - executable: none — a predicate would project the seated parts again,
    ///   which the witness does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    pub(crate) fn seat(
        &self,
        (arena, layout): (&mut CoreArena, &Layout),
        (walk, body): (&[ArenaNode], Option<&Minted>),
    ) -> Result<SeatedParts, seating::Absent>
    {
        let outside = match Minted::of(&self.outside, self.roots.iter().cloned(), (arena, layout)) {
            Maybe::Present(outside) => outside,
            Maybe::Absent(reason) => return Err(reason),
        };
        let seat = Seat {
            walk,
            body,
            outside: (&outside, &self.roots),
            layout,
        };
        let elaboration = match self.elaboration {
            Maybe::Present(ref elaboration) => Maybe::Present(seat.elaboration(elaboration)?),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let suspension = match self.suspension {
            Maybe::Present(ref suspension) => Maybe::Present(seat.suspension(suspension)?),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        Ok((elaboration, suspension))
    }

    /// Seat the suspension alone in `arena`, as [`ReportContent::seat`]
    /// seats it, minting only the outside nodes it names.
    ///
    /// # Specification
    /// - requires: as [`ReportContent::seat`]; a suspended item's report names
    ///   no node of a judged body.
    /// - ensures: as [`ReportContent::seat`] for the suspension.
    /// - fails: as [`ReportContent::seat`].
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    pub(crate) fn seat_suspension(
        &self,
        (arena, layout): (&mut CoreArena, &Layout),
        walk: &[ArenaNode],
    ) -> Result<Maybe<Suspension, waiting::Absent>, seating::Absent>
    {
        let suspension = match self.suspension {
            Maybe::Present(ref suspension) => suspension,
            Maybe::Absent(reason) => return Ok(Maybe::Absent(reason)),
        };
        let named = core::iter::once(&suspension.declared)
            .chain(
                suspension
                    .equations
                    .iter()
                    .flat_map(|equation| [&equation.flex, &equation.rigid]),
            )
            .filter_map(|place| match *place {
                Place::Outside(index) => self.roots.get(usize::from(index)).cloned(),
                Place::Written(_) | Place::Judged(_) => None,
            });
        let outside = match Minted::of(&self.outside, named, (arena, layout)) {
            Maybe::Present(outside) => outside,
            Maybe::Absent(reason) => return Err(reason),
        };
        let seat = Seat {
            walk,
            body: None,
            outside: (&outside, &self.roots),
            layout,
        };
        Ok(Maybe::Present(seat.suspension(suspension)?))
    }
}

impl SeatedReport
{
    /// The seated `elaboration` and `suspension`, placed against `body`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn of(
        (elaboration, suspension): (
            Maybe<NestedElaboration, nesting::Absent>,
            Maybe<Suspension, waiting::Absent>,
        ),
        body: Maybe<ValueId, written::Absent>,
    ) -> Self
    {
        Self {
            elaboration,
            suspension,
            body,
        }
    }

    /// The elaboration of the body's nested computations, seated, or why the
    /// report keeps none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn elaboration(&self) -> Maybe<&NestedElaboration, nesting::Absent>
    {
        match self.elaboration {
            Maybe::Present(ref elaboration) => Maybe::Present(elaboration),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// What the suspended verdict waits on, seated, or why the report keeps
    /// none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn suspension(&self) -> Maybe<&Suspension, waiting::Absent>
    {
        match self.suspension {
            Maybe::Present(ref suspension) => Maybe::Present(suspension),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The report that these seated parts give in `arena`: the item at
    /// `ordinal` of `program` walked there, and the judged body that the seat
    /// minted.
    ///
    /// # Specification
    /// - requires: `arena` is the arena that the seat minted into.
    /// - ensures: as [`ReportContent`] projects the parts of a judgement.
    /// - panics: none.
    /// - executable: none — the witness compares it with the report kept.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    #[inline]
    pub fn content(
        &self,
        arena: &CoreArena,
        (program, ordinal): (&Program, ItemOrdinal),
    ) -> Maybe<ReportContent, reported::Absent>
    {
        let layout = program.layout();
        let item = crate::content::encode_item(arena, layout, ordinal);
        let body = match self.body {
            Maybe::Present(body) => {
                Some(TypeContent::placed(arena, layout, ArenaNode::Value(body)).1)
            },
            Maybe::Absent(_) => None,
        };
        ReportContent::of(
            (arena, layout),
            (&item.sites, body.as_ref()),
            (
                match self.elaboration {
                    Maybe::Present(ref elaboration) => Some(elaboration),
                    Maybe::Absent(_) => None,
                },
                match self.suspension {
                    Maybe::Present(ref suspension) => Some(suspension),
                    Maybe::Absent(_) => None,
                },
            ),
        )
    }
}

/// The nodes a seat mints the places of a report to.
///
/// # Specification
/// trivial.
struct Seat<'walk, 'body, 'outside, 'layout>
{
    /// The item's walk in the edited program.
    walk: &'walk [ArenaNode],
    /// The judged body's table, minted.
    body: Option<&'body Minted>,
    /// The report's own table, minted, beside the place of each root in it.
    outside: (&'outside Minted, &'outside [TablePlace]),
    /// The layout that places each item a report names.
    layout: &'layout Layout,
}

impl Seat<'_, '_, '_, '_>
{
    /// The node at `place`.
    ///
    /// # Specification
    /// trivial.
    fn node(
        &self,
        place: &Place,
    ) -> Result<ArenaNode, seating::Absent>
    {
        match *place {
            Place::Written(discovery) => self
                .walk
                .get(usize::from(discovery))
                .copied()
                .ok_or(seating::Absent::Unwalked),
            Place::Judged(ref at) => self
                .body
                .and_then(|body| body.node(at))
                .ok_or(seating::Absent::Unplaceable),
            Place::Outside(index) => {
                let (minted, roots) = self.outside;
                roots
                    .get(usize::from(index))
                    .and_then(|root| minted.node(root))
                    .ok_or(seating::Absent::Unplaceable)
            },
        }
    }

    /// The item's constant that `reference` names.
    ///
    /// # Specification
    /// trivial.
    fn constant(
        &self,
        reference: &Reference,
    ) -> Result<ConstantIndex, seating::Absent>
    {
        match place(self.layout, reference) {
            Maybe::Present(constant) => Ok(constant),
            Maybe::Absent(reason) => Err(reason),
        }
    }

    /// The elaboration that `content` keeps, seated.
    ///
    /// # Specification
    /// - ensures: each node at its seated place; the carried pairs and the
    ///   binds in their kept order. Two decisions or crossings whose places
    ///   mint one node keep the last.
    /// - fails: as [`ReportContent::seat`].
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    fn elaboration(
        &self,
        content: &ElaborationContent,
    ) -> Result<NestedElaboration, seating::Absent>
    {
        let mut decisions = BTreeMap::new();
        for &(ref at, ref decided) in &content.decisions {
            let nesting = match *decided {
                NestingContent::Suspended => Nesting::Suspended,
                NestingContent::Ran(purity) => Nesting::Ran(purity),
                NestingContent::Returned => Nesting::Returned,
                NestingContent::Filled(ref fill) => {
                    Nesting::Filled(computation_of(self.node(fill)?)?)
                },
            };
            let _earlier = decisions.insert(value_of(self.node(at)?)?, nesting);
        }
        let carried = content
            .carried
            .iter()
            .map(|&(ref from, ref to)| carried_of(self.node(from)?, self.node(to)?))
            .collect::<Result<Vec<_>, _>>()?;
        let binds = content
            .binds
            .iter()
            .map(|&(ref run, ref bind)| {
                Ok((
                    value_of(self.node(run)?)?,
                    computation_of(self.node(bind)?)?,
                ))
            })
            .collect::<Result<Vec<_>, seating::Absent>>()?;
        let mut crossings = BTreeMap::new();
        for &(ref at, ref crossing) in &content.crossings {
            let by = match crossing.by {
                Maybe::Present(ref reference) => Maybe::Present(self.constant(reference)?),
                Maybe::Absent(()) => Maybe::Absent(()),
            };
            let carriers = crossing
                .carriers
                .iter()
                .map(|carrier| value_of(self.node(carrier)?))
                .collect::<Result<Vec<_>, _>>()?;
            let operand = match crossing.operand {
                OperandContent::Itself => CrossedOperand::Itself,
                OperandContent::Standing(ref standing) => {
                    CrossedOperand::Standing(value_of(self.node(standing)?)?)
                },
                OperandContent::Overlaid(ref overlay) => {
                    CrossedOperand::Overlaid(value_of(self.node(overlay)?)?)
                },
            };
            let _earlier = crossings.insert(value_of(self.node(at)?)?, Crossing {
                by,
                carriers,
                operand,
            });
        }
        Ok(NestedElaboration::seated(
            (decisions, carried),
            (binds, crossings),
        ))
    }

    /// The suspension that `content` keeps, seated.
    ///
    /// # Specification
    /// - ensures: each node at its seated place; the equations sorted and
    ///   unique in the order of the minted ids, as the checker keeps them.
    /// - fails: as [`ReportContent::seat`].
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReportContent`].
    /// - witness: `report::tests::a_report_read_back_from_bytes_seats_as_the_parts_that_give_it`
    fn suspension(
        &self,
        content: &SuspensionContent,
    ) -> Result<Suspension, seating::Absent>
    {
        let declared = value_type_of(self.node(&content.declared)?)?;
        let mut equations = content
            .equations
            .iter()
            .map(|equation| {
                Ok(Equation::seated(
                    self.constant(&equation.hole)?,
                    (
                        type_node_of(self.node(&equation.flex)?)?,
                        type_node_of(self.node(&equation.rigid)?)?,
                    ),
                ))
            })
            .collect::<Result<Vec<_>, seating::Absent>>()?;
        equations.sort_unstable();
        equations.dedup();
        let blockers = content
            .blockers
            .iter()
            .map(|hole| self.constant(hole))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let dependencies = content
            .dependencies
            .iter()
            .map(|waiting| self.constant(waiting))
            .collect::<Result<BTreeSet<_>, _>>()?;
        Ok(Suspension::seated(
            (declared, equations),
            (blockers, dependencies),
        ))
    }
}

/// The node a rebuild built from and the node it built, as arena nodes.
///
/// # Specification
/// trivial.
const fn carried_nodes(carried: Carried) -> (ArenaNode, ArenaNode)
{
    match carried {
        Carried::Value(from, to) => (ArenaNode::Value(from), ArenaNode::Value(to)),
        Carried::Computation(from, to) => {
            (ArenaNode::Computation(from), ArenaNode::Computation(to))
        },
        Carried::ValueType(from, to) => (ArenaNode::ValueType(from), ArenaNode::ValueType(to)),
        Carried::CompType(from, to) => (ArenaNode::CompType(from), ArenaNode::CompType(to)),
    }
}

/// The rebuild from `from` to `to`, two nodes of one sort.
///
/// # Specification
/// trivial.
fn carried_of(
    from: ArenaNode,
    to: ArenaNode,
) -> Result<Carried, seating::Absent>
{
    match from {
        ArenaNode::Value(from) => value_of(to).map(|to| Carried::Value(from, to)),
        ArenaNode::Computation(from) => computation_of(to).map(|to| Carried::Computation(from, to)),
        ArenaNode::ValueType(from) => value_type_of(to).map(|to| Carried::ValueType(from, to)),
        ArenaNode::CompType(from) => comp_type_of(to).map(|to| Carried::CompType(from, to)),
    }
}

/// The places `places` of the report's roots, each place once in the order of
/// its first root, beside the index each root takes among them when two roots
/// share a place.
///
/// # Specification
/// - ensures: the distinct places in first-occurrence order; no indices when
///   the roots' places are distinct, since then each root keeps its index.
/// - panics: none.
/// - executable: none — the clause restates the body.
///
/// # Adequacy
/// - hypothesis: L3 — roots that share a place keep it once, each at the index
///   of that place; roots at distinct places keep their own indices.
/// - witness: `report::tests::roots_that_share_a_place_keep_it_once`
fn merged(places: Vec<TablePlace>) -> (Vec<TablePlace>, Option<Vec<OutsideIndex>>)
{
    let mut first: BTreeMap<&TablePlace, OutsideIndex> = BTreeMap::new();
    let remap: Vec<OutsideIndex> = places
        .iter()
        .map(|place| {
            let next = OutsideIndex::from(first.len());
            *first.entry(place).or_insert(next)
        })
        .collect();
    if first.len() == places.len() {
        return (places, None);
    }
    let mut seen = 0_usize;
    let roots = places
        .into_iter()
        .zip(&remap)
        .filter_map(|(place, &index)| {
            (usize::from(index) == seen).then(|| {
                seen = seen.saturating_add(1);
                place
            })
        })
        .collect();
    (roots, Some(remap))
}

#[cfg(test)]
mod tests;
