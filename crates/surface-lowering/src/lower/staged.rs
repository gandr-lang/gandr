//! Definitions quantified over stages and regions in the lowering: the
//! telescope `@[i : Size, j < i, r : Region]` after a function's name, the
//! staged types `Nat[i]` and `Nat[<i]` its parameter and result types write,
//! and the region binders a kept type `A at r` names.
//!
//! # A binder is its ordinal
//!
//! The telescope binds each stage binder by its position in it. A staged type
//! in the function's parameter or result types names the stage of the binder
//! its name resolves to: `Nat[i]` the binder's own stage, `Nat[<i]` the stage
//! one below it. The checker mints one stage per binder before it forms the
//! signature, each the stage its ordinal names, so the declared type is
//! written over those stages directly; the bounds cross on the declaration
//! ([`crate::LoweredModule::stages`]), and a call instantiates each binder at
//! the stage its arguments show. A body's types are plain: a case answering a
//! staged result reads its branches at the stage, as a recursion's does.
//!
//! # A call supplies a stage by name
//!
//! A call may state the stage of a binder of its callee, `applyAt[i = j](f,
//! x)`, inside a function quantified over `j`. The supply crosses beside the
//! declaration making the call ([`crate::LoweredModule::supplies`]), at the
//! value the call forces: the callee's binder by its ordinal and the stage the
//! caller's binder `j` mints. It never reaches the kernel, which re-derives
//! every stage from the arguments; the checker holds the supply to the stage
//! they show.
//!
//! # A region binder is the caller's region
//!
//! An entry `r : Region` binds a region its caller holds, by its ordinal among
//! the telescope's region binders. The binders are filed under the
//! declaration's key, and a kept type `A at r` anywhere in the definition
//! that names no capability scope or hold reads `r` there
//! ([`Lowerer::at_type`]), so the type keeps its value at
//! [`gandr_core_term::effect::capability::Region::Bound`]. A region binder is
//! no value: the body reads it only in a kept type.
//!
//! # Boundaries
//!
//! - A telescope entry `a : T` of a sort other than `Size` is an implicit
//!   parameter, which the function's merged telescope binds
//!   ([`crate::module::Plicity`]); an entry out of shape is
//!   [`LoweringRefusal::ImplicitTelescope`].
//! - A bound `i < n` names a binder `i` and a binder `n` written before it;
//!   either name otherwise is [`LoweringRefusal::UnresolvedName`], and so is a
//!   staged type naming no binder of its function's telescope, and a supply `i
//!   = j` whose `j` names no stage binder of the function making the call. A
//!   supply's value is that name alone, and a supply on a reference standing
//!   without a call leaves the fragment.
//! - A staged type anywhere but a quantified function's parameter and result
//!   types leaves the fragment: a stage is the signature's, never a body's. So
//!   does one under a form the marks do not reach through, [`PLACING`] naming
//!   those they do: a path's carrier places no stage.
//! - A stage refining no data type is the checkers' refusal: the kernel's mark
//!   places only data types.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::effect::capability::RegionBinder;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageBinder;
use gandr_kernel_term::StageBound;
use gandr_kernel_term::StageDepth;
use gandr_kernel_term::StageId;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Sink;
use super::Site;
use super::closed;
use super::exhausted;
use super::lowered;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::module::SlotIndex;
use crate::origin::Origin;
use crate::resolve::SurfaceName;
use crate::resolve::TypeAtom;

#[cfg(test)]
mod tests;

/// The type forms whose operands a stage written under them is placed in:
/// the formers the kernel's mark reaches through, arrows and dependent
/// arrows, returners, thunks, products, sums, records and lazy products, a
/// data type's arguments, and parentheses.
const PLACING: [Former; 13] = [
    Former::ValueFunctionType,
    Former::ArrowType,
    Former::ReturnerType,
    Former::ThunkType,
    Former::ProductType,
    Former::SumType,
    Former::LabelledSumType,
    Former::LazyProductType,
    Former::LazyRecordType,
    Former::TelescopeType,
    Former::ParenthesizedType,
    Former::TypeApplication,
    Former::StagedType,
];

/// Whether a stage written under a node is one the signature's marks place.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: two distinct readings.
/// - executable: none — a plain tag.
///
/// # Adequacy
/// - hypothesis: L3 — a stage in a path's carrier is refused and one in an
///   arrow's domain marked.
/// - witness: `lower::staged::tests::a_stage_outside_a_signature_leaves_the_fragment`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Placement
{
    /// Every form above the node places a stage.
    Placed,
    /// Some form above the node places none.
    Unplaced,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Read the telescope `@[i : Size, j < i, r : Region, m : Mode]` a
    /// function's name is followed by, when it is: file its stage binders'
    /// bounds, its region binders and its mode binders, and mark each staged
    /// type its parameter and result types write.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the function's name; `site` is the
    ///   function's declaration form.
    /// - ensures: past a telescope, `cursor` stands after its `]`; when the
    ///   telescope binds a stage, the declaration's bounds are filed under its
    ///   key, one per binder in written order, and every staged type under the
    ///   parameter and result types is marked with the stage its binder's
    ///   ordinal names; when it binds a region, its region binders are filed
    ///   under the key by name, each at its ordinal among them; when it binds a
    ///   mode, its mode binders are filed under the key by name; an entry `a :
    ///   T` of another sort is passed over, the function's merged telescope
    ///   binding it; without a telescope nothing changes.
    /// - fails: [`LoweringRefusal::ImplicitTelescope`] at the declaration for
    ///   an entry out of shape, or one of another sort where the function has
    ///   no merged telescope; [`LoweringRefusal::UnresolvedName`] for a bound
    ///   naming no stage binder, or none written before the one it bounds, and
    ///   for a staged type naming no binder; a fault naming the function for a
    ///   tile out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// The telescope's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a telescope of one binder and of a bounded pair files
    ///   its bounds and marks its staged types; a bound on a later binder and a
    ///   stage naming no binder are refused, each exactly; a stage beside an
    ///   implicit is filed as alone; a region binder is filed by its ordinal
    ///   and its kept types bound to it; a mode binder is filed by its name.
    /// - witness: `lower::implicit::tests::a_stage_telescope_merges_nothing`
    /// - witness: `lower::staged::tests::a_telescope_files_its_bounds_and_marks_its_stages`
    /// - witness: `lower::staged::tests::a_bound_or_stage_naming_no_binder_is_refused_by_name`
    /// - witness: `lower::capability::tests::a_kept_type_at_a_region_binder_is_bound_to_it_1221`
    /// - witness: `lower::method::tests::a_deduced_mode_is_erased_from_the_telescope`
    #[spec(captures: before = self.stage_bounds.len(), ensures: |ret| ret.is_err() || self.stage_bounds.len() >= before)]
    pub(super) fn stage_telescope(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(_) = cursor.tile(TileName::ATTRIBUTES)
        else {
            return Ok(());
        };
        let implicit = LoweringRefusal::ImplicitTelescope { span: site.at.span };
        let mut names: BTreeMap<SurfaceName<'source>, StageBinder> = BTreeMap::new();
        let mut bounds: Vec<StageBound> = Vec::new();
        let mut regions: BTreeMap<SurfaceName<'source>, RegionBinder> = BTreeMap::new();
        let mut modes: BTreeSet<SurfaceName<'source>> = BTreeSet::new();
        loop {
            if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_CLOSE) {
                break;
            }
            let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(implicit);
            };
            let name = self.name_at(written);
            if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
                let sort = site.one(cursor.operands())?;
                let head = matches!(self.form_at(sort)?, Some((_, Former::TypeHead)));
                if head && self.name_at(sort).as_ref() == "Size" {
                    let _shadowed = names.insert(name, StageBinder::from(bounds.len()));
                    bounds.push(StageBound::Unbounded);
                }
                else if head && self.name_at(sort).as_ref() == "Region" {
                    let ordinal = u32::try_from(regions.len()).map_err(|_wide| implicit)?;
                    let _shadowed = regions.insert(name, RegionBinder::from(ordinal));
                }
                else if head && self.name_at(sort).as_ref() == "Mode" {
                    let _fresh = modes.insert(name);
                }
                else if let Maybe::Absent(_) = self.merged_at(site.at.node) {
                    return Err(implicit);
                }
            }
            else if let Maybe::Present(_) = cursor.tile(TileName::LESS_THAN) {
                let Maybe::Present(over) = cursor.tile(TileName::IDENTIFIER)
                else {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                };
                let bounding = self.name_at(over);
                let Some(&bounded) = names.get(&name)
                else {
                    return Err(LoweringRefusal::UnresolvedName {
                        span: written.span,
                        name,
                    });
                };
                let earlier = names
                    .get(&bounding)
                    .copied()
                    .filter(|&earlier| usize::from(earlier) < usize::from(bounded));
                match (earlier, bounds.get_mut(usize::from(bounded))) {
                    (Some(earlier), Some(slot @ &mut StageBound::Unbounded)) => {
                        *slot = StageBound::Below(earlier);
                    },
                    (Some(_), Some(&mut StageBound::Below(_)) | None) => {
                        return Err(site.fault(over.span, FormFault::MisplacedTile));
                    },
                    (None, _) => {
                        return Err(LoweringRefusal::UnresolvedName {
                            span: over.span,
                            name: bounding,
                        });
                    },
                }
            }
            else {
                return Err(implicit);
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::BRACKET_CLOSE)
            {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            }
        }
        if let Maybe::Present(slot) = self.collected.owner_of(site.at.node) {
            if !regions.is_empty() {
                let _first = self.region_binders.insert(slot, regions);
            }
            if !modes.is_empty() {
                let _first = self.mode_binders.insert(slot, modes);
            }
        }
        if bounds.is_empty() {
            return Ok(());
        }
        let mut ahead = cursor.clone();
        let mut pending = Vec::new();
        while let Maybe::Present(piece) = ahead.read() {
            match piece {
                Piece::Tile { label, .. } if label == TileName::BRACE_OPEN => break,
                Piece::Operand(operand) => pending.push((operand.node, Placement::Placed)),
                Piece::Tile { .. } => {},
            }
        }
        pending.reverse();
        let mut scratch = core::mem::take(&mut self.scratch);
        let marked = self.mark_stages(&names, pending, &mut scratch);
        self.scratch = scratch;
        marked?;
        let key = self.key_at(site.at.node);
        let _first = self.stage_bounds.insert(key, bounds);

        Ok(())
    }

    /// The region binder `name` names at `at`: the binder of that name in the
    /// telescope of the definition owning `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the binder [`Self::stage_telescope`] filed under the slot
    ///   owning `at` by `name`; none where no slot owns `at` or its definition
    ///   binds no region of that name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter's kept type and a body's value name the
    ///   binder of their definition's telescope.
    /// - witness: `lower::capability::tests::a_kept_type_at_a_region_binder_is_bound_to_it_1221`
    #[spec(ensures: |ret| ret.is_none() || matches!(self.collected.owner_of(at), Maybe::Present(_)))]
    pub(super) fn region_binder(
        &self,
        at: NodeIndex,
        name: SurfaceName<'source>,
    ) -> Option<RegionBinder>
    {
        let Maybe::Present(slot) = self.collected.owner_of(at)
        else {
            return None;
        };
        self.region_binders.get(&slot)?.get(&name).copied()
    }

    /// The stages a call at `site` supplies the stage binders of the function
    /// at `callee` at, `f[i = j]`, each such resident taken out of
    /// `supplied`.
    ///
    /// # Specification
    /// - requires: `supplied` holds the call's residents `a = e` by name, each
    ///   beside its name's tile and its value's node.
    /// - ensures: one entry per resident naming a stage binder of `callee`, the
    ///   binder's ordinal beside the stage of the binder of the function making
    ///   the call its value names, that binder's own ordinal; those residents
    ///   are taken out of `supplied`, which keeps every other one. Nothing
    ///   changes for a callee quantified over no stage.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at a value naming no stage
    ///   binder of the function making the call; the reserved refusal at a
    ///   resident whose value is not a name; a form fault reading a value.
    /// - panics: none.
    ///
    /// # Errors
    /// The first refusal met.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call inside a quantified function supplying its own
    ///   binder files the stage at the callee's binder; a supply naming no
    ///   binder of the caller is refused at the name.
    /// - witness: `lower::staged::tests::a_supplied_stage_crosses_at_the_call_s_head_1227`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |staged| staged.len() <= self.collected.stage_binders.get(&callee).map_or(0, Vec::len)))]
    pub(super) fn stage_supplies(
        &mut self,
        site: Site,
        callee: SlotIndex,
        supplied: &mut BTreeMap<SurfaceName<'source>, (Placed, NodeIndex)>,
    ) -> Result<Vec<(StageBinder, Stage)>, LoweringRefusal<'source>>
    {
        let mut staged = Vec::new();
        let ordinals = |names: &[SurfaceName<'source>]| -> BTreeMap<SurfaceName<'source>, usize> {
            names
                .iter()
                .enumerate()
                .map(|(ordinal, &name)| (name, ordinal))
                .collect()
        };
        let Some(callee) = self
            .collected
            .stage_binders
            .get(&callee)
            .map(|names| ordinals(names))
        else {
            return Ok(staged);
        };
        let caller = match self.collected.owner_of(site.at.node) {
            Maybe::Present(owner) => self
                .collected
                .stage_binders
                .get(&owner)
                .map(|names| ordinals(names))
                .unwrap_or_default(),
            Maybe::Absent(_) => BTreeMap::new(),
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let mut outcome = Ok(());
        for (name, &(written, value)) in supplied.iter() {
            let Some(&binder) = callee.get(name)
            else {
                continue;
            };
            if let Err(refusal) = read_pieces(self.pbg, self.tree, value, &mut scratch) {
                outcome = Err(refusal);
                break;
            }
            let [Piece::Tile { label, at }] = *scratch.pieces.as_slice()
            else {
                outcome = Err(Site {
                    at: written,
                    ..site
                }
                .out(FragmentBoundary::Reserved));
                break;
            };
            let stage_name = self.name_at(at);
            match caller.get(&stage_name) {
                Some(&ordinal) if label == TileName::IDENTIFIER => {
                    staged.push((StageBinder::from(binder), Stage::At(StageId::from(ordinal))));
                },
                Some(_) | None => {
                    outcome = Err(LoweringRefusal::UnresolvedName {
                        span: at.span,
                        name: stage_name,
                    });
                    break;
                },
            }
        }
        self.scratch = scratch;
        outcome?;
        supplied.retain(|name, _| !callee.contains_key(name));

        Ok(staged)
    }

    /// Mark every staged type under `pending` with the stage of the binder of
    /// `names` it names.
    ///
    /// # Specification
    /// - requires: `scratch` is free for reading pieces; each pending node is
    ///   paired with whether a stage written under it is placed.
    /// - ensures: each staged type reached is marked `At` its binder's ordinal,
    ///   or one `Below` it when written `<`; a node stays placed while every
    ///   form above it is one [`PLACING`] names.
    /// - fails: [`LoweringRefusal::UnresolvedName`] for a staged type naming no
    ///   binder of `names`; the out-of-fragment refusal for one under a form
    ///   that places no stage, a path's carrier or a capability's region among
    ///   them; a form fault reading a node's pieces.
    /// - panics: none.
    ///
    /// # Errors
    /// The first refusal met.
    ///
    /// # Termination
    /// - reason: the `while let` worklist, not recursion; each node is popped
    ///   once, the tree being a tree.
    /// - measure: the nodes under `pending` not yet popped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stage_telescope`], and a stage in a path's
    ///   carrier is refused where it is written.
    /// - witness: `lower::staged::tests::a_telescope_files_its_bounds_and_marks_its_stages`
    /// - witness: `lower::staged::tests::a_stage_outside_a_signature_leaves_the_fragment`
    #[spec(captures: before = self.stage_marks.len(), ensures: |ret| ret.is_err() || self.stage_marks.len() >= before)]
    fn mark_stages(
        &mut self,
        names: &BTreeMap<SurfaceName<'source>, StageBinder>,
        mut pending: Vec<(NodeIndex, Placement)>,
        scratch: &mut Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        while let Some((at, placement)) = pending.pop() {
            let Some(node) = self.tree.node(at)
            else {
                continue;
            };
            let placed = Placed::of(at, node);
            let formed = self.form_at(placed)?;
            read_pieces(self.pbg, self.tree, at, scratch)?;
            if let Some((form, Former::StagedType)) = formed {
                if placement == Placement::Unplaced {
                    return Err(LoweringRefusal::OutOfFragment {
                        span: placed.span,
                        form,
                        sort: FragmentSort::ValueType,
                        boundary: FragmentBoundary::Unadmitted,
                    });
                }
                let below = scratch.pieces.iter().any(|piece| {
                    matches!(*piece, Piece::Tile { label, .. } if label == TileName::LESS_THAN)
                });
                let written = scratch.pieces.iter().find_map(|piece| match *piece {
                    Piece::Tile { label, at } if label == TileName::IDENTIFIER => Some(at),
                    Piece::Tile { .. } | Piece::Operand(_) => None,
                });
                if let Some(written) = written {
                    let name = self.name_at(written);
                    let Some(&binder) = names.get(&name)
                    else {
                        return Err(LoweringRefusal::UnresolvedName {
                            span: written.span,
                            name,
                        });
                    };
                    let anchor = StageId::from(usize::from(binder));
                    let stage = if below {
                        Stage::Below {
                            anchor,
                            depth: StageDepth::from(core::num::NonZeroU32::MIN),
                        }
                    }
                    else {
                        Stage::At(anchor)
                    };
                    let _first = self.stage_marks.insert(at, stage);
                }
            }
            let below = match formed {
                Some((_, former)) if !PLACING.contains(&former) => Placement::Unplaced,
                Some(_) | None => placement,
            };
            pending.extend(
                scratch
                    .pieces
                    .iter()
                    .rev()
                    .filter_map(|piece| match *piece {
                        Piece::Operand(operand) => Some((operand.node, below)),
                        Piece::Tile { .. } => None,
                    }),
            );
        }

        Ok(())
    }

    /// Classify a staged type, `Nat[i]` or `Nat[<i]`, or the view type
    /// `View[m](a)` a method answering a place declares its result at.
    ///
    /// # Specification
    /// - requires: `site` is a staged type.
    /// - ensures: the type stands as its operand at the stage its function's
    ///   telescope marked it with, the operand read where the staged type
    ///   stands; a view type its function recorded stands as its place's index,
    ///   the atom `Integer`, its element read by the function.
    /// - fails: the wrong-sort refusal where no value type is read; a fault
    ///   naming the form for a tile out of place; the out-of-fragment refusal
    ///   for a staged type no quantified function's signature marked;
    ///   [`LoweringRefusal::ViewNotPlace`] for a view type no method answering
    ///   a place declares its result at.
    /// - panics: none.
    ///
    /// # Errors
    /// The type's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a marked staged type plans its stage, and one in a
    ///   body is refused; a view type at a method's result plans the index, and
    ///   one at a parameter is refused.
    /// - witness: `lower::staged::tests::a_telescope_files_its_bounds_and_marks_its_stages`
    /// - witness: `lower::staged::tests::a_stage_outside_a_signature_leaves_the_fragment`
    /// - witness: `lower::method::tests::a_view_method_answers_its_place_index`
    /// - witness: `lower::method::tests::a_view_method_answering_no_place_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Staged(..) | Plan::Atom(TypeAtom::Integer)))))]
    pub(super) fn staged_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::ValueType)?;
        let base = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::BRACKET_OPEN)?;
        let _below = cursor.tile(TileName::LESS_THAN);
        let Maybe::Present(_) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
        if let Maybe::Present(_) = cursor.at(TileName::PAREN_OPEN) {
            if !self.view_types.contains(&site.at.node) {
                return Err(LoweringRefusal::ViewNotPlace { span: site.at.span });
            }
            self.plan(site, Plan::Atom(TypeAtom::Integer));
            return Ok(());
        }
        exhausted(site, &cursor)?;
        let Some(&stage) = self.stage_marks.get(&site.at.node)
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        self.read(base.node, site.reading);
        self.plan(site, Plan::Staged(base.node, stage));

        Ok(())
    }

    /// Mint the staged type over `base` at `stage`.
    ///
    /// # Specification
    /// - requires: `base` is already minted or absent.
    /// - ensures: the staged type over the base's lowered type at `origin`; the
    ///   base's absence otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::staged_type`].
    /// - witness: `lower::staged::tests::a_telescope_files_its_bounds_and_marks_its_stages`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(Lowered::ValueType(id)) => sink.origins.value_type(id) == Maybe::Present(origin),
        Maybe::Present(_) => false,
        Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_staged(
        &self,
        base: NodeIndex,
        stage: Stage,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        self.value_type_at(base).map(|base| {
            let id = sink.arena.value_type_staged(base, stage);
            sink.origins.record_value_type(id, origin);
            Lowered::ValueType(id)
        })
    }
}
