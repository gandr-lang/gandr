//! The static bracket after a record type in the lowering: the field form
//! `T[.l = v, …]` fixes the fields it names, and the face form `T[f ↦ *{.l =
//! v, …}]` fixes the fields of the face `f` that the type member `T` names,
//! `type T = *{…} where face f = { … }`.
//!
//! # A patched type is the record of its free fields
//!
//! The base `T` is a record type: a type member whose definition is a record,
//! or a record written in place. The patched type lowers to the record of the
//! fields the bracket leaves free, each at the type the base writes for it
//! ([`Plan::Patched`]). Each fixed value is read as a value where the bracket
//! stands, so its names resolve there. A field's value is written as a type
//! takes a value as a call's argument: a number, a boolean, a name or a call.
//! A face's value is an expression, the record of the face's fields. The core
//! type holds no fixed value: a value of the patched type is the record of its
//! free fields.
//!
//! # A fixed field reads its value back
//!
//! A selection `c.l` off a name written at a patched type reads a free field
//! as the field of the record, and a fixed field as the value the bracket
//! fixes ([`Lowerer::patched_field`]). That value is a literal: a number, a
//! string, a character or a boolean. A literal holds no name, so it reads the
//! same at the bracket and at the selection.
//!
//! # Boundaries
//!
//! - A fixed label the base does not write is
//!   [`LoweringRefusal::UnresolvedName`]. So is a face the base's type member
//!   does not name, and a label of a face's value that the face does not hold.
//!   A face's value that omits a label of the face is a form fault.
//! - The face form holds one face. Two faces, `T[f ↦ a, g ↦ b]`, form no
//!   bracket of the grammar.
//! - A face's value that is no record written in place, and a fixed field read
//!   back where its value is no literal, leave the fragment
//!   ([`Unbuilt::FixedValue`]). So does a base with a field whose type names an
//!   earlier field ([`Unbuilt::DependentPatch`]).
//! - The checker reads no fixed value. It does not check a fixed value at its
//!   field's type, and it does not coerce a value of the base to the patched
//!   type: the core holds no patched type of its own.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::Side;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_shapes::Membership;
use quenchant_shape::shape::Maybe;

use super::Frame;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Site;
use super::arity::Arranged;
use super::arity::Entry;
use super::arity::Held;
use super::arity::Key;
use super::arity::Planned;
use super::arity::Thunked;
use super::arity::arrange;
use super::arity::separated;
use super::closed;
use super::exhausted;
use super::parse_literal;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::module::SlotIndex;
use crate::module::TypeMeaning;
use crate::resolve::SurfaceName;
use crate::unbuilt::Unbuilt;

#[cfg(test)]
mod tests;

/// What a static bracket after a type writes.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a field form holds one labelled entry per fixed field, in written
///   order, each label once; a face form holds the face's name and its value.
/// - executable: none — [`Lowerer::bracket`] reads it off the form.
///
/// # Adequacy
/// - hypothesis: L3 — a stage, a field form and a face form each reach their
///   own reading.
/// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
/// - witness: `lower::staged::tests::a_telescope_files_its_bounds_and_marks_its_stages`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Bracket<'source>
{
    /// A stage `T[i]` or `T[< i]`, or a view's mode `View[m](a)`.
    Stage,
    /// The field form `T[.l = v, …]`.
    Fields(Vec<Entry<'source>>),
    /// The face form `T[f ↦ v]`: the face's name and its value.
    Face(Placed, Placed),
}

/// What a staged type's bracket writes, read off its own tiles.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: two distinct readings.
/// - executable: none — a plain tag.
///
/// # Adequacy
/// - hypothesis: L3 — a patched type in a quantified function's signature is
///   left unmarked, and a stage beside it is marked.
/// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Written
{
    /// A stage or a view's mode.
    Stage,
    /// A field form or a face form.
    Patch,
}

/// What the staged type whose reading is `pieces` writes: a patch when a
/// `.` or a `↦` stands among its own tiles.
///
/// # Specification
/// - requires: `pieces` is the reading of a staged type.
/// - ensures: a patch exactly when a tile of the form is `.` or `↦`; a stage
///   and a view's mode write neither.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a patched type in a quantified function's signature is
///   left unmarked, and a stage beside it is marked.
/// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
#[spec(ensures: |ret| (ret == Written::Patch) == pieces.iter().any(|piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::DOT || label == TileName::MAPS_TO)))]
pub(super) fn bracket_of(pieces: &[Piece]) -> Written
{
    if pieces.iter().any(|piece| {
        matches!(*piece, Piece::Tile { label, .. } if label == TileName::DOT || label == TileName::MAPS_TO)
    }) {
        Written::Patch
    }
    else {
        Written::Stage
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// Read what the static bracket of the form at `site` writes, the cursor
    /// standing just past its `[`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past a staged type's `[`.
    /// - ensures: the field form's entries when a `.` follows the `[`, the face
    ///   form's face when a `↦` follows the name after it, the cursor exhausted
    ///   for either; a stage otherwise, the cursor where it stood.
    /// - fails: a misplaced tile; an index label, `.0 = v`, is
    ///   [`LoweringRefusal::UnresolvedName`]; a label written twice is
    ///   [`LoweringRefusal::DuplicateDefinition`]; a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field form, a face form and a stage each read
    ///   apart, and a field fixed twice is refused at its second label.
    /// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
    /// - witness: `lower::patched::tests::a_bracket_naming_what_its_base_lacks_is_refused_by_the_name`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |bracket| match *bracket {
        | Bracket::Fields(ref fixed) => !fixed.is_empty() && fixed.iter().all(|entry| matches!(entry.key, Key::Label(..))),
        | Bracket::Face(..) | Bracket::Stage => true,
    }))]
    pub(super) fn bracket(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Bracket<'source>, LoweringRefusal<'source>>
    {
        if let Maybe::Present(_) = cursor.at(TileName::DOT) {
            let mut fixed = Vec::new();
            while let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_CLOSE) {
                let key = match self.dotted(site, cursor)? {
                    Key::Index(_, name, at) => {
                        return Err(LoweringRefusal::UnresolvedName {
                            span: at.span,
                            name,
                        });
                    },
                    key @ (Key::Label(..) | Key::Positional) => key,
                };
                closed(site, cursor, TileName::EQUALS)?;
                fixed.push(Entry {
                    key,
                    held: Held::Operand(site.one(cursor.operands())?),
                });
                separated(site, cursor, TileName::BRACKET_CLOSE)?;
            }
            exhausted(site, cursor)?;
            return match arrange(site, fixed)? {
                Arranged::Labelled(fixed) => Ok(Bracket::Fields(fixed)),
                Arranged::Positional(_) => Err(site.fault(site.at.span, FormFault::MisplacedTile)),
            };
        }
        let faced = matches!(
            cursor.remaining().get(1),
            Some(&Piece::Tile { label, .. }) if label == TileName::MAPS_TO
        );
        if !faced {
            return Ok(Bracket::Stage);
        }
        let Maybe::Present(face) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(site, cursor, TileName::MAPS_TO)?;
        let value = site.one(cursor.operands())?;
        closed(site, cursor, TileName::BRACKET_CLOSE)?;
        exhausted(site, cursor)?;

        Ok(Bracket::Face(face, value))
    }

    /// Classify the field form `T[.l = v, …]` at `site` over `base`, under
    /// the frame `frame` the staged type reads its operands in.
    ///
    /// # Specification
    /// - requires: `site` is a staged type read as a value type under `frame`;
    ///   `fixed` is its bracket's field form.
    /// - ensures: the base is read as a value type and each fixed value as a
    ///   value, both under `frame`; the type is planned as the record of the
    ///   base's fields no entry of `fixed` names.
    /// - fails: as [`Self::free_fields`].
    /// - panics: none.
    ///
    /// # Errors
    /// The type's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type member's record and a record written in place,
    ///   each patched at two of three fields, and a field the base lacks.
    /// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
    /// - witness: `lower::patched::tests::a_bracket_naming_what_its_base_lacks_is_refused_by_the_name`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Patched(_))))]
    pub(super) fn patched_fields(
        &mut self,
        site: Site,
        frame: Frame,
        base: Placed,
        fixed: &[Entry<'source>],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let (entries, _) = self.base_record(site, frame, base)?;
        let labels = fixed
            .iter()
            .filter_map(|entry| match entry.key {
                Key::Label(label, at) => Some((label, at)),
                Key::Index(..) | Key::Positional => None,
            })
            .collect();
        let free = self.free_fields(site, &entries, &labels)?;
        self.read(base.node, Reading::ValueType(frame));
        for entry in fixed {
            self.read(entry.held.at().node, Reading::Value(frame));
        }
        self.plan(site, Plan::Patched(free));

        Ok(())
    }

    /// Classify the face form `T[f ↦ v]` at `site` over `base`, under the
    /// frame `frame` the staged type reads its operands in.
    ///
    /// # Specification
    /// - requires: `site` is a staged type read as a value type under `frame`;
    ///   `face` and `value` are its bracket's face and the value the bracket
    ///   fixes it at.
    /// - ensures: for a face the base's type member names, whose value is a
    ///   record written in place over exactly the face's labels: the base is
    ///   read as a value type and the value as a value, both under `frame`, and
    ///   the type is planned as the record of the base's fields outside the
    ///   face.
    /// - fails: the unresolved-name refusal for a face the type member does not
    ///   name, a base that is no type member, and a label of the value the face
    ///   does not hold; a form fault for a value that omits a label of the
    ///   face; [`Unbuilt::FixedValue`] for a value that is no record written in
    ///   place; as [`Self::free_fields`].
    /// - panics: none.
    ///
    /// # Errors
    /// The type's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a face of two of three fields, and a face the type
    ///   does not name.
    /// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
    /// - witness: `lower::patched::tests::a_bracket_naming_what_its_base_lacks_is_refused_by_the_name`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Patched(_))))]
    pub(super) fn patched_face(
        &mut self,
        site: Site,
        frame: Frame,
        base: Placed,
        face: Placed,
        value: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let (entries, held) = self.base_record(site, frame, base)?;
        let named = self.name_at(face);
        let unnamed = LoweringRefusal::UnresolvedName {
            span: face.span,
            name: named,
        };
        let Some(record) = held.and_then(|held| self.collected.record_faces.get(&held))
        else {
            return Err(unnamed);
        };
        let Some(&(_, ref subshape)) = record.faces.iter().find(|&&(name, _)| name == named)
        else {
            return Err(unnamed);
        };
        let written = self.face_value(site, value)?;
        let mut fixed = BTreeMap::new();
        for entry in &written {
            let Key::Label(label, at) = entry.key
            else {
                return Err(site.fault(entry.keyed_at().span, FormFault::MisplacedTile));
            };
            let inside = record
                .boundary
                .point(label)
                .ok()
                .and_then(|point| subshape.contains(point).ok());
            if inside != Some(Membership::Inside) {
                return Err(LoweringRefusal::UnresolvedName {
                    span: at.span,
                    name: label,
                });
            }
            let _first = fixed.insert(label, at);
        }
        let held_labels = subshape
            .decisions()
            .iter()
            .filter(|&&decision| decision == Membership::Inside)
            .count();
        if fixed.len() != held_labels {
            let form = self.form_at(value)?.map_or(site.name, |(name, _)| name);
            return Err(LoweringRefusal::MalformedForm {
                span: value.span,
                form,
                fault: FormFault::MissingOperand,
            });
        }
        let free = self.free_fields(site, &entries, &fixed)?;
        self.read(base.node, Reading::ValueType(frame));
        self.read(value.node, Reading::Value(frame));
        self.plan(site, Plan::Patched(free));

        Ok(())
    }

    /// The entries of the record type `base` names, and the held slot of the
    /// type member it names when it names one.
    ///
    /// # Specification
    /// - requires: `base` is a staged type's base, read under `frame`.
    /// - ensures: the entries of the record a manifest type member's definition
    ///   writes, with that member's held slot, when `base` names one; otherwise
    ///   the entries of the record `base` writes in place, with no slot; no
    ///   entries when neither is a record.
    /// - fails: the name's own resolution refusals; the record's own
    ///   malformation; [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type member's record and a record written in place.
    /// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ref entries, _)| entries.iter().all(|entry| !matches!(entry.key, Key::Positional))))]
    fn base_record(
        &mut self,
        site: Site,
        frame: Frame,
        base: Placed,
    ) -> Result<(Vec<Entry<'source>>, Option<SlotIndex>), LoweringRefusal<'source>>
    {
        let mut record = base.node;
        let mut held = None;
        if let Some((name, Former::TypeHead | Former::Name | Former::Constructor)) =
            self.form_at(base)?
        {
            let named = Site {
                at: base,
                name,
                reading: Reading::ValueType(frame),
            };
            if let Maybe::Present(stated) = self.stated_named(named, self.name_at(base))?
                && let TypeMeaning::Manifest(defined) = stated.meaning
            {
                record = defined.node;
                held = Some(stated.held);
            }
        }
        let entries = match self.stated_form(site, record, Former::TelescopeType, Thunked(false))? {
            Maybe::Present((_, entries))
                if entries
                    .iter()
                    .all(|entry| matches!(entry.key, Key::Label(..))) =>
            {
                entries
            },
            Maybe::Present(_) | Maybe::Absent(_) => Vec::new(),
        };

        Ok((entries, held))
    }

    /// The record of the base's fields `fixed` leaves free: each field's label
    /// and the node of the type the base writes for it.
    ///
    /// # Specification
    /// - requires: `entries` are the labelled entries of the base's record;
    ///   `fixed` holds each fixed label with where it is written.
    /// - ensures: every entry whose label `fixed` does not hold, by label.
    /// - fails: the unresolved-name refusal for the least fixed label no entry
    ///   writes; [`Unbuilt::DependentPatch`] when an entry's type names an
    ///   earlier label; the budget refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two of three fields fixed leave the third, and a
    ///   label the record lacks is refused by its name.
    /// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
    /// - witness: `lower::patched::tests::a_bracket_naming_what_its_base_lacks_is_refused_by_the_name`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |free| free.len() <= entries.len()))]
    fn free_fields(
        &mut self,
        site: Site,
        entries: &[Entry<'source>],
        fixed: &BTreeMap<SurfaceName<'source>, Placed>,
    ) -> Result<BTreeMap<FieldLabel, NodeIndex>, LoweringRefusal<'source>>
    {
        let written: BTreeMap<SurfaceName<'source>, NodeIndex> = entries
            .iter()
            .filter_map(|entry| match entry.key {
                Key::Label(label, _) => Some((label, entry.held.at().node)),
                Key::Index(..) | Key::Positional => None,
            })
            .collect();
        if let Some((&label, &at)) = fixed
            .iter()
            .find(|&(label, _)| !written.contains_key(label))
        {
            return Err(LoweringRefusal::UnresolvedName {
                span: at.span,
                name: label,
            });
        }
        if let Maybe::Present(_) = self.dependent_links(entries)? {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::DependentPatch)));
        }

        Ok(written
            .into_iter()
            .filter(|&(ref label, _)| !fixed.contains_key(label))
            .map(|(label, node)| (FieldLabel::from(String::from(label.as_ref())), node))
            .collect())
    }

    /// The entries of the record a face's value writes in place, `*{.l = v,
    /// …}`.
    ///
    /// # Specification
    /// - requires: `value` is the value of a face form at `site`.
    /// - ensures: the record's entries in written order, each label once.
    /// - fails: [`Unbuilt::FixedValue`] for a value that is no record written
    ///   with labels; the record's own malformation and its labels' refusals,
    ///   as [`Self::dotted_entries`] and [`arrange`] read them.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a record of the face's two fields, and a value that
    ///   is a name.
    /// - witness: `lower::patched::tests::a_patched_type_is_the_record_of_its_free_fields`
    /// - witness: `lower::patched::tests::a_fixed_value_the_lowering_does_not_read_leaves_the_fragment`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| !matches!(entry.key, Key::Positional))))]
    fn face_value(
        &self,
        site: Site,
        value: Placed,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let declined = || site.out(FragmentBoundary::Unadmitted(Unbuilt::FixedValue));
        let Some((name, Former::Telescope)) = self.form_at(value)?
        else {
            return Err(declined());
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, value.node, &mut pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(name));
        }
        let written = Site {
            at: value,
            name,
            reading: site.reading,
        };
        let mut cursor = Cursor::new(&pieces.pieces, value.span);
        closed(written, &mut cursor, TileName::RECORD)?;
        if let Maybe::Absent(_) = cursor.at(TileName::DOT) {
            return Err(declined());
        }
        let entries = self.dotted_entries(written, &mut cursor, TileName::EQUALS)?;
        match arrange(written, entries)? {
            Arranged::Labelled(entries) => Ok(entries),
            Arranged::Positional(_) => Err(declined()),
        }
    }

    /// The fields a patched type written at `declared` fixes, each label with
    /// its value, read off its bracket.
    ///
    /// # Specification
    /// - requires: `declared` is the type a name's binder or declaration is
    ///   written with; `site` is a selection off that name.
    /// - ensures: each fixed label with its value when the type is a staged
    ///   type whose bracket writes a field form, or a face form of one face
    ///   whose value is a record written in place; nothing for any other type.
    /// - fails: the bracket's own malformation, as [`Self::bracket`] and
    ///   [`Self::face_value`] read it.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field form and a face form each read their fixed
    ///   values back.
    /// - witness: `lower::patched::tests::a_fixed_field_reads_its_value_back`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|fixed| fixed.as_ref().is_none_or(|fixed| !fixed.is_empty())))]
    fn fixed_fields(
        &self,
        site: Site,
        declared: NodeIndex,
    ) -> Result<Option<BTreeMap<SurfaceName<'source>, Placed>>, LoweringRefusal<'source>>
    {
        let Some(tree) = self.tree.node(declared)
        else {
            return Ok(None);
        };
        let placed = Placed::of(declared, tree);
        let Some((name, Former::StagedType)) = self.form_at(placed)?
        else {
            return Ok(None);
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, declared, &mut pieces)?;
        if bracket_of(&pieces.pieces) == Written::Stage {
            return Ok(None);
        }
        let written = Site {
            at: placed,
            name,
            reading: site.reading,
        };
        let mut cursor = Cursor::new(&pieces.pieces, placed.span);
        let _base = written.one(cursor.operands())?;
        closed(written, &mut cursor, TileName::BRACKET_OPEN)?;
        let fixed = match self.bracket(written, &mut cursor)? {
            Bracket::Stage => return Ok(None),
            Bracket::Fields(fixed) => fixed,
            Bracket::Face(_, value) => self.face_value(written, value)?,
        };

        Ok(Some(
            fixed
                .iter()
                .filter_map(|entry| match entry.key {
                    Key::Label(label, _) => Some((label, entry.held.at())),
                    Key::Index(..) | Key::Positional => None,
                })
                .collect(),
        ))
    }

    /// Classify a selection `c.l` off a name written at a patched type.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: planned when the selection is one link off a name whose
    ///   binder or declaration is written at a patched type: a fixed field as
    ///   the literal its value is, and a free field as the field of the record,
    ///   the name read as a value under the form's frame; nothing is planned
    ///   otherwise.
    /// - fails: [`Unbuilt::FixedValue`] for a fixed field whose value is no
    ///   literal; the wrong-sort refusal where neither a value nor a
    ///   computation is read; the name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fixed number, a fixed boolean and a free string
    ///   read off one name, and a fixed name read back.
    /// - witness: `lower::patched::tests::a_fixed_field_reads_its_value_back`
    /// - witness: `lower::patched::tests::a_fixed_value_the_lowering_does_not_read_leaves_the_fragment`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&(Plan::Field(..) | Plan::Literal(_) | Plan::Boolean(_)))))]
    pub(super) fn patched_field(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let Ok((target, selected)) = Self::link(site, &pieces.pieces, site.at.span)
        else {
            return Ok(Planned(false));
        };
        let Some((_, Former::Name)) = self.form_at(target)?
        else {
            return Ok(Planned(false));
        };
        let frame = site.reading.frame();
        let named = Site {
            at: target,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let declared = match self.resolve_name(named, frame, self.name_at(target))? {
            Maybe::Present(Resolved::Binder(bound)) => bound.declared,
            Maybe::Present(Resolved::Declaration { declared, .. }) => declared,
            Maybe::Absent(_) => return Ok(Planned(false)),
        };
        let Maybe::Present(declared) = declared
        else {
            return Ok(Planned(false));
        };
        let Some(fixed) = self.fixed_fields(site, declared)?
        else {
            return Ok(Planned(false));
        };
        let member = self.name_at(selected);
        if let Some(&value) = fixed.get(&member) {
            let _frame = self.require(site, Produced::Value)?;
            let plan = self.fixed_literal(site, value)?;
            self.plan(site, plan);
        }
        else {
            let frame = self.require(site, Produced::Computation)?;
            self.read(target.node, Reading::Value(frame));
            let label = FieldLabel::from(String::from(member.as_ref()));
            self.plan(site, Plan::Field(target.node, label));
        }

        Ok(Planned(true))
    }

    /// The plan of the literal a fixed field's value `value` is, read back at
    /// the selection `site`.
    ///
    /// # Specification
    /// - requires: `value` is a fixed field's value.
    /// - ensures: a boolean as its side, `true` the left; a number, a character
    ///   or a string with no interpolation as the literal its text parses to.
    /// - fails: [`Unbuilt::FixedValue`] for any other value, a number with a
    ///   suffix among them.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a number and a boolean read back, and a name refused.
    /// - witness: `lower::patched::tests::a_fixed_field_reads_its_value_back`
    /// - witness: `lower::patched::tests::a_fixed_value_the_lowering_does_not_read_leaves_the_fragment`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |plan| matches!(*plan, Plan::Literal(_) | Plan::Boolean(_))))]
    fn fixed_literal(
        &self,
        site: Site,
        value: Placed,
    ) -> Result<Plan, LoweringRefusal<'source>>
    {
        let declined = || site.out(FragmentBoundary::Unadmitted(Unbuilt::FixedValue));
        let Some((_, former)) = self.form_at(value)?
        else {
            return Err(declined());
        };
        let text = self.text_at(value);
        if former == Former::Boolean {
            let side = if text.as_ref() == "true" {
                Side::Left
            }
            else {
                Side::Right
            };
            return Ok(Plan::Boolean(side));
        }
        if !matches!(former, Former::Number | Former::Character | Former::Text) {
            return Err(declined());
        }
        if former == Former::Text {
            let mut pieces = Pieces::new();
            read_pieces(self.pbg, self.tree, value.node, &mut pieces)?;
            let interpolated = pieces.pieces.iter().any(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::INTERPOLATION),
            );
            if interpolated {
                return Err(declined());
            }
        }
        match parse_literal(former, text) {
            Maybe::Present(literal) => Ok(Plan::Literal(literal)),
            Maybe::Absent(_) => Err(declined()),
        }
    }
}
