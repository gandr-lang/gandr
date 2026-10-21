//! Edits: every mutation of a store, checked as it is made and as it closes.
//!
//! An [`Edit`] holds the store exclusively. Each step is checked as it is
//! made: a reference to a part that is not live is refused, and a delete that
//! would leave a live part referring to the deleted one is refused naming the
//! arrow and the referrer. Closing the edit checks what only the whole edit
//! can settle: every part it added has every arrow and attribute set, and
//! every path equation holds at every part the edit could have changed. A
//! refused close, a dropped edit and an abandoned one all restore the store
//! as it was, except that the keys the edit minted stay minted: a key once
//! handed out is never handed out again.
//!
//! # The equation check
//!
//! Before an edit every equation holds at every live part. A part's two path
//! ends can change only if the edit added the part or set an arrow cell its
//! paths cross, so the check visits exactly those parts:
//!
//! - each part the edit added, for every equation rooted at its table;
//! - for each arrow cell `(f, x)` the edit set and each occurrence of `f` in an
//!   equation's side after the prefix `p`, every live `y` with `p(y) = x`,
//!   found by walking `p` backwards through the arrows' preimages.
//!
//! A part whose paths cross no changed cell reaches the ends it reached
//! before, where the equation held. The cost is the backward walk plus two
//! path walks per visited part; a prefix arrow whose inverse is kept costs a
//! lookup per step, an unkept one a scan of its column.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;

use crate::error::Refusal;
use crate::parts::Liveness;
use crate::parts::PartKey;
use crate::schema::ArrowId;
use crate::schema::AttributeId;
use crate::schema::EquationId;
use crate::schema::ObjectId;
use crate::store::AttributeValue;
use crate::store::Row;
use crate::store::Store;
use crate::store::ensure_slot;

/// What an edit step replaced in a cell.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Prior<T>
{
    /// The cell held a value.
    Set(T),
    /// The cell was never set: its part was added by this edit.
    Unset,
}

/// One step of an edit, as its undoing needs it.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Undo
{
    /// A part was minted.
    Minted(ObjectId, PartKey),
    /// An arrow cell was set.
    Arrow(ArrowId, PartKey, Prior<PartKey>),
    /// An attribute cell was set.
    Value(AttributeId, PartKey, Prior<AttributeValue>),
    /// A part was deleted.
    Deleted(ObjectId, PartKey),
}

/// Whether an edit still owes its rollback.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Closing
{
    /// Still open: dropping it rolls back.
    Open,
    /// Finished or rolled back.
    Closed,
}

/// An open edit of a store.
///
/// # Specification
/// - requires: construction through [`Store::edit`].
/// - ensures: while open, every set arrow of a live part reaches a live part;
///   once closed by [`Edit::finish`] the store's invariant holds again, or the
///   store is as it was before the edit.
/// - provides: the four mutations and the close.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the defect, equation and keyed fixtures refuse each step
///   and each close by name and observe the store unchanged after every
///   refusal, an abandon and a drop.
/// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
/// - witness: `tests::equations::an_abandoned_edit_leaves_no_part_and_no_reused_key`
/// - witness: `tests::equations::a_refused_close_restores_the_store`
#[derive(Debug)]
#[must_use = "an edit dropped without `finish` is rolled back"]
pub struct Edit<'store>
{
    /// The store being edited.
    store: &'store mut Store,
    /// The steps taken, in order.
    undo: Vec<Undo>,
    /// Arrow cells of parts this edit added that are not yet set.
    unset_arrows: BTreeSet<(ArrowId, PartKey)>,
    /// Attribute cells of parts this edit added that are not yet set.
    unset_values: BTreeSet<(AttributeId, PartKey)>,
    /// Whether the rollback is still owed.
    closing: Closing,
}

impl Store
{
    /// Opens an edit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn edit(&mut self) -> Edit<'_>
    {
        Edit {
            store: self,
            undo: Vec::new(),
            unset_arrows: BTreeSet::new(),
            unset_values: BTreeSet::new(),
            closing: Closing::Open,
        }
    }

    /// Adds one part with its whole row, as one edit.
    ///
    /// # Specification
    /// - ensures: on success the part is live under the returned key with
    ///   exactly the row's arrows and values; on refusal the store is unchanged
    ///   except that the key stays minted.
    /// - fails: [`Refusal::ForeignField`] for a row entry that is not a column
    ///   of the table; the refusals of [`Edit::add_part`], [`Edit::set_arrow`],
    ///   [`Edit::set_value`] and [`Edit::finish`], [`Refusal::Unset`] among
    ///   them for a column the row omits.
    /// - panics: none.
    /// - executable: none — the postcondition reads the whole row back; the
    ///   witnesses do.
    ///
    /// # Errors
    /// Any refusal of the steps above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an edge added with both ends reads them back; one
    ///   whose row omits its target is refused as unset; one naming a vertex
    ///   column is refused as foreign.
    /// - witness: `tests::defect::a_row_must_be_complete_and_its_own`
    #[inline]
    #[cfg_attr(feature = "hotpath", hotpath::measure(impl_type = "Store"))]
    pub fn add_part(
        &mut self,
        object: ObjectId,
        row: &Row,
    ) -> Result<PartKey, Refusal>
    {
        let mut edit = self.edit();
        let part = edit.add_part(object)?;
        for &(arrow, target) in &row.arrows {
            let owner = edit.store.schema.arrow_at(arrow)?.source();
            let field = arrow_name(edit.store, arrow)?;
            edit.ensure_column_of(object, owner, field)?;
            edit.set_arrow(arrow, part, target)?;
        }
        for &(attribute, ref value) in &row.values {
            let owner = edit.store.schema.attribute_at(attribute)?.object();
            let field = edit.store.schema.attribute_at(attribute)?.name().clone();
            edit.ensure_column_of(object, owner, field)?;
            edit.set_value(attribute, part, value)?;
        }
        edit.finish()?;
        Ok(part)
    }

    /// Sets one arrow cell, as one edit.
    ///
    /// # Specification
    /// - ensures: on success the arrow takes the part to the target; on refusal
    ///   the store is unchanged.
    /// - fails: the refusals of [`Edit::set_arrow`] and [`Edit::finish`].
    /// - panics: none.
    /// - executable: none — the postcondition is the read-back the witnesses
    ///   perform.
    ///
    /// # Errors
    /// Any refusal of the steps above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — retargeting an edge is checked against the loop
    ///   equation and refused when it breaks it.
    /// - witness: `tests::equations::retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it`
    #[inline]
    pub fn set_arrow(
        &mut self,
        arrow: ArrowId,
        part: PartKey,
        target: PartKey,
    ) -> Result<(), Refusal>
    {
        let mut edit = self.edit();
        edit.set_arrow(arrow, part, target)?;
        edit.finish()
    }

    /// Sets one attribute cell, as one edit.
    ///
    /// # Specification
    /// - ensures: on success the attribute gives the part the value; on refusal
    ///   the store is unchanged.
    /// - fails: the refusals of [`Edit::set_value`].
    /// - panics: none.
    /// - executable: none — the postcondition is the read-back the witnesses
    ///   perform.
    ///
    /// # Errors
    /// Any refusal of [`Edit::set_value`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a task's standing is set and found through its
    ///   value's inverse, and not through the old value's.
    /// - witness: `tests::keyed::a_standing_moves_between_inverses`
    #[inline]
    pub fn set_value<V>(
        &mut self,
        attribute: AttributeId,
        part: PartKey,
        value: V,
    ) -> Result<(), Refusal>
    where
        V: Into<AttributeValue>,
    {
        let mut edit = self.edit();
        edit.set_value(attribute, part, &value.into())?;
        edit.finish()
    }

    /// Deletes one part, as one edit.
    ///
    /// # Specification
    /// - ensures: on success the part is dead and no other key moved; on
    ///   refusal the store is unchanged.
    /// - fails: the refusals of [`Edit::delete_part`].
    /// - panics: none.
    /// - executable: none — the postcondition is the liveness read-back the
    ///   witnesses perform.
    ///
    /// # Errors
    /// Any refusal of [`Edit::delete_part`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deleting vertex 1 of `1 → 2 → 3` is refused naming
    ///   the edge; deleting the edge first, then the vertex, succeeds and
    ///   leaves the other keys live.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    #[cfg_attr(feature = "hotpath", hotpath::measure(impl_type = "Store"))]
    pub fn delete_part(
        &mut self,
        object: ObjectId,
        part: PartKey,
    ) -> Result<(), Refusal>
    {
        let mut edit = self.edit();
        edit.delete_part(object, part)?;
        edit.finish()
    }
}

/// An arrow's name, for a refusal.
///
/// # Specification
/// - ensures: on success a copy of the arrow's name.
/// - fails: [`Refusal::Schema`] for an arrow outside the schema.
/// - panics: none.
/// - executable: none — the answer is the schema's name.
///
/// # Errors
/// [`Refusal::Schema`].
///
/// # Adequacy
/// - hypothesis: L3 — the foreign-row refusal names the arrow.
/// - witness: `tests::defect::a_row_must_be_complete_and_its_own`
#[inline]
fn arrow_name(
    store: &Store,
    arrow: ArrowId,
) -> Result<crate::schema::Name, Refusal>
{
    Ok(store.schema.arrow_at(arrow)?.name().clone())
}

impl Edit<'_>
{
    /// Adds a part to a table, every column unset.
    ///
    /// # Specification
    /// - ensures: on success the returned key is the table's previous counter
    ///   value, live, with every arrow and attribute of the table unset until
    ///   this edit sets them.
    /// - fails: [`Refusal::Schema`] for an object outside the schema, and
    ///   [`Refusal::Exhausted`] naming a table whose counter is spent.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::Exhausted`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consecutive adds mint consecutive keys, and a finish
    ///   without setting the new part's arrow is refused as unset.
    /// - witness: `tests::defect::a_row_must_be_complete_and_its_own`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |part| self.store.liveness(object, *part) == Ok(Liveness::Live)))]
    pub fn add_part(
        &mut self,
        object: ObjectId,
    ) -> Result<PartKey, Refusal>
    {
        let name = self.store.object_name(object)?;
        let table = self
            .store
            .tables
            .get_mut(usize::from(object))
            .ok_or_else(|| Refusal::Exhausted {
                object: name.clone(),
            })?;
        let part = table.mint().map_err(|_exhausted| Refusal::Exhausted {
            object: name.clone(),
        })?;
        let slot = part
            .slot()
            .map_err(|_unaddressable| Refusal::Exhausted { object: name })?;

        for &arrow in self.store.schema.outgoing(object) {
            if let Some(column) = self.store.arrows.get_mut(usize::from(arrow)) {
                ensure_slot(&mut column.targets, slot);
            }
            self.unset_arrows.insert((arrow, part));
        }
        for &attribute in self.store.schema.fields(object) {
            if let Some(column) = self.store.values.get_mut(usize::from(attribute)) {
                ensure_slot(&mut column.values, slot);
            }
            self.unset_values.insert((attribute, part));
        }

        self.undo.push(Undo::Minted(object, part));
        self.store.touch(object);
        Ok(part)
    }

    /// Sets an arrow cell of a live part to a live target.
    ///
    /// # Specification
    /// - ensures: on success the arrow takes the part to the target, and the
    ///   kept inverse lists the part under the target and under no other.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema, and
    ///   [`Refusal::NotLive`] naming the part or the target, whichever is not
    ///   live, changing nothing.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an edge pointed at a deleted vertex is refused naming
    ///   the vertex; every inverse agrees with a scan after each set.
    /// - witness: `tests::defect::a_reference_to_a_dead_part_is_refused_by_name`
    /// - witness: `tests::equations::every_inverse_agrees_with_a_scan_after_every_edit`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || self.store.target(arrow, part) == Ok(target))]
    pub fn set_arrow(
        &mut self,
        arrow: ArrowId,
        part: PartKey,
        target: PartKey,
    ) -> Result<(), Refusal>
    {
        let spec = self.store.schema.arrow_at(arrow)?;
        let (source, reaches) = (spec.source(), spec.target());
        self.store.ensure_live(source, part)?;
        self.store.ensure_live(reaches, target)?;
        let slot = self.store.slot(source, part)?;

        let prior = if self.unset_arrows.remove(&(arrow, part)) {
            Prior::Unset
        }
        else {
            Prior::Set(self.store.cell(arrow, part)?)
        };
        let Some(column) = self.store.arrows.get_mut(usize::from(arrow))
        else {
            return Err(self.store.not_live(source, part));
        };
        ensure_slot(&mut column.targets, slot);
        if let Prior::Set(old) = prior {
            column.index_remove(old, part);
        }
        if let Some(cell) = column.targets.get_mut(usize::from(slot)) {
            *cell = target;
        }
        column.index_insert(target, part);

        self.undo.push(Undo::Arrow(arrow, part, prior));
        self.store.touch(source);
        Ok(())
    }

    /// Sets an attribute cell of a live part.
    ///
    /// # Specification
    /// - ensures: on success the attribute gives the part the value, and the
    ///   kept inverse lists the part under the value and under no other.
    /// - fails: [`Refusal::Schema`] for an attribute outside the schema, and
    ///   [`Refusal::NotLive`] naming a part that is not live, changing nothing.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a standing set twice is found under the second value
    ///   only.
    /// - witness: `tests::keyed::a_standing_moves_between_inverses`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || self.store.value(attribute, part).is_ok())]
    pub fn set_value(
        &mut self,
        attribute: AttributeId,
        part: PartKey,
        value: &AttributeValue,
    ) -> Result<(), Refusal>
    {
        let object = self.store.schema.attribute_at(attribute)?.object();
        self.store.ensure_live(object, part)?;
        let slot = self.store.slot(object, part)?;
        let unset = self.unset_values.remove(&(attribute, part));

        let Some(column) = self.store.values.get_mut(usize::from(attribute))
        else {
            return Err(self.store.not_live(object, part));
        };
        ensure_slot(&mut column.values, slot);
        let Some(cell) = column.values.get_mut(usize::from(slot))
        else {
            return Err(self.store.not_live(object, part));
        };
        let old = core::mem::replace(cell, value.clone());
        let prior = if unset {
            Prior::Unset
        }
        else {
            column.index_remove(&old, part);
            Prior::Set(old)
        };
        column.index_insert(value, part);

        self.undo.push(Undo::Value(attribute, part, prior));
        self.store.touch(object);
        Ok(())
    }

    /// Deletes a live part no live part refers to.
    ///
    /// # Specification
    /// - ensures: on success the part is dead, no other key moved, and no kept
    ///   inverse lists it.
    /// - fails: [`Refusal::Schema`] for an object outside the schema,
    ///   [`Refusal::NotLive`] for a part that is not live, and
    ///   [`Refusal::Referenced`] naming the first arrow, in ordinal order, and
    ///   the first referring part, in key order, of a part some live part's set
    ///   arrow reaches; each changing nothing.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Refusal::Schema`], [`Refusal::NotLive`] or [`Refusal::Referenced`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the reproduced defect: deleting vertex 1 of `1 → 2 →
    ///   3` is refused naming `src` and the edge, through an indexed and an
    ///   unindexed arrow alike; the edge's own delete succeeds.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    /// - witness: `tests::defect::an_unindexed_arrow_still_refuses_the_delete`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || self.store.liveness(object, part) == Ok(Liveness::Dead))]
    pub fn delete_part(
        &mut self,
        object: ObjectId,
        part: PartKey,
    ) -> Result<(), Refusal>
    {
        self.store.ensure_live(object, part)?;

        for &arrow in self.store.schema.incoming(object) {
            let referrers = self.store.referrers(arrow, part, &self.unset_arrows)?;
            if let Some(&by) = referrers.first() {
                return Err(Refusal::Referenced {
                    object: self.store.object_name(object)?,
                    part,
                    arrow: arrow_name(self.store, arrow)?,
                    by,
                });
            }
        }

        self.unindex(object, part)?;
        if let Some(table) = self.store.tables.get_mut(usize::from(object)) {
            table.remove(part);
        }
        self.undo.push(Undo::Deleted(object, part));
        self.store.touch(object);
        Ok(())
    }

    /// Closes the edit: checks completeness and the equations, or rolls back.
    ///
    /// # Specification
    /// - ensures: on success the store's invariant holds and the edit's steps
    ///   stand; on refusal the store is as it was before the edit, except that
    ///   minted keys stay minted.
    /// - fails: [`Refusal::Unset`] naming the first unset cell of a live part,
    ///   then [`Refusal::EquationViolated`] naming the first violation in
    ///   equation then key order among the parts the edit could change.
    /// - panics: none.
    /// - executable: none — the postcondition is the store invariant, a
    ///   whole-store walk; the audit witnesses compare it.
    /// - intension: visits only the parts the module's equation-check section
    ///   names.
    ///
    /// # Errors
    /// [`Refusal::Unset`] or [`Refusal::EquationViolated`].
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — a loop whose source leaves its vertex is refused
    ///   naming the equation, the part and both ends; retargeting an edge
    ///   reaches, through a two-step backward walk, the loops whose paths cross
    ///   it; after every accepted edit the whole-store audit agrees.
    /// - witness: `tests::equations::a_loop_that_leaves_its_vertex_is_refused_by_equation`
    /// - witness: `tests::equations::retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it`
    /// - witness: `tests::equations::a_refused_close_restores_the_store`
    #[inline]
    pub fn finish(mut self) -> Result<(), Refusal>
    {
        let verdict = self.verdict();
        if verdict.is_err() {
            self.rollback();
        }
        self.closing = Closing::Closed;
        verdict
    }

    /// Abandons the edit, restoring the store.
    ///
    /// # Specification
    /// - ensures: the store is as it was before the edit, except that minted
    ///   keys stay minted.
    /// - panics: none.
    /// - executable: none — the postcondition compares the whole store; the
    ///   witness does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an abandoned add leaves no part, and the next add
    ///   mints the following key.
    /// - witness: `tests::equations::an_abandoned_edit_leaves_no_part_and_no_reused_key`
    #[inline]
    pub fn abandon(mut self)
    {
        self.rollback();
        self.closing = Closing::Closed;
    }

    /// Refuses a row entry that is not a column of the row's table.
    ///
    /// # Specification
    /// - ensures: success exactly when the column's table is the row's.
    /// - fails: [`Refusal::ForeignField`] naming the column and the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Refusal::ForeignField`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an edge row naming a vertex attribute is refused
    ///   naming it.
    /// - witness: `tests::defect::a_row_must_be_complete_and_its_own`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (object == owner))]
    fn ensure_column_of(
        &self,
        object: ObjectId,
        owner: ObjectId,
        field: crate::schema::Name,
    ) -> Result<(), Refusal>
    {
        if object == owner {
            return Ok(());
        }
        Err(Refusal::ForeignField {
            field,
            object: self.store.object_name(object)?,
        })
    }

    /// Checks completeness, then the equations at the affected parts.
    ///
    /// # Specification
    /// - ensures: success exactly when no live part has an unset cell and every
    ///   equation holds at every affected part.
    /// - fails: as [`Edit::finish`].
    /// - panics: none.
    /// - executable: none — see [`Edit::finish`].
    ///
    /// # Errors
    /// [`Refusal::Unset`] or [`Refusal::EquationViolated`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — see [`Edit::finish`].
    /// - witness: `tests::equations::a_loop_that_leaves_its_vertex_is_refused_by_equation`
    /// - witness: `tests::defect::a_row_must_be_complete_and_its_own`
    #[inline]
    fn verdict(&self) -> Result<(), Refusal>
    {
        for &(arrow, part) in &self.unset_arrows {
            let object = self.store.schema.arrow_at(arrow)?.source();
            if self.store.liveness(object, part)? == Liveness::Live {
                return Err(Refusal::Unset {
                    field: arrow_name(self.store, arrow)?,
                    object: self.store.object_name(object)?,
                    part,
                });
            }
        }
        for &(attribute, part) in &self.unset_values {
            let spec = self.store.schema.attribute_at(attribute)?;
            if self.store.liveness(spec.object(), part)? == Liveness::Live {
                return Err(Refusal::Unset {
                    field: spec.name().clone(),
                    object: self.store.object_name(spec.object())?,
                    part,
                });
            }
        }

        for (equation, part) in self.affected()? {
            self.store.check(equation, part)?;
        }
        Ok(())
    }

    /// The parts whose equations this edit could have changed, live, paired
    /// with each equation to check there.
    ///
    /// # Specification
    /// - requires: no live part has an unset cell.
    /// - ensures: on success every pair the module's equation-check section
    ///   names whose part is live, each once, in equation then key order.
    /// - fails: [`Refusal::Schema`] for an identifier outside the schema.
    /// - panics: none.
    /// - executable: none — the set is the check's whole domain; the witnesses
    ///   observe that a violation beyond the edited part is found.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — retargeting an edge finds the loops two arrows
    ///   upstream of it, so a lost prefix step or occurrence leaves their
    ///   violation unrefused; a part minted and deleted in one edit is no part
    ///   to recheck.
    /// - witness: `tests::equations::retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it`
    /// - witness: `tests::equations::a_part_minted_and_deleted_in_one_edit_owes_no_equation`
    #[inline]
    fn affected(&self) -> Result<BTreeSet<(EquationId, PartKey)>, Refusal>
    {
        let schema = &self.store.schema;
        let mut affected = BTreeSet::new();

        for step in &self.undo {
            match *step {
                Undo::Minted(object, part) => {
                    if self.store.liveness(object, part)? == Liveness::Live {
                        for &equation in schema.rooted(object) {
                            affected.insert((equation, part));
                        }
                    }
                },
                Undo::Arrow(arrow, part, _) => {
                    for occurrence in schema.occurrences(arrow) {
                        let equation = schema.equation_at(occurrence.equation)?;
                        let side = equation.side(occurrence.side);
                        let prefix = side
                            .arrows()
                            .get(.. usize::from(occurrence.position))
                            .unwrap_or_default();
                        let start = side.start();
                        for source in self.backward(prefix, part)? {
                            if self.store.liveness(start, source)? == Liveness::Live {
                                affected.insert((occurrence.equation, source));
                            }
                        }
                    }
                },
                Undo::Value(..) | Undo::Deleted(..) => {},
            }
        }

        Ok(affected)
    }

    /// The parts a path prefix takes to one part, by walking the prefix
    /// backwards through its arrows' preimages.
    ///
    /// # Specification
    /// - ensures: on success exactly the live parts `y` of the prefix's start
    ///   with `prefix(y) = part`; `part` itself for the empty prefix.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema.
    /// - panics: none.
    /// - executable: none — the reference is a forward walk from every part,
    ///   the scan this avoids.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-arrow prefix from a loop through an edge to its
    ///   vertex is walked back from the vertex to the loop.
    /// - witness: `tests::equations::retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it`
    #[inline]
    fn backward(
        &self,
        prefix: &[ArrowId],
        part: PartKey,
    ) -> Result<BTreeSet<PartKey>, Refusal>
    {
        let mut frontier = BTreeSet::from([part]);
        for &arrow in prefix.iter().rev() {
            let mut next = BTreeSet::new();
            for &target in &frontier {
                next.extend(self.store.referrers(arrow, target, &self.unset_arrows)?);
            }
            frontier = next;
        }
        Ok(frontier)
    }

    /// Drops a part's set cells from every kept inverse.
    ///
    /// # Specification
    /// - ensures: on success no kept inverse of the part's table lists it.
    /// - fails: [`Refusal::Schema`] for an identifier outside the schema.
    /// - panics: none.
    /// - executable: none — the postcondition reads every inverse; the
    ///   scan-agreement witness does.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — after a delete every inverse agrees with a scan.
    /// - witness: `tests::equations::every_inverse_agrees_with_a_scan_after_every_edit`
    #[inline]
    fn unindex(
        &mut self,
        object: ObjectId,
        part: PartKey,
    ) -> Result<(), Refusal>
    {
        let slot = self.store.slot(object, part)?;
        let outgoing = self.store.schema.outgoing(object).to_vec();
        for arrow in outgoing {
            if self.unset_arrows.contains(&(arrow, part)) {
                continue;
            }
            if let Some(column) = self.store.arrows.get_mut(usize::from(arrow))
                && let Some(&target) = column.targets.get(usize::from(slot))
            {
                column.index_remove(target, part);
            }
        }
        let fields = self.store.schema.fields(object).to_vec();
        for attribute in fields {
            if self.unset_values.contains(&(attribute, part)) {
                continue;
            }
            if let Some(column) = self.store.values.get_mut(usize::from(attribute)) {
                column.index_remove_slot(slot, part);
            }
        }
        Ok(())
    }

    /// Puts a restored part's set cells back into every kept inverse.
    ///
    /// # Specification
    /// - ensures: every kept inverse of the part's table lists it under its set
    ///   cells' values.
    /// - panics: none.
    /// - executable: none — the postcondition reads every inverse; the rollback
    ///   witness does.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — after a refused close that deleted a part, every
    ///   inverse agrees with a scan.
    /// - witness: `tests::equations::a_refused_close_restores_the_store`
    #[inline]
    fn reindex(
        &mut self,
        object: ObjectId,
        part: PartKey,
    )
    {
        let Ok(slot) = part.slot()
        else {
            return;
        };
        let outgoing = self.store.schema.outgoing(object).to_vec();
        for arrow in outgoing {
            if self.unset_arrows.contains(&(arrow, part)) {
                continue;
            }
            if let Some(column) = self.store.arrows.get_mut(usize::from(arrow))
                && let Some(&target) = column.targets.get(usize::from(slot))
            {
                column.index_insert(target, part);
            }
        }
        let fields = self.store.schema.fields(object).to_vec();
        for attribute in fields {
            if self.unset_values.contains(&(attribute, part)) {
                continue;
            }
            if let Some(column) = self.store.values.get_mut(usize::from(attribute)) {
                column.index_insert_slot(slot, part);
            }
        }
    }

    /// Undoes every step, newest first.
    ///
    /// # Specification
    /// - ensures: the store's parts, cells and inverses are as before the edit;
    ///   counters stay where the edit left them.
    /// - panics: none.
    /// - executable: none — the postcondition compares the whole store; the
    ///   witnesses do.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused close after an add, a set and a delete
    ///   leaves a store equal to a copy taken before the edit, apart from the
    ///   counter.
    /// - witness: `tests::equations::a_refused_close_restores_the_store`
    #[inline]
    fn rollback(&mut self)
    {
        while let Some(step) = self.undo.pop() {
            match step {
                Undo::Minted(object, part) => {
                    if let Some(table) = self.store.tables.get_mut(usize::from(object)) {
                        table.remove(part);
                    }
                },
                Undo::Arrow(arrow, part, prior) => {
                    let Ok(slot) = part.slot()
                    else {
                        continue;
                    };
                    let Some(column) = self.store.arrows.get_mut(usize::from(arrow))
                    else {
                        continue;
                    };
                    if let Some(&current) = column.targets.get(usize::from(slot)) {
                        column.index_remove(current, part);
                    }
                    match prior {
                        Prior::Set(old) => {
                            if let Some(cell) = column.targets.get_mut(usize::from(slot)) {
                                *cell = old;
                            }
                            column.index_insert(old, part);
                        },
                        Prior::Unset => {
                            self.unset_arrows.insert((arrow, part));
                        },
                    }
                },
                Undo::Value(attribute, part, prior) => {
                    let Ok(slot) = part.slot()
                    else {
                        continue;
                    };
                    let Some(column) = self.store.values.get_mut(usize::from(attribute))
                    else {
                        continue;
                    };
                    column.index_remove_slot(slot, part);
                    match prior {
                        Prior::Set(old) => {
                            column.index_insert(&old, part);
                            if let Some(cell) = column.values.get_mut(usize::from(slot)) {
                                *cell = old;
                            }
                        },
                        Prior::Unset => {
                            self.unset_values.insert((attribute, part));
                        },
                    }
                },
                Undo::Deleted(object, part) => {
                    if let Some(table) = self.store.tables.get_mut(usize::from(object)) {
                        table.restore(part);
                    }
                    self.reindex(object, part);
                },
            }
        }
    }
}

impl Drop for Edit<'_>
{
    /// Rolls back an edit dropped while open.
    ///
    /// # Specification
    /// - ensures: an open edit's steps are undone; a closed one is left.
    /// - panics: none.
    /// - executable: none — the postcondition compares the whole store; the
    ///   witness does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a step refused inside [`Store::add_part`] drops its
    ///   edit, and the store reads as before.
    /// - witness: `tests::defect::a_row_must_be_complete_and_its_own`
    #[inline]
    fn drop(&mut self)
    {
        if self.closing == Closing::Open {
            self.rollback();
            self.closing = Closing::Closed;
        }
    }
}
