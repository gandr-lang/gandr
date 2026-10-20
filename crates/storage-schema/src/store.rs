//! The store: one schema's parts, columns and materialized inverses.
//!
//! Each object of the schema is a table of parts under stable keys
//! ([`PartSet`]). Each arrow is a column mapping every live part of its
//! source to a live part of its target, and each attribute a column mapping
//! every live part of its object to an [`AttributeValue`]. A column declared
//! [`Indexing::Indexed`] keeps its inverse: for every value, the sorted keys of
//! the live parts that map to it, updated on every write. The inverse is
//! derived data; declaring it changes what the store maintains and proves,
//! never what it holds.
//!
//! Every live part has every arrow and every attribute of its table set, and
//! every set arrow reaches a live part: the reads below never meet a dangling
//! reference, and the edits in [`edit`] refuse, by name, anything that would
//! make one. A column slot of a dead part keeps its last value and is never
//! read: liveness gates every read.
//!
//! # Economy
//!
//! Columns are dense vectors indexed by key, so their memory follows each
//! table's counter, not its live count; a table that mints and deletes
//! without bound grows without bound. The ceiling is the record's own
//! answer: an explicit compaction that returns its renumbering, run where the
//! renumbering's hash rewrite is acceptable.

pub mod edit;
pub mod layout;
pub mod prove;
mod pull;

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;

use crate::error::Refusal;
use crate::error::StoreError;
use crate::manifest::StoreManifest;
use crate::manifest::StoreRoot;
use crate::parts::LiveParts;
use crate::parts::Liveness;
use crate::parts::PartCount;
use crate::parts::PartKey;
use crate::parts::PartSet;
use crate::parts::Slot;
use crate::schema::ArrowId;
use crate::schema::AttributeId;
use crate::schema::Indexing;
use crate::schema::Name;
use crate::schema::ObjectId;
use crate::schema::Path;
use crate::schema::Schema;
pub use crate::store::edit::Edit;

/// One attribute value: canonical bytes of the attribute's type, opaque to
/// the store.
///
/// The store compares values bytewise and never interprets them; that the
/// bytes are a valid value of the attribute's type is the consumer's codec's
/// obligation.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AttributeValue(Box<[u8]>);

impl From<&[u8]> for AttributeValue
{
    /// Copies bytes as a value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(Box::from(bytes))
    }
}

impl From<Vec<u8>> for AttributeValue
{
    /// Takes over bytes as a value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes.into_boxed_slice())
    }
}

impl AsRef<[u8]> for AttributeValue
{
    /// Borrows the value's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// The arrows and attributes a new part is added with.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Row
{
    /// Each arrow's target.
    arrows: Vec<(ArrowId, PartKey)>,
    /// Each attribute's value.
    values: Vec<(AttributeId, AttributeValue)>,
}

impl Row
{
    /// An empty row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            arrows: Vec::new(),
            values: Vec::new(),
        }
    }

    /// Sets an arrow's target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arrow(
        mut self,
        arrow: ArrowId,
        target: PartKey,
    ) -> Self
    {
        self.arrows.push((arrow, target));
        self
    }

    /// Sets an attribute's value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value<V>(
        mut self,
        attribute: AttributeId,
        value: V,
    ) -> Self
    where
        V: Into<AttributeValue>,
    {
        self.values.push((attribute, value.into()));
        self
    }
}

/// One arrow's column and, when declared, its inverse.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ArrowColumn
{
    /// Each source slot's target.
    targets: Vec<PartKey>,
    /// The inverse.
    index: ArrowIndex,
}

/// An arrow column's inverse.
#[derive(Clone, Debug, Eq, PartialEq)]
enum ArrowIndex
{
    /// The schema declares none.
    Undeclared,
    /// For each target slot, the sorted live sources mapping to it.
    Kept(Vec<Vec<PartKey>>),
}

/// One attribute's column and, when declared, its inverse.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ValueColumn
{
    /// Each part slot's value.
    values: Vec<AttributeValue>,
    /// The inverse.
    index: ValueIndex,
}

/// An attribute column's inverse.
#[derive(Clone, Debug, Eq, PartialEq)]
enum ValueIndex
{
    /// The schema declares none.
    Undeclared,
    /// For each value held, the sorted live parts holding it.
    Kept(BTreeMap<AttributeValue, Vec<PartKey>>),
}

/// Whether a table changed since its tree was last built.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Staleness
{
    /// The tree is the table's.
    Fresh,
    /// The table changed since.
    Stale,
}

/// The last committed state: one tree per table and the manifest naming
/// them.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Committed
{
    /// Each table's tree, in object order.
    trees: Box<[RecordTree]>,
    /// Whether each table changed since its tree was built.
    staleness: Box<[Staleness]>,
    /// The manifest over the trees.
    manifest: StoreManifest,
}

/// A store of one schema's parts over the record plane.
///
/// # Specification
/// - requires: construction through [`Store::new`], [`Store::open`] or
///   [`Store::pull_back`].
/// - ensures: outside an open [`Edit`], every live part has every arrow and
///   attribute of its table set, every set arrow reaches a live part of its
///   target, every equation holds at every live part of its object, and every
///   kept inverse lists exactly the live parts mapping to each value.
/// - provides: reads, edits, commits and proofs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the defect, equation and keyed fixtures drive every
///   edit and read the columns and inverses back exactly; reopening rebuilds
///   the same store from the block store and an independently built record set
///   agrees with the committed one.
/// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
/// - witness: `tests::equations::retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it`
/// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Store
{
    /// The schema.
    schema: Schema,
    /// The record plane's parameters every table tree is built under.
    params: TreeParams,
    /// Each object's parts.
    tables: Box<[PartSet]>,
    /// Each arrow's column.
    arrows: Box<[ArrowColumn]>,
    /// Each attribute's column.
    values: Box<[ValueColumn]>,
    /// The last commit.
    committed: Committed,
}

impl Store
{
    /// An empty store of a schema.
    ///
    /// # Specification
    /// - ensures: on success every table is empty with its counter at
    ///   [`PartKey::FIRST`], and [`Store::root`] names the empty store.
    /// - fails: [`StoreError::Records`] when the record plane does not support
    ///   `params`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`StoreError::Records`]: unsupported parameters.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a new store reads no part in any table, and two new
    ///   stores of one schema have one root while another schema's differs.
    /// - witness: `tests::proofs::an_empty_store_has_a_root_that_names_its_schema`
    #[inline]
    #[spec(
        captures: identity = schema.identity(),
        ensures: |ret| ret.as_ref().map_or(true, |store| store.manifest().schema() == identity),
    )]
    pub fn new(
        schema: Schema,
        params: TreeParams,
    ) -> Result<Self, StoreError>
    {
        params.ensure_supported()?;

        let tables = schema.objects().map(|_object| PartSet::new()).collect();
        let arrows = schema
            .arrows()
            .map(|arrow| {
                let index = match schema.arrow_at(arrow).map(crate::schema::Arrow::indexing) {
                    Ok(Indexing::Indexed) => ArrowIndex::Kept(Vec::new()),
                    Ok(Indexing::Unindexed) | Err(_) => ArrowIndex::Undeclared,
                };
                ArrowColumn {
                    targets: Vec::new(),
                    index,
                }
            })
            .collect();
        let values = schema
            .attributes()
            .map(|attribute| {
                let index = match schema
                    .attribute_at(attribute)
                    .map(crate::schema::Attribute::indexing)
                {
                    Ok(Indexing::Indexed) => ValueIndex::Kept(BTreeMap::new()),
                    Ok(Indexing::Unindexed) | Err(_) => ValueIndex::Undeclared,
                };
                ValueColumn {
                    values: Vec::new(),
                    index,
                }
            })
            .collect();

        let staleness: Box<[Staleness]> =
            schema.objects().map(|_object| Staleness::Fresh).collect();
        let empty = RecordTree::build(&[], params)?;
        let trees: Box<[RecordTree]> = schema.objects().map(|_object| empty.clone()).collect();
        let manifest = StoreManifest::over(
            &schema,
            params,
            trees.iter().map(|tree| (PartKey::FIRST, tree)),
        )?;

        Ok(Self {
            schema,
            params,
            tables,
            arrows,
            values,
            committed: Committed {
                trees,
                staleness,
                manifest,
            },
        })
    }

    /// The store's schema.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn schema(&self) -> &Schema
    {
        &self.schema
    }

    /// The parameters every table tree is built under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn params(&self) -> TreeParams
    {
        self.params
    }

    /// The manifest of the last commit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn manifest(&self) -> &StoreManifest
    {
        &self.committed.manifest
    }

    /// The root of the last commit: BLAKE3 of its manifest image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(&self) -> StoreRoot
    {
        self.committed.manifest.identity()
    }

    /// Whether a key names a live part of a table.
    ///
    /// # Specification
    /// - ensures: on success [`Liveness::Live`] exactly when the key was minted
    ///   in the table and not deleted since.
    /// - fails: [`Refusal::Schema`] for an object outside the schema.
    /// - panics: none.
    /// - executable: none — the answer is the table's bit; the edit witnesses
    ///   observe it across mints, deletes and rollbacks.
    ///
    /// # Errors
    /// [`Refusal::Schema`]: unknown object.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a deleted edge is dead and its neighbours live; an
    ///   abandoned edit's part is dead.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    /// - witness: `tests::equations::an_abandoned_edit_leaves_no_part_and_no_reused_key`
    #[inline]
    pub fn liveness(
        &self,
        object: ObjectId,
        part: PartKey,
    ) -> Result<Liveness, Refusal>
    {
        let table = self.table(object)?;
        Ok(table.liveness(part))
    }

    /// The live parts of a table, ascending by key.
    ///
    /// # Specification
    /// - ensures: on success yields each live key of the table once.
    /// - fails: [`Refusal::Schema`] for an object outside the schema.
    /// - panics: none.
    /// - executable: none — the iterator is lazy; the keyed round trip compares
    ///   its whole sequence with the fixture's.
    ///
    /// # Errors
    /// [`Refusal::Schema`]: unknown object.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every table of the reopened keyed fixture lists the
    ///   fixture's keys.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    pub fn parts(
        &self,
        object: ObjectId,
    ) -> Result<LiveParts<'_>, Refusal>
    {
        let table = self.table(object)?;
        Ok(table.iter())
    }

    /// How many parts of a table are live.
    ///
    /// # Specification
    /// - ensures: on success the number of keys [`Store::parts`] yields.
    /// - fails: [`Refusal::Schema`] for an object outside the schema.
    /// - panics: none.
    /// - executable: none — the count is maintained, not computed; the defect
    ///   witness compares it after each edit.
    ///
    /// # Errors
    /// [`Refusal::Schema`]: unknown object.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — counts after adds, a refused delete and an accepted
    ///   one.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    pub fn live_count(
        &self,
        object: ObjectId,
    ) -> Result<PartCount, Refusal>
    {
        let table = self.table(object)?;
        Ok(table.live())
    }

    /// The part an arrow takes a live part to.
    ///
    /// # Specification
    /// - ensures: on success the arrow's value at the part.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema, and
    ///   [`Refusal::NotLive`] naming the source table and key when the part is
    ///   not live.
    /// - panics: none.
    /// - executable: none — the answer is the column's cell; the fixtures read
    ///   every cell back against what they wrote.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the reopened keyed fixture reads every arrow of every
    ///   part back as written; a deleted part's arrow is refused.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    pub fn target(
        &self,
        arrow: ArrowId,
        part: PartKey,
    ) -> Result<PartKey, Refusal>
    {
        let source = self.schema.arrow_at(arrow)?.source();
        self.ensure_live(source, part)?;
        self.cell(arrow, part)
    }

    /// The value an attribute gives a live part.
    ///
    /// # Specification
    /// - ensures: on success the attribute's value at the part.
    /// - fails: [`Refusal::Schema`] for an attribute outside the schema, and
    ///   [`Refusal::NotLive`] naming the table and key when the part is not
    ///   live.
    /// - panics: none.
    /// - executable: none — the answer is the column's cell; the fixtures read
    ///   every cell back against what they wrote.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the reopened keyed fixture reads every attribute of
    ///   every part back as written.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    pub fn value(
        &self,
        attribute: AttributeId,
        part: PartKey,
    ) -> Result<&AttributeValue, Refusal>
    {
        let object = self.schema.attribute_at(attribute)?.object();
        self.ensure_live(object, part)?;
        let column = self.value_column(attribute)?;
        let slot = self.slot(object, part)?;
        column
            .values
            .get(usize::from(slot))
            .ok_or_else(|| self.not_live(object, part))
    }

    /// The live parts an indexed arrow takes to one live part, ascending.
    ///
    /// # Specification
    /// - ensures: on success exactly the live sources whose arrow reaches the
    ///   target, each once, ascending; empty when none does.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema,
    ///   [`Refusal::NotIndexed`] naming an arrow whose inverse is not kept, and
    ///   [`Refusal::NotLive`] naming the target table and key when the target
    ///   is not live.
    /// - panics: none.
    /// - executable: none — a predicate comparing with a scan would walk the
    ///   column the index exists to avoid; the scan is the witnesses'
    ///   independent reference.
    /// - intension: a constant number of lookups; the slice is borrowed, not
    ///   copied.
    ///
    /// # Errors
    /// [`Refusal::Schema`], [`Refusal::NotIndexed`] or [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — after every edit of the equation and keyed fixtures
    ///   the preimage of every live target equals a scan of the column; an
    ///   unindexed arrow is refused.
    /// - witness: `tests::equations::every_inverse_agrees_with_a_scan_after_every_edit`
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    #[cfg_attr(feature = "hotpath", hotpath::measure(impl_type = "Store"))]
    pub fn preimage(
        &self,
        arrow: ArrowId,
        target: PartKey,
    ) -> Result<&[PartKey], Refusal>
    {
        let spec = self.schema.arrow_at(arrow)?;
        let column = self.arrow_column(arrow)?;
        let ArrowIndex::Kept(ref index) = column.index
        else {
            return Err(Refusal::NotIndexed {
                field: spec.name().clone(),
            });
        };
        self.ensure_live(spec.target(), target)?;
        let slot = self.slot(spec.target(), target)?;
        Ok(index.get(usize::from(slot)).map_or(&[], |sources| sources))
    }

    /// The live parts an indexed attribute gives one value, ascending.
    ///
    /// # Specification
    /// - ensures: on success exactly the live parts holding the value, each
    ///   once, ascending; empty when none does.
    /// - fails: [`Refusal::Schema`] for an attribute outside the schema, and
    ///   [`Refusal::NotIndexed`] naming an attribute whose inverse is not kept.
    /// - panics: none.
    /// - executable: none — a predicate comparing with a scan would walk the
    ///   column the index exists to avoid; the scan is the witnesses'
    ///   independent reference.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotIndexed`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the keyed fixture finds tasks by name and moves by
    ///   subject digest, and every value's preimage equals a scan.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    pub fn value_preimage(
        &self,
        attribute: AttributeId,
        value: &AttributeValue,
    ) -> Result<&[PartKey], Refusal>
    {
        let spec = self.schema.attribute_at(attribute)?;
        let column = self.value_column(attribute)?;
        let ValueIndex::Kept(ref index) = column.index
        else {
            return Err(Refusal::NotIndexed {
                field: spec.name().clone(),
            });
        };
        Ok(index.get(value).map_or(&[], |parts| parts))
    }

    /// Checks every equation at every live part.
    ///
    /// # Specification
    /// - ensures: success exactly when, for every equation and every live part
    ///   of its object, both sides reach the same part.
    /// - fails: [`Refusal::EquationViolated`] for the first violation in
    ///   equation then key order.
    /// - panics: none.
    /// - executable: none — the check is itself the whole-store walk; its
    ///   independent observation is the per-edit check refusing the same
    ///   violation.
    /// - intension: one path walk per equation per live part of its object.
    ///
    /// # Errors
    /// [`Refusal::EquationViolated`]: some part violates some equation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pulled-back store, built without any check, passes
    ///   the audit, and a reopened store with a doctored arrow fails it by
    ///   name.
    /// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    pub fn audit(&self) -> Result<(), Refusal>
    {
        for equation in self.schema.equations() {
            let start = self.schema.equation_at(equation)?.left().start();
            let table = self.table(start)?;
            for part in table.iter() {
                self.check(equation, part)?;
            }
        }
        Ok(())
    }

    /// Checks one equation at one part.
    ///
    /// # Specification
    /// - requires: the part is live in the equation's object and every arrow on
    ///   both paths is set along the way.
    /// - ensures: success exactly when both sides reach the same part.
    /// - fails: [`Refusal::EquationViolated`] naming the equation, the object,
    ///   the part and both ends.
    /// - panics: none.
    /// - executable: none — the answer is two path walks; the witnesses compare
    ///   against hand-computed ends.
    ///
    /// # Errors
    /// [`Refusal::EquationViolated`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a loop whose source is another vertex is refused with
    ///   both ends; the same loop at its own vertex is admitted.
    /// - witness: `tests::equations::a_loop_that_leaves_its_vertex_is_refused_by_equation`
    #[inline]
    fn check(
        &self,
        equation: crate::schema::EquationId,
        part: PartKey,
    ) -> Result<(), Refusal>
    {
        let spec = self.schema.equation_at(equation)?;
        let left = self.follow(spec.left(), part)?;
        let right = self.follow(spec.right(), part)?;
        if left == right {
            return Ok(());
        }
        let object = self.schema.object_name(spec.left().start())?;
        Err(Refusal::EquationViolated {
            equation: spec.name().clone(),
            object: object.clone(),
            part,
            left,
            right,
        })
    }

    /// The part a path reaches from a part.
    ///
    /// # Specification
    /// - requires: the part is live in the path's start and every arrow on the
    ///   path is set along the way.
    /// - ensures: on success the composite of the path's arrows applied in
    ///   order, the part itself for the identity path.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema.
    /// - panics: none.
    /// - executable: none — the answer is the composite itself; the witnesses
    ///   compare it with hand-computed ends.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the loop equation's identity side and two-arrow side
    ///   reach the hand-computed vertices.
    /// - witness: `tests::equations::a_loop_that_leaves_its_vertex_is_refused_by_equation`
    #[inline]
    fn follow(
        &self,
        path: &Path,
        part: PartKey,
    ) -> Result<PartKey, Refusal>
    {
        let mut at = part;
        for arrow in path.arrows() {
            at = self.cell(*arrow, at)?;
        }
        Ok(at)
    }

    /// The live sources whose set arrow reaches a target, through the
    /// inverse when kept and by scanning the column otherwise.
    ///
    /// # Specification
    /// - ensures: on success exactly the live parts of the arrow's source whose
    ///   arrow is set, not listed in `unset`, and reaches `target`, ascending.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema.
    /// - panics: none.
    /// - executable: none — the scan arm is the reference the indexed arm is
    ///   checked against, so a predicate would only repeat it.
    /// - intension: an indexed arrow costs one lookup and a copy of the
    ///   preimage; an unindexed one scans every live source.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the defect fixture refuses a delete through an
    ///   unindexed arrow and an indexed one alike, and the equation fixture's
    ///   recheck reaches parts through both arms.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    /// - witness: `tests::defect::an_unindexed_arrow_still_refuses_the_delete`
    /// - witness: `tests::equations::retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it`
    #[inline]
    fn referrers(
        &self,
        arrow: ArrowId,
        target: PartKey,
        unset: &BTreeSet<(ArrowId, PartKey)>,
    ) -> Result<Vec<PartKey>, Refusal>
    {
        let source = self.schema.arrow_at(arrow)?.source();
        let column = self.arrow_column(arrow)?;
        if let ArrowIndex::Kept(ref index) = column.index {
            let Ok(slot) = target.slot()
            else {
                return Ok(Vec::new());
            };
            return Ok(index.get(usize::from(slot)).cloned().unwrap_or_default());
        }

        // economy: an unindexed arrow is scanned whole; declaring its index
        // makes this a lookup.
        let table = self.table(source)?;
        let mut found = Vec::new();
        for part in table.iter() {
            if unset.contains(&(arrow, part)) {
                continue;
            }
            if self.cell(arrow, part)? == target {
                found.push(part);
            }
        }
        Ok(found)
    }

    /// An arrow's cell at a part, read without a liveness check.
    ///
    /// # Specification
    /// - requires: the part was minted in the arrow's source.
    /// - ensures: on success the cell's stored target.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema, and
    ///   [`Refusal::NotLive`] for a slot the column does not hold.
    /// - panics: none.
    /// - executable: none — the answer is the cell itself.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every arrow read of the keyed round trip goes through
    ///   this cell read.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    fn cell(
        &self,
        arrow: ArrowId,
        part: PartKey,
    ) -> Result<PartKey, Refusal>
    {
        let source = self.schema.arrow_at(arrow)?.source();
        let column = self.arrow_column(arrow)?;
        let slot = self.slot(source, part)?;
        column
            .targets
            .get(usize::from(slot))
            .copied()
            .ok_or_else(|| self.not_live(source, part))
    }

    /// Refuses a part that is not live.
    ///
    /// # Specification
    /// - ensures: success exactly when the part is live in the table.
    /// - fails: [`Refusal::Schema`] for an unknown object, and
    ///   [`Refusal::NotLive`] naming the table and key.
    /// - panics: none.
    /// - executable: none — the answer is the table's bit.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reading a deleted edge's arrow is refused by the edge
    ///   table's name and the key.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    fn ensure_live(
        &self,
        object: ObjectId,
        part: PartKey,
    ) -> Result<(), Refusal>
    {
        match self.table(object)?.liveness(part) {
            Liveness::Live => Ok(()),
            Liveness::Dead => Err(self.not_live(object, part)),
        }
    }

    /// The refusal naming a part that is not live.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn not_live(
        &self,
        object: ObjectId,
        part: PartKey,
    ) -> Refusal
    {
        match self.schema.object_name(object) {
            Ok(name) => Refusal::NotLive {
                object: name.clone(),
                part,
            },
            Err(error) => Refusal::Schema(error),
        }
    }

    /// A part's column slot.
    ///
    /// # Specification
    /// - ensures: on success the slot the key's cells occupy.
    /// - fails: [`Refusal::NotLive`] for a key beyond what this target can
    ///   index.
    /// - panics: none.
    /// - executable: none — the slot is the key's value.
    ///
    /// # Errors
    /// [`Refusal::NotLive`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every read of the keyed round trip resolves its slot
    ///   here.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    fn slot(
        &self,
        object: ObjectId,
        part: PartKey,
    ) -> Result<Slot, Refusal>
    {
        part.slot()
            .map_err(|_unaddressable| self.not_live(object, part))
    }

    /// One table's parts.
    ///
    /// # Specification
    /// - ensures: on success the table at the object's ordinal.
    /// - fails: [`Refusal::Schema`] for an object outside the schema.
    /// - panics: none.
    /// - executable: none — the answer is the table itself.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an object ordinal past the schema is refused.
    /// - witness: `tests::schema::an_ordinal_out_of_range_is_refused`
    #[inline]
    fn table(
        &self,
        object: ObjectId,
    ) -> Result<&PartSet, Refusal>
    {
        self.schema.object_name(object)?;
        self.tables
            .get(usize::from(object))
            .ok_or_else(|| self.not_live(object, PartKey::FIRST))
    }

    /// One arrow's column.
    ///
    /// # Specification
    /// - ensures: on success the column at the arrow's ordinal.
    /// - fails: [`Refusal::Schema`] for an arrow outside the schema.
    /// - panics: none.
    /// - executable: none — the answer is the column itself.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arrow ordinal past the schema is refused.
    /// - witness: `tests::schema::an_ordinal_out_of_range_is_refused`
    #[inline]
    fn arrow_column(
        &self,
        arrow: ArrowId,
    ) -> Result<&ArrowColumn, Refusal>
    {
        let spec = self.schema.arrow_at(arrow)?;
        self.arrows
            .get(usize::from(arrow))
            .ok_or_else(|| Refusal::NotIndexed {
                field: spec.name().clone(),
            })
    }

    /// One attribute's column.
    ///
    /// # Specification
    /// - ensures: on success the column at the attribute's ordinal.
    /// - fails: [`Refusal::Schema`] for an attribute outside the schema.
    /// - panics: none.
    /// - executable: none — the answer is the column itself.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an attribute ordinal past the schema is refused.
    /// - witness: `tests::schema::an_ordinal_out_of_range_is_refused`
    #[inline]
    fn value_column(
        &self,
        attribute: AttributeId,
    ) -> Result<&ValueColumn, Refusal>
    {
        let spec = self.schema.attribute_at(attribute)?;
        self.values
            .get(usize::from(attribute))
            .ok_or_else(|| Refusal::NotIndexed {
                field: spec.name().clone(),
            })
    }

    /// Marks a table changed since its tree was built.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn touch(
        &mut self,
        object: ObjectId,
    )
    {
        if let Some(staleness) = self.committed.staleness.get_mut(usize::from(object)) {
            *staleness = Staleness::Stale;
        }
    }

    /// The object's name, for a refusal.
    ///
    /// # Specification
    /// - ensures: on success a copy of the object's name.
    /// - fails: [`Refusal::Schema`] for an object outside the schema.
    /// - panics: none.
    /// - executable: none — the answer is the schema's name.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusals name their tables; the defect witness
    ///   asserts the name.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    fn object_name(
        &self,
        object: ObjectId,
    ) -> Result<Name, Refusal>
    {
        Ok(self.schema.object_name(object)?.clone())
    }
}

/// Grows a column so a slot exists, filling with a placeholder.
///
/// # Specification
/// - ensures: the column holds the slot; existing cells are unchanged.
/// - panics: none.
/// - executable: none — `T` carries no bound a predicate could compare with.
///
/// # Adequacy
/// - hypothesis: L2 — every add in the fixtures writes through a slot this
///   grows, and the round trip reads each back.
/// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
#[inline]
fn ensure_slot<T>(
    column: &mut Vec<T>,
    slot: Slot,
) where
    T: Default + Clone,
{
    let wanted = usize::from(slot).saturating_add(1_usize);
    if column.len() < wanted {
        column.resize(wanted, T::default());
    }
}

/// Inserts a key into a sorted list, once.
///
/// # Specification
/// - ensures: the list is sorted and holds the key once.
/// - panics: none.
/// - executable: none — the sortedness is the index's invariant, compared whole
///   against a scan by the witness.
///
/// # Adequacy
/// - hypothesis: L2 — every inverse equals a scan after every edit.
/// - witness: `tests::equations::every_inverse_agrees_with_a_scan_after_every_edit`
#[inline]
fn insert_sorted(
    list: &mut Vec<PartKey>,
    key: PartKey,
)
{
    if let Err(position) = list.binary_search(&key) {
        list.insert(position, key);
    }
}

/// Removes a key from a sorted list, when present.
///
/// # Specification
/// - ensures: the list is sorted and does not hold the key.
/// - panics: none.
/// - executable: none — the sortedness is the index's invariant, compared whole
///   against a scan by the witness.
///
/// # Adequacy
/// - hypothesis: L2 — every inverse equals a scan after every edit.
/// - witness: `tests::equations::every_inverse_agrees_with_a_scan_after_every_edit`
#[inline]
fn remove_sorted(
    list: &mut Vec<PartKey>,
    key: PartKey,
)
{
    if let Ok(position) = list.binary_search(&key) {
        list.remove(position);
    }
}

impl ArrowColumn
{
    /// Records that a source now maps to a target in the inverse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_insert(
        &mut self,
        target: PartKey,
        source: PartKey,
    )
    {
        if let ArrowIndex::Kept(ref mut index) = self.index
            && let Ok(slot) = target.slot()
        {
            ensure_slot(index, slot);
            if let Some(list) = index.get_mut(usize::from(slot)) {
                insert_sorted(list, source);
            }
        }
    }

    /// Records that a source no longer maps to a target in the inverse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_remove(
        &mut self,
        target: PartKey,
        source: PartKey,
    )
    {
        if let ArrowIndex::Kept(ref mut index) = self.index
            && let Ok(slot) = target.slot()
            && let Some(list) = index.get_mut(usize::from(slot))
        {
            remove_sorted(list, source);
        }
    }
}

impl ValueColumn
{
    /// Records that a part now holds a value in the inverse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_insert(
        &mut self,
        value: &AttributeValue,
        part: PartKey,
    )
    {
        if let ValueIndex::Kept(ref mut index) = self.index {
            insert_sorted(index.entry(value.clone()).or_default(), part);
        }
    }

    /// Records that a part no longer holds a value in the inverse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_remove(
        &mut self,
        value: &AttributeValue,
        part: PartKey,
    )
    {
        if let ValueIndex::Kept(ref mut index) = self.index
            && let Some(list) = index.get_mut(value)
        {
            remove_sorted(list, part);
            if list.is_empty() {
                index.remove(value);
            }
        }
    }

    /// Lists a part in the inverse under the value at its slot.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_insert_slot(
        &mut self,
        slot: Slot,
        part: PartKey,
    )
    {
        if let Some(value) = self.values.get(usize::from(slot))
            && let ValueIndex::Kept(ref mut index) = self.index
        {
            if let Some(list) = index.get_mut(value) {
                insert_sorted(list, part);
            }
            else {
                let _absent = index.insert(value.clone(), alloc::vec![part]);
            }
        }
    }

    /// Takes a part out of the inverse's list under the value at its slot.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_remove_slot(
        &mut self,
        slot: Slot,
        part: PartKey,
    )
    {
        if let Some(value) = self.values.get(usize::from(slot))
            && let ValueIndex::Kept(ref mut index) = self.index
            && let Some(list) = index.get_mut(value)
        {
            remove_sorted(list, part);
            if list.is_empty() {
                let _emptied = index.remove(value);
            }
        }
    }
}
