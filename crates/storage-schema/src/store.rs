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
//! make one. A column cell of a dead part keeps its last value and is never
//! read: liveness gates every read.
//!
//! A store mints its parts as one [`Writer`], in that writer's region of each
//! table. [`Store::glue`] takes another writer's store into this one by a union
//! of their regions. A region that both stores hold must agree in both, so
//! the glue renumbers no part and changes no cell.
//!
//! # Economy
//!
//! Each column holds one dense run for each writer, indexed by offset, so its
//! memory follows each writer's counter, not the live count; a writer that
//! mints and deletes without bound grows its runs without bound. The ceiling
//! is the record's own answer: an explicit compaction that returns its
//! renumbering, run where the renumbering's hash rewrite is acceptable.

pub mod edit;
pub mod layout;
pub mod prove;
mod pull;

use alloc::borrow::Cow;
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
use crate::parts::Agreement;
use crate::parts::Holding;
use crate::parts::LiveParts;
use crate::parts::Liveness;
use crate::parts::PartCount;
use crate::parts::PartKey;
use crate::parts::PartSet;
use crate::parts::Region;
use crate::parts::Segments;
use crate::parts::Writer;
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
    /// Each source part's target.
    targets: Segments<PartKey>,
    /// The inverse.
    index: ArrowIndex,
}

/// An arrow column's inverse.
#[derive(Clone, Debug, Eq, PartialEq)]
enum ArrowIndex
{
    /// The schema declares none.
    Undeclared,
    /// For each target part, the sorted live sources mapping to it.
    Kept(Segments<Vec<PartKey>>),
}

/// One attribute's column and, when declared, its inverse.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ValueColumn
{
    /// Each part's value.
    values: Segments<AttributeValue>,
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
    /// The writer whose region this store mints in.
    writer: Writer,
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
    /// An empty store of a schema, minting as `writer`.
    ///
    /// # Specification
    /// - ensures: on success every table is empty and holds no region, the
    ///   store mints as `writer`, and [`Store::root`] names the empty store.
    ///   The root does not depend on `writer`.
    /// - fails: [`StoreError::Records`] when the record plane does not support
    ///   `params`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`StoreError::Records`]: unsupported parameters.
    ///
    /// # Cost
    /// - allocation: one part set, column and empty tree for each object, arrow
    ///   and attribute of the schema, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a new store reads no part in any table, and two new
    ///   stores of one schema have one root while another schema's differs.
    /// - witness: `tests::proofs::an_empty_store_has_a_root_that_names_its_schema`
    #[inline]
    #[spec(
        captures: identity = schema.identity(),
        ensures: |ret| ret.as_ref().map_or(true, |store| store.manifest().schema() == identity && store.writer == writer),
    )]
    pub fn new(
        schema: Schema,
        params: TreeParams,
        writer: Writer,
    ) -> Result<Self, StoreError>
    {
        params.ensure_supported()?;

        let tables = schema.objects().map(|_object| PartSet::new()).collect();
        let arrows = schema
            .arrows()
            .map(|arrow| {
                let index = match schema.arrow_at(arrow).map(crate::schema::Arrow::indexing) {
                    Ok(Indexing::Indexed) => ArrowIndex::Kept(Segments::new()),
                    Ok(Indexing::Unindexed) | Err(_) => ArrowIndex::Undeclared,
                };
                ArrowColumn {
                    targets: Segments::new(),
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
                    values: Segments::new(),
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
            trees.iter().map(|tree| (core::iter::empty(), tree)),
        )?;

        Ok(Self {
            schema,
            params,
            writer,
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

    /// The writer whose region this store mints in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn writer(&self) -> Writer
    {
        self.writer
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
        column
            .values
            .cell(part)
            .map_err(|_unaddressable| self.not_live(object, part))
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
    /// # Cost
    /// - allocation: the arrow's name in a refusal, error path
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
        Ok(index.cell(target).map_or(&[], |sources| sources))
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

    /// Takes `other`, a store of the same schema, into this one by a union
    /// of their regions.
    ///
    /// # Specification
    /// - ensures: on success each table holds each region that it held and each
    ///   region of `other`. A region of a writer that this store has not seen
    ///   comes with its parts, its cells and its inverse entries, under the
    ///   keys that `other` minted. No key is renumbered, and this store's
    ///   writer and its last commit stay. A table that takes a region is stale.
    /// - fails: [`StoreError::SchemaMismatch`] and
    ///   [`StoreError::ProfileMismatch`] when `other` is of another schema or
    ///   other boundary parameters. [`StoreError::Refused`] carrying
    ///   [`Refusal::Disagreed`] names the table and the writer of a region that
    ///   both stores hold apart: another counter, other live parts, or another
    ///   cell of a live part. A refused glue changes nothing.
    /// - panics: none.
    /// - executable: none — the union is observed through each read of the
    ///   glued store; the witnesses compare each part with its source.
    /// - intension: one comparison of each shared region's parts and cells,
    ///   then one copy of each run that a new region brings.
    ///
    /// # Errors
    /// [`StoreError::SchemaMismatch`], [`StoreError::ProfileMismatch`] or
    /// [`StoreError::Refused`] with [`Refusal::Disagreed`].
    ///
    /// # Cost
    /// - allocation: the copies of the new regions, their runs and their
    ///   inverse entries, growth within the parts of the glued stores
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — two writers' stores glue to the union of their
    ///   parts in either order, to one root, with every cell and inverse read
    ///   back; two writers that share a base glue over it; an edit of the
    ///   shared base by one of them refuses the glue by name and changes
    ///   nothing; another schema is refused.
    /// - witness: `tests::glue::two_writers_glue_to_the_union_of_their_parts`
    /// - witness: `tests::glue::two_writers_that_share_a_base_glue_over_it`
    /// - witness: `tests::glue::two_stores_that_disagree_on_a_shared_region_do_not_glue`
    #[inline]
    pub fn glue(
        &mut self,
        other: &Self,
    ) -> Result<(), StoreError>
    {
        if other.schema.identity() != self.schema.identity() {
            return Err(StoreError::SchemaMismatch {
                expected: self.schema.identity(),
                found: other.schema.identity(),
            });
        }
        if other.params.boundary_commitment() != self.params.boundary_commitment() {
            return Err(StoreError::ProfileMismatch);
        }
        for object in self.schema.objects() {
            let ours = self.table(object)?;
            for (writer, region) in other.table(object)?.regions() {
                if let Holding::Held(held) = ours.holding(writer) {
                    self.agree(other, object, writer, (held, region))?;
                }
            }
        }
        for object in other.schema.objects() {
            for (writer, region) in other.table(object)?.regions() {
                if matches!(self.table(object)?.holding(writer), Holding::Unseen) {
                    self.adopt(other, object, writer, region)?;
                }
            }
        }
        Ok(())
    }

    /// Refuses two copies of one writer's region of a table that differ.
    ///
    /// # Specification
    /// - requires: `other` is of this store's schema, and both regions are
    ///   `writer`'s region of `object`, `ours` from this store and `theirs`
    ///   from `other`.
    /// - ensures: success exactly when the two copies have one counter and one
    ///   set of live parts, and each arrow and attribute of each live part
    ///   holds one cell in both stores.
    /// - fails: [`Refusal::Disagreed`] naming the table and the writer.
    /// - panics: none.
    /// - executable: none — the answer is the comparison itself; the glue
    ///   witnesses observe both outcomes.
    ///
    /// # Errors
    /// [`Refusal::Disagreed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shared base agrees, and a value changed in one copy
    ///   of it is refused.
    /// - witness: `tests::glue::two_writers_that_share_a_base_glue_over_it`
    /// - witness: `tests::glue::two_stores_that_disagree_on_a_shared_region_do_not_glue`
    #[inline]
    fn agree(
        &self,
        other: &Self,
        object: ObjectId,
        writer: Writer,
        (ours, theirs): (&Region, &Region),
    ) -> Result<(), Refusal>
    {
        let disagreed = || match self.object_name(object) {
            Ok(name) => Refusal::Disagreed {
                object: name,
                writer,
            },
            Err(refusal) => refusal,
        };
        if ours.agreement(theirs) == Agreement::Differs {
            return Err(disagreed());
        }
        for part in theirs.parts(writer) {
            for &arrow in self.schema.outgoing(object) {
                let mine = self.cell(arrow, part)?;
                let other_target = other.cell(arrow, part)?;
                if mine != other_target {
                    return Err(disagreed());
                }
            }
            for &attribute in self.schema.fields(object) {
                let mine = self.value_column(attribute)?.values.cell(part);
                let other_value = other.value_column(attribute)?.values.cell(part);
                if mine != other_value {
                    return Err(disagreed());
                }
            }
        }
        Ok(())
    }

    /// Takes `other`'s region of a writer that this store has not seen, with
    /// its cells and its inverse entries.
    ///
    /// # Specification
    /// - requires: `other` is of this store's schema, `region` is its region of
    ///   `writer` in `object`, and this store holds no region of `writer` in
    ///   `object`.
    /// - ensures: on success the table holds the region; each column of the
    ///   table holds `other`'s run of the writer; each kept inverse lists the
    ///   region's live parts under their cells; the table is stale.
    /// - fails: [`Refusal::Schema`] for an arrow or attribute outside the
    ///   schema, and [`Refusal::NotLive`] for a live part of `other` with no
    ///   cell, which a store outside an edit never holds.
    /// - panics: none.
    /// - executable: none — the region and the runs are copied whole; the glue
    ///   witness reads each cell and each inverse back.
    ///
    /// # Errors
    /// [`Refusal::Schema`] or [`Refusal::NotLive`].
    ///
    /// # Cost
    /// - allocation: the copies of the region, its runs and its inverse
    ///   entries, growth within the parts of the glued stores
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every cell and inverse of the glued store equals the
    ///   source store's for each part.
    /// - witness: `tests::glue::two_writers_glue_to_the_union_of_their_parts`
    #[inline]
    fn adopt(
        &mut self,
        other: &Self,
        object: ObjectId,
        writer: Writer,
        region: &Region,
    ) -> Result<(), Refusal>
    {
        if let Some(table) = self.tables.get_mut(usize::from(object)) {
            table.adopt(writer, region);
        }
        for &arrow in other.schema.outgoing(object) {
            let theirs = other.arrow_column(arrow)?;
            if let Some(column) = self.arrows.get_mut(usize::from(arrow)) {
                column.targets.adopt(&theirs.targets, writer);
            }
        }
        for &attribute in other.schema.fields(object) {
            let theirs = other.value_column(attribute)?;
            if let Some(column) = self.values.get_mut(usize::from(attribute)) {
                column.values.adopt(&theirs.values, writer);
            }
        }
        for part in region.parts(writer) {
            for &arrow in other.schema.outgoing(object) {
                let target = other.cell(arrow, part)?;
                if let Some(column) = self.arrows.get_mut(usize::from(arrow)) {
                    column.index_insert(target, part);
                }
            }
            for &attribute in other.schema.fields(object) {
                if let Some(column) = self.values.get_mut(usize::from(attribute)) {
                    column.index_insert_slot(part);
                }
            }
        }
        self.touch(object);
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
    /// - intension: an indexed arrow costs one lookup and borrows the preimage;
    ///   an unindexed one scans every live source.
    ///
    /// # Errors
    /// [`Refusal::Schema`].
    ///
    /// # Cost
    /// - allocation: the referrers of an unindexed arrow, growth within the
    ///   source table's live parts
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
    ) -> Result<Cow<'_, [PartKey]>, Refusal>
    {
        let source = self.schema.arrow_at(arrow)?.source();
        let column = self.arrow_column(arrow)?;
        if let ArrowIndex::Kept(ref index) = column.index {
            return Ok(Cow::Borrowed(index.cell(target).map_or(&[], Vec::as_slice)));
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
        Ok(Cow::Owned(found))
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
        column
            .targets
            .cell(part)
            .copied()
            .map_err(|_unaddressable| self.not_live(source, part))
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
            .ok_or_else(|| self.not_live(object, PartKey::default()))
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
    /// # Cost
    /// - allocation: the arrow's name in a refusal, error path
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
    /// # Cost
    /// - allocation: the attribute's name in a refusal, error path
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
            && let Ok(list) = index.ensure(target)
        {
            insert_sorted(list, source);
        }
    }

    /// Removes a source's entry under a target from the inverse.
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
            && let Ok(list) = index.cell_mut(target)
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

    /// Removes a part's entry under a value from the inverse.
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

    /// Lists a part in the inverse under the value of its cell.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: a new value's entry in the inverse, growth within the
    ///   attribute's values
    #[inline]
    fn index_insert_slot(
        &mut self,
        part: PartKey,
    )
    {
        if let Ok(value) = self.values.cell(part)
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

    /// Takes a part out of the inverse's list under the value of its cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_remove_slot(
        &mut self,
        part: PartKey,
    )
    {
        if let Ok(value) = self.values.cell(part)
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
