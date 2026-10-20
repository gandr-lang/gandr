//! How a table lies on the record plane, and the commit and reopen paths.
//!
//! # The records of one table
//!
//! Every table is one record tree. Its keys fall into five families, each
//! opening with a family byte; integers in keys are big-endian at a fixed
//! width so byte order is numeric order, and integers in values are
//! little-endian like every other committed integer:
//!
//! | Key | Value | Holds |
//! | --- | ----- | ----- |
//! | `0x00 ‖ part` | empty | the part is live |
//! | `0x01 ‖ arrow ‖ part` | `u64le` target | the arrow's cell |
//! | `0x02 ‖ attribute ‖ part` | the value's bytes | the attribute's cell |
//! | `0x03 ‖ arrow ‖ target ‖ part` | empty | the arrow's kept inverse |
//! | `0x04 ‖ attribute ‖ u32 length ‖ value ‖ part` | empty | the attribute's kept inverse |
//!
//! `part` and `target` are `u64` keys and `arrow` and `attribute` `u32`
//! ordinals of columns leaving this table. A part's membership is one record;
//! an arrow's value one record; a kept inverse's preimage of one value is the
//! contiguous run under `0x03 ‖ arrow ‖ target`, or under
//! `0x04 ‖ attribute ‖ length ‖ value`, so the record plane's range proof
//! proves it complete. The length prefix keeps one value's run from
//! continuing into a longer value that extends it.
//!
//! **Choice.** One tree per table, the columns as key families inside it.
//! **Alternatives.** A tree per column multiplies the roots a manifest binds
//! and a proof carries for no new question; a row per part, every column in
//! one value, makes an arrow's proof carry the whole row and the inverse a
//! second structure. **Reversal.** A table whose one column dominates its
//! edits, where splitting it out would save rebuilding the rest.
//!
//! # Reopening
//!
//! [`Store::open`] loads each table's records through the block store's
//! verified load, rebuilds the tree and refuses one whose root node or record
//! count is not the manifest's. It reads the parts and cells, recomputes the
//! inverses, and refuses records that are not exactly the records this store
//! would write for what they hold. Then it refuses an arrow that reaches a
//! part that is not live, and an equation that fails at any part: a reopened
//! store meets the invariant every edit keeps, whoever wrote its blocks.

use alloc::vec::Vec;

use anodized::spec;
use gandr_storage_records::BlockStore;
use gandr_storage_records::DecodeWork;
use gandr_storage_records::DecodedNode;
use gandr_storage_records::NodeHash;
use gandr_storage_records::OwnedRecordKey;
use gandr_storage_records::Record;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;
use gandr_storage_records::decode_node;

use crate::error::LayoutFault;
use crate::error::StoreError;
use crate::manifest::StoreManifest;
use crate::manifest::StoreRoot;
use crate::parts::Liveness;
use crate::parts::PartKey;
use crate::parts::PartSet;
use crate::schema::ArrowId;
use crate::schema::AttributeId;
use crate::schema::ObjectId;
use crate::schema::Ordinal;
use crate::schema::Schema;
use crate::store::ArrowIndex;
use crate::store::AttributeValue;
use crate::store::Staleness;
use crate::store::Store;
use crate::store::ValueIndex;
use crate::store::ensure_slot;

/// The family of a part's membership record.
pub(crate) const PART: Family = Family(0x00_u8);
/// The family of an arrow cell.
pub(crate) const ARROW: Family = Family(0x01_u8);
/// The family of an attribute cell.
pub(crate) const VALUE: Family = Family(0x02_u8);
/// The family of an arrow's kept inverse.
pub(crate) const ARROW_INDEX: Family = Family(0x03_u8);
/// The family of an attribute's kept inverse.
pub(crate) const VALUE_INDEX: Family = Family(0x04_u8);

/// A key being written.
#[repr(transparent)]
pub(crate) struct KeyWriter(Vec<u8>);

impl KeyWriter
{
    /// A key opening with a family byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn family(family: Family) -> Self
    {
        let mut bytes = Vec::with_capacity(32_usize);
        bytes.push(family.0);
        Self(bytes)
    }

    /// Appends a part key, eight bytes big-endian.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn part(
        mut self,
        part: PartKey,
    ) -> Self
    {
        let mut bytes = u64::from(part).to_le_bytes();
        bytes.reverse();
        self.0.extend_from_slice(&bytes);
        self
    }

    /// Appends a column ordinal, four bytes big-endian.
    ///
    /// # Specification
    /// - ensures: on success four big-endian bytes of the ordinal are appended.
    /// - fails: [`LayoutFault::Width`] for an ordinal above `u32::MAX`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LayoutFault::Width`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the keyed fixture's records rebuild the committed
    ///   root on reopening, so a column ordinal written at another width or
    ///   order misreads.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == u32::try_from(ordinal.0).is_ok())]
    pub(crate) fn column(
        mut self,
        ordinal: Ordinal,
    ) -> Result<Self, LayoutFault>
    {
        let ordinal = u32::try_from(ordinal.0).map_err(|_overflow| LayoutFault::Width)?;
        let mut bytes = ordinal.to_le_bytes();
        bytes.reverse();
        self.0.extend_from_slice(&bytes);
        Ok(self)
    }

    /// Appends a value with its four-byte big-endian length.
    ///
    /// # Specification
    /// - ensures: on success the length and the bytes are appended.
    /// - fails: [`LayoutFault::Width`] for a value over `u32::MAX` bytes.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LayoutFault::Width`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the subject inverse's proof for one digest excludes a
    ///   longer digest that extends it.
    /// - witness: `tests::proofs::a_value_preimage_excludes_a_value_it_prefixes`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == u32::try_from(value.as_ref().len()).is_ok())]
    pub(crate) fn value(
        mut self,
        value: &AttributeValue,
    ) -> Result<Self, LayoutFault>
    {
        let length = u32::try_from(value.as_ref().len()).map_err(|_overflow| LayoutFault::Width)?;
        let mut bytes = length.to_le_bytes();
        bytes.reverse();
        self.0.extend_from_slice(&bytes);
        self.0.extend_from_slice(value.as_ref());
        Ok(self)
    }

    /// The finished key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn key(self) -> OwnedRecordKey
    {
        OwnedRecordKey::from(self.0)
    }
}

/// A key family's opening byte.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Family(u8);

impl Store
{
    /// Every record of one table, sorted by key.
    ///
    /// # Specification
    /// - ensures: on success the records the module documentation's table lists
    ///   for the table's live parts, cells and kept inverses, strictly
    ///   increasing.
    /// - fails: [`StoreError::Refused`] for an identifier outside the schema,
    ///   and [`StoreError::Layout`] for an ordinal or value too wide to key.
    /// - panics: none.
    /// - executable: none — the layout's independent statement is the reopen
    ///   comparison and the fixed record witness.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the two-vertex fixture's records are compared with
    ///   a hand-written list; reopening refuses records that are not these.
    /// - witness: `tests::proofs::a_table_lies_on_the_record_plane_as_documented`
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    pub(crate) fn table_records(
        &self,
        object: ObjectId,
    ) -> Result<Vec<Record>, StoreError>
    {
        let name = self.object_name(object)?;
        let layout = |fault| StoreError::Layout {
            object: name.clone(),
            fault,
        };
        let table = self.table(object)?;
        let mut records = Vec::new();

        for part in table.iter() {
            let key = KeyWriter::family(PART).part(part).key();
            records.push(Record::new(key, Vec::new()));
        }

        for &arrow in self.schema.outgoing(object) {
            let column = self.arrow_column(arrow)?;
            for part in table.iter() {
                let target = self.cell(arrow, part)?;
                let key = KeyWriter::family(ARROW)
                    .column(Ordinal(usize::from(arrow)))
                    .map_err(layout)?
                    .part(part)
                    .key();
                records.push(Record::new(key, Vec::from(u64::from(target).to_le_bytes())));
                if let ArrowIndex::Kept(_) = column.index {
                    let key = KeyWriter::family(ARROW_INDEX)
                        .column(Ordinal(usize::from(arrow)))
                        .map_err(layout)?
                        .part(target)
                        .part(part)
                        .key();
                    records.push(Record::new(key, Vec::new()));
                }
            }
        }

        for &attribute in self.schema.fields(object) {
            let column = self.value_column(attribute)?;
            for part in table.iter() {
                let value = self.value(attribute, part)?;
                let key = KeyWriter::family(VALUE)
                    .column(Ordinal(usize::from(attribute)))
                    .map_err(layout)?
                    .part(part)
                    .key();
                records.push(Record::new(key, Vec::from(value.as_ref())));
                if let ValueIndex::Kept(_) = column.index {
                    let key = KeyWriter::family(VALUE_INDEX)
                        .column(Ordinal(usize::from(attribute)))
                        .map_err(layout)?
                        .value(value)
                        .map_err(layout)?
                        .part(part)
                        .key();
                    records.push(Record::new(key, Vec::new()));
                }
            }
        }

        records.sort_unstable();
        Ok(records)
    }

    /// Builds every stale table's tree, writes every tree into the block
    /// store, and seals the manifest.
    ///
    /// # Specification
    /// - ensures: on success every node of every table's tree is loadable from
    ///   `blocks`, the manifest binds each table's counter and tree, and the
    ///   returned root is [`Store::root`]; the root is a function of the
    ///   schema, the parameters and each table's parts, cells and counter.
    /// - fails: [`StoreError::Records`] carrying the record plane's refusal of
    ///   a tree or a node, and [`StoreError::Layout`] for a column too wide to
    ///   key; the last commit stands.
    /// - panics: none.
    /// - executable: none — the postcondition loads every node; the reopen
    ///   witness does.
    /// - intension: rebuilds only the tables edited since the last commit;
    ///   writes every table's nodes, because the block store a commit receives
    ///   need not be the one before.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a committed fixture reopens from the block store to
    ///   an equal store; two stores built in the same order commit to one root,
    ///   and an edit and its inverse edit return the counter-advanced root.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    /// - witness: `tests::proofs::the_root_is_a_function_of_the_contents_and_counters`
    #[inline]
    pub fn commit<B>(
        &mut self,
        blocks: &mut B,
    ) -> Result<StoreRoot, StoreError>
    where
        B: BlockStore + ?Sized,
    {
        let mut trees = self.committed.trees.to_vec();
        for object in self.schema.objects() {
            let stale = self
                .committed
                .staleness
                .get(usize::from(object))
                .is_none_or(|staleness| *staleness == Staleness::Stale);
            if !stale {
                continue;
            }
            let records = self.table_records(object)?;
            let refs: Vec<RecordRef<'_>> = records.iter().map(Record::as_record_ref).collect();
            let tree = RecordTree::build(&refs, self.params)?;
            if let Some(slot) = trees.get_mut(usize::from(object)) {
                *slot = tree;
            }
        }

        // economy: every table's nodes are written on every commit; a store
        // that remembered which block store holds them could skip the
        // tables no edit touched.
        for tree in &trees {
            tree.write_to(blocks)?;
        }

        let manifest = StoreManifest::over(
            &self.schema,
            self.params,
            self.tables.iter().map(PartSet::next_key).zip(trees.iter()),
        )?;
        self.committed.trees = trees.into_boxed_slice();
        self.committed.manifest = manifest;
        for staleness in &mut self.committed.staleness {
            *staleness = Staleness::Fresh;
        }
        Ok(self.root())
    }

    /// Reopens a committed store from a block store.
    ///
    /// # Specification
    /// - ensures: on success the store's parts, cells, counters and root are
    ///   the committed store's, and the store meets its invariant.
    /// - fails: [`StoreError::SchemaMismatch`], [`StoreError::ProfileMismatch`]
    ///   and [`StoreError::TableCount`] before any load;
    ///   [`StoreError::Records`] for a node the block store cannot
    ///   authenticate; [`StoreError::Layout`] naming the table and the fault
    ///   for records that do not rebuild the committed tree, do not parse, or
    ///   are not canonical; [`StoreError::Refused`] carrying
    ///   [`crate::Refusal::NotLive`] for an arrow reaching a part that is not
    ///   live and [`crate::Refusal::EquationViolated`] for an equation that
    ///   fails.
    /// - panics: none.
    /// - executable: none — the postcondition compares whole stores; the
    ///   round-trip witness does.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the keyed fixture reopens equal to the store that
    ///   committed it; a block store whose table was rewritten with a violating
    ///   arrow, signed under its own root, is refused by the equation's name; a
    ///   missing cell is refused as not canonical.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    pub fn open<B>(
        schema: Schema,
        params: TreeParams,
        manifest: &StoreManifest,
        blocks: &B,
    ) -> Result<Self, StoreError>
    where
        B: BlockStore + ?Sized,
    {
        manifest.ensure_reader(&schema, params)?;
        let mut store = Self::new(schema, params)?;

        let mut loaded = Vec::new();
        let mut trees = Vec::new();
        let objects: Vec<ObjectId> = store.schema.objects().collect();
        for (&object, table) in objects.iter().zip(manifest.tables()) {
            let name = store.object_name(object)?;
            let records = load_records(blocks, table.root_node())?;
            let refs: Vec<RecordRef<'_>> = records.iter().map(Record::as_record_ref).collect();
            let tree = RecordTree::build(&refs, params)?;
            if tree.root_node_hash() != table.root_node()
                || tree.root().record_count() != table.records()
            {
                return Err(StoreError::Layout {
                    object: name,
                    fault: LayoutFault::Root,
                });
            }
            if let Some(parts) = store.tables.get_mut(usize::from(object)) {
                *parts = PartSet::reserved(table.next());
            }
            store.read_table(object, &records)?;
            loaded.push(records);
            trees.push(tree);
        }

        store.reindex_all()?;
        for (object, records) in store.schema.objects().zip(&loaded) {
            if store.table_records(object)? != *records {
                return Err(StoreError::Layout {
                    object: store.object_name(object)?,
                    fault: LayoutFault::NotCanonical,
                });
            }
        }
        store.ensure_references()?;
        store.audit()?;

        store.committed.trees = trees.into_boxed_slice();
        store.committed.manifest = manifest.clone();
        for staleness in &mut store.committed.staleness {
            *staleness = Staleness::Fresh;
        }
        Ok(store)
    }

    /// Reads one table's parts and cells from its records.
    ///
    /// # Specification
    /// - requires: the table's counter is the manifest's.
    /// - ensures: on success every part and cell record is in the store; the
    ///   inverse families are skipped, to be compared once recomputed.
    /// - fails: [`StoreError::Layout`] naming the table and the fault for an
    ///   unknown family, a wrong width, a foreign column or a key at or past
    ///   the counter.
    /// - panics: none.
    /// - executable: none — the reading is checked by the canonical comparison
    ///   that follows it.
    ///
    /// # Errors
    /// [`StoreError::Layout`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a table with a record of an unknown family is refused
    ///   with the family fault.
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    fn read_table(
        &mut self,
        object: ObjectId,
        records: &[Record],
    ) -> Result<(), StoreError>
    {
        let name = self.object_name(object)?;
        let fail = |fault| StoreError::Layout {
            object: name.clone(),
            fault,
        };
        let next = self.table(object)?.next_key();

        for record in records {
            let key: &[u8] = record.key().into();
            let Some((&family, rest)) = key.split_first()
            else {
                return Err(fail(LayoutFault::Family));
            };
            match Family(family) {
                PART => {
                    let part = exact_part(KeySuffix(rest)).map_err(fail)?;
                    if part >= next {
                        return Err(fail(LayoutFault::Counter));
                    }
                    if let Some(table) = self.tables.get_mut(usize::from(object)) {
                        table.restore(part);
                    }
                },
                ARROW => {
                    let (ordinal, part) = column_part(KeySuffix(rest)).map_err(fail)?;
                    let arrow = self
                        .schema
                        .outgoing(object)
                        .iter()
                        .copied()
                        .find(|arrow| usize::from(*arrow) == ordinal.0)
                        .ok_or_else(|| fail(LayoutFault::Column))?;
                    let value: &[u8] = record.value().into();
                    let target: [u8; 8] = value
                        .try_into()
                        .map_err(|_width| fail(LayoutFault::Width))?;
                    let target = PartKey::from(u64::from_le_bytes(target));
                    if part >= next {
                        return Err(fail(LayoutFault::Counter));
                    }
                    let slot = part
                        .slot()
                        .map_err(|_unaddressable| fail(LayoutFault::Counter))?;
                    if let Some(column) = self.arrows.get_mut(usize::from(arrow)) {
                        ensure_slot(&mut column.targets, slot);
                        if let Some(cell) = column.targets.get_mut(usize::from(slot)) {
                            *cell = target;
                        }
                    }
                },
                VALUE => {
                    let (ordinal, part) = column_part(KeySuffix(rest)).map_err(fail)?;
                    let attribute = self
                        .schema
                        .fields(object)
                        .iter()
                        .copied()
                        .find(|attribute| usize::from(*attribute) == ordinal.0)
                        .ok_or_else(|| fail(LayoutFault::Column))?;
                    if part >= next {
                        return Err(fail(LayoutFault::Counter));
                    }
                    let slot = part
                        .slot()
                        .map_err(|_unaddressable| fail(LayoutFault::Counter))?;
                    let value: &[u8] = record.value().into();
                    if let Some(column) = self.values.get_mut(usize::from(attribute)) {
                        ensure_slot(&mut column.values, slot);
                        if let Some(cell) = column.values.get_mut(usize::from(slot)) {
                            *cell = AttributeValue::from(value);
                        }
                    }
                },
                ARROW_INDEX | VALUE_INDEX => {},
                _ => return Err(fail(LayoutFault::Family)),
            }
        }
        Ok(())
    }

    /// Recomputes every kept inverse from the cells of live parts.
    ///
    /// # Specification
    /// - ensures: on success every kept inverse lists exactly the live parts
    ///   mapping to each value.
    /// - fails: [`StoreError::Refused`] for an identifier outside the schema.
    /// - panics: none.
    /// - executable: none — the postcondition reads every inverse; the
    ///   canonical comparison that follows compares them with the stored ones.
    ///
    /// # Errors
    /// [`StoreError::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the reopened keyed fixture answers every preimage the
    ///   original answered.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    pub(crate) fn reindex_all(&mut self) -> Result<(), StoreError>
    {
        let arrows: Vec<ArrowId> = self.schema.arrows().collect();
        for arrow in arrows {
            let source = self.schema.arrow_at(arrow)?.source();
            let parts: Vec<PartKey> = self.table(source)?.iter().collect();
            for part in parts {
                let target = self.cell(arrow, part)?;
                if let Some(column) = self.arrows.get_mut(usize::from(arrow)) {
                    column.index_insert(target, part);
                }
            }
        }
        let attributes: Vec<AttributeId> = self.schema.attributes().collect();
        for attribute in attributes {
            let object = self.schema.attribute_at(attribute)?.object();
            let parts: Vec<PartKey> = self.table(object)?.iter().collect();
            for part in parts {
                // The read refuses a part that is not live; the inverse then
                // takes the value from its slot in place.
                let _held = self.value(attribute, part)?;
                let slot = self.slot(object, part)?;
                if let Some(column) = self.values.get_mut(usize::from(attribute)) {
                    column.index_insert_slot(slot, part);
                }
            }
        }
        Ok(())
    }

    /// Refuses an arrow cell of a live part that reaches a part that is not
    /// live.
    ///
    /// # Specification
    /// - ensures: success exactly when every arrow of every live part reaches a
    ///   live part.
    /// - fails: [`StoreError::Refused`] carrying [`crate::Refusal::NotLive`]
    ///   naming the first unreachable target, in arrow then key order.
    /// - panics: none.
    /// - executable: none — the check is itself the whole-store walk.
    ///
    /// # Errors
    /// [`StoreError::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block store whose edge reaches a deleted vertex is
    ///   refused naming the vertex.
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    fn ensure_references(&self) -> Result<(), StoreError>
    {
        for arrow in self.schema.arrows() {
            let spec = self.schema.arrow_at(arrow)?;
            for part in self.table(spec.source())?.iter() {
                let target = self.cell(arrow, part)?;
                if self.table(spec.target())?.liveness(target) == Liveness::Dead {
                    return Err(StoreError::Refused(self.not_live(spec.target(), target)));
                }
            }
        }
        Ok(())
    }
}

/// A key suffix that is exactly one part key.
///
/// # Specification
/// - ensures: on success the key the eight big-endian bytes state.
/// - fails: [`LayoutFault::Width`] for any other length.
/// - panics: none.
/// - executable: none — the answer is the decoding itself.
///
/// # Errors
/// [`LayoutFault::Width`].
///
/// # Adequacy
/// - hypothesis: L2 — every part record of the keyed fixture reads back.
/// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
#[inline]
fn exact_part(suffix: KeySuffix<'_>) -> Result<PartKey, LayoutFault>
{
    let mut bytes: [u8; 8] = suffix.0.try_into().map_err(|_width| LayoutFault::Width)?;
    bytes.reverse();
    Ok(PartKey::from(u64::from_le_bytes(bytes)))
}

/// A key suffix that is exactly a column ordinal and a part key.
///
/// # Specification
/// - ensures: on success the ordinal and key when the suffix is exactly twelve
///   bytes.
/// - fails: [`LayoutFault::Width`] for any other length.
/// - panics: none.
/// - executable: none — the answer is the decoding itself.
///
/// # Errors
/// [`LayoutFault::Width`].
///
/// # Adequacy
/// - hypothesis: L2 — every cell record of the keyed fixture reads back.
/// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
#[inline]
fn column_part(suffix: KeySuffix<'_>) -> Result<(Ordinal, PartKey), LayoutFault>
{
    let (column, part) = suffix
        .0
        .split_first_chunk::<4>()
        .ok_or(LayoutFault::Width)?;
    let mut column = *column;
    column.reverse();
    let ordinal =
        usize::try_from(u32::from_le_bytes(column)).map_err(|_overflow| LayoutFault::Width)?;
    let part = exact_part(KeySuffix(part))?;
    Ok((Ordinal(ordinal), part))
}

/// The bytes of a key after its family byte.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct KeySuffix<'key>(&'key [u8]);

/// Loads every record a stored tree holds, in key order.
///
/// # Specification
/// - ensures: on success the records of the root when it is a leaf, or of each
///   child leaf in child order when it is internal, each node loaded through
///   the block store's verified load.
/// - fails: [`StoreError::Records`] carrying the block store's or the node
///   decoder's refusal, or the refusal of a child that is not a leaf.
/// - panics: none.
/// - executable: none — the records are checked against the manifest by
///   rebuilding, which is this function's independent observation.
///
/// # Errors
/// [`StoreError::Records`].
///
/// # Adequacy
/// - hypothesis: L2 — the keyed fixture reopens through leaf and internal roots
///   alike, and a block store missing a node is refused.
/// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
/// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
fn load_records<B>(
    blocks: &B,
    root: NodeHash,
) -> Result<Vec<Record>, StoreError>
where
    B: BlockStore + ?Sized,
{
    let stored = blocks.load(root)?;
    let node = decode_node(stored.bytes(), &mut DecodeWork::new())?;
    let internal = match node {
        DecodedNode::Leaf(leaf) => return Ok(leaf.records().to_vec()),
        DecodedNode::Internal(internal) => internal,
    };
    let mut records = Vec::new();
    for child in internal.children() {
        let stored = blocks.load(child.identity())?;
        let node = decode_node(stored.bytes(), &mut DecodeWork::new())?;
        let leaf = node.as_leaf()?;
        records.extend_from_slice(leaf.records());
    }
    Ok(records)
}
