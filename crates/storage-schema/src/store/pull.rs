//! The pull-back `Δ_F` of a store along a schema map; the map and what the
//! migration preserves are in [`crate::migrate`].

use alloc::vec::Vec;

use crate::error::StoreError;
use crate::migrate::SchemaMap;
use crate::parts::PartKey;
use crate::store::Staleness;
use crate::store::Store;

impl Store
{
    /// The store of the map's source schema that this store of its target
    /// schema determines.
    ///
    /// # Specification
    /// - requires: this store is of the map's target schema.
    /// - ensures: on success the table at each source object is this store's
    ///   table at its image, keys and counters included; each source arrow
    ///   takes a part where its image path takes it here; each source attribute
    ///   holds the image attribute's value at the image path's end; every kept
    ///   inverse lists exactly its live preimages. The new store mints as this
    ///   store's writer, and its root still names its empty commit until it is
    ///   committed.
    /// - fails: [`StoreError::SchemaMismatch`] for a store of another schema;
    ///   [`StoreError::Refused`] for an identifier the map does not resolve.
    /// - panics: none.
    /// - executable: none — the postcondition reads every column of both
    ///   stores; the witness reads them and audits the equations.
    /// - intension: no equation is checked: the map's check makes every source
    ///   equation hold of the images in any store of the target.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Cost
    /// - allocation: the pulled-back store, its tables, cells and inverses, and
    ///   the lists of parts that it walks, setup
    /// - allocation: a table's name in a refusal, error path
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the keyed fixture pulled back along a view reads
    ///   each column as its followed path, passes the full audit and keeps its
    ///   counters; a store of another schema is refused.
    /// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
    #[inline]
    pub fn pull_back(
        &self,
        map: &SchemaMap,
    ) -> Result<Self, StoreError>
    {
        if map.target().identity() != self.schema.identity() {
            return Err(StoreError::SchemaMismatch {
                expected: map.target().identity(),
                found: self.schema.identity(),
            });
        }
        let mut pulled = Self::new(map.source().clone(), self.params, self.writer)?;

        for object in map.source().objects() {
            let image = map.object(object)?;
            let table = self.table(image)?.clone();
            if let Some(slot) = pulled.tables.get_mut(usize::from(object)) {
                *slot = table;
            }
        }

        for arrow in map.source().arrows() {
            let source = map.source().arrow_at(arrow)?.source();
            let path = map.arrow(arrow)?;
            let parts: Vec<PartKey> = pulled.table(source)?.iter().collect();
            for part in parts {
                let target = self.follow(path, part)?;
                let Some(column) = pulled.arrows.get_mut(usize::from(arrow))
                else {
                    continue;
                };
                let Ok(cell) = column.targets.ensure(part)
                else {
                    return Err(StoreError::Refused(pulled.not_live(source, part)));
                };
                *cell = target;
            }
        }

        for attribute in map.source().attributes() {
            let object = map.source().attribute_at(attribute)?.object();
            let &(ref path, landing) = map.attribute(attribute)?;
            let parts: Vec<PartKey> = pulled.table(object)?.iter().collect();
            for part in parts {
                let end = self.follow(path, part)?;
                let value = self.value(landing, end)?.clone();
                let Some(column) = pulled.values.get_mut(usize::from(attribute))
                else {
                    continue;
                };
                let Ok(cell) = column.values.ensure(part)
                else {
                    return Err(StoreError::Refused(pulled.not_live(object, part)));
                };
                *cell = value;
            }
        }

        pulled.reindex_all()?;
        for staleness in &mut pulled.committed.staleness {
            *staleness = Staleness::Stale;
        }
        Ok(pulled)
    }
}
