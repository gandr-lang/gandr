//! A table a declaration's checking reads by its key, held in two parts: the
//! entries of the closure a module was lowered after, shared with every other
//! module lowered after it, and the module's own.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a layered table holds no entry at a key.
    pub mod layered_entry {
        /// Neither part holds the key.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No declaration filed an entry under the key.
            Unfiled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a layered table shares no closure's part.
    pub mod closure_part {
        /// The module holds every entry itself.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The module was lowered whole, after no closure.
            Whole,
        }
    }
}

/// A table by key: the entries of the closure a module was lowered after,
/// shared, and the entries the module's own lowering filed.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the table is the closure's entries and the module's own, the own
///   part holding no key the closure's does; two tables are equal when they
///   hold the same entries, however they are held.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — a type-level block.
///
/// # Adequacy
/// - hypothesis: L3 — a document resumed after its closure reads each of its
///   tables as the whole lowering's module does, at the closure's declarations
///   and its own.
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_reads_each_table_by_declaration_as_the_whole_3321`
#[derive(Clone)]
pub struct Layered<Key, Value>
{
    /// The closure's entries, shared with every module lowered after it.
    closure: Maybe<Arc<BTreeMap<Key, Value>>, closure_part::Absent>,
    /// The entries the module's own lowering filed: past the closure's for a
    /// module lowered after one, every entry otherwise.
    own: BTreeMap<Key, Value>,
}

impl<Key, Value> Layered<Key, Value>
where
    Key: Ord,
{
    /// The table of a module lowered whole, holding `own`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn whole(own: BTreeMap<Key, Value>) -> Self
    {
        Self {
            closure: Maybe::Absent(closure_part::Absent::Whole),
            own,
        }
    }

    /// The table of a module lowered after a closure whose table is
    /// `closure`: this table's entries at keys `closure` does not hold, read
    /// after `closure`'s.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer shares `closure`, and its own entries are this
    ///   table's at every key `closure` does not hold.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_reads_each_table_by_declaration_as_the_whole_3321`
    #[spec(ensures: |ret| matches!(ret.closure, Maybe::Present(ref shared) if Arc::ptr_eq(shared, closure))
        && ret.own.keys().all(|key| !closure.contains_key(key)))]
    #[inline]
    #[must_use]
    pub(crate) fn after(
        self,
        closure: &Arc<BTreeMap<Key, Value>>,
    ) -> Self
    where
        Key: Clone,
        Value: Clone,
    {
        let mut own = match self.closure {
            Maybe::Absent(_) => self.own,
            Maybe::Present(held) => {
                let mut own = Arc::unwrap_or_clone(held);
                own.extend(self.own);
                own
            },
        };
        own.retain(|key, _| !closure.contains_key(key));
        Self {
            closure: Maybe::Present(Arc::clone(closure)),
            own,
        }
    }

    /// The entry at `key`: the module's own, else the closure's.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the own part's entry at `key` when it holds one, else the
    ///   closure's; absent when neither part holds `key`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_reads_each_table_by_declaration_as_the_whole_3321`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_))
        == (self.own.contains_key(key)
            || matches!(self.closure, Maybe::Present(ref closure) if closure.contains_key(key))))]
    #[inline]
    pub(crate) fn get(
        &self,
        key: &Key,
    ) -> Maybe<&Value, layered_entry::Absent>
    {
        self.own
            .get(key)
            .or_else(|| match self.closure {
                Maybe::Present(ref closure) => closure.get(key),
                Maybe::Absent(_) => None,
            })
            .map_or(
                Maybe::Absent(layered_entry::Absent::Unfiled),
                Maybe::Present,
            )
    }

    /// Every entry, as one table: the closure's, shared with the modules
    /// lowered after it, for the closure itself to share.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a table holding exactly this table's entries; the closure's
    ///   own when this table holds none past it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer holds the entries of both parts, which a
    ///   clause could only compare by merging them again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_reads_each_table_by_declaration_as_the_whole_3321`
    #[inline]
    #[must_use]
    pub(crate) fn shared(self) -> Arc<BTreeMap<Key, Value>>
    where
        Key: Clone,
        Value: Clone,
    {
        match self.closure {
            Maybe::Absent(_) => Arc::new(self.own),
            Maybe::Present(closure) if self.own.is_empty() => closure,
            Maybe::Present(closure) => {
                let mut every = Arc::unwrap_or_clone(closure);
                every.extend(self.own);
                Arc::new(every)
            },
        }
    }

    /// Every entry: the closure's in key order, then the module's own in key
    /// order.
    ///
    /// # Specification
    /// trivial.
    fn entries(&self) -> impl Iterator<Item = (&Key, &Value)>
    {
        let closure = match self.closure {
            Maybe::Present(ref closure) => Some(closure.iter()),
            Maybe::Absent(_) => None,
        };
        closure.into_iter().flatten().chain(self.own.iter())
    }
}

impl<Key, Value> PartialEq for Layered<Key, Value>
where
    Key: Ord,
    Value: PartialEq,
{
    /// Whether the two tables hold the same entries, however each holds them.
    ///
    /// # Specification
    /// - requires: nothing; a table's own part holds no key its closure's part
    ///   holds, as [`Layered`] ensures.
    /// - ensures: true exactly when each entry of one is an entry of the other
    ///   at the same key, and they hold as many.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would restate the comparison.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_reads_each_table_by_declaration_as_the_whole_3321`
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.entries().count() == other.entries().count()
            && self.entries().all(
                |(key, value)| matches!(other.get(key), Maybe::Present(theirs) if theirs == value),
            )
    }
}

impl<Key, Value> Eq for Layered<Key, Value>
where
    Key: Ord,
    Value: Eq,
{
}

impl<Key, Value> fmt::Debug for Layered<Key, Value>
where
    Key: Ord + fmt::Debug,
    Value: fmt::Debug,
{
    /// The table's entries, as one map.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_map().entries(self.entries()).finish()
    }
}
