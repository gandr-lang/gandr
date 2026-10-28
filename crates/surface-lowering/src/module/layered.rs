//! A table by key held in two parts: the entries of the closure a module was
//! lowered after, shared with every other module lowered after it and with the
//! suspended lowering, and the module's own.

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

/// How many entries a layered table holds, its two parts together.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EntryCount(pub usize);

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

    /// The entry at `key` to write: the module's own, else the closure's,
    /// whose part is first copied apart when another table shares it, so no
    /// table sharing it sees the write.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: what [`Self::get`] reads at `key`, writable; every other
    ///   entry, and every other table's, unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `module::layered::tests::a_write_to_the_closure_s_entry_is_the_writer_s_own_3408`
    #[spec(
        captures: held = matches!(self.get(key), Maybe::Present(_)),
        ensures: |ret| matches!(ret, Maybe::Present(_)) == held,
    )]
    #[inline]
    pub(crate) fn get_mut(
        &mut self,
        key: &Key,
    ) -> Maybe<&mut Value, layered_entry::Absent>
    where
        Key: Clone,
        Value: Clone,
    {
        let held = if self.own.contains_key(key) {
            self.own.get_mut(key)
        }
        else {
            match self.closure {
                Maybe::Present(ref mut closure) if closure.contains_key(key) => {
                    Arc::make_mut(closure).get_mut(key)
                },
                Maybe::Present(_) | Maybe::Absent(_) => None,
            }
        };
        held.map_or(
            Maybe::Absent(layered_entry::Absent::Unfiled),
            Maybe::Present,
        )
    }

    /// File `value` at `key`: over the closure's entry when it holds one,
    /// copied apart as [`Self::get_mut`] does, else among the module's own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::get`] reads `value` at `key`; every other entry
    ///   unchanged, and the own part holds no key the closure's does.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — `key` and `value` move into the table, so a clause
    ///   could read them back only through a clone the method does not need.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `module::layered::tests::a_write_to_the_closure_s_entry_is_the_writer_s_own_3408`
    #[inline]
    pub(crate) fn insert(
        &mut self,
        key: Key,
        value: Value,
    ) where
        Key: Clone,
        Value: Clone,
    {
        match self.get_mut(&key) {
            Maybe::Present(held) => *held = value,
            Maybe::Absent(_) => {
                let _fresh = self.own.insert(key, value);
            },
        }
    }

    /// How many entries the two parts hold together.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the closure's entries and the module's own, which share no
    ///   key.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — counting the entries again would walk both parts,
    ///   which a clause may not; the sum of the two parts' lengths is the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `module::layered::tests::a_write_to_the_closure_s_entry_is_the_writer_s_own_3408`
    #[inline]
    pub(crate) fn count(&self) -> EntryCount
    {
        let closure = match self.closure {
            Maybe::Present(ref closure) => closure.len(),
            Maybe::Absent(_) => 0_usize,
        };
        EntryCount(closure.saturating_add(self.own.len()))
    }

    /// Every entry's value: the closure's in key order, then the module's own
    /// in key order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn values(&self) -> impl Iterator<Item = &Value>
    {
        self.entries().map(|(_, value)| value)
    }

    /// Share every entry, so a clone copies none of them: the module's own
    /// moved into the closure's part.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every entry kept, and the own part empty.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Layered`].
    /// - witness: `module::layered::tests::a_write_to_the_closure_s_entry_is_the_writer_s_own_3408`
    #[spec(
        captures: count = self.count(),
        ensures: self.count() == count && self.own.is_empty(),
    )]
    #[inline]
    pub(crate) fn share(&mut self)
    where
        Key: Clone,
        Value: Clone,
    {
        let every = core::mem::replace(self, Self::whole(BTreeMap::new())).shared();
        self.closure = Maybe::Present(every);
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
        self.count() == other.count()
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

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::sync::Arc;

    use quenchant_shape::shape::Maybe;

    use super::EntryCount;
    use super::Layered;

    /// #3408: a lowering resumed after its closure shares the closure's
    /// collected entries with the suspended lowering rather than copying
    /// them, so an entry one of them files or writes is its own: the other
    /// still reads the shared entry. Sharing keeps every entry, and the
    /// table's own entries read after the closure's.
    #[test]
    fn a_write_to_the_closure_s_entry_is_the_writer_s_own_3408()
    {
        let values = |table: &Layered<u8, char>| table.values().copied().collect::<String>();
        let mut suspended = Layered::whole(BTreeMap::from([(0_u8, 'a'), (2_u8, 'c')]));
        suspended.insert(1_u8, 'b');
        suspended.share();
        assert_eq!(suspended.count(), EntryCount(3_usize));
        assert!(suspended.own.is_empty(), "sharing leaves nothing own");
        assert_eq!("abc", values(&suspended));

        let mut resumed = suspended.clone();
        let shared = |table: &Layered<u8, char>| match table.closure {
            Maybe::Present(ref closure) => Arc::clone(closure),
            Maybe::Absent(_) => panic!("the table shares a closure's part"),
        };
        assert!(Arc::ptr_eq(&shared(&resumed), &shared(&suspended)));
        resumed.insert(4_u8, 'e');
        resumed.insert(3_u8, 'd');
        assert!(
            Arc::ptr_eq(&shared(&resumed), &shared(&suspended)),
            "filing past the closure leaves its part shared"
        );
        assert_eq!("abcde", values(&resumed));
        assert_eq!(resumed.count(), EntryCount(5_usize));
        assert!(matches!(resumed.get(&3_u8), Maybe::Present(&'d')));
        assert!(matches!(suspended.get(&3_u8), Maybe::Absent(_)));

        let Maybe::Present(written) = resumed.get_mut(&0_u8)
        else {
            panic!("the closure's entry is held");
        };
        *written = 'A';
        resumed.insert(2_u8, 'C');
        assert_eq!("AbCde", values(&resumed));
        assert_eq!(
            resumed.count(),
            EntryCount(5_usize),
            "a write over the closure's entry adds none"
        );
        assert_eq!(
            "abc",
            values(&suspended),
            "and is unseen by the suspended table"
        );
        assert!(matches!(resumed.get(&5_u8), Maybe::Absent(_)));
        assert!(matches!(resumed.get_mut(&5_u8), Maybe::Absent(_)));

        resumed.share();
        assert_eq!("AbCde", values(&resumed), "sharing keeps every entry");
        assert_ne!(resumed, suspended);
        assert_eq!(
            suspended,
            Layered::whole(BTreeMap::from([(0_u8, 'a'), (1_u8, 'b'), (2_u8, 'c')]))
        );
    }
}
