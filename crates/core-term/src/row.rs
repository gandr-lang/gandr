//! Closed rows: finite maps from labels to entries, each label once.
//!
//! A row `⟨l₁ : E₁, …, lₙ : Eₙ⟩` holds each label once — label apartness is
//! its well-formedness — in canonical label order, so two rows that list the
//! same entries in different orders are one row. The empty row allocates
//! nothing, and cloning a nonempty row shares its immutable map.
//! [`EffectRow`](crate::effect::EffectRow) is the effects reading: the
//! interfaces a returner may perform, each under its name.
//!
//! # Items
//!
//! The three operations are the set operations of rows that agree at the
//! labels they share: [`Row::union`] joins two rows and refuses a label they
//! define apart, [`Row::without`] removes a label, and [`Row::is_subset`]
//! decides inclusion. [`Row::from_entries`] refuses a label written twice,
//! [`LabelTwice`].
//!
//! # References
//!
//! - Daniel Hillerström and Sam Lindley. _Liberating Effects with Rows and
//!   Handlers_. Type-Driven Development 2016: one row kind for records,
//!   variants and effects.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map;
use alloc::sync::Arc;

use anodized::spec;

/// A closed row: each label once, in canonical label order.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Row<L, E>(Option<Arc<BTreeMap<L, E>>>);

/// A label a row would hold twice: written twice, or defined apart by two
/// rows joined.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabelTwice<L>(pub L);

/// Inclusion between rows that agree at the labels they share.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RowInclusion
{
    /// Every label is in the receiving row, with an agreeing entry.
    Included,
    /// A label is absent from the receiving row or holds a disagreeing entry
    /// there.
    Excluded,
}

impl<L, E> Row<L, E>
{
    /// The empty row.
    pub const EMPTY: Self = Self(None);
}

impl<L, E> Default for Row<L, E>
{
    /// The allocation-free empty row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::EMPTY
    }
}

impl<L: Ord + Clone + 'static, E: Clone + 'static> Row<L, E>
{
    /// A shared empty map for this label and entry family.
    const EMPTY_ENTRIES: &'static BTreeMap<L, E> = &BTreeMap::new();

    /// Borrow the canonical map, the empty row's included.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn entries(&self) -> &BTreeMap<L, E>
    {
        self.0.as_deref().unwrap_or(Self::EMPTY_ENTRIES)
    }

    /// The row of `map`'s entries, which a map's keys make apart.
    ///
    /// # Specification
    /// - ensures: the row holds exactly `map`'s entries; an empty map is the
    ///   allocation-free empty row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rewriting no entry and every entry of a row
    ///   distinguishes sharing from rebuilding.
    /// - witness: `effect::tests::operation_types_survive_substitution_and_import`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0.as_ref().is_none_or(|map| !map.is_empty()))]
    pub(crate) fn from_map(map: BTreeMap<L, E>) -> Self
    {
        if map.is_empty() {
            Self::EMPTY
        }
        else {
            Self(Some(Arc::new(map)))
        }
    }

    /// The row holding `entry` at `label` alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn singleton(
        label: L,
        entry: E,
    ) -> Self
    {
        Self(Some(Arc::new(BTreeMap::from([(label, entry)]))))
    }

    /// The row of `entries`, each label once.
    ///
    /// # Specification
    /// - ensures: the row holds every entry under its label whatever order they
    ///   come in; no entries make the allocation-free empty row.
    /// - fails: a label written twice is refused, never overwritten.
    ///
    /// # Errors
    /// [`LabelTwice`] for the first label written again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one label twice, the same entries in two orders and
    ///   no entries distinguish apartness from overwriting, a canonical row
    ///   from a list, and the empty row from an empty allocation.
    /// - witness: `row::tests::a_label_twice_is_refused_and_order_is_no_part_of_a_row`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|row| row.0.as_ref().is_none_or(|map| !map.is_empty())))]
    pub fn from_entries<Entries>(entries: Entries) -> Result<Self, LabelTwice<L>>
    where
        Entries: IntoIterator<Item = (L, E)>,
    {
        let mut map = BTreeMap::new();
        for (label, entry) in entries {
            match map.entry(label) {
                btree_map::Entry::Vacant(vacant) => {
                    let _entry = vacant.insert(entry);
                },
                btree_map::Entry::Occupied(occupied) => {
                    return Err(LabelTwice(occupied.key().clone()));
                },
            }
        }
        Ok(Self::from_map(map))
    }

    /// The entry at `label`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        label: &L,
    ) -> Option<&E>
    {
        self.entries().get(label)
    }

    /// Join two rows: every label of either, an agreeing shared label once.
    ///
    /// # Specification
    /// - requires: `agree` is an equivalence on entries.
    /// - ensures: each input is included in a successful union; a union that
    ///   adds no label shares this row's map.
    /// - fails: a label both rows hold with entries `agree` excludes is
    ///   refused.
    ///
    /// # Errors
    /// [`LabelTwice`] for the first label, in canonical order, the two rows
    /// define apart.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every pair of rows over three labels, and a
    ///   disagreeing entry at a shared label, distinguish the union from
    ///   intersection, replacement and duplicate accumulation.
    /// - witness: `effect::tests::the_row_operations_are_the_set_arithmetic_of_their_names`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the other row's labels and copies this row's map on growth; the check compares each label of both rows with the union once"
        )
    )]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|row| self.is_subset(row, agree) == RowInclusion::Included && other.is_subset(row, agree) == RowInclusion::Included))]
    pub fn union<Agree>(
        &self,
        other: &Self,
        agree: &Agree,
    ) -> Result<Self, LabelTwice<L>>
    where
        Agree: Fn(&E, &E) -> RowInclusion,
    {
        if self.0.is_none() {
            return Ok(other.clone());
        }
        let mut expanded = None;
        for (label, entry) in other.entries() {
            match self.entries().get(label) {
                Some(existing) => {
                    if agree(existing, entry) == RowInclusion::Excluded {
                        return Err(LabelTwice(label.clone()));
                    }
                },
                None => {
                    let _replaced = expanded
                        .get_or_insert_with(|| self.entries().clone())
                        .insert(label.clone(), entry.clone());
                },
            }
        }
        Ok(expanded.map_or_else(|| self.clone(), |entries| Self(Some(Arc::new(entries)))))
    }

    /// Remove `label`.
    ///
    /// # Specification
    /// - ensures: `label` is absent and every other entry is kept; removing an
    ///   absent label shares this row's map, and removing the last label makes
    ///   the allocation-free empty row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — removing a present and an absent label from every row
    ///   over three labels distinguishes selective removal from clearing and
    ///   identity.
    /// - witness: `effect::tests::the_row_operations_are_the_set_arithmetic_of_their_names`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.get(label).is_none() && ret.entries().len() == self.entries().len().saturating_sub(usize::from(self.entries().contains_key(label))))]
    pub fn without(
        &self,
        label: &L,
    ) -> Self
    {
        if !self.entries().contains_key(label) {
            return self.clone();
        }
        let mut entries = self.entries().clone();
        let _removed = entries.remove(label);
        Self::from_map(entries)
    }

    /// Decide whether every label of this row is in `other` with an agreeing
    /// entry.
    ///
    /// # Specification
    /// - requires: `agree` is an equivalence on entries.
    /// - ensures: inclusion holds exactly when every label of this row is in
    ///   `other` and `agree` includes the two entries.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every pair of rows over three labels, and a
    ///   disagreeing entry at a shared label, distinguish inclusion from label
    ///   equality and from label inclusion alone.
    /// - witness: `effect::tests::the_row_operations_are_the_set_arithmetic_of_their_names`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body compares every label of this row once; the check compares each once more"
        )
    )]
    #[spec(ensures: |ret| (ret == RowInclusion::Included) == self.entries().iter().all(|(label, entry)| other.entries().get(label).is_some_and(|theirs| agree(entry, theirs) == RowInclusion::Included)))]
    pub fn is_subset<Agree>(
        &self,
        other: &Self,
        agree: &Agree,
    ) -> RowInclusion
    where
        Agree: Fn(&E, &E) -> RowInclusion,
    {
        if self.entries().iter().all(|(label, entry)| {
            other
                .entries()
                .get(label)
                .is_some_and(|theirs| agree(entry, theirs) == RowInclusion::Included)
        }) {
            RowInclusion::Included
        }
        else {
            RowInclusion::Excluded
        }
    }
}

#[cfg(test)]
mod tests;
