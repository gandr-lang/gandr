//! Rows: finite maps from labels to entries, each label once, closed or open
//! through one tail.
//!
//! A row `⟨l₁ : E₁, …, lₙ : Eₙ⟩` holds each label once — label apartness is
//! its well-formedness — in canonical label order, so two rows that list the
//! same entries in different orders are one row. A row `⟨l₁ : E₁, … | ρ⟩` is
//! open: its tail `ρ` stands for the further entries a row variable is
//! instantiated with, and lacks every label written beside it. A row has at
//! most one tail. The empty row allocates nothing, and cloning a nonempty row
//! shares its immutable map. A [`Label`] names a record field, a variant
//! constructor or an effect instance alike: one named thing of a type.
//! [`EffectRow`](crate::effect::EffectRow) is the effects reading: the
//! interfaces a returner may perform, each under its label.
//!
//! # Items
//!
//! The operations are the set operations of rows that agree at the labels
//! they share. [`Row::union`] joins two rows, keeping their one tail and
//! refusing a label they define apart or two different tails.
//! [`Row::without`] removes a label and keeps the tail. [`Row::is_subset`]
//! decides inclusion, an open row included only in a row open through the
//! same tail. [`Row::difference`] keeps the entries another row does not
//! write, which is what a tail is solved to when a row equation forces it.
//! [`Row::from_entries`] refuses a label written twice, [`LabelTwice`].
//!
//! # References
//!
//! - Daniel Hillerström and Sam Lindley. _Liberating Effects with Rows and
//!   Handlers_. Type-Driven Development 2016: one row kind for records,
//!   variants and effects; the row variable lacks the labels written beside it.
//! - J. Garrett Morris and James `McKinna`. _Abstracting Extensible Data Types:
//!   Or, Rows by Any Other Name_. POPL 2019: rows as a partial monoid under
//!   combination, and containment.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map;
use alloc::sync::Arc;

use anodized::spec;

/// The name of a row's entry: a record field, a variant constructor or an
/// effect instance.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Label(Arc<str>);

impl From<&str> for Label
{
    /// Copy a label into shared storage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(Arc::from(name))
    }
}

impl From<Arc<str>> for Label
{
    /// A label sharing `name`'s storage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: Arc<str>) -> Self
    {
        Self(name)
    }
}

impl AsRef<str> for Label
{
    /// Borrow the label's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// A row: each label once, in canonical label order, closed or open through
/// one tail.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Row<L, E, T>
{
    /// The written entries, none for the allocation-free empty map.
    entries: Option<Arc<BTreeMap<L, E>>>,
    /// The tail the row is open through, none for a closed row.
    tail: Option<T>,
}

/// A label a row would hold twice.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabelTwice<L>(pub L);

/// Two rows a union cannot join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RowsApart<L, T>
{
    /// A label both rows hold with entries that do not agree.
    Label(L),
    /// The two different tails the rows are open through: a row has one.
    Tails(T, T),
}

/// Inclusion between rows that agree at the labels they share.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RowInclusion
{
    /// Every label is in the receiving row, with an agreeing entry, and the
    /// tail, when there is one, is the receiving row's.
    Included,
    /// A label is absent from the receiving row or holds a disagreeing entry
    /// there, or the tail is not the receiving row's.
    Excluded,
}

impl<L, E, T> Row<L, E, T>
{
    /// The empty row.
    pub const EMPTY: Self = Self {
        entries: None,
        tail: None,
    };

    /// The tail the row is open through, none for a closed row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tail(&self) -> Option<&T>
    {
        self.tail.as_ref()
    }
}

impl<L, E, T> Default for Row<L, E, T>
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

impl<L: Ord + Clone + 'static, E: Clone + 'static, T: Clone + Eq> Row<L, E, T>
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
        self.entries.as_deref().unwrap_or(Self::EMPTY_ENTRIES)
    }

    /// The row of `map`'s entries, which a map's keys make apart, open
    /// through `tail`.
    ///
    /// # Specification
    /// - ensures: the row holds exactly `map`'s entries and `tail`; an empty
    ///   map allocates nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rewriting no entry and every entry of a row
    ///   distinguishes sharing from rebuilding.
    /// - witness: `effect::tests::operation_types_survive_substitution_and_import`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.entries.as_ref().is_none_or(|map| !map.is_empty()))]
    pub(crate) fn from_map(
        map: BTreeMap<L, E>,
        tail: Option<T>,
    ) -> Self
    {
        Self {
            entries: (!map.is_empty()).then(|| Arc::new(map)),
            tail,
        }
    }

    /// The closed row holding `entry` at `label` alone.
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
        Self {
            entries: Some(Arc::new(BTreeMap::from([(label, entry)]))),
            tail: None,
        }
    }

    /// The closed row of `entries`, each label once.
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
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|row| row.tail.is_none() && row.entries.as_ref().is_none_or(|map| !map.is_empty())))]
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
        Ok(Self::from_map(map, None))
    }

    /// This row's entries, open through `tail` instead of this row's tail.
    ///
    /// # Specification
    /// - ensures: the entries are this row's, shared, and the tail is `tail`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — opening a closed row, closing an open one and
    ///   replacing a tail distinguish the tail's replacement from a join.
    /// - witness: `row::tests::a_row_has_one_tail_and_inclusion_keeps_it`
    #[inline]
    #[must_use]
    #[spec(captures: expected = tail.clone(), ensures: |ret| ret.entries.as_ref().map(Arc::as_ptr) == self.entries.as_ref().map(Arc::as_ptr) && ret.tail == expected)]
    pub fn with_tail(
        &self,
        tail: Option<T>,
    ) -> Self
    {
        Self {
            entries: self.entries.clone(),
            tail,
        }
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

    /// Join two rows: every label of either, an agreeing shared label once,
    /// and the one tail either is open through.
    ///
    /// # Specification
    /// - requires: `agree` is an equivalence on entries.
    /// - ensures: each input is included in a successful union; a union that
    ///   adds no label and no tail shares this row's map.
    /// - fails: a label both rows hold with entries `agree` excludes, or two
    ///   different tails, is refused.
    ///
    /// # Errors
    /// [`RowsApart::Label`] for the first label, in canonical order, the two
    /// rows define apart; [`RowsApart::Tails`] for two different tails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every pair of rows over three labels, a disagreeing
    ///   entry at a shared label, and each pairing of no tail, one tail and two
    ///   distinguish the union from intersection, replacement, duplicate
    ///   accumulation and a dropped or invented tail.
    /// - witness: `effect::tests::the_row_operations_are_the_set_arithmetic_of_their_names`
    /// - witness: `row::tests::a_row_has_one_tail_and_inclusion_keeps_it`
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
    ) -> Result<Self, RowsApart<L, T>>
    where
        Agree: Fn(&E, &E) -> RowInclusion,
    {
        let tail = match (&self.tail, &other.tail) {
            (&Some(ref ours), &Some(ref theirs)) if ours != theirs => {
                return Err(RowsApart::Tails(ours.clone(), theirs.clone()));
            },
            (&Some(ref tail), _) | (&None, &Some(ref tail)) => Some(tail.clone()),
            (&None, &None) => None,
        };
        if self.entries.is_none() {
            return Ok(other.with_tail(tail));
        }
        let mut expanded = None;
        for (label, entry) in other.entries() {
            match self.entries().get(label) {
                Some(existing) => {
                    if agree(existing, entry) == RowInclusion::Excluded {
                        return Err(RowsApart::Label(label.clone()));
                    }
                },
                None => {
                    let _replaced = expanded
                        .get_or_insert_with(|| self.entries().clone())
                        .insert(label.clone(), entry.clone());
                },
            }
        }
        Ok(expanded.map_or_else(
            || self.with_tail(tail.clone()),
            |entries| Self::from_map(entries, tail.clone()),
        ))
    }

    /// Remove `label`, keeping the tail.
    ///
    /// # Specification
    /// - ensures: `label` is absent, every other entry and the tail are kept;
    ///   removing an absent label shares this row's map, and removing the last
    ///   label leaves no allocation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — removing a present and an absent label from every row
    ///   over three labels, open and closed, distinguishes selective removal
    ///   from clearing, identity and dropping the tail.
    /// - witness: `effect::tests::the_row_operations_are_the_set_arithmetic_of_their_names`
    /// - witness: `row::tests::a_row_has_one_tail_and_inclusion_keeps_it`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.get(label).is_none() && ret.tail == self.tail && ret.entries().len() == self.entries().len().saturating_sub(usize::from(self.entries().contains_key(label))))]
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
        Self::from_map(entries, self.tail.clone())
    }

    /// Keep the entries whose labels `other` does not write, open through
    /// this row's tail.
    ///
    /// # Specification
    /// - ensures: a label is in the difference exactly when this row writes it
    ///   and `other` does not, with this row's entry; the tail is this row's; a
    ///   difference that removes nothing shares this row's map.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every pair of rows over three labels, open and
    ///   closed, distinguishes the difference from removal of shared entries
    ///   alone, from intersection, and from taking the other row's tail.
    /// - witness: `row::tests::a_row_has_one_tail_and_inclusion_keeps_it`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body filters this row's labels once; the check compares each label of this row with the difference once"
        )
    )]
    #[spec(ensures: |ret| ret.tail == self.tail && self.entries().keys().all(|label| ret.entries().contains_key(label) != other.entries().contains_key(label)) && ret.entries().keys().all(|label| self.entries().contains_key(label)))]
    pub fn difference(
        &self,
        other: &Self,
    ) -> Self
    {
        if !self
            .entries()
            .keys()
            .any(|label| other.entries().contains_key(label))
        {
            return self.clone();
        }
        let entries = self
            .entries()
            .iter()
            .filter(|&(label, _entry)| !other.entries().contains_key(label))
            .map(|(label, entry)| (label.clone(), entry.clone()))
            .collect();
        Self::from_map(entries, self.tail.clone())
    }

    /// Decide whether every label of this row is in `other` with an agreeing
    /// entry, and this row's tail, when there is one, is `other`'s.
    ///
    /// # Specification
    /// - requires: `agree` is an equivalence on entries.
    /// - ensures: inclusion holds exactly when every label of this row is in
    ///   `other` with an entry `agree` includes, and this row is closed or open
    ///   through `other`'s tail.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every pair of rows over three labels, a disagreeing
    ///   entry at a shared label, and each pairing of no tail, one tail and two
    ///   distinguish inclusion from label equality, from label inclusion alone,
    ///   and from ignoring the tail.
    /// - witness: `effect::tests::the_row_operations_are_the_set_arithmetic_of_their_names`
    /// - witness: `row::tests::a_row_has_one_tail_and_inclusion_keeps_it`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body compares every label of this row once; the check compares each once more"
        )
    )]
    #[spec(ensures: |ret| (ret == RowInclusion::Included) == (self.tail.as_ref().is_none_or(|tail| other.tail.as_ref() == Some(tail)) && self.entries().iter().all(|(label, entry)| other.entries().get(label).is_some_and(|theirs| agree(entry, theirs) == RowInclusion::Included))))]
    pub fn is_subset<Agree>(
        &self,
        other: &Self,
        agree: &Agree,
    ) -> RowInclusion
    where
        Agree: Fn(&E, &E) -> RowInclusion,
    {
        let tail_kept = self
            .tail
            .as_ref()
            .is_none_or(|tail| other.tail.as_ref() == Some(tail));
        if tail_kept
            && self.entries().iter().all(|(label, entry)| {
                other
                    .entries()
                    .get(label)
                    .is_some_and(|theirs| agree(entry, theirs) == RowInclusion::Included)
            })
        {
            RowInclusion::Included
        }
        else {
            RowInclusion::Excluded
        }
    }
}

#[cfg(test)]
mod tests;
