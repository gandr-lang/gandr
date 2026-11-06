//! Entries numbered within the form that pushed each: the store the scope's
//! frames and the lowering's flat stores share.
//!
//! # An entry takes its place within its form
//!
//! An entry's coordinate is the form whose classification pushed it and its
//! place among that form's entries ([`FormPlace`]). The layout block of a
//! form's descendants names the form, as a block and an offset name a node.
//! An edit to one form renumbers that form's entries only. Thus a lowered
//! segment kept across an edit to another form keeps every coordinate it
//! holds (#4373). The entries stay in one vector in push order. The
//! classification sweep pushes the top-level forms' own entries first, and
//! each form's descendants' entries after them. So a form's entries lie in a
//! few runs of the vector, and a lookup walks the form's runs. The
//! alternative was one vector per form, which allocates once per form at
//! least. The reversal is a sweep that pushes each form's entries in one run,
//! which makes each lookup one read. Witness:
//! `by_form::tests::an_entry_keeps_its_coordinate_whatever_another_form_pushes`.
//!
//! # A stretch names its first entry and its length
//!
//! A plan reads a list of entries as a [`FormStretch`]: the coordinate of
//! its first entry and how many entries follow it in push order. The entries
//! of a stretch are pushed one after another, so they stay next to each
//! other in the vector, and a read is one slice. A stretch can hold the
//! entries of two forms: the census sweep finds 551 such stretches among
//! 365,875 (#5604). Its first entry's form keys it all the same. The
//! alternative was a stretch per form, which splits a list a plan reads as
//! one. Witness:
//! `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`.

use alloc::vec::Vec;
use core::marker::PhantomData;

use anodized::spec;
use gandr_surface_syntax::LayoutBlock;

/// The coordinate of one entry in a [`ByForm`]: the form whose
/// classification pushed it, and its place among that form's entries.
///
/// # Specification
/// - requires: the store that gave it out reads it.
/// - ensures: the coordinate names one entry only relative to that store; it
///   does not authenticate where it was given out.
/// - provides: a key that an edit to another form leaves alone.
/// - executable: none — a coordinate does not hold the store needed to check
///   its bounds.
///
/// # Adequacy
/// - hypothesis: L3 — an entry keeps its coordinate whatever another form
///   pushes.
/// - witness: `by_form::tests::an_entry_keeps_its_coordinate_whatever_another_form_pushes`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormPlace
{
    /// The layout block of the form that pushed the entry.
    pub form: LayoutBlock,
    /// The entry's place among its form's entries, in push order.
    pub place: u32,
}

/// Entries one after another in a [`ByForm`]'s push order: the coordinate of
/// the first, and how many there are.
///
/// # Specification
/// - requires: the store that gave it out reads it.
/// - ensures: an empty stretch is the default one, whatever store and place it
///   came from.
/// - provides: a borrowed-store key rather than an owned list.
/// - executable: none — a stretch does not hold the store needed to check its
///   bounds.
///
/// # Adequacy
/// - hypothesis: L3 — a stretch reads the entries it was built over, whatever
///   another form pushes, and two adjacent stretches join.
/// - witness: `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormStretch
{
    /// The coordinate of the first entry.
    first: FormPlace,
    /// How many entries the stretch holds.
    length: u32,
}

/// A position in a [`ByForm`]'s vector of entries or of runs: what a stretch
/// is built from, before its first entry's coordinate is read.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct At(u32);

impl At
{
    /// The position after this one: where a store's mark lies after one
    /// push.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

impl From<usize> for At
{
    /// Read a vector's length as the position after its last entry,
    /// saturating past `u32::MAX`, beyond any store a lowering builds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(at: usize) -> Self
    {
        Self(u32::try_from(at).unwrap_or(u32::MAX))
    }
}

impl From<At> for usize
{
    /// Read the position back as an index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(at: At) -> Self
    {
        Self::try_from(at.0).unwrap_or(Self::MAX)
    }
}

/// Entries numbered within the form that pushed each, kept in one vector in
/// push order.
///
/// Each form keeps its count and its first and last run of the vector, and
/// each run names the next. A push extends its form's last run when that run
/// ends the vector, and starts a run otherwise. A lookup walks its form's
/// runs. No form allocates a vector of its own. The store pushes into the
/// form [`Self::enter`] names last. `Key` is the coordinate the store gives
/// out and reads, a [`FormPlace`] or a newtype over one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an entry pushed into a form answers at its place among that
///   form's entries, whatever other forms push before or after it.
/// - provides: the frames of a scope, and the lowering's flat stores.
/// - executable: none — a carrier; [`Self::push`] and [`Self::get`] carry the
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — two forms that push in turn keep each entry at its own
///   coordinate.
/// - witness: `by_form::tests::an_entry_keeps_its_coordinate_whatever_another_form_pushes`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByForm<Entry, Key = FormPlace>
{
    /// The entries, in push order.
    entries: Vec<Entry>,
    /// Each form's entries, by the form's block.
    forms: Vec<Segment>,
    /// The runs of `entries` that the forms' entries lie in, ascending by
    /// their first entry.
    runs: Vec<Run>,
    /// The form the next entry is pushed into.
    form: LayoutBlock,
    /// The coordinate the store gives out.
    key: PhantomData<fn(Key) -> Key>,
}

impl<Entry, Key> Default for ByForm<Entry, Key>
{
    /// A store holding no entries, pushing into the first block's form.
    ///
    /// # Specification
    /// trivial.
    fn default() -> Self
    {
        Self {
            entries: Vec::new(),
            forms: Vec::new(),
            runs: Vec::new(),
            form: LayoutBlock::default(),
            key: PhantomData,
        }
    }
}

/// One form's entries in a [`ByForm`]: how many, and the first and the last
/// run they lie in.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Segment
{
    /// How many entries the form holds.
    count: u32,
    /// The form's first run and its last, when it holds an entry.
    runs: Option<(At, At)>,
}

/// Consecutive entries of one form in a [`ByForm`].
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Run
{
    /// The position of the run's first entry.
    start: At,
    /// How many entries the run holds.
    length: u32,
    /// The form whose entries the run holds.
    form: LayoutBlock,
    /// The place of the run's first entry among its form's entries.
    base: u32,
    /// The form's next run, when the form holds one.
    next: Option<At>,
}

impl<Entry, Key: Copy + From<FormPlace> + Into<FormPlace>> ByForm<Entry, Key>
{
    /// Push the entries after this into `form`, the layout block of the form
    /// whose node the lowering reads now.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn enter(
        &mut self,
        form: LayoutBlock,
    )
    {
        self.form = form;
    }

    /// The form the next entry is pushed into.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> LayoutBlock
    {
        self.form
    }

    /// Push `entry` into the form [`Self::enter`] names, after every entry
    /// that form holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the store holds one more entry, and the coordinate returned
    ///   names the form and the count of entries it held before; every earlier
    ///   coordinate answers its entry as before.
    /// - provides: the one place an entry takes its coordinate.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one write to the form's count and one to its last run, or
    ///   one run pushed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `by_form::tests::an_entry_keeps_its_coordinate_whatever_another_form_pushes`
    #[spec(
        captures: before = (self.entries.len(), self.form, self.forms.get(usize::from(self.form)).map_or(0_u32, |segment| segment.count)),
        ensures: |ret| self.entries.len() == before.0.saturating_add(1) && Into::<FormPlace>::into(ret) == (FormPlace { form: before.1, place: before.2 }),
    )]
    pub fn push(
        &mut self,
        entry: Entry,
    ) -> Key
    {
        let form = self.form;
        let at = usize::from(form);
        if self.forms.len() <= at {
            self.forms.resize(at.saturating_add(1), Segment::default());
        }
        let start = At::from(self.entries.len());
        let fresh = At::from(self.runs.len());
        let mut place = 0_u32;
        if let Some(segment) = self.forms.get_mut(at) {
            place = segment.count;
            segment.count = place.saturating_add(1);
            let last = segment.runs.and_then(|(first, last)| {
                let run = self.runs.get_mut(usize::from(last))?;
                Some((first, run))
            });
            let run = Run {
                start,
                length: 1,
                form,
                base: place,
                next: None,
            };
            match last {
                Some((_, last)) if At(last.start.0.saturating_add(last.length)) == start => {
                    last.length = last.length.saturating_add(1);
                },
                Some((first, last)) => {
                    last.next = Some(fresh);
                    segment.runs = Some((first, fresh));
                    self.runs.push(run);
                },
                None => {
                    segment.runs = Some((fresh, fresh));
                    self.runs.push(run);
                },
            }
        }
        self.entries.push(entry);

        Key::from(FormPlace { form, place })
    }

    /// Where the entry `id` names lies in the vector, or nothing for a
    /// coordinate the store does not hold.
    ///
    /// # Specification
    /// - requires: nothing — any coordinate is admissible.
    /// - ensures: for a coordinate [`Self::push`] returned, the position of its
    ///   entry; nothing for a form or a place the store does not hold.
    /// - provides: the lookup every read of an entry makes.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one read of the form, then one step per run before the
    ///   entry's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `by_form::tests::an_entry_keeps_its_coordinate_whatever_another_form_pushes`
    #[spec(ensures: |ret| ret.is_none_or(|at| usize::from(at) < self.entries.len()))]
    pub fn position(
        &self,
        id: Key,
    ) -> Option<At>
    {
        self.find(id.into())
    }

    /// Where the entry `id` names lies in the vector, as [`Self::position`].
    ///
    /// # Specification
    /// trivial.
    fn find(
        &self,
        id: FormPlace,
    ) -> Option<At>
    {
        let (first, _) = self.forms.get(usize::from(id.form))?.runs?;
        let mut place = id.place;
        let mut at = Some(first);
        while let Some(run) = at.and_then(|run| self.runs.get(usize::from(run))) {
            if place < run.length {
                let found = At(run.start.0.saturating_add(place));
                return (usize::from(found) < self.entries.len()).then_some(found);
            }
            place = place.saturating_sub(run.length);
            at = run.next;
        }
        None
    }

    /// The coordinate of the entry at `at` in the vector, or nothing past the
    /// last entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the coordinate whose [`Self::position`] is `at`, for `at`
    ///   below the count of entries; nothing past it.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one binary search of the runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormStretch`].
    /// - witness: `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`
    #[spec(ensures: |ret| ret.is_none_or(|id| self.find(id) == Some(at)))]
    pub fn locate(
        &self,
        at: At,
    ) -> Option<FormPlace>
    {
        let after = self.runs.partition_point(|run| run.start <= at);
        let run = self.runs.get(after.checked_sub(1)?)?;
        let offset = at.0.checked_sub(run.start.0)?;
        (offset < run.length).then(|| FormPlace {
            form: run.form,
            place: run.base.saturating_add(offset),
        })
    }

    /// The position after the last entry: where the next entry goes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn mark(&self) -> At
    {
        At::from(self.entries.len())
    }

    /// The stretch of every entry pushed since [`Self::mark`] answered
    /// `start`.
    ///
    /// # Specification
    /// - requires: `start` is a mark of this store.
    /// - ensures: the stretch whose first entry sits at `start` and that runs
    ///   to the last entry; the default, empty stretch when no entry follows
    ///   `start`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormStretch`].
    /// - witness: `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`
    #[spec(ensures: |ret| self.read(ret).len() == self.entries.len().saturating_sub(usize::from(start)))]
    pub fn since(
        &self,
        start: At,
    ) -> FormStretch
    {
        let length = At::from(self.entries.len()).0.saturating_sub(start.0);
        match self.locate(start) {
            Some(first) if length > 0 => FormStretch { first, length },
            Some(_) | None => FormStretch::default(),
        }
    }

    /// The entries `stretch` names, in push order; nothing for a stretch this
    /// store does not hold whole.
    ///
    /// # Specification
    /// - requires: nothing — any stretch is admissible.
    /// - ensures: as [`Self::whole`], with the empty slice for a stretch that
    ///   runs past the last entry or names a place the store does not hold.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one lookup of the first entry, then one slice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormStretch`].
    /// - witness: `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`
    #[spec(ensures: |ret| ret.is_empty() || ret.len() == usize::try_from(stretch.length).unwrap_or(usize::MAX))]
    pub fn read(
        &self,
        stretch: FormStretch,
    ) -> &[Entry]
    {
        self.whole(stretch).unwrap_or(&[])
    }

    /// The entries `stretch` names, in push order, when this store holds
    /// every one of them; nothing otherwise.
    ///
    /// # Specification
    /// - requires: nothing — any stretch is admissible.
    /// - ensures: the slice of the vector from the first entry's position, as
    ///   long as the stretch; the empty slice for an empty stretch; nothing for
    ///   a stretch that runs past the last entry or names a place the store
    ///   does not hold.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one lookup of the first entry, then one slice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormStretch`].
    /// - witness: `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`
    #[spec(ensures: |ret| ret.is_none_or(|entries| entries.len() == usize::try_from(stretch.length).unwrap_or(usize::MAX)))]
    pub fn whole(
        &self,
        stretch: FormStretch,
    ) -> Option<&[Entry]>
    {
        if stretch.length == 0 {
            return Some(&[]);
        }
        let start = usize::from(self.find(stretch.first)?);
        let end = start.saturating_add(usize::try_from(stretch.length).unwrap_or(usize::MAX));
        self.entries.get(start .. end)
    }

    /// Where the first entry of `stretch` lies in the vector, or nothing for
    /// an empty stretch or one this store does not hold.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn first(
        &self,
        stretch: FormStretch,
    ) -> Option<At>
    {
        if stretch.length == 0 {
            return None;
        }
        self.find(stretch.first)
    }

    /// The stretch of `before`'s entries and then `after`'s, when `after`'s
    /// first entry follows `before`'s last in the vector; nothing otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a stretch that reads `before`'s entries then `after`'s, when
    ///   they lie next to each other or either is empty; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormStretch`].
    /// - witness: `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`
    #[spec(ensures: |ret| ret.is_none_or(|joined| self.read(joined).len() == self.read(before).len().saturating_add(self.read(after).len())))]
    pub fn join(
        &self,
        before: FormStretch,
        after: FormStretch,
    ) -> Option<FormStretch>
    {
        if before.length == 0 {
            return Some(after);
        }
        if after.length == 0 {
            return Some(before);
        }
        let ends = self.find(before.first)?.0.checked_add(before.length)?;
        (self.find(after.first)?.0 == ends).then(|| FormStretch {
            first: before.first,
            length: before.length.saturating_add(after.length),
        })
    }

    /// `stretch` without its first entries, up to and including the one at
    /// `last` in the vector.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stretch of the entries of `stretch` after the one at
    ///   `last`; the default, empty stretch when `last` lies outside `stretch`
    ///   or ends it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormStretch`].
    /// - witness: `by_form::tests::a_stretch_reads_its_entries_whatever_another_form_pushes`
    #[spec(ensures: |ret| self.read(ret).len() <= self.read(stretch).len())]
    pub fn after(
        &self,
        stretch: FormStretch,
        last: At,
    ) -> FormStretch
    {
        let Some(first) = self.find(stretch.first)
        else {
            return FormStretch::default();
        };
        let end = first.0.saturating_add(stretch.length);
        let next = last.0.saturating_add(1);
        if last < first || next >= end {
            return FormStretch::default();
        }
        self.since_until(At(next), At(end))
    }

    /// The stretch from `start` up to `end` in the vector.
    ///
    /// # Specification
    /// trivial.
    fn since_until(
        &self,
        start: At,
        end: At,
    ) -> FormStretch
    {
        let length = end.0.saturating_sub(start.0);
        match self.locate(start) {
            Some(first) if length > 0 => FormStretch { first, length },
            Some(_) | None => FormStretch::default(),
        }
    }

    /// The entry `id` names, or nothing for a coordinate the store does not
    /// hold.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn get(
        &self,
        id: Key,
    ) -> Option<&Entry>
    {
        self.entries.get(usize::from(self.position(id)?))
    }

    /// The entry `id` names, to change, or nothing for a coordinate the store
    /// does not hold.
    ///
    /// # Specification
    /// trivial.
    pub fn get_mut(
        &mut self,
        id: Key,
    ) -> Option<&mut Entry>
    {
        let at = self.position(id)?;
        self.entries.get_mut(usize::from(at))
    }

    /// The entry at `at` in the vector, of any form.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn at(
        &self,
        at: At,
    ) -> Option<&Entry>
    {
        self.entries.get(usize::from(at))
    }

    /// The entry at `at` in the vector, of any form, to change.
    ///
    /// # Specification
    /// trivial.
    pub fn at_mut(
        &mut self,
        at: At,
    ) -> Option<&mut Entry>
    {
        self.entries.get_mut(usize::from(at))
    }

    /// The entry pushed last, of any form.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn last(&self) -> Option<&Entry>
    {
        self.entries.last()
    }

    /// Every entry, in push order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn entries(&self) -> &[Entry]
    {
        &self.entries
    }

    /// The store with each entry read through `read`, every coordinate kept.
    ///
    /// # Specification
    /// trivial.
    pub fn map<Other, Read>(
        &self,
        read: Read,
    ) -> ByForm<Other, Key>
    where
        Read: FnMut(&Entry) -> Other,
    {
        ByForm {
            entries: self.entries.iter().map(read).collect(),
            forms: self.forms.clone(),
            runs: self.runs.clone(),
            form: self.form,
            key: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_surface_syntax::LayoutBlock;

    use super::ByForm;
    use super::FormPlace;

    #[test]
    fn an_entry_keeps_its_coordinate_whatever_another_form_pushes()
    {
        // A store whose forms push `pushes` in turn: each pair names the
        // form and the entry.
        let pushed = |pushes: &[(usize, char)]| {
            let mut store = ByForm::<char>::default();
            let mut ids = Vec::new();
            for &(form, entry) in pushes {
                store.enter(LayoutBlock::from(form));
                ids.push(store.push(entry));
            }
            (store, ids)
        };
        let (narrow, narrow_ids) = pushed(&[(1, 'a'), (2, 'x'), (2, 'y'), (1, 'b')]);
        let (wide, wide_ids) =
            pushed(&[(1, 'a'), (1, 'p'), (1, 'q'), (2, 'x'), (2, 'y'), (1, 'b')]);
        let second = |ids: &[FormPlace]| -> Vec<FormPlace> {
            ids.iter()
                .copied()
                .filter(|id| id.form == LayoutBlock::from(2_usize))
                .collect()
        };
        assert_eq!(
            second(&narrow_ids),
            second(&wide_ids),
            "two entries more in form 1 leave form 2's coordinates where they were"
        );
        for (store, ids) in [(&narrow, &narrow_ids), (&wide, &wide_ids)] {
            for (at, &id) in ids.iter().enumerate() {
                assert_eq!(
                    store.position(id).map(usize::from),
                    Some(at),
                    "a coordinate finds its entry"
                );
                assert_eq!(
                    store.locate(super::At::from(at)),
                    Some(id),
                    "a position reads back its coordinate"
                );
            }
        }
        assert_eq!(
            narrow.get(FormPlace {
                form: LayoutBlock::from(1_usize),
                place: 1
            }),
            Some(&'b'),
            "form 1's second entry lies in its second run"
        );
        assert_eq!(
            narrow.get(FormPlace {
                form: LayoutBlock::from(1_usize),
                place: 2
            }),
            None,
            "a place past the form's count names nothing"
        );
    }

    #[test]
    fn a_stretch_reads_its_entries_whatever_another_form_pushes()
    {
        let read = |before: &[(usize, char)]| {
            let mut store = ByForm::<char>::default();
            for &(form, entry) in before {
                store.enter(LayoutBlock::from(form));
                let _id = store.push(entry);
            }
            store.enter(LayoutBlock::from(3_usize));
            let start = store.mark();
            let _id = store.push('s');
            store.enter(LayoutBlock::from(4_usize));
            let _id = store.push('t');
            let stretch = store.since(start);
            (store, stretch)
        };
        let (narrow, narrow_stretch) = read(&[(1, 'a')]);
        let (wide, wide_stretch) = read(&[(1, 'a'), (1, 'b'), (2, 'c')]);
        assert_eq!(
            narrow_stretch, wide_stretch,
            "a stretch over forms 3 and 4 keeps its key when forms 1 and 2 push more"
        );
        assert_eq!(narrow.read(narrow_stretch), ['s', 't']);
        assert_eq!(
            wide.read(wide_stretch),
            ['s', 't'],
            "it reads the entries of both forms"
        );
        assert_eq!(
            narrow.since(narrow.mark()),
            super::FormStretch::default(),
            "a stretch of no entry is the empty one"
        );
        assert!(narrow.read(super::FormStretch::default()).is_empty());
        let mut store = ByForm::<char>::default();
        store.enter(LayoutBlock::from(1_usize));
        let first = store.mark();
        let p = store.push('p');
        let second = store.mark();
        let _q = store.push('q');
        let _r = store.push('r');
        let (head, tail) = (store.since_until(first, second), store.since(second));
        let joined = store.join(head, tail).expect("adjacent stretches join");
        assert_eq!(store.read(joined), ['p', 'q', 'r']);
        assert_eq!(
            store.join(tail, head),
            None,
            "a stretch before another does not join after it"
        );
        let at = store.position(p).expect("`p` lies in the store");
        assert_eq!(
            store.read(store.after(joined, at)),
            ['q', 'r'],
            "the entries after one read on"
        );
    }
}
