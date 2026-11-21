//! A bounded memo of entries held under their content: the one ring every
//! process store of the surface keeps its results in.
//!
//! A [`Memo`] holds at most `HELD` entries, each under a key and stamped with
//! the tick of the memo's clock it was last asked for at. A question names a
//! key, ranks the entries held under it and answers the highest; keeping an
//! entry replaces those under its key it reads as the same, then lets the
//! entry asked for longest ago go past the bound. The key is the entry's
//! content, so nothing a memo answers is keyed by a name, a position or a
//! session.
//!
//! The entries sit in a map by key, so a question costs one lookup and a pass
//! over the few entries under its key. The alternative was one list of every
//! entry, which a question scans whole; it reverses for a memo of a handful of
//! entries, where the scan and the lookup cost alike.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::borrow::Borrow;

use anodized::spec;

/// One entry, beside the tick it was last asked for at.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Stamped<Entry>
{
    /// The entry.
    entry: Entry,
    /// The tick of the memo's clock it was last asked for at.
    used: u64,
}

/// At most `HELD` entries under their content, letting the one asked for
/// longest ago go.
///
/// # Specification
/// - requires: nothing.
/// - ensures: never holds more than `HELD` once a [`Memo::keep`] returns.
/// - panics: none.
/// - executable: none — a store; [`Memo::find`], [`Memo::keep`] and
///   [`Memo::forget`] carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a memo answers what it kept under the key asked, and past
///   its bound it lets the entry asked for longest ago go.
/// - witness: `memo::tests::past_its_bound_a_memo_lets_the_entry_asked_for_longest_ago_go`
#[derive(Debug)]
pub struct Memo<Key, Entry, const HELD: usize>
{
    /// The entries under each key, in no order.
    held: BTreeMap<Key, Vec<Stamped<Entry>>>,
    /// How many entries `held` holds.
    count: usize,
    /// Ticks once per question and once per keep.
    clock: u64,
}

impl<Key, Entry, const HELD: usize> Default for Memo<Key, Entry, HELD>
{
    /// A memo holding nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl<Key, Entry, const HELD: usize> Memo<Key, Entry, HELD>
{
    /// A memo holding nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            held: BTreeMap::new(),
            count: 0_usize,
            clock: 0_u64,
        }
    }

    /// The entry under `key` that `rank` ranks highest among those it admits,
    /// now the one asked for last.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: of the entries held under `key` that `rank` answers a rank
    ///   for, one with the highest rank, its tick now the clock's; `None` when
    ///   `rank` admits none.
    /// - provides: the entry a store answers a question with.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the rank is the caller's; the witnesses ask a memo
    ///   under exact and ranked questions.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Memo`].
    /// - witness: `memo::tests::a_memo_answers_the_highest_ranked_entry_its_key_admits`
    #[inline]
    pub fn find<Query, Rank, Ranking>(
        &mut self,
        key: &Query,
        mut rank: Ranking,
    ) -> Option<&Entry>
    where
        Key: Borrow<Query> + Ord,
        Query: Ord + ?Sized,
        Rank: Ord,
        Ranking: FnMut(&Entry) -> Option<Rank>,
    {
        self.clock = self.clock.saturating_add(1);
        let now = self.clock;
        let found = self
            .held
            .get_mut(key)?
            .iter_mut()
            .filter_map(|held| rank(&held.entry).map(|ranked| (ranked, held)))
            .max_by(|left, right| left.0.cmp(&right.0))?
            .1;
        found.used = now;
        Some(&found.entry)
    }

    /// Hold `entry` under `key` in place of every entry held there that `same`
    /// reads as `entry`, letting the one asked for longest ago go past `HELD`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no entry under `key` but `entry` is one `same` reads as
    ///   `entry`; no more than `HELD` is held, and `entry` stays while `HELD`
    ///   is one or more.
    /// - provides: the record a later [`Memo::find`] answers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Memo`].
    /// - witness: `memo::tests::past_its_bound_a_memo_lets_the_entry_asked_for_longest_ago_go`
    /// - witness: `memo::tests::keeping_under_a_held_key_replaces_the_entry`
    /// - witness: `memo::tests::past_its_bound_a_key_holding_two_entries_loses_only_the_older`
    #[spec(ensures: self.count <= HELD)]
    #[inline]
    pub fn keep<Same>(
        &mut self,
        key: Key,
        entry: Entry,
        mut same: Same,
    ) where
        Key: Ord,
        Same: FnMut(&Entry, &Entry) -> bool,
    {
        self.clock = self.clock.saturating_add(1);
        let now = self.clock;
        let held = self.held.entry(key).or_default();
        let before = held.len();
        held.retain(|held| !same(&held.entry, &entry));
        let replaced = before.saturating_sub(held.len());
        held.push(Stamped { entry, used: now });
        self.count = self.count.saturating_sub(replaced).saturating_add(1);
        while self.count > HELD {
            let Some(oldest) = self.held.values().flatten().map(|held| held.used).min()
            else {
                break;
            };
            self.retain(|_, held| held.used != oldest);
        }
    }

    /// Let go every entry `gone` reads as gone under its key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no entry `gone` answers true for is held; every other entry
    ///   is held as it was.
    /// - provides: what a store lets go when what its entries stand for
    ///   changes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Memo`].
    /// - witness: `memo::tests::a_forgotten_entry_is_no_longer_found`
    #[spec(
        captures: [count = self.count],
        ensures: self.count <= count,
    )]
    #[inline]
    pub fn forget<Gone>(
        &mut self,
        mut gone: Gone,
    ) where
        Key: Ord,
        Gone: FnMut(&Key, &Entry) -> bool,
    {
        self.retain(|key, held| !gone(key, &held.entry));
    }

    /// Keep the entries `kept` answers true for, counting them.
    ///
    /// # Specification
    /// trivial.
    fn retain<Kept>(
        &mut self,
        mut kept: Kept,
    ) where
        Key: Ord,
        Kept: FnMut(&Key, &Stamped<Entry>) -> bool,
    {
        let mut count = 0_usize;
        self.held.retain(|key, held| {
            held.retain(|held| kept(key, held));
            count = count.saturating_add(held.len());
            !held.is_empty()
        });
        self.count = count;
    }
}

#[cfg(test)]
mod tests
{
    use super::Memo;

    /// A test entry's key.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Key(char);

    /// A test entry's value, which a ranked question ranks by.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Value(u32);

    /// A memo of two values.
    type Values = Memo<Key, Value, 2>;

    /// The value `memo` answers under `key`.
    ///
    /// # Specification
    /// trivial.
    fn under(
        memo: &mut Values,
        key: Key,
    ) -> Option<Value>
    {
        memo.find(&key, |_| Some(())).copied()
    }

    /// Hold `value` under `key` in `memo`, in place of any held there.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        memo: &mut Values,
        key: Key,
        value: Value,
    )
    {
        memo.keep(key, value, |_, _| true);
    }

    #[test]
    fn past_its_bound_a_memo_lets_the_entry_asked_for_longest_ago_go()
    {
        let mut memo = Values::new();
        keep(&mut memo, Key('a'), Value(1));
        keep(&mut memo, Key('b'), Value(2));
        assert_eq!(
            under(&mut memo, Key('a')),
            Some(Value(1)),
            "a question renews the entry it answers"
        );
        keep(&mut memo, Key('c'), Value(3));
        assert_eq!(
            under(&mut memo, Key('b')),
            None,
            "the entry asked for longest ago goes"
        );
        assert_eq!(
            under(&mut memo, Key('a')),
            Some(Value(1)),
            "the entry asked for since stays"
        );
        assert_eq!(
            under(&mut memo, Key('c')),
            Some(Value(3)),
            "the entry just kept stays"
        );
    }

    #[test]
    fn past_its_bound_a_key_holding_two_entries_loses_only_the_older()
    {
        let mut memo = Values::new();
        memo.keep(Key('a'), Value(1), |_, _| false);
        memo.keep(Key('a'), Value(2), |_, _| false);
        keep(&mut memo, Key('b'), Value(3));
        assert_eq!(
            memo.find(&Key('a'), |value| (*value == Value(1)).then_some(())),
            None,
            "the entry asked for longest ago goes"
        );
        assert_eq!(
            (
                memo.find(&Key('a'), |value| Some(*value)).copied(),
                under(&mut memo, Key('b'))
            ),
            (Some(Value(2)), Some(Value(3))),
            "the newer entry under its key stays beside the one just kept"
        );
    }

    #[test]
    fn keeping_under_a_held_key_replaces_the_entry()
    {
        let mut memo = Values::new();
        keep(&mut memo, Key('a'), Value(1));
        keep(&mut memo, Key('b'), Value(2));
        keep(&mut memo, Key('a'), Value(3));
        assert_eq!(
            under(&mut memo, Key('a')),
            Some(Value(3)),
            "the later entry answers"
        );
        assert_eq!(
            under(&mut memo, Key('b')),
            Some(Value(2)),
            "a replacement lets no other entry go"
        );
    }

    #[test]
    fn a_memo_answers_the_highest_ranked_entry_its_key_admits()
    {
        let mut memo = Values::new();
        memo.keep(Key('a'), Value(1), |_, _| false);
        memo.keep(Key('a'), Value(2), |_, _| false);
        let highest = memo.find(&Key('a'), |value| (*value <= Value(2)).then_some(*value));
        assert_eq!(
            highest,
            Some(&Value(2)),
            "of the admitted entries the highest rank answers"
        );
        let none = memo.find(&Key('a'), |value| (*value > Value(2)).then_some(*value));
        assert_eq!(none, None, "a rank no entry meets finds none");
        assert_eq!(
            memo.find(&Key('b'), |value| Some(*value)),
            None,
            "a key no entry is held under finds none"
        );
    }

    #[test]
    fn a_forgotten_entry_is_no_longer_found()
    {
        let mut memo = Values::new();
        keep(&mut memo, Key('a'), Value(1));
        keep(&mut memo, Key('b'), Value(2));
        memo.forget(|&key, _| key == Key('a'));
        assert_eq!(under(&mut memo, Key('a')), None, "the forgotten entry goes");
        keep(&mut memo, Key('c'), Value(3));
        assert_eq!(
            (under(&mut memo, Key('b')), under(&mut memo, Key('c'))),
            (Some(Value(2)), Some(Value(3))),
            "a forgotten entry frees its place, so the next keep lets nothing go"
        );
    }
}
