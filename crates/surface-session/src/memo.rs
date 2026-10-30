//! A bounded memo of entries held under their content: the one ring every
//! process store of this crate keeps its results in.
//!
//! A [`Memo`] holds at most `HELD` entries, each stamped with the tick of the
//! memo's clock it was last asked for at. A question ranks the entries its key
//! admits and answers the highest; keeping an entry replaces those under the
//! same key, then lets the entry asked for longest ago go past the bound. The
//! key is the entry's content, so nothing a memo answers is keyed by a name, a
//! position or a session.

use alloc::vec::Vec;

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
/// - executable: none — a store; [`Memo::find`] and [`Memo::keep`] carry the
///   executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a memo answers what it kept under the key asked, and past
///   its bound it lets the entry asked for longest ago go.
/// - witness: `memo::tests::past_its_bound_a_memo_lets_the_entry_asked_for_longest_ago_go`
#[derive(Debug)]
pub struct Memo<Entry, const HELD: usize>
{
    /// The entries, in no order.
    held: Vec<Stamped<Entry>>,
    /// Ticks once per question.
    clock: u64,
}

impl<Entry, const HELD: usize> Memo<Entry, HELD>
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
            held: Vec::new(),
            clock: 0_u64,
        }
    }

    /// The entry `rank` ranks highest among those it admits, now the one
    /// asked for last.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: of the held entries `rank` answers a rank for, one with the
    ///   highest rank, its tick now the clock's; `None` when `rank` admits
    ///   none.
    /// - provides: the entry a store answers a question with.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the rank is the caller's; the witnesses ask a memo
    ///   under exact and ranked keys.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Memo`].
    /// - witness: `memo::tests::a_memo_answers_the_highest_ranked_entry_its_key_admits`
    pub fn find<Rank, Ranking>(
        &mut self,
        mut rank: Ranking,
    ) -> Option<&Entry>
    where
        Rank: Ord,
        Ranking: FnMut(&Entry) -> Option<Rank>,
    {
        self.clock = self.clock.saturating_add(1);
        let now = self.clock;
        let found = self
            .held
            .iter_mut()
            .filter_map(|held| rank(&held.entry).map(|ranked| (ranked, held)))
            .max_by(|left, right| left.0.cmp(&right.0))?
            .1;
        found.used = now;
        Some(&found.entry)
    }

    /// Hold `entry` in place of every held entry `same` reads as under its
    /// key, letting the one asked for longest ago go past `HELD`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no held entry but `entry` is one `same` reads as under
    ///   `entry`'s key; no more than `HELD` is held, and `entry` stays while
    ///   `HELD` is one or more.
    /// - provides: the record a later [`Memo::find`] answers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Memo`].
    /// - witness: `memo::tests::past_its_bound_a_memo_lets_the_entry_asked_for_longest_ago_go`
    /// - witness: `memo::tests::keeping_under_a_held_key_replaces_the_entry`
    #[spec(ensures: self.held.len() <= HELD)]
    pub fn keep<Same>(
        &mut self,
        entry: Entry,
        mut same: Same,
    ) where
        Same: FnMut(&Entry, &Entry) -> bool,
    {
        self.clock = self.clock.saturating_add(1);
        let now = self.clock;
        self.held.retain(|held| !same(&held.entry, &entry));
        self.held.push(Stamped { entry, used: now });
        while self.held.len() > HELD {
            let oldest = self
                .held
                .iter()
                .enumerate()
                .min_by_key(|&(_, held)| held.used)
                .map(|(index, _)| index);
            let Some(oldest) = oldest
            else {
                break;
            };
            let _gone = self.held.swap_remove(oldest);
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::Memo;

    /// A test entry's key.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Key(char);

    /// A test entry's value, which a ranked question ranks by.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Value(u32);

    /// A value under its key.
    #[derive(Debug)]
    struct Pair
    {
        /// The key it is kept and asked under.
        key: Key,
        /// The value kept.
        value: Value,
    }

    /// A memo of two pairs.
    type Pairs = Memo<Pair, 2>;

    /// The value `memo` answers under `key`.
    ///
    /// # Specification
    /// trivial.
    fn under(
        memo: &mut Pairs,
        key: Key,
    ) -> Option<Value>
    {
        memo.find(|pair| (pair.key == key).then_some(()))
            .map(|pair| pair.value)
    }

    /// Hold `value` under `key` in `memo`.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        memo: &mut Pairs,
        key: Key,
        value: Value,
    )
    {
        memo.keep(Pair { key, value }, |held, kept| held.key == kept.key);
    }

    #[test]
    fn past_its_bound_a_memo_lets_the_entry_asked_for_longest_ago_go()
    {
        let mut memo = Pairs::new();
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
    fn keeping_under_a_held_key_replaces_the_entry()
    {
        let mut memo = Pairs::new();
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
        let mut memo = Pairs::new();
        keep(&mut memo, Key('a'), Value(1));
        keep(&mut memo, Key('b'), Value(2));
        let highest = memo
            .find(|pair| (pair.value <= Value(2)).then_some(pair.value))
            .map(|pair| pair.key);
        assert_eq!(
            highest,
            Some(Key('b')),
            "of the admitted entries the highest rank answers"
        );
        let none = memo
            .find(|pair| (pair.value > Value(2)).then_some(pair.value))
            .map(|pair| pair.key);
        assert_eq!(none, None, "a key no entry meets finds none");
    }
}
