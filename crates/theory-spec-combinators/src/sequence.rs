//! Combinators over a sequence a function appends to, inserts into or
//! overwrites.
//!
//! They read what the sequence gained since a captured mark, whether it grew
//! by one element, and whether it stays ordered around the point a change
//! wrote at.

use anodized::spec;

use crate::holds::Holds;

/// A position in a sequence: its length captured before a change, or the index
/// a change wrote at.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Mark(usize);

impl Mark
{
    /// The mark at the end of `items`: its length, captured before a change.
    ///
    /// # Specification
    /// - ensures: the mark's position is `items.len()`.
    /// - panics: none.
    ///
    /// # Clause cost
    /// - bound: reads the length of `items` and no element.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over every length up to the witness's bound, the
    ///   suffix [`appended`] returns at the captured mark is empty; a mark at
    ///   any other position returns a nonempty suffix or one that ends early.
    /// - witness: `sequence::tests::appended_reads_no_element`
    #[spec(ensures: |ret| usize::from(ret) == items.len())]
    #[inline]
    #[must_use]
    pub fn of<T>(items: &[T]) -> Self
    {
        Self(items.len())
    }
}

impl From<usize> for Mark
{
    /// Wraps a position computed elsewhere, such as an insertion point.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: constant; wraps the position it is handed.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<Mark> for usize
{
    /// Unwraps a mark to its position.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: constant; unwraps the position.
    #[inline]
    fn from(mark: Mark) -> Self
    {
        mark.0
    }
}

/// The elements of `items` at or after `mark`: what the sequence gained since
/// the mark was captured.
///
/// # Specification
/// - ensures: the result is the suffix of `items` that starts at `mark`; it is
///   empty when `items` is no longer than `mark`. It borrows from `items`, so
///   it ends where `items` ends.
/// - provides: the elements a clause may walk after an append, at a cost
///   bounded by the number appended.
/// - panics: none.
///
/// # Clause cost
/// - bound: reads no element; the slice it returns holds only the elements at
///   or after `mark`.
///
/// # Adequacy
/// - hypothesis: L3 — marks before, at and past the end of an empty and a
///   three-element sequence. Returning the whole sequence, a suffix starting
///   one place early or late, or a slice of a copy changes the result's length
///   or where it ends. The bound is a property over every length and mark up to
///   the witness's bound: no element is compared and the result borrows the
///   input's tail.
/// - witness: `sequence::tests::appended_is_the_suffix_at_the_mark`
/// - witness: `sequence::tests::appended_reads_no_element`
#[spec(ensures: |ret| ret.len() == items.len().saturating_sub(usize::from(mark))
    && core::ptr::eq(ret.as_ptr_range().end, items.as_ptr_range().end))]
#[inline]
#[must_use]
pub fn appended<'items, T>(
    items: &'items [T],
    mark: Mark,
) -> &'items [T]
{
    let start = usize::from(mark).min(items.len());
    items.get(start ..).unwrap_or_default()
}

/// Whether `items` grew by exactly one element since `mark`, and that element
/// equals `value`.
///
/// # Specification
/// - ensures: holds exactly when `items` is one element longer than `mark` and
///   its last element equals `value`.
/// - panics: none.
///
/// # Clause cost
/// - bound: reads the length of `items` and compares its last element once, and
///   once more when its own clause is checked.
///
/// # Adequacy
/// - hypothesis: L3 — one push of the expected value holds; the same last
///   element after two pushes, a different last element after one push, no
///   growth and a shrink each fail, so a claim that checks only the last
///   element or only the length is refuted. The bound is a property over every
///   length up to the witness's bound: at most one comparison, two in an
///   enforcing build.
/// - witness: `sequence::tests::pushed_holds_for_exactly_one_new_last_element`
/// - witness: `sequence::tests::pushed_compares_at_most_one_element`
#[spec(ensures: |ret| bool::from(ret)
    == (usize::from(mark).checked_add(1) == Some(items.len()) && items.last() == Some(value)))]
#[inline]
#[must_use]
pub fn pushed<T>(
    items: &[T],
    mark: Mark,
    value: &T,
) -> Holds
where
    T: PartialEq,
{
    Holds::from(
        usize::from(mark).checked_add(1) == Some(items.len()) && items.last() == Some(value),
    )
}

/// Whether `items` is strictly increasing across the element at `at`: that
/// element exists, the element before it, if any, is less than it, and the
/// element after it, if any, is greater.
///
/// # Specification
/// - ensures: holds exactly when `items` has an element at `at`, the element
///   before it is less than it or absent, and the element after it is greater
///   than it or absent. When `items` was strictly increasing before a single
///   insertion or overwrite at `at`, the answer is whether all of `items` is
///   strictly increasing after it.
/// - panics: none.
///
/// # Clause cost
/// - bound: reads the element at `at` and its two neighbours, with at most two
///   comparisons, and two more when its own clause is checked.
///
/// # Adequacy
/// - hypothesis: L3 — a sequence out of order away from `at` but ordered around
///   it holds, refuting a whole-sequence check; an equal neighbour fails,
///   refuting a non-strict check; the first and last positions read one
///   neighbour; a position past the end and an empty sequence fail. The bound
///   is a property over every length and position up to the witness's bound: at
///   most two comparisons, four in an enforcing build.
/// - witness: `sequence::tests::sorted_around_reads_only_the_neighbours`
/// - witness: `sequence::tests::sorted_around_compares_at_most_two_elements`
#[spec(ensures: |ret| bool::from(ret) == {
    let at = usize::from(at);
    items.get(at).is_some_and(|here| {
        at.checked_sub(1).and_then(|before| items.get(before)).is_none_or(|before| before < here)
            && at.checked_add(1).and_then(|after| items.get(after)).is_none_or(|after| here < after)
    })
})]
#[inline]
#[must_use]
pub fn sorted_around<T>(
    items: &[T],
    at: Mark,
) -> Holds
where
    T: Ord,
{
    let at = usize::from(at);
    let Some(here) = items.get(at)
    else {
        return Holds::from(false);
    };
    let before = at
        .checked_sub(1)
        .and_then(|before| items.get(before))
        .is_none_or(|before| before < here);
    let after = at
        .checked_add(1)
        .and_then(|after| items.get(after))
        .is_none_or(|after| here < after);
    Holds::from(before && after)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use core::cell::Cell;
    use core::cmp::Ordering;

    use anodized::spec;

    use super::Mark;
    use super::appended;
    use super::pushed;
    use super::sorted_around;

    /// The largest sequence the bound witnesses build.
    const LONGEST: usize = 256;

    /// How many times a combinator's comparisons run: once, and once more for
    /// its own clause in an enforcing build.
    const CHECKED: usize = if cfg!(anodized_panic) { 2 } else { 1 };

    /// An element whose comparisons add to a shared tally.
    #[derive(Debug)]
    struct Counted<'tally>
    {
        /// What the element compares by.
        value: usize,
        /// The comparisons made so far, shared by every element of a sequence.
        tally: &'tally Cell<usize>,
    }

    impl PartialEq for Counted<'_>
    {
        /// Equal values, counting the comparison.
        ///
        /// # Specification
        /// - ensures: returns whether the two values are equal and adds one to
        ///   the shared tally.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the bound witnesses read the tally after calls
        ///   that compare a known number of times; an uncounted comparison
        ///   would let a walking combinator pass.
        /// - witness: `sequence::tests::pushed_compares_at_most_one_element`
        #[spec(captures: before = self.tally.get(),
            ensures: |ret| ret == (self.value == other.value) && self.tally.get() == before.saturating_add(1))]
        fn eq(
            &self,
            other: &Self,
        ) -> bool
        {
            self.tally.set(self.tally.get().saturating_add(1));
            self.value == other.value
        }
    }

    impl Eq for Counted<'_>
    {
    }

    impl PartialOrd for Counted<'_>
    {
        /// The total order of [`Ord::cmp`].
        ///
        /// # Specification
        /// trivial.
        fn partial_cmp(
            &self,
            other: &Self,
        ) -> Option<Ordering>
        {
            Some(self.cmp(other))
        }
    }

    impl Ord for Counted<'_>
    {
        /// The order of the values, counting the comparison.
        ///
        /// # Specification
        /// - ensures: returns the order of the two values and adds one to the
        ///   shared tally.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the bound witnesses read the tally after calls
        ///   that compare a known number of times; an uncounted comparison
        ///   would let a walking combinator pass.
        /// - witness: `sequence::tests::sorted_around_compares_at_most_two_elements`
        #[spec(captures: before = self.tally.get(),
            ensures: |ret| ret == self.value.cmp(&other.value) && self.tally.get() == before.saturating_add(1))]
        fn cmp(
            &self,
            other: &Self,
        ) -> Ordering
        {
            self.tally.set(self.tally.get().saturating_add(1));
            self.value.cmp(&other.value)
        }
    }

    #[test]
    fn appended_is_the_suffix_at_the_mark()
    {
        let items = [1_u8, 2, 3];
        let end = items.as_ptr_range().end;
        let at = |position: usize| appended(&items, Mark::from(position));
        assert_eq!(at(0), [1, 2, 3]);
        assert_eq!(at(1), [2, 3]);
        assert_eq!(at(2), [3]);
        assert!(at(3).is_empty());
        assert!(at(5).is_empty());
        for position in 0 ..= 5 {
            assert!(core::ptr::eq(at(position).as_ptr_range().end, end));
        }
        let empty: [u8; 0] = [];
        assert!(appended(&empty, Mark::from(0)).is_empty());
        assert!(appended(&empty, Mark::of(&items)).is_empty());
    }

    #[test]
    fn appended_reads_no_element()
    {
        let tally = Cell::new(0_usize);
        let mut items = Vec::new();
        for length in 0 ..= LONGEST {
            let mark = Mark::of(&items);
            assert_eq!(usize::from(mark), length);
            assert!(appended(&items, mark).is_empty());
            for position in 0 ..= length.saturating_add(2) {
                let suffix = appended(&items, Mark::from(position));
                assert_eq!(suffix.len(), length.saturating_sub(position));
                assert!(core::ptr::eq(
                    suffix.as_ptr_range().end,
                    items.as_ptr_range().end
                ));
            }
            items.push(Counted {
                value: length,
                tally: &tally,
            });
        }
        assert_eq!(tally.get(), 0);
    }

    #[test]
    fn pushed_holds_for_exactly_one_new_last_element()
    {
        let two = Mark::from(2);
        assert!(bool::from(pushed(&[1_u8, 2, 3], two, &3)));
        assert!(!bool::from(pushed(&[1_u8, 2, 3], two, &4)));
        assert!(!bool::from(pushed(&[1_u8, 2, 3, 3], two, &3)));
        assert!(!bool::from(pushed(&[1_u8, 2], two, &2)));
        assert!(!bool::from(pushed(&[1_u8], two, &1)));
        let empty: &[u8] = &[];
        assert!(!bool::from(pushed(empty, Mark::from(usize::MAX), &0)));
    }

    #[test]
    fn pushed_compares_at_most_one_element()
    {
        let tally = Cell::new(0_usize);
        let mut items = Vec::new();
        for length in 0 ..= LONGEST {
            let mark = Mark::of(&items);
            let value = Counted {
                value: length,
                tally: &tally,
            };
            items.push(Counted {
                value: length,
                tally: &tally,
            });
            tally.set(0);
            assert!(bool::from(pushed(&items, mark, &value)));
            assert!(tally.get() <= CHECKED);
            for position in 0 ..= length.saturating_add(1) {
                tally.set(0);
                let _answer = pushed(&items, Mark::from(position), &value);
                assert!(tally.get() <= CHECKED);
            }
        }
    }

    #[test]
    fn sorted_around_reads_only_the_neighbours()
    {
        let holds = |items: &[u8], at: usize| bool::from(sorted_around(items, Mark::from(at)));
        assert!(holds(&[5, 1, 2, 3], 2));
        assert!(!holds(&[5, 1, 2, 3], 1));
        assert!(!holds(&[1, 2, 2], 2));
        assert!(!holds(&[1, 2, 2], 1));
        assert!(holds(&[1, 2], 0));
        assert!(holds(&[1, 2], 1));
        assert!(holds(&[7], 0));
        assert!(!holds(&[1, 2, 3], 3));
        assert!(!holds(&[], 0));
    }

    #[test]
    fn sorted_around_compares_at_most_two_elements()
    {
        let tally = Cell::new(0_usize);
        let mut items = Vec::new();
        for length in 0 ..= LONGEST {
            for position in 0 ..= length {
                tally.set(0);
                let answer = sorted_around(&items, Mark::from(position));
                assert!(tally.get() <= CHECKED.saturating_mul(2));
                assert_eq!(bool::from(answer), position < length);
            }
            items.push(Counted {
                value: length,
                tally: &tally,
            });
        }
    }
}
