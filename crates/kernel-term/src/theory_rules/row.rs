//! The row of theories a rule fires under, and how two rules' rows compose
//! at a critical pair.
//!
//! A row is a set of theories. A rule's row holds exactly the theories it
//! names, or at least them; at least no theory is every row, the row of a
//! rule stated under none. Rows are ordered by inclusion of the rows they
//! describe, and two rows' [`RuleRow::meet`] is their unifier: the rows both
//! describe, as one row, or none where they share no row.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;

/// A theory a rule's row names, by its place among the theories a
/// presentation's rows name.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RowLabel(u32);

impl From<u32> for RowLabel
{
    /// The theory at `place`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: u32) -> Self
    {
        Self(place)
    }
}

/// How a rule's row holds the theories it names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum RowExtent
{
    /// Exactly them: `under [S, C]`.
    Exactly,
    /// At least them: `under [S, C | r]`.
    #[default]
    AtLeast,
}

/// The rows a rule fires in: those holding exactly, or at least, its
/// theories. The default, at least no theory, is every row.
///
/// `a <= b` when every row `a` describes `b` describes too: a rule under `b`
/// fires wherever `a` holds.
///
/// A row is the program's, never a position's: no operation's port carries a
/// row of its own and a rewrite keeps its program's row, so a rule's row is
/// the same at every match and along every rewrite, and two rules' rows
/// compose at an overlap by [`RuleRow::meet`] alone.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct RuleRow
{
    /// The theories named, ascending, each once.
    labels: Box<[RowLabel]>,
    /// Whether the row holds exactly them or at least them.
    extent: RowExtent,
}

impl RuleRow
{
    /// The row holding `labels`, exactly or at least as `extent` says.
    ///
    /// # Specification
    /// - ensures: the row's theories are `labels` ascending, each once, and its
    ///   extent is `extent`.
    /// - panics: none.
    /// - executable: none — the labels are private, and the order and meet the
    ///   witness observes read them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row written with a theory twice and out of order is
    ///   the row written once in order.
    /// - witness: `theory_rules::tests::rows_compose_as_their_unifier_2448`
    #[inline]
    #[must_use]
    pub fn new<L>(
        labels: L,
        extent: RowExtent,
    ) -> Self
    where
        L: IntoIterator<Item = RowLabel>,
    {
        let mut labels: Vec<RowLabel> = labels.into_iter().collect();
        labels.sort_unstable();
        labels.dedup();
        Self {
            labels: labels.into(),
            extent,
        }
    }

    /// The rows both `self` and `other` describe, as one row; [`None`] where
    /// they share none.
    ///
    /// # Specification
    /// - ensures: on [`Some`], the greatest row below both; two rows open
    ///   through their tails meet at the union of their theories, an open row
    ///   meets a closed one holding its theories at the closed one, two closed
    ///   rows meet only when equal; otherwise [`None`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two open rows, an open row inside and outside a
    ///   closed one, and two closed rows equal and apart; over every row three
    ///   theories write, the meet commutes, is idempotent and associates, and a
    ///   row lies below two rows exactly when it lies below their meet.
    /// - witness: `theory_rules::tests::rows_compose_as_their_unifier_2448`
    /// - witness: `theory_rules::tests::rows_meet_as_a_semilattice_2448`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|met| met <= self && met <= other))]
    #[inline]
    #[must_use]
    pub fn meet(
        &self,
        other: &Self,
    ) -> Option<Self>
    {
        match (self.extent, other.extent) {
            (RowExtent::AtLeast, RowExtent::AtLeast) => Some(Self {
                labels: union(&self.labels, &other.labels),
                extent: RowExtent::AtLeast,
            }),
            (RowExtent::AtLeast, RowExtent::Exactly) => missing(&self.labels, &other.labels)
                .is_none()
                .then(|| other.clone()),
            (RowExtent::Exactly, RowExtent::AtLeast) => missing(&other.labels, &self.labels)
                .is_none()
                .then(|| self.clone()),
            (RowExtent::Exactly, RowExtent::Exactly) => {
                (self.labels == other.labels).then(|| self.clone())
            },
        }
    }
}

impl PartialOrd for RuleRow
{
    /// Inclusion of the rows described: [`Ordering::Less`] when every row
    /// `self` describes `other` describes and not the converse.
    ///
    /// # Specification
    /// - ensures: [`Ordering::Equal`] exactly when the two are equal; a row is
    ///   below an open one when it holds at least that one's theories, and
    ///   below a closed one only when it is that closed row.
    /// - panics: none.
    /// - executable: none — the order is what [`RuleRow::meet`]'s predicate
    ///   states its result by.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed row below the open row of its theories, an
    ///   open row below the open row of fewer, and two closed rows apart.
    /// - witness: `theory_rules::tests::rows_compose_as_their_unifier_2448`
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        let within = |row: &Self, outer: &Self| match outer.extent {
            RowExtent::AtLeast => missing(&outer.labels, &row.labels).is_none(),
            RowExtent::Exactly => row.extent == RowExtent::Exactly && row.labels == outer.labels,
        };
        match (within(self, other), within(other, self)) {
            (true, true) => Some(Ordering::Equal),
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => None,
        }
    }
}

/// The first of `labels` that `from` does not hold; both ascending.
///
/// # Specification
/// trivial.
fn missing(
    labels: &[RowLabel],
    from: &[RowLabel],
) -> Option<RowLabel>
{
    let mut from = from.iter().peekable();
    labels.iter().copied().find(|&label| {
        while from.next_if(|&&held| held < label).is_some() {}
        from.next_if_eq(&&label).is_none()
    })
}

/// The labels of `first` and `second`, ascending, each once; both ascending.
///
/// # Specification
/// trivial.
fn union(
    first: &[RowLabel],
    second: &[RowLabel],
) -> Box<[RowLabel]>
{
    let mut out = Vec::with_capacity(first.len().saturating_add(second.len()));
    let (mut first, mut second) = (first.iter().peekable(), second.iter().peekable());
    loop {
        let next = match (first.peek(), second.peek()) {
            (Some(&&a), Some(&&b)) => {
                if a <= b {
                    let _a = first.next();
                }
                if b <= a {
                    let _b = second.next();
                }
                a.min(b)
            },
            (Some(&&a), None) => {
                let _a = first.next();
                a
            },
            (None, Some(&&b)) => {
                let _b = second.next();
                b
            },
            (None, None) => break,
        };
        out.push(next);
    }
    out.into()
}
