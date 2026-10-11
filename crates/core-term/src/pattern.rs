//! Patterns, holes among them, and the three answers a branch can get.
//!
//! # A pattern table, flat and addressed by id
//!
//! A [`Patterns`] table owns every pattern a match's arms are written in. A
//! composite names its parts by [`PatternId`], and a part is minted before the
//! pattern holding it, so a walk over a pattern is a loop over ids rather than
//! a descent through owned boxes.
//!
//! # A pattern may be a hole
//!
//! [`Pattern::Hole`] stands for a pattern the author has not written. It is
//! neither a wildcard nor an absurd pattern: a fill may make it either, or
//! anything between, so a question about a match with a pattern hole has an
//! answer only when every filling gives the same one (Yuan et al., *Live
//! Pattern Matching with Typed Holes*, OOPSLA 2023, doi:10.1145/3586048).
//!
//! # Three answers per branch
//!
//! [`BranchStatus`] is the verdict for one branch: it matches whatever any
//! hole is filled with, it cannot match whatever the fill, or a hole decides.
//! A scrutinee holding a hole leaves the same three answers as a pattern
//! holding one, so evaluation and coverage report in one vocabulary.
//!
//! # No core match former
//!
//! The core calculus eliminates by case, data case and projection; it has no
//! match. Patterns stand here as the vocabulary a match's arms are classified
//! in — live, against a scrutinee, and statically, for coverage — while
//! compiling a nested match into eliminations belongs to the elaboration of
//! eliminators. Reversal: a core match former becomes worth its kernel
//! translation once a consumer needs nested patterns to survive into the core
//! term rather than being compiled away, at which point this table is its
//! arms' vocabulary.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;

use crate::hole::HoleId;

/// The id of a pattern in a [`Patterns`] table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PatternId(u32);

/// One pattern.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Pattern
{
    /// Matches anything and binds nothing.
    Wildcard,
    /// Matches anything and binds it.
    Binder,
    /// Matches the unit value.
    Unit,
    /// Matches exactly this literal.
    Literal(Literal),
    /// Matches a pair whose components match the two parts.
    Pair(PatternId, PatternId),
    /// Matches an injection into this side whose body matches the part.
    Injection(Side, PatternId),
    /// Matches this constructor whose fields match the parts, in order.
    Constructor
    {
        /// The constructor's ordinal in its declaration.
        tag: ConstructorTag,
        /// One pattern per field, in signature order.
        fields: Vec<PatternId>,
    },
    /// A pattern the author has not written.
    Hole(HoleId),
}

impl Pattern
{
    /// The parts of this pattern, left to right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: both components of a pair, the body of an injection, every
    ///   field of a constructor in order, and nothing for a leaf.
    /// - provides: the one child relation every walk over a pattern follows.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair, an injection, a constructor of two fields and
    ///   a hole separate the arities and the order.
    /// - witness: `pattern::tests::a_pattern_names_its_parts_in_order`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *self {
        Self::Pair(first, second) => ret.as_slice() == [first, second],
        Self::Injection(_, body) => ret.as_slice() == [body],
        Self::Constructor { ref fields, .. } => ret == *fields,
        Self::Wildcard | Self::Binder | Self::Unit | Self::Literal(_) | Self::Hole(_) => ret.is_empty(),
    })]
    pub fn parts(&self) -> Vec<PatternId>
    {
        match *self {
            | Self::Pair(first, second) => Vec::from([first, second]),
            | Self::Injection(_, body) => Vec::from([body]),
            | Self::Constructor { ref fields, .. } => fields.clone(),
            | Self::Wildcard | Self::Binder | Self::Unit | Self::Literal(_) | Self::Hole(_) => {
                Vec::new()
            },
        }
    }
}

/// A table of patterns, each part minted before the pattern holding it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Patterns
{
    /// The patterns, by id.
    nodes: Vec<Pattern>,
}

impl Patterns
{
    /// An empty table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Mint `pattern` and name it.
    ///
    /// # Specification
    /// - requires: every part `pattern` names was minted in this table, and the
    ///   table holds fewer than `u32::MAX` patterns.
    /// - ensures: a fresh id naming `pattern`; every earlier id names what it
    ///   named.
    /// - provides: the only way a pattern enters the table.
    /// - fails: never.
    /// - panics: none — an id past the representable ceiling saturates, which
    ///   the requirement excludes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two patterns minted in turn get distinct ids, each
    ///   reading back what was minted under it.
    /// - witness: `pattern::tests::a_pattern_names_its_parts_in_order`
    #[inline]
    #[spec(captures: [entry = self.nodes.len(), minted = pattern.clone()],
        ensures: |ret| self.nodes.len() == entry.saturating_add(1_usize) && self.pattern(ret) == Some(&minted))]
    pub fn mint(
        &mut self,
        pattern: Pattern,
    ) -> PatternId
    {
        let id = PatternId(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX));
        self.nodes.push(pattern);
        id
    }

    /// The pattern `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the pattern minted under `id`, or nothing when `id` names
    ///   none of this table's.
    /// - provides: the checked read every walk resolves a part through.
    /// - fails: answers nothing for a foreign or dangling id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted id and an empty table separate the hit from
    ///   the miss.
    /// - witness: `pattern::tests::a_pattern_names_its_parts_in_order`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(id.0).is_ok_and(|at| at < self.nodes.len()))]
    pub fn pattern(
        &self,
        id: PatternId,
    ) -> Option<&Pattern>
    {
        self.nodes.get(usize::try_from(id.0).ok()?)
    }
}

/// How one branch of a match stands against its scrutinee.
///
/// A scrutinee or a pattern holding a hole leaves some branches undecided;
/// calling such a branch refuted hides a match the finished program will take,
/// and calling it satisfied claims one it may not. `Possibly` is the third
/// answer that keeps checking and evaluation from blocking on an unfinished
/// program.
///
/// # Specification
/// - requires: the producer classifies a branch against its scrutinee and the
///   possible fillings of holes.
/// - ensures: the three labels remain distinct; no consumer turns uncertainty
///   into satisfaction or refutation.
/// - executable: none — the declaration has no call boundary and carries
///   neither the branch nor its scrutinee; classification is the producer's
///   obligation.
///
/// # Adequacy
/// - hypothesis: L3 — the conjunction over all nine pairs separates the three
///   labels: each is the answer of some pair, and pairs that differ in their
///   strongest operand differ in their answer.
/// - witness: `pattern::tests::a_conjunction_refutes_first_and_doubts_second`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BranchStatus
{
    /// The branch matches, whatever any hole is filled with.
    Satisfied,
    /// Some hole decides whether the branch matches.
    Possibly,
    /// The branch cannot match, whatever any hole is filled with.
    Refuted,
}

impl BranchStatus
{
    /// The status of a match whose parts must all match.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`BranchStatus::Refuted`] when either part is refuted;
    ///   otherwise [`BranchStatus::Possibly`] when either is possible;
    ///   otherwise [`BranchStatus::Satisfied`].
    /// - provides: the strong three-valued conjunction a composite pattern
    ///   combines its parts' answers with: a part that cannot match refutes the
    ///   whole whatever a hole elsewhere is filled with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all nine pairs, so refutation beats doubt on either
    ///   side and doubt beats satisfaction on either side.
    /// - witness: `pattern::tests::a_conjunction_refutes_first_and_doubts_second`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match (self, other) {
        (Self::Refuted, _) | (_, Self::Refuted) => matches!(ret, Self::Refuted),
        (Self::Possibly, _) | (_, Self::Possibly) => matches!(ret, Self::Possibly),
        (Self::Satisfied, Self::Satisfied) => matches!(ret, Self::Satisfied),
    })]
    pub const fn and(
        self,
        other: Self,
    ) -> Self
    {
        match (self, other) {
            | (Self::Refuted, Self::Satisfied | Self::Possibly | Self::Refuted)
            | (Self::Satisfied | Self::Possibly, Self::Refuted) => Self::Refuted,
            | (Self::Possibly, Self::Satisfied | Self::Possibly)
            | (Self::Satisfied, Self::Possibly) => Self::Possibly,
            | (Self::Satisfied, Self::Satisfied) => Self::Satisfied,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::Side;

    use super::BranchStatus;
    use super::Pattern;
    use super::PatternId;
    use super::Patterns;
    use crate::hole::HoleId;

    #[test]
    fn a_conjunction_refutes_first_and_doubts_second()
    {
        use BranchStatus::Possibly;
        use BranchStatus::Refuted;
        use BranchStatus::Satisfied;
        let table = [
            (Satisfied, Satisfied, Satisfied),
            (Satisfied, Possibly, Possibly),
            (Satisfied, Refuted, Refuted),
            (Possibly, Satisfied, Possibly),
            (Possibly, Possibly, Possibly),
            (Possibly, Refuted, Refuted),
            (Refuted, Satisfied, Refuted),
            (Refuted, Possibly, Refuted),
            (Refuted, Refuted, Refuted),
        ];
        for (left, right, expected) in table {
            assert_eq!(left.and(right), expected, "{left:?} and {right:?}");
        }
    }

    #[test]
    fn a_pattern_names_its_parts_in_order()
    {
        let mut patterns = Patterns::new();
        let first = patterns.mint(Pattern::Binder);
        let second = patterns.mint(Pattern::Hole(HoleId::from(3_u32)));
        assert_ne!(first, second, "two mints are two patterns");
        let pair = patterns.mint(Pattern::Pair(first, second));
        let injected = patterns.mint(Pattern::Injection(Side::Right, pair));
        let constructed = patterns.mint(Pattern::Constructor {
            tag: ConstructorTag::from(1_usize),
            fields: vec![second, first],
        });
        let read = |id: PatternId| patterns.pattern(id).expect("minted").parts();
        assert_eq!(read(pair), vec![first, second]);
        assert_eq!(read(injected), vec![pair]);
        assert_eq!(
            read(constructed),
            vec![second, first],
            "fields keep their order"
        );
        assert_eq!(read(second), Vec::<PatternId>::new(), "a hole has no parts");
        assert_eq!(
            patterns.pattern(second),
            Some(&Pattern::Hole(HoleId::from(3_u32))),
            "an id reads back what was minted under it"
        );
        assert_eq!(
            Patterns::new().pattern(first),
            None,
            "an empty table resolves nothing"
        );
    }
}
