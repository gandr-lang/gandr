//! The cached word: a guard minted with every value, computation and neutral,
//! which step 2 of the conversion pipeline reads in constant time.
//!
//! # What the word holds
//!
//! A [`Guard`] is [`Guard::Rigid`] carrying a [`ContentHash`], or
//! [`Guard::Flexible`]. A node is rigid when nothing inside it can change its
//! answer under conversion: no closure, whose body a binder rule or an
//! η-equation compares only after it is opened, and no neutral whose head has
//! a body to unfold. For a rigid pair conversion **is** structural equality on
//! the hashed content, so two rigid guards with different hashes settle the
//! pair distinct without reading either node. Equal hashes settle nothing: a
//! collision is possible, and the pair falls through to structural
//! comparison.
//!
//! # What it does not hold
//!
//! The word carries the hash and one rigidity bit. A hole bit is not carried,
//! because the domain has no hole former; a loose-variable range and an
//! approximate depth are not carried, because levels make α-equivalence
//! identity and every node a binder could make loose is a closure, which is
//! flexible and never hashed. Each omitted field reopens with the condition
//! that would make it non-trivial: the hole surface, or a guard asked to decide
//! under a binder.
//!
//! # The hash
//!
//! FNV-1a over 64 bits, folded at mint from a node's kind, its own payload and
//! its children's words — a literal's payload and a lift's level through their
//! `Hash` implementations, whose equality is the conversion equality for both.
//! The word is computed and compared within one run; nothing claims it is
//! stable across hosts or builds.

use core::hash::Hash;
use core::hash::Hasher;

/// A content hash, comparable only within the run that minted it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContentHash(u64);

impl ContentHash
{
    /// The fold of `content`'s `Hash` encoding, by the hash every guard is
    /// minted with.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: equal content folds to equal words within one run.
    /// - provides: the digest the re-sharing memo buckets its supports by, so
    ///   one hash serves both and the fold order is fixed in this module.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub(crate) fn of<Content>(content: &Content) -> Self
    where
        Content: Hash + ?Sized,
    {
        let mut fold = Fold(FNV_OFFSET);
        content.hash(&mut fold);
        Self(fold.finish())
    }
}

impl From<ContentHash> for u64
{
    /// The word `hash` carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(hash: ContentHash) -> Self
    {
        hash.0
    }
}

/// The word minted with a domain node, read by the pipeline's step 2.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Guard
{
    /// Nothing inside the node can change its answer under conversion, so
    /// conversion on a pair of such nodes is structural equality on the
    /// content this hash folds.
    Rigid(ContentHash),
    /// A closure or an unfoldable head sits inside the node, so its content
    /// says nothing step 2 may act on.
    Flexible,
}

/// What step 2 answers for a pair.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum GuardAnswer
{
    /// Both words are rigid and their hashes differ: the pair is distinct.
    Apart,
    /// The words settle nothing — either is flexible, or the hashes agree —
    /// and the pair falls through to structural comparison.
    Inconclusive,
}

/// The node kind a word folds first, so two kinds over equal content hash
/// apart.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum GuardTag
{
    /// The unit value.
    Unit,
    /// A literal value.
    Literal,
    /// A pair.
    Pair,
    /// A sum injection.
    Injection,
    /// A universe lift.
    Lift,
    /// A neutral standing in a value position.
    ValueNeutral,
    /// A returner.
    Return,
    /// A neutral standing in a computation position.
    CompNeutral,
    /// A bound-variable head.
    Variable,
    /// A declaration head that cannot unfold.
    Constant,
    /// A module-form head.
    Module,
    /// An application stacked on a spine.
    Apply,
    /// A force stacked on a spine.
    Force,
    /// A static application stacked on a spine.
    StaticApply,
}

/// The FNV-1a 64-bit offset basis.
const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325_u64;

/// The FNV-1a 64-bit prime.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3_u64;

/// FNV-1a as a [`Hasher`], so any `Hash` payload folds into a word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Fold(u64);

impl Hasher for Fold
{
    /// The folded state.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn finish(&self) -> u64
    {
        self.0
    }

    /// Fold `bytes` in order: exclusive-or each byte in, then multiply by the
    /// prime modulo 2⁶⁴.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the state is the FNV-1a fold of `bytes` onto the state at
    ///   entry.
    /// - provides: the one mixing step every word is built from; the
    ///   multiplication wraps by definition of the hash.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn write(
        &mut self,
        bytes: &[u8],
    )
    {
        for &byte in bytes {
            self.0 = (self.0 ^ u64::from(byte)).wrapping_mul(FNV_PRIME);
        }
    }
}

impl Guard
{
    /// The word for a node of kind `tag` carrying `content` over `children`.
    ///
    /// # Specification
    /// - requires: `children` are the words of the node's children, in the
    ///   order the node holds them.
    /// - ensures: [`Guard::Flexible`] when any child is flexible; otherwise
    ///   [`Guard::Rigid`] carrying the fold of `tag`, `content` and each
    ///   child's hash in order, so equal kinds over equal content and equal
    ///   children always fold to equal hashes.
    /// - provides: the one constructor every rigid word is minted through, so
    ///   the fold order is fixed in one place.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the flexible child and the
    ///   fold, separated by equal content at distinct ids folding equal, a
    ///   differing literal folding apart, and a pair over a thunk folding
    ///   flexible.
    /// - witness: `guard::tests::equal_content_folds_to_one_word`
    /// - witness: `guard::tests::a_flexible_child_makes_its_parent_flexible`
    #[inline]
    #[must_use]
    pub(crate) fn compose<Content>(
        tag: GuardTag,
        content: &Content,
        children: &[Self],
    ) -> Self
    where
        Content: Hash + ?Sized,
    {
        let mut fold = Fold(FNV_OFFSET);
        tag.hash(&mut fold);
        content.hash(&mut fold);
        for &child in children {
            match child {
                | Self::Rigid(ContentHash(hash)) => fold.write_u64(hash),
                | Self::Flexible => return Self::Flexible,
            }
        }
        Self::Rigid(ContentHash(fold.finish()))
    }

    /// Step 2 for a pair: whether the two words settle it distinct.
    ///
    /// # Specification
    /// - requires: both words were minted in one run.
    /// - ensures: [`GuardAnswer::Apart`] exactly when both words are rigid and
    ///   their hashes differ; [`GuardAnswer::Inconclusive`] otherwise.
    /// - provides: the constant-time distinct answer for a rigid pair, which
    ///   never answers convertible — equal hashes may collide.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the rigid-and-different
    ///   conjunction, separated by two rigid words that differ, two that agree,
    ///   and a flexible word against a rigid one.
    /// - witness: `guard::tests::only_two_rigid_words_that_differ_are_apart`
    #[inline]
    #[must_use]
    pub fn settles(
        self,
        other: Self,
    ) -> GuardAnswer
    {
        match (self, other) {
            | (Self::Rigid(one), Self::Rigid(two)) if one != two => GuardAnswer::Apart,
            | (Self::Rigid(_) | Self::Flexible, Self::Rigid(_) | Self::Flexible) => {
                GuardAnswer::Inconclusive
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;

    use super::Guard;
    use super::GuardAnswer;
    use super::GuardTag;

    /// The non-negative integer literal spelled by `digits`.
    ///
    /// # Specification
    /// - requires: `digits` is a non-empty run of decimal digits.
    /// - ensures: the integer literal those digits spell.
    /// - provides: the payloads the folding witnesses compare.
    /// - panics: when `digits` is not decimal, which no fixture passes.
    fn integer(digits: String) -> Literal
    {
        let magnitude = Magnitude::from_decimal_text(digits).expect("the digits are decimal");
        Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
    }

    #[test]
    fn equal_content_folds_to_one_word()
    {
        let unit = Guard::compose(GuardTag::Unit, &(), &[]);
        let one = Guard::compose(GuardTag::Literal, &integer(String::from("1")), &[]);
        let first = Guard::compose(GuardTag::Pair, &(), &[unit, one]);
        let again = Guard::compose(GuardTag::Pair, &(), &[
            Guard::compose(GuardTag::Unit, &(), &[]),
            Guard::compose(GuardTag::Literal, &integer(String::from("1")), &[]),
        ]);
        assert_eq!(
            first, again,
            "equal content folds to one word wherever it is minted"
        );
        assert!(
            matches!(first, Guard::Rigid(_)),
            "and content with no closure inside is rigid"
        );
        let two = Guard::compose(GuardTag::Literal, &integer(String::from("2")), &[]);
        assert_ne!(
            first,
            Guard::compose(GuardTag::Pair, &(), &[unit, two]),
            "a differing payload folds apart"
        );
        assert_ne!(
            first,
            Guard::compose(GuardTag::Pair, &(), &[one, unit]),
            "and so does the same content in another order"
        );
    }

    #[test]
    fn a_flexible_child_makes_its_parent_flexible()
    {
        let unit = Guard::compose(GuardTag::Unit, &(), &[]);
        assert_eq!(
            Guard::Flexible,
            Guard::compose(GuardTag::Pair, &(), &[unit, Guard::Flexible]),
            "a closure anywhere inside makes the whole word flexible"
        );
    }

    #[test]
    fn only_two_rigid_words_that_differ_are_apart()
    {
        let unit = Guard::compose(GuardTag::Unit, &(), &[]);
        let one = Guard::compose(GuardTag::Literal, &integer(String::from("1")), &[]);
        assert_eq!(
            GuardAnswer::Apart,
            unit.settles(one),
            "two rigid words that differ"
        );
        assert_eq!(
            GuardAnswer::Inconclusive,
            unit.settles(unit),
            "two rigid words that agree settle nothing, because a hash may collide"
        );
        assert_eq!(
            GuardAnswer::Inconclusive,
            Guard::Flexible.settles(one),
            "and a flexible word settles nothing against any word"
        );
    }
}
