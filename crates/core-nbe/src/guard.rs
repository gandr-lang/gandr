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
//!
//! # The cached word
//!
//! Every value, computation and neutral is minted with a `Guard`:
//! `Guard::Rigid` carrying an FNV-1a `ContentHash` of the node's kind, payload
//! and children's words, or `Guard::Flexible`. A node is flexible when a
//! closure or a head with a body to unfold sits inside it; a dangling child at
//! mint makes its parent flexible, the direction that decides nothing. For two
//! rigid nodes conversion is structural equality on the hashed content, so
//! differing hashes separate them; equal hashes decide nothing, because a hash
//! may collide. Literal payloads and lift levels enter the hash through their
//! `Hash` implementations, whose equality is the conversion equality for both;
//! a term face never enters it, because two faces over one content are one
//! value.
//!
//! The word carries the hash and the rigidity bit and nothing else.
//! Alternatives: the hole and metavariable bits, a loose-variable range and an
//! approximate depth that a Lean-style word packs. Each is uniformly trivial
//! here — a neutral headed by a hole or a mark carries a closure and is
//! flexible, so it decides nothing until filled, which is all a hole bit would
//! say; levels make α-equivalence identity; and every node a binder could make
//! loose is a closure, which is flexible and never hashed. Reversal: a guard
//! asked to decide under a binder adds the range.
//!
//! The fold is ten lines over `core::hash::Hasher` rather than a crate.
//! Alternatives: `rustc-hash`, whose algorithm changed across major versions
//! and which would hold conversion machinery outside the workspace; `fnv`,
//! unreleased since 2020; `foldhash`, seeded per instance with no stable
//! output; and the workspace's `blake3`, a 256-bit cryptographic digest where a
//! collision costs only a fall-through to step 3. Reversal: a word that crosses
//! a run boundary, or needs an output stable across builds, takes a maintained
//! crate with that guarantee.

use core::hash::Hash;
use core::hash::Hasher;

use anodized::spec;

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
    /// - executable: none — the clause relates arbitrary `Hash` encodings
    ///   across calls; an independent check would invoke user hashing again,
    ///   and the completed call exposes no byte transcript.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the unit and a byte are observed against the empty
    ///   and single-byte FNV words; a wrong seed, omitted encoding or constant
    ///   digest changes an observation. These finite encodings do not certify
    ///   every custom Hash implementation.
    /// - witness: `guard::tests::fnv_vectors_preserve_empty_and_segmented_writes`
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
    /// A literal value.
    Literal,
    /// A tuple of any arity, the unit among them.
    Tuple,
    /// The empty native list.
    ListNil,
    /// A native list cell.
    ListCons,
    /// A sum injection.
    Injection,
    /// Reflexivity of an element path.
    Here,
    /// Univalence over a record.
    Univalence,
    /// A flow introduction.
    Flow,
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
    /// A structural record in canonical label order.
    Record,
    /// A recorded run's payloads in move order.
    Recorded,
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, single-byte and six-byte inputs, including
    ///   segmented writes with an empty middle segment, have published FNV-1a
    ///   words; wrong constants, reversed bytes or resetting between writes
    ///   changes a word.
    /// - witness: `guard::tests::fnv_vectors_preserve_empty_and_segmented_writes`
    #[inline]
    #[spec(
        captures: initial = self.0,
        ensures: self.0 == bytes.iter().fold(initial, |hash, &byte| {
            (hash ^ u64::from(byte)).wrapping_mul(FNV_PRIME)
        }),
    )]
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
    /// - hypothesis: L3 — zero-child leaves and two-child pairs separate rigid
    ///   hashing from flexibility at either or both positions. Equal numeric
    ///   content, changed signs, changed magnitudes and reversed children
    ///   observe the fold; ignoring a child or payload, confusing order or
    ///   losing rigidity changes an observation.
    /// - witness: `guard::tests::equal_content_folds_to_one_word`
    /// - witness: `guard::tests::a_flexible_child_makes_its_parent_flexible`
    #[inline]
    #[must_use]
    #[spec(captures: flexible = children.clone().into_iter().any(|child| matches!(core::borrow::Borrow::<Self>::borrow(&child),Self::Flexible)),
        ensures: |ret| matches!(ret,Self::Flexible) == flexible)]
    pub(crate) fn compose<Content, Children>(
        tag: GuardTag,
        content: &Content,
        children: Children,
    ) -> Self
    where
        Content: Hash + ?Sized,
        Children: IntoIterator + Clone,
        Children::Item: core::borrow::Borrow<Self>,
    {
        let mut fold = Fold(FNV_OFFSET);
        tag.hash(&mut fold);
        content.hash(&mut fold);
        for child in children {
            let child = *core::borrow::Borrow::<Self>::borrow(&child);
            match child {
                Self::Rigid(ContentHash(hash)) => fold.write_u64(hash),
                Self::Flexible => return Self::Flexible,
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
    /// - hypothesis: L3 — all nine ordered pairs of two unequal rigid words and
    ///   a flexible word have exact verdicts. Asymmetric flexibility, treating
    ///   equal hashes as apart or accepting unequal rigid hashes changes an
    ///   entry.
    /// - witness: `guard::tests::only_two_rigid_words_that_differ_are_apart`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| (ret == GuardAnswer::Apart)
        == matches!((self, other), (Self::Rigid(one), Self::Rigid(two)) if one != two))]
    pub fn settles(
        self,
        other: Self,
    ) -> GuardAnswer
    {
        match (self, other) {
            (Self::Rigid(one), Self::Rigid(two)) if one != two => GuardAnswer::Apart,
            (Self::Rigid(_) | Self::Flexible, Self::Rigid(_) | Self::Flexible) => {
                GuardAnswer::Inconclusive
            },
        }
    }
}

#[cfg(test)]
mod tests;
