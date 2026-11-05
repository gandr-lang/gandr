//! The built-in roles a declaration takes: the declarations the core's own
//! formers read by role, never by name.
//!
//! The type of inductive-recursive signatures and the two functions by
//! recursion on a signature are ordinary declarations (Kovács 2026, § 2.2):
//! `E`, the fields that a signature asks for, and `F`, the decode of those
//! fields. The dependent pairs that `E` asks for are an ordinary declaration
//! too. The family that a signature defines and its decoder are ordinary
//! declarations in one mutual block: the family's one constructor holds the
//! fields of `E` over the family and its decoder, and the decoder decodes
//! them by `F`. The eliminator of the family and the two functions it reads,
//! the induction hypotheses over the fields and their map, are ordinary
//! declarations too (§ 2.2.3). A declaration that the source marks
//! `@[ builtin(…) ]` takes one of these roles, and both checkers and the
//! kernel compare it with the canonical form of its role.
//!
//! The mark states a role and decides nothing else. A role that two
//! declarations claim is refused, and so is a mark on a declaration of the
//! wrong judgement: the signature type, the pair type and the family are
//! data declarations, and `E`, `F`, the decoder, the hypotheses, the map and
//! the eliminator are value declarations.
//!
//! # References
//!
//! - cites: [doi:10.1145/3776685] — the signatures, `E` and `F` (§ 2.2)
//! - `vault:01a183fc-63df-77a0-9df0-1c3f0b02ddf6` — anchor: the signatures, `E`
//!   and `F` of § 2.2 give the roles and the judgement of each holder. The
//!   dependent pairs of `E`'s `σ` and `δ` cases give the pair role.
//!
//! [doi:10.1145/3776685]: https://doi.org/10.1145/3776685 "Kovács, Canonicity for indexed inductive-recursive types"

use anodized::spec;
use quenchant_shape::shape::Maybe;

/// A built-in role: the declaration that one of the core's formers reads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Builtin
{
    /// The type of inductive-recursive signatures over an output type, a data
    /// declaration whose constructors are `ι`, `σ` and `δ`.
    IrSignature,
    /// The dependent pairs that `E` asks for, a data declaration over a type
    /// and a family of types, with one constructor of two fields.
    IrPair,
    /// `E`: the fields that a signature asks for over a family and its
    /// decoder, a value declaration by recursion on the signature.
    IrArgs,
    /// `F`: the decode of those fields, a value declaration by recursion on
    /// the signature.
    IrDecode,
    /// The family that a signature defines, a data declaration over the output
    /// type and the signature, with one constructor whose one field holds the
    /// fields that `E` asks for over the family and its decoder.
    IrFamily,
    /// The decoder of that family, a value declaration that decodes the one
    /// field of the family's constructor by `F`.
    IrDecoder,
    /// The induction hypotheses over the fields that a signature asks for:
    /// one proof of a predicate for each value of the family among them, a
    /// value declaration by recursion on the signature.
    IrHypotheses,
    /// The map of a function over those fields into their hypotheses, a value
    /// declaration by recursion on the signature.
    IrMap,
    /// The eliminator of the family, a value declaration whose answer at the
    /// family's one constructor is the step at the fields and the map of the
    /// eliminator over them.
    IrEliminator,
}

/// The word that an attribute names a built-in role by, as the source spells
/// it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RoleWord<'word>(pub &'word str);

impl core::fmt::Display for RoleWord<'_>
{
    /// The word as the source spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0)
    }
}

/// The judgement of the declaration that holds a built-in role.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Holder
{
    /// A data declaration.
    Data,
    /// A value declaration.
    Value,
}

/// The first place where a role's holder departs from the canonical form of
/// its role.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Departure
{
    /// The parameter telescope: another number of parameters, or a parameter
    /// that is no value universe.
    Parameters,
    /// An index telescope, where the canonical form has none.
    Indices,
    /// The constructor table: another number of constructors.
    Constructors,
    /// One constructor's fields: another number of fields.
    Arity(crate::ConstructorTag),
    /// One field of one constructor.
    Field
    {
        /// The constructor.
        tag: crate::ConstructorTag,
        /// The field.
        field: crate::FieldPosition,
    },
    /// A role that the canonical form reads, which no declaration holds yet.
    Reads(Builtin),
    /// The holder's answer at one constructor of the signature type.
    Answer(crate::ConstructorTag),
}

impl Builtin
{
    /// The words that an attribute names the roles by, in the order of
    /// [`Self::ALL`].
    pub const WORDS: &'static [&'static str] = &[
        "irSignature",
        "irPair",
        "irArgs",
        "irDecode",
        "irFamily",
        "irDecoder",
        "irHypotheses",
        "irMap",
        "irEliminator",
    ];

    /// Every role, in the order of [`Self::WORDS`].
    pub const ALL: [Self; 9] = [
        Self::IrSignature,
        Self::IrPair,
        Self::IrArgs,
        Self::IrDecode,
        Self::IrFamily,
        Self::IrDecoder,
        Self::IrHypotheses,
        Self::IrMap,
        Self::IrEliminator,
    ];

    /// The word that an attribute names this role by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn word(self) -> RoleWord<'static>
    {
        RoleWord(match self {
            Self::IrSignature => "irSignature",
            Self::IrPair => "irPair",
            Self::IrArgs => "irArgs",
            Self::IrDecode => "irDecode",
            Self::IrFamily => "irFamily",
            Self::IrDecoder => "irDecoder",
            Self::IrHypotheses => "irHypotheses",
            Self::IrMap => "irMap",
            Self::IrEliminator => "irEliminator",
        })
    }

    /// The role that `word` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the role whose [`Self::word`] is `word`, and
    ///   [`builtin_role::Absent::Unnamed`] for any other word.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each role's word names it back, and a word that no
    ///   role carries names none.
    /// - witness: `builtin::tests::each_role_is_named_back_by_its_word`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(role) => role.word() == word,
        | Maybe::Absent(_) => Self::ALL.iter().all(|role| role.word() != word),
    })]
    #[inline]
    pub fn named(word: RoleWord<'_>) -> Maybe<Self, builtin_role::Absent>
    {
        Self::ALL
            .into_iter()
            .find(|role| role.word() == word)
            .map_or(Maybe::Absent(builtin_role::Absent::Unnamed), Maybe::Present)
    }

    /// The judgement of the declaration that holds this role.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn holder(self) -> Holder
    {
        match self {
            Self::IrSignature | Self::IrPair | Self::IrFamily => Holder::Data,
            Self::IrArgs
            | Self::IrDecode
            | Self::IrDecoder
            | Self::IrHypotheses
            | Self::IrMap
            | Self::IrEliminator => Holder::Value,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration takes no built-in role.
    pub mod builtin_role {
        /// The reason a declaration takes no role.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The source marks the declaration with no role.
            Unmarked,
            /// The word names no role.
            Unnamed,
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::Builtin;
    use super::RoleWord;
    use super::builtin_role;

    #[test]
    fn each_role_is_named_back_by_its_word()
    {
        for (role, &word) in Builtin::ALL.into_iter().zip(Builtin::WORDS) {
            assert_eq!(role.word(), RoleWord(word));
            assert_eq!(Builtin::named(RoleWord(word)), Maybe::Present(role));
        }
        assert_eq!(
            Builtin::named(RoleWord("irElim")),
            Maybe::Absent(builtin_role::Absent::Unnamed)
        );
    }
}
