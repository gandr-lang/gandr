//! The built-in roles a declaration takes: the declarations the core's own
//! formers read by role, never by name.
//!
//! The family that an inductive-recursive signature defines, its constructor
//! and its decoder are core formers over a signature value (Kovács 2026,
//! § 2.2). The type of the signatures and the two functions by recursion on a
//! signature are ordinary declarations: `E`, the fields that a signature asks
//! for, and `F`, the decode of those fields. The dependent pairs that `E` asks
//! for are an ordinary declaration too. A declaration that the source marks
//! `@[ builtin(…) ]` takes one of these roles. The checker records the
//! declaration that holds each role, for the formers to read (owed to #3575).
//!
//! The mark states a role and decides nothing else. A role that two
//! declarations claim is refused, and so is a mark on a declaration of the
//! wrong judgement: the signature type and the pair type are data
//! declarations, and `E` and `F` are value declarations.
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
    pub const WORDS: &'static [&'static str] = &["irSignature", "irPair", "irArgs", "irDecode"];

    /// Every role, in the order of [`Self::WORDS`].
    pub const ALL: [Self; 4] = [
        Self::IrSignature,
        Self::IrPair,
        Self::IrArgs,
        Self::IrDecode,
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
            Self::IrSignature | Self::IrPair => Holder::Data,
            Self::IrArgs | Self::IrDecode => Holder::Value,
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
