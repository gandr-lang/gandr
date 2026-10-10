//! The grammar-facing vocabulary a molded tree carries: a mold's identity in
//! its grammar's table, the sort tag grout carries, the fingerprint that
//! scopes both, and the bracketing class of a paired delimiter.
//!
//! The grammar owns the tables these values index; a tree stores only the
//! compact references, so the vocabulary sits here, below both the grammar and
//! the parser that reads it.

use core::num::TryFromIntError;

use anodized::spec;

/// One mold's position in the table of the grammar that assigned it.
///
/// An id means nothing without its table: the [`GrammarFingerprint`] of the
/// grammar names which table, so an id read against another grammar's table is
/// a mismatch a consumer detects by fingerprint rather than a silent
/// reinterpretation.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MoldId(u32);

impl MoldId
{
    /// Compare represented values during constant evaluation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn const_eq(
        self,
        other: Self,
    ) -> crate::ConstEquality
    {
        if self.0 == other.0 {
            crate::ConstEquality::Equal
        }
        else {
            crate::ConstEquality::Unequal
        }
    }
}

impl From<u32> for MoldId
{
    /// Reads a table position as a mold id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: u32) -> Self
    {
        Self(position)
    }
}

impl From<MoldId> for u32
{
    /// Reads the table position back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: MoldId) -> Self
    {
        id.0
    }
}

impl TryFrom<usize> for MoldId
{
    type Error = TryFromIntError;

    /// Reads a host index as a mold id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the id is `position`.
    /// - fails: when `position` does not fit the 32-bit id.
    /// - panics: none.
    ///
    /// # Errors
    /// The integer conversion's error when `position` exceeds `u32::MAX`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, an ordinary id and the largest 32-bit index
    ///   retain their exact values; the next index, where the host can name it,
    ///   is refused. These observers detect truncation, shifted ids and an
    ///   off-by-one upper bound.
    /// - witness: `mold::tests::a_host_index_past_the_id_width_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |_| u32::try_from(position).is_err(),
        |id| usize::try_from(id.0) == Ok(position),
    ))]
    fn try_from(position: usize) -> Result<Self, Self::Error>
    {
        u32::try_from(position).map(Self)
    }
}

/// The sort tag grout carries: which grammar sort a hole stands in for.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GroutSort(u16);

impl GroutSort
{
    /// Compare represented values during constant evaluation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn const_eq(
        self,
        other: Self,
    ) -> crate::ConstEquality
    {
        if self.0 == other.0 {
            crate::ConstEquality::Equal
        }
        else {
            crate::ConstEquality::Unequal
        }
    }
}

impl From<u16> for GroutSort
{
    /// Reads a raw tag as a grout sort.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: u16) -> Self
    {
        Self(tag)
    }
}

impl From<GroutSort> for u16
{
    /// Reads the raw tag back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(sort: GroutSort) -> Self
    {
        sort.0
    }
}

/// The shape of a piece of grout: which of its sides face a neighbour.
///
/// Grout is the material a parser inserts where the source leaves a term or a
/// closer unwritten; its shape says which sides it stands between. A missing
/// operand is convex — it faces nothing — and a closer the source never wrote
/// is postfix, closing the form to its left.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GroutShape
{
    /// Faces nothing: a whole term that is absent.
    Convex,
    /// Faces a term on its right only.
    Prefix,
    /// Faces a term on its left only.
    Postfix,
    /// Faces a term on both sides.
    Infix,
}

/// The fingerprint of the grammar whose mold table a tree's [`MoldId`]s
/// index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GrammarFingerprint(u64);

impl GrammarFingerprint
{
    /// Compare represented values during constant evaluation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn const_eq(
        self,
        other: Self,
    ) -> crate::ConstEquality
    {
        if self.0 == other.0 {
            crate::ConstEquality::Equal
        }
        else {
            crate::ConstEquality::Unequal
        }
    }
}

impl From<u64> for GrammarFingerprint
{
    /// Reads a raw hash as a grammar fingerprint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(hash: u64) -> Self
    {
        Self(hash)
    }
}

impl From<GrammarFingerprint> for u64
{
    /// Reads the raw hash back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fingerprint: GrammarFingerprint) -> Self
    {
        fingerprint.0
    }
}

/// The spelling of a delimiter, as written.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DelimSpelling<'text>(&'text str);

impl<'text> From<&'text str> for DelimSpelling<'text>
{
    /// Borrows text as a delimiter spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// The bracketing family a paired delimiter belongs to.
///
/// A closer stands in for its own family only: a `}` answers a `{` or a `#{`
/// and says nothing about a `(` still waiting for its `)`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ClosingClass
{
    /// `(` … `)`.
    Paren,
    /// `[` … `]`.
    Bracket,
    /// `{` … `}`, the record opener `#{` included.
    Brace,
}

impl ClosingClass
{
    /// Names the family a spelling opens, if it opens one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `(` is [`Paren`](Self::Paren), `[` is
    ///   [`Bracket`](Self::Bracket), `{` and `#{` are [`Brace`](Self::Brace),
    ///   and every other spelling, the closers included, is `None`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — every opener, every closer and a
    ///   non-delimiter are each classified.
    /// - witness: `mold::tests::openers_and_closers_pair_by_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == match spelling.0 { "(" => Some(Self::Paren), "[" => Some(Self::Bracket), "{" | "#{" => Some(Self::Brace), _ => None })]
    pub fn opening(spelling: DelimSpelling<'_>) -> Option<Self>
    {
        match spelling.0 {
            | "(" => Some(Self::Paren),
            | "[" => Some(Self::Bracket),
            | "{" | "#{" => Some(Self::Brace),
            | _ => None,
        }
    }

    /// Names the family a spelling closes, if it closes one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `)` is [`Paren`](Self::Paren), `]` is
    ///   [`Bracket`](Self::Bracket), `}` is [`Brace`](Self::Brace), and every
    ///   other spelling, the openers included, is `None`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — every closer, every opener and a
    ///   non-delimiter are each classified.
    /// - witness: `mold::tests::openers_and_closers_pair_by_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == match spelling.0 { ")" => Some(Self::Paren), "]" => Some(Self::Bracket), "}" => Some(Self::Brace), _ => None })]
    pub fn closing(spelling: DelimSpelling<'_>) -> Option<Self>
    {
        match spelling.0 {
            | ")" => Some(Self::Paren),
            | "]" => Some(Self::Bracket),
            | "}" => Some(Self::Brace),
            | _ => None,
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::ClosingClass;
    use super::DelimSpelling;
    use super::MoldId;

    #[test]
    fn openers_and_closers_pair_by_family()
    {
        let rows = [
            ("(", Some(ClosingClass::Paren), None),
            ("[", Some(ClosingClass::Bracket), None),
            ("{", Some(ClosingClass::Brace), None),
            ("#{", Some(ClosingClass::Brace), None),
            (")", None, Some(ClosingClass::Paren)),
            ("]", None, Some(ClosingClass::Bracket)),
            ("}", None, Some(ClosingClass::Brace)),
            ("#}", None, None),
            (";", None, None),
            ("", None, None),
        ];
        for (spelling, opens, closes) in rows {
            assert_eq!(
                opens,
                ClosingClass::opening(DelimSpelling::from(spelling)),
                "{spelling:?} opens"
            );
            assert_eq!(
                closes,
                ClosingClass::closing(DelimSpelling::from(spelling)),
                "{spelling:?} closes"
            );
        }
    }

    #[test]
    fn a_host_index_past_the_id_width_is_refused()
    {
        for value in [0_u32, 17, u32::MAX] {
            assert_eq!(
                Ok(MoldId::from(value)),
                MoldId::try_from(usize::try_from(value).expect("hosts are at least 32-bit")),
            );
        }
        let past = usize::try_from(u64::from(u32::MAX).checked_add(1).expect("fits in u64"));
        if let Ok(past) = past {
            assert!(MoldId::try_from(past).is_err());
        }
    }
}
