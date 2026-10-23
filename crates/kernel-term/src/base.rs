//! The rigid base-type atoms and the literal stock, each held in a canonical
//! form its smart constructor maintains.
//!
//! The base-type atoms are rigid and closed: the stock is exactly the four the
//! literal forms name — an integer atom, a string atom, a numeric atom, a
//! character atom and a 64-bit binary floating-point atom.
//!
//! Literal payloads are canonical and structurally comparable — leading and
//! trailing zeros normalized, the zero sign pinned — so syntactic equality of
//! two literals coincides with equality of the values they denote. That is what
//! lets the format's content-keyed deduplication collapse two spellings of one
//! literal, and what makes a non-canonical literal unrepresentable in memory
//! rather than merely rejected on the wire.
//!
//! # The character atom
//!
//! A character literal is its own literal over its own atom, the type the
//! surface writes `Char`, rather than an elaboration into one of the other
//! three. Two elaborations were open: a one-scalar string, which would make
//! `Char` and `String` one type, so `'a'` and `"a"` would compare equal and
//! a string of any length would check where a character is declared; and the
//! scalar's code point as an integer, which would let arithmetic reach a
//! character and lose the type a description's `Char` field already names.
//! The atom keeps both apart at the cost of one literal kind and one base
//! tag in each encoding. Its payload is the scalar, framed on the wire as the
//! scalar's UTF-8 text, so a payload of no scalar or of two is refused when
//! read. Reversal: if characters are ever wanted as bounded integers or as
//! strings of length one, the atom folds into that type and the tag retires.

use alloc::string::String;
use core::str::FromStr;

use anodized::spec;

/// A rigid base-type atom.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BaseType
{
    /// The integer atom — the type of an [`IntegerLiteral`].
    Integer,
    /// The string atom — the type of a [`StringLiteral`].
    String,
    /// The numeric atom — the type of a [`NumericLiteral`].
    Numeric,
    /// The character atom — the type of a [`CharacterLiteral`].
    Character,
    /// The 64-bit binary floating-point atom — the type of a
    /// [`Float64Literal`].
    Float64,
}

/// The sign of a numeric literal.
///
/// Zero is [`Self::NonNegative`], so a canonical literal never carries a
/// negative zero.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Sign
{
    /// A negative magnitude, never the zero magnitude.
    Negative,
    /// A non-negative magnitude, zero included.
    NonNegative,
}

/// A canonical unsigned integer magnitude: ASCII decimal digits with no leading
/// zeros, the all-zero magnitude collapsed to a single `0`.
///
/// # Specification
/// - requires: the payload is obtained through its owning smart constructors.
/// - ensures: contains nonempty ASCII digits with no leading zero except the
///   single zero.
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its smart
///   constructors and variant projection carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L2 agreement compares every decimal value from zero through 99
///   with independently formatted canonical digits, padded forms, and explicit
///   empty, invalid ASCII and Unicode near-misses. L3 observes exact payload
///   bytes, the zero/nonzero sign boundary and all literal variants; it
///   separates digit loss, wrong trimming direction, negative zero and atom
///   substitution. Arbitrarily long payloads and allocation refusal are outside
///   these witnesses.
/// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
/// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Magnitude(String);

impl Magnitude
{
    /// The canonical zero magnitude.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the magnitude whose digits are exactly `0`.
    /// - provides: the one zero magnitude every canonicalization collapses to,
    ///   so equality on zero does not depend on its spelling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[spec(
        ensures: |ret| ret.0 == "0",
    )]
    #[inline]
    #[must_use]
    pub fn zero() -> Self
    {
        Self(String::from("0"))
    }

    /// Build a canonical magnitude from decimal digit text.
    ///
    /// # Specification
    /// - requires: any UTF-8 text, including malformed decimal input.
    /// - ensures: returns the same integer digits with leading zeros removed;
    ///   an all-zero input becomes the single zero.
    /// - provides: canonical magnitude equality. The predicate checks
    ///   acceptance, canonical shape, length and endpoint bytes without
    ///   retaining the consumed string; the independent witness checks complete
    ///   digit preservation.
    /// - fails: returns None exactly for empty text or any non-ASCII-decimal
    ///   byte.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[spec(
        captures: entry = (!text.is_empty()
                && text.bytes().all(|byte| byte.is_ascii_digit()), text.trim_start_matches('0').len().max(1), text.bytes().find(|&byte| byte != b'0').unwrap_or(b'0'), text.as_bytes().last().copied().unwrap_or(b'0')),
        ensures: |ret| ret.as_ref().map_or(!entry.0,
            |value| entry.0
                && value.0.len() == entry.1
                && value.0.bytes().all(|byte| byte.is_ascii_digit())
                && (value.0 == "0" || !value.0.starts_with('0'))
                && value.0.as_bytes().first().copied() == Some(entry.2)
                && value.0.as_bytes().last().copied() == Some(entry.3)),
    )]
    #[inline]
    #[must_use]
    pub fn from_decimal_text(mut text: String) -> Option<Self>
    {
        if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        let Some(index) = text.find(|character: char| character != '0')
        else {
            return Some(Self::zero());
        };
        text.replace_range(.. index, "");
        Some(Self(text))
    }

    /// The canonical decimal digits, as owned text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn to_digits(&self) -> String
    {
        self.0.clone()
    }
}

impl AsRef<str> for Magnitude
{
    /// Borrow the canonical digits, for a consumer computing a content
    /// encoding over them.
    ///
    /// The borrow is what a content-keyed memo one crate up needs: its
    /// canonical encoding must mirror the term relation exactly, so it has to
    /// reach the payload rather than the wrapper. The digits are already
    /// canonical, so a borrow cannot expose a non-canonical spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_str()
    }
}

/// A canonical fractional-digit sequence: ASCII decimal digits with no trailing
/// zeros, the empty sequence denoting an integral value.
///
/// # Specification
/// - requires: the payload is obtained through its owning smart constructors.
/// - ensures: contains ASCII digits without trailing zeros; the empty string
///   denotes an integral value.
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its smart
///   constructors and variant projection carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L2 agreement compares every decimal value from zero through 99
///   with independently formatted canonical digits, padded forms, and explicit
///   empty, invalid ASCII and Unicode near-misses. L3 observes exact payload
///   bytes, the zero/nonzero sign boundary and all literal variants; it
///   separates digit loss, wrong trimming direction, negative zero and atom
///   substitution. Arbitrarily long payloads and allocation refusal are outside
///   these witnesses.
/// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
/// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FractionDigits(String);

impl FractionDigits
{
    /// The canonical empty fraction, denoting an integral value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the fraction with no digits.
    /// - provides: the one fraction denoting an integral value, so equality on
    ///   an integral numeric literal does not depend on trailing zeros.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[spec(
        ensures: |ret| ret.0.is_empty(),
    )]
    #[inline]
    #[must_use]
    pub fn none() -> Self
    {
        Self(String::new())
    }

    /// Build a canonical fraction from decimal digit text.
    ///
    /// # Specification
    /// - requires: any UTF-8 text, including an empty or malformed fractional
    ///   part.
    /// - ensures: returns the same fractional digits with trailing zeros
    ///   removed; an empty or all-zero input becomes the empty fraction.
    /// - provides: canonical fractional equality. The predicate checks
    ///   acceptance, canonical shape, length and endpoint bytes without
    ///   retaining the consumed string; the independent witness checks complete
    ///   digit preservation.
    /// - fails: returns None exactly when a byte is not an ASCII decimal digit.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[spec(
        captures: entry = (text.bytes().all(|byte| byte.is_ascii_digit()), text.trim_end_matches('0').len(), text.as_bytes().first().copied(), text.bytes().rev().find(|&byte| byte != b'0')),
        ensures: |ret| ret.as_ref().map_or(!entry.0,
            |value| entry.0
                && value.0.len() == entry.1
                && value.0.bytes().all(|byte| byte.is_ascii_digit())
                && !value.0.ends_with('0')
                && value.0.as_bytes().first().copied() == if entry.1 == 0 { None }
            else { entry.2 }
                && value.0.as_bytes().last().copied() == entry.3),
    )]
    #[inline]
    #[must_use]
    pub fn from_decimal_text(mut text: String) -> Option<Self>
    {
        if !text.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        let trimmed = text.trim_end_matches('0').len();
        text.truncate(trimmed);
        Some(Self(text))
    }

    /// The canonical fractional digits, as owned text; empty for an integral
    /// value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn to_digits(&self) -> String
    {
        self.0.clone()
    }
}

impl AsRef<str> for FractionDigits
{
    /// Borrow the canonical fractional digits; see [`Magnitude::as_ref`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_str()
    }
}

/// A canonical integer literal: a [`Sign`] and a [`Magnitude`], inhabiting
/// [`BaseType::Integer`].
///
/// # Specification
/// - requires: the payload is obtained through its owning smart constructors.
/// - ensures: stores a canonical magnitude and sign; zero always has a
///   nonnegative sign.
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its smart
///   constructors and variant projection carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L2 agreement compares every decimal value from zero through 99
///   with independently formatted canonical digits, padded forms, and explicit
///   empty, invalid ASCII and Unicode near-misses. L3 observes exact payload
///   bytes, the zero/nonzero sign boundary and all literal variants; it
///   separates digit loss, wrong trimming direction, negative zero and atom
///   substitution. Arbitrarily long payloads and allocation refusal are outside
///   these witnesses.
/// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
/// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntegerLiteral
{
    /// The sign, never [`Sign::Negative`] on the zero magnitude.
    sign: Sign,
    /// The canonical unsigned magnitude.
    magnitude: Magnitude,
}

impl IntegerLiteral
{
    /// Build a canonical integer literal, pinning a negative zero to
    /// non-negative.
    ///
    /// # Specification
    /// - requires: `magnitude` is already canonical, which
    ///   [`Magnitude::from_decimal_text`] and [`Magnitude::zero`] are the only
    ///   ways to obtain.
    /// - ensures: the sign of the zero magnitude is forced to
    ///   [`Sign::NonNegative`], so two literals compare equal exactly when they
    ///   denote the same integer.
    /// - provides: the canonical integer literal.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[inline]
    #[must_use]
    #[spec(
        requires: magnitude.0 == "0"
            || (!magnitude.0.is_empty() && !magnitude.0.starts_with('0')
                && magnitude.0.bytes().all(|byte| byte.is_ascii_digit())),
        captures: entry_is_zero = magnitude.0 == "0",
        ensures: |ret| ret.sign == if entry_is_zero { Sign::NonNegative } else { sign },
    )]
    pub fn new(
        sign: Sign,
        magnitude: Magnitude,
    ) -> Self
    {
        let sign = if magnitude == Magnitude::zero() {
            Sign::NonNegative
        }
        else {
            sign
        };
        Self { sign, magnitude }
    }

    /// The literal's sign.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sign(&self) -> Sign
    {
        self.sign
    }

    /// The literal's canonical magnitude.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn magnitude(&self) -> &Magnitude
    {
        &self.magnitude
    }
}

/// A canonical string literal, inhabiting [`BaseType::String`].
///
/// The payload is held verbatim: a string carries no normalization beyond its
/// own bytes.
///
/// # Specification
/// - requires: the payload is obtained through its owning smart constructors.
/// - ensures: retains the UTF-8 payload without Unicode, whitespace or
///   line-ending normalization.
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its smart
///   constructors and variant projection carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L2 agreement compares every decimal value from zero through 99
///   with independently formatted canonical digits, padded forms, and explicit
///   empty, invalid ASCII and Unicode near-misses. L3 observes exact payload
///   bytes, the zero/nonzero sign boundary and all literal variants; it
///   separates digit loss, wrong trimming direction, negative zero and atom
///   substitution. Arbitrarily long payloads and allocation refusal are outside
///   these witnesses.
/// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
/// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StringLiteral(String);

impl StringLiteral
{
    /// Wrap string content as a literal.
    ///
    /// # Specification
    /// - requires: nothing; any content is admissible.
    /// - ensures: returns the literal carrying `content` byte for byte.
    /// - provides: the one literal constructor that canonicalizes nothing — a
    ///   string's bytes are already its canonical form, so two string literals
    ///   compare equal exactly when their bytes do.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[spec(
        captures: entry = (content.len(), content.as_bytes().first().copied(), content.as_bytes().last().copied()),
        ensures: |ret| ret.0.len() == entry.0
                && ret.0.as_bytes().first().copied() == entry.1
                && ret.0.as_bytes().last().copied() == entry.2,
    )]
    #[inline]
    #[must_use]
    pub fn new(content: String) -> Self
    {
        Self(content)
    }

    /// The string content, as owned text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn to_content(&self) -> String
    {
        self.0.clone()
    }
}

impl AsRef<str> for StringLiteral
{
    /// Borrow the string content; see [`Magnitude::as_ref`].
    ///
    /// The payload carries no normalization beyond its own bytes, so a content
    /// encoding over it must length-prefix what it reads — the borrow supplies
    /// the bytes and states nothing about how they are framed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_str()
    }
}

/// A character literal, one Unicode scalar value, inhabiting
/// [`BaseType::Character`].
///
/// A character is its own atom rather than a one-scalar string: `Char` and
/// `String` are distinct types, so `'a'` and `"a"` neither convert nor compare
/// equal. The payload is the scalar itself; a scalar is already canonical, so
/// two character literals compare equal exactly when their scalars do.
///
/// # Specification
/// - requires: the payload is obtained through `From<char>` or
///   `TryFrom<String>`.
/// - ensures: retains exactly one Unicode scalar value, without normalization.
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its
///   constructors carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L3 observes the scalar of ASCII, NUL, a two-byte, a three-byte
///   and a four-byte scalar through both constructors and the text reading, and
///   refuses the empty text, two scalars and a base letter with a combining
///   mark. This separates truncation to the first scalar, byte for scalar
///   counting and atom substitution.
/// - witness: `base::tests::a_character_literal_holds_exactly_one_scalar`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CharacterLiteral(char);

/// Why a text is no character literal: it holds no scalar, or more than one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotOneCharacter
{
    /// The text is empty.
    Empty,
    /// The text holds a second scalar after its first.
    Several,
}

impl CharacterLiteral
{
    /// The character's UTF-8 encoding, as owned text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns text holding exactly the literal's scalar.
    /// - provides: the payload's byte image for an encoding that frames text.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the text of ASCII, NUL and two-, three- and four-byte
    ///   scalars is exactly that scalar.
    /// - witness: `base::tests::a_character_literal_holds_exactly_one_scalar`
    #[spec(ensures: |ret| ret.chars().eq(core::iter::once(self.0)))]
    #[inline]
    #[must_use]
    pub fn to_text(&self) -> String
    {
        String::from(self.0)
    }
}

impl From<char> for CharacterLiteral
{
    /// Wrap a scalar as a literal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(scalar: char) -> Self
    {
        Self(scalar)
    }
}

impl From<CharacterLiteral> for char
{
    /// The literal's scalar.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(literal: CharacterLiteral) -> Self
    {
        literal.0
    }
}

impl TryFrom<String> for CharacterLiteral
{
    type Error = NotOneCharacter;

    /// Read a text holding exactly one scalar as its character.
    ///
    /// # Specification
    /// - requires: nothing; any text is admissible.
    /// - ensures: on `Ok`, the literal holds the text's one scalar.
    /// - fails: [`NotOneCharacter::Empty`] for the empty text,
    ///   [`NotOneCharacter::Several`] for a text of two or more scalars.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one scalar of each UTF-8 width reads back as its
    ///   character; the empty text, two letters and a letter with a combining
    ///   mark are refused with their exact reason.
    /// - witness: `base::tests::a_character_literal_holds_exactly_one_scalar`
    #[spec(
        captures: entry = (text.chars().next(), text.chars().count()),
        ensures: |ret| match entry.1 { 0 => ret == Err(NotOneCharacter::Empty), 1 => ret.ok().map(|literal| literal.0) == entry.0, _ => ret == Err(NotOneCharacter::Several) },
    )]
    #[inline]
    fn try_from(text: String) -> Result<Self, Self::Error>
    {
        let mut scalars = text.chars();
        let first = scalars.next().ok_or(NotOneCharacter::Empty)?;
        match scalars.next() {
            None => Ok(Self(first)),
            Some(_) => Err(NotOneCharacter::Several),
        }
    }
}

/// A canonical numeric literal: a [`Sign`], an integral [`Magnitude`], and a
/// [`FractionDigits`] fractional part, inhabiting [`BaseType::Numeric`].
///
/// # Specification
/// - requires: the payload is obtained through its owning smart constructors.
/// - ensures: stores canonical integer and fractional digits; zero has a
///   nonnegative sign.
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its smart
///   constructors and variant projection carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L2 agreement compares every decimal value from zero through 99
///   with independently formatted canonical digits, padded forms, and explicit
///   empty, invalid ASCII and Unicode near-misses. L3 observes exact payload
///   bytes, the zero/nonzero sign boundary and all literal variants; it
///   separates digit loss, wrong trimming direction, negative zero and atom
///   substitution. Arbitrarily long payloads and allocation refusal are outside
///   these witnesses.
/// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
/// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct NumericLiteral
{
    /// The sign, never [`Sign::Negative`] on the zero value.
    sign: Sign,
    /// The canonical integral part.
    integer_part: Magnitude,
    /// The canonical fractional part, empty for an integral value.
    fraction: FractionDigits,
}

impl NumericLiteral
{
    /// Build a canonical numeric literal, pinning a negative zero to
    /// non-negative.
    ///
    /// # Specification
    /// - requires: `integer_part` and `fraction` are already canonical.
    /// - ensures: the sign of the zero value — a zero integral part with an
    ///   empty fraction — is forced to [`Sign::NonNegative`], so two literals
    ///   compare equal exactly when they denote the same numeric value.
    /// - provides: the canonical numeric literal.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[inline]
    #[must_use]
    #[spec(
        requires: (integer_part.0 == "0"
            || (!integer_part.0.is_empty() && !integer_part.0.starts_with('0')
                && integer_part.0.bytes().all(|byte| byte.is_ascii_digit())))
            && !fraction.0.ends_with('0')
            && fraction.0.bytes().all(|byte| byte.is_ascii_digit()),
        captures: entry_is_zero = integer_part.0 == "0" && fraction.0.is_empty(),
        ensures: |ret| ret.sign == if entry_is_zero { Sign::NonNegative } else { sign },
    )]
    pub fn new(
        sign: Sign,
        integer_part: Magnitude,
        fraction: FractionDigits,
    ) -> Self
    {
        let zero = integer_part == Magnitude::zero() && fraction == FractionDigits::none();
        let sign = if zero { Sign::NonNegative } else { sign };
        Self {
            sign,
            integer_part,
            fraction,
        }
    }

    /// The literal's sign.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sign(&self) -> Sign
    {
        self.sign
    }

    /// The literal's integral part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn integer_part(&self) -> &Magnitude
    {
        &self.integer_part
    }

    /// The literal's fractional part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fraction(&self) -> &FractionDigits
    {
        &self.fraction
    }
}

/// A canonical 64-bit binary floating-point literal (IEEE 754 binary64),
/// inhabiting [`BaseType::Float64`], held as its bit pattern.
///
/// Every NaN collapses to the one quiet NaN [`Self::NAN`], so syntactic
/// equality of two literals is equality of their bit patterns and every NaN
/// is one value. The two zeros stay distinct: `-0.0` and `0.0` are different
/// bit patterns, and IEEE comparison, not literal equality, equates them.
///
/// # Specification
/// - requires: the payload is obtained through its owning smart constructors.
/// - ensures: stores a bit pattern that is either a non-NaN binary64 value or
///   [`Self::NAN`].
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its smart
///   constructors carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L3 — decimal spellings parse to the correctly rounded value,
///   every NaN payload collapses to the one quiet NaN, the two zeros stay apart
///   and malformed spellings are refused.
/// - witness: `base::tests::a_float64_literal_is_its_rounded_bit_pattern`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Float64Literal(u64);

impl Float64Literal
{
    /// The one NaN a literal holds: the quiet NaN with an empty payload.
    pub const NAN: Self = Self(0x7ff8_0000_0000_0000_u64);
}

impl From<f64> for Float64Literal
{
    /// The literal holding `value`, every NaN collapsed to
    /// [`Float64Literal::NAN`].
    ///
    /// # Specification
    /// - ensures: a NaN `value` is [`Float64Literal::NAN`]; any other is its
    ///   own bit pattern.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a NaN with a payload and a negative NaN collapse to
    ///   one literal; the two zeros and the infinities keep their bits.
    /// - witness: `base::tests::a_float64_literal_is_its_rounded_bit_pattern`
    #[spec(ensures: |ret| if value.is_nan() { ret == Self::NAN } else { ret.0 == value.to_bits() })]
    #[inline]
    fn from(value: f64) -> Self
    {
        if value.is_nan() {
            Self::NAN
        }
        else {
            Self(value.to_bits())
        }
    }
}

impl From<Float64Literal> for f64
{
    /// The value the literal holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(literal: Float64Literal) -> Self
    {
        Self::from_bits(literal.0)
    }
}

impl From<Float64Literal> for u64
{
    /// The literal's bit pattern, which its encodings write.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(literal: Float64Literal) -> Self
    {
        literal.0
    }
}

/// A spelling that is no unsigned decimal number, refused by
/// [`Float64Literal`]'s [`FromStr`] reading.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MalformedDecimal;

impl FromStr for Float64Literal
{
    type Err = MalformedDecimal;

    /// The literal a decimal spelling denotes, rounded to the nearest binary64
    /// value, ties to even.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when `text` is ASCII digits, then optionally a
    ///   `.` and digits, then optionally an exponent `e` or `E`, an optional
    ///   sign and digits; its value is the correctly rounded binary64 value of
    ///   that decimal, infinite past the largest finite value.
    /// - fails: [`MalformedDecimal`] for any other spelling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`MalformedDecimal`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `0.2`, `1e-7` and `2.5E3` read as Rust's correctly
    ///   rounded parse reads them; a sign, a bare dot, a missing exponent digit
    ///   and a word are refused.
    /// - witness: `base::tests::a_float64_literal_is_its_rounded_bit_pattern`
    #[spec(ensures: |ret| ret.is_err() || text.bytes().next().is_some_and(|byte| byte.is_ascii_digit()))]
    #[inline]
    fn from_str(text: &str) -> Result<Self, MalformedDecimal>
    {
        let bytes = text.as_bytes();
        let digits = |from: usize| {
            bytes.get(from ..).map_or(0, |rest| {
                rest.iter().take_while(|byte| byte.is_ascii_digit()).count()
            })
        };
        let past = |at: usize, count: usize| at.checked_add(count).ok_or(MalformedDecimal);
        let whole = digits(0);
        if whole == 0 {
            return Err(MalformedDecimal);
        }
        let mut at = whole;
        if bytes.get(at) == Some(&b'.') {
            let fraction = digits(past(at, 1)?);
            if fraction == 0 {
                return Err(MalformedDecimal);
            }
            at = past(past(at, 1)?, fraction)?;
        }
        if matches!(bytes.get(at), Some(&(b'e' | b'E'))) {
            at = past(at, 1)?;
            if matches!(bytes.get(at), Some(&(b'+' | b'-'))) {
                at = past(at, 1)?;
            }
            let exponent = digits(at);
            if exponent == 0 {
                return Err(MalformedDecimal);
            }
            at = past(at, exponent)?;
        }
        if at != bytes.len() {
            return Err(MalformedDecimal);
        }
        text.parse::<f64>()
            .map(Self::from)
            .map_err(|_unparsed| MalformedDecimal)
    }
}
/// A literal value: one of the four rigid base-type atoms' canonical payloads.
///
/// # Specification
/// - requires: the payload is obtained through its owning smart constructors.
/// - ensures: retains the canonical payload of its variant and selects the
///   corresponding rigid base-type atom.
/// - panics: none.
/// - executable: none — this data carrier has no invocation boundary; its smart
///   constructors and variant projection carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L2 agreement compares every decimal value from zero through 99
///   with independently formatted canonical digits, padded forms, and explicit
///   empty, invalid ASCII and Unicode near-misses. L3 observes exact payload
///   bytes, the zero/nonzero sign boundary and all literal variants; it
///   separates digit loss, wrong trimming direction, negative zero and atom
///   substitution. Arbitrarily long payloads and allocation refusal are outside
///   these witnesses.
/// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
/// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Literal
{
    /// An integer literal, inhabiting [`BaseType::Integer`].
    Integer(IntegerLiteral),
    /// A string literal, inhabiting [`BaseType::String`].
    Text(StringLiteral),
    /// A numeric literal, inhabiting [`BaseType::Numeric`].
    Numeric(NumericLiteral),
    /// A character literal, inhabiting [`BaseType::Character`].
    Character(CharacterLiteral),
    /// A 64-bit floating-point literal, inhabiting [`BaseType::Float64`].
    Float64(Float64Literal),
}

impl Literal
{
    /// The rigid base-type atom this literal inhabits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: maps an integer literal to [`BaseType::Integer`], a text
    ///   literal to [`BaseType::String`], a numeric literal to
    ///   [`BaseType::Numeric`], a character literal to [`BaseType::Character`],
    ///   and a floating-point literal to [`BaseType::Float64`].
    /// - provides: the total variant-to-atom map the checker reads, so a
    ///   literal's base type is decided by its payload rather than by an
    ///   annotation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement compares every decimal value from zero
    ///   through 99 with independently formatted canonical digits, padded
    ///   forms, and explicit empty, invalid ASCII and Unicode near-misses. L3
    ///   observes exact payload bytes, the zero/nonzero sign boundary and all
    ///   literal variants; it separates digit loss, wrong trimming direction,
    ///   negative zero and atom substitution. Arbitrarily long payloads and
    ///   allocation refusal are outside these witnesses.
    /// - witness: `base::tests::a_literal_reports_its_base_type_atom`
    /// - witness: `base::tests::decimal_normalization_matches_a_numeric_reference`
    /// - witness: `base::tests::literal_constructors_preserve_payloads_and_zero_signs`
    #[spec(
        ensures: |ret| matches!((self, ret), (&Self::Integer(_), BaseType::Integer) | (&Self::Text(_), BaseType::String) | (&Self::Numeric(_), BaseType::Numeric) | (&Self::Character(_), BaseType::Character) | (&Self::Float64(_), BaseType::Float64)),
    )]
    #[inline]
    #[must_use]
    pub const fn base_type(&self) -> BaseType
    {
        match *self {
            Self::Integer(_) => BaseType::Integer,
            Self::Text(_) => BaseType::String,
            Self::Numeric(_) => BaseType::Numeric,
            Self::Character(_) => BaseType::Character,
            Self::Float64(_) => BaseType::Float64,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use super::BaseType;
    use super::CharacterLiteral;
    use super::Float64Literal;
    use super::FractionDigits;
    use super::IntegerLiteral;
    use super::Literal;
    use super::Magnitude;
    use super::MalformedDecimal;
    use super::NotOneCharacter;
    use super::NumericLiteral;
    use super::Sign;
    use super::StringLiteral;

    #[test]
    fn magnitude_strips_leading_zeros()
    {
        let padded = Magnitude::from_decimal_text(String::from("007"));
        let bare = Magnitude::from_decimal_text(String::from("7"));
        assert_eq!(bare, padded, "leading zeros canonicalize away");
    }

    #[test]
    fn an_all_zero_magnitude_collapses_to_one_zero()
    {
        assert_eq!(
            Some(Magnitude::zero()),
            Magnitude::from_decimal_text(String::from("000")),
            "an all-zero magnitude is the canonical zero"
        );
    }

    #[test]
    fn magnitude_refuses_non_digits_and_the_empty_text()
    {
        assert_eq!(
            None,
            Magnitude::from_decimal_text(String::from("1a2")),
            "a non-digit character makes the magnitude unrepresentable"
        );
        assert_eq!(
            None,
            Magnitude::from_decimal_text(String::new()),
            "the empty text is not a decimal integer"
        );
    }

    #[test]
    fn fraction_strips_trailing_zeros()
    {
        let padded = FractionDigits::from_decimal_text(String::from("50"));
        let bare = FractionDigits::from_decimal_text(String::from("5"));
        assert_eq!(bare, padded, "trailing zeros canonicalize away");
        assert_eq!(
            Some(FractionDigits::none()),
            FractionDigits::from_decimal_text(String::from("00")),
            "an all-zero fraction is the empty fraction"
        );
    }

    #[test]
    fn fraction_refuses_non_digits()
    {
        assert_eq!(
            None,
            FractionDigits::from_decimal_text(String::from("5x")),
            "a non-digit character makes the fraction unrepresentable"
        );
    }

    #[test]
    fn a_negative_zero_integer_is_pinned_non_negative()
    {
        let negative = IntegerLiteral::new(Sign::Negative, Magnitude::zero());
        let positive = IntegerLiteral::new(Sign::NonNegative, Magnitude::zero());
        assert_eq!(positive, negative, "a negative zero canonicalizes away");
        assert_eq!(Sign::NonNegative, negative.sign(), "zero is non-negative");
        let one = Magnitude::from_decimal_text(String::from("1")).expect("one is decimal digits");
        assert_eq!(
            Sign::Negative,
            IntegerLiteral::new(Sign::Negative, one).sign(),
            "a non-zero magnitude keeps its sign"
        );
    }

    #[test]
    fn numeric_equality_ignores_representation_padding()
    {
        let digits = |text: &str| {
            Magnitude::from_decimal_text(String::from(text)).expect("decimal digits parse")
        };
        let fraction = |text: &str| {
            FractionDigits::from_decimal_text(String::from(text)).expect("decimal digits parse")
        };
        let long = NumericLiteral::new(Sign::NonNegative, digits("01"), fraction("50"));
        let short = NumericLiteral::new(Sign::NonNegative, digits("1"), fraction("5"));
        assert_eq!(short, long, "1.50 and 01.5 denote the same numeric value");
    }

    #[test]
    fn a_negative_zero_numeric_is_pinned_non_negative()
    {
        let negative =
            NumericLiteral::new(Sign::Negative, Magnitude::zero(), FractionDigits::none());
        assert_eq!(
            Sign::NonNegative,
            negative.sign(),
            "the numeric zero is non-negative"
        );
    }

    #[test]
    fn a_literal_reports_its_base_type_atom()
    {
        let integer = Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero()));
        let text = Literal::Text(StringLiteral::new(String::from("hi")));
        let numeric = Literal::Numeric(NumericLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
            FractionDigits::none(),
        ));
        assert_eq!(BaseType::Integer, integer.base_type(), "the integer atom");
        assert_eq!(BaseType::String, text.base_type(), "the string atom");
        assert_eq!(BaseType::Numeric, numeric.base_type(), "the numeric atom");
        let character = Literal::Character(CharacterLiteral::from('a'));
        assert_eq!(
            BaseType::Character,
            character.base_type(),
            "the character atom"
        );
        assert_eq!(
            BaseType::Float64,
            Literal::Float64(Float64Literal::from(0.5_f64)).base_type(),
            "the floating-point atom"
        );
    }

    #[test]
    fn a_character_literal_holds_exactly_one_scalar()
    {
        for scalar in ['a', '\0', 'é', '€', '𐐀'] {
            let wrapped = CharacterLiteral::from(scalar);
            assert_eq!(scalar, char::from(wrapped), "the scalar is held verbatim");
            assert_eq!(
                String::from(scalar),
                wrapped.to_text(),
                "the text is the scalar"
            );
            assert_eq!(
                Ok(wrapped),
                CharacterLiteral::try_from(String::from(scalar)),
                "one scalar's text reads back as its character"
            );
        }
        assert_eq!(
            Err(NotOneCharacter::Empty),
            CharacterLiteral::try_from(String::new()),
            "the empty text holds no character"
        );
        for several in ["ab", "e\u{301}", "𐐀a"] {
            assert_eq!(
                Err(NotOneCharacter::Several),
                CharacterLiteral::try_from(String::from(several)),
                "{several:?} holds more than one scalar"
            );
        }
    }

    #[test]
    fn a_float64_literal_is_its_rounded_bit_pattern()
    {
        for (text, value) in [
            ("0.2", 0.2_f64),
            ("1e-7", 1.0e-7_f64),
            ("2.5E3", 2500.0_f64),
            ("7", 7.0_f64),
            ("1e400", f64::INFINITY),
        ] {
            assert_eq!(
                text.parse::<Float64Literal>().map(u64::from),
                Ok(value.to_bits()),
                "{text} is the correctly rounded binary64 value"
            );
        }
        for text in [
            "", "-1", "+1", ".5", "5.", "1e", "1e+", "inf", "NaN", "0x1", "1.5f64",
        ] {
            assert_eq!(
                text.parse::<Float64Literal>(),
                Err(MalformedDecimal),
                "{text:?} is no decimal spelling"
            );
        }
        let payload = f64::from_bits(0x7ff8_0000_0000_0001_u64);
        assert_eq!(Float64Literal::from(payload), Float64Literal::NAN);
        assert_eq!(Float64Literal::from(-f64::NAN), Float64Literal::NAN);
        assert_eq!(
            Float64Literal::from(f64::from_bits(0xfff0_0000_0000_0001_u64)),
            Float64Literal::NAN,
            "a signalling NaN pattern collapses"
        );
        assert_ne!(
            Float64Literal::from(-0.0_f64),
            Float64Literal::from(0.0_f64),
            "the two zeros are distinct literals"
        );
        assert_eq!(
            u64::from(Float64Literal::from(f64::NEG_INFINITY)),
            f64::NEG_INFINITY.to_bits(),
            "an infinity keeps its bits"
        );
    }

    #[test]
    fn decimal_normalization_matches_a_numeric_reference()
    {
        assert_eq!("0", Magnitude::zero().as_ref());
        assert_eq!("", FractionDigits::none().as_ref());
        assert_eq!(None, Magnitude::from_decimal_text(String::new()));
        assert_eq!(
            Some(FractionDigits::none()),
            FractionDigits::from_decimal_text(String::new())
        );
        for number in 0u16 ..= 99 {
            let canonical = alloc::format!("{number}");
            for prefix in ["", "0", "000"] {
                let input = alloc::format!("{prefix}{number}");
                let magnitude = Magnitude::from_decimal_text(input).expect("ASCII decimal input");
                assert_eq!(canonical, magnitude.as_ref());
                assert_eq!(canonical, magnitude.to_digits());
            }
            let fractional = if number == 0 {
                String::new()
            }
            else if number.is_multiple_of(10) {
                alloc::format!("{}", number.div_euclid(10))
            }
            else {
                alloc::format!("{number:02}")
            };
            for suffix in ["", "0", "000"] {
                let input = alloc::format!("{number:02}{suffix}");
                let fraction =
                    FractionDigits::from_decimal_text(input).expect("ASCII fractional input");
                assert_eq!(fractional, fraction.as_ref());
                assert_eq!(fractional, fraction.to_digits());
            }
        }
        for invalid in [
            "/", ":", "-1", "+1", "1.0", " 1", "1 ", "1\0", "é", "١", "𝟡",
        ] {
            assert_eq!(None, Magnitude::from_decimal_text(String::from(invalid)));
            assert_eq!(
                None,
                FractionDigits::from_decimal_text(String::from(invalid))
            );
        }
    }

    #[test]
    fn literal_constructors_preserve_payloads_and_zero_signs()
    {
        for sign in [Sign::Negative, Sign::NonNegative] {
            for digits in ["0", "7", "908"] {
                let integer = IntegerLiteral::new(
                    sign,
                    Magnitude::from_decimal_text(String::from(digits))
                        .expect("canonical magnitude"),
                );
                assert_eq!(digits, integer.magnitude().as_ref());
                assert_eq!(
                    if digits == "0" {
                        Sign::NonNegative
                    }
                    else {
                        sign
                    },
                    integer.sign()
                );
                assert_eq!(BaseType::Integer, Literal::Integer(integer).base_type());
                for fraction in ["", "01", "5"] {
                    let numeric = NumericLiteral::new(
                        sign,
                        Magnitude::from_decimal_text(String::from(digits))
                            .expect("canonical magnitude"),
                        FractionDigits::from_decimal_text(String::from(fraction))
                            .expect("canonical fraction"),
                    );
                    assert_eq!(digits, numeric.integer_part().as_ref());
                    assert_eq!(fraction, numeric.fraction().as_ref());
                    assert_eq!(
                        if digits == "0" && fraction.is_empty() {
                            Sign::NonNegative
                        }
                        else {
                            sign
                        },
                        numeric.sign()
                    );
                    assert_eq!(BaseType::Numeric, Literal::Numeric(numeric).base_type());
                }
            }
        }
        for text in ["", "\0", "é", "𐐀", "a\r\nb", "e\u{301}"] {
            let literal = StringLiteral::new(String::from(text));
            assert_eq!(text, literal.as_ref());
            assert_eq!(text, literal.to_content());
            assert_eq!(BaseType::String, Literal::Text(literal).base_type());
        }
    }
}
