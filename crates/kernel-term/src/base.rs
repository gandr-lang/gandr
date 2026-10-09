//! The rigid base-type atoms and the literal stock, each held in a canonical
//! form its smart constructor maintains.
//!
//! The base-type atoms are rigid and closed: the stock is exactly the three the
//! literal forms name — an integer atom, a string atom, and a numeric atom.
//!
//! Literal payloads are canonical and structurally comparable — leading and
//! trailing zeros normalized, the zero sign pinned — so syntactic equality of
//! two literals coincides with equality of the values they denote. That is what
//! lets the format's content-keyed deduplication collapse two spellings of one
//! literal, and what makes a non-canonical literal unrepresentable in memory
//! rather than merely rejected on the wire.

use alloc::string::String;

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
    #[inline]
    #[must_use]
    pub fn zero() -> Self
    {
        Self(String::from("0"))
    }

    /// Build a canonical magnitude from decimal digit text.
    ///
    /// # Specification
    /// - requires: `text` is intended as an unsigned decimal integer.
    /// - ensures: `Some(magnitude)` with leading zeros stripped and the
    ///   all-zero case collapsed to `0`, when every character is an ASCII
    ///   digit; the result compares equal exactly to magnitudes of the same
    ///   integer value.
    /// - provides: the canonical, structurally comparable magnitude of an
    ///   integer or numeric literal. The clause checks decimal acceptance.
    ///   Caller intent and exact digit preservation stay prose: `text` is
    ///   consumed and mutated, so comparing its entry bytes would require an
    ///   allocating capture even without checks.
    /// - fails: returns `None` when `text` is empty or holds a non-digit
    ///   character — a malformed magnitude is not representable.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the canonicalization and its guard are separated by
    ///   the padded, all-zero, empty and non-digit inputs, each asserted
    ///   exactly.
    /// - witness: `base::tests::magnitude_strips_leading_zeros`
    /// - witness: `base::tests::an_all_zero_magnitude_collapses_to_one_zero`
    /// - witness: `base::tests::magnitude_refuses_non_digits_and_the_empty_text`
    #[inline]
    #[must_use]
    #[spec(
        captures: entry_is_decimal = !text.is_empty()
            && text.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ret| ret.is_some() == entry_is_decimal,
    )]
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
    #[inline]
    #[must_use]
    pub fn none() -> Self
    {
        Self(String::new())
    }

    /// Build a canonical fraction from decimal digit text.
    ///
    /// # Specification
    /// - requires: `text` is intended as the digits after a decimal point.
    /// - ensures: `Some(fraction)` with trailing zeros stripped, when every
    ///   character is an ASCII digit; the result compares equal exactly to
    ///   fractions denoting the same value.
    /// - provides: the canonical, structurally comparable fractional part of a
    ///   numeric literal. The clause checks decimal acceptance. Caller intent
    ///   and exact digit preservation stay prose: `text` is consumed and
    ///   mutated, so comparing its entry bytes would require an allocating
    ///   capture even without checks.
    /// - fails: returns `None` on a non-digit character.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the truncation and its guard are separated by the
    ///   trailing-zero, all-zero and non-digit inputs, each asserted exactly.
    /// - witness: `base::tests::fraction_strips_trailing_zeros`
    /// - witness: `base::tests::fraction_refuses_non_digits`
    #[inline]
    #[must_use]
    #[spec(
        captures: entry_is_decimal = text.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ret| ret.is_some() == entry_is_decimal,
    )]
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
    /// - hypothesis: L3 — the sign pin has one decision surface, separated by
    ///   the zero magnitude against a non-zero one.
    /// - witness: `base::tests::a_negative_zero_integer_is_pinned_non_negative`
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
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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

/// A canonical numeric literal: a [`Sign`], an integral [`Magnitude`], and a
/// [`FractionDigits`] fractional part, inhabiting [`BaseType::Numeric`].
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
    /// - hypothesis: L3 — the sign pin has one decision surface, separated by
    ///   the zero value against a padded non-zero one whose canonical form must
    ///   still compare equal to its unpadded spelling.
    /// - witness: `base::tests::a_negative_zero_numeric_is_pinned_non_negative`
    /// - witness: `base::tests::numeric_equality_ignores_representation_padding`
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

/// A literal value: one of the three rigid base-type atoms' canonical payloads.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Literal
{
    /// An integer literal, inhabiting [`BaseType::Integer`].
    Integer(IntegerLiteral),
    /// A string literal, inhabiting [`BaseType::String`].
    Text(StringLiteral),
    /// A numeric literal, inhabiting [`BaseType::Numeric`].
    Numeric(NumericLiteral),
}

impl Literal
{
    /// The rigid base-type atom this literal inhabits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: maps an integer literal to [`BaseType::Integer`], a text
    ///   literal to [`BaseType::String`], and a numeric literal to
    ///   [`BaseType::Numeric`].
    /// - provides: the total variant-to-atom map the checker reads, so a
    ///   literal's base type is decided by its payload rather than by an
    ///   annotation.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn base_type(&self) -> BaseType
    {
        match *self {
            | Self::Integer(_) => BaseType::Integer,
            | Self::Text(_) => BaseType::String,
            | Self::Numeric(_) => BaseType::Numeric,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use super::BaseType;
    use super::FractionDigits;
    use super::IntegerLiteral;
    use super::Literal;
    use super::Magnitude;
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
    }
}
