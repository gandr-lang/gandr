//! The literal identity tests: the native operations the kernel computes.
//!
//! A native operation of the core's prelude crosses to the kernel as an axiom
//! of its table type, and the kernel never runs it. Four rows are the
//! exception: `string.eq`, `int.eq`, `eq` and `ne` ask whether two literals
//! are the same literal. A literal's payload is canonical, so two literals of
//! one base type are the same literal exactly when their payloads are equal.
//! The kernel decides that by its own comparison. Its conversion computes such
//! a test where both arguments are literals, and a test over anything else
//! stays stuck, as an axiom does.
//!
//! The answer is an injection into `1 + 1`, the core's booleans: the left
//! summand when the test holds, the right summand when it does not.
//!
//! **Choice.** A declaration form of its own beside the axioms, admitted only
//! at the one type its base gives, `U(B → B → F(1 + 1))`. It is priced as
//! trusted surface: the kernel's own comparison of canonical payloads, with no
//! host arithmetic. An audit reports it as a kernel primitive and not as an
//! axiom, because the kernel computes it. Only integers and texts take the
//! form. Floating-point equality is no identity of literals, since a NaN
//! differs from itself and the two zeros are equal. Ordering and arithmetic
//! need an evaluator the kernel does not hold. Revisit when a certified
//! evaluator lets a row compute past identity.
//!
//! # References
//!
//! - `vault:01a178aa-50dc-70f1-8a3c-3cb1c31f530e` — anchor: a computational
//!   kernel primitive is admissible, priced as permanent trusted surface, and
//!   the audit names it.
//!
//! # Witnesses
//! - `literal_identity::tests::a_test_answers_by_payload_and_refuses_another_base`

use anodized::spec;

use crate::BaseType;
use crate::Literal;
use crate::Summand;

/// The base type a literal identity test compares at.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum IdentityBase
{
    /// Arbitrary-precision integers.
    Integer,
    /// Texts.
    Text,
}

impl IdentityBase
{
    /// The base-type atom this base names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn base_type(self) -> BaseType
    {
        match self {
            Self::Integer => BaseType::Integer,
            Self::Text => BaseType::String,
        }
    }
}

/// Whether a test holds where its two literals are the same, or where they
/// differ.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Polarity
{
    /// The test holds where its literals are the same literal.
    Same,
    /// The test holds where its literals differ.
    Different,
}

/// A literal identity test: a base and a polarity.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LiteralIdentity
{
    /// The base type both literals stand at.
    base: IdentityBase,
    /// Whether the test holds on the same literals or on different ones.
    polarity: Polarity,
}

impl LiteralIdentity
{
    /// The test at `base` with `polarity`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        base: IdentityBase,
        polarity: Polarity,
    ) -> Self
    {
        Self { base, polarity }
    }

    /// The base type both literals stand at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn base(self) -> IdentityBase
    {
        self.base
    }

    /// Whether the test holds on the same literals or on different ones.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn polarity(self) -> Polarity
    {
        self.polarity
    }

    /// The summand of `1 + 1` the test answers at `left` and `right`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `None` unless both literals stand at this test's base;
    ///   otherwise the left summand exactly when the test holds, the payloads
    ///   equal for [`Polarity::Same`] and unequal for [`Polarity::Different`],
    ///   and the right summand when it does not.
    /// - provides: the one comparison the kernel's reduction and the checker's
    ///   evaluation both run.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal and unequal integers and texts at both
    ///   polarities, texts equal only up to Unicode normalisation, and a
    ///   literal of another base on either side.
    /// - witness: `literal_identity::tests::a_test_answers_by_payload_and_refuses_another_base`
    #[spec(ensures: |ret| ret.map_or_else(
        || left.base_type() != self.base.base_type() || right.base_type() != self.base.base_type(),
        |summand| left.base_type() == self.base.base_type()
            && right.base_type() == self.base.base_type()
            && (summand == Summand::from(0_usize))
                == ((left == right) == (self.polarity == Polarity::Same)),
    ))]
    #[inline]
    #[must_use]
    pub fn answer(
        self,
        left: &Literal,
        right: &Literal,
    ) -> Option<Summand>
    {
        let base = self.base.base_type();
        if left.base_type() != base || right.base_type() != base {
            return None;
        }
        let holds = (left == right) == (self.polarity == Polarity::Same);
        Some(Summand::from(usize::from(!holds)))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::string::ToString as _;

    use super::IdentityBase;
    use super::LiteralIdentity;
    use super::Polarity;
    use crate::IntegerLiteral;
    use crate::Literal;
    use crate::Magnitude;
    use crate::Sign;
    use crate::StringLiteral;
    use crate::Summand;

    #[test]
    fn a_test_answers_by_payload_and_refuses_another_base()
    {
        let integer = |value: i64| {
            let sign = if value < 0 {
                Sign::Negative
            }
            else {
                Sign::NonNegative
            };
            let magnitude = Magnitude::from_decimal_text(value.unsigned_abs().to_string())
                .expect("decimal digits");
            Literal::Integer(IntegerLiteral::new(sign, magnitude))
        };
        let text = |value: &str| Literal::Text(StringLiteral::new(String::from(value)));
        let (yes, no) = (Some(Summand::from(0_usize)), Some(Summand::from(1_usize)));
        let same = |base| LiteralIdentity::new(base, Polarity::Same);
        let different = |base| LiteralIdentity::new(base, Polarity::Different);
        assert_eq!(
            same(IdentityBase::Integer).answer(&integer(-7), &integer(-7)),
            yes
        );
        assert_eq!(
            same(IdentityBase::Integer).answer(&integer(7), &integer(-7)),
            no
        );
        assert_eq!(
            different(IdentityBase::Integer).answer(&integer(7), &integer(-7)),
            yes
        );
        assert_eq!(
            different(IdentityBase::Integer).answer(&integer(0), &integer(0)),
            no
        );
        assert_eq!(same(IdentityBase::Text).answer(&text(""), &text("")), yes);
        assert_eq!(
            same(IdentityBase::Text).answer(&text("é"), &text("e\u{301}")),
            no,
            "bytes, not a normal form"
        );
        assert_eq!(
            same(IdentityBase::Text).answer(&integer(1), &integer(1)),
            None,
            "an integer is no text"
        );
        assert_eq!(
            same(IdentityBase::Integer).answer(&integer(1), &text("1")),
            None,
            "a text on either side is refused"
        );
    }
}
