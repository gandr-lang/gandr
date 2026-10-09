//! The stable diagnostic codes and their localizable message arguments.
//!
//! A code is an identity: allocated once, in its registry row, and never
//! reused. A message is the code's template with its arguments filled; the
//! arguments are the data, and the prose is a projection of them.

use alloc::string::String;
use core::fmt;

/// One localizable message template, its arguments named in braces.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DiagnosticTemplate(&'static str);

impl fmt::Display for DiagnosticTemplate
{
    /// Write the template with its argument slots unfilled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the registered template exactly, braces included.
    /// - provides: the text a translation keys on.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// The stable spelling of a code, read only by its display, its parse and its
/// wire image.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct DiagnosticCodeText(&'static str);

/// Declares the complete code registry: the enum, the allocation-ordered
/// list, and the two per-code tables.
///
/// A code's spelling and its template each occur once, in the code's row.
macro_rules! diagnostic_registry {
    ($( #[doc = $doc:literal] $variant:ident => ($code:literal, $template:literal) ),+ $(,)?) => {
        /// A stable diagnostic identifier, spelled by a severity letter and its
        /// allocation number.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum DiagnosticCode
        {
            $(
                #[doc = $doc]
                $variant,
            )+
        }

        /// Every allocated diagnostic code, in allocation order.
        pub const DIAGNOSTIC_CODES: &[DiagnosticCode] = &[
            $(DiagnosticCode::$variant,)+
        ];

        impl DiagnosticCode
        {
            /// The stable spelling of this code.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            const fn text(self) -> DiagnosticCodeText
            {
                match self {
                    $(Self::$variant => DiagnosticCodeText($code),)+
                }
            }

            /// The localizable message template registered for this code.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            #[must_use]
            pub const fn template(self) -> DiagnosticTemplate
            {
                match self {
                    $(Self::$variant => DiagnosticTemplate($template),)+
                }
            }
        }
    };
}

diagnostic_registry! {
    /// A synthesised type that does not convert to the expected one.
    TypeMismatch => ("E0001", "type mismatch: expected {expected}, actual {actual}"),
    /// A type of another former than the rule requires.
    ShapeMismatch => ("E0002", "type shape mismatch: expected {expected_shape}, actual {actual}"),
    /// A term no typing rule applies to.
    StuckExpression => ("E0003", "no typing rule applies to term {expression}: {hint}"),
    /// A name no scope binds.
    UnboundVariable => ("E0004", "variable is unbound: {name}"),
    /// A grade that does not sit below the grade it must.
    GradeOrder => ("E0005", "grade order requirement failed: {lower} ⊑ {upper} does not hold"),
    /// An attribute name the registry does not hold.
    UnknownAttribute => ("E0006", "unknown attribute `{name}`{suggestion}"),
    /// A single-valued attribute written twice.
    DuplicateAttribute => ("E0007", "duplicate attribute `{name}` (single-valued)"),
    /// An attribute written without the payload its schema requires.
    MissingAttributePayload => ("E0008", "attribute `{name}` requires a payload"),
    /// An attribute payload that is a computation, not a value.
    NonValueAttributePayload => ("E0009", "attribute `{name}` payload must be a value, not a computation"),
    /// A declaration that takes a prelude or host name the policy lets it take.
    ShadowedName => ("W0010", "`{path}` is a prelude or host name; this declaration takes it, and the policy allows it"),
    /// A message the registry has no template for.
    Other => ("E0011", "{message}"),
    /// A parse the recovering parser repaired.
    ParseRepair => ("W0012", "parse repaired: {class}"),
}

/// The refusal of a spelling no registry row carries.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnknownDiagnosticCode;

impl fmt::Display for UnknownDiagnosticCode
{
    /// Write the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str("no diagnostic code has this spelling")
    }
}

impl core::error::Error for UnknownDiagnosticCode
{
}

impl core::str::FromStr for DiagnosticCode
{
    type Err = UnknownDiagnosticCode;

    /// The code `spelling` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the one code whose stable spelling is exactly
    ///   `spelling`, matched byte for byte.
    /// - provides: the inverse of the code's display.
    /// - fails: [`UnknownDiagnosticCode`] for any other spelling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`UnknownDiagnosticCode`] when no row carries `spelling`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every allocated spelling parses back to its own code,
    ///   which separates a lookup that confuses two rows; an unallocated
    ///   spelling separates one that accepts a near miss.
    /// - witness: `diagnostic::tests::registry_codes_are_dense_unique_and_round_trip`
    #[inline]
    fn from_str(spelling: &str) -> Result<Self, Self::Err>
    {
        DIAGNOSTIC_CODES
            .iter()
            .copied()
            .find(|code| code.text().0 == spelling)
            .ok_or(UnknownDiagnosticCode)
    }
}

impl fmt::Display for DiagnosticCode
{
    /// Write the code's stable spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.text().0)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for DiagnosticCode
{
    /// Encode the code as its stable spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the wire image is the spelling the display writes.
    /// - fails: propagates the serializer's own error.
    /// - panics: none.
    ///
    /// # Errors
    /// The serializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one code's exact wire string separates the spelling
    ///   from the variant name.
    /// - witness: `diagnostic::tests::code_wire_image_is_its_stable_spelling`
    #[inline]
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.text().0)
    }
}

/// Decodes a code from its stable spelling, borrowed or owned.
#[cfg(feature = "serde")]
struct CodeVisitor;

#[cfg(feature = "serde")]
impl serde::de::Visitor<'_> for CodeVisitor
{
    type Value = DiagnosticCode;

    /// Name what the visitor accepts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn expecting(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        formatter.write_str("a registered diagnostic code spelling")
    }

    /// The code the spelling `v` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the code the spelling parses to.
    /// - fails: an invalid-value error quoting the spelling when no row carries
    ///   it.
    /// - panics: none.
    ///
    /// # Errors
    /// The invalid-value error for an unallocated spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact code decoded from its spelling separates a
    ///   visitor that parses from one that defaults.
    /// - witness: `diagnostic::tests::code_wire_image_is_its_stable_spelling`
    #[inline]
    fn visit_str<E>(
        self,
        v: &str,
    ) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        match v.parse() {
            | Ok(code) => Ok(code),
            | Err(UnknownDiagnosticCode) => {
                Err(E::invalid_value(serde::de::Unexpected::Str(v), &self))
            },
        }
    }
}

#[cfg(feature = "serde")]
impl<'input> serde::Deserialize<'input> for DiagnosticCode
{
    /// Decode a code from its stable spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the code whose spelling the image carries.
    /// - fails: the deserializer's error for a non-string image, and the
    ///   invalid-value error for an unallocated spelling.
    /// - panics: none.
    ///
    /// # Errors
    /// The deserializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a spelling decoded to its code, and an unallocated
    ///   one refused, separate the registry decode from a permissive one.
    /// - witness: `diagnostic::tests::code_wire_image_is_its_stable_spelling`
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'input>,
    {
        deserializer.deserialize_str(CodeVisitor)
    }
}

/// A diagnostic's template identity and its named arguments.
///
/// The variant is the template; its fields are the arguments. The rendered
/// prose is the display, never stored.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(tag = "message_template", content = "message_arguments")
)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DiagnosticMessage
{
    /// The arguments of [`DiagnosticCode::TypeMismatch`].
    TypeMismatch
    {
        /// The expected type.
        expected: String,
        /// The actual type.
        actual: String,
    },
    /// The arguments of [`DiagnosticCode::ShapeMismatch`].
    ShapeMismatch
    {
        /// The expected shape.
        expected_shape: String,
        /// The actual type.
        actual: String,
    },
    /// The arguments of [`DiagnosticCode::StuckExpression`].
    StuckExpression
    {
        /// The offending expression.
        expression: String,
        /// The progress hint.
        hint: String,
    },
    /// The arguments of [`DiagnosticCode::UnboundVariable`].
    UnboundVariable
    {
        /// The unbound name.
        name: String,
    },
    /// The arguments of [`DiagnosticCode::GradeOrder`].
    GradeOrder
    {
        /// The lower grade.
        lower: String,
        /// The upper grade.
        upper: String,
    },
    /// The arguments of [`DiagnosticCode::UnknownAttribute`].
    UnknownAttribute
    {
        /// The unknown name.
        name: String,
        /// The nearest registered name, absent when none is near.
        suggestion: Option<String>,
    },
    /// The arguments of [`DiagnosticCode::DuplicateAttribute`].
    DuplicateAttribute
    {
        /// The duplicated name.
        name: String,
    },
    /// The arguments of [`DiagnosticCode::MissingAttributePayload`].
    MissingAttributePayload
    {
        /// The attribute name.
        name: String,
    },
    /// The arguments of [`DiagnosticCode::NonValueAttributePayload`].
    NonValueAttributePayload
    {
        /// The attribute name.
        name: String,
    },
    /// The arguments of [`DiagnosticCode::ShadowedName`].
    ShadowedName
    {
        /// The taken path.
        path: String,
    },
    /// The arguments of [`DiagnosticCode::ParseRepair`].
    ParseRepair
    {
        /// The repair's class.
        class: String,
    },
    /// The arguments of [`DiagnosticCode::Other`].
    Other
    {
        /// The rendered message.
        message: String,
    },
}

impl DiagnosticMessage
{
    /// The registry code of this message's template.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the code named like the variant, whatever the
    ///   arguments.
    /// - provides: the identity a renderer and a translation key on.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two messages of one variant with different arguments
    ///   answer one code, which separates a code read off the arguments.
    /// - witness: `diagnostic::tests::one_message_kind_has_one_code_independent_of_arguments`
    #[inline]
    #[must_use]
    pub const fn code(&self) -> DiagnosticCode
    {
        match *self {
            | Self::TypeMismatch { .. } => DiagnosticCode::TypeMismatch,
            | Self::ShapeMismatch { .. } => DiagnosticCode::ShapeMismatch,
            | Self::StuckExpression { .. } => DiagnosticCode::StuckExpression,
            | Self::UnboundVariable { .. } => DiagnosticCode::UnboundVariable,
            | Self::GradeOrder { .. } => DiagnosticCode::GradeOrder,
            | Self::UnknownAttribute { .. } => DiagnosticCode::UnknownAttribute,
            | Self::DuplicateAttribute { .. } => DiagnosticCode::DuplicateAttribute,
            | Self::MissingAttributePayload { .. } => DiagnosticCode::MissingAttributePayload,
            | Self::NonValueAttributePayload { .. } => DiagnosticCode::NonValueAttributePayload,
            | Self::ShadowedName { .. } => DiagnosticCode::ShadowedName,
            | Self::ParseRepair { .. } => DiagnosticCode::ParseRepair,
            | Self::Other { .. } => DiagnosticCode::Other,
        }
    }

    /// The localizable template of this message's code.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn template(&self) -> DiagnosticTemplate
    {
        self.code().template()
    }
}

impl fmt::Display for DiagnosticMessage
{
    /// Write the message: its template with the arguments filled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the code's template with each slot replaced by its
    ///   argument; an unknown attribute without a suggestion leaves its
    ///   suggestion slot empty, and one with a suggestion fills it with a
    ///   question naming it.
    /// - provides: the rendered prose a card carries.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two arguments of one variant render two exact
    ///   messages, which separates filling from echoing the template.
    /// - witness: `diagnostic::tests::one_message_kind_has_one_code_independent_of_arguments`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::TypeMismatch {
                ref expected,
                ref actual,
            } => write!(f, "type mismatch: expected {expected}, actual {actual}"),
            | Self::ShapeMismatch {
                ref expected_shape,
                ref actual,
            } => write!(
                f,
                "type shape mismatch: expected {expected_shape}, actual {actual}"
            ),
            | Self::StuckExpression {
                ref expression,
                ref hint,
            } => write!(f, "no typing rule applies to term {expression}: {hint}"),
            | Self::UnboundVariable { ref name } => write!(f, "variable is unbound: {name}"),
            | Self::GradeOrder {
                ref lower,
                ref upper,
            } => write!(
                f,
                "grade order requirement failed: {lower} ⊑ {upper} does not hold"
            ),
            | Self::UnknownAttribute {
                ref name,
                ref suggestion,
            } => match *suggestion {
                | Some(ref candidate) => {
                    write!(f, "unknown attribute `{name}`; did you mean `{candidate}`?")
                },
                | None => write!(f, "unknown attribute `{name}`"),
            },
            | Self::DuplicateAttribute { ref name } => {
                write!(f, "duplicate attribute `{name}` (single-valued)")
            },
            | Self::MissingAttributePayload { ref name } => {
                write!(f, "attribute `{name}` requires a payload")
            },
            | Self::NonValueAttributePayload { ref name } => {
                write!(
                    f,
                    "attribute `{name}` payload must be a value, not a computation"
                )
            },
            | Self::ShadowedName { ref path } => write!(
                f,
                "`{path}` is a prelude or host name; this declaration takes it, and the policy allows it"
            ),
            | Self::ParseRepair { ref class } => write!(f, "parse repaired: {class}"),
            | Self::Other { ref message } => f.write_str(message),
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::string::ToString as _;

    use super::DIAGNOSTIC_CODES;
    use super::DiagnosticCode;
    use super::DiagnosticMessage;
    use super::UnknownDiagnosticCode;

    #[test]
    fn registry_codes_are_dense_unique_and_round_trip()
    {
        for (index, code) in DIAGNOSTIC_CODES.iter().copied().enumerate() {
            assert!(
                !DIAGNOSTIC_CODES[.. index].contains(&code),
                "{code} is allocated once"
            );
            let spelling = code.to_string();
            let digits = spelling
                .strip_prefix(['E', 'W'])
                .expect("registry codes begin with their severity letter");
            assert_eq!(
                digits.parse::<usize>(),
                Ok(index.saturating_add(1)),
                "{code} is numbered by its allocation"
            );
            assert_eq!(
                spelling.parse::<DiagnosticCode>(),
                Ok(code),
                "{code} parses back to itself"
            );
        }
        assert_eq!(
            "E0013".parse::<DiagnosticCode>(),
            Err(UnknownDiagnosticCode),
            "an unallocated number names no code"
        );
        assert_eq!(
            "e0001".parse::<DiagnosticCode>(),
            Err(UnknownDiagnosticCode),
            "a spelling matches byte for byte"
        );
    }

    #[test]
    fn one_message_kind_has_one_code_independent_of_arguments()
    {
        let first = DiagnosticMessage::UnboundVariable {
            name: String::from("first"),
        };
        let second = DiagnosticMessage::UnboundVariable {
            name: String::from("second"),
        };

        assert_eq!(
            first.code(),
            DiagnosticCode::UnboundVariable,
            "the variant names the code"
        );
        assert_eq!(
            second.code(),
            DiagnosticCode::UnboundVariable,
            "other arguments name the same code"
        );
        assert_eq!(
            first.template().to_string(),
            "variable is unbound: {name}",
            "the template is the code's"
        );
        assert_eq!(
            first.to_string(),
            "variable is unbound: first",
            "the display fills the slot"
        );
        assert_eq!(
            second.to_string(),
            "variable is unbound: second",
            "the display fills the slot with its own argument"
        );
    }

    #[test]
    fn code_wire_image_is_its_stable_spelling()
    {
        let json = serde_json::to_string(&DiagnosticCode::TypeMismatch).unwrap();
        assert_eq!(json, r#""E0001""#, "the wire image is the spelling");
        let decoded = serde_json::from_str::<DiagnosticCode>(&json).unwrap();
        assert_eq!(
            decoded,
            DiagnosticCode::TypeMismatch,
            "the spelling decodes to its code"
        );
        let owned = serde_json::from_value::<DiagnosticCode>(serde_json::json!("W0012")).unwrap();
        assert_eq!(
            owned,
            DiagnosticCode::ParseRepair,
            "an owned spelling decodes too"
        );
        let refused = serde_json::from_str::<DiagnosticCode>(r#""TypeMismatch""#)
            .expect_err("the variant name is not a spelling");
        assert!(
            refused.to_string().contains("TypeMismatch"),
            "the refusal quotes what it read: {refused}"
        );
    }
}
