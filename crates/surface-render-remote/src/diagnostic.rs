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
    /// - executable: none — the formatter exposes write status, not the text
    ///   emitted to its caller-owned sink; the output cannot be inspected here.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the finite registry is observed through the ordered
    ///   argument-slot names of every message template. Missing, renamed or
    ///   exchanged slots are distinguished; English phrasing and arbitrary
    ///   formatter failures are outside this finite successful-write observer.
    /// - witness: `diagnostic::tests::message_templates_preserve_argument_roles`
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
    /// - hypothesis: L3 — every allocated protocol spelling has an independent
    ///   expected identity. Dense allocation, case, padding, shortened numbers
    ///   and a non-ASCII prefix distinguish wrong rows and normalization; an
    ///   unallocated number is refused. The domain is exact UTF-8 spelling.
    /// - witness: `diagnostic::tests::registry_codes_are_dense_unique_and_round_trip`
    #[inline]
    #[anodized::spec(ensures: |ret| match ret {
        | Ok(code) => code.text().0 == spelling,
        | Err(_) => !DIAGNOSTIC_CODES.iter().any(|code| code.text().0 == spelling),
    })]
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
    /// - executable: none — the serializer consumes the encoding operation; its
    ///   generic success value exposes neither the emitted string nor a
    ///   format-independent observation of the output.
    ///
    /// # Errors
    /// The serializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every registered code has an independently stated
    ///   JSON string, distinguishing code identity, a variant-name image and a
    ///   wrong wire kind. Other serializer formats and their sink failures are
    ///   outside this finite wire observer.
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
    /// - hypothesis: L3 — every registered spelling is decoded from borrowed
    ///   and owned JSON strings; unknown spellings and other JSON kinds are
    ///   refused. These distinguish defaulting, alias acceptance and the wrong
    ///   visitor kind within the JSON string boundary.
    /// - witness: `diagnostic::tests::code_wire_image_is_its_stable_spelling`
    #[inline]
    #[anodized::spec(ensures: |ref ret| match *ret {
        | Ok(code) => code.text().0 == v,
        | Err(_) => !DIAGNOSTIC_CODES.iter().any(|code| code.text().0 == v),
    })]
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
    /// - executable: none — the generic deserializer owns and consumes its
    ///   input; the returned code cannot be compared with that hidden image.
    ///   The string visitor checks the relation when the spelling is available.
    ///
    /// # Errors
    /// The deserializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the complete registered vocabulary is decoded from
    ///   borrowed and owned JSON strings; variant names, unknown identifiers
    ///   and non-string kinds are data errors. These distinguish a permissive
    ///   decode and an incorrect wire representation, not every possible serde
    ///   format.
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
    /// - hypothesis: L3 — every message variant, both suggestion branches and
    ///   different arguments of an unbound-variable message are observed by
    ///   their exact code. These distinguish exchanged identities and a code
    ///   derived from payload text across the finite variant vocabulary.
    /// - witness: `diagnostic::tests::one_message_kind_has_one_code_independent_of_arguments`
    /// - witness: `diagnostic::tests::message_templates_preserve_argument_roles`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| matches!((self, ret),
        (&Self::TypeMismatch { .. }, DiagnosticCode::TypeMismatch)
        | (&Self::ShapeMismatch { .. }, DiagnosticCode::ShapeMismatch)
        | (&Self::StuckExpression { .. }, DiagnosticCode::StuckExpression)
        | (&Self::UnboundVariable { .. }, DiagnosticCode::UnboundVariable)
        | (&Self::GradeOrder { .. }, DiagnosticCode::GradeOrder)
        | (&Self::UnknownAttribute { .. }, DiagnosticCode::UnknownAttribute)
        | (&Self::DuplicateAttribute { .. }, DiagnosticCode::DuplicateAttribute)
        | (&Self::MissingAttributePayload { .. }, DiagnosticCode::MissingAttributePayload)
        | (&Self::NonValueAttributePayload { .. }, DiagnosticCode::NonValueAttributePayload)
        | (&Self::ShadowedName { .. }, DiagnosticCode::ShadowedName)
        | (&Self::Other { .. }, DiagnosticCode::Other)
        | (&Self::ParseRepair { .. }, DiagnosticCode::ParseRepair)
    ))]
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
    /// - executable: none — the formatter's sink is opaque, so the emitted
    ///   argument sequence cannot be inspected by a postcondition; its status
    ///   alone does not expose missing, repeated or reordered arguments.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct Unicode and brace-containing arguments in
    ///   every variant, including both suggestion branches, are observed in
    ///   their declared order without unfilled slots. Missing, repeated and
    ///   reordered arguments are distinguished. English phrasing and rejecting
    ///   formatter sinks are not pinned by this successful-write observer.
    /// - witness: `diagnostic::tests::message_templates_preserve_argument_roles`
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

    /// Protocol identities stated independently of display and parse.
    const CODE_CASES: [(DiagnosticCode, &str); 12] = [
        (DiagnosticCode::TypeMismatch, "E0001"),
        (DiagnosticCode::ShapeMismatch, "E0002"),
        (DiagnosticCode::StuckExpression, "E0003"),
        (DiagnosticCode::UnboundVariable, "E0004"),
        (DiagnosticCode::GradeOrder, "E0005"),
        (DiagnosticCode::UnknownAttribute, "E0006"),
        (DiagnosticCode::DuplicateAttribute, "E0007"),
        (DiagnosticCode::MissingAttributePayload, "E0008"),
        (DiagnosticCode::NonValueAttributePayload, "E0009"),
        (DiagnosticCode::ShadowedName, "W0010"),
        (DiagnosticCode::Other, "E0011"),
        (DiagnosticCode::ParseRepair, "W0012"),
    ];

    #[test]
    fn registry_codes_are_dense_unique_and_round_trip()
    {
        for (index, code) in DIAGNOSTIC_CODES.iter().copied().enumerate() {
            assert!(!DIAGNOSTIC_CODES[.. index].contains(&code));
            let spelling = code.to_string();
            let digits = spelling.strip_prefix(['E', 'W']).expect("severity prefix");
            assert_eq!(digits.parse::<usize>(), Ok(index.saturating_add(1)));
        }
        for (expected, spelling) in CODE_CASES {
            assert_eq!(spelling.parse::<DiagnosticCode>(), Ok(expected));
            assert_eq!(expected.to_string(), spelling);
        }
        for spelling in ["E0013", "e0001", " E0001", "E1", "Ｅ0001"] {
            assert_eq!(
                spelling.parse::<DiagnosticCode>(),
                Err(UnknownDiagnosticCode)
            );
        }
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
    }

    #[test]
    fn code_wire_image_is_its_stable_spelling()
    {
        for (code, spelling) in CODE_CASES {
            assert_eq!(
                serde_json::to_value(code).unwrap(),
                serde_json::json!(spelling)
            );
            let image = alloc::format!("\"{spelling}\"");
            assert_eq!(
                serde_json::from_str::<DiagnosticCode>(&image).unwrap(),
                code
            );
            assert_eq!(
                serde_json::from_value::<DiagnosticCode>(serde_json::json!(spelling)).unwrap(),
                code
            );
        }
        for image in [
            serde_json::json!("TypeMismatch"),
            serde_json::json!("E0013"),
            serde_json::json!(null),
            serde_json::json!(false),
            serde_json::json!(1_i32),
            serde_json::json!([]),
            serde_json::json!({}),
        ] {
            assert!(
                serde_json::from_value::<DiagnosticCode>(image)
                    .unwrap_err()
                    .is_data()
            );
        }
    }

    /// Translation slots and payload roles survive every message variant.
    #[test]
    fn message_templates_preserve_argument_roles()
    {
        let first = "α[one]";
        let second = "β{two}";
        let cases: [(DiagnosticMessage, DiagnosticCode, &[&str], &[&str]); 13] = [
            (
                DiagnosticMessage::TypeMismatch {
                    expected: String::from(first),
                    actual: String::from(second),
                },
                DiagnosticCode::TypeMismatch,
                &["expected", "actual"],
                &[first, second],
            ),
            (
                DiagnosticMessage::ShapeMismatch {
                    expected_shape: String::from(first),
                    actual: String::from(second),
                },
                DiagnosticCode::ShapeMismatch,
                &["expected_shape", "actual"],
                &[first, second],
            ),
            (
                DiagnosticMessage::StuckExpression {
                    expression: String::from(first),
                    hint: String::from(second),
                },
                DiagnosticCode::StuckExpression,
                &["expression", "hint"],
                &[first, second],
            ),
            (
                DiagnosticMessage::UnboundVariable {
                    name: String::from(first),
                },
                DiagnosticCode::UnboundVariable,
                &["name"],
                &[first],
            ),
            (
                DiagnosticMessage::GradeOrder {
                    lower: String::from(first),
                    upper: String::from(second),
                },
                DiagnosticCode::GradeOrder,
                &["lower", "upper"],
                &[first, second],
            ),
            (
                DiagnosticMessage::UnknownAttribute {
                    name: String::from(first),
                    suggestion: Some(String::from(second)),
                },
                DiagnosticCode::UnknownAttribute,
                &["name", "suggestion"],
                &[first, second],
            ),
            (
                DiagnosticMessage::UnknownAttribute {
                    name: String::from(first),
                    suggestion: None,
                },
                DiagnosticCode::UnknownAttribute,
                &["name", "suggestion"],
                &[first],
            ),
            (
                DiagnosticMessage::DuplicateAttribute {
                    name: String::from(first),
                },
                DiagnosticCode::DuplicateAttribute,
                &["name"],
                &[first],
            ),
            (
                DiagnosticMessage::MissingAttributePayload {
                    name: String::from(first),
                },
                DiagnosticCode::MissingAttributePayload,
                &["name"],
                &[first],
            ),
            (
                DiagnosticMessage::NonValueAttributePayload {
                    name: String::from(first),
                },
                DiagnosticCode::NonValueAttributePayload,
                &["name"],
                &[first],
            ),
            (
                DiagnosticMessage::ShadowedName {
                    path: String::from(first),
                },
                DiagnosticCode::ShadowedName,
                &["path"],
                &[first],
            ),
            (
                DiagnosticMessage::Other {
                    message: String::from(first),
                },
                DiagnosticCode::Other,
                &["message"],
                &[first],
            ),
            (
                DiagnosticMessage::ParseRepair {
                    class: String::from(first),
                },
                DiagnosticCode::ParseRepair,
                &["class"],
                &[first],
            ),
        ];
        for (message, expected_code, slots, arguments) in cases {
            assert_eq!(message.code(), expected_code);
            let template = message.template().to_string();
            let actual_slots = template
                .split('{')
                .skip(1)
                .map(|part| part.split_once('}').expect("a named slot closes").0);
            assert!(actual_slots.eq(slots.iter().copied()), "{expected_code}");
            let rendered = message.to_string();
            let mut remaining = rendered.as_str();
            for &argument in arguments {
                remaining = remaining
                    .split_once(argument)
                    .expect("arguments keep their order")
                    .1;
                assert_eq!(rendered.matches(argument).count(), 1);
            }
            for &slot in slots {
                assert!(
                    !rendered.split('{').skip(1).any(|suffix| {
                        suffix
                            .strip_prefix(slot)
                            .is_some_and(|rest| rest.starts_with('}'))
                    }),
                    "{expected_code} leaves no unfilled slot"
                );
            }
        }
    }
}
