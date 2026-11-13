//! The records and the parts of the lowering that read nothing of its
//! context.
//!
//! They are the exits and the runs the lowering infers, the reading of a
//! literal's own text, the spelling of reflexivity, the refusal of a `cells`
//! node, and a theory read as a capability's interface. The lowering's
//! families read them, and `gandr-surface-lowering` names each one at its old
//! path.

use alloc::string::String;

use anodized::spec;
use gandr_kernel_term::CharacterLiteral;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::form::Former;
use crate::written_import::decode_escapes;

pub mod capability;
pub mod cells;
pub mod exits;
pub mod runs;

pub use exits::ElidableExit;
pub use exits::Exit;
pub use exits::Explicitness;
pub use exits::InferredExit;
pub use exits::Returned;
pub use runs::AskedRuns;
pub use runs::InferredRun;
pub use runs::LinearRun;
pub use runs::NestedSite;
pub use runs::RunOperand;
pub use runs::RunSpelling;

/// Reflexivity's spelling, which no pattern may take.
pub const HERE: &str = "here";

quenchant_shape::reason_enum! {
    /// Why a lexeme denotes no literal.
    pub mod literal {
        /// The text is not a lexeme of the literal form asked about.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The text is not the form's lexeme.
            Malformed,
            /// The former is not a literal former at all.
            NotALiteral,
            /// A typed number's digits do not fit its integer width, or are
            /// no integer.
            OutsideWidth,
        }
    }
}

/// Parse a literal's own text into a core literal.
///
/// # Specification
/// - requires: `text` is the literal node's whole source text.
/// - ensures: a number is the canonical non-negative magnitude of its digits,
///   so a padded spelling and its unpadded form are one literal; a string is
///   the text between its delimiting quotes with its escapes decoded — `\n`,
///   `\t`, `\r`, `\0`, `\\`, `\"` and `\'` to the character each names, a
///   backslash before a line break elided with the break, any other escaped
///   character to itself, and a trailing lone backslash dropped; a character is
///   the one scalar its quotes hold once that same decoding runs.
/// - provides: the only place a lexeme becomes a core literal.
/// - fails: never; the malformed absence for a number holding a non-digit or
///   nothing at all, a string missing either delimiter, and a character whose
///   quotes are missing or decode to no scalar or to several, and the
///   not-a-literal absence for every other former.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two decision surfaces (the magnitude guard and the
///   delimiter strip) and the escape table, separated by a padded integer, an
///   empty integer, an integer holding a letter, a quoted text, an escaped
///   text, an unterminated text, a bare quote and an unquoted text, each
///   asserted as an exact literal or absence.
/// - witness: `gandr-surface-lowering::lower::tests::an_integer_literal_is_its_canonical_magnitude`
/// - witness: `gandr-surface-lowering::lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
/// - witness: `gandr-surface-lowering::lower::tests::a_lexeme_of_the_wrong_shape_parses_to_nothing`
#[spec(
    ensures: |ret| {
        let spelled: &str = text.as_ref();
        match former {
            | Former::Number => {
                if spelled.is_empty() || !spelled.bytes().all(|byte| byte.is_ascii_digit()) {
                    matches!(ret, Maybe::Absent(literal::Absent::Malformed))
                }
                else {
                    let unpadded = spelled.trim_start_matches('0');
                    let expected = if unpadded.is_empty() { "0" } else { unpadded };
                    matches!(ret, Maybe::Present(Literal::Integer(ref integer)) if integer.sign() == Sign::NonNegative && integer.magnitude().as_ref() == expected)
                }
            },
            | Former::Text => match spelled
                .strip_prefix('"')
                .and_then(|opened| opened.strip_suffix('"'))
            {
                | Some(content) => match ret {
                    | Maybe::Present(Literal::Text(ref literal)) => {
                        let content: &str = content;
                        let actual: &str = literal.as_ref();
                        let mut escaped = false;
                        let mut after_cr = false;
                        actual.chars().eq(content.chars().filter_map(|character| {
                            if after_cr {
                                after_cr = false;
                                if character == '\n' {
                                    return None;
                                }
                            }
                            if escaped {
                                escaped = false;
                                match character {
                                    | 'n' => Some('\n'),
                                    | 't' => Some('\t'),
                                    | 'r' => Some('\r'),
                                    | '0' => Some('\0'),
                                    | '\r' => {
                                        after_cr = true;
                                        None
                                    },
                                    | '\n' => None,
                                    | other => Some(other),
                                }
                            }
                            else if character == '\\' {
                                escaped = true;
                                None
                            }
                            else {
                                Some(character)
                            }
                        }))
                    },
                    | _ => false,
                },
                | None => matches!(ret, Maybe::Absent(literal::Absent::Malformed)),
            },
            | Former::Character => match spelled
                .strip_prefix('\'')
                .and_then(|opened| opened.strip_suffix('\''))
                .map(|content| decode_escapes(SourceFragment::from(content)))
            {
                | Some(decoded) if decoded.chars().count() == 1 => {
                    matches!(ret, Maybe::Present(Literal::Character(character)) if decoded.chars().eq(core::iter::once(char::from(character))))
                },
                | _ => matches!(ret, Maybe::Absent(literal::Absent::Malformed)),
            },
            | _ => matches!(ret, Maybe::Absent(literal::Absent::NotALiteral)),
        }
    },
)]
#[inline]
pub fn parse_literal(
    former: Former,
    text: SourceFragment<'_>,
) -> Maybe<Literal, literal::Absent>
{
    let spelled: &str = text.as_ref();
    let found = match former {
        Former::Number => Magnitude::from_decimal_text(String::from(spelled))
            .map(|magnitude| Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))),
        Former::Text => spelled
            .strip_prefix('"')
            .and_then(|opened| opened.strip_suffix('"'))
            .map(|content| {
                Literal::Text(StringLiteral::new(decode_escapes(SourceFragment::from(
                    content,
                ))))
            }),
        Former::Character => spelled
            .strip_prefix('\'')
            .and_then(|opened| opened.strip_suffix('\''))
            .and_then(|content| {
                CharacterLiteral::try_from(decode_escapes(SourceFragment::from(content))).ok()
            })
            .map(Literal::Character),
        Former::Name
        | Former::Hole
        | Former::Binary
        | Former::Unary
        | Former::Constructor
        | Former::Parenthesized
        | Former::TypeQuote
        | Former::Boolean
        | Former::Thunk
        | Former::Lambda
        | Former::Block
        | Former::Return
        | Former::Exit
        | Former::Become
        | Former::Loop
        | Former::While
        | Former::For
        | Former::Break
        | Former::Continue
        | Former::Force
        | Former::Run
        | Former::Call
        | Former::ForgetModel
        | Former::Case
        | Former::If
        | Former::Telescope
        | Former::List
        | Former::PackModel
        | Former::Injection
        | Former::LazyRecord
        | Former::Instantiation
        | Former::Projection
        | Former::TypeHead
        | Former::TypePath
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::LinearArrowType
        | Former::ProductType
        | Former::SumType
        | Former::LazyProductType
        | Former::TelescopeType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ParenthesizedType
        | Former::PathType
        | Former::BridgeType
        | Former::FlowType
        | Former::RelationType
        | Former::ManifestType
        | Former::CapabilityType
        | Former::AtType
        | Former::StagedType
        | Former::ModedType
        | Former::Scope
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Visibility
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Mutual
        | Former::SessionType
        | Former::Action
        | Former::Offer
        | Former::Access
        | Former::World
        | Former::WorldDeclaration
        | Former::Reserved(_)
        | Former::Unadmitted(_)
        | Former::Misplaced => return Maybe::Absent(literal::Absent::NotALiteral),
    };

    found.map_or(Maybe::Absent(literal::Absent::Malformed), Maybe::Present)
}
