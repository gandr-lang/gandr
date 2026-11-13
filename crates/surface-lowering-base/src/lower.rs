//! The records of the lowering and the parts of it that read nothing of its
//! context.
//!
//! The module pass reads the exits and the runs the lowering infers, the
//! reading of a literal's own text, and the spelling of reflexivity. The
//! context holds the readings, the plans and the records that its families
//! write and read: one module here for each family that defines such a type.
//! The refusal of a `cells` node and a theory read as a capability's interface
//! read nothing of the context. The families read these items, and
//! `gandr-surface-lowering` names each one at its old path.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::identity::Relation;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::SessionAction;
use gandr_core_term::world::World;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CharacterLiteral;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::by_form::ByForm;
use crate::by_form::FormStretch;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Family;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Placed;
use crate::form::Run;
use crate::form::TileName;
use crate::form::Universe;
use crate::form::declined_feature;
use crate::lower::native::record_copied_since;
use crate::lower::native::rooted;
use crate::module::FamilyIndex;
use crate::module::InstanceIndex;
use crate::module::SlotIndex;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::origin::OriginTable;
use crate::resolve::Bound;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::ScopeId;
use crate::resolve::Telescope;
use crate::resolve::TypeAtom;
use crate::resolve::TypeFormer;
use crate::resolve::atom_type;
use crate::resolve::binder_type;
use crate::unbuilt::Unbuilt;
use crate::unit::SourceIndex;
use crate::written_import::decode_escapes;

pub mod access;
pub mod arity;
pub mod capability;
pub mod cells;
pub mod conditional;
pub mod context;
pub mod exits;
pub mod families;
pub mod generic;
pub mod identity;
pub mod implicit;
pub mod loops;
pub mod method;
pub mod model;
pub mod native;
pub mod natural;
pub mod opening;
pub mod runs;
pub mod session;
pub mod world;

pub use context::Context;
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

quenchant_shape::reason_enum! {
    /// Why a node has no lowered core node.
    pub mod lowered {
        /// The mint sweep produced nothing usable for the node.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node was not minted: unread, refused, or under a refusal.
            Unminted,
            /// The node was minted at another sort than the one asked for.
            OtherSort,
            /// The function tail states no type: a parameter or the result is
            /// untyped.
            Unstated,
            /// The slot belongs to a functor's template, which each
            /// application renames into declarations of its own.
            Templated,
            /// The constructor around a field reads as no application of a
            /// family, so the field gives the constructor written in it no
            /// type.
            Unclassified,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node sees no manifest type component.
    pub mod scoped {
        /// The node lies in no module signature.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No signature type encloses the node.
            Unscoped,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a name resolves to nothing.
    pub mod named {
        /// Neither scope carries the name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No enclosing binder and no earlier declaration is named so.
            Unresolved,
        }
    }
}

/// How a node's position reads it.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A reading retains its positional sort and, for framed readings,
///   the binder frame used by its children.
/// - provides: The context for classification and insertion decisions.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The tag retains neither its source position nor its
///   scope; sort, family, frame and require specify its projections and
///   interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — lambda binding, forced heads and returner insertion
///   distinguish the framed term and type positions on the listed sources.
/// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `gandr-surface-lowering::lower::tests::a_positive_result_gains_a_returner_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Reading
{
    /// Not read: an own tile, layout, or a node under a form that refused.
    Unread,
    /// Read as a value type, under the binder frame named here.
    ValueType(Frame),
    /// Read as a computation type, under the binder frame named here.
    CompType(Frame),
    /// Read as a value, under the binder frame named here.
    Value(Frame),
    /// Read as a computation, under the binder frame named here.
    Computation(Frame),
    /// Read as an application's head: a computation under the binder frame
    /// named here, which a value standing here reaches by an inserted force.
    Head(Frame),
    /// Read as a function's result: a computation type under the binder frame
    /// named here, which a value type standing here reaches by an inserted
    /// returner.
    Result(Frame),
    /// Read as a function: the declaration form whose tail is one.
    Function,
}

impl Reading
{
    /// The sort a refusal at this position reports.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: unread and function positions report declarations, type
    ///   positions their own type sort, and heads/results the computation sort
    ///   they demand.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — wrong-sort refusals distinguish the expected value,
    ///   computation and type positions; function sites report a declaration.
    /// - witness: `gandr-surface-lowering::lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
    /// - witness: `gandr-surface-lowering::lower::tests::a_computation_codomain_of_a_box_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::forms_outside_the_fragment_are_unadmitted`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (Self::Unread | Self::Function, FragmentSort::Declaration)
                    | (Self::ValueType(_), FragmentSort::ValueType)
                    | (Self::CompType(_) | Self::Result(_), FragmentSort::CompType)
                    | (Self::Value(_), FragmentSort::Value)
                    | (
                        Self::Computation(_) | Self::Head(_),
                        FragmentSort::Computation
                    )
            )
        },
    )]
    #[inline]
    #[must_use]
    pub const fn sort(self) -> FragmentSort
    {
        match self {
            Self::Unread | Self::Function => FragmentSort::Declaration,
            Self::ValueType(_frame) => FragmentSort::ValueType,
            Self::CompType(_frame) | Self::Result(_frame) => FragmentSort::CompType,
            Self::Value(_frame) => FragmentSort::Value,
            Self::Computation(_frame) | Self::Head(_frame) => FragmentSort::Computation,
        }
    }

    /// The family of formers this reading admits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: type and result readings admit the type family, term and head
    ///   readings the term family, and unread/function readings neither.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — term and type fixtures exercise their reading
    ///   families; a type in value position is quoted rather than rejected as a
    ///   wrong family.
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_lambda_binds_its_name_over_a_quoted_body`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (Self::Unread | Self::Function, Family::Neither)
                    | (
                        Self::ValueType(_) | Self::CompType(_) | Self::Result(_),
                        Family::Type
                    )
                    | (
                        Self::Value(_) | Self::Computation(_) | Self::Head(_),
                        Family::Term
                    )
            )
        },
    )]
    #[inline]
    #[must_use]
    pub const fn family(self) -> Family
    {
        match self {
            Self::Unread | Self::Function => Family::Neither,
            Self::ValueType(_frame) | Self::CompType(_frame) | Self::Result(_frame) => Family::Type,
            Self::Value(_frame) | Self::Computation(_frame) | Self::Head(_frame) => Family::Term,
        }
    }

    /// The binder frame this reading is under, the outermost for a reading
    /// that names none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: framed readings retain their frame, while unread and function
    ///   readings use the outermost frame.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda body resolves its binder at the exact index;
    ///   a reading without a binder is interpreted in the outermost scope.
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (
                    Self::Unread
                        | Self::Function
                        | Self::ValueType(Frame::Outermost)
                        | Self::CompType(Frame::Outermost)
                        | Self::Value(Frame::Outermost)
                        | Self::Computation(Frame::Outermost)
                        | Self::Head(Frame::Outermost)
                        | Self::Result(Frame::Outermost),
                    Frame::Outermost
                ) | (
                    Self::ValueType(Frame::Inner(_))
                        | Self::CompType(Frame::Inner(_))
                        | Self::Value(Frame::Inner(_))
                        | Self::Computation(Frame::Inner(_))
                        | Self::Head(Frame::Inner(_))
                        | Self::Result(Frame::Inner(_)),
                    Frame::Inner(_)
                )
            )
        },
    )]
    #[inline]
    #[must_use]
    pub const fn frame(self) -> Frame
    {
        match self {
            Self::Unread | Self::Function => Frame::Outermost,
            Self::ValueType(frame)
            | Self::CompType(frame)
            | Self::Value(frame)
            | Self::Computation(frame)
            | Self::Head(frame)
            | Self::Result(frame) => frame,
        }
    }

    /// The universe a decode stands at when nothing was written to say, at
    /// the fuss-free level: the computation types where only a computation
    /// type is read, the value types everywhere else — a function's result
    /// included, which takes a value type under an inserted returner.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: only a computation-type reading defaults to the computation
    ///   universe; every other reading defaults to the value universe, all at
    ///   level zero.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — static application decodes at the written universe or
    ///   at the sort demanded by its position when no universe is written.
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| {
            matches!(ret.level, LevelConstant::ZERO)
                && matches!(
                    (self, ret.sort),
                    (Self::CompType(_), GroundSort::Computation)
                        | (
                            Self::Unread
                                | Self::Function
                                | Self::ValueType(_)
                                | Self::Value(_)
                                | Self::Computation(_)
                                | Self::Head(_)
                                | Self::Result(_),
                            GroundSort::Value
                        )
                )
        },
    )]
    #[inline]
    #[must_use]
    pub const fn positional_universe(self) -> Universe
    {
        match self {
            Self::CompType(_) => Universe {
                sort: GroundSort::Computation,
                level: LevelConstant::ZERO,
            },
            Self::Unread
            | Self::Function
            | Self::ValueType(_)
            | Self::Value(_)
            | Self::Computation(_)
            | Self::Head(_)
            | Self::Result(_) => Universe::FUSS_FREE,
        }
    }
}

/// What the mint sweep writes over a node's own core node.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A bare result is unchanged; an insertion request is interpreted
///   against the lowered child family.
/// - provides: The conversion to apply after the node’s own plan is minted.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The child is not retained on the tag; require selects
///   requests and `Sink::bridge` checks the result family and provenance.
///
/// # Adequacy
/// - hypothesis: L3 — forcing, returner insertion and quotation record the
///   inserted node while preserving the authored child’s origin.
/// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `gandr-surface-lowering::lower::tests::a_positive_result_gains_a_returner_once`
/// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Bridge
{
    /// Nothing: the node's sort is the sort its position reads.
    Bare,
    /// The bridge from the node's sort to the one its position reads.
    Inserted(Insertion),
    /// A call or a selection at an application's head, nested and then forced:
    /// the checker runs it when it returns a function, and suspends it
    /// otherwise (#3935, #4818).
    HeadCall,
}

quenchant_shape::reason_enum! {
    /// Why a function's parameter or result carries no type.
    pub mod stated {
        /// The function tail leaves the type to a signature written apart.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source wrote no `: T` after the binder, or no `-> T` after
            /// the parameter list.
            Unstated,
            /// The parameter is an instance a label of the result's row binds:
            /// its type is the capability of the label's interface at the
            /// label's own region (`Lowerer::instance_parameters`).
            Instance,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a function tail closes no fixpoint.
    pub mod recursion {
        /// The function names nothing recursively.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration was not written `def rec`.
            Plain,
        }
    }
}

/// One segment of an interpolated string, in written order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TextSegment
{
    /// A run of text between the quotes and the interpolations, its escapes
    /// decoded.
    Text(StringLiteral),
    /// The expression an interpolation `${ e }` holds, read as a value.
    Operand(NodeIndex),
}

/// What a block statement does with the value its computation returns, or
/// the fork, the receive or the hold it is.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StatementBinding
{
    /// `let x = c ;` names the value for the rest of the block; the node is
    /// the name's own.
    Named(NodeIndex),
    /// `let b = c.alloc(n) ;` names, under `b`'s linear binder, the buffer
    /// an exercise replies, placed live over the rest of the block; the
    /// reply's own binder is one no name reaches. The node is the name's own.
    Placed(NodeIndex),
    /// `let x = v ;` with `v` a value: `v` returned once and bound to `x`'s
    /// binder, which the checker reads as `v` itself. The node is the name's
    /// own.
    Let(NodeIndex),
    /// `let x : A = v ;`: as [`Self::Let`], `v` ascribed `A`.
    TypedLet
    {
        /// The name's own node.
        name: NodeIndex,
        /// The stated type's node.
        annotation: NodeIndex,
    },
    /// `c ;` discards it, splitting it as the unit under a binder no name
    /// reaches.
    Discarded,
    /// `let (x, y, …) = c ;` splits the tuple it returns, under a binder no
    /// name reaches, into one named binder per component.
    Split
    {
        /// The tuple's arity.
        arity: gandr_core_term::ComponentCount,
        /// The tuple pattern's own node.
        pattern: NodeIndex,
    },
    /// `let (q, r, …) = f(a) ;` binds each output of a call whose result is a
    /// group, one named binder per output, the first outermost, with no
    /// product built.
    Outputs
    {
        /// How many outputs the call returns.
        arity: gandr_core_term::ComponentCount,
        /// The pattern's own node.
        pattern: NodeIndex,
    },
    /// `let x : A = c ;` ascribes `c` the returner `-F A`, pure as the
    /// annotation writes no row, and names the value it returns for the rest
    /// of the block, so a computation that returns no `A` refuses.
    Typed
    {
        /// The name's own node.
        name: NodeIndex,
        /// The value type `A` written, read in the statement's own frame.
        annotation: NodeIndex,
    },
    /// `module m = p ;` ascribes `return p` the returner of the model type
    /// `p` is declared at, as [`Self::Typed`] does, so the checker binds `m`
    /// as a variable of that type rather than reading it as `p`.
    Opening
    {
        /// The name's own node.
        name: NodeIndex,
        /// The model type `p` is declared at, read in its own frame.
        stated: NodeIndex,
        /// The frame the statement stands in, which the type is carried to.
        frame: Frame,
    },
    /// `let (x, y, …) : A = c ;` ascribes `c` the returner `-F A`, as
    /// [`Self::Typed`] does, and splits the tuple it returns, as
    /// [`Self::Split`] does.
    TypedSplit
    {
        /// The tuple's arity.
        arity: gandr_core_term::ComponentCount,
        /// The tuple pattern's own node.
        pattern: NodeIndex,
        /// The value type `A` written, read in the statement's own frame.
        annotation: NodeIndex,
    },
    /// `let d = fork (c : S) t;` runs `t`, under `c`'s linear binder, beside
    /// the rest of the block, under `d`'s: the fork's protocol `S`, its
    /// child `t`, and `c`, the channel's name.
    Forked
    {
        /// The protocol type `S` written for the child's end.
        protocol: NodeIndex,
        /// The child computation.
        child: NodeIndex,
        /// The name `c` the child's end binds.
        end: NodeIndex,
    },
    /// `let x = recv c;` receives on `c` into `x`'s linear binder, over the
    /// rest of the block.
    Received
    {
        /// The endpoint `c`, read where the statement stands.
        endpoint: DeBruijnIndex,
        /// The bytes `c` is written at.
        subject: ByteSpan,
        /// The name's own node.
        name: NodeIndex,
    },
    /// `var x = e ;` holds the value `e`, under `x`'s linear binder, over the
    /// rest of the block, at the grade `var[g]` writes, ascribed the type
    /// `var x : T = e ;` states.
    Held
    {
        /// The value held.
        value: NodeIndex,
        /// The grade it is held at.
        grade: gandr_core_term::memory::HoldGrade,
        /// The name's own node.
        name: NodeIndex,
        /// The value type `T` written, read in the statement's own frame.
        stated: Maybe<NodeIndex, access::unstated::Absent>,
    },
    /// `var x : A at w = e ;` binds `x` to the handle the world `w` holds
    /// `e` at, as `var x : A at w = e ;` does; the bound node is `e`.
    Located
    {
        /// The handle type `A at w` written, read in the statement's own
        /// frame.
        annotation: NodeIndex,
        /// The name's own node.
        name: NodeIndex,
    },
    /// `let x at w = v ;` opens the handle `v`, binding `x`, an intuitionistic
    /// hypothesis located at `w`, over the rest of the block.
    Opened
    {
        /// The handle opened.
        value: NodeIndex,
        /// The name's own node.
        name: NodeIndex,
        /// The world the source writes.
        world: World,
    },
}

/// One `let x = c ;` or `c ;` statement of a block.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The origin position supplies the bind’s origin while the bound
///   position supplies its computation; the rest says whether the block after
///   the statement is bound once or continues every local end of the
///   computation.
/// - provides: One source-ordered block binding.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Neither the source tree nor the lowered-node table is
///   retained; statement and `mint_block` check the coordinate roles.
///
/// # Adequacy
/// - hypothesis: L3 — consecutive run bindings scope over the following
///   computation and preserve their own source origins.
/// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `gandr-surface-lowering::lower::tests::a_discarded_statement_splits_its_unit`
/// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Statement
{
    /// The origin of the bind: the `let` tile, or a discarded statement's
    /// computation.
    pub origin: NodeIndex,
    /// The computation whose returned value the statement binds.
    pub bound: NodeIndex,
    /// Whether the rest of the block names the value or discards it.
    pub binding: StatementBinding,
    /// Where the rest of the block goes.
    pub rest: exits::Rest,
}

/// A block: its statements, in source order, and its last computation.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The statement range precedes one final computation, which is not
///   replaced by an empty block result.
/// - provides: A block plan over the shared statement store.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The statement store and child results are absent; block
///   and `mint_block` check the range, final computation and bind order.
///
/// # Adequacy
/// - hypothesis: L3 — chained binds preserve order; a block without its final
///   computation is refused at the arity boundary.
/// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `gandr-surface-lowering::lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Block
{
    /// The block's statements, in the lowerer's statement store.
    pub statements: FormStretch,
    /// The computation the block ends with.
    pub last: NodeIndex,
}

/// One parameter of a function tail.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The binder’s origin, introduced frame and optional written type
///   remain separate coordinates.
/// - provides: The data a function’s lambda and signature spines are built
///   from.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The source, scope and lowered types are not retained;
///   function, `mint_function` and `mint_signature` interpret those
///   coordinates.
///
/// # Adequacy
/// - hypothesis: L3 — a typed parameter contributes to both spines, while an
///   unstated type does not prevent the function body from lowering.
/// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `gandr-surface-lowering::lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Parameter
{
    /// The binder tile, the origin of the parameter's lambda and arrow.
    pub binder: NodeIndex,
    /// The frame the parameter binds, which says whether a type names it.
    pub frame: ScopeId,
    /// The parameter's type, when the source wrote one: a flattened model
    /// implicit's model type.
    pub declared: Maybe<NodeIndex, stated::Absent>,
    /// The place of the component the parameter binds among its model
    /// implicit's, when it is one of a flattened model implicit's parameters
    /// ([`model::Flattened`]).
    pub component: Option<model::ComponentPlace>,
    /// Whether the tail's own parameter list writes the parameter.
    pub listed: Listed,
}
impl Parameter
{
    /// A parameter the tail's own list writes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn own(
        binder: NodeIndex,
        frame: ScopeId,
        declared: Maybe<NodeIndex, stated::Absent>,
    ) -> Self
    {
        Self {
            binder,
            frame,
            declared,
            component: None,
            listed: Listed::Own,
        }
    }

    /// A parameter bound outside the tail's own list.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn elsewhere(
        binder: NodeIndex,
        frame: ScopeId,
        declared: Maybe<NodeIndex, stated::Absent>,
    ) -> Self
    {
        Self {
            binder,
            frame,
            declared,
            component: None,
            listed: Listed::Elsewhere,
        }
    }

    /// A component of a flattened model implicit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn component(
        binder: NodeIndex,
        frame: ScopeId,
        declared: NodeIndex,
        component: model::ComponentPlace,
    ) -> Self
    {
        Self {
            binder,
            frame,
            declared: Maybe::Present(declared),
            component: Some(component),
            listed: Listed::Elsewhere,
        }
    }

    /// `domain`, the type `parameter` states, read past the binders of the
    /// names before it that share its written type: `y` in `x y : a` reads `a`
    /// past `x` when a later type names `x`.
    ///
    /// # Specification
    /// - requires: `domain` is minted from `parameter`'s written type, under
    ///   the frame of the first name that shares it; `earlier` holds the
    ///   parameters before `parameter`, in written order; `binds` answers
    ///   whether a parameter's arrow is a Π, as the caller mints it.
    /// - ensures: `domain` itself when no name just before `parameter` that
    ///   shares its written type binds; otherwise `domain` with every free
    ///   index raised by the names that bind, each copy recorded as
    ///   `NativeRef::lift_value_type` records its own.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two names that share a type a later type names
    ///   declare what the names written apart declare, in a def head and in a
    ///   box's group.
    /// - witness: `gandr-surface-lowering::lower::tests::a_def_head_s_shared_names_are_its_parameters_written_apart_4853`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::names_that_share_a_type_are_their_entries_written_apart_4853`
    #[spec(ensures: |ret| sink.arena.value_type(ret).is_some() || ret == domain)]
    #[inline]
    #[expect(
        clippy::use_self,
        reason = "the body keeps the tokens it had in the native family, which named the type"
    )]
    #[expect(
        clippy::impl_trait_in_params,
        reason = "the model family's crate and the lowering call it, and the lowering names no type for the closure"
    )]
    pub fn shared_domain(
        earlier: &[Parameter],
        parameter: &Parameter,
        binds: impl Fn(&Parameter) -> bool,
        domain: ValueTypeId,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        let binding = earlier
            .iter()
            .rev()
            .take_while(|named| named.declared == parameter.declared)
            .filter(|&named| binds(named))
            .count();
        let lift = Binders::from(u32::try_from(binding).unwrap_or(u32::MAX));
        if lift == Binders::NONE {
            return domain;
        }
        let mark = sink.arena.watermark();
        let mut copies = Vec::new();
        let lifted = gandr_core_term::shift_value_type(sink.arena, domain, lift)
            .settle_traced(sink.arena, &mut copies);
        record_copied_since(
            sink,
            mark,
            origin,
            Maybe::Absent(rooted::Absent::Classifier),
            &copies,
        );

        lifted
    }
}

/// Where a function's parameter is written.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: [`Self::Own`] for a parameter the tail's own list writes, bound
///   in written or in merged order; [`Self::Elsewhere`] for one an implicit
///   group, a row label, a model's components, a telescope or a clause's
///   columns bind.
/// - executable: none — the record holds no tree.
///
/// # Adequacy
/// - hypothesis: L3 — a linear tail with an implicit group takes its written
///   parameters linearly and its implicit one intuitionistically.
/// - witness: `gandr-surface-lowering::lower::tests::a_linear_tail_takes_each_written_parameter_once_5853`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Listed
{
    /// The tail's own parameter list writes the parameter.
    Own,
    /// Something other than the tail's own list binds the parameter.
    Elsewhere,
}

/// A label the source writes against an entry, kept while the lowering plans
/// so the label can answer what its entry lowers to.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the label's bytes, the node of the entry it names, and how that
///   entry is read.
/// - executable: none — the record holds neither the tree nor the scope its
///   coordinates are read in.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::labelled`.
/// - witness: `gandr-surface-lowering::lower::arity::tests::each_label_names_what_it_labels`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LabelSite
{
    /// The label's bytes.
    pub written: ByteSpan,
    /// The entry the label names.
    pub held: NodeIndex,
    /// How the entry is read.
    pub read: LabelRead,
}

/// How the entry a label names is read.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LabelRead
{
    /// As a value type under the frame: the label answers at that type.
    ValueType(Frame),
    /// As a computation type under the frame.
    CompType(Frame),
    /// As a term: the label answers at the term's type.
    Term,
}

/// What a path-shaped type's carrier is written as.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Carrier
{
    /// A type, the node written at the carrier's place or supplied by name.
    Written(NodeIndex),
    /// A universe spelled by the form's own tiles, `Path[.A = Type](A, B)`: the
    /// endpoints are written as types.
    Universe(Universe),
    /// No carrier written, `Flow(a, b)`: the decoding of a hole the form
    /// nominates, which the endpoints fix where the type forms.
    Omitted(gandr_core_term::hole::HoleId),
}

/// The former a path-shaped type relates its endpoints by.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Relating
{
    /// `Path[.A = A](a, b)`, element identity.
    Path,
    /// `Bridge[.A = A](a, b)`, relatedness: no reflexivity, transport or J.
    Bridge,
}

impl Relating
{
    /// The head tile the form is written under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn head(self) -> TileName
    {
        match self {
            Self::Path => TileName::PATH,
            Self::Bridge => TileName::BRIDGE,
        }
    }
}

/// The code a decode reads its type from, and the head a static application
/// applies.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A bound code retains the use frame and binder identity until
///   telescope indexing; a constant retains its admission coordinate.
/// - provides: The common head of static applications and decoded types.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The scope and declaration store needed for resolution
///   are absent; `resolve_name`, `static_application` and `mint_code` check
///   their uses.
///
/// # Adequacy
/// - hypothesis: L3 — bound and declared codes decode at their written universe
///   and static applications retain source argument order.
/// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
/// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Code
{
    /// A binder, named from a use site under the frame `from`, whose index is
    /// counted in `telescope` once every type has been read: the signature's,
    /// or a body quote's (#547).
    Bound
    {
        /// The use site's frame.
        from: Frame,
        /// The binder's frame.
        binder: ScopeId,
        /// The telescope the index is counted in.
        telescope: Telescope,
    },
    /// A declaration at this admission position.
    Constant(ConstantIndex),
}

quenchant_shape::reason_enum! {
    /// Why a static lambda's position states no classifier.
    pub mod classified {
        /// The position fixes the static sort and states no arrow.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A transport's or a ride's motive, whose binder ranges over
            /// the path's points.
            Motive,
        }
    }
}

/// A function tail's reading: `(params) -> T? { … }`.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The parameter range, optional result and block are retained
///   separately so an incomplete signature does not discard the body; a
///   recursive tail retains the frame binding its own name.
/// - provides: The two spines of a function tail.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The parameter store and lowered children are not
///   retained; function, `mint_function` and `mint_signature` check the stored
///   ranges and outcomes.
///
/// # Adequacy
/// - hypothesis: L3 — zero and multiple parameters preserve the body and
///   signature distinction, including tails with an unstated type.
/// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `gandr-surface-lowering::lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
/// - witness: `gandr-surface-lowering::lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Function
{
    /// The parameters, in the lowerer's parameter store.
    pub parameters: FormStretch,
    /// The result type, when the source wrote one.
    pub result: Maybe<NodeIndex, stated::Absent>,
    /// The body.
    pub body: Body,
    /// The frame binding the function's own name, between the staged
    /// parameter and the ones before it, when the tail recurses.
    pub recursion: Maybe<ScopeId, recursion::Absent>,
    /// The receiver a written-through method holds over its body.
    pub receiver: Maybe<method::HeldReceiver, method::unheld::Absent>,
    /// The parameters at a session type its body places, in the lowerer's
    /// endpoint store.
    pub endpoints: FormStretch,
    /// How the tail takes its written parameters: the arrow its result
    /// follows.
    pub taking: Taking,
}

/// How a function tail takes its written parameters, read off the arrow
/// before its result.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a linear tail takes linearly each parameter its own list writes,
///   in any order a merged telescope binds them; every other parameter stays
///   intuitionistic.
/// - executable: none — the parameter store is not retained.
///
/// # Adequacy
/// - hypothesis: L3 — a tail at `⊸` mints the linear lambda and the linear
///   arrow for each written parameter, and one at `->` the lambda and the
///   arrow; an implicit group stays intuitionistic.
/// - witness: `gandr-surface-lowering::lower::tests::a_linear_tail_takes_each_written_parameter_once_5853`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Taking
{
    /// `->`: each parameter is intuitionistic.
    Unrestricted,
    /// `⊸`: each parameter the tail's own list writes is linear, at the
    /// multiplicity one.
    Linear,
}

impl Taking
{
    /// The taking of `parameter`: linear when the tail takes its own list
    /// linearly and that list writes `parameter`, unrestricted otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(
        self,
        parameter: &Parameter,
    ) -> Self
    {
        if self == Self::Linear && parameter.listed == Listed::Own {
            Self::Linear
        }
        else {
            Self::Unrestricted
        }
    }
}

/// A function tail's body: a block, or the decision tree its clauses compile
/// to.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: a clause body's tree stands directly under the lambdas of the
///   parameters its columns bind, each column one tree binder.
/// - provides: what `Lowerer::mint_function` mints under the lambda chain.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the statement and case stores are not retained;
///   `function` and `mint_function` interpret the coordinates.
///
/// # Adequacy
/// - hypothesis: L3 — a block body and a clause body each lower under the same
///   lambda chain.
/// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `gandr-surface-lowering::lower::native::tests::clauses_match_one_column_per_arrow`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Body
{
    /// A block, `{ s… c }`.
    Block(Block),
    /// Clauses, `where { | p, … => c … }`, compiled to one match.
    Clauses(native::CaseIndex),
}

/// What the mint sweep does for one node, decided by the classification.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The selected former retains the child coordinates and flat-store
///   ranges needed by the later mint sweep; transparent plans adopt their
///   child.
/// - provides: The classification-to-minting boundary without recursive source
///   re-reading.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The source, stores and child results are absent; the
///   readers specify each plan and `mint_plan` checks its output family and
///   transparent case.
///
/// # Adequacy
/// - hypothesis: L3 — the admitted term and type formers retain their concrete
///   core structure, while grouping adds no constructor.
/// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `gandr-surface-lowering::lower::tests::a_grouping_lowers_to_what_it_wraps`
/// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
/// - witness: `gandr-surface-lowering::lower::tests::a_static_lambda_binds_its_name_over_a_quoted_body`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Plan
{
    /// Mint nothing.
    Unplanned,
    /// A value hole at its source occurrence.
    ValueHole(gandr_core_term::hole::HoleId),
    /// A computation hole at its source occurrence.
    CompHole(gandr_core_term::hole::HoleId),
    /// A variable at this index, bound by the binder that entered this frame.
    Variable(DeBruijnIndex, ScopeId),
    /// A constant at this admission position.
    Constant(ConstantIndex),
    /// A table-typed native prelude thunk.
    Primitive(gandr_core_term::primitive::Primitive),
    /// A saturated table operation selected by source operator syntax.
    PrimitiveCall(
        gandr_core_term::primitive::Primitive,
        gandr_core_term::primitive::Arguments<NodeIndex>,
    ),
    /// An interpolated string: the segments in the lowerer's segment store,
    /// each appended after the ones before it by the prelude's
    /// `string.append`.
    Interpolated(gandr_core_term::primitive::Primitive, FormStretch),
    /// A boolean literal: the unit injected into the side of `Bool` it names,
    /// `true` the left.
    Boolean(gandr_kernel_term::Side),
    /// A literal, already parsed from the node's own text.
    Literal(Literal),
    /// A numeral annotated `(n : Nat)`, the prelude's: the binary natural
    /// its magnitude is, over the prelude's constructors.
    Natural(natural::Naturals, Magnitude),
    /// A nullary type atom.
    Atom(TypeAtom),
    /// The atom the abstract type at this admission position declares.
    Sealed(ConstantIndex),
    /// The manifest type an application's instance exports: the type the
    /// functor's body wrote at the node, renamed by the application.
    Instantiated(InstanceIndex, NodeIndex),
    /// A universe.
    Universe(Universe),
    /// The type a code denotes, in the universe it was declared at: the code
    /// is the head applied statically to the arguments in the lowerer's
    /// operand store, none for a bare name.
    Decode(Code, FormStretch, Universe),
    /// The type the code a dynamic function returns denotes: the function the
    /// code names — a declaration at its admission position, or a binder
    /// holding a thunk — called on the arguments in the lowerer's operand
    /// store, its returned code decoded in the universe the position reads.
    Unquote(Code, FormStretch, Universe),
    /// The type the code a dynamic function's result returns denotes, `f(a)(b)`
    /// where a type is read: the function the code names called on the first
    /// stretch of the lowerer's operand store, the value that call returns
    /// forced and applied to the second stretch, its returned code decoded in
    /// the universe the position reads (#5213).
    Reapplied(Code, FormStretch, FormStretch, Universe),
    /// The carrier the model a binder holds gives one of its theory's
    /// unindexed sorts, `a.C`: the binder's bundled record projected at the
    /// sort's field — at its label off a record, along the nesting otherwise —
    /// the projection's returned code decoded in the fuss-free universe.
    Carrier(Code, arity::Observed, Option<FieldLabel>),
    /// The type the model type a binder is held at fixes one of its theory's
    /// sorts to, `a.C` for `a : Model(T) with sort C = A`: the type `A`, at the
    /// node it is written at, raised past the binders between that type and
    /// the reading.
    FixedCarrier(Code, NodeIndex),
    /// The call of a dynamic function the code names on the arguments in the
    /// lowerer's operand store, left to right: a type-position call's argument
    /// written as a call, which a value position nests.
    Called(Code, FormStretch),
    /// The force of the dynamic function the code names, called with no
    /// argument where a type reads a value: the expression grammar's `f()`,
    /// which a value position nests (#6787).
    Forced(Code),
    /// A static application of the head to the arguments in the lowerer's
    /// operand store, left to right.
    StaticApplication(Code, FormStretch),
    /// A static lambda over its body.
    StaticLambda(NodeIndex),
    /// A type former over its argument.
    Former(TypeFormer, NodeIndex),
    /// An arrow over its domain and codomain.
    Arrow(NodeIndex, NodeIndex),
    /// A static Pi over its domain and codomain.
    StaticPi(NodeIndex, NodeIndex),
    /// One eager product of the value types in the lowerer's operand store,
    /// in order: an unparenthesized `*` chain is one former, and the
    /// positional telescope type `#{A, …}` another, of any arity.
    Product(FormStretch),
    /// The type over labels `#{ l : A, … }`: its fields by label, the binders
    /// of every entry but the last in the lowerer's parameter store, each
    /// over the entries after it, the last entry's type and where its label
    /// is written. The record type of its fields when no later entry names an
    /// earlier label, the dependent pairs nested to the right otherwise.
    RecordType(
        BTreeMap<FieldLabel, NodeIndex>,
        FormStretch,
        NodeIndex,
        Option<NodeIndex>,
    ),
    /// The sum of the value types in the lowerer's operand store, in order,
    /// and the labels its entries are written at, none for a positional sum.
    Sum(FormStretch, FormStretch),
    /// The lazy record of the computation types in the lowerer's operand
    /// store, in order: one lazy product of them all. The labels its entries
    /// are written at follow, none for a positional lazy record.
    With(FormStretch, FormStretch),
    /// A case of no arms over a scrutinee stated at no data type and no path
    /// type: the eliminator of the empty sum.
    EmptyCase(NodeIndex),
    /// One tuple of the values in the lowerer's operand store, in order.
    Tuple(FormStretch),
    /// The native list of the values in the lowerer's operand store, in
    /// order: their cons cells ending in the empty list.
    List(FormStretch),
    /// The record of the values its labels name: `#{ .l = v, … }`.
    Record(BTreeMap<FieldLabel, NodeIndex>),
    /// The update of its base by the record of the values its labels name:
    /// `#{ b | l = v, … }`.
    RecordUpdate(NodeIndex, BTreeMap<FieldLabel, NodeIndex>),
    /// The injection of its value into the summand at this index.
    Injection(Summand, NodeIndex),
    /// The copattern block over the computations in the lowerer's operand
    /// store, in order: one lazy product of them all.
    Copattern(FormStretch),
    /// One entry of the lazy record or the codata the node holds: a thunk
    /// forced, when thunked, or a call run, then projected at the entry's
    /// position.
    Observe(NodeIndex, arity::Observed, arity::Thunked),
    /// One entry of the record, the dependent record or the product the name
    /// at the node holds, with the type over labels it is stated with and the
    /// entry's label when the entry has one: projected at the label off a
    /// record, along the nesting off a dependent record, and at the
    /// component off a product.
    Select(NodeIndex, arity::Observed, Option<(NodeIndex, FieldLabel)>),
    /// The field the label names of the record the value at the node is, its
    /// type stated nowhere: projected at the label, for the checker to read
    /// off the record type the value synthesises.
    Field(NodeIndex, FieldLabel),
    /// The record of the fields the labels select off the value at the node,
    /// `r.#{ .a, .b }`: each field projected in turn as its selection `r.a`
    /// is, bound, and the record of the bound fields returned.
    SubRecord(NodeIndex, Vec<arity::Selected>),
    /// The field a label names of the data value the name at the node is,
    /// read as the case returning it from each constructor.
    Projected(native::ProjectedIndex),
    /// The thunked arrow from the domains in the lowerer's operand store to
    /// the returner of the codomain.
    ValueFunction(FormStretch, NodeIndex),
    /// The thunked telescope from the entries in the lowerer's parameter
    /// store, each binding the ones after it, to the returner of the
    /// codomain.
    Telescope(FormStretch, NodeIndex),
    /// A dependent arrow `(x : A) -> C`: its one binder, in the parameter
    /// store, and its codomain.
    DependentArrow(FormStretch, NodeIndex),
    /// A linear arrow `(x : A) ⊸ C`: its one binder, in the parameter store,
    /// its codomain, and whether a value type is read there, which takes the
    /// box over it.
    LinearArrow(FormStretch, NodeIndex, crate::form::Boxed),
    /// A function's group of outputs read as its result, `(q : A, r : B)`:
    /// the returner of the entries in the lowerer's parameter store, each
    /// standing under the ones before it.
    Returns(FormStretch),
    /// A tuple ending a body whose result is a group of outputs: the return
    /// of the members in the lowerer's operand store, one per output.
    ReturnAll(FormStretch),
    /// One output of a call whose result is a group, `f(a).l`: the call,
    /// every output bound, and the one at `index` returned.
    SelectedOutput
    {
        /// The call.
        call: NodeIndex,
        /// How many outputs the call returns.
        arity: gandr_core_term::ComponentCount,
        /// The selected output's place among them.
        index: usize,
    },
    /// A plugging `left |> right`: every output of `left` bound, and `right`
    /// applied to them in order.
    Plugged
    {
        /// The plugged computation.
        left: NodeIndex,
        /// The function its outputs are plugged into.
        right: NodeIndex,
        /// How many outputs `left` returns.
        arity: gandr_core_term::ComponentCount,
    },
    /// Adopt the child's lowered node unchanged.
    Transparent(NodeIndex),
    /// The value at the first node, ascribed the value type at the second:
    /// `(e : T)` where no other form carries `T`.
    Ascribed(NodeIndex, NodeIndex),
    /// A thunk over its block.
    Thunk(Block),
    /// A returner over its value.
    Return(NodeIndex),
    /// A force over its value.
    Force(NodeIndex),
    /// A run over its computation, standing for the value it returns.
    Run(NodeIndex),
    /// A lambda over its block, and the node its parameter is written at.
    Lambda(Block, NodeIndex),
    /// A block's statements bound over its last computation.
    Block(Block),
    /// A loop's fixpoint over its body.
    Loop(Block),
    /// A conditional loop's fixpoint over the case of its condition: its body
    /// when the condition holds, leaving the loop with unit when it does not.
    While(NodeIndex, Block),
    /// A conditional: the case of its condition over its two branches.
    If(conditional::Conditional),
    /// A list loop's structural fixpoint over the case of the remaining list,
    /// applied to the list: its body on a cell, leaving the loop with unit on
    /// the empty list.
    For(NodeIndex, Block),
    /// A bare `break`: the returner of unit, leaving the nearest loop.
    Break,
    /// A `continue`: the force of the nearest loop's fixpoint, applied to its
    /// remaining tail in a `for`.
    Reenter(loops::Reentry),
    /// An application of its head to its arguments, left to right, in the
    /// lowerer's operand store.
    Application(NodeIndex, FormStretch),
    /// A function tail's declared type and body.
    Function(Function),
    /// The nominal family declared at this admission position, over the
    /// arguments in the lowerer's operand store, left to right.
    Data(ConstantIndex, FormStretch),
    /// The codata declaration at this admission position, applied to the
    /// arguments in the lowerer's operand store, left to right: a
    /// computation type.
    Codata(ConstantIndex, FormStretch),
    /// The type family member at this place of the collection's family list,
    /// its type expanded over the arguments in the lowerer's operand store,
    /// left to right.
    Expansion(FamilyIndex, FormStretch),
    /// A constructor applied to its fields.
    Constructor(native::Constructed),
    /// A multi-output constructor applied to its inputs and no output named:
    /// the record of its ports, each the constructor at its tag over the
    /// same fields, labelled by its output.
    Ports(native::Constructed, Vec<(FieldLabel, ConstructorTag)>),
    /// A match, compiled to the decision tree at this position of the
    /// lowerer's match store.
    Case(native::CaseIndex),
    /// An element path type or a bridge type over its carrier and its two
    /// endpoints.
    Path(Relating, Carrier, NodeIndex, NodeIndex),
    /// Reflexivity at its point.
    Here(NodeIndex),
    /// Function extensionality between its two functions.
    Funext(NodeIndex, NodeIndex),
    /// A universe equivalence between its two translators.
    Equiv(NodeIndex, NodeIndex),
    /// Univalence over its record, `ua(e)`.
    Univalence(NodeIndex),
    /// The native product of two universe paths.
    PathProduct(NodeIndex, NodeIndex),
    /// Univalence at a stratum between two descriptions, over its forward
    /// and backward translator records.
    Ua
    {
        /// The degree and catalogue bound written in the head.
        stratum: gandr_core_term::ua::Stratum,
        /// The two descriptions as a stratum reads them.
        sides: Arc<gandr_core_term::ua::Sides>,
        /// Where the two descriptions are named, the source's first.
        named: [Origin; 2],
        /// The forward translator record.
        forward: NodeIndex,
        /// The backward translator record.
        backward: NodeIndex,
    },
    /// The filler generator at a stratum over a chain: its generator, read
    /// as a computation, and its cells.
    Fill
    {
        /// The stratum and the chain.
        composite: gandr_core_term::compose::Composite,
        /// The generator `t`.
        generator: NodeIndex,
        /// The cells in vertex order, in the lowerer's operand store.
        cells: FormStretch,
    },
    /// `Eq.generic(T)` as a definition's whole body: nothing here, the
    /// declaration's type and body derived whole from `T`'s signature
    /// (`Lowerer::mint_generics`).
    Generic,
    /// The empty native list.
    ListNil,
    /// A native list cell over its head and tail.
    ListCons(NodeIndex, NodeIndex),
    /// Transport along a path, over the static abstraction its motive is
    /// written as, the path, and the transported value.
    Transport(NodeIndex, NodeIndex, NodeIndex),
    /// A directed identity type over its carrier and its two endpoints:
    /// `Flow[.A = A](a, b)` or `Flow(a, b)`.
    Flow(Carrier, NodeIndex, NodeIndex),
    /// A relation between two types written infix, over its two operands:
    /// value types for the equivalence and the quasi-inverse, codes for the
    /// flow.
    Relation(Relation, NodeIndex, NodeIndex),
    /// A theory's models as a type, `Model(S)`: the bundled record the
    /// signature derived from `S` states.
    Bundle(Arc<model::Bundled>),
    /// A module packed at its model type, `pack M at Model(S)`: the bundled
    /// record of the module's members.
    Packed(Arc<model::Packed>),
    /// A first-class continuation's type over the computation types it runs
    /// from and to: `Stack(C, D)`.
    Stack(NodeIndex, NodeIndex),
    /// A session statement, `Path.bisim(A, B)` or `Flow.sim(A, B)`, over its
    /// two codes, and the payload paths `Path.bisim(A, B, p)` writes.
    SessionRelated(
        gandr_core_term::session::SessionRelation,
        NodeIndex,
        NodeIndex,
        Option<NodeIndex>,
    ),
    /// The identity flow at its point.
    Stay(NodeIndex),
    /// The forward flow of its translator.
    Forward(NodeIndex),
    /// The function flow over its domain and codomain flows.
    FunctionFlow(NodeIndex, NodeIndex),
    /// The product of two universe flows.
    FlowProduct(NodeIndex, NodeIndex),
    /// Two flows composed, returned: `Flow.then(f, g)` where a flow is
    /// answered.
    FlowThen(NodeIndex, NodeIndex),
    /// A recorded run, its moves in order, each payload the node it was
    /// written as.
    Recorded(Arc<[gandr_core_term::session::RecordedMove<NodeIndex>]>),
    /// A dialogue, its moves in log order, each beside its endpoint, each
    /// payload the node it was written as.
    Dialogue(Arc<[gandr_core_term::session::DialogueMove<NodeIndex>]>),
    /// The causal web of the dialogue written at the node.
    Decompose(NodeIndex),
    /// A ride along a flow, over the static abstraction its motive is written
    /// as, the flow, and the value moved.
    Ride(NodeIndex, NodeIndex, NodeIndex),
    /// `back`, `then` or `cong`, unfolded to the transport it derives
    /// against the path type its position answers.
    Derived(identity::Derived),
    /// The dependent transport over its telescope motive.
    TelescopeTransport(identity::Transported),
    /// A capability type over its authority at its grade, living in its
    /// region.
    Capability(
        capability::Authority,
        gandr_core_term::effect::capability::CapabilityGrade,
        gandr_core_term::effect::capability::Region,
    ),
    /// The returner of the value type at the node, its row holding these
    /// interfaces whole, open through its tail when one is written.
    Effectful(capability::WrittenRow, NodeIndex),
    /// An operation exercised through a capability.
    Exercise(capability::Exercised),
    /// A method called off its receiver.
    Method(method::Called),
    /// A capability scope over its subject and clauses.
    Scope(capability::Scoped),
    /// The continuation at the node resumed with the reply the values in the
    /// lowerer's operand store make.
    Resume(NodeIndex, FormStretch),
    /// The continuation at the node abandoned.
    Abandon(NodeIndex),
    /// A session type: its protocol over the payload types in the lowerer's
    /// operand store, in slot order, standing at the protocol's root, and
    /// every site the source writes one of its states at.
    Session(Arc<Protocol>, FormStretch, Arc<session::Written>),
    /// A session action over the nodes of its payload, its arms and a fork's
    /// protocol and children, with the bytes its endpoint is written at and,
    /// for an offer, each arm's label with the bytes its pattern is written at.
    Action(
        SessionAction<NodeIndex, NodeIndex, NodeIndex>,
        ByteSpan,
        session::ArmLabels,
    ),
    /// A temporary-access form: an access over its body and unwind, or an
    /// eliminator of its view.
    Access(access::Accessed),
    /// A located form or type: a handle type `A at w`, a hold or a
    /// migration.
    World(world::Worlded),
    /// A data type at a stage its function's telescope binds: the type and
    /// the stage.
    Staged(NodeIndex, gandr_kernel_term::Stage),
    /// A record type patched by a static bracket, `T[.l = v]` or a system of
    /// faces `T[f ↦ v, g ↦ w]`: each field of the base `T` at the type `T`
    /// writes for it, each fixed label at the value the bracket first writes
    /// for it, and each later face's value on a meet.
    Patched
    {
        /// The base's fields, by label.
        fields: BTreeMap<FieldLabel, NodeIndex>,
        /// The fixed values, by label.
        fixed: BTreeMap<FieldLabel, NodeIndex>,
        /// Each later face's value at a label of its meet with an earlier
        /// face, as the face poset gives the meet, in written order (#5106).
        meets: Vec<(FieldLabel, NodeIndex)>,
        /// Where the base is written as the name of a type member, when it
        /// is: the printer writes the name for the base's record.
        member: Option<NodeIndex>,
    },
    /// A value type kept in a region: the type and the region, a capability
    /// scope's or a hold's by its depth, or the definition's region binder.
    Kept(NodeIndex, gandr_core_term::effect::capability::Region),
}

/// A node's lowered core node, at the sort its own form produced.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The family tag prevents reading a value as a computation or type;
///   a function can retain a body without a signature.
/// - provides: A family-indexed result for later parents and declaration
///   assembly.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Arena membership cannot be checked from numeric
///   identifiers alone; minting functions and family accessors state the
///   executable result relations.
///
/// # Adequacy
/// - hypothesis: L3 — completed and one-sided declarations preserve their
///   available halves, and function tails keep their body when a type is
///   absent.
/// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `gandr-surface-lowering::lower::tests::an_uncompleted_signature_is_the_obligation_producer`
/// - witness: `gandr-surface-lowering::lower::tests::a_bodiless_definition_lowers_its_body_alone`
/// - witness: `gandr-surface-lowering::lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Lowered
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
    /// A function tail: its declared type, when it states one, and its body.
    Function
    {
        /// `+U (A1 -> … -> An -> C)`, from the parameter and result types.
        signature: Maybe<ValueTypeId, lowered::Absent>,
        /// `thunk (λ … λ. block)`.
        body: ValueId,
    },
}

/// Whether a node lies inside an attribute payload, which lowers whatever
/// its declaration's outcome.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag marks nodes that remain eligible for minting despite an
///   enclosing declaration’s refusal.
/// - provides: The payload exception to ordinary refusal pruning.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The node and enclosing attributes are absent; seed,
///   `inherit_payload` and `mint_at` check marking and its effect.
///
/// # Adequacy
/// - hypothesis: L3 — an otherwise refused declaration retains its valid
///   attribute payload, and invalid attributes still receive their diagnostics.
/// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
/// - witness: `gandr-surface-lowering::lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InPayload(pub bool);

/// One form being classified: where it stands, what it is called, and how
/// its position reads it.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The location, form name and positional reading stay available
///   together when constructing a located refusal.
/// - provides: The source context shared by the form readers.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The grammar and source tree are not retained; readers
///   check admission and one checks the operand-count projection.
///
/// # Adequacy
/// - hypothesis: L3 — misplaced tiles, extra operands and wrong operand counts
///   retain their distinct refusal kinds and source positions.
/// - witness: `gandr-surface-lowering::lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
/// - witness: `gandr-surface-lowering::lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
/// - witness: `gandr-surface-lowering::lower::tests::a_juxtaposed_operand_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Site
{
    /// The form.
    pub at: Placed,
    /// The form's kind, as a diagnostic writes it.
    pub name: FormName,
    /// How the form's position reads it.
    pub reading: Reading,
}

impl Site
{
    /// The refusal this form earns for leaving the fragment by `boundary`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn out<'source>(
        self,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        self.folded(self.name, boundary)
    }

    /// The refusal this form earns as the folded form `form`.
    ///
    /// # Specification
    /// - requires: the site identifies the refused source form.
    /// - ensures: the refusal retains the supplied form and boundary at the
    ///   site, with the sort demanded by its reading.
    /// - provides: a positional refusal for a nested former.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declined value, computation and type forms keep the
    ///   position’s sort, distinct from the former’s own family.
    /// - witness: `gandr-surface-lowering::lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
    #[spec(
        ensures: |ret| {
            matches!(
                (self.reading, ret),
                (
                    Reading::Unread | Reading::Function,
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::Declaration,
                        ..
                    }
                ) | (Reading::ValueType(_), LoweringRefusal::OutOfFragment {
                    sort: FragmentSort::ValueType,
                    ..
                }) | (
                    Reading::CompType(_) | Reading::Result(_),
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::CompType,
                        ..
                    }
                ) | (Reading::Value(_), LoweringRefusal::OutOfFragment {
                    sort: FragmentSort::Value,
                    ..
                }) | (
                    Reading::Computation(_) | Reading::Head(_),
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::Computation,
                        ..
                    }
                )
            )
        },
    )]
    #[inline]
    #[must_use]
    pub const fn folded<'source>(
        self,
        form: FormName,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::OutOfFragment {
            span: self.at.span,
            form,
            sort: self.reading.sort(),
            boundary,
        }
    }

    /// The refusal this form earns for `fault` at `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fault<'source>(
        self,
        span: ByteSpan,
        fault: FormFault,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::MalformedForm {
            span,
            form: self.name,
            fault,
        }
    }

    /// The operand a one-operand hole holds, or the fault its run earns.
    ///
    /// # Specification
    /// - requires: `run` is a hole of this form.
    /// - ensures: the operand of a one-operand run; an empty run is a missing
    ///   operand at its gap, and a longer run an extra operand at its second.
    /// - provides: the one-hole reading every former shares.
    /// - fails: yields the missing-operand or extra-operand refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a hole not holding one form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — single-operand forms and an overfull hole distinguish
    ///   success from an arity fault at the extra operand.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_juxtaposed_operand_is_refused`
    #[spec(
        ensures: |ret| {
            matches!(
                (run, ret),
                (Run::One(_), Ok(_))
                    | (
                        Run::Empty(_),
                        Err(LoweringRefusal::MalformedForm {
                            fault: FormFault::MissingOperand,
                            ..
                        })
                    )
                    | (
                        Run::Several { .. },
                        Err(LoweringRefusal::MalformedForm {
                            fault: FormFault::ExtraOperand,
                            ..
                        })
                    )
            )
        },
    )]
    #[inline]
    pub const fn one<'source>(
        self,
        run: Run,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        match run {
            Run::One(operand) => Ok(operand),
            Run::Empty(gap) => Err(self.fault(gap, FormFault::MissingOperand)),
            Run::Several { extra, .. } => Err(self.fault(extra.span, FormFault::ExtraOperand)),
        }
    }
}

/// A manifest type an instance exports: its template's type renamed by the
/// application, at the template's sort.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a value type for a value template, a computation type for a
///   computation template.
/// - executable: none — a renamed type is data its readers match on.
///
/// # Adequacy
/// - hypothesis: L3 — a transparent functor's manifest result reads the
///   argument's type at each instance, a computation type too.
/// - witness: `gandr-surface-lowering::tests::modules::functors::a_transparent_result_reads_the_argument_through`
/// - witness: `gandr-surface-lowering::tests::modules::a_type_member_names_a_computation_type_3080`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InstanceType
{
    /// A renamed value type.
    Value(ValueTypeId),
    /// A renamed computation type.
    Computation(CompTypeId),
}

/// The groups by which hole names count the tree's blocks (#5469).
///
/// The record is read as far as a hole asks. A block that holds a top-level
/// form joins the group of the block before it when one slot owns both
/// forms, as a signature and its definition, or a declaration and its
/// attributes. A block that holds a root joins the group before it. Each
/// other block opens the next group.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `groups` holds one group for each block read, in order; `form` is
///   the next top-level form no block read has passed; `owner` is the slot of
///   the last form's block, when a slot owns its form.
/// - executable: none — `Lowerer::hole_group` states the relations.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration written in one form or in two names the
///   holes of the declaration after it alike.
/// - witness: `gandr-surface-lowering::lower::implicit::tests::a_declaration_in_one_form_or_two_names_the_later_holes_alike_5469`
#[derive(Clone, Debug, Default)]
pub struct HoleGroups
{
    /// Each block's group, by the block's number: the number a hole's name
    /// holds, and the group's first block.
    pub groups: Vec<(u32, LayoutBlock)>,
    /// The next of the tree's top-level forms whose block no block read has
    /// passed.
    pub form: usize,
    /// The slot that owns the form of the last block read, when a slot owns
    /// one.
    pub owner: Option<SlotIndex>,
}

/// The source that a lowering is at, and where its share of each list begins.
///
/// A unit is lowered one source at a time, in its order. Each source's
/// collection and each pass over it run before the next source's. So what a
/// source lowers to does not depend on the sources after it.
///
/// # Specification
/// - ensures: each mark is the length its list had when the source's collection
///   began.
/// - executable: none — the marks are positions into lists this record does not
///   hold.
///
/// # Adequacy
/// - hypothesis: L3 — a source lowers to the same declarations and the same
///   leading arena rows whether or not another source follows it.
/// - witness: `gandr-surface-lowering::tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
#[derive(Clone, Copy, Debug, Default)]
pub struct Current
{
    /// The source.
    pub source: SourceIndex,
    /// Where its slots begin.
    pub slots: usize,
    /// Where its modules begin.
    pub structures: usize,
    /// Where its data declarations begin.
    pub data: usize,
    /// Where its words begin.
    pub words: usize,
    /// Where its theories' terms begin.
    pub terms: usize,
    /// Where its family members begin.
    pub families: usize,
    /// Where its functors begin.
    pub functors: usize,
    /// Where its functor applications begin.
    pub instances: usize,
    /// Where its mutual blocks begin.
    pub blocks: usize,
    /// Where its decorated modules begin.
    pub decorated: usize,
    /// Where its signature scopes begin.
    pub scopes: usize,
    /// Where its synthesised sites begin.
    pub synthesised: usize,
    /// Where its labels begin.
    pub labels: usize,
    /// Where its data declarations' framed sites begin.
    pub data_frames: usize,
    /// Where its letters begin.
    pub lettered: usize,
    /// Where its empty words' points begin.
    pub pointed: usize,
}

/// The sort a former produces before positional bridges.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The tag describes the former’s own core family before any
///   positional bridge is inserted.
/// - provides: The input sort to the positional admission relation.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The producing former and demanded reading are not
///   retained; require states the complete admission and insertion relation.
///
/// # Adequacy
/// - hypothesis: L3 — explicit and inserted force remain distinct, and a
///   positive result acquires one returner rather than changing its source
///   type.
/// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
/// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `gandr-surface-lowering::lower::tests::a_positive_result_gains_a_returner_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Produced
{
    /// A value.
    Value,
    /// A computation.
    Computation,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
}

/// Positions in a flat vector: the part store of one case's patterns, or the
/// operand store while one classification pushes and takes back a list.
///
/// A plan keeps a [`FormStretch`] of operands instead, which [`Context::kept`]
/// gives (#5628).
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The endpoints denote a half-open range in a caller-selected flat
///   store; they do not certify order or bounds by themselves.
/// - provides: A borrowed-store coordinate rather than an owned list.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No store is retained, and reversed ranges are admitted
///   inputs to stretch; the accessor checks the borrowed range and empty
///   fallback.
///
/// # Adequacy
/// - hypothesis: L3 — empty, full, interior, reversed and past-end ranges
///   distinguish a valid selection from an invalid range.
/// - witness: `gandr-surface-lowering::lower::tests::recorded_ranges_keep_valid_members_and_reject_invalid_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Stretch
{
    /// The first entry.
    pub start: usize,
    /// One past the last entry.
    pub end: usize,
}

/// What a name resolved to.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A binder retains its bound coordinate; a declaration retains its
///   constant and available written signature.
/// - provides: A resolved name that can become a term or static code.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No name, lookup frame or declaration table is retained;
///   `resolve_name` checks lookup and term checks the projection.
///
/// # Adequacy
/// - hypothesis: L3 — local binders and earlier declarations produce different
///   core references, and self-reference remains unresolved.
/// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `gandr-surface-lowering::lower::tests::an_earlier_declaration_resolves_as_a_constant`
/// - witness: `gandr-surface-lowering::lower::tests::a_self_reference_is_unresolved`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Resolved
{
    /// An enclosing binder.
    Binder(Bound),
    /// A declaration strictly earlier than the name's own.
    Declaration
    {
        /// The declaration's admission position.
        constant: ConstantIndex,
        /// The type its signature was written with, when it has one.
        declared: Maybe<NodeIndex, binder_type::Absent>,
    },
}

impl Resolved
{
    /// The plan of the value the name stands for in term position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a resolved binder becomes a variable plan and a resolved
    ///   declaration a constant plan, retaining the respective index.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — binder uses become de Bruijn variables, while earlier
    ///   declarations become constants with their admission position.
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `gandr-surface-lowering::tests::modules::a_backward_member_reference_resolves`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, &ret),
                (Self::Binder(_), &Plan::Variable(..))
                    | (Self::Declaration { .. }, &Plan::Constant(_))
            )
        },
    )]
    #[must_use]
    #[inline]
    pub const fn term(self) -> Plan
    {
        match self {
            Self::Binder(bound) => Plan::Variable(bound.index, bound.binder),
            Self::Declaration { constant, .. } => Plan::Constant(constant),
        }
    }
}

/// Where the mint sweep writes: the arena and the origin table, with the
/// computations the commuting of early exits reads.
///
/// # Specification
/// - requires: The arena and origin table belong to the current minting run;
///   pre-existing arena nodes need not have entries in the new table.
/// - ensures: Minting operations pair newly allocated nodes with written or
///   inserted origins rather than treating an identifier as proof of ownership.
/// - provides: The shared targets of core allocation and provenance recording.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Allocation history is not a property of the pair of
///   references; value, computation, atom and bridge specify each recording
///   operation.
///
/// # Adequacy
/// - hypothesis: L3 — authored nodes, inserted force and derived function
///   thunks retain distinct provenance on the listed source forms.
/// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
/// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `gandr-surface-lowering::lower::exits::tests::an_exit_under_nesting_leaves_its_function`
pub struct Sink<'run>
{
    /// The arena the core nodes are minted into.
    pub arena: &'run mut CoreArena,
    /// The table every minted node's origin is recorded in.
    pub origins: &'run mut OriginTable,
    /// Every computation an exit minted, and each copy a match leaf made of
    /// one.
    pub exits: BTreeSet<ComputationId>,
    /// Every bind whose rest is distributed to its computation's local ends,
    /// and each copy a match leaf made of one, with its statement's origin.
    pub distributed: BTreeMap<ComputationId, Origin>,
    /// The host's interfaces, once a capability form has minted them.
    pub host: capability::Host,
    /// The signature each capability scope over a theory handles, by the
    /// scope's node and where the signature stands, minted at the first form
    /// naming it there.
    pub theories: BTreeMap<(NodeIndex, capability::Standing), EffectSig>,
    /// The signature of each extern block's interface, by where the block
    /// names it, minted at the first form reading it.
    pub foreign: BTreeMap<ByteOffset, EffectSig>,
    /// Every fixpoint a loop minted, and each copy a match leaf made of one:
    /// the commuting walks into its body.
    pub loops: BTreeSet<ComputationId>,
    /// Every returner a `break` minted, and each copy a match leaf made of
    /// one: a local end of its loop's position rather than of its body.
    pub breaks: BTreeSet<ComputationId>,
    /// Every hold a threading loop's pass minted to hold a slot again, and
    /// each copy a rewrite made of one: it stands in for the slot it holds
    /// again, so a rest a `break` continues under it reads it in that slot's
    /// place rather than past it.
    pub reholds: BTreeSet<ComputationId>,
    /// Every derived operation's transport, with the path type it returns an
    /// element of: what an operation over it reads where no type is answered.
    pub identities: BTreeMap<ComputationId, identity::Identity>,
    /// How many wildcards the mint inserted in each form, past the ones the
    /// planner nominated there: the place the next one takes (#6113).
    pub wildcards: BTreeMap<gandr_core_term::hole::HoleForm, u32>,
}

/// The tables the mint sweep keeps beside the arena and the origin table,
/// held between two sources' lowerings.
///
/// # Specification
/// - ensures: each table is [`Sink`]'s field of the same name.
/// - provides: what a lowering suspended at a source boundary carries of its
///   sink.
/// - fails: none as a data value.
/// - panics: none as a data value.
///
/// # Adequacy
/// - hypothesis: L3 — a document resumed after its closure commutes its exits
///   over the closure's tables as the whole lowering does.
/// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[derive(Clone, Debug)]
pub struct SinkTables
{
    /// [`Sink::exits`].
    pub exits: BTreeSet<ComputationId>,
    /// [`Sink::distributed`].
    pub distributed: BTreeMap<ComputationId, Origin>,
    /// [`Sink::host`].
    pub host: capability::Host,
    /// [`Sink::theories`].
    pub theories: BTreeMap<(NodeIndex, capability::Standing), EffectSig>,
    /// [`Sink::foreign`].
    pub foreign: BTreeMap<ByteOffset, EffectSig>,
    /// [`Sink::loops`].
    pub loops: BTreeSet<ComputationId>,
    /// [`Sink::breaks`].
    pub breaks: BTreeSet<ComputationId>,
    /// [`Sink::reholds`].
    pub reholds: BTreeSet<ComputationId>,
    /// [`Sink::identities`].
    pub identities: BTreeMap<ComputationId, identity::Identity>,
    /// [`Sink::wildcards`].
    pub wildcards: BTreeMap<gandr_core_term::hole::HoleForm, u32>,
}

impl SinkTables
{
    /// The tables before anything is minted: every table empty, the host
    /// unminted.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn new() -> Self
    {
        Self {
            exits: BTreeSet::new(),
            distributed: BTreeMap::new(),
            host: capability::Host::Unminted,
            theories: BTreeMap::new(),
            foreign: BTreeMap::new(),
            loops: BTreeSet::new(),
            breaks: BTreeSet::new(),
            reholds: BTreeSet::new(),
            identities: BTreeMap::new(),
            wildcards: BTreeMap::new(),
        }
    }
}

impl Default for SinkTables
{
    /// [`SinkTables::new`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl<'run> Sink<'run>
{
    /// The sink writing into `arena` and `origins`, its tables `tables`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn new(
        arena: &'run mut CoreArena,
        origins: &'run mut OriginTable,
        tables: SinkTables,
    ) -> Self
    {
        let SinkTables {
            exits,
            distributed,
            host,
            theories,
            foreign,
            loops,
            breaks,
            reholds,
            identities,
            wildcards,
        } = tables;
        Self {
            arena,
            origins,
            exits,
            distributed,
            host,
            theories,
            foreign,
            loops,
            breaks,
            reholds,
            identities,
            wildcards,
        }
    }

    /// The sink's tables, its arena and origin table released.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn into_tables(self) -> SinkTables
    {
        let Self {
            exits,
            distributed,
            host,
            theories,
            foreign,
            loops,
            breaks,
            reholds,
            identities,
            wildcards,
            ..
        } = self;
        SinkTables {
            exits,
            distributed,
            host,
            theories,
            foreign,
            loops,
            breaks,
            reholds,
            identities,
            wildcards,
        }
    }
}

impl Sink<'_>
{
    /// Write `bridge` over `minted`, the core node of the syntax node at
    /// `origin`.
    ///
    /// # Specification
    /// - requires: `minted` is what the node's own plan minted.
    /// - ensures: a bare node is `minted` unchanged; a forced value is minted
    ///   as a force over it, a returned value type as a returner over it, a
    ///   quoted type as the quote of it at its own sort, a computation standing
    ///   as an endpoint as the value it returns, a lambda standing there as its
    ///   thunk, and a value standing at a tail as the returner over it, each
    ///   with `origin` marked as the insertion it is; nothing when the node did
    ///   not lower at the sort its bridge leaves, which the classification
    ///   makes unreachable.
    /// - provides: the minting half of the insertions a position's sort
    ///   decides.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forced heads, positive results, quoted types and
    ///   values at a tail acquire the intended inserted provenance, while an
    ///   author-written force stays written.
    /// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_positive_result_gains_a_returner_once`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_lambda_argument_in_an_endpoint_is_its_thunk_3697`
    /// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    /// - witness: `gandr-surface-lowering::lower::runs::tests::a_call_returning_a_function_runs_where_it_is_applied_3935`
    #[spec(
        ensures: |ret| match bridge {
            | Bridge::Bare => ret == minted,
            | Bridge::HeadCall => match (minted, ret) {
                | (Maybe::Present(Lowered::Computation(_)), Maybe::Present(Lowered::Computation(id))) => {
                    self.origins.computation(id) == Maybe::Present(origin.inserted(Insertion::Force))
                },
                | (Maybe::Present(Lowered::Computation(_)), _) => false,
                | (Maybe::Absent(reason), _) => ret == Maybe::Absent(reason),
                | (Maybe::Present(_), _) => ret == Maybe::Absent(lowered::Absent::OtherSort),
            },
            | Bridge::Inserted(insertion) => match (minted, insertion, ret) {
                | (Maybe::Absent(reason), ..) => ret == Maybe::Absent(reason),
                | (
                    Maybe::Present(Lowered::Value(_)),
                    Insertion::Force | Insertion::Return,
                    Maybe::Present(Lowered::Computation(id)),
                ) => self.origins.computation(id) == Maybe::Present(origin.inserted(insertion)),
                | (
                    Maybe::Present(Lowered::ValueType(_)),
                    Insertion::Returner,
                    Maybe::Present(Lowered::CompType(id)),
                ) => self.origins.comp_type(id) == Maybe::Present(origin.inserted(insertion)),
                | (
                    Maybe::Present(Lowered::ValueType(_) | Lowered::CompType(_)),
                    Insertion::Quote,
                    Maybe::Present(Lowered::Value(id)),
                )
                | (
                    Maybe::Present(Lowered::Computation(_)),
                    Insertion::Endpoint | Insertion::Nested | Insertion::Bound | Insertion::Thunk,
                    Maybe::Present(Lowered::Value(id)),
                ) => self.origins.value(id) == Maybe::Present(origin.inserted(insertion)),
                | (Maybe::Present(Lowered::Value(_)), Insertion::Force | Insertion::Return, _)
                | (Maybe::Present(Lowered::ValueType(_)), Insertion::Returner, _)
                | (Maybe::Present(Lowered::Computation(_)), Insertion::Endpoint | Insertion::Nested | Insertion::Bound | Insertion::Thunk, _)
                | (
                    Maybe::Present(Lowered::ValueType(_) | Lowered::CompType(_)),
                    Insertion::Quote,
                    _,
                ) => false,
                | _ => ret == Maybe::Absent(lowered::Absent::OtherSort),
            },
        },
    )]
    #[inline]
    pub fn bridge(
        &mut self,
        minted: Maybe<Lowered, lowered::Absent>,
        bridge: Bridge,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let insertion = match (bridge, minted) {
            (Bridge::Bare, _) => return minted,
            // A call or a selection at an application's head stands nested
            // under a force: the checker decides whether it runs (#3935, #4818).
            (Bridge::HeadCall, Maybe::Present(Lowered::Computation(call))) => {
                let nested = self.arena.value_nested(call);
                self.origins
                    .record_value(nested, origin.inserted(Insertion::Nested));
                let id = self.arena.computation_force(nested);
                return Maybe::Present(self.computation(id, origin.inserted(Insertion::Force)));
            },
            (Bridge::HeadCall, Maybe::Present(_)) => {
                return Maybe::Absent(lowered::Absent::OtherSort);
            },
            (Bridge::HeadCall, Maybe::Absent(reason)) => return Maybe::Absent(reason),
            (Bridge::Inserted(insertion), _) => insertion,
        };
        let inserted = origin.inserted(insertion);
        match (minted, insertion) {
            (Maybe::Present(Lowered::Value(forced)), Insertion::Force) => {
                let id = self.arena.computation_force(forced);
                Maybe::Present(self.computation(id, inserted))
            },
            (Maybe::Present(Lowered::ValueType(returned)), Insertion::Returner) => {
                let id = self.arena.comp_type_returner(returned);
                self.origins.record_comp_type(id, inserted);
                Maybe::Present(Lowered::CompType(id))
            },
            (Maybe::Present(Lowered::ValueType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::CompType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote_computation(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::Computation(returned)), Insertion::Endpoint) => {
                let id = self.arena.value_returned(returned);
                Maybe::Present(self.value(id, inserted))
            },
            (
                Maybe::Present(Lowered::Computation(nested)),
                Insertion::Nested | Insertion::Bound,
            ) => {
                let id = self.arena.value_nested(nested);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::Computation(suspended)), Insertion::Thunk) => {
                let id = self.arena.value_thunk(suspended);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::Value(returned)), Insertion::Return) => {
                let id = self.arena.computation_return(returned);
                Maybe::Present(self.computation(id, inserted))
            },
            (
                Maybe::Present(_),
                Insertion::Force
                | Insertion::Thunk
                | Insertion::Returner
                | Insertion::Quote
                | Insertion::Decode
                | Insertion::Return
                | Insertion::Classifier
                | Insertion::Match
                | Insertion::Fixpoint
                | Insertion::Joint
                | Insertion::Loop
                | Insertion::Statement
                | Insertion::Endpoint
                | Insertion::Identity
                | Insertion::Nested
                | Insertion::Bound
                | Insertion::Unwind
                | Insertion::Model
                | Insertion::Relation
                | Insertion::Words
                | Insertion::Terms
                | Insertion::Method
                | Insertion::Assignment
                | Insertion::Parameter
                | Insertion::Derived
                | Insertion::Implicit
                | Insertion::Foreign
                | Insertion::Multiplicity,
            ) => Maybe::Absent(lowered::Absent::OtherSort),
            (Maybe::Absent(reason), _) => Maybe::Absent(reason),
        }
    }

    /// Record `id`'s origin and wrap it as a lowered value.
    ///
    /// # Specification
    /// - requires: the value id follows all values already recorded in this
    ///   origin table.
    /// - ensures: the supplied origin is recorded under the value id and the
    ///   lowered result retains that id and family.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every minted value has its own source origin, and an
    ///   inserted force does not relabel the source value it consumes.
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == Lowered::Value(id) && self.origins.value(id) == Maybe::Present(origin)
        },
    )]
    #[inline]
    pub fn value(
        &mut self,
        id: ValueId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_value(id, origin);

        Lowered::Value(id)
    }

    /// Record `id`'s origin and wrap it as a lowered computation.
    ///
    /// # Specification
    /// - requires: the computation id follows all computations already recorded
    ///   in this origin table.
    /// - ensures: the supplied origin is recorded under the computation id and
    ///   the lowered result retains that id and family.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — written and inserted computations retain their own
    ///   source and provenance rather than borrowing an operand origin.
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == Lowered::Computation(id)
                && self.origins.computation(id) == Maybe::Present(origin)
        },
    )]
    #[inline]
    pub fn computation(
        &mut self,
        id: ComputationId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_computation(id, origin);

        Lowered::Computation(id)
    }

    /// Mint `atom`'s value type and record its origin.
    ///
    /// # Specification
    /// - requires: newly minted type ids follow those already recorded in the
    ///   origin table.
    /// - ensures: the selected unit, integer, text, character or floating-point
    ///   value type is minted and receives the supplied origin.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete nullary type heads mint their own core type
    ///   and every minted type carries a source origin.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match ret {
            | Lowered::ValueType(id) => self.origins.value_type(id) == Maybe::Present(origin) && match atom {
                TypeAtom::Boolean => self.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Sum(ref parts) if parts.len() == 2 && parts.iter().all(|&part| self.arena.value_type(part) == Some(&ValueType::unit())))),
                TypeAtom::Unit => self.arena.value_type(id) == Some(&ValueType::unit()),
                TypeAtom::Integer => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::Integer)),
                TypeAtom::Text => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::String)),
                TypeAtom::Character => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::Character)),
                TypeAtom::Float64 => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::Float64)),
                TypeAtom::Fixed(width) => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::Fixed(width))),
                TypeAtom::Void => self.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Sum(ref parts) if parts.is_empty())),
                TypeAtom::Buffer => self.arena.value_type(id) == Some(&ValueType::Buffer),
                TypeAtom::Qubit => self.arena.value_type(id) == Some(&ValueType::Qubit),
                TypeAtom::Web => self.arena.value_type(id) == Some(&ValueType::Web),
                TypeAtom::Row => self.arena.value_type(id) == Some(&ValueType::Row),
            },
            | _ => false,
        },
    )]
    #[inline]
    pub fn atom(
        &mut self,
        atom: TypeAtom,
        origin: Origin,
    ) -> Lowered
    {
        let id = match atom {
            TypeAtom::Boolean => {
                let unit = self.arena.value_type_unit();
                self.origins.record_value_type(unit, origin);
                self.arena.value_type_sum(&[unit, unit])
            },
            TypeAtom::Unit
            | TypeAtom::Integer
            | TypeAtom::Text
            | TypeAtom::Character
            | TypeAtom::Float64
            | TypeAtom::Fixed(_)
            | TypeAtom::Void
            | TypeAtom::Buffer
            | TypeAtom::Qubit
            | TypeAtom::Web
            | TypeAtom::Row => atom_type(self.arena, atom),
        };
        self.origins.record_value_type(id, origin);

        Lowered::ValueType(id)
    }
}

/// The feature a form named `name`, written where a pattern is read and taken
/// by no pattern reading, is refused by.
///
/// # Specification
/// - requires: `name` names a form no pattern reading at its position takes.
/// - ensures: the feature the dispatch table declines `name` by where it
///   declines it, [`Unbuilt::UnreadPattern`] for every other form.
/// - provides: the one feature every pattern position refuses an unread form
///   by.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a rest pattern outside a list, declined by its own row, a
///   lambda, which the dispatch reads, and a misplaced form, standing as
///   patterns.
/// - witness: `gandr-surface-lowering::lower::tests::an_unread_pattern_names_its_feature`
#[spec(ensures: |ret| match declined_feature(name) {
    | Maybe::Present(feature) => ret == feature,
    | Maybe::Absent(_) => ret == Unbuilt::UnreadPattern,
})]
#[must_use]
#[inline]
pub fn unread_pattern(name: FormName) -> Unbuilt
{
    match declined_feature(name) {
        Maybe::Present(feature) => feature,
        Maybe::Absent(_) => Unbuilt::UnreadPattern,
    }
}

/// Read a parenthesised, comma-separated argument list into `written`.
///
/// # Specification
/// - requires: `cursor` stands at the list's `(`.
/// - ensures: [`delimited`] between `(` and `)`.
/// - provides: the argument reading of calls and type applications.
/// - fails: as [`delimited`].
/// - panics: none.
/// - executable: none — the parentheses fixed for [`delimited`], whose
///   predicate states the reading.
///
/// # Errors
/// The form's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — as [`delimited`], whose argument-list witnesses read
///   through this one.
/// - witness: `gandr-surface-lowering::lower::tests::argument_lists_preserve_prefixes_and_locate_the_first_fault`
/// - witness: `gandr-surface-lowering::lower::tests::a_call_applies_its_arguments_left_to_right`
#[inline]
pub fn arguments<'source, Written>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut Written,
) -> Result<(), LoweringRefusal<'source>>
where
    Written: Extend<NodeIndex> + AsRef<[NodeIndex]>,
{
    delimited(
        site,
        cursor,
        written,
        TileName::PAREN_OPEN,
        TileName::PAREN_CLOSE,
    )
}

/// Read the argument list of a call that takes exactly `N` arguments.
///
/// # Specification
/// - requires: `cursor` stands at the list's `(`.
/// - ensures: the `N` arguments in written order; `written` holds what it held
///   before, whatever the answer.
/// - fails: the list's own refusal first; then, for a list of any other count,
///   the arity boundary at `site`.
/// - panics: none.
///
/// # Errors
/// The list's refusal, or [`LoweringRefusal::OutOfFragment`] with the arity
/// boundary at the call.
///
/// # Adequacy
/// - hypothesis: L3 — a generic's one argument, a composite's two, a fill's
///   three and a statement's four lower in written order; a composite of one
///   argument, a fill of two and a statement one short are each refused by
///   their count.
/// - witness: `gandr-surface-lowering::lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_composite_the_syntax_cannot_read_is_refused`
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_fill_lowers_to_its_generator_and_cells`
/// - witness: `gandr-surface-lowering::lower::ua::tests::a_statement_the_syntax_cannot_read_is_refused`
#[spec(captures: before = written.entries().len(), ensures: |_| written.entries().len() == before)]
#[inline]
pub fn exactly<'source, const N: usize>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut ByForm<NodeIndex>,
) -> Result<[NodeIndex; N], LoweringRefusal<'source>>
{
    let start = written.mark();
    let read = arguments(site, cursor, written);
    let appended = written.entries().get(usize::from(start) ..).unwrap_or(&[]);
    let count = appended.len();
    let exact = <[NodeIndex; N]>::try_from(appended).ok();
    written.truncate(start);
    read?;
    exact.ok_or_else(|| site.out(FragmentBoundary::Arity(OperandCount::from(count))))
}

/// Read a comma-separated operand list between the tiles `open` and `close`
/// into `written`.
///
/// # Specification
/// - requires: `cursor` stands at the list's `open`.
/// - ensures: every operand written is appended to `written`, left to right,
///   with the cursor past the `close` and nothing after it; an empty list
///   appends nothing, and a comma after the last operand is admitted.
/// - provides: the argument reading of calls and type applications, and the
///   element reading of a list literal.
/// - fails: yields the hole's own refusal for an empty or juxtaposed argument,
///   and a misplaced-tile refusal for a list out of shape; the arguments read
///   before the refusal stay appended.
/// - panics: none.
///
/// # Errors
/// The form's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — empty, multi-argument and comma-closed calls append their
///   own ordered operand range; a failure preserves the already-read prefix and
///   locates the unexpected operand or tile instead of silently accepting a
///   suffix. The predicate re-reads the list as the body did and compares it
///   with only the operands this call appended.
/// - witness: `gandr-surface-lowering::lower::tests::argument_lists_preserve_prefixes_and_locate_the_first_fault`
/// - witness: `gandr-surface-lowering::lower::tests::a_call_applies_its_arguments_left_to_right`
#[spec(
    captures: before = (written.as_ref().len(), cursor.clone()),
    ensures: |ret| {
        written.as_ref().len() >= before.0
            && ret.as_ref().map_or(true, |&()| written.as_ref().get(before.0 ..).is_some_and(|appended| {
                let mut input = before.1.clone();
                let mut appended = appended.iter();
                if matches!(input.tile(open), Maybe::Absent(_)) {
                    return false;
                }
                if matches!(input.tile(close), Maybe::Present(_)) {
                    return appended.next().is_none()
                        && matches!(input.peek(), Maybe::Absent(_))
                        && cursor.peek() == input.peek();
                }
                loop {
                    match input.read() {
                        | Maybe::Present(Piece::Operand(at))
                            if appended.next() == Some(&at.node) => {},
                        | _ => return false,
                    }
                    if matches!(input.tile(close), Maybe::Present(_)) {
                        break;
                    }
                    if matches!(input.tile(TileName::COMMA), Maybe::Absent(_)) {
                        return false;
                    }
                    if matches!(input.tile(close), Maybe::Present(_)) {
                        break;
                    }
                }
                appended.next().is_none()
                    && matches!(input.peek(), Maybe::Absent(_))
                    && cursor.peek() == input.peek()
            }))
    },
)]
#[inline]
pub fn delimited<'source, Written>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut Written,
    open: TileName,
    close: TileName,
) -> Result<(), LoweringRefusal<'source>>
where
    Written: Extend<NodeIndex> + AsRef<[NodeIndex]>,
{
    delimited_list(site, cursor, written, open, close)?;
    exhausted(site, cursor)
}

/// Read a comma-separated operand list between the tiles `open` and `close`
/// into `written`, and leave the cursor past the `close`, where a call in a
/// type may write its second list, `f(a)(b)` (#5213).
///
/// # Specification
/// - requires: `cursor` stands at the list's `open`.
/// - ensures: as [`delimited`], except that pieces may follow the `close`.
/// - fails: as [`delimited`].
/// - panics: none.
/// - executable: none — [`delimited`] states the reading, and this is its
///   reading without the check that nothing follows.
///
/// # Errors
/// The form's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — as [`delimited`]; a type's call of a call reads both of
///   its lists.
/// - witness: `gandr-surface-lowering::tests::modules::a_module_s_function_is_called_in_a_type_5213`
#[inline]
pub fn delimited_list<'source, Written>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut Written,
    open: TileName,
    close: TileName,
) -> Result<(), LoweringRefusal<'source>>
where
    Written: Extend<NodeIndex>,
{
    if let Maybe::Absent(_) = cursor.tile(open) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    loop {
        let run = cursor.operands();
        let closing = cursor.tile(close);
        if let (Run::Empty(_), Maybe::Present(_)) = (run, closing) {
            return Ok(());
        }
        let argument = site.one(run)?;
        written.extend([argument.node]);
        if let Maybe::Present(_) = closing {
            return Ok(());
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        }
    }
}

/// The entries of `store` that `stretch` names.
///
/// # Specification
/// - requires: the range is interpreted against the supplied store.
/// - ensures: an ordered in-bounds range returns that borrowed slice; a
///   reversed or out-of-bounds range returns an empty slice.
/// - provides: an allocation-free view of the positions one classification
///   reads in the operand store or the part store.
/// - fails: invalid ranges are represented by the empty view.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, interior and full ranges retain the requested
///   members; reversed and past-end ranges do not read an unrelated prefix.
/// - witness: `gandr-surface-lowering::lower::tests::recorded_ranges_keep_valid_members_and_reject_invalid_bounds`
#[spec(
    ensures: |ret| match store.get(stretch.start .. stretch.end) {
        | Some(expected) => core::ptr::eq(&raw const *ret, &raw const *expected),
        | None => ret.is_empty(),
    },
)]
#[inline]
pub fn stretch<Entry>(
    store: &[Entry],
    stretch: Stretch,
) -> &[Entry]
{
    store.get(stretch.start .. stretch.end).unwrap_or(&[])
}

/// Read the closing tile `label`, refusing anything else in its place.
///
/// # Specification
/// - requires: the cursor describes the site’s remaining pieces.
/// - ensures: the requested tile is consumed if present; otherwise the cursor
///   is unchanged and the refusal locates its current piece or gap.
/// - provides: a checked closing tile for the form reader.
/// - fails: an absent or different tile is `MisplacedTile`.
/// - panics: none.
///
/// # Errors
/// `MisplacedTile` when the tile at the cursor is absent or another.
///
/// # Adequacy
/// - hypothesis: L3 — matching and mismatched closing tiles separate
///   consumption from a located refusal, including the exhausted-cursor gap.
/// - witness: `gandr-surface-lowering::lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
#[spec(
    captures: before = {
        let found = cursor.at(label);
        let here = cursor.here();
        let mut next = cursor.clone();
        if matches!(found, Maybe::Present(_)) {
            let _piece = next.read();
        }
        (found, here, next.peek(), next.here())
    },
    ensures: |ret| {
        ret == match before.0 {
            | Maybe::Present(_) => Ok(()),
            | Maybe::Absent(_) => Err(site.fault(before.1, FormFault::MisplacedTile)),
        } && cursor.peek() == before.2
            && cursor.here() == before.3
    },
)]
#[inline]
pub fn closed<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    label: TileName,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.tile(label) {
        Maybe::Present(_) => Ok(()),
        Maybe::Absent(_) => Err(site.fault(cursor.here(), FormFault::MisplacedTile)),
    }
}

/// Refuse a piece left after a form's last.
///
/// # Specification
/// - requires: the cursor describes the site’s remaining pieces.
/// - ensures: only an exhausted cursor succeeds; a remaining operand and a
///   remaining tile yield their distinct located refusals.
/// - provides: a check that a form reader consumed its complete input.
/// - fails: an operand is `ExtraOperand` and a tile is `MisplacedTile`.
/// - panics: none.
///
/// # Errors
/// `ExtraOperand` for a remaining operand, and `MisplacedTile` for a remaining
/// tile.
///
/// # Adequacy
/// - hypothesis: L3 — remaining operands and tiles are distinguished from the
///   terminal gap without consuming the unexpected piece.
/// - witness: `gandr-surface-lowering::lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
/// - witness: `gandr-surface-lowering::lower::tests::a_juxtaposed_operand_is_refused`
#[spec(
    ensures: |ret| {
        ret == match cursor.peek() {
            | Maybe::Absent(_) => Ok(()),
            | Maybe::Present(Piece::Operand(at)) => {
                Err(site.fault(at.span, FormFault::ExtraOperand))
            },
            | Maybe::Present(Piece::Tile { at, .. }) => {
                Err(site.fault(at.span, FormFault::MisplacedTile))
            },
        }
    },
)]
#[inline]
pub fn exhausted<'source>(
    site: Site,
    cursor: &Cursor<'_>,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.peek() {
        Maybe::Absent(_) => Ok(()),
        Maybe::Present(Piece::Operand(stray)) => {
            Err(site.fault(stray.span, FormFault::ExtraOperand))
        },
        Maybe::Present(Piece::Tile { at, .. }) => {
            Err(site.fault(at.span, FormFault::MisplacedTile))
        },
    }
}
